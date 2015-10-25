/**
 * Alex Podolsky <apodolsk@andrew.cmu.edu>
 */

#define MODULE LFLISTM

#define E_LFLISTM 0, BRK, LVL_TODO

#include <atomics.h>
#include <lflist.h>
#include <nalloc.h>

static volatile
dbg cnt enqs, enq_restarts, helpful_enqs, deqs, dels, del_restarts,
        pn_wins, naborts, paborts, prev_helps,
        prev_help_attempts, cas_ops, cas_fails, reads, nnp_help_attempts;

#ifndef FAKELOCKFREE

#define PROFILE_LFLIST 0
#define LIST_CHECK_FREQ 0
#define FLANC_CHECK_FREQ E_DBG_LVL ? 0 : 0
#define MAX_LOOP 0

#define ADD FL_ADD
#define ABORT FL_ABORT
#define RDY FL_RDY
#define COMMIT FL_COMMIT

static err help_next(flx a, flx *n, flx *np, flx *refn, type *t);
static err help_prev(flx a, flx *p, flx *pn, flx *refp, flx *refpp, type *t);
static err finish_del(flx a, flx p, flx n, flx np, type *t);
static err do_del(flx a, flx *p, type *t);

#define help_next(as...) trace(LFLISTM, 3, help_next, as)
#define help_prev(as...) trace(LFLISTM, 3, help_prev, as)
#define refupd(as...) trace(LFLISTM, 4, refupd, as)
#define flinref_up(as...) trace(LFLISTM, 5, flinref_up, as)
#define flinref_down(as...) trace(LFLISTM, 5, flinref_down, as)

static inline
flanchor *pt(flx a){
    return (flanchor *) (uptr)(a.pt << 3);
}

static inline
flx fl(flx p, flstate s, uptr gen){
    return (flx){.nil=p.nil, .st=s, .pt=p.pt, gen};
}

static inline
void profile_upd(volatile uptr *i){
    if(PROFILE_LFLIST)
        xadd(1, i);
}

static
err (flinref_up)(flx a, type *t){
    assert(pt(a));
    if(a.nil || !t->linref_up(pt(a), t))
        return 0;
    return -1;
}

static
void (flinref_down)(flx *a, type *t){
    if(!a->nil && pt(*a))
        t->linref_down(pt(*a));
    *a = (flx){};
}

#include <race.h>
static noinline
flx readx(volatile flx *x){
    flx r;
    r.markp = atomic_read(&x->markp);
    r.gen = atomic_read(&x->gen);
    profile_upd(&reads);
    return r;
}

static
bool eqx(volatile flx *a, flx *b){
    flx old = *b;
    *b = readx(a);
    return eq2(old, *b);
}

#include <stdatomic.h>
#define casx(as...) casx(__func__, __LINE__, as)
static
flx (casx)(const char *f, int l, flx n, volatile flx *a, flx e){
    assert(!eq2(n, e));
    assert(n.nil || pt(n) != cof_aligned_pow2(a, flanchor));
    assert(n.st >= ABORT || pt(n));
    profile_upd(&cas_ops);
    
    /* log(2, "CAS! %:% - % if %, addr:%", f, l, n, e, a); */
    flx ne = e;
    atomic_compare_exchange_strong(a, &ne, n);
    /* flx ne = cas2(n, a, e); */
    if(eq2(e, ne))
        log(2, "% %:%- found:% addr:%", eq2(e, ne)? "WON" : "LOST", f, l, e, a);
    
    if((int)(ne.gen - e.gen) < 0)
        SUPER_RARITY("woahverflow");
    if(!eq2(ne, e))
        profile_upd(&cas_fails);
    assert(!pt(n) || flanchor_valid(n));
    return ne;
}

#define updx_ok(as...) updx_ok(__func__, __LINE__, as)
static
howok (updx_ok)(const char *f, int l, flx n, volatile flx *a, flx *e){
    flx oe = *e;
    if(eq2(*e = (casx)(f, l, n, a, *e), oe))
        return *e = n, WON;
    if(eq2(*e, n))
        return OK;
    return NOT;
}

#define updx_ok_modst(as...) updx_ok_modst(__func__, __LINE__, as)
static
howok (updx_ok_modst)(const char *f, int l,
                      flstate st, flstate nst, flx n, volatile flx *a, flx *e){
    flx oe = *e;
    howok k = (updx_ok)(f, l, n, a, e);
    if(k)
        return k;
    if(eq2(*e, rup(oe, .st=st)))
        return (updx_ok)(f, l, rup(n, .st=nst), a, e);
    return NOT;
}

#define updx_won(as...) updx_won(__func__, __LINE__, as)
static
bool (updx_won)(const char *f, int l, flx n, volatile flx *a, flx *e){
    return WON == (updx_ok)(f, l, n, a, e);
}

static
void countloops(cnt loops){
    if(MAX_LOOP && loops > MAX_LOOP)
        SUPER_RARITY("LOTTA LOOPS: %", loops);
}

#define progress(o, n, loops) progress(o, ppl(2, n), loops)
static
bool (progress)(flx *o, flx n, cnt loops){
    bool eq = eq2(*o, n);
    *o = n;
    countloops(loops);
    return !eq;
}

static
err (refupd)(flx *a, flx *held, volatile flx *src, type *t){
    if(!pt(*a))
        return -1;
    if(pt(*a) == pt(*held))
        return 0;
    flinref_down(held, t);
    if(!flinref_up(*a, t)){
        *held = *a;
        return 0;
    }
    if(src && eqx(src, a))
        *a = (flx){};
    return -1;
}

err (lflist_del)(flx a, type *t){
    profile_upd(&dels);
    assert(!a.nil);
    
    flx p = readx(&pt(a)->p);
    if(p.gen != a.gen || p.st >= ABORT)
        return EARG("Early gen abort: %", a);
    return do_del(a, &p, t);
}

static
err (do_del)(flx a, flx *p, type *t){
    howok pn_ok = NOT;
    bool del_won = false;
    flx pn = {}, refp = {}, refpp = {};
    
    flx np, refn = {}, n = readx(&pt(a)->n);
    for(int l = 0;; countloops(l++), profile_upd(&del_restarts)){
        if(help_next(a, &n, &np, &refn, t))
            break;
        assert(pt(np) == pt(a));
        if(help_prev(a, p, &pn, &refp, &refpp, t))
            break;
        assert(pt(pn) == pt(a) && (pn.st == RDY || pn.st == ABORT));

        bool has_winner = n.st >= ABORT;
        switch(updx_ok(fl(n, COMMIT, n.gen + 1), &pt(a)->n, &n)){
        case NOT: continue;
        case WON: del_won = del_won || !has_winner;
        case OK: break;
        }

        pn_ok = updx_ok(fl(n, pn.st, pn.gen + 1), &pt(*p)->n, &pn);
        if(pn_ok)
            break;
    }

    if(pn_ok == WON && !finish_del(a, *p, n, np, t))
        *p = casx((flx){.st=COMMIT,.gen=a.gen}, &pt(a)->p, *p);

    if(pn_ok == WON) profile_upd(&pn_wins);
    else if(pt(np) == pt(a)) profile_upd(&paborts);
    else if(pt(np) != pt(a)) profile_upd(&naborts);
        
    flinref_down(&refn, t);
    flinref_down(&refp, t);
    flinref_down(&refpp, t);
    return -!del_won;
}

static
bool flanc_dead(flx a, flx *ap){
    *ap = readx(&pt(a)->p);
    if(ap->gen != a.gen || ap->st == ADD || ap->st == ABORT)
        return false;
    if(ap->st == RDY){
        flx apn = pt(*ap)->n;
        if(eqx(&pt(a)->p, ap)){
            if(pt(apn) == pt(a))
                return false;
        } else if(!eq2(*ap, ((flx){.st=COMMIT, .gen=a.gen})))
            return false;
    }
    return true;
}

err (lflist_enq)(flx a, type *t, lflist *l){
    profile_upd(&enqs);
    
    flx ap;
    if(!flanc_dead(a, &ap))
        return -1;

    flx oap = ap;
    while(!updx_won(fl(oap = ap, ABORT, a.gen + 1), &pt(a)->p, &ap))
        if(ap.gen != a.gen || ap.st != COMMIT)
            return -1;
       
    if(oap.st != COMMIT){
        profile_upd(&helpful_enqs);
        flx n = readx(&pt(a)->n);
        assert(n.st == COMMIT);
        if(pt(n) && !refupd(&n, &(flx){}, &pt(a)->n, t)){
            finish_del(a, ap, n, readx(&pt(n)->p), t);
            flinref_down(&n, t);
        }
    }

    cnt ngen = pt(a)->n.gen + 1;
    flx op = {}, opn = {}, refpp = {}, pn = {}, refp = {};
    flx nil = pt(a)->n = (flx){.nil=1, ADD, mpt(&l->nil), ngen};
    flx p = readx(&pt(nil)->p);
    for(int c = 0;;
        profile_upd(&enq_restarts),
        assert(progress(&op, p, c++) | progress(&opn, pn, 0)))
    {
        muste(help_prev(nil, &p, &pn, &refp, &refpp, t));
        if(pt(a)->n.gen != ngen)
            return EWTF(), 0;
        /* pt(a)->p = ap = fl(p, ADD, ap.gen); */
        must(upd2_ok(fl(p, ADD, ap.gen), &pt(a)->p, &ap));
        if(updx_won(fl(a, umax(pn.st, RDY), pn.gen + 1), &pt(p)->n, &pn))
            break;
    }
    casx(fl(a, RDY, p.gen + 1), &l->nil.p, p);
    casx(fl(p, RDY, ap.gen), &pt(a)->p, ap);
    
    flinref_down(&p, t);
    flinref_down(&refpp, t);
    return 0;
}

err (lflist_jam)(flx a, type *t){
    return lflist_jam_upd(a, a.gen + 1, t);
}

err (lflist_jam_upd)(flx a, uptr ng, type *t){
    flx p;
    do_del(a, &p, t);

    for(;;){
        if(p.gen != a.gen)
            return -1;
        if(p.st == ADD)
            break;
        if(updx_won(rup(p, .gen=ng), &pt(a)->p, &p))
            return 0;
    }

    for(flx n = readx(&pt(a)->n);;){
        if(pt(a)->p.gen != a.gen)
            return -1;
        if(n.st != ADD)
            break;
        if(updx_won(rup(n, .gen++), &pt(a)->n, &n))
            break;
    }

    do_del(a, &p, t);

    for(;;){
        if(p.gen != a.gen)
            return -1;
        assert(p.st == ADD);
        if(updx_won(rup(p, .gen=ng), &pt(a)->p, &p))
            return 0;
    }
    
    return 0;
}

flx (lflist_deq)(type *t, lflist *l){
    profile_upd(&deqs);
    
    flx a = {.nil=1,.pt=mpt(&l->nil)};
    flx refn = {}, on = {};
    for(cnt lps = 0;;){
        flx np = {}, n = readx(&pt(a)->n);
        do{
            if(help_next(a, &n, &np, (flx[]){on}, t))
                EWTF();
            if(pt(n) == &l->nil || !progress(&on, n, lps++))
                return flinref_down(&n, t), (flx){};
        }while(!eqx(&pt(a)->n, &n));
            
        if(!do_del(((flx){.pt=n.pt, np.gen}), &np, t))
            return (flx){n.mp, np.gen};
    }
}

static 
err (help_next)(flx a, flx *n, flx *np, flx *refn, type *t){
    for(flx on = *refn;; assert(progress(&on, *n, 0))){
        do if(!pt(*n)) return *np = (flx){}, -1;
        while(refupd(n, refn, &pt(a)->n, t));

        flx onp = *np = readx(&pt(*n)->p);
        for(cnt l = 0;; assert(progress(&onp, *np, l++)))
        {
            if(pt(*np) == pt(a) && np->st < ABORT)
                return 0;
            if(!eqx(&pt(a)->n, n))
                break;
            if(n->st == ADD || n->st == COMMIT)
                return -1;
            assert(pt(*np) && (np->st == RDY || np->st == ADD));

            if(updx_ok_modst(RDY, RDY,
                             fl(a, np->st, np->gen + n->nil), &pt(*n)->p, np))
                return 0;
        }
    }
}

static 
err (help_prev)(flx a, flx *p, flx *pn, flx *refp, flx *refpp, type *t){
    flx op = {}, opn = {};
    for(cnt pl = 0;; assert(progress(&op, *p, pl++))){
        if(!pt(*refp))
            goto newp;
        for(cnt pnl = 0;; countloops(pl + pnl++)){
        readp:
            if(!eqx(&pt(a)->p, p))
                break;
            if(pt(*pn) != pt(a)){
                if(!a.nil)
                    return EARG("P abort %:%", a, pn);
                updx_ok(fl(*pn, RDY, p->gen + 1), &pt(a)->p, p);
                break;
            }
            if(p->st == ADD && !updx_ok(fl(*p, RDY, a.gen), &pt(a)->p, p))
                break;
        newpn:
            if(pn->st < COMMIT)
                return 0;

        readpp:;
            flx pp = readx(&pt(*p)->p);
        newpp:;
            profile_upd(&prev_help_attempts);
            do if(!pt(pp) || pp.st == COMMIT || pp.st == ADD)
                   goto readp;
            while(refupd(&pp, refpp, &pt(*p)->p, t));
            
            flx ppn = readx(&pt(pp)->n), oppn = {};
            for(cnt ppnl = 0;;progress(&oppn, ppn, pl + pnl + ppnl++)){
                if(!eqx(&pt(*p)->p, &pp))
                    goto newpp;
                if(pt(ppn) != pt(*p) && pt(ppn) != pt(a))
                    goto readpp;
                if(pt(ppn) == pt(a)){
                    if(!updx_ok(fl(pp, RDY, p->gen + a.nil), &pt(a)->p, p))
                        goto newp;
                    swap(refpp, refp);
                    *pn = ppn;
                    goto newpn;
                }
                if(!updx_ok(fl(a, ppn.st == COMMIT ? ABORT : COMMIT, pn->gen + 1),
                            &pt(*p)->n, pn))
                    break;
                if(pn->st == ABORT)
                    return 0;

                if(updx_won(fl(a, ppn.st, ppn.gen + 1), &pt(pp)->n, &ppn))
                    profile_upd(&prev_helps);
            }
        }
    newp:;
        do if(!a.nil && (p->st >= ABORT || p->gen != a.gen))
               return EARG("Gen p abort %:%", a, p);
            else assert(pt(*p));
        while(refupd(p, refp, &pt(a)->p, t));

        *pn = readx(&pt(*p)->n);
    }
}

static 
err (finish_del)(flx a, flx p, flx n, flx np, type *t){
    assert(n.st == COMMIT);
    
    flx onp = np;
    if(pt(np) == pt(a))
        updx_ok_modst(RDY, RDY, fl(p, np.st, np.gen + n.nil), &pt(n)->p, &np);

    if(pt(np) && np.st == ADD && onp.gen == np.gen){
        profile_upd(&nnp_help_attempts);
        flx nn = readx(&pt(n)->n);
        if(nn.nil && nn.st == ADD){
            flx nnp = readx(&pt(nn)->p);
            if(pt(a)->p.gen != a.gen)
                return -1;
            if(pt(nnp) == pt(a))
                casx(fl(n, RDY, nnp.gen + 1), &pt(nn)->p, nnp);
        }
    }

    return 0;
}

flanchor *flptr(flx a){
    assert(!a.nil);
    return pt(a);
}

flx flx_of(flanchor *a){
    return (flx){.pt = mpt(a), a->p.gen};
}

static bool _flanchor_valid(flx ax, flx *retn, lflist **on);

bool lflist_valid(flx a){
    if(!randpcnt(LIST_CHECK_FREQ) || pause_universe())
        return true;
    lflist *on = NULL;
    for(flx c = a;;){
        assert(_flanchor_valid(c, &c, &on));
        TODO();
        if(!pt(c) || pt(c) == pt(a))
            break;
    }
    assert(on);
    resume_universe();
    return true;
}

bool flanchor_valid(flx ax){
    if(!randpcnt(FLANC_CHECK_FREQ) || pause_universe())
        return true;
    assert(_flanchor_valid(ax, NULL, NULL));
    resume_universe();
    return true;
}

static
bool _flanchor_valid(flx ax, flx *retn, lflist **on){
    flanchor *volatile a = pt(ax);
    assert(a);
    volatile flx 
        px = readx(&a->p),
        nx = readx(&a->n);
    flanchor
        *volatile p = pt(px),
        *volatile n = pt(nx);
    if(retn)
        *retn = nx;

    if(!p || !n){
        assert(!ax.nil);
        assert(px.st == COMMIT || px.st == ABORT);
        assert(nx.st == COMMIT || nx.st == ADD);
        
        if(retn) *retn = (flx){};
        return true;
    }

    volatile flx
        pnx = readx(&p->n),
        ppx = readx(&p->p),
        npx = readx(&n->p),
        nnx = readx(&n->n);
    

    flanchor
        *volatile pn = pt(pnx),
        *volatile pp = pt(ppx),
        *volatile np = pt(npx),
        *volatile nn = pt(nnx);


    assert(!on || *on != cof(a, lflist, nil));
    assert(n != p || ax.nil || nx.nil);
    assert(nx.st != ADD || nx.nil);

    if(ax.nil){
        assert(px.st == RDY && nx.st == RDY);
        assert((np == a && npx.nil)
               || (pt(np->p) == a &&
                   np->n.st == COMMIT &&
                   (np->p.st == RDY || np->p.st == ABORT)));
        assert((pn == a && pnx.nil) ||
               ({
                   assert(ppx.st != COMMIT);
                   assert(pn->n.st == ADD && pn->p.st == ADD);
                   assert(pt(pn->n) == a && pn->n.nil);
               }));
        return true;
    }

    switch(px.st){
    case ADD:
        assert(nx.st == ADD || nx.st == RDY);
        break;
    case RDY:
        assert(pn == a || nx.st == COMMIT);
        break;
    case ABORT:
        assert(pn != a && (nx.st == COMMIT || nx.st == ADD));
        break;
    case COMMIT:
        assert(nx.st == COMMIT);
        assert(pn != a);
        assert(np != a);
        assert(!nn || pt(nn->p) != a);
        break;
    }

               
    switch(nx.st){
    case ADD:
        assert(nx.nil);
        assert(px.st == ADD || px.st == ABORT || np == a);
        break;
    case RDY: case ABORT: 
        assert(pn == a);
        assert(np == a
               || (pt(np->p) == a &&
                   np->n.st == COMMIT &&
                   (np->p.st == RDY || np->p.st == ABORT)));
        break;
    case COMMIT:
        assert((pn == a && np == a) ||
               (pn == n && np == a) ||
               (pn == n && np == p) ||
               (pn != a && np != a));
        break;
    }

    
    /* Sniff out unpaused universe or reordering weirdness. */
    assert(eq2(a->p, px));
    assert(eq2(a->n, nx));
    
    return true;
}

void report_lflist_profile(void){
    if(!PROFILE_LFLIST)
        return;
    cnt ops = enqs + dels + deqs;
    cnt del_ops = dels + deqs;
    double ideal_reads = (4 * enqs + 5 * dels + 7 * deqs);
    double ideal_casx = (4 * enqs + 3 * dels + 3 * deqs);
    lppl(0, enqs, 
         (double) enq_restarts/enqs,
         (double) helpful_enqs/enqs,
         deqs,
         dels,
         (double) del_restarts/del_ops,
         (double) pn_wins/del_ops,
         (double) naborts/del_ops,
         (double) paborts/del_ops,
         (double) nnp_help_attempts/ops,
         cas_ops,
         (double) cas_ops/ideal_casx,
         ideal_casx,
         (double) cas_fails/cas_ops,
         (double) prev_help_attempts/enqs,
         (double) prev_helps/prev_help_attempts,
         reads,
         (double) reads/ideal_reads
         );

}


#endif
