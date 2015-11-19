#define MODULE LFLISTM
#define E_LFLISTM 1, BRK, LVL_TODO

#include <atomics.h>
#include <lflist.h>
#include <nalloc.h>

/* TODO: probably obsoleted by perf probe. */
static volatile
dbg cnt
    enqs, enq_restarts, deqs, dels, del_restarts,
    pn_wins, naborts, paborts, prev_helps,
    prev_help_attempts, cas_ops, cas_fails,
    reads, nnp_help_attempts, flinrefs, flinref_fails;

#ifndef FAKELOCKFREE

#define PROFILE_LFLIST 0
#define FLANC_CHECK_FREQ E_DBG_LVL ? 50 : 0
#define MAX_LOOP 256

#define ADD FL_ADD
#define ABORT FL_ABORT
#define RDY FL_RDY
#define COMMIT FL_COMMIT

static err help_next(flx a, flx *n, flx *np, flx *refn, type *t);
static err help_prev(flx a, flx *p, flx *pn, flx *refp, flx *refpp, type *t);
static void finish_del(flx a, flx *p, const flx *n, const flx *np, type *t);
static err do_del(flx a, flx *p, type *t);

#define help_next(as...) trace(LFLISTM, 3, help_next, as)
#define do_del(as...) trace(LFLISTM, 2, do_del, as)
#define help_prev(as...) trace(LFLISTM, 3, help_prev, as)
#define refupd(as...) trace(LFLISTM, 4, refupd, as)
#define flinref_up(as...) trace(LFLISTM, 5, flinref_up, as)
#define flinref_down(as...) trace(LFLISTM, 5, flinref_down, as)

#undef LOG_LFLISTM
#define LOG_LFLISTM 0

static inline
flanchor *pt(flx a){
    return (flanchor *) (uptr)(a.pt << 4);
}
#define mpt(flanc) ((uptr) (flanc) >> 4)

static
void countloops(cnt loops){
    if(MAX_LOOP && loops > MAX_LOOP)
        SUPER_RARITY("LOTTA LOOPS: %", loops);
}

static
bool (progress)(flx *o, flx n, cnt loops){
    bool eq = eq2(*o, n);
    *o = n;
    countloops(loops);
    return !eq;
}

static inline
flx fl(flx p, flstate s, uptr gen){
    return (flx){.nil=p.nil, .st=s, .pt=p.pt, .validity=FLANC_VALID, .gen=gen};
}

static inline
void profile_upd(volatile uptr *i){
    if(PROFILE_LFLIST)
        xadd(1, i);
}

static
err (flinref_up)(flx a, type *t){
    assert(pt(a));
    profile_upd(&flinrefs);
    if(a.nil || !t->linref_up(pt(a), t))
        return 0;
    profile_upd(&flinref_fails);
    return -1;
}

static
void (flinref_down)(flx *a, type *t){
    if(!a->nil && pt(*a))
        t->linref_down(pt(*a));
    *a = (flx){};
}

/* TODO: the only issue with this is a race involving validity bits:
   do_del(a) via seg_new reads a->n.markgen when it's part of a zombie
   seg, so .rsvd=0. Then a is freed anew and a valid a->n.mgen is
   read. Wild access results. It'd suffice to add another reserved bit to
   x->markp. */
/* static */
/* flx readx(volatile flx *x){ */
/*     flx r; */
/*     r.markp = atomic_read(&x->markp); */
/*     r.mgen = atomic_read(&x->mgen); */
/*     if(r.validity != FLANC_VALID || r.rsvd) */
/*         r = (flx){.st=COMMIT}; */
/*     profile_upd(&reads); */
/*     return r; */
/* } */

static
flx readx(volatile flx *x){
    flx r = atomic_read2(x);
    if(r.validity != FLANC_VALID || r.rsvd)
        r = (flx){.st=COMMIT};
    profile_upd(&reads);
    return r;
}

static
bool eqx(volatile flx *a, flx *b){
    flx old = *b;
    *b = readx(a);
    return eq2(old, *b);
}

static
bool gen_eq(mgen a, mgen ref){
    assert(ref.validity == FLANC_VALID);
    return a.gen == ref.gen && a.validity == FLANC_VALID;
}

#define raw_casx(as...) raw_casx(__func__, __LINE__, as)
static
flx (raw_casx)(const char *f, int l, flx n, volatile flx *a, flx e){
    flx ne = cas2(n, a, e);
    if(eq2(e, ne))
        log(2, "%:%- % => % p:%", f, l, e, n, (void *) a);
    if(!eq2(ne, e))
        profile_upd(&cas_fails);
    if(ne.rsvd || ne.validity != FLANC_VALID)
        ne = (flx){};
    return ne;
}

#define casx(as...) casx(__func__, __LINE__, as)
static
flx (casx)(const char *f, int l, flx n, volatile flx *a, flx e){
    assert(!eq2(n, e));
    assert(aligned_pow2(pt(n), alignof(flanchor)));
    assert(n.validity == FLANC_VALID && e.validity == FLANC_VALID);
    assert(!n.rsvd && !e.rsvd);
    assert(pt(n) || n.st >= ABORT);
    assert(n.nil || pt(n) != cof_aligned_pow2(a, flanchor));
    profile_upd(&cas_ops);
    
    flx ne = (raw_casx)(f, l, n, a, e);

    if_dbg(flanc_valid(cof_aligned_pow2(a, flanchor)));
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
    if(eqx(src, a))
        *a = (flx){};
    return -1;
}

err (lflist_del)(flx a, type *t){
    assert(!a.nil);
    
    flx p = readx(&pt(a)->p);
    if(!gen_eq(p.mgen, a.mgen) || p.st >= ABORT)
        return EARG("Early gen abort: %", a);
    return (do_del)(a, &p, t);
}

static
err (do_del)(flx a, flx *p, type *t){
    assert(a.validity == FLANC_VALID);
    profile_upd(&dels);
    
    howok pn_ok = NOT;
    bool del_won = false;
    flx pn = {}, refp = {}, refpp = {};

    flx np, refn = {}, n = readx(&pt(a)->n);
    for(int l = 0;; countloops(l++), profile_upd(&del_restarts)){
        if(help_next(a, &n, &np, &refn, t)){
            ppl(2, n, np);
            break;
        }
        assert(pt(np) == pt(a));
        if(help_prev(a, p, &pn, &refp, &refpp, t)){
            ppl(2, *p, pn);
            break;
        }
        assert(pt(pn) == pt(a) && (pn.st == RDY || pn.st == ABORT));

        bool has_winner = n.st >= ABORT;
        switch(updx_ok(rup(n, .st=COMMIT, .gen++), &pt(a)->n, &n)){
        case NOT: continue;
        case WON: del_won = del_won || !has_winner;
        case OK: break;
        }

        pn_ok = updx_ok(fl(n, pn.st, pn.gen + 1), &pt(*p)->n, &pn);
        if(pn_ok)
            break;
    }

    if(p->st == ADD)
        goto done;

    if(pn_ok)
        finish_del(a, p, &n, &np, t);
    else
        finish_del(a, p, NULL, NULL, t);
    
    if(gen_eq(p->mgen, a.mgen) && p->st != COMMIT)
        if(!updx_ok(rup(*p, .nil=0, .pt=0, .st=COMMIT), &pt(a)->p, p))
            assert(!gen_eq(p->mgen, a.mgen));

    if(pn_ok == WON) profile_upd(&pn_wins);
    else if(pt(np) == pt(a)) profile_upd(&paborts);
    else if(pt(np) != pt(a)) profile_upd(&naborts);

done:
    
    flinref_down(&refn, t);
    flinref_down(&refp, t);
    flinref_down(&refpp, t);
    return -!del_won;
}

static 
void (finish_del)(flx a, flx *p, const flx *n_opt, const flx *np_opt, type *t){
    if(p->st == COMMIT || !gen_eq(p->mgen, a.mgen))
        return;

    flx np, n;
    if(!np_opt){
        n = readx(&pt(a)->n);
        if(!pt(n) || refupd(&n, &(flx){}, &pt(a)->n, t))
            return;
        np = readx(&pt(n)->p);
        *p = readx(&pt(a)->p);
        if(p->st == COMMIT || !gen_eq(p->mgen, a.mgen))
            goto finish;
    }else{
        np = *np_opt;
        n = *n_opt;
    }

    assert(p->st != ADD);
    
    flx onp = np;
    if(pt(np) == pt(a))
        updx_ok_modst(RDY, RDY, fl(*p, np.st, np.gen + n.nil), &pt(n)->p, &np);

    if(pt(np) && np.st == ADD && gen_eq(np.mgen, onp.mgen)){
        profile_upd(&nnp_help_attempts);
        flx nn = readx(&pt(n)->n);
        if(nn.nil && nn.st == ADD){
            flx nnp = readx(&pt(nn)->p);
            if(!eqx(&pt(a)->p, p))
                goto finish;
            if(pt(nnp) == pt(a))
                casx(fl(n, RDY, nnp.gen + 1), &pt(nn)->p, nnp);
        }
    }

finish:
    if(!np_opt)
        flinref_down(&n, t);
    return;
}

static
bool flanc_enqable(flx a, flx *ap){
    *ap = readx(&pt(a)->p);
    if(ap->st != COMMIT || !gen_eq(ap->mgen, a.mgen))
        return false;
    return true;
}

err (lflist_enq)(flx a, type *t, lflist *l){
    return lflist_enq_upd(a.gen + 1, a, t, l);
}

err (lflist_enq_upd)(uptr ng, flx a, type *t, lflist *l){
    profile_upd(&enqs);

    assert(a.validity == FLANC_VALID);

    flx ap;
    if(!flanc_enqable(a, &ap))
        return -1;
    flx n = readx(&pt(a)->n);
    if(!updx_won(fl(ap, ABORT, ng), &pt(a)->p, &ap))
        return -1;

    assert(n.st == COMMIT || n.st == ADD);
    flx nil = {.nil=1,
               .st=ADD,
               .pt=mpt(&l->nil),
               .validity=FLANC_VALID,
               .gen=n.gen + 1};
    while(!updx_won(fl(nil, ADD, n.gen + 1), &pt(a)->n, &n))
        if(!eqx(&pt(a)->p, &ap))
            return -1;

    flx op = {}, opn = {}, refpp = {}, pn = {}, refp = {};
    flx p = readx(&pt(nil)->p);
    bool won = false;
    for(int c = 0;;
        profile_upd(&enq_restarts),
        assert(progress(&op, p, c++) | progress(&opn, pn, 0)))
    {
        muste(help_prev(nil, &p, &pn, &refp, &refpp, t));
        if(!upd2_won(fl(p, ADD, ap.gen), &pt(a)->p, &ap))
            break;
        if(!gen_eq(pt(a)->n.mgen, n.mgen))
            break;
        if((won = updx_won(fl(a, umax(pn.st, RDY), pn.gen + 1),
                           &pt(p)->n,
                           &pn)))
            break;
    }
    if(won){
        casx(fl(a, RDY, p.gen + 1), &l->nil.p, p);
        casx(rup(ap, .st=RDY), &pt(a)->p, ap);
    }
    
    flinref_down(&p, t);
    flinref_down(&refpp, t);
    return -!won;
}

err (lflist_jam)(flx a, type *t){
    return lflist_jam_upd(a.gen + 1, a, t);
}

/* TODO: need to take flinref on p in pn-write case. Not a problem while
   the only consumer of jam_upd is segalloc, with guaranteed mem validity.  */
/* TODO: haven't seriously tried to optimize here. */
err (lflist_jam_upd)(uptr ng, flx a, type *t){
    flx p = readx(&pt(a)->p);
    for(;;){
        if(p.st == RDY || p.st == ADD)
            do_del(a, &p, t);
        if(!gen_eq(p.mgen, a.mgen))
            return -1;
        if(p.st == ADD)
            break;
        if(updx_won(rup(p, .gen = ng, .st = COMMIT), &pt(a)->p, &p))
            return 0;
    }

    flx n = readx(&pt(a)->n);
    do{ p = readx(&pt(a)->p);
        if(!gen_eq(p.mgen, a.mgen) || n.rsvd)
           return -1;
    }while(n.st == ADD &&
           !updx_won(rup(n, .gen++), &pt(a)->n, &n));

    /* TODO: can probably avoid loop */
    for(;n.st == ADD;){
        assert(n.nil);
        if(!gen_eq(p.mgen, a.mgen))
            return -1;
        if(p.st != ADD)
            break;
        flx pn = readx(&pt(p)->n);
        flx np = readx(&pt(n)->p);
        if(!eqx(&pt(a)->p, &p))
            continue;
        
        if(pt(pn) == pt(a)){
            if(pt(np) == pt(a))
                break;
            /* TODO: can probably break */
            if(!eqx(&pt(a)->n, &n))
                continue;
            if(updx_ok(fl(a, RDY, np.gen), &pt(n)->p, &np))
                break;
            continue;
        }
        if(!eqx(&pt(p)->n, &pn))
            continue;

        if(pn.st == COMMIT || pt(pn) != pt(n) || pt(np) != pt(p))
            goto skip_del;
        if(updx_ok(rup(pn, .gen++), &pt(p)->n, &pn))
            goto skip_del;
    }

    do_del(a, &p, t);
skip_del:;
    if_dbg(flanc_valid(pt(a)));

    while(gen_eq(p.mgen, a.mgen))
        if(updx_won(rup(p, .st=COMMIT, .gen=ng), &pt(a)->p, &p))
            return 0;
        else
            assert(p.st != ABORT || !gen_eq(p.mgen, a.mgen));
    return -1;
}

flx (lflist_deq)(type *t, lflist *l){
    profile_upd(&deqs);
    
    flx a = {.nil=1,.pt=mpt(&l->nil)};
    flx on = {};
    for(cnt lps = 0;;){
        flx np = {}, n = readx(&pt(a)->n);
        do{
            if(help_next(a, &n, &np, (flx[]){on}, t))
                EWTF();
            if(n.nil || !progress(&on, n, lps++))
                return flinref_down(&n, t), (flx){};
        }while(!eqx(&pt(a)->n, &n));
        
        flx r = {.pt=n.pt, .mgen=np.mgen};
        if(!(do_del)(r, &np, t))
            return r;
    }
}

static 
err (help_next)(flx a, flx *n, flx *np, flx *refn, type *t){
    for(flx on = *refn;; assert(progress(&on, *n, 0))){
        do if(!pt(*n)) return -1;
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
    flx op = {};
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
            do if(!pt(pp) || pp.st != RDY)
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
        do if(!a.nil && (p->st >= ABORT || !gen_eq(p->mgen, a.mgen)))
               return EARG("Gen p abort %:%", a, p);
            else assert(pt(*p));
        while(refupd(p, refp, &pt(a)->p, t));

        *pn = readx(&pt(*p)->n);
    }
}

flanchor *flptr(flx a){
    assert(!a.nil);
    return pt(a);
}

flx flx_of(flanchor *a){
    return (flx){.pt = mpt(a), .mgen=a->p.mgen};
}

void (flanc_ordered_init)(uptr g, flanchor *a){
    a->n.markp = (markp){.st=FL_COMMIT};
    a->p.markp = (markp){.st=FL_COMMIT};
    a->n.mgen = (mgen){.validity=FLANC_VALID, .gen=g};
    a->p.mgen = (mgen){.validity=FLANC_VALID, .gen=g};
}

bool (mgen_upd_won)(mgen g, flx a, type *t){
    assert(pt(a)->n.st == COMMIT ||
           pt(a)->n.st == ADD ||
           !gen_eq(pt(a)->p.mgen, a.mgen));
    for(flx p = readx(&pt(a)->p); gen_eq(p.mgen, a.mgen);){
        assert(p.st == COMMIT);
        flx n = raw_casx(rup(p, .mgen=g), &pt(a)->p, p);
        if(eq2(n, p))
            return true;
        p = n;
    }
    return false;
}

bool (flanchor_unused)(flanchor *a){
    return a->p.st == COMMIT;
}

/* TODO: printf isn't reentrant. Watch CPU usage for deadlock upon assert
   print failure.  */
bool flanc_valid(flanchor *a){
    if(!randpcnt(FLANC_CHECK_FREQ) || pause_universe())
        return false;

    volatile flx 
        px = readx(&a->p),
        nx = readx(&a->n);
    flanchor
        *volatile p = pt(px),
        *volatile n = pt(nx);

    if(px.validity != FLANC_VALID ||
       nx.validity != FLANC_VALID ||
       nx.rsvd || px.rsvd)
        return resume_universe(),
               true;
    
    if(!p || !n){
        assert(px.st == COMMIT || px.st == ABORT);
        assert(nx.st == COMMIT || nx.st == ADD);

        assert(!p);
        if(n){
            assert(pt(n->p) != a);
            flanchor *nn = pt(n->n);
            assert(!nn || pt(nn->p) != a);
        }

        resume_universe();
        return true;
    }

    volatile flx
        pnx = readx(&p->n),
        ppx = readx(&p->p),
        npx = readx(&n->p),
        nnx = readx(&n->n);
    

    flanchor
        *volatile pn = pt(pnx),
        *volatile np = pt(npx),
        *volatile nn = pt(nnx);

    bool nil = false;
    if(np == a)
        nil = npx.nil;
    else if(np && pt(np->p) == a)
        nil = np->p.nil;

    /* assert(!on || *on != cof(a, lflist, nil)); */
    assert(n != p || nil || nx.nil);
    assert(nx.st != ADD || nx.nil);

    if(nil){
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
                   1;
               }));
        resume_universe();
        return true;
    }

    assert(pn == a
           || nx.st == COMMIT
           || nx.st == ADD);
    assert(np == a
           || pn != a
           || (px.st == ADD && nx.st == ADD)
           || (pt(np->p) == a &&
               np->n.st == COMMIT &&
               np->p.st == RDY));
    assert((px.st != COMMIT && px.st != ABORT) || pn != a);
           
    /* TODO: probably not worth maintaining these. Failure here could be
       an out-of-date assert. Though I'm not seeing any. */
    switch(px.st){
    case ADD:
        assert(nx.st == ADD || nx.st == RDY);
        break;
    case RDY:
        assert(pn == a || nx.st == COMMIT || nx.st == ADD);
        break;
    case ABORT:
        assert(pn != a && (nx.st == COMMIT || nx.st == ADD));
        break;
    case COMMIT:
        assert(pn != a);
        assert(np != a);
        assert(!nn || pt(nn->p) != a);
        break;
    }

    switch(nx.st){
    case ADD:
        assert(nx.nil);
        assert(px.st != RDY || pn == a);
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

    resume_universe();
    return true;
}

void lflist_report_profile(void){
    if(!PROFILE_LFLIST)
        return;
    /* TODO: doesn't take jam into account */
    /* TODO: way out of date. */
    /* double ideal_reads = (4 * enqs + 5 * dels + 7 * deqs); */
    /* double ideal_casx = (4 * enqs + 3 * dels + 3 * deqs); */
    lppl(0, enqs, 
         (double) enq_restarts/enqs,
         deqs,
         dels,
         (double) del_restarts/dels,
         (double) pn_wins/dels,
         (double) naborts/dels,
         (double) paborts/dels,
         (double) nnp_help_attempts/dels,
         cas_ops,
         /* (double) cas_ops/ideal_casx, */
         /* ideal_casx, */
         (double) cas_fails/cas_ops,
         (double) prev_help_attempts/enqs,
         (double) prev_helps/prev_help_attempts,
         reads,
         flinrefs,
         (double) flinrefs/flinref_fails
         /* (double) reads/ideal_reads */
         );

}


#endif
