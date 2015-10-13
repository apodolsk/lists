/**
 * A lockfree double linked list. It supports queue operations and
 * arbitrary deletion but only allows addition at the end of the
 * list. It's uniquely robust in that it neither calls malloc nor forbids
 * the immediate reuse of deleted nodes. Concurrent calls to del(a) will
 * cooperate up to the point where no subsequent deq() will return a, but
 * del(a) can't abort enq(a), and vice-versa.
 *
 * Nodes ("flanchors") have a generation count incremented upon enq(). So
 * do double word node references ("flx"). del() and enq() abort if called
 * with an flx of the wrong gen, so you can achieve things like "remove a
 * from set s iff a is still in state x."
 *
 * An lflist works a lot like a regular list with a dummy ("nil")
 * node. del(a) still "basically" sets n->p=p; p->n=n and enq(a, l) sets
 * l->nil.p->n = a; l->nil.p = a.
 *
 * This works because for flanchor a, a', del(a') writes a->n iff a->n ==
 * a' and help_prev(a') deduced or ensured that a'->p == a and, for all p,
 * no del(a) will make any successful writes to p->n before it reads a->n.
 *
 * The first condition is given by CAS and the trick to ensuring the other
 * two is that 'a' maintains a transaction counter and state flags in
 * a->n.gen and a->n.st.
 *
 * Before reading a->p, del(a) reads ngen := a->n.gen. After help_prev(a)
 * in del(a) finds p | a p->n write could be attempted, del(a) will set
 * a->n.gen = ngen + 1 and a->n.st = COMMIT iff a->n.gen == ngen. If it
 * succeeds there, it'll write p->n = a iff p->n.gen hasn't been updated
 * since it last read p->n. If it fails either step, it restarts. (This
 * iff behavior is achieved by CAS)
 *
 * So if help_prev(n) finds an := a->n | an.st == COMMIT, it reads p :=
 * a->p
 *  
 *
 * Alex Podolsky <apodolsk@andrew.cmu.edu>
 */

#define MODULE LFLISTM

#define E_LFLISTM 0, BRK, LVL_TODO

#include <atomics.h>
#include <lflist.h>
#include <nalloc.h>

dbg cnt naborts, paborts, pn_oks, helpful_enqs,
        cas_ops, atomic_read_ops, lflist_ops;

#ifndef FAKELOCKFREE

#define LIST_CHECK_FREQ 0
#define FLANC_CHECK_FREQ 0
#define MAX_LOOP 0

#define ADD FL_ADD
#define ABORT FL_ABORT
#define RDY FL_RDY
#define COMMIT FL_COMMIT

static err help_next(flx a, flx *n, flx *np, flx *refn, type *t);
static err help_prev(flx a, flx *p, flx *pn, flx *refp, flx *refpp, type *t);
static void finish_del(flx a, flx p, flx n, flx np, type *t);

#define help_next(as...) trace(LFLISTM, 3, help_next, as)
#define help_prev(as...) trace(LFLISTM, 3, help_prev, as)
#define refupd(as...) trace(LFLISTM, 4, refupd, as)
#define flinref_up(as...) trace(LFLISTM, 5, flinref_up, as)
#define flinref_down(as...) trace(LFLISTM, 5, flinref_down, as)

#define progress(o, n, loops) progress(o, ppl(2, n), loops)
#define casx(as...) casx(__func__, __LINE__, as)
#define updx_ok(as...) updx_ok(__func__, __LINE__, as)
#define updx_ok_modhlp(as...) updx_ok_modhlp(__func__, __LINE__, as)
#define updx_won(as...) updx_won(__func__, __LINE__, as)

static inline
flanchor *pt(flx a){
    return (flanchor *) (uptr)(a.pt << 3);
}

static inline
flx fl(flx p, flstate s, uptr gen){
    return (flx){.nil=p.nil, .st=s, .pt=p.pt, gen};
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

static
flx hard_readx(volatile flx *x){
    assert(xadd(1, &atomic_read_ops), 1);
    return atomic_read2(x);
}

static
flx readx(volatile flx *x){
    flx r;
    do{
        r.gen = atomic_read(&x->gen);
        r.markp = atomic_read(&x->markp);
    }while(atomic_read(&x->gen) != r.gen);
    return r;
}

static
flx soft_readx(volatile flx *x){
    flx r;
    r.markp = atomic_read(&x->markp);
    r.gen = atomic_read(&x->gen);
    return r;
}

static
bool eqx(volatile flx *a, flx *b){
    flx old = *b;
    *b = readx(a);
    return eq2(old, *b);
}

static
bool soft_eqx(volatile flx *a, flx *b){
    flx old = *b;
    *b = soft_readx(a);
    return eq2(old, *b);
}

static
flx (casx)(const char *f, int l, flx n, volatile flx *a, flx *e){
    /* assert(n.nil || (a != &pt(n)->p && a != &pt(n)->n)); */
    /* assert(n.pt || !e->pt); */
    /* assert(!eq2(n, *e)); */
    assert(xadd(1, &cas_ops), 1);
    log(2, "CAS! %:% - % if %, addr:%", f, l, n, *e, a);
    flx oe = *e;
    /* *e = readx(a); */
    /* if(!eq2(*e, oe)) */
    /*     return *e; */
    *e = cas2(n, a, oe);
    log(2, "% %:%- found:% addr:%", eq2(*e, oe)? "WON" : "LOST", f, l, *e, a);
    if(e->gen > n.gen && e->gen - n.gen >= (UPTR_MAX >> 1))
        SUPER_RARITY("woahverflow");
    assert(!pt(n) || flanchor_valid(n));
    return *e;
}

static
howok (updx_ok)(const char *f, int l, flx n, volatile flx *a, flx *e){
    flx oe = *e;
    (casx)(f, l, n, a, e);
    if(eq2(*e, oe))
        return *e = n, WON;
    if(eq2(*e, n))
        return OK;
    return NOT;
}

static
howok (updx_ok_modhlp)(const char *f, int l, flx n,
                              volatile flx *a, flx *e){
    flx oe = *e;
    (casx)(f, l, n, a, e);
    if(eq2(*e, oe))
        return *e = n, WON;
    if(eq2(*e, n))
        return OK;
    if(e->st == RDY && n.st == ADD){
        oe.st = n.st = RDY;
        if(eq2(*e, oe)){
            *e = oe;
            return (updx_ok)(f, l, n, a, e);
        }
    }
    return NOT;
}

static
bool (updx_won)(const char *f, int l,
                       flx n, volatile flx *a, flx *e){
    return WON == (updx_ok)(f, l, n, a, e);
}

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
    if(src && soft_eqx(src, a))
        *a = (flx){};
    return -1;
}

err (lflist_del)(flx a, type *t){
    assert(!a.nil);
    assert(xadd(1, &lflist_ops), 1);

    if(pt(a)->p.gen != a.gen || !pt(pt(a)->p))
        return EARG("Early gen abort: %", a);

    howok pn_ok = NOT;
    bool del_won = false;
    flx pn, refp = {}, refpp = {}, p = {};
    flx np, refn = {}, n = soft_readx(&pt(a)->n);
    for(int lps = 0;; countloops(lps++)){
        if(help_next(a, &n, &np, &refn, t))
            break;
        assert(pt(np) == pt(a));
        if(help_prev(a, &p, &pn, &refp, &refpp, t))
            break;
        assert(pt(pn) == pt(a) && pn.st < COMMIT && pn.st > ADD);

        bool has_winner = n.st >= ABORT;
        if(!updx_won(fl(n, COMMIT, n.gen + 1), &pt(a)->n, &n))
            continue;
        assert(!del_won || has_winner);
        del_won = del_won || !has_winner;

        pn_ok = updx_ok(fl(n, pn.st, pn.gen + 1), &pt(p)->n, &pn);
        if(pn_ok)
            break;
    }
    if(pn_ok) assert(xadd(1, &pn_oks), 1);
    else if(pt(np) == pt(a)) assert(xadd(1, &paborts), 1);
    else if(pt(np) != pt(a)) assert(xadd(1, &naborts), 1);
    
    if(!del_won || p.gen != a.gen)
        goto cleanup;

    if(pn_ok || pt(np) == pt(a))
        assert(eq2(p, pt(a)->p) || pt(a)->p.gen != a.gen);
    if(pn_ok || pt(np) != pt(a))
        assert(n.pt == pt(a)->n.pt || pt(a)->p.gen != a.gen);

    /* Must be p abort */
    if(!pn_ok && pt(np) == pt(a)){
        n = soft_readx(&pt(a)->n);
        if(n.st <= RDY)
            goto report_finish;
        np = refupd(&n, &refn, NULL, t) ? (flx){} : soft_readx(&pt(n)->p);
        if(!pt(np))
            goto report_finish;
    }

    p = soft_readx(&pt(a)->p);
    if(p.gen != a.gen)
        goto cleanup;

    ppl(2, n, np, pn_ok);
    assert(flanchor_valid(n));
    finish_del(a, p, n, np, t);

report_finish:
    ppl(2, p, pn, pn_ok);
    casx((flx){.st=COMMIT,.gen=a.gen}, &pt(a)->p, &p);
    
cleanup:
    assert(flanchor_valid(a));
    
    flinref_down(&refn, t);
    flinref_down(&refp, t);
    flinref_down(&refpp, t);
    return -!del_won;
}

err (lflist_enq)(flx a, type *t, lflist *l){
    assert(xadd(1, &lflist_ops), 1);
    flx ap;
    for(ap = soft_readx(&pt(a)->p);;){
        if(ap.gen != a.gen || ap.st == ADD || ap.st == ABORT)
            return -1;
        if(ap.st == COMMIT)
            break;
        assert(pt(ap));
        flx apn = pt(ap)->n;
        if(!eqx(&pt(a)->p, &ap))
            continue;
        if(pt(apn) == pt(a))
            return -1;
        break;
    }

    assert(ap.st != ADD);
    flx oap = ap;
    if(!updx_won(fl(ap, ABORT, a.gen + 1), &pt(a)->p, &ap)){
        oap = ap;
        if(ap.gen != a.gen
           || (assert(ap.st == COMMIT), 0)
           || !updx_won(fl(ap, ABORT, a.gen + 1), &pt(a)->p, &ap))
        return -1;
    }
       
    if(oap.st != COMMIT){
        assert(xadd(1, &helpful_enqs), 1);
        flx n = soft_readx(&pt(a)->n);
        assert(n.st == COMMIT);
        if(pt(n) && !refupd(&n, (flx[1]){}, &pt(a)->n, t)){
            finish_del(a, ap, n, soft_readx(&pt(n)->p), t);
            flinref_down(&n, t);
        }
    }
    
    flx nil = pt(a)->n = (flx){.nil=1, ADD, mpt(&l->nil), pt(a)->n.gen + 1};

    markp amp;
    flx op = {}, opn = {}, refpp = {}, p = {}, pn = {};
    for(int c = 0;; countloops(c++)){
        assert(flanchor_valid(nil));
        
        if(help_prev(nil, &p, &pn, (flx[]){p}, &refpp, t))
            EWTF();
        assert(!eq2(op, p) || !eq2(opn, pn)), op = p, opn = pn;
        assert(pt(p) != pt(a));

        pt(a)->p.markp = amp = fl(p, ADD, 0).markp;
        if(updx_won(fl(a, umax(pn.st, RDY), pn.gen + 1), &pt(p)->n, &pn))
            break;
    }
    casx(fl(a, RDY, p.gen + 1), &l->nil.p, (flx[]){p});
    casx(fl(p, RDY, a.gen + 1), &pt(a)->p, &(flx){.markp=amp, a.gen + 1});
    flinref_down(&p, t);
    flinref_down(&refpp, t);
    return 0;
}

err lflist_jam_enq(flx a){
    return -!updx_won((flx){.st=ADD, .gen=a.gen + 1}, &pt(a)->p,
                      &(flx){.st=ADD, .gen=a.gen});
}

flx (lflist_deq)(type *t, lflist *l){
    flx a = {.nil=1,.pt=mpt(&l->nil)};
    flx on = {};
    for(cnt lps = 0;;){
        flx np = {}, n = soft_readx(&pt(a)->n);
        if(help_next(a, &n, &np, (flx[]){on}, t))
            EWTF();
        if(pt(n) == &l->nil || !progress(&on, n, lps++))
            return flinref_down(&n, t), (flx){};
        if(!lflist_del(((flx){.pt=n.pt, np.gen}), t))
            return (flx){n.mp, np.gen};
    }
}

static void (finish_del)(flx a, flx p, flx n, flx np, type *t){
    flx onp = np;
    if(pt(np) == pt(a))
        updx_ok_modhlp(fl(p, np.st, np.gen + n.nil), &pt(n)->p, &np);

    /* Clean up after an interrupted add of n. In this case, a->n is the
       only reference to n reachable from nil. */
    if(pt(np) && np.st == ADD && onp.gen == np.gen){
        assert(!n.nil);
        flx nn = readx(&pt(n)->n);
        if(nn.nil && nn.st == ADD){
            flx nnp = readx(&pt(nn)->p);
            if(pt(nnp) == pt(a))
                casx(fl(n, RDY, nnp.gen + 1), &pt(nn)->p, &nnp);
        }
    }else{
        flx nn = readx(&pt(n)->n);
        assert(!pt(nn) || flanchor_valid(nn));
    }

    assert(flanchor_valid(n));
}

static 
err (help_next)(flx a, flx *n, flx *np, flx *refn, type *t){
    flx on = *refn;
    for(cnt nl = 0, npl = 0;; assert(progress(&on, *n, nl++))){
        do if(!pt(*n)) return *np = (flx){}, -1;
        while(refupd(n, refn, &pt(a)->n, t));
        
        for(flx onp = *np = readx(&pt(*n)->p);;
            progress(&onp, *np, nl + npl++))
        {
            if(pt(*np) == pt(a) && np->st != ABORT)
                return 0;
            if(!soft_eqx(&pt(a)->n, n))
                break;
            if(n->st == ADD || n->st == COMMIT)
                return -1;
            assert(pt(*np) && (np->st == RDY || np->st == ADD));

            if(updx_ok_modhlp(fl(a, np->st, np->gen + n->nil), &pt(*n)->p, np))
                return 0;
        }
    }
}

static 
err (help_prev)(flx a, flx *p, flx *pn, flx *refp, flx *refpp, type *t){
    flx op = *p, opn = *pn;
    for(cnt pl = 0;; assert(progress(&op, *p, pl++))){
        for(cnt pnl = 0;; countloops(pl + pnl++)){
            if(!soft_eqx(&pt(a)->p, p))
                break;
            if(pt(*pn) != pt(a)){
                if(!a.nil)
                    return EARG("P abort %:%", a, pn);
                updx_ok(fl(*pn, RDY, p->gen + 1), &pt(a)->p, p);
                break;
            }
            if(p->st == ADD && !updx_ok(fl(*p, RDY, a.gen), &pt(a)->p, p))
                break;
            if(pn->st < COMMIT)
                return 0;

        readpp:;
            flx pp = soft_readx(&pt(*p)->p);
        newpp:;
            do if(!pt(pp) || pp.st == COMMIT || pp.st == ADD){
                    must(!soft_eqx(&pt(a)->p, p));
                    goto newp;
                } else assert(!eq2(pn, opn) || !eq2(pp, refpp));
            while(refupd(&pp, refpp, &pt(*p)->p, t));
            
            flx ppn = soft_readx(&pt(pp)->n), oppn = {};
            for(cnt ppnl = 0;;progress(&oppn, ppn, pl + pnl + ppnl++)){
                if(!soft_eqx(&pt(*p)->p, &pp))
                    goto newpp;
                if(pt(ppn) != pt(*p) && pt(ppn) != pt(a))
                    goto readpp;
                if(pt(ppn) == pt(a)){
                    if(!updx_ok(fl(pp, RDY, p->gen + a.nil), &pt(a)->p, p))
                        goto newp;
                    swap(refpp, refp);
                    *pn = ppn;
                    /* TODO: can avoid the a->p recheck. */
                    break;
                }
                if(!updx_won(fl(a, ppn.st == COMMIT ? ABORT : COMMIT, pn->gen + 1),
                             &pt(*p)->n, pn))
                    break;
                if(pn->st == ABORT){
                    assert((eq2(pt(a)->p, *p) && pt(pp)->n.pt == p->pt)
                           || !eq2(pt(*p)->n, *pn)
                           || !eq2(pt(*p)->p, pp));
                    return 0;
                }
                assert(ppn.st < COMMIT);
                assert(ppn.st > ADD);

                if(updx_ok(fl(a, ppn.st, ppn.gen + 1), &pt(pp)->n, &ppn))
                {
                    assert(eq2(pt(a)->p, *p)
                           || pt(a)->p.pt == pp.pt
                           || !eq2(pt(pp)->n, ppn));
                    assert(pt(*p)->n.st == COMMIT
                           || !pt(*p)->n.st
                           || !eq2(pp.gen, pt(*p)->p.gen));
                }
            }
        }
    newp:;
        do if(!a.nil && (!pt(*p) || p->st == COMMIT || p->gen != a.gen))
               return EARG("Gen p abort %:%", a, p);
        while(refupd(p, refp, &pt(a)->p, t));

        assert(a.nil || pt(*p) != pt(a));
        *pn = soft_readx(&pt(*p)->n);
    }
}

flx (lflist_next)(flx p, lflist *l){
    flx r, n;
    do{
        n = readx(&pt(p)->n);
        if(n.nil)
            return (flx){};
        r = (flx){.pt = n.pt, pt(n)->p.gen};
        if(pt(p)->p.gen != p.gen)
            return lflist_peek(l);
    }while(atomic_read(&pt(p)->n.gen) != n.gen);
    return r;
}

flx (lflist_peek)(lflist *l){
    flx n = l->nil.n;
    return n.nil ? (flx){} : (flx){.pt = n.pt, pt(n)->p.gen};
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
    flanchor *a = pt(ax);
    assert(a);
    flx px = readx(&a->p), nx = readx(&a->n);
    flanchor *p = pt(px), *n = pt(nx);
    if(retn) *retn = nx;

    /* Early enq(a) or late del(a). */
    if(!p || !n){
        assert(!ax.nil);
        /*        /\* a's on no list. *\/ */
        /* assert((!p && !n && px.st == ADD) */
        /*        /\* enq(a) has locked a->p *\/ */
        /*        || (!n && !p && px.st == COMMIT) */
        /*        /\* enq(a, l) set a->n=&l->nil  *\/ */
        /*        || (!p && n */
        /*            && px.st == COMMIT */
        /*            && pt(n->p) != a */
        /*            && (!pt(n->n) || pt(pt(n->n)->p) != a)) */
        /*        /\* last stage of del(a). It should have helped enq("n") */
        /*           first. *\/ */
        /*        || (!n && p */
        /*            && px.st == RDY */
        /*            && pt(p->n) != a */
        /*            /\* try to check that del(a) hlp enq(n) *\/ */
        /*            && (!pt(pt(p->n)->n) || */
        /*                 pt(pt(pt(p->n)->n)->p) != a))); */
        if(retn) *retn = (flx){};
        return true;
    }

    flanchor
        *pn = pt(readx(&p->n)),
        *pp = pt(readx(&p->p)),
        *np = pt(readx(&n->p)),
        *nn = pt(readx(&n->n));

    if(ax.nil){
        assert(!on || !*on || *on == cof(a, lflist, nil));
        if(on)
            *on = cof(a, lflist, nil);
        assert(p && n && pn && np && nn && pp);
        assert(px.st == RDY && nx.st == RDY);
        assert(np == a
               || (pt(np->p) == a && pt(np->n) == n && np->n.st >= ABORT));
        assert(pn == a
               || (pn->n.st == ADD
                   && pt(pn->n) == a
                   && (pt(pn->p) == p || pt(pp->n) != p)));
    }else{
        assert(!on || *on != cof(a, lflist, nil));
        assert(p != a && n != a);
        assert(n != p || (nx.nil && n == p));
        assert(nx.nil || nx.st != ADD);
        switch(px.st){
        case ADD:
            assert(nx.st == ADD || nx.st == RDY);
            break;
        case RDY:
            assert(np == a
                   || (pn != a && nx.st == COMMIT)
                   || (pt(np->p) == a && nx.st < COMMIT && nx.st > ADD));
            break;
        case COMMIT:
            assert(nx.st == COMMIT);
            break;
        case ABORT:
            assert(pn != a);
        }
        switch(nx.st){
        case ADD:
            assert(nx.nil);
            assert((pn == n && np == p)
                   /* first step, and del(np) hasn't gone too far */
                   || (pn == a && np == p)
                   /* finished. */
                   || (pn == a && np == a)
                   /* enq(a) has stale p so hasn't set p->n=a */
                   || (pn != a && np != p)
                   /* enq(pn) has set p->n=pn but not nil->p=pn.
                      enq(a) will help in help_prev. */
                   || (pn != n && np == p
                       && pt(pn->n) == n && pn->n.st == ADD
                       /* del(p) hasn't made its first step */
                       && (pt(pn->p) == p
                           /* del(p) is far enough along to enable pn->p
                              updates from del(pp) but hasn't helped enq(pn)
                              set nil->p=pn */
                           || (pt(pp->n) != p && p->n.st == COMMIT)))
                   /* Similar to above, except now enq(a) is the one in
                      trouble. It hasn't set nil->p=a but del(PREV_P) has
                      set a->p=PREV_P->p but hasn't helped set n->p=a and
                      thus hasn't cleared PREV_P->n. */
                   || (pn == a && np != p
                       && pt(np->n) == a && np->n.st == COMMIT
                       && pt(pt(np->p)->n) != np));
            break;
        case RDY: case ABORT:
            assert(pn == a);
            assert(np == a || (pt(np->p) == a && np->n.st == COMMIT));
            break;
        case COMMIT:
            assert((pn == a && np == a)
                   || (pn == n && np == a)
                   || (pn == n && np == p)
                   || (pn != a && np != a));
            break;
        }
    }

    
    /* Sniff out for unpaused universe or reordering weirdness. */
    assert(eq2(a->p, px));
    assert(eq2(a->n, nx));
    
    return true;
}


#endif
