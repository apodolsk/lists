#define MODULE LFLISTM

#include <atomics.h>
#include <lflist.h>
#include <nalloc.h>

#ifndef FAKELOCKFREE

/* #undef E_DBG_LVL */
/* #define E_DBG_LVL 0 */
#define FLANC_CHECK_FREQ E_DBG_LVL ? 50 : 0

static err help_next(flx a, flx *n, flx *np);
static err help_prev(flx a, flx *p, flx *pn);

static err help_enq(flx a, flx *n, flx *np);
static err abort_enq(flx a, flx *p, flx *pn);

static err lflist_del_upd(flx a, flx *p, uptr ng);

#define pt(flx)                                 \
    ((flanchor *) (uptr)((flx).pt << 3))

#define to_pt(flanc) ((uptr) (flanc) >> 3)

#define fl(markp, flstate, _gen, extra...)                              \
    ((flx){.nil = (markp).nil,                                          \
            .pt = (markp).pt,                                           \
            .st = (flstate),                                            \
            .gen = (_gen)})

/* flx readx(volatile flx *x){ */
/*     flx r; */
/*     r.markp = x->markp; */
/*     fuzz_atomics(); */
/*     r.gen = x->gen; */
/*     return r; */
/* } */
#define readx(x)({                              \
            flx _r;                             \
            _r.markp = (x)->markp;              \
            fuzz_atomics();                     \
            _r.gen = (x)->gen;                  \
            _r;                                 \
        })
/* #define readx(x) atomic_read2(x) */

static
bool eq_upd(volatile flx *a, flx *b){
    flx old = *b;
    *b = readx(a);
    return eq2(old, *b);
}

#define raw_updx_won(as...) raw_updx_won(__func__, __LINE__, as)
#include <stdatomic.h>
static
bool (raw_updx_won)(const char *f, int l, flx n, volatile flx *a, flx *e){
    /* flx r = *a; */
    /* if(eq2(r, *e)){ */
    /*     *a = n; */
    /*     return true; */
    /* } */
    /* *e = r; */

    if(atomic_compare_exchange_strong((_Atomic volatile flx *) a, e, n)){
        log(1, "%:%- %(% => %)", f, l, (void *) a, *e, n);
        *e = n;
        return true;
    }

    /* if(cas2_won(n, a, e)){ */
    /*     log(1, "%:%- %(% => %)", f, l, (void *) a, *e, n); */
    /*     *e = n; */
    /*     return true; */
    /* } */

    return false;
}

#define updx_won(as...) updx_won(__func__, __LINE__, as)
static
bool (updx_won)(const char *f, int l, flx n, volatile flx *a, flx *e){
    assert(!eq2(n, *e));
    assert(aligned_pow2(pt(n), alignof(flanchor)));
    assert(pt(n) || n.st == COMMIT);
    assert(n.nil || pt(n) != cof_aligned_pow2(a, flanchor));

    bool w = (raw_updx_won)(f, l, n, a, e);
    if_dbg(flanc_valid(cof_aligned_pow2(a, flanchor)));
    return w;
}

flat
err (lflist_del)(flx a, type *t){
    assert(!a.nil);
    flx p = readx(&pt(a)->p);
    if(p.st == COMMIT || a.gen != p.gen)
        return -1;
    return (lflist_del_upd)(a, &p, a.gen);
}

err (lflist_jam_upd)(uptr ng, flx a, type *t){
    flx p = readx(&pt(a)->p);
    if(a.gen != p.gen)
        return -1;
    return (lflist_del_upd)(a, &p, ng);
}

err (lflist_jam)(flx a, type *t){
    return lflist_jam_upd(a.gen + 1, a, t);
}

#include <pthread.h>
static flat
err (lflist_del_upd)(flx a, flx *p, uptr ng){
    flx n = readx(&pt(a)->n);
    flx np, pn = {};
    if(!abort_enq(a, p, &pn))
        goto done;
    if(p->gen != a.gen)
        return -1;

    for(;;){
        if(help_next(a, &n, &np))
            goto done;
        assert(pt(np) == pt(a) && np.st != COMMIT);

        if(help_prev(a, p, &pn)){
            if(p->st == COMMIT || a.gen != p->gen)
                goto done;
            if(!eq_upd(&pt(a)->n, &n))
                continue;
            assert(n.st == COMMIT);
            break;
        }
        assert(pt(pn) == pt(a) && pn.st == RDY);

        if(!updx_won(fl(n, COMMIT, n.gen + 1), &pt(a)->n, &n))
            continue;

        if(updx_won(fl(n, pn.st, pn.gen + 1), &pt(*p)->n, &pn))
            break;
    }

    flx np_alt = rup(np, .st = ABORT);
    if(!updx_won(fl(*p, RDY, np.gen + n.nil), &pt(n)->p, &np))
        updx_won(fl(*p, RDY, np.gen + n.nil), &pt(n)->p, &np_alt);
done:
    while(a.gen == p->gen){
        if(ng == a.gen && p->st == COMMIT)
            return -1;
        if(updx_won((flx){.st = COMMIT, .gen = ng}, &pt(a)->p, p))
            return 0;
    }
    return -1;
}

static
err (help_next)(flx a, flx *n, flx *np){
    for(;;){
        if(!pt(*n))
            return -1;

        *np = readx(&pt(*n)->p);
        for(;;){
            if(pt(*np) == pt(a)){
                if(help_enq(a, n, np))
                    break;
                return 0;
            }
            if(!eq_upd(&pt(a)->n, n))
                break;
            if(n->st == COMMIT || (n->st == ADD && pt(a)->p.gen != a.gen))
                return EARG("n abort %:%:%", a, n, np);
            assert(pt(*np) && (np->st != COMMIT));

            updx_won(fl(a, RDY, np->gen + n->nil), &pt(*n)->p, np);
        }

    }
}

static
err (help_prev)(flx a, flx *p, flx *pn){
    for(;;){
        if(!pt(*pn))
            goto newp;
        for(;;){
        readp:
            if(!eq_upd(&pt(a)->p, p))
                break;
            if(pt(*pn) != pt(a))
                return EARG("p abort %:%:%", a, p, pn);
        newpn:
            if(pn->st != COMMIT)
                return 0;

        readpp:;
            flx pp = readx(&pt(*p)->p);
        newpp:;
            if(!pt(pp) || pp.st == COMMIT)
                goto readp;

            flx ppn = readx(&pt(pp)->n);
            for(;;){
                if(!eq_upd(&pt(*p)->p, &pp))
                    goto newpp;
                if(pt(ppn) == pt(a)){
                    if(!updx_won(fl(pp, RDY, p->gen + a.nil), &pt(a)->p, p))
                        goto newp;
                    *pn = ppn;
                    goto newpn;
                }
                if(pt(ppn) != pt(*p))
                    goto readpp;
                if(!updx_won(fl(a,
                                ppn.st == COMMIT ? RDY : COMMIT,
                                pn->gen + 1),
                            &pt(*p)->n, pn))
                    break;
                if(pn->st != COMMIT)
                    return 0;

                updx_won(fl(a, ppn.st, ppn.gen + 1), &pt(pp)->n, &ppn);
            }
        }
    newp:;
        if(!a.nil && (p->st == COMMIT || p->gen != a.gen))
            return EARG("Gen p abort %:%", a, p);

        *pn = readx(&pt(*p)->n);
    }
}

static
err help_enq(flx a, flx *n, flx *np){
    if(np->st != ADD || n->st != RDY)
        return 0;

    flx nn = readx(&pt(*n)->n);
    if(nn.st != ADD)
        return 0;
    assert(nn.nil);

    flx nnp = readx(&pt(nn)->p);
    if(pt(nnp) != pt(a))
        return 0;
    if(!eq_upd(&pt(a)->n, n))
        return -1;
    updx_won(fl(*n, RDY, nnp.gen + 1), &pt(nn)->p, &nnp);
    return 0;
}

static
err abort_enq(flx a, flx *p, flx *_pn){
    flx *pn = (flx[1]){};
    do{
    restart:;
        if(p->st != ADD || p->gen != a.gen)
           return -1;
        *pn = readx(&pt(*p)->n);
        if(pt(*pn) == pt(a))
            return -1;
        /* TODO */
        *p = readx(&pt(a)->p);
        pthread_yield();
        goto restart;
    }while(!updx_won(rup(*p, .st = ABORT), &pt(a)->p, p));

    while(pn->st != COMMIT && pn->nil)
        if(updx_won(rup(*pn, .gen++), &pt(*p)->n, pn))
            break;
        else if(pt(*pn) == pt(a))
            return -1;
    
    return 0;
}

err (lflist_enq)(flx a, type *t, lflist *l){
    return lflist_enq_upd(a.gen + 1, a, t, l);
}

err (lflist_enq_upd)(uptr ng, flx a, type *t, lflist *l){
    flx p = readx(&pt(a)->p);
    if(p.st != COMMIT || p.gen != a.gen)
        return -1;
    flx n = readx(&pt(a)->n);

    flx nil = {.nil=1,
               .pt=to_pt(&l->nil)};
    flx nilp = readx(&l->nil.p);
    flx nilpn = {};

    bool won = false;
    for(;;){
        if(help_prev(nil, &nilp, &nilpn)){
            if(pt(nilpn) != pt(nil)){
                dbg flanchor *npn = pt(nilpn);
                assert((pt(npn->n) == pt(nil)
                        && npn->n.st == ADD
                        && npn->p.st == ADD
                        && pt(npn->p) == pt(nilp))
                        || !eq2(l->nil.p, nilp));
                
                updx_won(fl(nilpn, RDY, nilp.gen + 1), &pt(nil)->p, &nilp);
                nilpn = (flx){};
            }
            continue;
        }

        if(!raw_updx_won(fl(nilp, ADD, ng), &pt(a)->p, &p))
            return assert(!won), -!won;
        won = true;

        /* TODO: avoid gen updates? */
        while(!updx_won(fl(nil, ADD, n.gen + 1), &pt(a)->n, &n))
            if(n.st != COMMIT || !eq_upd(&pt(a)->p, &p))
                return assert(0), 0;

        if(updx_won(fl(a, RDY, nilpn.gen + 1), &pt(nilp)->n, &nilpn))
            break;
    }

    updx_won(fl(a, RDY, nilp.gen + 1), &pt(nil)->p, &nilp);

    return 0;
}

flx (lflist_deq)(type *t, lflist *l){
    flx nil = {.nil=1, .pt=to_pt(&l->nil)};
    flx p = readx(&pt(nil)->p);
    for(;;){
        /* TODO: flinref */
        if(p.nil)
            return (flx){};
        flx r = flx_of(pt(p));
        if(!eq_upd(&pt(nil)->p, &p))
            continue;
        if(!lflist_del(r, t))
            return fake_linref_up(), r;
        must(!eq_upd(&pt(nil)->p, &p));
    }
}

constfun
flanchor *flptr(flx a){
    assert(!a.nil);
    return pt(a);
}

flx flx_of(flanchor *a){
    return (flx){.pt = to_pt(a), .gen=a->p.gen};
}

void (flanc_ordered_init)(uptr g, flanchor *a){
    a->n.markp = (markp){.st=COMMIT};
    a->p.markp = (markp){.st=COMMIT};
    a->n.gen = g;
    a->p.gen = g;
}

/* TODO */
bool (mgen_upd_won)(uptr g, flx a, type *t){
    assert(pt(a)->n.st == COMMIT ||
           a.gen != pt(a)->p.gen);
    for(flx p = readx(&pt(a)->p); p.gen == a.gen;){
        assert(p.st == COMMIT);
        if(raw_updx_won(rup(p, .gen=g), &pt(a)->p, &p))
            return true;
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

    if(!p){
        assert(px.st == COMMIT);
        assert(nx.st == COMMIT);
        if(n)
            assert(pt(n->p) != a);

        goto done;
    }

    if(!n){
        assert(nx.st == COMMIT);
        if(p)
            assert(pt(p->n) != a);
        goto done;
    }

    volatile dbg flx
        pnx = readx(&p->n),
        ppx = readx(&p->p),
        npx = readx(&n->p);


    dbg flanchor
        *volatile pn = pt(pnx),
        *volatile np = pt(npx);

    bool nil = false;
    if(np == a)
        nil = npx.nil;
    else if(np && pt(np->p) == a)
        nil = np->p.nil;

    assert(n != p || nx.nil || nil || px.st == ADD);

    if(nil){
        assert(px.st == RDY && nx.st == RDY);
        assert((np == a && npx.nil)
               || (pt(np->p) == a &&
                   np->p.st != COMMIT &&
                   pt(np->n) == n &&
                   np->n.st == COMMIT));
        dbg flx pnn = pn->n;
        dbg flx pnp = pn->p;
        assert((pn == a && pnx.nil)
               || (pt(pnn) == a &&
                   pnn.nil &&
                   pnn.st == ADD &&
                   pnp.st == ADD &&
                   pt(pnp) == p));
        goto done;
    }

    if(nx.st == COMMIT){
        flanchor *nn = pt(n->n);
        if(nn && (pn == a))
            assert(pt(nn->p) != a);
    }
    if(nx.st == ADD)
        assert(nx.nil);
    assert(np == a
           || pn != a
           || (pt(np->p) == a &&
               np->n.st == COMMIT &&
               np->p.st != COMMIT &&
               nx.st == RDY)
           || (px.st == ADD && nx.st == ADD && nx.nil));
    assert(pn == a
           || nx.st == COMMIT
           || (px.st == ADD && nx.st == ADD && nx.nil && np != a));
    if(pn == a)
        assert(px.st != COMMIT);
    if(np == a && px.st != COMMIT && nx.st != COMMIT)
        assert(pn == a);
    
done:
    /* Sniff out unpaused universe or reordering weirdness. */
    assert(eq2(a->p, px));
    assert(eq2(a->n, nx));

    resume_universe();
    return true;
}

#endif
