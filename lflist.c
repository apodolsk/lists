#define MODULE LFLISTM

#include <atomics.h>
#include <lflist.h>
#include <nalloc.h>

#ifndef FAKELOCKFREE

#define FLANC_CHECK_FREQ E_DBG_LVL ? 50 : 0

#define RDY 0
#define COMMIT 1

static err help_next(flx a, flx *n, flx *np);
static err help_prev(flx a, flx *p, flx *pn);
static err lflist_del_upd(flx a, flx *p, uptr ng);

#define pt(flx)                                 \
    ((flanchor *) (uptr)((flx).pt << 2))

#define to_pt(flanc) ((uptr) (flanc) >> 2)

#define fl(markp, flstate, _gen)                                        \
    ((flx){.nil = (markp).nil,                                          \
            .pt = (markp).pt,                                           \
            .st = (flstate),                                            \
            .gen = (_gen),})

static
flx readx(volatile flx *x){
    flx r;
    r.markp = x->markp;
    fuzz_atomics();
    r.gen = x->gen;
    return r;
}

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
    /* return false; */
    
    if(atomic_compare_exchange_strong((_Atomic volatile flx *) a, e, n)){
        log(1, "%:%- % => % p:%", f, l, e, n, (void *) a);
        return true;
    }
    return false;
    
    /* if(cas2_won(n, a, e)){ */
    /*     log(1, "%:%- %(% => %)", f, l, (void *) a, *e, n); */
    /*     *e = n; */
    /*     return true; */
    /* } */
    
    /* return false; */
}

#define updx_won(as...) updx_won(__func__, __LINE__, as)
static
bool (updx_won)(const char *f, int l, flx n, volatile flx *a, flx *e){
    assert(!eq2(n, *e));
    assert(aligned_pow2(pt(n), alignof(flanchor)));
    assert(pt(n) || n.st == COMMIT);
    assert(n.nil || pt(n) != cof_aligned_pow2(a, flanchor));
    
    if((raw_updx_won)(f, l, n, a, e)){
        *e = n;
        if_dbg(flanc_valid(cof_aligned_pow2(a, flanchor)));
        return true;
    }

    if_dbg(flanc_valid(cof_aligned_pow2(a, flanchor)));
    return false;
}

flat
err (lflist_del)(flx a, type *t){
    assert(!a.nil);
    flx p = readx(&pt(a)->p);
    if(p.st == COMMIT || a.gen != p.gen)
        return -1;
    return (lflist_del_upd)(a, &p, a.gen);
}

#include <pthread.h>
static flat
err (lflist_del_upd)(flx a, flx *p, uptr ng){
    flx np,
        pn = {};
    flx n = readx(&pt(a)->n);
    
    for(;;){
        if(help_next(a, &n, &np))
            goto done;
        assert(pt(np) == pt(a) && np.st == RDY);

        if(help_prev(a, p, &pn)){
            if(p->st != RDY || p->gen != a.gen)
                goto done;
            if(!eq_upd(&pt(a)->n, &n))
                continue;
            if(p->nil && pt(np) == pt(a)){
                pthread_yield();
                continue;
            }
            assert(n.st == COMMIT);
            break;
        }
        assert(pt(pn) == pt(a) && pn.st == RDY);

        if(!updx_won(rup(n, .st=COMMIT, .gen++), &pt(a)->n, &n))
            continue;

        if(updx_won(fl(n, pn.st, pn.gen + 1), &pt(*p)->n, &pn))
            break;
    }

    updx_won(fl(*p, np.st, np.gen + n.nil), &pt(n)->p, &np);

done:
    while(a.gen == p->gen && p->st != COMMIT)
        if(updx_won(rup(*p, .nil=0, .pt=0, .st=COMMIT, .gen = ng),
                    &pt(a)->p,
                    p))
            return 0;
    return -1;
}

static
err (help_next)(flx a, flx *n, flx *np){
    for(;;){
        if(!pt(*n))
            return -1;

        *np = readx(&pt(*n)->p);
        for(;;){
            if(pt(*np) == pt(a))
                return 0;
            if(!eq_upd(&pt(a)->n, n))
                break;
            if(n->st == COMMIT || np->nil)
                return EARG("n abort %:%:%", a, n, np);
            assert(pt(*np) && (np->st == RDY));

            updx_won(fl(a, np->st, np->gen + n->nil), &pt(*n)->p, np);
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
            /* TODO */
            if(pt(*pn) != pt(a))
                return EARG("p abort %:%:%", a, p, pn);
        newpn:
            if(pn->st != COMMIT)
                return 0;

        readpp:;
            flx pp = readx(&pt(*p)->p);
        newpp:;
            if(!pt(pp) || pp.st != RDY)
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
                if(pn->st == RDY)
                    return 0;

                updx_won(fl(a, ppn.st, ppn.gen + 1), &pt(pp)->n, &ppn);
            }
        }
    newp:;
        if(p->st == COMMIT || p->gen != a.gen)
            return EARG("Gen p abort %:%", a, p);
        assert(pt(*p));

        *pn = readx(&pt(*p)->n);
    }
}

/* assert p->nil. */
static
err abort_enq(flx a, flx *n, flx *p){
    /* if(p->nil){ */
    /*     /\* TODO: recheck p *\/ */
    /*     if(n.st == COMMIT){ */
    /*         if(updx_won(rup(*n, .pt = 0, .gen++), &pt(a)->n, n)) */
    /*             return 0; */
    /*         return -1; */
    /*     } */
    /*     /\* TODO: less optimism here *\/ */
    /*     while(!updx_won(rup(*n, .gen++), &pt(a)->n, n)) */
    /*         if(n.st == COMMIT) */
    /*             return -1; */

    /*     flx pn = readx(&pt(*p)->n); */
    /*     while(pt(pn) != pt(a)){ */
    /*         if(!eq_upd(&pt(a)->p, p)) */
    /*             return -1; */
    /*         if(updx_won(rup(pn, .gen++), &pt(p)->n, &pn)) */
    /*             return 0; */
    /*     } */
    /* } */

    /* flx np = readx(&pt(*n)->p); */
    /* if(!eq_upd(&pt(a)->n, n)) */
    /*     return 0; */
    /* if(pt(np)) */
    
    return 0;
}

err (lflist_enq)(flx a, type *t, lflist *l){
    return lflist_enq_upd(a.gen + 1, a, t, l);
}

err (lflist_enq_upd)(uptr ng, flx a, type *t, lflist *l){
    flx n = readx(&pt(a)->n);
    flx p = readx(&pt(a)->p);
    if(p.st != COMMIT || p.gen != a.gen)
        return -1;
    
    flx nil = {.nil=1,
               .pt=to_pt(&l->nil)};
    if(!updx_won(fl(nil, RDY, ng), &pt(a)->p, &p))
        return -1;

    flx niln = readx(&pt(nil)->n);
    flx nilnp;
    do{
        muste(help_next(nil, &niln, &nilnp));
        while(!updx_won(fl(niln, RDY, n.gen + 1), &pt(a)->n, &n))
            if(n.st != COMMIT || !pt(n) || !eq_upd(&pt(a)->p, &p))
                return 0;
    }while(!updx_won(fl(a, RDY, niln.gen + 1), &pt(nil)->n, &niln));

    upd_won(fl(a, RDY, nilnp.gen), &pt(n)->p, &nilnp);
    
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

err (lflist_jam)(flx a, type *t){
    return 0;
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
    

    flanchor
        *volatile pn = pt(pnx),
        *volatile np = pt(npx);

    bool nil = false;
    if(np == a)
        nil = npx.nil;
    else if(np && pt(np->p) == a)
        nil = np->p.nil;

    /* assert(!on || *on != cof(a, lflist, nil)); */
    assert(n != p || nx.nil || nil);

    if(nil){
        assert(px.st == RDY && nx.st == RDY);
        assert((np == a && npx.nil)
               || (pt(np->p) == a &&
                   np->n.st == COMMIT &&
                   np->p.st == RDY));
        assert((pn == a && pnx.nil) || px.nil);
        goto done;
    }

    assert(pn == a
           || nx.st == COMMIT
           || px.nil);
    assert(np == a
           || pn != a
           || (px.nil && np == p)
           || (pt(np->p) == a &&
               np->n.st == COMMIT &&
               np->p.st == RDY));
    assert(px.st == RDY || pn != a);

done:
    /* Sniff out unpaused universe or reordering weirdness. */
    assert(eq2(a->p, px));
    assert(eq2(a->n, nx));

    resume_universe();
    return true;
}

#endif
