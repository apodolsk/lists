#ifndef FAKELOCKFREE

#include <cxx_dialect.hpp>

struct type;

#define FLANC_CHECK_FREQ E_DBG_LVL ? 50 : 0

extern void fuzz_atomics(void);
extern void fake_linref_up(void);
extern bool randpcnt(uptr u);

enum flst{
    COMMIT,
    RDY,
    ADD,
    ABORT,
};

struct lflist;
struct flanchor;

struct flx{
    flst st:2;
    uptr nil:1;
    uptr pt:WORDBITS-3;
    
    uptr gen;

    flx(flx x, flst st, uptr gen):
        st(st),
        nil(x.nil),
        pt(x.pt),
        gen(gen)
        {};

    flx(volatile lflist *l);
    flx(volatile flanchor *l);

    flx() = default;

    operator volatile flanchor*();
    
    /* flanchor& operator*(); */
    flanchor* operator->();
};

struct flanchor{
    flx n;
    flx p;
} align(2 * sizeof(dptr));

struct lflist{
    flanchor nil;
};

#define log(...)
#define ppl(...)
#define RUP_PFX(fld,_, __) __rup_copy fld
#define rup(orig, changes...)({                 \
            auto __rup_copy = orig;             \
            MAP(RUP_PFX,, changes);             \
            __rup_copy;                         \
        })                                      \

err lflist_enq_upd(uptr ng, flx a, type *t, lflist *l);
err lflist_enq(flx a, type *t, lflist *l);

flx lflist_deq(type *t, lflist *l);

err lflist_del(flx a, type *t);
err lflist_jam_upd(uptr ng, flx a, type *t);
err lflist_jam(flx a, type *t);

static err help_next(flx a, flx& n, flx& np, bool enq_aborted);
static err help_prev(flx a, flx& p, flx& pn);

static err help_enq(flx a, flx& n, flx& np);
static err abort_enq(flx a, flx& p, flx& pn);

static err lflist_del_upd(flx a, flx& p, uptr ng);

#define to_pt(flanc) ((uptr) (flanc) >> 3)

flx::flx(volatile lflist *l):
    st(),
    nil(1),
    pt(to_pt(&l->nil)),
    gen()
{}

flx::flx(volatile flanchor *a):
    st(),
    nil(),
    pt(to_pt(a)),
    gen(a->p.gen)
{}

#define pt(x) ((flanchor *)(uptr)((x).pt << 3))

/* flanchor& flx::operator*(){ */
/*     return *(flanchor *)(uptr)(pt << 3); */
/* } */

flx::operator volatile flanchor*(){
    return (flanchor *)(uptr)(pt << 3);
}

flanchor* flx::operator->(){
    return (flanchor *)(uptr)(pt << 3);
}

/* bool flx::operator==(const flx &x){ */
/*     return pt == x.pt; */
/* } */

/* bool flx::operator!=(const flx &x){ */
/*     return pt != x.pt; */
/* } */


/* flx(volatile flx *x){ */
/*     union flx_read{ */
/*         flx x; */
/*         uptr read[2]; */
/*     }; */

/*     flx_read r; */
/*     r.read[0] = ((volatile flx_read *)x)->read[0]; */
/*     fuzz_atomics(); */
/*     r.read[1] = ((volatile flx_read *)x)->read[1]; */
/*     return r.x; */
/* } */
typedef aliasing uptr uptr_aliasing;
flx readx(volatile flx *x){
    union flx_read{
        flx x;
        uptr read[2];
    };

    flx_read r;
    r.read[0] = ((volatile flx_read *)x)->read[0];
    fuzz_atomics();
    r.read[1] = ((volatile flx_read *)x)->read[1];
    return r.x;
}
/* #define readx(x)({                              \ */
/*             flx_read _r;                                   \ */
/*             _r.read[0] = ((volatile flx_read *)x)->read[0]; \ */
/*             fuzz_atomics();                     \ */
/*             _r.read[1] = ((volatile flx_read *)x)->read[1]; \ */
/*             _r.x;   \ */
/*         }) */
/* #define readx(x) atomic_read2(x) */

#include <cstring>
bool eq2(flx a, flx b){
    return !memcmp(&a, &b, sizeof(a));
}
static
bool eq_upd(volatile flx *a, flx& b){
    flx old = b;
    b = readx(a);
    return eq2(b, old);
}

#define raw_updx_won(as...) raw_updx_won(__func__, __LINE__, as)
static
bool (raw_updx_won)(const char *f, int l, flx n, volatile flx *a, flx& e){
    /* flx r = *a; */
    /* if(eq2(r, *e)){ */
    /*     *a = n; */
    /*     return true; */
    /* } */
    /* *e = r; */

    /* if(atomic_compare_exchange_strong((_Atomic volatile flx *) a, e, n)){ */
    /*     log(1, "%:%- %(% => %)", f, l, (void *) a, *e, n); */
    /*     *e = n; */
    /*     return true; */
    /* } */
    (void) a;
    if(__atomic_compare_exchange(a, &e, &n, false,
                                 __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)){
        log(1, "%:%- %(% => %)", f, l, (void *) a, e, n);
        e = n;
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
bool (updx_won)(const char *f, int l, flx n, volatile flx *a, flx& e){
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
    flx p = readx(&a->p);
    if(p.st == COMMIT || a.gen != p.gen)
        return -1;
    return (lflist_del_upd)(a, p, a.gen);
}

err (lflist_jam_upd)(uptr ng, flx a, type *t){
    flx p = readx(&a->p);
    if(a.gen != p.gen)
        return -1;
    return (lflist_del_upd)(a, p, ng);
}

#include <pthread.h>
static flat
err (lflist_del_upd)(flx a, flx& p, uptr ng){
    flx n = readx(&a->n);
    flx np, pn = {};
    bool aborted = !abort_enq(a, p, pn);
    if(p.gen != a.gen || p.st == COMMIT)
        goto done;

    for(;;){
        if(help_next(a, n, np, aborted))
            goto done;
        assert(np == a && np.st != COMMIT);

        if(help_prev(a, p, pn)){
            if(p.st == COMMIT || a.gen != p.gen)
                goto done;
            if(!eq_upd(&a->n, n))
                continue;
            assert(n.st == COMMIT);
            break;
        }
        assert(pn == a && pn.st == RDY);

        if(!updx_won(flx(n, COMMIT, n.gen + 1), &a->n, n))
            continue;

        if(updx_won(flx(n, pn.st, pn.gen + 1), &p->n, pn))
            break;
    }

    {
        flx np_alt = rup(np, .st = ABORT);
        if(!updx_won(flx(p, RDY, np.gen + n.nil), &n->p, np))
            updx_won(flx(p, RDY, np.gen + n.nil), &n->p, np_alt);
    }
done:
    while(a.gen == p.gen){
        if(ng == a.gen && p.st == COMMIT)
            return -1;
        if(updx_won(rup(p, .st = COMMIT, .pt = 0, .gen = ng), &a->p, p))
            return 0;
    }
    return -1;
}

static
err (help_next)(flx a, flx& n, flx& np, bool enq_aborted){
    for(;;){
        if(!n)
            return -1;

        np = readx(&n->p);
        for(;;){
            if(np == a){
                if(help_enq(a, n, np))
                    break;
                return 0;
            }
            if(!eq_upd(&a->n, n))
                break;
            if(n.st == COMMIT || (n.st == ADD && (enq_aborted || a->p.gen != a.gen)))
                return EARG("n abort %:%:%", a, n, np);
            assert(*np && (np->st != COMMIT));

            updx_won(flx(a, RDY, np.gen + n.nil), &n->p, np);
        }

    }
}

static
err (help_prev)(flx a, flx& p, flx& pn){
    for(;;){
        if(!pn)
            goto newp;
        for(;;){
        readp:
            if(!eq_upd(&a->p, p))
                break;
            if(pn != a)
                return EARG("p abort %:%:%", a, p, pn);
        newpn:
            if(pn.st != COMMIT)
                return 0;

        readpp:;
            flx pp = readx(&p->p);
        newpp:;
            if(!pp || pp.st == COMMIT)
                goto readp;

            flx ppn = readx(&pp->n);
            for(;;){
                if(!eq_upd(&p->p, pp))
                    goto newpp;
                if(ppn == a){
                    if(!updx_won(flx(pp, RDY, p.gen + a.nil), &a->p, p))
                        goto newp;
                    pn = ppn;
                    goto newpn;
                }
                if(ppn != p)
                    goto readpp;
                if(!updx_won(flx(a,
                                ppn.st == COMMIT ? RDY : COMMIT,
                                pn.gen + 1),
                            &p->n, pn))
                    break;
                if(pn.st != COMMIT)
                    return 0;

                updx_won(flx(a, ppn.st, ppn.gen + 1), &pp->n, ppn);
            }
        }
    newp:;
        if(!a.nil && (p.st == COMMIT || p.gen != a.gen))
            return EARG("Gen p abort %:%", a, p);

        pn = readx(&p->n);
    }
}

static
err help_enq(flx a, flx& n, flx& np){
    if((np.st != ADD && np.st != ABORT)
       || n.st != RDY)
        return 0;

    flx nn = readx(&n->n);
    if(nn.st != ADD)
        return 0;
    assert(nn.nil);

    flx nnp = readx(&nn->p);
    if(nnp != a)
        return 0;
    if(!eq_upd(&a->n, n))
        return -1;
    updx_won(flx(n, RDY, nnp.gen + 1), &nn->p, nnp);
    return 0;
}

static
err abort_enq(flx a, flx& p, flx& pn){
    bool abort_on_pn_change = false;
    for(;;){
        if(p.st == COMMIT || p.gen != a.gen)
            return -1;
        pn = readx(&p->n);
        if(p.st == RDY)
            return -1;
        for(;;){
            if(pn == a)
                return -1;
            if(abort_on_pn_change)
                return 0;
            if(p.st == ADD){
                if(!updx_won(rup(p, .st = ABORT), &a->p, p))
                    break;
            }else{
                if(!eq_upd(&a->p, p))
                    break;
                abort_on_pn_change = true;
            }

            if(!pn.nil || pn.st == COMMIT){
                if(abort_on_pn_change)
                    return 0;
                break;
            }

            if(updx_won(rup(pn, .gen++), &p->n, pn))
                return 0;
        }
    }
}

err (lflist_enq)(flx a, type *t, lflist *l){
    return lflist_enq_upd(a.gen + 1, a, t, l);
}

err (lflist_enq_upd)(uptr ng, flx a, type *t, lflist *l){
    flx p = readx(&a->p);
    if(p.st != COMMIT || p.gen != a.gen)
        return -1;
    flx n = readx(&a->n);

    flx nil(l);
    flx nilp = readx(&l->nil.p);
    flx nilpn = {};

    bool won = false;
    for(;;){
        if(help_prev(nil, nilp, nilpn)){
            if(nilpn != nil){
                dbg volatile flanchor *npn = nilpn;
                assert((npn->n == nil
                        && npn->n.st == ADD
                        && (npn->p.st == ADD || npn->p.st == ABORT)
                        && npn->p == nilp)
                        || !eq2(l->nil.p, nilp));
                
                updx_won(flx(nilpn, RDY, nilp.gen + 1), &nil->p, nilp);
                nilpn = (flx){};
            }
            continue;
        }

        if(!raw_updx_won(flx(nilp, ADD, ng), &a->p, p))
            return -!won;

        /* TODO: avoid gen updates? */
        while(!won && !updx_won(flx(nil, ADD, n.gen + 1), &a->n, n))
            if(n.st != COMMIT || !eq_upd(&a->p, p))
                return 0;
        won = true;

        if(updx_won(flx(a, RDY, nilpn.gen + 1), &nilp->n, nilpn))
            break;
    }

    updx_won(flx(a, RDY, nilp.gen + 1), &nil->p, nilp);

    return 0;
}

flx (lflist_deq)(type *t, lflist *l){
    flx nil(l);
    flx p = readx(&nil->p);
    for(;;){
        /* TODO: flinref */
        if(p.nil)
            return (flx){};
        flx r(p);
        if(!eq_upd(&nil->p, p))
            continue;
        if(!lflist_del(r, t))
            return fake_linref_up(), r;
        must(!eq_upd(&nil->p, p));
    }
}

constfun
volatile flanchor *flptr(flx a){
    assert(!a.nil);
    return a;
}

flx flx_of(flanchor *a){
    return flx(a);
}

bool (flanchor_unused)(flanchor *a){
    return a->p.st == COMMIT;
}

/* TODO: printf isn't reentrant. Watch CPU usage for deadlock upon assert
   print failure.  */
bool flanc_valid(flanchor *a){
    if(!randpcnt(FLANC_CHECK_FREQ) || pause_universe())
        return false;

    dbg flx
        p = readx(&a->p),
        n = readx(&a->n);

    if(!p){
        assert(p.st == COMMIT);
        assert(n.st == COMMIT || n.st == ADD);
        if(n)
            assert(n->p != a);

        goto done;
    }

    if(!n){
        assert(n.st == COMMIT);
        if(p)
            assert(p->n != a);
        goto done;
    }
    {

    dbg flx
        pn = readx(&p->n),
        pp = readx(&p->p),
        np = readx(&n->p),
        nn = n->n;

    bool nil = false;
    if(np == a)
        nil = np.nil;
    else if(np && np->p == a)
        nil = np->p.nil;

    assert(n != p || n.nil || nil || (p.st == ADD || p.st == ABORT));

    if(nil){
        assert(p.st == RDY && n.st == RDY);
        assert((np == a && np.nil)
               || (np->p == a &&
                   np->p.st != COMMIT &&
                   np->n == n &&
                   np->n.st == COMMIT));
        dbg flx pnn = pn->n;
        dbg flx pnp = pn->p;
        assert((pn == a && pn.nil)
               || (pnn == a &&
                   pnn.nil &&
                   pnn.st == ADD &&
                   (pnp.st == ADD || pnp.st == ABORT) &&
                   pnp == p));
        goto done;
    }

    if(n.st == COMMIT){
        if(nn && (pn == a))
            assert(nn->p != a);
    }
    if(n.st == ADD)
        assert(n.nil);
    assert(np == a
           || pn != a
           || ((p.st == ADD || p.st == ABORT) &&
               n.st == ADD &&
               n.nil)
           || (np->p == a &&
               np->n.st == COMMIT &&
               np->p.st != COMMIT &&
               n.st == RDY));
    assert(pn == a
           || n.st == COMMIT
           || (p.st == COMMIT && n.st == ADD)
           || ((p.st == ADD || p.st == ABORT) &&
               n.st == ADD &&
               n.nil &&
               np != a));
    if(pn == a)
        assert(p.st != COMMIT);
    if(np == a && p.st != COMMIT && n.st != COMMIT)
        assert(pn == a);
    }    
done:
    /* Sniff out unpaused universe or reordering weirdness. */
    assert(eq2(a->p, p));
    assert(eq2(a->n, n));

    resume_universe();
    return true;
}

#endif
