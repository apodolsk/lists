#ifndef FAKELOCKFREE

#define FLANC_CHECK_FREQ E_DBG_LVL ? 50 : 0

using namespace std;

struct lflist;
struct flanchor;

struct flref{
    flanchor *ptr;
    uptr gen;

    flref() = default;
    flref(flanchor *a);

    operator flanchor*() const{
        return ptr;
    }

    flanchor* operator->() const{
        return ptr;
    }
};

extern "C"{
/* This version of lflist just assumes type stability. In general, the
   linref stuff just adds trivial line noise to lflist. */
    struct type;
    
    extern void fake_linref_up(void);
    
    err lflist_enq_upd(uptr ng, flref a, type *t, lflist *l);
    err lflist_enq(flref a, type *t, lflist *l);

    err lflist_del_upd(uptr ng, flref a, type *t);
    err lflist_del(flref a, type *t);
    err lflist_jam(flref a, type *t);

    flref lflist_deq(type *t, lflist *l);

    bool flanc_valid(flanchor *a);
}

/* The states can mean different things for flanchor::n and flanchor::p.

   A->p.st == COMMIT iff A is enqable. del() and enq() return 0 iff they
   can set and unset p.st = COMMIT, respectively. 

   A->p.st == RDY means nothing except the absence of other
   states. Namely, the absence of COMMIT.

   A->p.st == ADD iff A->p hasn't been written since the last enq(A). In
   (only) this case, del(A->p) must check whether the enq(A) is incomplete
   and needs helped. Otherwise, it's treated like RDY.
   - ADD is just an optimization. The point is that, if A->p.st != ADD,
     then del(A->p) can avoid the cost of such a check. 
   
   A->p.st == ABORT iff a del(A) tried to abort an enq(A). It's possible
   that this del(A) "spuriously" set ABORT after enq(A) finished, so ABORT
   is treated like RDY by every function except enq(A). It's a "harmless"
   signal to enq(A).

   ------

   A->n.st == COMMIT iff a del(A) committed to writing "P"->n. del(A->n)
   takes it as a signal to try and help del(A) before committing to
   writing A->n.

   A->n.st == RDY iff no del(A) is "committed". A->pt can only be written
   when A->n.st == RDY. Implies A->p.st != COMMIT.

   A->n.st == ADD iif A->n hasn't been written since enq(A). Exactly
   analogous to A->p.st == ADD.

   A->n.st == ABORT is currently unused. There's a good hypothetical use
   for it, but it'd also be an optimization.

*/
enum flst{
    COMMIT,
    RDY,
    ADD,
    ABORT,
};

struct flx{
    flst st:2;
    uptr nil:1;
    uptr pt:WORDBITS-3;
    
    uptr gen;

    flx() = default;
    flx(flx x, flst st, uptr gen):
        st(st),
        nil(x.nil),
        pt(x.pt),
        gen(gen)
        {}

    explicit flx(lflist *l);
    flx(flref r);

    operator flanchor*() const{
        return (flanchor *)(uptr)(pt << 3);
    }
    flanchor* operator->() const{
        return *this;
    }

    /* NB: operator== is undefined. Instead, == implicitly converts flx
       arguments to flanchor *, effectively making a comparison against
       flx::pt. "Full" comparison against state bits, etc. is done via
       eq2 and eq_upd. */
};

/* NB: load is used to convert atomic<flx> to flx, e.g. in flx np =
   ((flanchor *) n)->p.

   The absence of a 16B MOV on x86 forces atomic<flx>::load to use an
   expensive CAS2(this, 0, 0). I redefine load to make non-atomic reads,
   which suffice. */
class half_atomic_flx : public atomic<flx>{
    flx load(memory_order order = memory_order_seq_cst) const{
        flx r;
        typedef aliasing uptr auptr;
        ((auptr *) &r)[0] = ((volatile auptr *) this)[0];
        ((auptr *) &r)[1] = ((volatile auptr *) this)[1];
        return r;
    }
};

struct flanchor{
    half_atomic_flx n;
    half_atomic_flx p;
} align(2 * sizeof(dptr));

struct lflist{
    flanchor nil;
};

static err help_next(flx a, flx& n, flx& np, bool enq_aborted);
static err help_prev(flx a, flx& p, flx& pn);

static err help_enq(flx a, flx& n, flx& np);
static err abort_enq(flx a, flx& p, flx& pn);

#define to_pt(flanc) (((uptr) (flanc)) >> 3)

flref::flref(flanchor *a):
    ptr(a),
    gen(flx(a->p).gen){}

flx::flx(lflist *l):
    st(),
    nil(1),
    pt(to_pt(&l->nil)),
    gen()
{}

flx::flx(flref r):
    st(),
    nil(),
    pt(to_pt(r.ptr)),
    gen(r.gen)
{}

#undef eq2
#include <cstring>
template<class T>
bool eq2(T a, T b){
    return !memcmp(&a, &b, sizeof(dptr));
}
static
bool eq_upd(atomic<flx> *a, flx& b){
    flx old = b;
    b = *a;
    return eq2(b, old);
}


static inline constexpr
const char *flststr(flst s){
    return (const char *[]){"COMMIT", "RDY", "ADD", "ABORT"}[s];
}
#define raw_updx_won(as...) raw_updx_won(__func__, __LINE__, as)
static
bool (raw_updx_won)(const char *f, int l, flx n, atomic<flx>* a, flx& e){
    
    fuzz_atomics();

    if(a->compare_exchange_strong(e, n)){
        /* printf("%lu %s:%d- %p({%p:%lu %s, %lu} => {%p:%lu %s, %lu})\n", */
        /*        get_dbg_id(), */
        /*        f, l, a, */
        /*        (volatile flanchor *) e, e.nil, flststr(e.st), e.gen, */
        /*        (volatile flanchor *) n, n.nil, flststr(n.st), n.gen); */
        e = n;
        return true;
    }
    return false;
}

#define updx_won(as...) updx_won(__func__, __LINE__, as)
static
bool (updx_won)(const char *f, int l, flx n, atomic<flx> *a, flx& e){
    assert(!eq2(n, e));
    assert(aligned_pow2((flanchor *) n, alignof(flanchor)));
    assert(n || n.st == COMMIT);
    assert(n.nil || n != cof_aligned_pow2(a, flanchor));

    bool w = (raw_updx_won)(f, l, n, a, e);
    assert((flanc_valid(cof_aligned_pow2(a, flanchor)), 1));
    return w;
}

err (lflist_del)(flref a, type *t){
    return (lflist_del_upd)(a.gen, a, t);
}

err (lflist_jam)(flref a, type *t){
    return lflist_del_upd(a.gen + 1, a, t);
}

flat
err (lflist_del_upd)(uptr ng, flref a, type *t){
    flx n = a->n,
        np;
    flx p = a->p,
        pn = {};
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
        if(updx_won(flx((flx){}, COMMIT, ng), &a->p, p))
            return 0;
    }
    return -1;
}

static
err (help_next)(flx a, flx& n, flx& np, bool enq_aborted){
    for(;;){
        if(!n)
            return -1;
        
        np = n->p;
        for(;;){
            if(np == a){
                if(help_enq(a, n, np))
                    break;
                return 0;
            }
            if(!eq_upd(&a->n, n))
                break;
            if(n.st == COMMIT || (n.st == ADD && (enq_aborted ||
                                                  flx(a->p).gen != a.gen)))
                return EARG("n abort %:%:%", a, n, np);
            assert(np && (np.st != COMMIT));

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
            flx pp = p->p;
        newpp:;
            if(!pp || pp.st == COMMIT)
                goto readp;

            flx ppn = pp->n;
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

        pn = p->n;
    }
}

static
err help_enq(flx a, flx& n, flx& np){
    if((np.st != ADD && np.st != ABORT)
       || n.st != RDY)
        return 0;

    flx nn = n->n;
    if(nn.st != ADD)
        return 0;
    assert(nn.nil);

    flx nnp = nn->p;
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
        pn = p->n;
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

err (lflist_enq)(flref a, type *t, lflist *l){
    return lflist_enq_upd(a.gen + 1, a, t, l);
}

err (lflist_enq_upd)(uptr ng, flref a, type *t, lflist *l){
    assert(ng != a.gen);
    
    flx p = a->p;
    if(p.st != COMMIT || p.gen != a.gen)
        return -1;
    flx n = a->n;

    flx nil(l);
    flx nilp = l->nil.p;
    flx nilpn = {};

    bool won = false;
    for(;;){
        if(help_prev(nil, nilp, nilpn)){
            assert(nilpn != nil);
            updx_won(flx(nilpn, RDY, nilp.gen + 1), &nil->p, nilp);
            nilpn = (flx){};
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

flref (lflist_deq)(type *t, lflist *l){
    flx nil(l);
    flx p = nil->p;
    for(;;){
        /* TODO: flinref */
        if(p.nil)
            return (flref){};
        flref r(p);
        if(!eq_upd(&nil->p, p))
            continue;
        if(!lflist_del(r, t))
            return fake_linref_up(), r;
        must(!eq_upd(&nil->p, p));
    }
}

bool (flanchor_unused)(flanchor *a){
    return flx(a->p).st == COMMIT;
}

/* TODO: printf isn't reentrant. Watch CPU usage for deadlock upon assert
   print failure.  */
bool flanc_valid(flanchor *_a){
    
    if(!randpcnt(FLANC_CHECK_FREQ) || pause_universe())
        return false;
    
    /* Here comes something nasty. atomic<flx> disallows direct member
       access, as in "n->p.st". It's suuuper inconvenient here. */
    struct owned_flanchor;
    struct owned_flx{
        flst st:2;
        uptr nil:1;
        uptr pt:WORDBITS-3;
    
        uptr gen;

        operator owned_flanchor*() const{
            return (owned_flanchor *)(uptr)(pt << 3);
        };
        owned_flanchor* operator->() const{
            return *this;
        };
    };

    struct owned_flanchor{
        owned_flx n;
        owned_flx p;
    };

    owned_flanchor *a = (owned_flanchor *) _a;
    
#define flanchor owned_flanchor
#define flx owned_flx

    dbg flx
        p = a->p,
        n = a->n;

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
        pn = p->n,
        pp = p->p,
        np = n->p,
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
    /* return true; */
}

#endif
