#ifndef FAKELOCKFREE

#include <lflist.hpp>

#define FLANC_CHECK_FREQ E_DBG_LVL ? 50 : 0

using namespace std;

/* The flx::st can mean different things for flanchor::n and flanchor::p.

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


/* Non-const references are intentional. Functions reading memory "return"
   up-to-date values of the referenced variables "tracking" that memory.
*/

static bool truly_eq(flx a, flx b);
static bool changed(atomic<flx> *src, flx& read);

static bool updx_won(flx n, atomic<flx>* a, flx& e);

static err help_next(flx a, flx& n, flx& np, bool enq_aborted);
static err help_prev(flx a, flx& p, flx& pn);

static err help_enq(flx a, flx& n, flx& np);
static err abort_enq(flx a, flx& p, flx& pn);

static bool updx_valid(flx n, atomic<flx>* a, flx e);
static void report_updx_won(flx n, atomic<flx>* a, flx e,
                            const char *func, int line);

/* As noted, == on flx compares only flx::pt. */
static
bool truly_eq(flx a, flx b){
    return !memcmp(&a, &b, sizeof(dptr));
}

static
bool changed(atomic<flx> *src, flx& read){
    flx old = read;
    read = *src;
    return !truly_eq(read, old);
}

static
bool updx_won(flx n, atomic<flx>* a, flx& e){
    bool won = a->compare_exchange_strong(e, n);
    if(won)
        e = n;
    return won;
}

#define trace_updx(n, a, e) ({                                      \
            flx _old = e;                                           \
            bool _won = (updx_won)(n, a, e);                        \
            if(_won)                                                \
                report_updx_won(n, a, _old, __func__, __LINE__);    \
            _won;                                                   \
        })
#define raw_updx_won(n, a, e) trace_updx(n, a, e)
#define updx_won(n, a, e) (assert(updx_valid(n, a, e)), trace_updx(n, a, e))

err (lflist_del)(flref a, type *t){
    return (lflist_del_upd)(a.gen, a, t);
}

err (lflist_jam)(flref a, type *t){
    return (lflist_del_upd)(a.gen + 1, a, t);
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
            if(changed(&a->n, n))
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
        flx np_aborted = rup(np, .st = ABORT);
        if(!updx_won(flx(p, RDY, np.gen + n.nil), &n->p, np))
            updx_won(flx(p, RDY, np.gen + n.nil), &n->p, np_aborted);
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
            if(changed(&a->n, n))
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
            if(changed(&a->p, p))
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
                if(changed(&p->p, pp))
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
    if(changed(&a->n, n))
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
                if(changed(&a->p, p))
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

        while(!won && !updx_won(flx(nil, ADD, n.gen + 1), &a->n, n))
            if(n.st != COMMIT || changed(&a->p, p))
                return 0;
        won = true;

        if(updx_won(flx(a, RDY, nilpn.gen + 1), &nilp->n, nilpn))
            break;
    }

    updx_won(flx(a, RDY, nilp.gen + 1), &nil->p, nilp);

    return 0;
}

flref (lflist_unenq)(type *t, lflist *l){
    flx nil(l);
    flx p = nil->p;
    for(;;){
        if(p.nil)
            return (flref){};
        flref r(p);
        if(changed(&nil->p, p))
            continue;
        if(!lflist_del(r, t))
            return fake_linref_up(), r;
        must(changed(&nil->p, p));
    }
}

static
bool updx_valid(flx n, atomic<flx>* a, flx e){
    assert(!truly_eq(n, e));
    assert(n || n.st == COMMIT);
    assert(n.nil || n != cof_aligned_pow2(a, flanchor));
    return true;
}

static inline constexpr
const char *flststr(flst s){
    return (const char *[]){"COMMIT", "RDY", "ADD", "ABORT"}[s];
}
static 
void report_updx_won(flx n, atomic<flx>* a, flx e, const char *f, int l){
    /* printf("%lu %s:%d- %p({%p:%lu %s, %lu} => {%p:%lu %s, %lu})\n", */
    /*        get_dbg_id(), */
    /*        f, l, a, */
    /*        (volatile flanchor *) e, e.nil, flststr(e.st), e.gen, */
    /*        (volatile flanchor *) n, n.nil, flststr(n.st), n.gen); */
    assert(flanc_valid(cof_aligned_pow2(a, flanchor)), 1);
}

/* TODO: printf isn't async-signal-safe. Watch CPU usage for deadlock upon
   printf call in assert(). */
bool flanc_valid(flanchor *_a){
    if(!randpcnt(FLANC_CHECK_FREQ) || pause_universe())
        return false;
    
    /* Here comes something nasty. atomic<flx> disallows direct member
       access, as in "n->p.st". It's suuuper inconvenient here. */
    struct flanchor_na;
    struct flx_na : flx{
        explicit operator flanchor*();
        operator flanchor_na*() const{
            return (flanchor_na *)(uptr)(pt << 3);
        };
        flanchor_na* operator->() const{
            return *this;
        };
    };
    struct flanchor_na{
        flx_na n;
        flx_na p;
    };

    flanchor_na *a = (flanchor_na *) _a;
    
    dbg flx_na
        p = a->p,
        n = a->n;

    dbg flx_na
        pn = p ? p->n : (flx_na){},
        pp = p ? p->p : (flx_na){},
        np = n ? n->p : (flx_na){},
        nn = n ? n->n : (flx_na){};

    bool nil = false;
    if(np == a)
        nil = np.nil;
    else if(np && np->p == a)
        nil = np->p.nil;

    assert(n != p
           || n.nil
           || nil
           || (p.st == ADD || p.st == ABORT));

    if(nil){
        assert(p.st == RDY && n.st == RDY);
        assert((np == a && np.nil)
               || (1
                   && np->p == a
                   && np->p.st != COMMIT
                   && np->n == n
                   && np->n.st == COMMIT));
        assert((pn == a && pn.nil)
               || (1
                   && pn->n == a
                   && pn->n.nil
                   && pn->n.st == ADD
                   && (pn->p.st == ADD || pn->p.st == ABORT)
                   && pn->p == p));
        goto done;
    }

    if(n.st == COMMIT && np == a)
        assert(nn->p != a);

    assert(0
           || (pn == a && np == a
               && p.st != COMMIT)

           || (pn != a && np == a
               && (1
                   /* Incomplete del(a) wrote p->n = n. */
                   && pn == n
                   && n.st == COMMIT
                   && n.st == COMMIT
                   && p.st != COMMIT
                   && pn.st != COMMIT))
           
           || (pn == a && np != a
               && n.st != COMMIT
               && p.st != COMMIT
               && (0

                   /* Incomplete enq(a) wrote p->n = a. */
                   || (1
                       && np == p
                       && n.nil
                       && n.st == ADD
                       && (p.st == ADD || p.st == ABORT)
                       && pn.st == RDY)

                   /* Incomplete del(np) wrote a->n = np->n. */
                   || (1
                       && np->p == a
                       && np->n == n
                       && np->n.st == COMMIT
                       && np->p.st != COMMIT
                       && n.st == RDY)
                   )
               )

           || (pn != a && np != a
               && n.st != RDY
               && (0
                   /* del(a) completed */
                   || p.st == COMMIT
                   
                   /* Almost-complete del(a) wrote n->p = p. */
                   || n.st == COMMIT

                   /* Incomplete enq(a) wrote a->p = p. */
                   || (p.st == ADD || p.st == ABORT)
                   )
               )
        );
done:
    /* Sniff out unpaused universe or reordering weirdness. */
    assert(truly_eq(a->p, p));
    assert(truly_eq(a->n, n));

    resume_universe();
    return true;
    /* return true; */
}


#endif
