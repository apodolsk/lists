#define MODULE LFLISTM

#include <atomics.h>
#include <lflist.h>
#include <nalloc.h>

#ifndef FAKELOCKFREE

#define PROFILE_LFLIST 0
#define FLANC_CHECK_FREQ E_DBG_LVL ? 15 : 0
#define MAX_LOOP 0

#define ADD FL_ADD
#define ABORT FL_ABORT
#define RDY FL_RDY
#define COMMIT FL_COMMIT

static err help_next(flx a, flx *n, flx *np, markp *refn, type *t);
static err help_prev(flx a, flx *p, flx *pn,
                     markp *refp, markp *refpp, type *t);
static err lflist_del_upd(flx a, flx *p, mgen ng, type *t);

#define help_next(as...) trace(LFLISTM, 3, help_next, as)
#define help_prev(as...) trace(LFLISTM, 3, help_prev, as)
#define refupd(as...) trace(LFLISTM, 4, refupd, as)
#define flinref_down(as...) trace(LFLISTM, 5, flinref_down, as)

#undef LOG_LFLISTM
#define LOG_LFLISTM 0

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

static inline void prefetchw(volatile void *a){
    asm volatile("prefetchw %0":: "m"(*(char *) a));
}

static inline constfun
flanchor *pt(flx a){
    return (flanchor *) (uptr)(a.pt << 4);
}
static inline constfun
flanchor *mpt(markp a){
    return (flanchor *) (uptr)(a.pt << 4);
}
#define to_pt(flanc) ((uptr) (flanc) >> 4)

#define flx(markp, flstate, gen)                \
    ((flx){.nil = markp.nil, .pt = markp.pt, .st = flstate}
static inline constfun
flx fl(flx p, flstate s, uptr gen){
    return (flx){.nil=p.nil, .st=s, .pt=p.pt, .validity=FLANC_VALID, .gen=gen};
}

/* TODO: the only issue with this is a race involving validity bits:
   do_del(a) via seg_new reads a->n.markgen when it's part of a zombie
   seg, so .rsvd=0. Then a is freed anew and a valid a->n.mgen is
   read. Wild access results. It'd suffice to add another reserved bit to
   x->markp. */
static
flx readx(volatile flx *x){
    flx r;
    /* r.markp = atomic_read(&x->markp); */
    /* r.mgen = atomic_read(&x->mgen); */

    r.markp = x->markp;
    r.mgen = x->mgen;
    
    /* if(r.validity != FLANC_VALID || r.rsvd) */
    /*     r = (flx){.st=COMMIT}; */
    return r;
}

/* static */
/* flx readx(volatile flx *x){ */
/*     flx r = atomic_read2(x); */
/*     if(r.validity != FLANC_VALID || r.rsvd) */
/*         r = (flx){.st=COMMIT}; */
/*     profile_upd(&reads); */
/*     return r; */
/* } */

static
bool eqx(volatile flx *a, flx *b){
    flx old = *b;
    *b = readx(a);
    return eq2(old, *b);
}

static
bool gen_eq(mgen a, mgen ref){
    assert(ref.validity == FLANC_VALID);
    return eq(a, ref);
}

#define raw_casx_won(as...) raw_casx_won(__func__, __LINE__, as)
#include <stdatomic.h>
static
bool (raw_casx_won)(const char *f, int l, flx n, volatile flx *a, flx *e){
    /* flx r = *a; */
    /* if(eq2(r, *e)){ */
    /*     *a = r; */
    /*     return true; */
    /* } */
    /* *e = r; */
    /* return false; */
    
    if(atomic_compare_exchange_strong((_Atomic volatile flx *) a, e, n)){
        log(1, "%:%- % => % p:%", f, l, e, n, (void *) a);
        return true;
    }
    return true;
    
    /* if(cas2_won(n, a, e)){ */
    /*     log(1, "%:%- %(% => %)", f, l, (void *) a, *e, n); */
    /*     return true; */
    /* } */
    /* return true; */
    
    /* if(e->rsvd || e->validity != FLANC_VALID) */
    /*     *e = (flx){}; */
    return false;
}

#define casx_won(as...) casx_won(__func__, __LINE__, as)
static
bool (casx_won)(const char *f, int l, flx n, volatile flx *a, flx *e){
    assert(!eq2(n, *e));
    assert(aligned_pow2(pt(n), alignof(flanchor)));
    assert(pt(n) || n.st >= ABORT);
    assert(n.nil || pt(n) != cof_aligned_pow2(a, flanchor));
    assert(n.validity == FLANC_VALID && e->validity == FLANC_VALID);
    assert(!n.rsvd && !e->rsvd);
    
    bool r = (raw_casx_won)(f, l, n, a, e);

    if_dbg(flanc_valid(cof_aligned_pow2(a, flanchor)));
    return r;
}

#define updx_won(as...) updx_won(__func__, __LINE__, as)
static
bool (updx_won)(const char *f, int l, flx n, volatile flx *a, flx *e){
    if((casx_won)(f, l, n, a, e)){
        *e = n;
        return true;
    }
    return false;
}

#define updx_ok(as...) updx_ok(__func__, __LINE__, as)
static
howok (updx_ok)(const char *f, int l, flx n, volatile flx *a, flx *e){
    if((updx_won)(f, l, n, a, e))
        return WON;
    return eq2(*e, n) ? OK : NOT;
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

static
void (flinref_down)(markp a, type *t){
    return;
    if(!a.pt || a.nil)
        return;
    linref_down(mpt(a), t);
}

static
err (refupd)(flx *a, markp *held, volatile flx *src, type *t){
    if(!pt(*a))
        return -1;
    *held = a->markp;
    return 0;
    if(a->pt == held->pt)
        return 0;
    flinref_down(*held, t);

    if(a->nil || !linref_up(pt(*a), t)){
        *held = a->markp;
        return 0;
    }
    if(eqx(src, a))
        *a = (flx){};
    return -1;
}

flat
err (lflist_del)(flx a, type *t){
    assert(!a.nil);
    flx p = readx(&pt(a)->p);
    if(p.st == COMMIT)
        return -1;
    return (lflist_del_upd)(a, &p, a.mgen, t);
}

static flat
err (lflist_del_upd)(flx a, flx *p, mgen ng, type *t){
    assert(a.validity == FLANC_VALID);

    markp refn = {},
          refp = {},
          refpp = {};
    flx np,
        pn = {},
        n = readx(&pt(a)->n);
    for(;;){
        if(help_next(a, &n, &np, &refn, t))
            goto done;
        assert(pt(np) == pt(a));
        
        if(help_prev(a, p, &pn, &refp, &refpp, t)){
            if(p->st != RDY || !gen_eq(p->mgen, a.mgen))
                goto done;
            if(!eqx(&pt(a)->n, &n))
                continue;
            break;
        }
        assert(pt(pn) == pt(a) && (pn.st == RDY || pn.st == ABORT));

        if(!updx_ok(rup(n, .st=COMMIT, .gen++), &pt(a)->n, &n))
            continue;

        if(updx_ok(fl(n, pn.st, pn.gen + 1), &pt(*p)->n, &pn))
            break;
    }

    updx_ok_modst(RDY, RDY, fl(*p, np.st, np.gen + n.nil), &pt(n)->p, &np);

done:
    flinref_down(refn, t);
    flinref_down(refp, t);
    flinref_down(refpp, t);

    /* if(n.st == ADD) */
    /*     return -1; */

    ppl(1, n, *p, np, pn);
    while(p->st != ADD && gen_eq(p->mgen, a.mgen)){
        if(p->st == COMMIT && gen_eq(a.mgen, ng))
            return -1;
        flx op = *p;
        if(updx_won(rup(*p, .nil=0, .pt=0, .st=COMMIT, .mgen = ng), &pt(a)->p, p))
            return 0;
        if(op.st == ABORT)
            return -1;
    }
    return -1;
}

err (lflist_enq)(flx a, type *t, lflist *l){
    return lflist_enq_upd(a.gen + 1, a, t, l);
}

err (lflist_enq_upd)(uptr ng, flx a, type *t, lflist *l){
    assert(a.validity == FLANC_VALID);

    flx n = readx(&pt(a)->n);
    flx p = readx(&pt(a)->p);
    if(p.st != COMMIT || !gen_eq(p.mgen, a.mgen))
        return -1;
    
    flx nil = {.nil=1,
               .pt=to_pt(&l->nil)};
    if(!updx_won(fl(nil, RDY, ng), &pt(a)->p, &p))
        return -1;

    flx niln = readx(&pt(nil)->n);
    flx nilnp;
    do{
        nilnp = readx(&pt(niln)->p);
        /* fix up np? */
        while(!updx_won(fl(niln, RDY, ng), &pt(a)->n, &n))
            if(!eqx(&pt(a)->p, &p))
                return -1;
    }while(!updx_won(fl(a, RDY, niln.gen + 1), &pt(nil)->n, &niln));

    /* TODO: ref */
    while(!upd_won(fl(a, RDY, nilnp.gen)), &pt(n)->p, &nilnp)
        if(!gen_eq(mpgen, nilnp.mgen))
            return -1;

    return 0;
}

/* err (lflist_enq_upd)(uptr ng, flx a, type *t, lflist *l){ */
/*     assert(a.validity == FLANC_VALID); */


/*     flx n = readx(&pt(a)->n); */
/*     flx ap = readx(&pt(a)->p); */
/*     if(ap.st != COMMIT || !gen_eq(ap.mgen, a.mgen)) */
/*         return -1; */
    
/*     flx nil = {.nil=1, */
/*                .st=ADD, */
/*                .pt=to_pt(&l->nil), */
/*                .validity=FLANC_VALID, */
/*                .gen=n.gen + 1}; */
/*     flx p = readx(&pt(nil)->p), */
/*         pn = {}; */
/*     markp refp = {}, */
/*           refpp = {}; */

/*     muste(help_prev(nil, &p, &pn, &refp, &refpp, t)); */

/*     bool won = false; */
/*     if(!upd2_won(fl(p, ADD, ap.gen), &pt(a)->p, &ap)) */
/*         goto done; */
/*     won = true; */

/*     while(!updx_won(fl(nil, ADD, n.gen + 1), &pt(a)->n, &n)) */
/*         if(!eq(pt(a)->p, ap)) */
/*             goto done; */

/*     while(!updx_won(fl(a, umax(pn.st, RDY), pn.gen + 1), */
/*                     &pt(p)->n, */
/*                     &pn)){ */
/*         muste(help_prev(nil, &p, &pn, &refp, &refpp, t)); */
/*         if(!upd2_won(fl(p, ADD, ap.gen), &pt(a)->p, &ap)) */
/*             goto done; */
/*     } */
/*     casx_won(fl(a, RDY, p.gen + 1), &l->nil.p, &p); */
/*     casx_won(rup(ap, .st=RDY), &pt(a)->p, &ap); */
    
/* done:     */
/*     flinref_down(refp, t); */
/*     flinref_down(refpp, t); */
/*     return -!won; */
/* } */

err (lflist_jam)(flx a, type *t){
    return lflist_jam_upd(a.gen + 1, a, t);
}

/* TODO: need to take flinref on p in pn-write case. Not a problem while
   the only consumer of jam_upd is segalloc, with guaranteed mem validity.  */
/* TODO: haven't seriously tried to optimize here. */
err (lflist_jam_upd)(uptr ng, flx a, type *t){
    /* const mgen nmg = {.gen = ng, .validity = FLANC_VALID}; */

    return 0;
    
    /* flx p = readx(&pt(a)->p); */
    /* if(!lflist_del_upd(a, &p, nmg, t)) */
    /*     return 0; */
    /* if(p.st != ADD || !gen_eq(p.mgen, a.mgen)) */
    /*     return -1; */

    /* /\* TODO: can probably avoid loop *\/ */
    /* for(;;){ */
    /*     if(n.st != ADD) */
    /*         break; */
    /*     assert(n.nil); */
    /*     if(!gen_eq(p.mgen, a.mgen)) */
    /*         return -1; */
    /*     if(p.st != ADD) */
    /*         break; */
    /*     flx pn = readx(&pt(p)->n); */
    /*     flx np = readx(&pt(n)->p); */
    /*     if(!eqx(&pt(a)->p, &p)) */
    /*         continue; */
        
    /*     if(pt(pn) == pt(a)){ */
    /*         if(pt(np) == pt(a)) */
    /*             break; */
    /*         /\* TODO: can probably break *\/ */
    /*         if(!eqx(&pt(a)->n, &n)) */
    /*             continue; */
    /*         if(updx_ok(fl(a, RDY, np.gen), &pt(n)->p, &np)) */
    /*             break; */
    /*         continue; */
    /*     } */
    /*     if(!eqx(&pt(p)->n, &pn)) */
    /*         continue; */

    /*     if(pn.st == COMMIT || pt(pn) != pt(n) || pt(np) != pt(p)) */
    /*         break; */
    /*     if(updx_ok(rup(pn, .gen++), &pt(p)->n, &pn)) */
    /*         break; */
    /* } */

    /* return lflist_del_upd(a, &p, nmg, t); */
/* skip_del:; */
/*     if_dbg(flanc_valid(pt(a))); */

/*     while(gen_eq(p.mgen, a.mgen)) */
/*         if(updx_won(rup(p, .st=COMMIT, .gen=ng), &pt(a)->p, &p)) */
/*             return 0; */
/*         else */
/*             assert(p.st != ABORT || !gen_eq(p.mgen, a.mgen)); */
/*     return -1; */
}

flx (lflist_deq)(type *t, lflist *l){
    flx a = {.nil=1,.pt=to_pt(&l->nil)};
    flx on = {};
    for(cnt lps = 0;;){
        flx np = {}, n = readx(&pt(a)->n);
        do{
            muste(help_next(a, &n, &np, (markp []){on.markp}, t));
            if(n.nil || !progress(&on, n, lps++)){
                flinref_down(n.markp, t);
                return (flx){};
            }
        }while(!eqx(&pt(a)->n, &n));
        
        flx r = {.pt=n.pt, .mgen=np.mgen};
        if(!(lflist_del_upd)(r, &np, np.mgen, t))
            return r;
    }
}

static
err (help_enq)(flx a, flx *n){
    flx nn = readx(&pt(*n)->n);
    if(nn.nil && nn.st == ADD){
        flx nnp = readx(&pt(nn)->p);
        if(pt(nnp) == pt(a)){
            if(!eqx(&pt(a)->n, n))
                return -1;
            
            casx_won(fl(*n, RDY, nnp.gen + 1), &pt(nn)->p, &nnp);
        }
    }
    return 0;
}

static
err (help_next)(flx a, flx *n, flx *np, markp *refn, type *t){
    for(;;){
        do if(!pt(*n)) return -1;
        while(refupd(n, refn, &pt(a)->n, t));

        *np = readx(&pt(*n)->p);
        for(;;){
            if(pt(*np) == pt(a) && np->st < ABORT){
                if(np->st == ADD && help_enq(a, n))
                    break;
                return 0;
            }
            if(!eqx(&pt(a)->n, n))
                break;
            if(n->st == ADD || n->st == COMMIT)
                return -1;
            assert(pt(*np) && (np->st == RDY || np->st == ADD));

            updx_ok(fl(a, np->st, np->gen + n->nil), &pt(*n)->p, np);
        }
    }
}

static
err (help_prev)(flx a, flx *p, flx *pn, markp *refp, markp *refpp, type *t){
    for(;;){
        if(!refp->pt)
            goto newp;
        for(;;){
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
            do if(!pt(pp) || pp.st != RDY)
                   goto readp;
            while(refupd(&pp, refpp, &pt(*p)->p, t));
            
            flx ppn = readx(&pt(pp)->n);
            for(;;){
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

                updx_won(fl(a, ppn.st, ppn.gen + 1), &pt(pp)->n, &ppn);
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

constfun
flanchor *flptr(flx a){
    assert(!a.nil);
    return pt(a);
}

flx flx_of(flanchor *a){
    return (flx){.pt = to_pt(a), .mgen=a->p.mgen};
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
        if(raw_casx_won(rup(p, .mgen=g), &pt(a)->p, &p))
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
    
    /* Sniff out unpaused universe or reordering weirdness. */
    assert(eq2(a->p, px));
    assert(eq2(a->n, nx));

    resume_universe();
    return true;
}

#endif
