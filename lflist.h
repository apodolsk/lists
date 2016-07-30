#pragma once

#ifdef FAKELOCKFREE
#include <fakelflist.h>
#else
#define LFLISTM 0

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

    flx(flx x, flst st, uptr gen):
        st(st),
        nil(x.nil),
        pt(x.pt),
        gen(gen)
        {};

    flx(struct lflist *l);
    flx(struct flanchor *l);

    flx() = default;
};

struct flanchor{
    flx n;
    flx p;
} align(2 * sizeof(dptr));

#define FLANCHOR(list){                                                 \
        .n.constexp = (list)                                            \
                      ? 5 + (uptr) (list)                               \
                      : 0,                                              \
        .p.constexp = (list)                                            \
                      ? 5 + (uptr) (list)                               \
                      : 0,                                              \
    }



struct lflist{
    flanchor nil;
};
#define LFLIST(l, elem){                                                \
        {.n = {.constexp = (elem)                                       \
               ? 1 + (uptr) (elem)                                      \
               : 5 + (uptr) (l)},                                       \
         .p = {.constexp = (elem)                                       \
               ? (uptr) (elem)                                          \
               : 5 + (uptr) (l)},                                       \
    }}

#endif  /* FAKELOCKFREE */

/* TODO: replace flx_of() with flarg() to pass the complete value of
   a->p to enq/deq/etc and omit the redundant a->p read there. */
flx flx_of(flanchor *a);
constfun
flanchor *flptr(flx a);

struct type;
err lflist_enq_upd(uptr ng, flx a, type *t, lflist *l);
err lflist_enq(flx a, type *t, lflist *l);

flx lflist_deq(type *t, lflist *l);

err lflist_del(flx a, type *t);
err lflist_jam_upd(uptr ng, flx a, type *t);
err lflist_jam(flx a, type *t);

bool mgen_upd_won(uptr g, flx a, type *t);

flx lflist_peek(lflist *l);
flx lflist_next(flx p, lflist *l);

bool flanchor_unused(flanchor *a);

void flanc_ordered_init(uptr g, flanchor *a);

void lflist_report_profile(void);

/* TODO: should probably change back to no-pause-universe scheme. */
bool flanc_valid(flanchor *a);

#ifndef FAKELOCKFREE

static inline
const char *flstatestr(uptr s){
    return (const char *[]){"COMMIT", "RDY", "ADD", "ABORT"}[s];
}

/* #define pudef (struct flx,                                              \ */
/*                "{%:% %, %}", (void *)(uptr)(a->pt << 3), (uptr) a->nil, \ */
/*                flstatestr(a->st), (uptr) a->gen) */
/* #include <pudef.h> */
/* #define pudef (struct flanchor, "n:%, p:%", a->n, a->p) */
/* #include <pudef.h> */
/* #define pudef (struct lflist, "LIST(%)", a->nil) */
/* #include <pudef.h> */

#endif

#ifndef LOG_LFLISTM
#define LOG_LFLISTM 0
#endif

/* #define mgen_upd_won(g, a, t) trace(LFLISTM, 2, mgen_upd_won, PUN(mgen, g), a, t) */

/* #define lflist_jam_upd(ng, a, t)                                        \ */
/*     linref_account(0, trace(LFLISTM, 2, lflist_jam_upd, PUN(uptr, ng), a, t)) */

/* #define lflist_enq_upd(ng, a, t, l)                                     \ */
/*     linref_account(0, trace(LFLISTM, 2, lflist_enq_upd, PUN(uptr, ng), a, t, l)) */


/* #define lflist_del(as...) linref_account(0, trace(LFLISTM, 2, lflist_del, as)) */
/* #define lflist_deq(as...)                       \ */
/*     linref_account(flptr(account_expr) ? 1 : 0, trace(LFLISTM, 2, lflist_deq, as)) */
/* #define lflist_enq(as...) linref_account(0, trace(LFLISTM, 2, lflist_enq, as)) */
/* #define lflist_jam(as...) linref_account(0, trace(LFLISTM, 2, lflist_jam, as)) */
/* #define lflist_peek(as...) trace(LFLISTM, 2, lflist_peek, as) */
/* #define lflist_next(as...) trace(LFLISTM, 2, lflist_next, as) */
