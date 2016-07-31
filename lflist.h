#pragma once

typedef struct{
    volatile struct flanchor *ptr;
    uptr gen;
}flref;

#ifdef FAKELOCKFREE
#include <fakelflist.h>
#else

#include <nalloc.h>

enum flst{
    COMMIT,
    RDY,
    ADD,
    ABORT,
};

struct flx{
    union{
        struct{
            enum flst st:2;
            uptr nil:1;
            uptr pt:WORDBITS-3;
        };
        uptr constexp;
    };
    
    uptr gen;
};
typedef struct flx flx;

typedef volatile struct flanchor flanchor;
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


typedef volatile struct lflist{
    struct flanchor nil;
}lflist;
#define LFLIST(l, elem){                                                \
        {.n = {.constexp = (elem)                                       \
               ? 1 + (uptr) (elem)                                      \
               : 5 + (uptr) (l)},                                       \
         .p = {.constexp = (elem)                                       \
               ? (uptr) (elem)                                          \
               : 5 + (uptr) (l)},                                       \
    }}

/* static inline constfun */
/* flanchor *flptr(flx a){ */
/*     assert(!a.nil); */
/*     return (flanchor *)(uptr)(a.pt << 3); */
/* } */

/* static inline */
/* flx flx_of(flanchor *a){ */
/*     return (flx){.pt = ((uptr) a) >> 3, .gen = a->p.gen}; */
/* } */

static inline constfun
flanchor *flptr(flref a){
    return a.ptr;
}

static inline
flref flref_of(flanchor *a){
    return (flref){.ptr = a, .gen = a->p.gen};
}

#endif  /* FAKELOCKFREE */


flanchor *flptr(flref a);
flref flref_of(flanchor *a);

/* TODO: replace flx_of() with flarg() to pass the complete value of
   a->p to enq/deq/etc and omit the redundant a->p read there. */

err lflist_enq_upd(uptr ng, flref a, type *t, lflist *l);
err lflist_enq(flref a, type *t, lflist *l);

flref lflist_deq(type *t, lflist *l);

err lflist_del(flref a, type *t);
err lflist_jam_upd(uptr ng, flref a, type *t);
err lflist_jam(flref a, type *t);

bool mgen_upd_won(uptr g, flref a, type *t);

flref lflist_peek(lflist *l);
flref lflist_next(flref p, lflist *l);

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

#define pudef (struct flx,                                              \
               "{%:% %, %}", (void *)(uptr)(a->pt << 3), (uptr) a->nil, \
               flstatestr(a->st), (uptr) a->gen)
#include <pudef.h>
#define pudef (struct flanchor, "n:%, p:%", a->n, a->p)
#include <pudef.h>
#define pudef (struct lflist, "LIST(%)", a->nil)
#include <pudef.h>

#endif

#ifndef LOG_LFLISTM
#define LOG_LFLISTM 0
#endif

#define mgen_upd_won(g, a, t) trace(LFLISTM, 2, mgen_upd_won, PUN(mgen, g), a, t)

#define lflist_jam_upd(ng, a, t)                                        \
    linref_account(0, trace(LFLISTM, 2, lflist_jam_upd, PUN(uptr, ng), a, t))

#define lflist_enq_upd(ng, a, t, l)                                     \
    linref_account(0, trace(LFLISTM, 2, lflist_enq_upd, PUN(uptr, ng), a, t, l))


#define lflist_del(as...) linref_account(0, trace(LFLISTM, 2, lflist_del, as))
#define lflist_deq(as...)                       \
    linref_account(flptr(account_expr) ? 1 : 0, trace(LFLISTM, 2, lflist_deq, as))
#define lflist_enq(as...) linref_account(0, trace(LFLISTM, 2, lflist_enq, as))
#define lflist_jam(as...) linref_account(0, trace(LFLISTM, 2, lflist_jam, as))
#define lflist_peek(as...) trace(LFLISTM, 2, lflist_peek, as)
#define lflist_next(as...) trace(LFLISTM, 2, lflist_next, as)
