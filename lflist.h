#pragma once

#ifdef FAKELOCKFREE
#include <fakelflist.h>
#else

#include <nalloc.h>

typedef enum flstate flstate;
typedef struct markp{
    uptr rsvd:1;
    uptr nil:1;
    enum flstate{
        FL_ADD,
        FL_RDY,
        FL_ABORT,
        FL_COMMIT
    } st:2;
    uptr pt:WORDBITS-4;
} markp;

#define FLANC_VALID 0b10
typedef struct{
    uptr validity: 2;
    uptr gen: WORDBITS - 2;
} mgen;

typedef struct flx flx;
struct flx{
    union {
        markp;
        
        /* It's implementation-defined in C11 (6.6) whether you can cast
           addresses in constant expressions. GCC/CLANG do as an
           undocumented extension, but no computation from a cast may be
           truncated (as it would be if writing .pt). There's a mailing
           list post
           (http://lists.cs.uiuc.edu/pipermail/cfe-dev/2013-May/029450.html)
           attributing this to relocation troubles. Nevertheless, you can
           use arithmetic on an untruncated cast to get the same effect,
           as in LFLIST(). */
        uptr constexp;
    };
    mgen;
} align(sizeof(dptr));
#define FLX(as...) ((flx){as})

typedef volatile struct flanchor flanchor;
struct flanchor{
    volatile flx n;
    volatile flx p;
} align(2 * sizeof(dptr));
#define FLANCHOR(list){                                                 \
        .n.constexp = (list)                                            \
        ? 2 + (FL_RDY << 2) + (uptr) (list)                             \
        : FL_COMMIT << 2,                                               \
        .n.validity = FLANC_VALID,                                      \
        .p.constexp = (list) ?                                          \
           2 + (FL_RDY << 2) + (uptr) (list) : FL_COMMIT << 2,          \
        .p.validity = FLANC_VALID,                                      \
    }



typedef volatile struct lflist{
    flanchor nil;
}lflist;
#define LFLIST(l, elem){                                                \
        {.n = {.constexp = (elem)                                       \
               ? (FL_RDY << 2) + (uptr) (elem)                          \
               : 2 + (FL_RDY << 2) + (uptr) (l),                        \
               .validity = FLANC_VALID},                                \
         .p = {.constexp = (elem)                                       \
               ? (FL_RDY << 2) + (uptr) (elem)                          \
               : 2 + (FL_RDY << 2)  + (uptr) (l),                       \
               .validity = FLANC_VALID},                                \
    }}

#endif  /* FAKELOCKFREE */

/* TODO: replace flx_of() with flarg() to pass the complete value of
   a->p to enq/deq/etc and omit the redundant a->p read there. */
flx flx_of(flanchor *a);
flanchor *flptr(flx a);

err lflist_enq_upd(uptr ng, flx a, type *t, lflist *l);
err lflist_enq(flx a, type *t, lflist *l);

err lflist_del(flx a, type *t);
flx lflist_deq(type *t, lflist *l);

err lflist_jam_upd(uptr ng, flx a, type *t);
err lflist_jam(flx a, type *t);

bool mgen_upd_won(mgen g, flx a, type *t);

flx lflist_peek(lflist *l);
flx lflist_next(flx p, lflist *l);

bool flanchor_unused(flanchor *a);

void flanc_ordered_init(uptr g, flanchor *a);

void lflist_report_profile(void);

/* TODO: should probably change back to no-pause-universe scheme. */
bool flanc_valid(flanchor *a);

#ifndef FAKELOCKFREE

static inline
const char *flstatestr(flstate s){
    return (const char *[]){"ADD", "RDY", "ABORT", "COMMIT"}[s];
}

#define pudef (struct flx,                                              \
               "{%:%:%, %:%}", (void *)(uptr)(a->pt << 4), (uptr) a->nil, \
               flstatestr(a->st), (uptr) a->gen, (uptr) a->validity)
#include <pudef.h>
#define pudef (struct flanchor, "n:%, p:%", a->n, a->p)
#include <pudef.h>
#define pudef (struct lflist, "LIST(%)", a->nil)
#include <pudef.h>

#endif

#ifndef LOG_LFLISTM
#define LOG_LFLISTM 0
#endif

#define mgen_upd_won(g, a, t) trace(LFLISTM, 1, mgen_upd_won, PUN(mgen, g), a, t)

#define lflist_jam_upd(ng, a, t)                                        \
    linref_account(0, trace(LFLISTM, 1, lflist_jam_upd, PUN(uptr, ng), a, t))

#define lflist_enq_upd(ng, a, t, l)                                     \
    linref_account(0, trace(LFLISTM, 1, lflist_enq_upd, PUN(uptr, ng), a, t, l))


#define lflist_del(as...) linref_account(0, trace(LFLISTM, 1, lflist_del, as))
#define lflist_deq(as...)                       \
    linref_account(flptr(account_expr) ? 1 : 0, trace(LFLISTM, 2, lflist_deq, as))
#define lflist_enq(as...) linref_account(0, trace(LFLISTM, 1, lflist_enq, as))
#define lflist_jam(as...) linref_account(0, trace(LFLISTM, 1, lflist_jam, as))
#define lflist_peek(as...) trace(LFLISTM, 2, lflist_peek, as)
#define lflist_next(as...) trace(LFLISTM, 2, lflist_next, as)
