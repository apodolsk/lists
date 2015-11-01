#pragma once

#ifdef FAKELOCKFREE
#include <fakelflist.h>
#else

#include <nalloc.h>

typedef struct flx flx;
typedef volatile struct flanchor flanchor;
typedef enum flstate flstate;

typedef struct markp{
    uptr nil:1;
    enum flstate{
        FL_ADD,
        FL_RDY,
        FL_ABORT,
        FL_COMMIT
    } st:2;
    uptr pt:WORDBITS-3;
} markp;

#define FLANC_VALID 0b10
typedef struct{
    uptr validity: 2;
    uptr gen: WORDBITS - 2;
} markgen;

struct flx{
    union {
        /* Only useful for gdb. */
        flanchor *mp;
        markp;
        /* C11 (6.6) doesn't require casting addresses in constant
           expressions. GCC/CLANG do as an undocumented extension, but no
           computation from a cast may be truncated (as it would be if
           writing .pt). The only documentation of this is a mailing list
           post
           (http://lists.cs.uiuc.edu/pipermail/cfe-dev/2013-May/029450.html)
           attributing this to relocation troubles. Nevertheless, an
           untruncated cast can be masked to get the same effect, as in
           LFLIST(). */
        uptr constexp;
    };
    markgen;
} align(sizeof(dptr));
#define mpt(flanc) ((uptr) (flanc) >> 3)
#define FLX(as...) ((flx){as})

struct flanchor{
    volatile flx n;
    volatile flx p;
};
#define FLANCHOR(list)                                                  \
    {.n.constexp = (list) ? 1 + (FL_RDY << 1) + (uptr) (list) : FL_COMMIT << 1, \
     .n.validity = FLANC_VALID,                                                 \
     .p.constexp = (list) ? 1 + (FL_RDY << 1) + (uptr) (list) : FL_COMMIT << 1, \
     .p.validity = FLANC_VALID,                                                 \
            }

CASSERT(offsetof(list, nil) == 0);

typedef volatile struct lflist{
    flanchor nil;
}lflist;
#define LFLIST(l, elem)                                                 \
    {{.n = {.constexp =                                     \
            (elem) ? 2 + (uptr) (elem) : 3 + (uptr) (l),    \
            .validity = FLANC_VALID},                       \
      .p = {.constexp =                                     \
            (elem) ? 2 + (uptr) (elem) : 3 + (uptr) (l),    \
            .validity = FLANC_VALID},                       \
    }}

#endif  /* FAKELOCKFREE */

flx flx_of(flanchor *a);
flanchor *flptr(flx a);

err lflist_del(flx a, type *t);

err lflist_enq(flx a, type *t, lflist *l);
flx lflist_deq(type *t, lflist *l);
err lflist_jam(flx a, type *t);

err lflist_jam_upd(uptr ng, flx a, type *t);
err lflist_enq_upd(uptr ng, flx a, type *t, lflist *l);

flx lflist_peek(lflist *l);
flx lflist_next(flx p, lflist *l);

bool flanchor_unused(flanchor *a);

bool lflist_valid(flx a);
bool flanchor_valid(flx ax);
void flanchor_ordered_init(flanchor *a, uptr g);

void report_lflist_profile(void);

#ifndef FAKELOCKFREE

static inline
const char *flstatestr(flstate s){
    return (const char *[]){"ADD", "RDY", "ABORT", "COMMIT"}[s];
}

#define pudef (flx, "{%:%:%, %:%}", (void *)(uptr)(a->pt << 3), (uptr) a->nil, \
               flstatestr(a->st), (uptr) a->gen, (uptr) a->validity)
#include <pudef.h>
#define pudef (flanchor, "n:%, p:%", a->n, a->p)
#include <pudef.h>
#define pudef (lflist, "LIST(%)", a->nil)
#include <pudef.h>

#endif

#ifndef LOG_LFLISTM
#define LOG_LFLISTM 0
#endif

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
