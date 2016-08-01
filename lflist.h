#pragma once

/* NB: lflist.cpp doesn't actually include this. You're better off reading
   lflist.cpp. Interface is documented inside the extern "C" block. */

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

err lflist_enq_upd(uptr ng, flref a, type *t, lflist *l);
err lflist_enq(flref a, type *t, lflist *l);

flref lflist_deq(type *t, lflist *l);

err lflist_del_upd(uptr ng, flref a, type *t);
err lflist_del(flref a, type *t);
err lflist_jam(flref a, type *t);

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

#define lflist_enq_upd(ng, a, t, l)                                     \
    linref_account(0, trace(LFLISTM, 2, lflist_enq_upd, PUN(uptr, ng), a, t, l))


#define lflist_del_upd(ng, a, t)                                        \
    linref_account(0, trace(LFLISTM, 2, lflist_del_upd, PUN(uptr, ng), a, t))


#define lflist_del(as...) linref_account(0, trace(LFLISTM, 2, lflist_del, as))
#define lflist_deq(as...)                       \
    linref_account(flptr(account_expr) ? 1 : 0, trace(LFLISTM, 2, lflist_deq, as))
#define lflist_enq(as...) linref_account(0, trace(LFLISTM, 2, lflist_enq, as))
#define lflist_jam(as...) linref_account(0, trace(LFLISTM, 2, lflist_jam, as))
