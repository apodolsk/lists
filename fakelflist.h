#pragma once
#include <list.h>
#include <nalloc.h>
#include <pthread.h>

typedef struct{
    uptr gen;
    struct lflist *host;
}stx;

typedef struct{
    lanchor lanc;
    stx;
} flanchor;
#define FLANCHOR(list)                          \
    {LANCHOR(list), .host = list}

typedef struct {
    flanchor *a;
    uptr gen;
}flx;

typedef struct lflist{
    list l;
    pthread_mutex_t mut;
} lflist;
#define LFLIST(self, elem)                      \
    {.l = LIST(&(self)->l, elem),               \
            .mut = PTHREAD_MUTEX_INITIALIZER}

#define pudef (flx, "{%, %}", a->a, a->gen)
#include <pudef.h>
#define pudef (flanchor, "l:%, g:%", a->lanc, a->gen)
#include <pudef.h>
#define pudef (lflist, "list{%}", a->l)
#include <pudef.h>
