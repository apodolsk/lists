#pragma once

typedef struct lanchor{
    struct lanchor *n;
    struct lanchor *p;
} lanchor;
#define LANCHOR(l) {                            \
        (l) ? &((list *) (l))->nil : NULL,      \
        (l) ? &((list *) (l))->nil : NULL}

typedef struct{
    lanchor nil;
    uptr size;
} list;
#define LIST(l, elem) {{(elem) ? (elem) : &(l)->nil ,   \
                        (elem) ? (elem) : &(l)->nil}}

#define LIST_FOR_EACH(cur, list)                                    \
    for(cur = list->nil.n; cur != &list->nil; cur = cur->n)

void list_push(lanchor *a, list *l);
void list_enq(lanchor *a, list *l);

void list_add_before(lanchor *a, lanchor *beforehis, list *l);
void list_add_after(lanchor *a, lanchor *afterhis, list *l);

void list_remove(lanchor *a, list *l);

typedef bool (* lpred)(lanchor *to_compare, void *key);
lanchor *list_find(lpred pred, void *key, list *list);

int list_contains(lanchor *anchor, list *list);
lanchor *list_nth(unsigned int n, list *list);

lanchor *list_deq(list *l);
lanchor *list_peek(list *l);

uptr list_size(list *list);

lanchor *circlist_next(lanchor *a, list *l);
lanchor *circlist_prev(lanchor *a, list *l);

int lanchor_unused(lanchor *a);
int lanchor_valid(lanchor *a, list *list);

#define pudef (lanchor, "{%, %}", a->n, a->p)
#include <pudef.h>
#define pudef (list, "LIST{%, sz=%}", a->nil, a->size)
#include <pudef.h>
