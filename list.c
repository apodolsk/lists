#define MODULE LIST

#include <list.h>

void list_add_before(lanchor *a, lanchor *n, list *l){
    a->n = n;
    a->p = n->p;
    n->p->n = a;
    n->p = a;
    l->size++;
}

void list_add_after(lanchor *a, lanchor *p, list *l){
    a->n = p->n;
    a->p = p;
    p->n->p = a;
    p->n = a;
    l->size++;
}

void list_push(lanchor *a, list *l){
    list_add_after(a, &l->nil, l);
}

void list_enq(lanchor *a, list *l){
    list_add_before(a, &l->nil, l);
}

void list_remove(lanchor *a, list *l){
    a->n->p = a->p;
    a->p->n = a->n;
    l->size--;
    *a = (lanchor) LANCHOR(NULL);
}

lanchor *list_find(lpred pred, void *key, list *l){
    lanchor *c;
    LIST_FOR_EACH(c, l)
        if(pred(c, key))
            return c;
    return NULL;
}

int list_contains(lanchor *a, list *l){
    lanchor *c;
    LIST_FOR_EACH(c, l)
        if(a == c)
            return 1;
    return 0;
}

lanchor *list_nth(unsigned int n, list *l){
    lanchor *c;
    LIST_FOR_EACH(c, l)
        if(n-- == 0)
            return c;
    return c;
}

lanchor *list_peek(list *l){
    lanchor *head = l->nil.n;
    return head == &l->nil ? NULL : head;
}

lanchor *list_deq(list *l){
    lanchor *a = list_peek(l);
    if(a)
        list_remove(a, l);
    return a;
}

lanchor *circlist_next(lanchor *a, list *l){
    return a->n == &l->nil ? l->nil.n : a->n;
}

lanchor *circlist_prev(lanchor *a, list *l){
    return a->p == &l->nil ? l->nil.p : a->p;
}

int lanchor_unused(lanchor *a){
    return a->n == NULL && a->p == NULL;
}

int lanchor_valid(lanchor *a, list *l){
    assert(a != &l->nil);
    assert(a->n->p == a);
    assert(a->p->n == a);
    /* assert2(list_contains(a, l)); */
    return 1;
}

uptr list_size(list *l){
    return l->size;
}

int list_valid(list *l){
    lanchor *c;
    LIST_FOR_EACH(c, l)
        assert(c->p->n == c);
    return 1;
}

