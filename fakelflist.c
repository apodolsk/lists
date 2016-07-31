#include <lflist.h>

#ifdef FAKELOCKFREE
#include <list.h>
#include <atomics.h>

#include <pthread.h>

static
void lock_lflist(lflist *l){
    fuzz_atomics();
    pthread_mutex_lock((pthread_mutex_t *) &l->mut);
}

static
void unlock_lflist(lflist *l){
    fuzz_atomics();
    pthread_mutex_unlock((pthread_mutex_t *) &l->mut);
}

flref flref_of(flanchor *a){
    return (flref){a, a->gen};
}

flanchor *flptr(flref a){
    return a.ptr;
}

/* TODO: lock_lflist may segfault in segalloc. As with lflist, need
   validity bits. */
err (lflist_del)(flx a, type *t){
    (void) t;
    lflist *l;
    while(1){
        l = a.ptr->host;
        if(!l || a.ptr->gen != a.gen)
            return -1;
        lock_lflist(l);
        if(a.ptr->host == l)
            break;
        unlock_lflist(l);
    }
    if(a.ptr->gen != a.gen)
        return unlock_lflist(l), -1;
    list_del(&a.ptr->lanc, &l->l);
    assert(a.ptr->host == l);
    a.ptr->host = NULL;
    unlock_lflist(l);
    return 0;
}

flx (lflist_deq)(type *t, lflist *l){
    lock_lflist(l);
    flx rlx = (flx){};
    flanchor *r = cof(list_deq(&l->l), flanchor, lanc);
    if(r){
        rlx = (flx){r, r->gen};
        assert(r->host == l);
        r->host = NULL;
        muste(linref_up(r, t));
    }
    unlock_lflist(l);
    return rlx;
}

err (lflist_enq)(flx a, type *t, lflist *l){
    return lflist_enq_upd(a.gen + 1, a, t, l);
}

err (lflist_enq_upd)(uptr ng, flx a, type *t, lflist *l){
    (void) t;
    if(a.ptr->gen != a.gen)
        return -1;
    lock_lflist(l);
    if(!cas2_won(((stx){ng, l}), &a.ptr->stx, (&(stx){a.gen, NULL})))
        return unlock_lflist(l), -1;
    list_enq(&a.ptr->lanc, &l->l);
    assert(a.ptr->host == l);
    assert(a.ptr->gen == ng);
    unlock_lflist(l);
    return 0;
}

err (lflist_jam)(flx a, type *t){
    return lflist_jam_upd(a.gen + 1, a, t);
}

err (lflist_jam_upd)(uptr ng, flx a, type *t){
    for(stx ax = a.ptr->stx;;){
        if(ax.gen != a.gen)
            return -1;
        if(ax.host){
            lflist_del(a, t);
            ax = a.ptr->stx;
            continue;
        }
        if(cas2_won(((stx){ng, NULL}), &a.ptr->stx, &ax))
            return 0;
    }
}

void flanc_ordered_init(uptr g, flanchor *a){
    *a = (flanchor) FLANCHOR_GEN(g);
}

void lflist_report_profile(void){}
 
#endif
