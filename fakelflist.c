#include <lflist.h>

#ifdef FAKELOCKFREE
#include <list.h>
#include <atomics.h>

#include <pthread.h>

dbg cnt wins;
dbg cnt paborts;
dbg cnt naborts;

static pthread_mutex_t mut = PTHREAD_MUTEX_INITIALIZER;

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

flx flx_of(flanchor *a){
    return (flx){a, a->gen};
}

flanchor *flptr(flx a){
    return a.a;
}

/* TODO: lock_lflist may segfault in segalloc. As with lflist, need
   validity bits. */
err (lflist_del)(flx a, type *t){
    (void) t;
    lflist *l;
    while(1){
        l = a.a->host;
        if(!l || a.a->gen != a.gen)
            return -1;
        lock_lflist(l);
        if(a.a->host == l)
            break;
        unlock_lflist(l);
    }
    if(a.a->gen != a.gen)
        return unlock_lflist(l), -1;
    list_remove(&a.a->lanc, &l->l);
    assert(a.a->host == l);
    a.a->host = NULL;
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
        muste(t->linref_up(r, t));
    }
    unlock_lflist(l);
    return rlx;
}

err (lflist_enq)(flx a, type *t, lflist *l){
    return lflist_enq_upd(a.gen + 1, a, t, l);
}

err (lflist_enq_upd)(uptr ng, flx a, type *t, lflist *l){
    (void) t;
    if(a.a->gen != a.gen)
        return -1;
    lock_lflist(l);
    if(!cas2_won(((stx){ng, l}), &a.a->stx, (&(stx){a.gen, NULL})))
        return unlock_lflist(l), -1;
    list_enq(&a.a->lanc, &l->l);
    assert(a.a->host == l);
    assert(a.a->gen == ng);
    unlock_lflist(l);
    return 0;
}

err (lflist_jam)(flx a, type *t){
    return lflist_jam_upd(a.gen + 1, a, t);
}

err (lflist_jam_upd)(uptr ng, flx a, type *t){
    for(stx ax = a.a->stx;;){
        if(ax.gen != a.gen)
            return -1;
        if(ax.host){
            lflist_del(a, t);
            ax = a.a->stx;
            continue;
        }
        if(cas2_won(((stx){ng, NULL}), &a.a->stx, &ax))
            return 0;
    }
}

void flanchor_ordered_init(uptr g, flanchor *a){
    *a = (flanchor) FLANCHOR_GEN(g);
}

void report_lflist_profile(void){}
 
#endif
