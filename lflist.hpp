struct lflist;
struct flanchor;

struct flref{
    flanchor *ptr;
    uptr gen;

    flref() = default;
    flref(flanchor *a);

    inline
    operator flanchor*() const{
        return ptr;
    }

    inline
    flanchor* operator->() const{
        return ptr;
    }
};

extern "C"{
/* This version of lflist just assumes type stability. */
    struct type;
    void fake_linref_up(void);

    /* If !ret:
       - For all flref b | b == a, the next lflist_del_upd(_, b, t) will
         return 0 iff b.gen == ng.

       Undefined iff:
       - *a isn't object of type flanchor, or
       - ng == a.gen. Internal consistency depends on every enq updating
         "the generation of *a".
    */
    err lflist_enq_upd(uptr ng, flref a, type *t, lflist *l);
    err lflist_enq(flref a, type *t, lflist *l);

    /* Iff !ret:
       - For all flref b | b == a, the next call to either
         lflist_enq_upd(_, b, t) or lflist_del_upd(ng', b, t) will return
         0 iff b.gen == ng and, in the latter case, ng' != ng.

       Undefined iff:
       - *a may not be an object of type flanchor.
      
     */
    err lflist_del_upd(uptr ng, flref a, type *t);
    err lflist_del(flref a, type *t);
    err lflist_jam(flref a, type *t);

    flref lflist_unenq(type *t, lflist *l);

    bool flanc_valid(flanchor *a);
}

enum flst{
    COMMIT,
    RDY,
    ADD,
    ABORT,
};

/* An flx is the lflist's "unit of atomic exchange". It's a tagged and
   version-counted double-word pointer to another anchor.

   Crucially, I don't define operator==(flx&, flx&). Instead, flx
   arguments to == are implicitly converted to flanchor *, effectively
   comparing against flx::pt.

   "Full" double-word comparisons are done through eq_upd() and
   updx_won().

   flx::nil == 1 iff it references a list's nil node. Exists solely
   because it's necessary to avoid calling linref_up() on a nil node.
   
   flx::st describes its containing anchor, rather than the one it
   references.
*/
struct flx{
    flst st:2;
    uptr nil:1;
    uptr pt:WORDBITS-3;
    
    uptr gen;

    flx() = default;
    flx(flx x, flst st, uptr gen):
        st(st),
        nil(x.nil),
        pt(x.pt),
        gen(gen)
        {}

    explicit flx(lflist *l);
    flx(flref r);

    inline
    operator flanchor*() const{
        return (flanchor *)(uptr)(pt << 3);
    }
    
    inline
    flanchor* operator->() const{
        return *this;
    }
};

/* The lack of a 16B MOV on x86 forces atomic<flx>::load to use CAS2(this,
   0, 0). I redefine load to make non-atomic reads, which suffice. I wrap
   CAS to randomly yield() in DBG mode. */
class half_atomic_flx : public std::atomic<flx>{
    inline
    bool compare_exchange_strong(flx& expected, flx desired,
                                std::memory_order order = std::memory_order_seq_cst)
    {
        fuzz_atomics();
        return atomic<flx>::compare_exchange_strong(expected, desired, order);
    }
        
    
    inline
    flx load(std::memory_order order = std::memory_order_seq_cst) const{
        typedef aliasing uptr auptr;
        flx r;
        ((auptr *) &r)[0] = ((volatile auptr *) this)[0];
        fuzz_atomics();
        ((auptr *) &r)[1] = ((volatile auptr *) this)[1];
        return r;
    }
};

struct flanchor{
    half_atomic_flx n;
    half_atomic_flx p;
}align(2 * sizeof(dptr));

struct lflist{
    flanchor nil;
};

#define to_pt(flanc) (((uptr) (flanc)) >> 3)

inline
flref::flref(flanchor *a):
    ptr(a),
    gen(flx(a->p).gen){}

inline
flx::flx(lflist *l):
    st(),
    nil(1),
    pt(to_pt(&l->nil)),
    gen()
{}

inline
flx::flx(flref r):
    st(),
    nil(),
    pt(to_pt(r.ptr)),
    gen(r.gen)
{}

