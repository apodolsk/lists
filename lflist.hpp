struct lflist;
struct flanchor;

struct flref{
    flanchor *ptr;
    uptr gen;

    flref() = default;
    explicit flref(flanchor *a);

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
    struct type;
    /* This version of lflist assumes type stability. */
    void fake_linref_up(void);


    err lflist_enq_upd(uptr ng, flref a, type *t, lflist *l);
    err lflist_enq(flref a, type *t, lflist *l);
    
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
}align(sizeof(dptr));

/* The lack of a 16B MOV on x86 forces atomic<flx>::load to use CAS2(this,
   0, 0). I redefine load to make non-atomic reads, which suffice. I wrap
   CAS to randomly yield() in DBG mode. */
class half_atomic_flx : private std::atomic<flx>{
public:
    inline 
    operator flx() const{
        return load();
    }

    bool compare_exchange_strong(flx& expected,
                                 flx desired,
                                 std::memory_order order
                                 = std::memory_order_seq_cst);
    flx load(std::memory_order order = std::memory_order_seq_cst) const;
};

pudef(flx, "{%:% %, %}",
      (void *)(flanchor *)*a,
      a->nil,
      (const char *[]){"COMMIT", "RDY", "ADD", "ABORT"}[a->st],
      a->gen);

struct flanchor{
    half_atomic_flx n;
    half_atomic_flx p;
}align(2 * sizeof(dptr));

struct lflist{
    flanchor nil;
};

#define to_pt(flanc) (((uptr) (flanc)) >> 3)

inline
flref::flref(flanchor *align(8) a):
    ptr(a),
    gen(flx(a->p).gen){}

inline
flx::flx(lflist *l):
    st(COMMIT),
    nil(1),
    pt(to_pt(&l->nil)),
    gen(0)
{}

inline
flx::flx(flref r):
    st(COMMIT),
    nil(0),
    pt(to_pt(__builtin_assume_aligned(r.ptr, 8))),
    gen(r.gen)
{}

noinline
bool half_atomic_flx::compare_exchange_strong(
    flx& expected,
    flx desired,
    std::memory_order order)
{
    fuzz_atomics();
    return atomic<flx>::compare_exchange_strong(expected, desired, order);
}

inline 
flx half_atomic_flx::load(std::memory_order order)
    const
{
    typedef aliasing uptr auptr;
    flx r;
    ((auptr *) &r)[0] = ((volatile auptr *) this)[0];
    fuzz_atomics();
    ((auptr *) &r)[1] = ((volatile auptr *) this)[1];
    return r;
}


CASSERT(std::is_trivially_copyable<flref>());
CASSERT(std::is_trivially_copyable<flanchor>());
CASSERT(std::is_trivially_copyable<lflist>());
