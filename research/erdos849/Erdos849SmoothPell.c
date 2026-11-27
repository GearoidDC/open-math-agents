/* Locate a convergent of sqrt(D) with positive norm nine. All integer
   divisions here are exact-width operations on unsigned values. */
typedef unsigned long long U;
_Static_assert(sizeof(U)==8, "64-bit word required");
typedef unsigned __int128 Wide;
#ifdef _WIN32
#define API __declspec(dllexport)
int DllMainCRTStartup(void *module, unsigned int reason, void *reserved) { return 1; }
#else
#define API __attribute__((visibility("default")))
#endif

static U wide_quotient(Wide n, U d) {
#if defined(__x86_64__) || defined(_M_X64)
    U q, rem;
    /* The reduced complete denominator is less than 2*sqrt(D)+1. */
    __asm__("divq %4" : "=a"(q), "=d"(rem) : "a"((U)n), "d"((U)(n>>64)), "r"(d));
    return q;
#else
    return (U)(n/d);
#endif
}

static unsigned bits(U x) { return 64u-(unsigned)__builtin_clzll(x); }

static unsigned possible(Wide disc, U root, unsigned bound_bits) {
    U p=0, den=1, a=root;
    U prev=0, cur=1; /* denominator of the 0th convergent, then its predecessors */
    unsigned scale=0, index=0;
    for (;;) {
        p=a*den-p;
        den=wide_quotient(disc-(Wide)p*p,den);
        if ((index&1) && den==9) return 1;
        a=(root+p)/den;
        Wide next=(Wide)a*cur+prev;
        prev=cur;
        if (next >= ((U)1<<32)) {
            U high=(U)(next>>64);
            unsigned shift=(high ? 64+bits(high) : bits((U)next))-20;
            cur=(U)(next>>shift);
            prev=shift>=64 ? 0 : prev>>shift;
            scale+=shift;
        } else {
            cur=(U)next;
        }
        if (scale+bits(cur)>bound_bits) return 0;
        ++index;
    }
}

API void pell_batch(const U *data, unsigned count, unsigned bound_bits,
                    unsigned char *out) {
    for (unsigned i=0;i<count;++i) {
        Wide disc=((Wide)data[3*i+1]<<64)|data[3*i];
        out[i]=(unsigned char)possible(disc,data[3*i+2],bound_bits);
    }
}
