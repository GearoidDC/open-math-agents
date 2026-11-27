/* Enumerate all 100-smooth odd anchors coprime to 3 and test gap three. */
typedef unsigned long long U;
typedef unsigned int I;
#ifdef _WIN32
#define API __declspec(dllexport)
int DllMainCRTStartup(void *module, I reason, void *reserved) { return 1; }
#else
#define API __attribute__((visibility("default")))
#endif

static const I primes[] = {5,7,11,13,17,19,23,29,31,37,41,43,
                           47,53,59,61,67,71,73,79,83,89,97};
enum { PRIME_COUNT=23 };

static int smooth(U x) {
    /* These endpoints are even and coprime to 3. Constant divisors
       let the compiler use exact multiplication-based divisibility tests. */
    while ((x&1)==0) x>>=1;
#define STRIP(P) while (x%(P)==0) x/=(P);
    STRIP(5) STRIP(7) STRIP(11) STRIP(13) STRIP(17) STRIP(19)
    STRIP(23) STRIP(29) STRIP(31) STRIP(37) STRIP(41) STRIP(43)
    STRIP(47) STRIP(53) STRIP(59) STRIP(61) STRIP(67) STRIP(71)
    STRIP(73) STRIP(79) STRIP(83) STRIP(89) STRIP(97)
#undef STRIP
    return x==1;
}

struct scan {
    U lo,hi,limits[PRIME_COUNT],anchors,found,capacity;
    U *pairs;
};

static void record(struct scan *work,U lower) {
    if (work->found<work->capacity) work->pairs[work->found]=lower;
    ++work->found;
}

static void visit(struct scan *work,U x,I first) {
    if (x>=work->lo) {
        ++work->anchors;
        if (x>=work->lo+3 && smooth(x-3)) record(work,x-3);
        if (x<=work->hi-3 && smooth(x+3)) record(work,x);
    }
    for (I i=first;i<PRIME_COUNT && x<=work->limits[i];++i)
        visit(work,x*primes[i],i);
}

API U gap_scan(U lo,U hi,I first,U *anchors,U *pairs,U capacity) {
    struct scan work;
    work.lo=lo;work.hi=hi;work.capacity=capacity;work.pairs=pairs;
    work.anchors=0;work.found=0;
    for (I i=0;i<PRIME_COUNT;++i) work.limits[i]=hi/primes[i];
    if (first<PRIME_COUNT && primes[first]<=hi)
        visit(&work,primes[first],first);
    *anchors=work.anchors;
    return work.found;
}
