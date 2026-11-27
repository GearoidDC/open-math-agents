/* Sieve generalized Pell solutions via complete quotients of sqrt(D).
   The returned byte reports the positive norms encountered for each D. */
typedef unsigned long long U;
typedef unsigned __int128 Wide;
_Static_assert(sizeof(U)==8,"64-bit word required");
#ifdef _WIN32
#define API __declspec(dllexport)
int DllMainCRTStartup(void *module,unsigned int reason,void *reserved) { return 1; }
#else
#define API __attribute__((visibility("default")))
#endif

static unsigned bits(U v) { return 64u-(unsigned)__builtin_clzll(v); }

static unsigned check_one(U root,U remainder,unsigned allowed,unsigned precision) {
    /* The zeroth convergent is root/1, with negative norm -remainder.
       (P,Q) below are the first complete quotient after that convergent. */
    U p=root, den=remainder, prior_den=1;
    U cur=1, prior=0;
    unsigned scale=0, found=0;
    for (unsigned i=1;;++i) {
        U a=(root+p)/den;
        U new_p=a*den-p;
        /* Q' = Qprev + a(P-P'). The exact value is positive and fits in U.
           Unsigned operations therefore give that value even on wraparound. */
        U next_den=prior_den+a*(p-new_p);
        U saved=cur;
        Wide next=(Wide)a*cur+prior;
        if (next>=((U)1<<32)) {
            U hi=(U)(next>>64);
            unsigned shift=(hi ? 64+bits(hi) : bits((U)next))-20;
            cur=(U)(next>>shift);
            prior=shift>=64 ? 0 : saved>>shift;
            scale+=shift;
            if (scale+bits(cur)>precision) return found;
        } else {
            cur=(U)next;
            prior=saved;
        }
        if (i&1) {
            if (next_den==9) found|=allowed&1;
            if (next_den==25) found|=allowed&2;
            if (next_den==49) found|=allowed&4;
            if (found==allowed || next_den==1) return found;
        }
        p=new_p;
        prior_den=den;
        den=next_den;
    }
}

API void pair_batch(const U *rows,unsigned n,unsigned precision,unsigned char *out) {
    for (unsigned i=0;i<n;++i)
        out[i]=(unsigned char)check_one(rows[3*i],rows[3*i+1],(unsigned)rows[3*i+2],precision);
}

enum { LIMBS=36 }; /* supports up to 2,176 bits, plus one partial quotient */
typedef struct { U limb[LIMBS]; unsigned len; } integer;

static void step(integer *out,U a,const integer *cur,const integer *prior) {
    U carry=0;
    for (unsigned i=0;i<cur->len;++i) {
        Wide v=(Wide)a*cur->limb[i]+carry;
        if (i<prior->len) v+=prior->limb[i];
        out->limb[i]=(U)v;
        carry=(U)(v>>64);
    }
    out->len=cur->len;
    if (carry) out->limb[out->len++]=carry;
}

static unsigned smooth(const integer *value) {
    static const unsigned primes[]={2,3,5,7,11,13,17,19,23,29,31,37,
                                    41,43,47,53,59,61,67,71,73,79,83,89,97};
    unsigned words[LIMBS*2];
    unsigned n=value->len*2;
    for (unsigned i=0;i<value->len;++i) {
        words[2*i]=(unsigned)value->limb[i];
        words[2*i+1]=(unsigned)(value->limb[i]>>32);
    }
    if (words[n-1]==0) --n;
    for (unsigned t=0;t<sizeof(primes)/sizeof(primes[0]);++t) {
        U p=primes[t];
        for (;;) {
            U r=0;
            for (unsigned i=n;i--;) r=((r<<32)+words[i])%p;
            if (r) break;
            for (unsigned i=n;i--;) {
                U digit=(r<<32)+words[i];
                words[i]=(unsigned)(digit/p);
                r=digit%p;
            }
            while (n>1 && words[n-1]==0) --n;
        }
        if (n==1 && words[0]==1) return 1;
    }
    return 0;
}

/* For retained radicands, replay all convergents with exact denominators.
   A smooth pair forces the denominator to be smooth. */
API unsigned pair_hits(const U *rows,const unsigned char *flags,unsigned n,
                       unsigned precision,U min_x,unsigned *out,unsigned capacity) {
    if (!precision || precision>2176) return ~0u;
    unsigned hits=0;
    for (unsigned pos=0;pos<n;++pos) {
        if (!flags[pos]) continue;
        U root=rows[3*pos],p=root,den=rows[3*pos+1],prior_den=1;
        integer store[3];
        integer *cur=&store[0],*prior=&store[1],*next=&store[2];
        cur->len=1; cur->limb[0]=1; prior->len=0;
        for (unsigned i=1;;++i) {
            U a=(root+p)/den;
            U new_p=a*den-p;
            U next_den=prior_den+a*(p-new_p);
            step(next,a,cur,prior);
            integer *tmp=prior;
            prior=cur; cur=next; next=tmp;
            if ((cur->len-1)*64+bits(cur->limb[cur->len-1])>precision) break;
            unsigned mask=next_den==9 ? 1 : next_den==25 ? 2 : next_den==49 ? 4 : 0;
            if ((i&1) && (mask&flags[pos]) &&
                (cur->len>1 || (Wide)(root+1)*cur->limb[0]+7>=min_x) && smooth(cur)) {
                if (hits<capacity) {
                    out[3*hits]=pos;out[3*hits+1]=i;out[3*hits+2]=(unsigned)next_den;
                }
                ++hits;
            }
            p=new_p;prior_den=den;den=next_den;
        }
    }
    return hits;
}
