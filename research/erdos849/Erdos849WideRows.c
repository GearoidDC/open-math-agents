/* Python supplies the arbitrary-precision origin and translates each residue set.
   Each wheel fits in 63 bits. Their product need not fit in a machine word. */
#include "Erdos849FocusedCRT.c"

/* Precompute multiplier times each possible 16-bit digit at each position.
   This avoids overflowing when an individual wheel has more than 32 bits. */
API void wide_phases(const U *xs,U *out,U n,U multiplier,U modulus,U *table) {
    U factor=multiplier;
    for(I j=0;j<4;j++) {
        U value=0;
        for(I d=0;d<65536;d++) {
            table[65536*j+d]=value;
            value+=factor;if(value>=modulus)value-=modulus;
        }
        factor=value;
    }
    for(U i=0;i<n;i++) {
        U x=xs[i],sum=0;
        for(I j=0;j<4;j++,x>>=16) {
            sum+=table[65536*j+(x&65535)];if(sum>=modulus)sum-=modulus;
        }
        out[i]=sum;
    }
}

API void wide_sort(U *xs,U n,U modulus,U *temp,U *counts) {
    U *src=xs,*dst=temp;
    for(I shift=0;shift<64 && ((modulus-1)>>shift);shift+=16) {
        for(I j=0;j<65536;j++)counts[j]=0;
        for(U i=0;i<n;i++)counts[(src[i]>>shift)&65535]++;
        U offset=0;
        for(I j=0;j<65536;j++) {
            U size=counts[j];counts[j]=offset;offset+=size;
        }
        for(U i=0;i<n;i++) {
            U x=src[i];dst[counts[(x>>shift)&65535]++]=x;
        }
        U *swap=src;src=dst;dst=swap;
    }
    if(src!=xs)for(U i=0;i<n;i++)xs[i]=src[i];
}

API void wide_sort_pairs(U *keys,U *values,U n,U modulus,U *kt,U *vt,U *counts) {
    U *ks=keys,*vs=values,*kd=kt,*vd=vt;
    for(I shift=0;shift<64 && ((modulus-1)>>shift);shift+=16) {
        for(I j=0;j<65536;j++)counts[j]=0;
        for(U i=0;i<n;i++)counts[(ks[i]>>shift)&65535]++;
        U offset=0;
        for(I j=0;j<65536;j++) {
            U size=counts[j];counts[j]=offset;offset+=size;
        }
        for(U i=0;i<n;i++) {
            U key=ks[i],dest=counts[(key>>shift)&65535]++;
            kd[dest]=key;vd[dest]=vs[i];
        }
        U *swap=ks;ks=kd;kd=swap;swap=vs;vs=vd;vd=swap;
    }
    if(ks!=keys)for(U i=0;i<n;i++){keys[i]=ks[i];values[i]=vs[i];}
}

/* The endpoints move in order of the left phase. Equal phases can move the
   upper endpoint back by one, depending on the final partial quotient. */
static U seek(const U *ys,U nr,U value,U *cursor) {
    U i=*cursor;
    while(i>0 && ys[i-1]>=value)i--;
    while(i<nr && ys[i]<value)i++;
    *cursor=i;return i;
}

API int wide_rows(U max_t,U extra,U M,U N,const U *left,const U *left_phase,
                  U nl,const U *ys,U nr,const I *mp,const U **masks,I nm,
                  const I *fp,const B **flags,I nf,const I *cyc_phase,
                  U *hit_a,U *hit_t,U cap,U *counts) {
    U words=(nr+63)/64, joined=0, masked=0, hits=0;
    U lower_cursor=0,upper_cursor[2]={0,0};
    if(nm>12 || max_t>N || N>=(1ULL<<63) || M>=(1ULL<<63))return -1;
    for(U g=0;g<nl;g++) {
        U a=left[g], start=left_phase[g];
        if(max_t==0 && a>extra)continue;
        U len=max_t+1-(a>extra);
        if(len>N)return -2;
        for(I pass=0;pass<2;pass++) {
            U off=pass?N:0;
            if(pass && start+len<=N)continue;
            U lo=pass?0:start, hi=start+len-off;
            if(hi>N)hi=N;
            if(ys[0]>=hi || ys[nr-1]<lo)continue;
            U i0=lo?seek(ys,nr,lo,&lower_cursor):0;
            U i1=hi==N?nr:seek(ys,nr,hi,&upper_cursor[pass]);
            if(i0>=i1)continue;
            joined+=i1-i0;
            const U *slice[12];
            for(I j=0;j<nm;j++) {
                I p=mp[j];
                U phase=(cyc_phase[j]+a%p+(M%p)*((off%p+p-start%p)%p))%p;
                slice[j]=masks[j]+phase*words;
            }
            for(U w=i0/64;w<=(i1-1)/64;w++) {
                U bits=~(U)0;
                if(w==i0/64)bits<<=i0%64;
                if(w==(i1-1)/64 && i1%64)bits&=(1ULL<<(i1%64))-1;
                if(nm==8) {
                    bits&=slice[0][w]&slice[1][w]&slice[2][w]&slice[3][w];
                    if(bits)bits&=slice[4][w]&slice[5][w]&slice[6][w]&slice[7][w];
                } else for(I j=0;j<nm && bits;j++)bits&=slice[j][w];
                while(bits) {
                    U h=w*64+__builtin_ctzll(bits), t=off+ys[h]-start;
                    bits&=bits-1;
                    if(t>=len)return -3;
                    masked++;
                    I j=0;
                    for(;j<nf;j++) {
                        I p=fp[j];
                        if(!flags[j][(cyc_phase[nm+j]+a%p+(M%p)*(t%p))%p])break;
                    }
                    if(j==nf) {
                        if(hits==cap)return -4;
                        hit_a[hits]=a;hit_t[hits++]=t;
                    }
                }
            }
        }
    }
    counts[0]=joined;counts[1]=masked;counts[2]=hits;
    return 0;
}
