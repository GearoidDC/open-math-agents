/* Exact integer-only CRT join. Python supplies and owns all arrays.
   No C runtime is needed on the compiler bundled with Lean for Windows. */
typedef unsigned long long U;
typedef unsigned int I;
typedef unsigned char B;
#ifdef _WIN32
#define API __declspec(dllexport)
int DllMainCRTStartup(void *module, I reason, void *reserved) { return 1; }
#else
#define API __attribute__((visibility("default")))
#endif

API void extend_wheel(const U *old, U size, U base, I p, const I *ids,
                      I count, I inverse, U *out) {
    U pos=0;
    for (U i=0;i<size;i++) {
        I r=old[i]%p;
        for (I j=0;j<count;j++)
            out[pos++]=old[i]+base*((U)(ids[j]+p-r)*inverse%p);
    }
}

API void quotients(U *ys,U size,U inverse,U modulus) {
    for (U i=0;i<size;i++) ys[i]=(ys[i]*inverse)%modulus;
}

API void make_masks(const U *ys,U size,U base,I p,const B *allow,U *masks,I *phases) {
    U words=(size+63)/64;
    for(U i=0;i<size;i++) phases[i]=((ys[i]%p)*(base%p))%p;
    for(I q=0;q<p;q++) {
        for(U w=0;w<words;w++) {
            U bits=0, start=64*w, stop=start+64;
            if(stop>size) stop=size;
            for(U j=start;j<stop;j++)
                bits|=(U)allow[q+phases[j]]<<(j-start);
            masks[(U)q*words+w]=bits;
        }
    }
}

static U lower(const U *xs,U size,U x) {
    U lo=0,hi=size;
    while(lo<hi) {
        U m=lo+(hi-lo)/2;
        if(xs[m]<x) lo=m+1; else hi=m;
    }
    return lo;
}

API int search_rows(U lo,U hi,U M,U N,U invM,
                    const U *left,U nl,const U *ys,U nr,
                    const I *mask_periods,const U **masks,I nm,
                    const I *periods,const B **flags,I nf,
                    U *hits,U capacity,U *totals) {
    U words=(nr+63)/64;
    U joined=0,masked=0,nh=0;
    for(U g=0;g<nl;g++) {
        U a=left[g];
        if(a>hi) continue;
        U t0=lo<=a ? 0 : (lo-a+M-1)/M, t1=(hi-a)/M;
        if(t1<t0) continue;
        U length=t1-t0+1, start=(a*invM%N+t0)%N;
        if(length>N) return -1;
        for(I pass=0;pass<2;pass++) {
            U off=pass?N:0;
            if(pass && start+length<=N) continue;
            U y0=pass?0:start, y1=start+length-off;
            if(y1>N) y1=N;
            U i0=lower(ys,nr,y0), i1=lower(ys,nr,y1);
            if(i1<=i0) continue;
            joined+=i1-i0;
            const U *slice[12];
            if(nm>12) return -2;
            for(I j=0;j<nm;j++) {
                I p=mask_periods[j];
                U c=((t0+off)%p+p-start%p)%p;
                U phase=(a%p+(M%p)*c)%p;
                slice[j]=masks[j]+words*phase;
            }
            for(U w=i0/64;w<=(i1-1)/64;w++) {
                U bits=~(U)0;
                if(w==i0/64) bits<<=(i0%64);
                if(w==(i1-1)/64 && i1%64) bits&=((U)1<<(i1%64))-1;
                if(nm==8) {
                    bits&=slice[0][w]&slice[1][w]&slice[2][w]&slice[3][w];
                    if(bits) bits&=slice[4][w]&slice[5][w]&slice[6][w]&slice[7][w];
                } else {
                    for(I j=0;j<nm && bits;j++) bits&=slice[j][w];
                }
                while(bits) {
                    U h=64*w+__builtin_ctzll(bits);
                    bits&=bits-1;
                    U t=t0+off+ys[h]-start, n=a+M*t;
                    if(n<lo || n>hi) return -3;
                    masked++;
                    I j=0;
                    while(j<nf && flags[j][n%periods[j]]) j++;
                    if(j==nf) {
                        if(nh==capacity) return -4;
                        hits[nh++]=n;
                    }
                }
            }
        }
    }
    totals[0]=joined; totals[1]=masked; totals[2]=nh;
    return 0;
}

/* Intersect simultaneous column candidates for every row. Each table entry
   is a bit set of all earlier columns that can give this row's value. */
API int group_filter(U lo,U hi,const I *periods,const U **tables,I count,
                     U *work,I block,U *rows,U *possible,U capacity,U *total) {
    if(!count || !block || lo>hi) return -1;
    U found=0;
    I dense=count<9?count:9;
    for(U base=lo;base<=hi;base+=block) {
        I length=hi-base+1<block?(I)(hi-base+1):block;
        for(I k=0;k<dense;k++) {
            I p=periods[k], start=base%p;
            const U *table=tables[k];
            for(I pos=0;pos<length;) {
                I run=p-start;
                if(run>length-pos) run=length-pos;
                if(!k) for(I i=0;i<run;i++) work[pos+i]=table[start+i];
                else for(I i=0;i<run;i++) work[pos+i]&=table[start+i];
                pos+=run;start=0;
            }
        }
        for(I i=0;i<length;i++) {
            U x=work[i], n=base+i;
            for(I k=dense;k<count && (x&(x-1));k++)
                x&=tables[k][n%periods[k]];
            if(x&(x-1)) {
                if(found==capacity) return -2;
                rows[found]=n;possible[found++]=x;
            }
        }
    }
    *total=found;
    return 0;
}
