"""Exact multi-column search with two CRT wheels and preindexed bit masks.

python Erdos849FocusedCRT.py --lower 105 --upper 120 --columns 3 5 7 8
The C kernel is compiled into a temporary directory. Supply --cc CLANG
if clang or cc is unavailable on PATH.
"""

import argparse
import ctypes as ct
from itertools import combinations
import math
import os
import shutil
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

from Erdos849Wheel import FORBIDDEN, max_row

U, I, B, V = ct.c_uint64, ct.c_uint32, ct.c_uint8, ct.c_void_p


@dataclass
class Rule:
    p: int
    period: int
    flags: bytearray
    ids: list

    @property
    def density(self):
        return len(self.ids)/self.period


def rules(cols):
    result = []
    d = max(cols)
    for p in range(2,502):
        if any(p%i == 0 for i in range(2,math.isqrt(p)+1)):
            continue
        # If mod=p^e and p^a<=d<p^(a+1), C(n,j) modulo mod has period
        # p^(a+e) for j<=d. Apply Vandermonde and
        # v_p(C(p^(a+e),i))=a+e-v_p(i) for 1<=i<=d.
        factor=1
        while factor*p <= d:
            factor*=p
        mod=p
        while mod*factor <= 16000:
            period=mod*factor
            common=set.intersection(*({math.comb(i,j)%mod for i in range(period)}
                                      for j in cols[:-1]))
            flags=bytearray(math.comb(i,d)%mod in common for i in range(period))
            result.append(Rule(p,period,flags,[i for i,v in enumerate(flags) if v]))
            mod*=p
    return result


def configure(kernel):
    kernel.extend_wheel.argtypes=[V,U,U,I,V,I,I,V]
    kernel.quotients.argtypes=[V,U,U,U]
    kernel.make_masks.argtypes=[V,U,U,I,V,V,V]
    kernel.search_rows.argtypes=[U,U,U,U,U,V,U,V,U,V,V,I,V,V,I,V,U,V]
    kernel.search_rows.restype=ct.c_int


def wheel(kernel,group):
    xs=(U*1)(0)
    M=1
    for r in group:
        ids=(I*len(r.ids))(*r.ids)
        out=(U*(len(xs)*len(ids)))()
        kernel.extend_wheel(xs,len(xs),M,r.period,ids,len(ids),pow(M,-1,r.period),out)
        M*=r.period
        xs=out
    return M,xs


def pointers(arrays):
    return (V*len(arrays))(*(ct.addressof(a) for a in arrays))


def check_join(kernel):
    """Check all signed wraps, word boundaries, and rows beyond 2^53."""
    def example(p,seed):
        flags=bytearray((n*n+seed*n+3)%p<p*3//4 for n in range(p))
        return Rule(p,p,flags,[n for n,f in enumerate(flags) if f])
    left_rules=[example(p,3) for p in (13,17)]
    right_rules=[example(p,4) for p in (19,23)]
    extra=[example(p,5) for p in (29,31,37,41,43,47,53,59)]
    tail=[example(p,7) for p in (61,67)]
    M,left=wheel(kernel,left_rules)
    N,ys=wheel(kernel,right_rules)
    inv=pow(M,-1,N)
    kernel.quotients(ys,len(ys),inv,N)
    ys=(U*len(ys))(*sorted(ys))
    assert len(ys)>64
    words=(len(ys)+63)//64
    masks=[]
    scratch=(I*len(ys))()
    for r in extra:
        dst=(U*(words*r.period))()
        kernel.make_masks(ys,len(ys),M,r.period,(B*(2*r.period)).from_buffer_copy(r.flags+r.flags),dst,scratch)
        masks.append(dst)
    flags=[(B*r.period).from_buffer(r.flags) for r in tail]
    for nm in (3,8):
        for lo in (37,2**55+12345):
            hi=lo+12344
            starts=[]
            for a in left:
                t0=max(0,(lo-a+M-1)//M)
                t1=(hi-a)//M
                if t1>=t0:
                    s=(a*inv+t0)%N
                    starts.append(s+t1-t0>=N)
            assert any(starts) and not all(starts)
            hits=(U*(hi-lo+1))()
            totals=(U*3)()
            status=kernel.search_rows(lo,hi,M,N,inv,left,len(left),ys,len(ys),
                                      (I*nm)(*(r.period for r in extra[:nm])),pointers(masks),nm,
                                      (I*len(tail))(*(r.period for r in tail)),pointers(flags),len(tail),
                                      hits,len(hits),totals)
            assert status==0
            survivors=list(range(lo,hi+1))
            for stage,restrictions in enumerate((left_rules+right_rules,extra[:nm],tail)):
                survivors=[x for x in survivors if all(r.flags[x%r.period] for r in restrictions)]
                assert totals[stage]==len(survivors)
            assert len(survivors)>10 and sorted(hits[:totals[2]])==survivors
    print('Direct CRT join controls passed, including positive and negative residues above 2^53.',flush=True)


def classes(options,capacity):
    groups=[[],[]]
    periods=[1,1]
    sizes=[1,1]
    used=set()
    for r in sorted(options,key=lambda r:-math.log(r.density)/math.log(len(r.ids)),reverse=True):
        if r.p in used:
            continue
        i=int(sizes[0]>sizes[1])
        if sizes[i]*len(r.ids)>capacity or periods[i]*r.period>=2**31:
            continue
        groups[i].append(r)
        sizes[i]*=len(r.ids)
        periods[i]*=r.period
        used.add(r.p)
    return groups,used,sizes,periods


def search(kernel,cols,low,high,capacity=1_500_000,mask_mib=128,plan_only=False,stats=None):
    d=cols[-1]
    lo=max(2*d,max_row(low,d)+1)
    hi=max_row(high,d)
    assert 0<=lo<=hi<2**62
    opts=rules(cols)
    groups,used,sizes,periods=classes(opts,capacity)
    M,N=periods
    assert M*N<2**62
    words=(sizes[1]+63)//64
    mask_rules=[]
    memory=0
    for r in sorted(opts,key=lambda r:-math.log(r.density)/r.period**0.35,reverse=True):
        need=8*words*r.period
        if r.p in used or len(mask_rules)==8 or memory+need>mask_mib*2**20:
            continue
        mask_rules.append(r)
        used.add(r.p)
        memory+=need
    other={}
    for r in opts:
        if r.p not in other or r.density<other[r.p].density:
            other[r.p]=r
    tail=sorted(other.values(),key=lambda r:r.density)
    print(f"rows [{lo:,},{hi:,}] wheels {sizes} periods {periods}; "
          f"mask periods {[r.period for r in mask_rules]} ({memory//2**20} MiB)",flush=True)
    if plan_only:
        return []
    M,left=wheel(kernel,groups[0])
    N,ys=wheel(kernel,groups[1])
    inverse=pow(M,-1,N)
    kernel.quotients(ys,len(ys),inverse,N)
    ys=(U*len(ys))(*sorted(ys))
    masks=[]
    phases=(I*len(ys))()
    for r in mask_rules:
        mask=(U*(r.period*words))()
        flags=(B*(2*r.period)).from_buffer_copy(r.flags+r.flags)
        kernel.make_masks(ys,len(ys),M,r.period,flags,mask,phases)
        masks.append(mask)
    tail_flags=[(B*r.period).from_buffer(r.flags) for r in tail]
    hits=(U*1024)()
    totals=[0,0,0]
    possible=[]
    for lower in range(lo,hi+1,M*N):
        counts=(U*3)()
        status=kernel.search_rows(lower,min(hi,lower+M*N-1),M,N,inverse,left,len(left),ys,len(ys),
                                  (I*len(masks))(*(r.period for r in mask_rules)),pointers(masks),len(masks),
                                  (I*len(tail))(*(r.period for r in tail)),pointers(tail_flags),len(tail),
                                  hits,len(hits),counts)
        assert status==0,status
        totals=[a+b for a,b in zip(totals,counts)]
        possible.extend(hits[:counts[2]])
    exact=[]
    for n in possible:
        assert lo<=n<=hi
        a=math.comb(n,d)
        if all(math.comb(max_row(a,j),j)==a and max_row(a,j)>=2*j for j in cols[:-1]):
            exact.append(n)
    print(f"joined {totals[0]:,}, after masks {totals[1]:,}, "
          f"after all local tests {totals[2]:,}, exact hits {sorted(exact)}",flush=True)
    if stats is not None:
        stats.append((hi-lo+1,*totals,len(exact)))
    return sorted(exact)


def main():
    if not __debug__:
        raise RuntimeError('Run with Python assertions enabled.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--columns',type=int,nargs='+',default=[3,5,7,8])
    ap.add_argument('--lower',type=int,default=105)
    ap.add_argument('--upper',type=int,default=120)
    ap.add_argument('--cc')
    ap.add_argument('--all-low',action='store_true',help='search all unclassified four-column patterns up to column 9')
    ap.add_argument('--middle',action='store_true',help='search all necessary triples for largest columns 10 through 14')
    ap.add_argument('--plan',action='store_true')
    ap.add_argument('--capacity',type=int,default=1500000)
    ap.add_argument('--mask-mib',type=int,default=128)
    args=ap.parse_args()
    assert args.columns==sorted(set(args.columns)) and min(args.columns)>=1
    compiler=args.cc or shutil.which('clang') or shutil.which('cc')
    if not compiler:
        ap.error('Supply a C compiler via --cc.')
    with tempfile.TemporaryDirectory(ignore_cleanup_errors=True) as tmp:
        dll=Path(tmp)/('sieve.dll' if os.name=='nt' else 'sieve.so')
        extra=['-nostdlib','-fuse-ld=lld'] if os.name=='nt' else ['-fPIC']
        subprocess.run([compiler,'-O3','-shared',*extra,'-o',str(dll),
                        str(Path(__file__).with_suffix('.c'))],check=True)
        kernel=ct.CDLL(str(dll))
        configure(kernel)
        if not args.plan:
            check_join(kernel)
            assert search(kernel,[1,2,5,6],2999,3020,1000,1)==[14]
            direct=[n for n in range(12,201) if math.comb(max_row(math.comb(n,3),2),2)==math.comb(n,3)]
            assert search(kernel,[2,3],math.comb(11,3),math.comb(200,3),1000,1)==direct
        patterns=[args.columns]
        if args.all_low:
            patterns=[p for p in combinations(range(2,10),4)
                      if not any(pair in FORBIDDEN for pair in combinations(p,2))]
            assert len(patterns)==10
        if args.middle:
            patterns=[(j,k,d) for d in range(10,15) for j,k in combinations((5,*range(7,d)),2)]
            assert len(patterns)==80
        stats=[]
        for c in patterns:
            print(f"columns {tuple(c)}",flush=True)
            assert not search(kernel,c,10**args.lower,10**args.upper,args.capacity,args.mask_mib,args.plan,stats)
        if stats:
            print('Totals (patterns, row-pattern pairs, CRT joins, mask survivors, local survivors, hits)',
                  (len(stats),*(sum(v) for v in zip(*stats))),flush=True)
        if os.name=='nt':
            import _ctypes
            _ctypes.FreeLibrary(kernel._handle)


if __name__=='__main__':
    main()
