"""Complete the multi-column search for largest columns >=15.

The nine published pair classifications imply that at least two earlier
columns must lie in {5,7,8,...}; the kernel tracks all of them simultaneously.
"""

import argparse
import ctypes as ct
from array import array
from math import comb,isqrt
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

from Erdos849FocusedCRT import U,I,V,pointers
from Erdos849Wheel import max_row


def build_tables(maximum):
    tables={}
    for p in range(7,701):
        if any(p%t==0 for t in range(2,isqrt(p)+1)):
            continue
        prev=array('H',[1])*p
        values={}
        images=[0]*p
        for j in range(1,min(maximum,p-1)+1):
            nxt=array('H',[0])*p
            v=0
            for n in range(j,p):
                v=(v+prev[n-1])%p
                nxt[n]=v
            values[j]=nxt
            bit=1<<j
            for y in set(nxt):
                images[y]|=bit
            prev=nxt
        tables[p]=(values,images)
    return tables


def rules(tables,d,group):
    mask=sum(1<<j for j in group)
    result=[]
    for p,(values,images) in tables.items():
        if p>d:
            rule=[images[y]&mask for y in values[d]]
            score=sum(x.bit_count() for x in rule)/p
            result.append((score,p,rule))
    result.sort()
    return [(p,r) for _,p,r in result]


def filtered(g,rs,lo,hi,group):
    if max(group)>=64:
        for n in range(lo,hi+1):
            x=sum(1<<j for j in group)
            for p,mask in rs:
                x&=mask[n%p]
                if x.bit_count()<2:
                    break
            if x.bit_count()>=2:
                yield n,x
        return
    masks=[(U*p)(*r) for p,r in rs]
    mods=(I*len(rs))(*(p for p,_ in rs))
    ptr=pointers(masks)
    block=16384
    work=(U*block)()
    capacity=1024
    row=(U*capacity)()
    possible=(U*capacity)()
    def visit(a,b):
        size=U()
        status=g.group_filter(a,b,mods,ptr,len(rs),work,block,row,possible,capacity,ct.byref(size))
        if status == -2:
            assert a<b
            mid=(a+b)//2
            yield from visit(a,mid)
            yield from visit(mid+1,b)
            return
        assert status==0
        yield from zip(row[:size.value],possible[:size.value])
    for a in range(lo,hi+1,8_000_000):
        yield from visit(a,min(hi,a+7_999_999))


def check(g,tables,d,lo,hi,group):
    count=exact=0
    triples=[]
    for n,x in filtered(g,rules(tables,d,group),lo,hi,group):
        assert lo<=n<=hi
        count+=1
        a=comb(n,d)
        hits=[]
        for j in group:
            if (x>>j)&1:
                exact+=1
                m=max_row(a,j)
                if m>=2*j and comb(m,j)==a:
                    hits.append((j,m))
        if len(hits)>=2:
            triples.append((d,n,hits))
    return count,exact,triples


def main():
    if not __debug__:
        raise RuntimeError('Run with Python assertions enabled.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--lower',type=int,default=105)
    ap.add_argument('--upper',type=int,default=120)
    ap.add_argument('--cc')
    args=ap.parse_args()
    low,high=10**args.lower,10**args.upper
    maximum=15
    while comb(2*(maximum+1),maximum+1)<=high:
        maximum+=1
    assert comb(2*maximum,maximum)<=high<comb(2*maximum+2,maximum+1)
    tables=build_tables(maximum)
    compiler=args.cc or shutil.which('clang') or shutil.which('cc')
    if not compiler:
        raise SystemExit('Supply a C compiler via --cc.')
    with tempfile.TemporaryDirectory(ignore_cleanup_errors=True) as tmp:
        lib=Path(tmp)/('group.dll' if os.name=='nt' else 'group.so')
        opts=['-nostdlib','-fuse-ld=lld'] if os.name=='nt' else ['-fPIC']
        subprocess.run([compiler,'-O3','-shared',*opts,'-o',str(lib),str(Path(__file__).with_name('Erdos849FocusedCRT.c'))],check=True)
        g=ct.CDLL(str(lib))
        g.group_filter.argtypes=[U,U,V,V,I,V,I,V,V,U,V]
        g.group_filter.restype=ct.c_int
        # Compare all retained column bits to independent evaluation for two
        # widely-separated ranges, including the true proper triple for 3003.
        for lo,hi in [(12,200),(10**12+123,10**12+1123)]:
            rs=rules(tables,6,(2,3,4,5))[:13]
            got=dict(filtered(g,rs,lo,hi,(2,3,4,5)))
            expected={}
            for n in range(lo,hi+1):
                x=sum(1<<j for j in (2,3,4,5) if all(
                    comb(n,6)%p in {comb(m,j)%p for m in range(p)} for p,_ in rs))
                if x.bit_count()>=2:
                    expected[n]=x
            assert got==expected
        assert (6,14,[(2,78),(5,15)]) in check(g,tables,6,12,200,(2,5))[2]
        size=rows=exact=0
        for d in range(15,maximum+1):
            lo=max(2*d,max_row(low,d)+1)
            hi=max_row(high,d)
            if lo>hi:
                continue
            group=(5,*range(7,d))
            c,e,h=check(g,tables,d,lo,hi,group)
            assert not h,h
            size+=hi-lo+1;rows+=c;exact+=e
            if d<=20 or d%25==0 or d==maximum:
                print(f"through {d}: {size:,} rows, {rows:,} mask survivors, {exact:,} exact inversions",flush=True)
        print(f"Largest column {maximum}; no relevant triple.",flush=True)
        if os.name=='nt':
            import _ctypes
            _ctypes.FreeLibrary(g._handle)


if __name__=='__main__':
    main()
