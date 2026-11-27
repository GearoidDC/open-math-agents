"""Exclude six or fewer primes above 100 in the two remaining column patterns."""

import argparse
from array import array
from concurrent.futures import ThreadPoolExecutor
import ctypes as ct
from itertools import islice
from math import comb, factorial, gcd, isqrt, prod
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

from Erdos849InterpolatedPowers import floor_root
from Erdos849PellSmall import smooth_gap_pairs
from Erdos849SmoothNeighbors import PRIMES, is_smooth, smooth_neighbors
from Erdos849TwelfthPower import equal_in_column


BITS=2100
LOW=floor_root(factorial(8)*10**128,8)-7
SQUARES=(9,25,49)
MASKS=[sum(1<<i for i,p in enumerate((3,5,7))
           if d%p in {r*r%p for r in range(1,p)}) for d in range(105)]


def subset_products(ps):
    result=[1]
    for p in ps:
        result.extend([a*p for a in result])
    return result


def batches():
    left=subset_products(PRIMES[:12])
    for b in subset_products(PRIMES[12:]):
        yield [d for a in left if (d:=a*b)>2401 and MASKS[d%105]]


def recover(d,i):
    root=isqrt(d)
    x,y,oldx,oldy=root,1,1,0
    p,den,a=0,1,root
    for _ in range(i):
        p=a*den-p
        den=(d-p*p)//den
        a=(root+p)//den
        x,oldx=a*x+oldx,x
        y,oldy=a*y+oldy,y
    return x,y


def normalized_pairs(x,h):
    if x%2 and x>h:
        yield (x-h)//2,(x+h)//2
    if h==3 and x>3:
        yield x-3,x+3


def scan(lib,ds,precision,min_x):
    rows=array("Q")
    for d in ds:
        root=isqrt(d)
        rows.extend((root,d-root*root,MASKS[d%105]))
    buf=(ct.c_uint64*len(rows)).from_buffer(rows)
    flags=(ct.c_ubyte*len(ds))()
    lib.pair_batch(buf,len(ds),precision,flags)
    capacity=1024
    while True:
        out=(ct.c_uint*(3*capacity))()
        num=lib.pair_hits(buf,flags,len(ds),precision,min_x,out,capacity)
        assert num<2**32-1
        if num<=capacity:
            break
        capacity=num
    hits=[(ds[out[3*k]],out[3*k+1],out[3*k+2]) for k in range(num)]
    return sum(bool(v) for v in flags),hits


def controls(lib):
    ds=[d for d in range(2410,3950) if isqrt(d)**2!=d and MASKS[d%105]]
    # Construct witnesses across the 64-bit boundary and near the full bound.
    for h in (3,5,7):
        for e in (34,44,54,58):
            x=2**e+1
            if x%h:
                ds.append((x*x-h*h)//4)
    bits=22
    exact=set()
    for d in ds:
        for i in range(2*bits+2):
            x,y=recover(d,i)
            if y>=2**bits:
                break
            norm=x*x-d*y*y
            if norm in SQUARES and MASKS[d%105]&(1<<SQUARES.index(norm)) and is_smooth(y):
                exact.add((d,i,norm))
    assert set(scan(lib,ds,bits,0)[1])==exact
    # By CRT these examples have opposite choices of +/-3 independently
    # in the prime-power factors of y. Both denominators exceed 64 bits.
    for x,y,good in (
        (19744233179471590741722001262877343747,37220882237953120000,True),
        (7208140096799636522020979199999999997,54800424286199200000,False),
    ):
        d,remainder=divmod(x*x-9,y*y)
        assert not remainder and gcd(x,y)==1 and is_smooth(y)==good
        idx=next(i for i in range(140) if recover(d,i)==(x,y))
        got=scan(lib,[d],67,0)[1]
        assert ((d,idx,9) in got)==good


def check(compiler,workers):
    assert prod(PRIMES)<2**122 and 2*isqrt(prod(PRIMES))+1<2**64
    assert ((2**(BITS-1)-7)**8>factorial(8)*10**5000)
    pairs={(a*k,b*k) for a,b in smooth_neighbors()
           for k in range(1,7//(b-a)+1) if k*a>=LOW}
    assert 407479035814853+2<LOW  # all odd centers for normalized gap four
    for a,b in smooth_gap_pairs(max_d=2401,y_limit=1<<BITS):
        if a>=LOW:
            pairs.add((a,b))
    windows=sys.platform=="win32"
    with TemporaryDirectory() as temp:
        target=Path(temp)/("pairs.dll" if windows else "pairs.so")
        opts=["-nostdlib","-fuse-ld=lld"] if windows else ["-fPIC"]
        subprocess.run([compiler,"-O3","-shared",*opts,str(Path(__file__).with_suffix(".c")),"-o",str(target)],check=True)
        lib=ct.CDLL(str(target))
        words=ct.POINTER(ct.c_uint64)
        flags=ct.POINTER(ct.c_ubyte)
        lib.pair_batch.argtypes=[words,ct.c_uint,ct.c_uint,flags]
        lib.pair_batch.restype=None
        lib.pair_hits.argtypes=[words,flags,ct.c_uint,ct.c_uint,ct.c_uint64,ct.POINTER(ct.c_uint),ct.c_uint]
        lib.pair_hits.restype=ct.c_uint
        controls(lib)
        total=flagged=candidates=0
        witnesses=[]
        def run(ds):
            return len(ds),scan(lib,ds,BITS,LOW)
        batch_iter=batches()
        with ThreadPoolExecutor(workers) as pool:
            for chunk in iter(lambda:list(islice(batch_iter,workers*3)),[]):
                before=total
                for n,(f,hits) in pool.map(run,chunk):
                    total+=n;flagged+=f;candidates+=len(hits)
                    for d,i,norm in hits:
                        witnesses.append((d,i,norm))
                        x,y=recover(d,i)
                        assert x*x-d*y*y==norm and y<2**BITS and is_smooth(y)
                        for u,v in normalized_pairs(x,isqrt(norm)):
                            if gcd(u,v)!=1 or not(is_smooth(u) and is_smooth(v)):
                                continue
                            for k in range(1,7//(v-u)+1):
                                if k*u>=LOW:
                                    pairs.add((k*u,k*v))
                if before//2000000 != total//2000000:
                    print(f"{total:,} large kernels, {len(pairs)} pairs.",flush=True)
        if windows:
            import _ctypes
            _ctypes.FreeLibrary(lib._handle)
    # Cross-check squarefree kernel counts with an independent subset count
    # grouped by residues, before excluding the small radicands.
    counts=[0]*105
    counts[1]=1
    for p in PRIMES:
        nxt=counts[:]
        for r,v in enumerate(counts):
            nxt[r*p%105]+=v
        counts=nxt
    small={v for v in range(1,2402) if MASKS[v%105] and is_smooth(v)
           and all(v%(p*p) for p in PRIMES)}
    assert total+len(small)==sum(c for r,c in enumerate(counts) if MASKS[r])
    assert total==19_398_233 and candidates==4
    assert all(norm!=9 for _,_,norm in witnesses)
    rows={n for a,b in pairs for n in range(b,a+8)}
    assert len(pairs)==36 and len(rows)==120
    collisions=[]
    for n in rows:
        a=comb(n,8)
        if a>=10**128 and all(equal_in_column(a,k) for k in (5,7)):
            collisions.append(n)
    print(f"{total:,} kernels, {flagged:,} positive flags, {candidates:,} smooth-denominator candidates.")
    print(f"Retained (kernel, index, norm): {sorted(witnesses)}.")
    print(f"{len(pairs)} smooth pairs, {len(rows)} candidate rows; surviving rows: {sorted(collisions)}.")
    assert not collisions


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cc",default=shutil.which("clang") or shutil.which("cc"))
    p.add_argument("--workers",type=int,default=8)
    args=p.parse_args()
    if not args.cc:
        p.error("provide a C compiler with --cc")
    check(args.cc,args.workers)
