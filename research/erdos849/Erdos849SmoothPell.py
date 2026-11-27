"""Check three 100-smooth numbers in progression of difference three."""

import argparse
from array import array
import ctypes as ct
from concurrent.futures import ThreadPoolExecutor
from itertools import islice
from math import isqrt, prod
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

from Erdos849SmoothNeighbors import PRIMES, is_smooth


# Only the pair not divisible by 97 is needed. Differences 3 and 6
# prevent 97 from dividing more than one member of the progression.
BASES = tuple(p for p in PRIMES if p not in (3,97))
BOUND_BITS = 1310
LOW_ROW = 2**64


def check_center(x,low,limit,triples):
    # For an outer pair x is the middle term; for an adjacent pair it is
    # the sum of the terms. Test both locations of this adjacent pair.
    starts = [x-3]
    if x%2:
        starts.extend(((x-3)//2,(x-9)//2))
    for t in starts:
        if t >= low and t <= limit and t%3 and all(is_smooth(t+s) for s in (0,3,6)):
            triples.add(t)


def continued(d,limit):
    """Yield all positive-norm-nine convergents within the coordinate bound."""
    root=isqrt(d)
    p,den,a=0,1,root
    oldx,x,oldy,y=1,a,0,1
    while y<=limit:
        if x*x-d*y*y==9:
            yield x
        p=a*den-p
        den=(d-p*p)//den
        a=(root+p)//den
        oldx,x=x,a*x+oldx
        oldy,y=y,a*y+oldy


def small_solutions(d,limit):
    if d==1:
        yield from (3,5)
        return
    # Find the fundamental positive unit.
    root=isqrt(d)
    p,den,a=0,1,root
    ox,u,oy,v=1,a,0,1
    while u*u-d*v*v!=1:
        p=a*den-p
        den=(d-p*p)//den
        a=(root+p)//den
        ox,u=u,a*u+ox
        oy,v=v,a*v+oy
    seed_bound=isqrt(9*(u-1)//(2*d))
    for seed in range(-seed_bound,seed_bound+1):
        z=d*seed*seed+9
        x,y=isqrt(z),seed
        if x*x!=z:
            continue
        while y<0 or x<=limit:
            if y>=0:
                yield x
            x,y=u*x+d*v*y,v*x+u*y


def kernels(bases):
    items=[1]
    for p in bases:
        items.extend([p*x for x in items])
    return items


def batches():
    left=kernels(BASES[:12])
    right=kernels(BASES[12:])
    for v in right:
        yield [v*w for w in left if (v*w)%3==1 and v*w>81]


def native_flags(func,ds,bits):
    data=array("Q")
    mask=2**64-1
    for d in ds:
        data.extend((d&mask,d>>64,isqrt(d)))
    buf=(ct.c_uint64*len(data)).from_buffer(data)
    flags=(ct.c_ubyte*len(ds))()
    func(buf,len(ds),bits,flags)
    return [d for d,b in zip(ds,flags) if b]


def controls(func):
    ds=[d for d in range(82,2500) if isqrt(d)**2!=d]
    for bits in (5,12,32):
        # The compressed denominator bound can run a few extra steps,
        # so flags must include all exact positives.
        exact={d for d in ds if any(continued(d,2**bits-1))}
        assert exact.issubset(native_flags(func,ds,bits))
    for d in (1,7,13,19,31,37,43,61,67,73,79):
        actual=set(small_solutions(d,2000))
        brute={x for x in range(3,2001) if (x*x-9)%d==0 and isqrt((x*x-9)//d)**2==(x*x-9)//d}
        assert actual==brute,(d,actual^brute)
    for t in range(1,5000):
        if t%3==0 or not all(is_smooth(t+s) for s in (0,3,6)):
            continue
        pair=next((a,b) for a,b in ((t,t+3),(t+3,t+6),(t,t+6)) if a%97 and b%97)
        a,b=pair
        delta=2 if b-a==3 else 1
        x=(a+b)*delta//2
        z=a*b
        d=1
        for p in BASES:
            while z%p==0:
                z//=p
                d=d//p if d%p==0 else d*p
        assert z==1 and d%3==1
        sols=small_solutions(d,20000) if d<=81 else continued(d,20000)
        assert x in sols,(t,d,x)
        found=set()
        check_center(x,1,5000,found)
        assert t in found


def verify(compiler,workers):
    assert prod(BASES)<2**120 and 2*isqrt(prod(BASES))+1 < 2**64
    # If a < 10^3133, the column-8 row n has (n-7)^8 <= 8! a.
    assert ((2**(BOUND_BITS-1)-7)**8 > 40320*10**3133)
    limit=2**BOUND_BITS-1
    high=2**(BOUND_BITS-1)-7
    low=LOW_ROW-7
    triples=set()
    small=[d for d in range(1,82) if d%3==1 and all(d%(p*p) for p in PRIMES)]
    for d in small:
        for x in small_solutions(d,limit):
            check_center(x,low,high,triples)
    windows=sys.platform=="win32"
    with TemporaryDirectory() as temp:
        libname=Path(temp)/("pell.dll" if windows else "pell.so")
        opts=["-nostdlib","-fuse-ld=lld"] if windows else ["-fPIC"]
        subprocess.run([compiler,"-O3","-shared",*opts,str(Path(__file__).with_suffix(".c")),"-o",str(libname)],check=True)
        lib=ct.CDLL(str(libname))
        func=lib.pell_batch
        func.argtypes=[ct.POINTER(ct.c_uint64),ct.c_uint,ct.c_uint,ct.POINTER(ct.c_ubyte)]
        func.restype=None
        controls(func)
        def run(ds):
            return len(ds),native_flags(func,ds,BOUND_BITS)
        total=hits=0
        jobs=batches()
        with ThreadPoolExecutor(workers) as pool:
            for chunk in iter(lambda:list(islice(jobs,workers*3)),[]):
                for num,retained in pool.map(run,chunk):
                    total+=num
                    hits+=len(retained)
                    for d in retained:
                        for x in continued(d,limit):
                            check_center(x,low,high,triples)
                if total//500000!=(total-sum(map(len,chunk)))//500000:
                    print(f"Checked {total:,} kernels; {hits:,} retained.",flush=True)
        if windows:
            import _ctypes
            _ctypes.FreeLibrary(lib._handle)
    assert total+len(small)==2**(len(BASES)-1)
    assert total==4_194_286 and len(small)==18
    print(f"Large kernels: {total:,}; flagged: {hits:,}; small kernels: {len(small)}.")
    print(f"Smooth progressions starting between 2^64-7 and 2^{BOUND_BITS-1}-7: {sorted(triples)}.")
    assert not triples


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cc",default=shutil.which("clang") or shutil.which("cc"))
    parser.add_argument("--workers",type=int,default=8)
    args=parser.parse_args()
    if not args.cc:
        parser.error("provide a C compiler with --cc")
    verify(args.cc,args.workers)
