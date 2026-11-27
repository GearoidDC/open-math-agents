"""Complete the bounded-height large-prime test for largest columns nine and ten."""

import argparse
import ctypes as ct
from math import comb, factorial
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory

from Erdos849EightSmooth import scan
from Erdos849InterpolatedPowers import floor_root
from Erdos849PellPairs import LOW
from Erdos849SmoothNeighbors import smooth_neighbors
from Erdos849TwelfthPower import equal_in_column


def check(compiler):
    lowers={k:floor_root(factorial(k)*10**128,k)-k+1 for k in (9,10)}
    windows=sys.platform=="win32"
    with TemporaryDirectory() as temp:
        target=Path(temp)/("smooth.dll" if windows else "smooth.so")
        opts=["-nostdlib","-fuse-ld=lld"] if windows else ["-fPIC"]
        source=Path(__file__).with_name("Erdos849EightSmooth.c")
        subprocess.run([compiler,"-O3","-shared",*opts,str(source),"-o",str(target)],check=True)
        lib=ct.CDLL(str(target))
        anchors,three=scan(lib,min(lowers.values()),LOW+7)
        if windows:
            import _ctypes
            _ctypes.FreeLibrary(lib._handle)
    assert anchors==228_952_657 and len(three)==13
    neighbors=smooth_neighbors()
    for d,gap in ((9,4),(10,3)):
        # With at most six large prime bases, at least d-6 terms are
        # smooth. The closest two are separated by at most this gap.
        assert (d-1)//(d-7)==gap
        pairs={(z*a,z*b) for a,b in neighbors for z in range(1,gap//(b-a)+1)
               if z*a>=lowers[d]}
        pairs.update((a,a+3) for a in three if a>=lowers[d])
        if gap==4:
            assert 407_479_035_814_853+2 < lowers[d]
        # Larger coprime gap-three pairs are excluded by the norm-nine
        # part of Erdos849PellPairs.py. That scan's x cut is conservative
        # here for every smaller endpoint >= LOW.
        rows={n for a,b in pairs for n in range(b,a+d)}
        assert (len(pairs),len(rows))=={9:(90,569),10:(302,2356)}[d]
        for n in rows:
            a=comb(n,d)
            if a>=10**128:
                assert sum(equal_in_column(a,k) for k in (5,*range(7,d)))<2
        print(f"Column {d}: {len(pairs)} pairs, {len(rows)} possible rows, zero collisions.")


if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cc",default=shutil.which("clang") or shutil.which("cc"))
    args=p.parse_args()
    if not args.cc:
        p.error("provide a C compiler with --cc")
    check(args.cc)
