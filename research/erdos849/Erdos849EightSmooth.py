"""Check the bounded smooth gap-three enumeration in column eight."""

import argparse
import ctypes as ct
import os
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from math import comb, factorial, gcd
from pathlib import Path
from tempfile import TemporaryDirectory

from Erdos849InterpolatedPowers import floor_root
from Erdos849SmoothNeighbors import is_smooth, smooth_neighbors


def scan(library, lower, upper):
    assert 5 <= lower and lower + 3 <= upper < 2**64
    word = ct.c_uint64
    func = library.gap_scan
    func.argtypes = [word, word, ct.c_uint, ct.POINTER(word), ct.POINTER(word), word]
    func.restype = word

    def part(first):
        anchors = word()
        pairs = (word*2048)()
        found = func(lower, upper, first, ct.byref(anchors), pairs, len(pairs))
        assert found <= len(pairs)
        return anchors.value, list(pairs[:found])

    with ThreadPoolExecutor(8) as pool:
        pieces = list(pool.map(part, range(23)))
    return sum(n for n, _ in pieces), sorted(x for _, xs in pieces for x in xs)


def main(compiler):
    source = Path(__file__).with_suffix(".c")
    windows = sys.platform == "win32"
    with TemporaryDirectory() as temp:
        dll = Path(temp)/("smooth.dll" if windows else "smooth.so")
        flags = ["-nostdlib", "-fuse-ld=lld"] if windows else ["-fPIC"]
        subprocess.run([compiler, "-O3", "-shared", *flags, "-o", str(dll), str(source)],
                       check=True)
        library = ct.CDLL(str(dll))
        test_lower, test_upper = 100, 10000
        anchors, matches = scan(library, test_lower, test_upper)
        assert anchors == sum(gcd(x, 6) == 1 and is_smooth(x)
                              for x in range(test_lower, test_upper+1))
        assert matches == [x for x in range(test_lower, test_upper-2)
                           if x%3 and is_smooth(x) and is_smooth(x+3)]

        lower = floor_root(factorial(8)*10**128, 8)-7
        upper = 2**64-1
        anchors, matches = scan(library, lower, upper)
        assert (anchors, matches) == (1431208549, [])
        if windows:
            # Windows prevents removal while this library is loaded.
            import _ctypes
            _ctypes.FreeLibrary(library._handle)
    neighbors = smooth_neighbors()
    pairs = {(a, b) for a, b in neighbors if lower <= a < b <= upper}
    pairs.update((3*a, 3*b) for a, b in neighbors
                 if b == a+1 and lower <= 3*a < 3*b <= upper)
    rows = {n for a, b in pairs for n in range(b, min(upper, a+7)+1)}
    assert len(pairs) == 8 and len(rows) == 48
    assert all(sum(is_smooth(n-i) for i in range(8)) < 3 for n in rows)
    # No upper row limit in this second enumeration. An odd gap-four
    # center is bounded independently by Najman's Theorem 3(a).
    assert 407479035814853+2 < lower
    unbounded = {(a, b) for a, b in neighbors if lower <= a}
    unbounded.update((2*a, 2*b) for a, b in neighbors if b-a == 2 and lower <= 2*a)
    unbounded.update((3*a, 3*b) for a, b in neighbors if b-a == 1 and lower <= 3*a)
    all_rows = {n for a, b in unbounded for n in range(b, a+8)}
    assert len(unbounded) == 15 and len(all_rows) == 79
    assert all(sum(is_smooth(n-i) for i in range(8)) < 3 for n in all_rows)
    print(f"Enumerated {anchors} odd anchors coprime to 3 from {lower} to {upper}.")
    print(f"Checked {len(pairs)} other close pairs in {len(rows)} possible rows.")
    print(f"Column eight has six primes above 100 from 10^128 through {comb(upper,8)}.")
    print("Every larger candidate with three smooth factors has an arithmetic "
          "progression of step three coprime to three.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cc", default=os.environ.get("CC") or shutil.which("clang")
                        or shutil.which("cc"), help="C compiler (Clang on Windows)")
    args = parser.parse_args()
    if not args.cc:
        parser.error("provide a C compiler with --cc")
    main(args.cc)
