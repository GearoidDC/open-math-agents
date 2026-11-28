"""Exclude exactly 35 primes in each four-column pattern above its cutoff."""

import gzip
import json
from itertools import product
from math import factorial, lcm, prod
from pathlib import Path

from Erdos849PatternThree import certificate_bounds, floor_root, root, valuation


def cell_bounds(columns, archive, height):
    """Maximum polynomial bound at each (column 8, column 5, column 7) position."""
    caps = [[[0]*7 for _ in range(5)] for _ in range(8)]
    with gzip.open(archive, "rt") as file:
        pieces = json.load(file)
    assert {tuple(offsets) for offsets,_,_ in pieces} == set(product(*(range(k) for k in columns)))
    for offsets, order, terms in pieces:
        positive, bound, weight = certificate_bounds(columns, offsets, order, terms, height)
        assert positive and 0 < 36*weight <= lcm(*columns)*order
        s = offsets[0]
        i = offsets[columns.index(5)]
        j = offsets[1]
        caps[s][i][j] = max(caps[s][i][j], 1+floor_root(bound, order))
    return [sorted((q for row in block for q in row), reverse=True) for block in caps]


def small_prime_options(p):
    """Upper multipliers on the eight terms and counts of exactly known hosted primes."""
    modulus = p
    while modulus <= 8:
        modulus *= p
    options = set()
    for n in range(modulus):
        vals = [valuation((n-s) % modulus or modulus, p) for s in range(8)]
        host = vals.index(max(vals))
        e = sum(vals)-valuation(factorial(8),p)
        assert 0 <= e <= vals[host]
        exact = [0]*8
        if n == host:
            # All lifts have the same cofactor, including the lift with e=0.
            vals[host] += valuation(420,p)-e
        elif e:
            exact[host] = 1
        options.add(tuple((p**v, flag) for v,flag in zip(vals,exact)))
    return options


def verify(columns, name, height):
    archive = Path(__file__).with_name("Erdos849Pattern"+name+".json.gz")
    caps = cell_bounds(columns,archive,height)
    smallest = root(8,height)-7
    thresholds = []
    for upper in caps:
        assert len(upper)==35 and min(upper)>0
        products = [prod(upper[:4-exact]) for exact in range(5)]
        thresholds.append([(smallest+v-1)//v for v in products])

    options = [small_prime_options(p) for p in (2,3,5,7)]
    least = 8
    for rows in product(*options):
        need_five = 0
        for s in range(8):
            known = prod(row[s][0] for row in rows)
            exact = sum(row[s][1] for row in rows)
            if known < thresholds[s][exact]:
                need_five += 1
        least = min(least, need_five)
    assert least >= 4
    print(columns, height, prod(map(len,options)), least, flush=True)


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    verify((8,7,5,3),"Three",291)
    verify((8,7,6,5),"SixHost",319)
