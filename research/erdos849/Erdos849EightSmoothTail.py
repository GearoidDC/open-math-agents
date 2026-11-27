"""Certify a lower bound on omega for common values of columns 5, 7 and 8."""

import argparse
from functools import lru_cache, reduce
from itertools import product
from math import factorial, gcd, lcm, prod

from Erdos849InterpolatedPowers import denominator, floor_root, multiply, row_powers


COLUMNS = (8, 7, 5)
WEIGHT_DENOMINATOR = lcm(*COLUMNS)
DENOMINATOR = lcm(*range(1, max(COLUMNS)))
OFFSETS = list(product(*(range(k) for k in COLUMNS)))


def expansion(rows, exponents, length):
    values = [1] + [0]*(length-1)
    for powers, exponent in zip(rows, exponents):
        if exponent:
            values = multiply(values, powers[exponent])
    return values


def polynomials(offsets, count):
    monomials = sorted((sum(e*(WEIGHT_DENOMINATOR//k) for e,k in zip(es,COLUMNS)), es)
                       for es in OFFSETS if any(es))[:count]
    assert len({w for w, _ in monomials}) == count
    divisor = lcm(*(denominator(k,s) for k,s in zip(COLUMNS,offsets)))
    assert DENOMINATOR % divisor == 0
    length = count+2
    rows = [row_powers(k,s,divisor,length) for k,s in zip(COLUMNS,offsets)]
    pivots = {}
    for index, (_, exponents) in enumerate(monomials):
        series = expansion(rows, exponents, length)
        coefficients = [int(j == index) for j in range(count)]
        assert series[0] == 0
        for h in range(1,length):
            if series[h] == 0:
                continue
            if h not in pivots:
                pivots[h] = series, coefficients
                terms = [(c,w,es) for c,(w,es) in zip(coefficients,monomials) if c]
                yield h, terms
                break
            previous, vector = pivots[h]
            g = gcd(previous[h],series[h])
            a, b = previous[h]//g, series[h]//g
            coefficients = [a*x-b*y for x,y in zip(coefficients,vector)]
            series = [a*x-b*y for x,y in zip(series,previous)]
            content = reduce(gcd,coefficients)
            assert all(x % content == 0 for x in series)
            coefficients = [x//content for x in coefficients]
            series = [x//content for x in series]


@lru_cache(None)
def endpoint(column, decade):
    return floor_root(factorial(column)*10**decade, column)


@lru_cache(None)
def threshold(decade, cap):
    return floor_root((10**decade-1)//DENOMINATOR, cap)


def size_test(offsets, h, terms, decade, cap):
    lead, weight, exponents = terms[-1]
    if cap*weight > WEIGHT_DENOMINATOR*h:
        return False
    lower = [endpoint(k,decade)-s for k,s in zip(COLUMNS,offsets)]
    upper = [endpoint(k,decade)+k-s for k,s in zip(COLUMNS,offsets)]
    leading = abs(lead)*prod(x**e for x,e in zip(lower,exponents))
    same_sign = opposite = 0
    for c, _, es in terms:
        bound = abs(c)*prod(x**e for x,e in zip(upper,es))
        if c*lead < 0:
            opposite += bound
        else:
            same_sign += bound
    return opposite < leading and max(same_sign,opposite) < threshold(decade,cap)**h


def verify_local(offsets, h, terms):
    divisor = lcm(*(denominator(k,s) for k,s in zip(COLUMNS,offsets)))
    rows = [row_powers(k,s,divisor,h) for k,s in zip(COLUMNS,offsets)]
    total = [0]*h
    for c, _, es in terms:
        series = expansion(rows,es,h)
        total = [x+c*y for x,y in zip(total,series)]
    assert not any(total)


def check(decade, cap, count):
    maximal_order = 0
    for offsets in OFFSETS:
        for h, terms in polynomials(offsets,count):
            if size_test(offsets,h,terms,decade,cap):
                verify_local(offsets,h,terms)
                maximal_order = max(h,maximal_order)
                break
        else:
            return False
    print(f"All {len(OFFSETS)} branches passed at 10^{decade} for omega <= {cap}"
          f" (largest order {maximal_order}).", flush=True)
    return True


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--decade", type=int, default=3133)
    parser.add_argument("--cap", type=int, default=30)
    parser.add_argument("--monomials", type=int, default=24)
    parser.add_argument("--bisect", action="store_true",
                        help="try smaller decades and replay each passing calculation")
    args = parser.parse_args()
    assert check(args.decade,args.cap,args.monomials)
    if args.bisect:
        low, high = 0, args.decade
        while high-low > 1:
            middle = (low+high)//2
            if check(middle,args.cap,args.monomials):
                high = middle
            else:
                low = middle
        print(f"Verified cutoff 10^{high}.")
