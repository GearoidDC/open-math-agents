"""Exact first-nonzero-moment bounds for logarithms of three numerator subsets."""

from fractions import Fraction
from itertools import combinations, product
from math import factorial, gcd, lcm

def floor_root(n, k):
    lo, hi = 0, 1 << ((n.bit_length()+k-1)//k)
    while hi-lo > 1:
        mid = (hi+lo)//2
        if mid**k <= n:
            lo = mid
        else:
            hi = mid
    return lo


def coefficients(K, sizes):
    a, b, c = [Fraction(s,k) for s,k in zip(sizes,K)]
    raw = [b-c, c-a, a-b]
    scale = lcm(*(x.denominator for x in raw))
    integers = [int(x*scale) for x in raw]
    common = gcd(*integers)
    result = [x//common for x in integers]
    assert sum(result) == sum(x*f for x,f in zip(result,(a,b,c))) == 0
    assert all(x and (x*f).denominator == 1 for x,f in zip(result,(a,b,c)))
    return result


def offset_profiles(k, s, t):
    """Return uniform absolute coefficient bounds grouped by first Taylor order."""
    root = floor_root(factorial(k)*10**t,k)
    lo, hi = root-k, root+k
    offsets = [Fraction(k-1,2)-i for i in range(k)]
    radius = max(offsets)
    assert lo > 2*radius
    by_order = {}
    for chosen in combinations(range(k),s):
        weights = [int(i in chosen)-Fraction(s,k) for i in range(k)]
        for r in range(1,k):
            moment = abs(sum(w*z**r for w,z in zip(weights,offsets)))/r
            if moment:
                break
        else:
            raise ValueError("A nonconstant subset had all moments zero")
        error = 2*sum(map(abs,weights))*radius**(r+1)/((r+1)*lo**(r+1))
        lower, upper = moment/hi**r-error, moment/lo**r+error
        assert lower > 0
        if r in by_order:
            old_lower, old_upper = by_order[r]
            lower, upper = min(lower,old_lower), max(upper,old_upper)
        by_order[r] = lower, upper
    return by_order


def verify(K, shapes, t):
    cache = {}
    worst = None
    triples = sorted({s[:3] for s in shapes})
    for sizes in triples:
        coeffs = coefficients(K,sizes)
        bounds = []
        for k,s in zip(K,sizes):
            if (k,s) not in cache:
                cache[k,s] = offset_profiles(k,s,t)
            bounds.append(cache[k,s])
        for orders in product(*bounds):
            rates = [Fraction(r,k) for r,k in zip(orders,K)]
            assert len(set(rates)) == len(K)
            i = min(range(3),key=rates.__getitem__)
            dominant = abs(coeffs[i])*bounds[i][orders[i]][0]
            others = sum(abs(coeffs[j])*bounds[j][orders[j]][1] for j in range(3) if j!=i)
            ratio = dominant/others
            assert ratio > 1, (K,sizes,orders,float(ratio))
            worst = ratio if worst is None else min(ratio,worst)
    print(K, "decimal-log threshold", t, "shapes", len(shapes),
          "distinct triples", len(triples), "minimum dominance ratio exceeds", int(worst))
    return worst


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    for K in [(3,5,7),(5,6,7)]:
        all_triples = list(product(*(range(1,k) for k in K)))
        verify(K,all_triples,128)


if __name__ == "__main__":
    main()
