"""Classify disconnected full-prime-power host graphs for nine pairs of columns."""

from collections import Counter
from itertools import product
from math import comb, factorial, gcd, isqrt


PATTERNS = ((3, 5, 7, 8), (5, 6, 7, 8))
PAIRS = sorted({(k,h) for cols in PATTERNS for k in cols for h in cols if k<h})
LOW = 100_000
MODULI = (11, 13, 17, 19, 23, 29, 31, 37, 41, 43)


def require(ok, message):
    if not ok:
        raise ArithmeticError(message)


def divisors(n):
    return sorted({v for i in range(1, isqrt(n)+1) if n % i == 0 for v in (i, n//i)})


def root(n, e):
    """Floor e-th root by exact integer Newton iteration with final checks."""
    if e == 1 or n == 0:
        return n
    x = 1 << ((n.bit_length()+e-1)//e)
    while True:
        z = ((e-1)*x + n//x**(e-1))//e
        if z >= x:
            require(x**e <= n < (x+1)**e, "integer root")
            return x
        x = z


def row_for_value(a, k):
    t = root(factorial(k)*a, k)
    for n in range(max(2*k, t), t+k+1):
        if comb(n, k) == a:
            return n
    return None


def graph_components(k,h,m,n):
    a = comb(n,h)
    require(a == comb(m,k), "mismatched rows")
    b = a
    options = []
    p = 2
    while b > 1:
        if p*p > b:
            p = b
        if b%p == 0:
            power = 1
            while b%p == 0:
                power *= p
                b //= p

            def hosts(N,K):
                def valuation(v):
                    j = 0
                    while v%p == 0:
                        j += 1
                        v //= p
                    return j
                vals = [valuation(N-i) for i in range(K)]
                greatest = max(vals)
                require(p**greatest >= power, "prime power has no host")
                return [i for i,v in enumerate(vals) if v == greatest]

            options.append([(i,k+j) for i in hosts(m,k) for j in hosts(n,h)])
        p += 1
    result = Counter()
    for edges in product(*options):
        groups = list(range(k+h))
        for i,j in edges:
            u,v = groups[i],groups[j]
            groups = [u if x==v else x for x in groups]
        result[len(set(groups))] += 1
    return dict(sorted(result.items()))


def windows(k,h):
    A,B = factorial(k),factorial(h)
    ratios = {(c//gcd(c,d),d//gcd(c,d)) for c in divisors(A) for d in divisors(B)}
    intervals = [(2*h, LOW)]
    raw = 0
    for s in range(k+1):
        for r in range(h+1):
            if (s,r) in ((0,0),(k,h)):
                continue
            e = h*s-k*r
            if e < 0:
                continue  # complementary cut orients the exponent positively
            radius_numerator = 2*k*(s*(k-1)+r*(h-1))
            if e == 0:
                require((k,h,s,r)==(6,8,3,4), "unexpected balanced cut")
                for u,v in ratios:
                    x,z = 56*u*u,v*v
                    # |log(q*sqrt(56))| >= |x-z|/(2*max(x,z)).
                    require(450*abs(x-z) >= 2*max(x,z), "balanced separation")
                require(LOW-h >= 450*2*(s*(k-1)+r*(h-1)), "balanced cutoff")
                continue
            width = (2*radius_numerator+e-1)//e
            require(LOW-h >= width and LOW-h >= B and LOW-h >= 2*h,
                    "small rows do not cover analytic threshold")
            for u,v in ratios:
                # y0^e = (u/v)^k (h!/k!)^s.
                center = root(u**k*(B//A)**s // v**k, e)
                left = max(LOW+1,center-width)
                right = center+width+h
                if left <= right:
                    raw += 1
                    intervals.append((left,right))
    merged = []
    for lo,hi in sorted(intervals):
        if merged and lo <= merged[-1][1]+1:
            merged[-1] = merged[-1][0], max(merged[-1][1],hi)
        else:
            merged.append((lo,hi))
    return raw,merged


def verify(k,h):
    raw, intervals = windows(k,h)
    tables = []
    for p in MODULI:
        require(p>h and all(p%i for i in range(2,isqrt(p)+1)), "bad modulus")
        permitted = {comb(i,k)%p for i in range(p)}
        tables.append([comb(n,h)%p in permitted for n in range(p)])
    hits = []
    tested = 0
    for lo,hi in intervals:
        for n in range(lo,hi+1):
            if not all(t[n%len(t)] for t in tables):
                continue
            tested += 1
            a = comb(n,h)
            m = row_for_value(a,k)
            if m is not None:
                hits.append((a,m,n,graph_components(k,h,m,n)))
    print(f"{k},{h}: {raw} high windows, {len(intervals)} merged, "
          f"{sum(hi-lo+1 for lo,hi in intervals)} rows, {tested} final tests; {hits}",
          flush=True)
    return hits


if __name__ == "__main__":
    for k,h in PAIRS:
        found = verify(k,h)
        expected = [(3003,15,14,{7:2})] if (k,h)==(5,6) else []
        require(found == expected, "unexpected collision or component counts")
