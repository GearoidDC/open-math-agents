"""Integer certificate for the large-value, fourteen-distinct-prime bound.

Suppose a has at most 13 distinct prime factors and at least five qualifying
rows in Erdős 849. The published fixed-column results exclude pair collisions
inside {2,3,4,6} above their listed exceptions. As columns 1 and 5 each
contribute at most one row, two distinct columns j,d >= 7 must occur. The
previously proved deep-column bound in Erdos849Factors.lean shows that d >= 14
would imply a <= (2^14 * 14!)^13. Hence, above that explicit constant, it
suffices to treat 7 <= j < d <= 13. Write a=C(n,d)=C(m,j).

For each prime p dividing a, write Q=p^v_p(a), s=n mod Q and r=m mod Q.
Kummer's carry criterion gives s<d and r<j (Erdos849PrimeHosts.lean).
Modulo Q^2, d!*a is (n-s) times (-1)^(d-1-s)*s!*(d-1-s)!: the first
factor is divisible by Q, and all other numerator factors can be reduced
modulo Q. Thus Q^2 divides the signed difference

    (-1)^(d-1-s)*A*(n-s) - (-1)^(j-1-r)*B*(m-r),
    A = j!*s!*(d-1-s)!,  B = d!*r!*(j-1-r)!.

If this difference is zero, the signs must agree and A*(n-s)=B*(m-r).
Otherwise, its absolute value after division by the p-free part of gcd(A,B)
is a positive multiple of Q^2. No primality of Q is needed.

Let X=10^K and y=a/X >= 1. Put R_k=floor((k!X)^(1/k)), with ceiling U_k
computed independently from the integer remainder. From the falling factorial
we have, for 0 <= h < k and any row u with C(u,k)=a,

    (R_k-h)*y^(1/k) <= u-h <= (U_k+k-1-h)*y^(1/k).

The left side follows from (k!a)^(1/k) <= u, and the right side from
u-k+1 <= (k!a)^(1/k). The program checks B*(R_j-r) > A*(U_d+d-1-s)
where the signs agree; since 1/j>1/d, this precludes a zero difference for
every a>=X. For a nonzero difference, after bounding both row terms with
the exponent 1/j, each prime power satisfies

    Q^2 <= C_p(X)*y^(1/j).

The constants take the worst upper bound over every admissible pair of offsets.
Primes greater than 13 cannot divide gcd(A,B), since every factorial in it
has argument at most 13. All those primes share the same constant C_inf.
The largest-prime-power test checks max_p C_p(X)^13 < X^2.
The sharper product test uses the fact that q = p^v appears only once per p:
multiply the six individual bounds for primes <=13 and seven copies of
C_inf. This overestimates the product for any choice of up to 13 primes,
since each individual bound is at least C_inf >= 1. If this product is
< X^2, we obtain a^2 < X^2*y^(13/j) <= a^2, since 13/j < 2.

All numerical comparisons use integers. The default reproduces the three
original largest-power and product thresholds. Use --power to verify one
of those thresholds and --staircase to run the stronger capped-prime and
finite-band argument. The latter replaces the large-value zero-ratio test
by an exhaustive integer-root test, requires no assumption on occupancy of
numerator positions, and also checks the crossover where d can exceed the
prime-factor cap. It uses the published small-column clique only above 10^60.
"""

import argparse
from dataclasses import dataclass
from functools import lru_cache
from math import comb, factorial, gcd, isqrt, prod


MAX_FACTORS = 13
SMALL_PRIMES = (2, 3, 5, 7, 11, 13)
MODES = ("raw-largest", "cancelled-largest", "cancelled-product")


def floor_root(value, degree):
    """Integer-only Newton iteration, starting from an upper bound."""
    root = 1 << ((value.bit_length() + degree - 1) // degree)
    while True:
        next_root = ((degree - 1) * root + value // root ** (degree - 1)) // degree
        if next_root >= root:
            assert root**degree <= value < (root + 1)**degree
            return root
        root = next_root


def prime_free_part(value, prime):
    while value % prime == 0:
        value //= prime
    return value


@dataclass(frozen=True)
class Weights:
    s: int
    r: int
    left: int
    right: int
    signs_agree: bool
    gcd_free: tuple


@lru_cache(maxsize=None)
def offset_weights(j, d):
    weights = []
    for s in range(d):
        for r in range(j):
            left = factorial(j) * factorial(s) * factorial(d - 1 - s)
            right = factorial(d) * factorial(r) * factorial(j - 1 - r)
            common = gcd(left, right)
            divisors = tuple(prime_free_part(common, p) for p in SMALL_PRIMES)
            weights.append(Weights(s, r, left, right, (d - 1 - s) % 2 == (j - 1 - r) % 2,
                                   (*divisors, common)))
    return weights


@lru_cache(maxsize=None)
def examine(power):
    X = 10**power
    roots = {}
    for k in range(7, MAX_FACTORS + 1):
        scaled = factorial(k) * X
        lower = floor_root(scaled, k)
        upper = lower if lower**k == scaled else lower + 1
        roots[k] = (lower, upper)

    failures = {mode: [] for mode in MODES}
    if (2**14 * factorial(14))**13 >= X:
        for mode in MODES:
            failures[mode].append("deep-column cutoff")

    for j in range(7, MAX_FACTORS):
        for d in range(j + 1, MAX_FACTORS + 1):
            raw = 0
            # The last entry applies to every prime greater than thirteen.
            bounds = [0] * (len(SMALL_PRIMES) + 1)
            bad_ratio = None
            for w in offset_weights(j, d):
                left = w.left * (roots[d][1] + d - 1 - w.s)
                right = w.right * (roots[j][1] + j - 1 - w.r)
                if w.signs_agree and w.right * (roots[j][0] - w.r) <= left:
                    bad_ratio = (w.s, w.r)
                bound = max(left, right) if w.signs_agree else left + right
                raw = max(raw, bound)
                for i, divisor in enumerate(w.gcd_free):
                    # Both summands are divisible by this integer.
                    assert bound % divisor == 0
                    bounds[i] = max(bounds[i], bound // divisor)
            if bad_ratio is not None:
                for mode in MODES:
                    failures[mode].append(("equal weights times rows", j, d, bad_ratio))
            ordinary = bounds[-1]
            assert all(b >= ordinary >= 1 for b in bounds)
            products = (raw**MAX_FACTORS, max(bounds)**MAX_FACTORS,
                        prod(bounds[:-1]) * ordinary**(MAX_FACTORS - len(SMALL_PRIMES)))
            for mode, upper in zip(MODES, products):
                if upper >= X**2:
                    failures[mode].append(("nonzero difference", j, d))
    return failures


def first_passing_power(mode):
    low, high = 0, 2048
    assert not examine(high)[mode]
    while low + 1 < high:
        middle = (low + high) // 2
        if examine(middle)[mode]:
            low = middle
        else:
            high = middle
    assert examine(high - 1)[mode] and not examine(high)[mode]
    return high


def falling_polynomial(multiplier, offset, k):
    """Coefficients of the falling product (multiplier*T+offset)_[k]."""
    poly = [1]
    for i in range(k):
        nxt = [0] * (len(poly) + 1)
        for degree, coefficient in enumerate(poly):
            nxt[degree] += (offset - i) * coefficient
            nxt[degree + 1] += multiplier * coefficient
        poly = nxt
    return poly


def divisors(value):
    factors = [1]
    p = 2
    while p * p <= value:
        old = factors[:]
        power = 1
        while value % p == 0:
            value //= p
            power *= p
            factors.extend(k * power for k in old)
        p += 1 if p == 2 else 2
    if value > 1:
        factors += [k * value for k in factors]
    return factors


@lru_cache(maxsize=None)
def audit_zero_branch():
    """Enumerate all integral row candidates when the signed difference vanishes.

    A(n-s)=B(m-r) forces n-s=(B/g)T, m-r=(A/g)T with integer T>=1.
    The two falling products give an integer polynomial in T; it is nonzero
    because the degrees d and j differ. Divide out its maximal power of T and
    the gcd of all its coefficients. Every integral root divides the remaining
    nonzero constant. Check all positive divisors in the admissible half-rows.
    """
    tested = 0
    for j in range(7, 13):
        for d in range(j + 1, 14):
            for w in offset_weights(j, d):
                if not w.signs_agree:
                    continue
                g = gcd(w.left, w.right)
                v, u = w.right // g, w.left // g
                left = falling_polynomial(v, w.s, d)
                right = falling_polynomial(u, w.r, j) + [0] * (d - j)
                coeffs = [factorial(j)*x - factorial(d)*y for x, y in zip(left, right)]
                assert coeffs[0] == coeffs[1] == 0 and coeffs[-1] != 0
                first = next(c for c in coeffs if c)
                for t in divisors(abs(first) // gcd(*coeffs)):
                    n, m = v*t + w.s, u*t + w.r
                    if n >= 2*d and m >= 2*j:
                        tested += 1
                        if comb(n, d) == comb(m, j):
                            raise ValueError(f"zero-difference collision at {(n, d, m, j)}")
    return tested


@lru_cache(maxsize=None)
def deep_threshold(w):
    """If d>w, then a<=(N-1)^w for the returned first row N.

    Kummer's valuation bound gives a<=n^w in each row of a value with <=w
    prime factors. Beyond N, C(n,w+1)>n^w: the ratio C(n,w+1)/n^w equals
    n times the product of the increasing positive factors (1-i/n), divided
    by (w+1)!. Within half-rows C(n,d)>=C(n,w+1) whenever d>=w+1.
    """
    low, high = w, 2 * factorial(w+1)
    assert comb(high, w+1) > high**w
    while high - low > 1:
        middle = (low + high) // 2
        if comb(middle, w+1) > middle**w:
            high = middle
        else:
            low = middle
    assert comb(low, w+1) <= low**w
    return high, (high - 1)**w


@lru_cache(maxsize=512)
def row_interval(endpoint, k):
    scaled = factorial(k) * endpoint
    root = floor_root(scaled, k)
    return root, root + (root**k != scaled) + k - 1


def continuous_product(X, w, j, d):
    """Return ordinary and row-capped product tests for every a>=X.

    The row-cap variant can replace the ell largest prime-specific bounds by
    Q^2<=n^2. The associated growth exponent is 2*ell/d+(w-ell)/j and is
    checked explicitly. Small primes that do not divide a may be replaced by
    any remaining large prime because their uncapped bounds dominate C_inf.
    """
    ny = row_interval(X, d)[1]
    my = row_interval(X, j)[1]
    bounds = [0] * (len(SMALL_PRIMES) + 1)
    for coeff in offset_weights(j, d):
        left = coeff.left * (ny - coeff.s)
        right = coeff.right * (my - coeff.r)
        upper = max(left, right) if coeff.signs_agree else left + right
        for i, div in enumerate(coeff.gcd_free):
            bounds[i] = max(bounds[i], upper // div)
    caps = sorted(bounds[:-1] + [bounds[-1]]*(w - len(SMALL_PRIMES)), reverse=True)
    ordinary = prod(caps) < X**2
    capped = any(2*ell*j + (w-ell)*d <= 2*d*j
                 and ny**(2*ell)*prod(caps[ell:]) < X**2 for ell in range(w+1))
    return ordinary, capped


def contains_host(low, high, offset, power):
    return offset < power and (high-offset)//power > (low-1-offset)//power


def interval_product(L, H, w, j, d):
    """Discrete product certificate for every L<=a<=H, using no occupancy.

    For each small base p try individual prime powers and retain the largest
    size consistent with both row intervals and some offset pair. Bases >13
    share an upper bound. The highest w of these bounds dominate every possible
    product, even when none of the small primes divide the unknown integer.
    """
    nl, nh = row_interval(L,d)[0], row_interval(H,d)[1]
    ml, mh = row_interval(L,j)[0], row_interval(H,j)[1]
    options = [[] for _ in SMALL_PRIMES]
    ordinary = 0
    for coeff in offset_weights(j,d):
        s, r = coeff.s, coeff.r
        left, right = coeff.left*(nh-s), coeff.right*(mh-r)
        if coeff.signs_agree:
            upper = max(left-coeff.right*(ml-r), right-coeff.left*(nl-s))
        else:
            upper = left + right
        ordinary = max(ordinary, upper//coeff.gcd_free[-1])
        for i in range(len(SMALL_PRIMES)):
            options[i].append((upper//coeff.gcd_free[i], s, r))
    small = []
    for p, possibilities in zip(SMALL_PRIMES, options):
        cap = min(nh, isqrt(max(b for b, _, _ in possibilities)))
        Q = 1
        while Q*p <= cap:
            Q *= p
        while Q > 1 and not any(Q*Q <= b and contains_host(nl,nh,s,Q)
                                 and contains_host(ml,mh,r,Q) for b,s,r in possibilities):
            Q //= p
        small.append(Q*Q)
    # Quantization may make a small-prime bound smaller than the generic one.
    bounds = small + [min(nh*nh, ordinary)]*w
    return prod(sorted(bounds, reverse=True)[:w]) < L**2


def check_band(L, H, w, j, d, budget=12):
    """Recursively cover a finite band. An unresolved leaf is reported as failure."""
    if interval_product(L,H,w,j,d):
        return True, 1
    if budget == 0 or L == H:
        return False, 1
    mid = isqrt(L*H)
    assert L <= mid < H
    valid, count = check_band(L,mid,w,j,d,budget-1)
    if not valid:
        return False, 1 + count
    valid, more = check_band(mid+1,H,w,j,d,budget-1)
    return valid, 1 + count + more


def column_unavailable(X, w, d):
    """The same increasing-ratio argument as deep_threshold, for any d>w."""
    n = floor_root(X, w)
    return d > w and n >= d and comb(n, d) > n**w


def pair_power(w, j, d, deep_power, capped, crossover=False):
    lo, hi = deep_power-1, 2048
    assert continuous_product(10**hi,w,j,d)[capped]
    while hi-lo > 1:
        mid = (hi+lo)//2
        X = 10**mid
        if (crossover and column_unavailable(X,w,d)) or continuous_product(X,w,j,d)[capped]:
            hi = mid
        else:
            lo = mid
    return hi


def bridge_decades(w, first, thresholds):
    threshold = first
    count = 0
    for (j,d), exponent in sorted(thresholds.items(), key=lambda item: -item[1]):
        while exponent > threshold:
            ok, nodes = check_band(10**(exponent-1),10**exponent-1,w,j,d)
            count += nodes
            if not ok:
                break
            exponent -= 1
        threshold = max(threshold,exponent)
    return threshold, count


def staircase():
    print(f"Zero signed differences: {audit_zero_branch()} admissible divisor tests; no solutions")
    print("factor cap | first excluded deep row | product | row-capped | discrete bands | crossover")
    for w in range(10,14):
        N, deep_bound = deep_threshold(w)
        # The previously classified clique is applied above 10^60.
        first = max(60, len(str(deep_bound)))
        pairs = [(j,d) for j in range(7,w) for d in range(j+1,w+1)]
        ordinary = {z: pair_power(w,*z,first,False) for z in pairs}
        capped = {z: pair_power(w,*z,first,True) for z in pairs}
        threshold, count = bridge_decades(w,first,capped)
        # Retain every column up to 13 even when its index exceeds the prime
        # count cap. This can extend below the point where d<=w is guaranteed.
        cross_first = 60
        while not column_unavailable(10**cross_first,w,14):
            cross_first += 1
        cross_pairs = [(j,d) for j in range(7,13) for d in range(j+1,14)]
        cross_caps = {z: pair_power(w,*z,cross_first,True,True) for z in cross_pairs}
        cross, cross_count = bridge_decades(w,cross_first,cross_caps)
        print(w, N, max(ordinary.values()), max(capped.values()), f"{threshold} ({count} nodes)",
              f"{cross} ({cross_count} nodes)", sep=" | ", flush=True)


def main():
    parser = argparse.ArgumentParser(description="Check the explicit fourteen-prime bound.")
    parser.add_argument("--power", type=int, help="check this decimal exponent")
    parser.add_argument("--staircase", action="store_true",
                        help="check the sharp column cutoff and product bounds for caps 10 through 13")
    options = parser.parse_args()
    if options.staircase:
        staircase()
        return 0
    if options.power is not None:
        if options.power < 1:
            parser.error("--power must be positive")
        results = examine(options.power)
        for mode in MODES:
            print(mode, "PASS" if not results[mode] else "FAIL", results[mode][:3])
        return int(bool(results["cancelled-product"]))
    for mode in MODES:
        power = first_passing_power(mode)
        print(f"{mode}: K={power}; preceding decade fails {examine(power - 1)[mode]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
