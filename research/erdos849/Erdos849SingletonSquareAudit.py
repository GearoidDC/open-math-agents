"""Independent, standard-library replay of the five singleton square-class exclusions.

Run python Erdos849SingletonSquareAudit.py. The checks also run with python -O.
"""

from math import comb, factorial, gcd, isqrt, prod


CASES = ((3, 8, 105), (5, 8, 21), (7, 8, 2), (5, 6, 6), (7, 6, 7))
CUTOFF = 20_000
PRIMES = (11, 13, 17, 19, 23, 29, 31, 37)


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def falling(n, k):
    return prod(n - i for i in range(k))


def evaluate(coefficients, x):
    value = 0
    for coefficient in reversed(coefficients):
        value = value * x + coefficient
    return value


def balanced_digits(value, base, size):
    digits = []
    for _ in range(size):
        digit = (value + base // 2) % base - base // 2
        digits.append(digit)
        value = (value - digit) // base
    require(value == 0, "balanced coefficient reconstruction overflow")
    return digits


def binomial_row(value, column):
    """Independent strictly monotone search, without extracting integer roots."""
    low = high = 2 * column
    while comb(high, column) < value:
        high *= 2
    while low < high:
        middle = (low + high) // 2
        if comb(middle, column) < value:
            low = middle + 1
        else:
            high = middle
    return low if comb(low, column) == value else None


def residue_filters(k, h, d, offset):
    tables = []
    for p in PRIMES:
        # k!,h! are units mod p, so the integer binomials are periodic mod p.
        require(p > max(k, h), "noninvertible factorial")
        image = {comb(n, h) % p for n in range(p)}
        allowed = [comb((d * u * u + offset) % p, k) % p in image for u in range(p)]
        tables.append((p, allowed))
    return tables


def search(k, h, d, r, stop):
    tables = residue_filters(k, h, d, r)
    eligible = tested = 0
    hits = []
    for u in range(1, stop):
        m = d * u * u + r
        if m < 2 * k:
            continue
        eligible += 1
        if any(not allowed[u % p] for p, allowed in tables):
            continue
        tested += 1
        n = binomial_row(comb(m, k), h)
        if n is not None:
            hits.append((u, m, n))
    return eligible, tested, hits


def high_check(k, h, d, r):
    """Reconstruct Q by a single integer square root, then certify it exactly."""
    slots = tuple(range(1, h, 2))
    b = factorial(k) // gcd(factorial(k), factorial(h))
    c, rem = divmod(256 * b**2 * factorial(h), factorial(k))
    require(rem == 0, "nonintegral scale")
    factor = 2 ** (8 - h) * b**2
    e, f = (4096 * b**2, 0) if h == 8 else (189 * b**2, 900 * b**2)

    def polynomial(x):
        return c * falling(d * x*x + r, k)

    # Recover integer coefficient candidates by evaluating at a very large base.
    # Their validity follows from the independent degree checks below.
    base = 1 << 128
    root = (isqrt(4 * polynomial(base)) + 1) // 2
    q = balanced_digits(root, base, k + 1)
    residual = balanced_digits(root**2 - polynomial(base), base, k)
    require(q[-1] > 0, "wrong square-root branch")
    # Both polynomials have degree <=2k. Equality at 2k+1 points is an identity.
    for x in range(2 * k + 1):
        require(evaluate(q, x)**2 - polynomial(x) == evaluate(residual, x),
                "Q or residual polynomial mismatch")

    def H(y):
        return prod(y - s*s for s in slots)

    # Degree at most h in n. Verify both falling-product normalization
    # and the completed square at h+1 distinct points.
    for n in range(h + 1):
        t = 2*n - h + 1
        y = t*t
        v = b * (y*y - 42*y + 105 if h == 8 else 2*t**3 - 35*t)
        require(factor * H(y) == 256 * b**2 * falling(n, h), "normalization")
        require(v*v == factor * H(y) + e*y + f, "even square identity")

    # Any integer B with B^(h/2)>c*(d+k)^k suffices to bound Y.
    target = c * (d + k)**k
    bound = 1
    while bound**len(slots) <= target:
        bound *= 2
    require(2*k <= (k-1)*len(slots), "invalid growth exponent")
    require(2*sum(abs(v) for v in q[:-1]) < q[-1]*CUTOFF, "Q size bound")
    require(2*(e*(slots[-1]**2 + bound) + f + sum(map(abs, residual))) < q[-1]*CUTOFF,
            "difference bound")

    def forced_polynomial(x):
        v = evaluate(residual, x) - f
        return factor * prod(v - e*s*s for s in slots) - e**len(slots) * polynomial(x)

    # Newton's forward formula: for every integer t>=0 the weights binom(t,j)
    # are nonnegative and binom(t,0)=1. The forward differences at the cutoff
    # therefore certify nonvanishing on the entire required infinite tail.
    degree = max((k-1)*len(slots), 2*k)
    values = [forced_polynomial(CUTOFF + i) for i in range(degree + 1)]
    sign = 1 if values[0] > 0 else -1
    require(sign * values[0] > 0, "root at cutoff")
    while values:
        require(sign * values[0] >= 0, "forward difference has wrong sign")
        values = [b-a for a,b in zip(values, values[1:])]


def main():
    for p in PRIMES:
        require(p > 1 and all(p % i for i in range(2, isqrt(p) + 1)), "bad modulus")
    # Both tests include a real off-diagonal collision, 3003 = C(15,5) = C(14,6).
    # 15=15*1^2+0 and 15=3*2^2+3 exercise distinct offsets and search endpoints.
    require(search(5, 6, 15, 0, 2)[2] == [(1, 15, 14)], "first positive control")
    require(search(5, 6, 3, 3, 3)[2] == [(2, 15, 14)], "second positive control")
    require(binomial_row(comb(16, 8), 8) == 16, "central positive control")
    for k, h, d in CASES:
        eligible = tested = 0
        for r in range(k):
            high_check(k, h, d, r)
            admissible, candidates, hits = search(k, h, d, r, CUTOFF)
            require(not hits, (k, h, d, r, hits))
            eligible += admissible
            tested += candidates
        print(f"k={k} h={h} D={d}: {k} tails checked, {eligible} admissible finite cases, "
              f"{tested} final binary searches, zero hits", flush=True)


if __name__ == "__main__":
    main()
