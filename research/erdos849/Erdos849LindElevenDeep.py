"""Prime-multiple cover and deep columns for the eleventh Lind–Singmaster value."""

from fractions import Fraction
from functools import cache
from math import gcd, isqrt


N, K = 3_478_759_200, 1_328_767_775
GAP = 1_476
ENDPOINT = 3_999_999_999_999_999_887
DEEP = 63_319_921


def first_uncovered(j):
    """Rows below this threshold are covered by the prime-multiple argument."""
    assert j >= GAP
    return ENDPOINT * (j // GAP) + 1


def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def check_endpoint():
    # A prime q | n-1 with q²>n and the order test below proves n prime.
    q = 2_712_263_549
    assert trial_prime(q)
    for n in (181_818_181_818_181_813, ENDPOINT):
        assert (n-1) % q == 0 and q*q > n
        assert pow(5, n-1, n) == 1 and gcd(pow(5, (n-1)//q, n) - 1, n) == 1
        q = n
    assert ENDPOINT < 4*10**18
    assert all(pow(2, n-1, n) != 1 for n in range(ENDPOINT+2, 4*10**18, 2))


def known_rows():
    p, q = 3_478_759_199, 3_478_759_213
    assert N-K < p <= N < q and 2*K <= p and q < ENDPOINT//2 - GAP
    assert trial_prime(p) and trial_prime(q)
    assert all(not trial_prime(n) for n in range(p+1, q))
    hits = []
    for m in range(p, q):
        # num/den = C(m,j)/C(N,K), initially j=K.
        j, num, den = K, 1, 1
        for v in range(N, m):
            num *= v+1
            den *= v+1-K
        for v in range(N, m, -1):
            num *= v-K
            den *= v
        while num > den and j > 1:
            num *= j
            den *= m-j+1
            j -= 1
        while num < den and 2*(j+1) <= m:
            num *= m-j
            den *= j+1
            j += 1
        if num == den:
            hits.append((m, j))
    assert hits == [(N-1, K+1), (N, K)]
    return hits


SCALE = 1 << 192


@cache
def log_normalized(z):
    """Enclose log((1+z)/(1-z)) in units of 2^-192."""
    assert 0 <= z <= Fraction(1, 3)
    power, z2 = z, z*z
    low = Fraction()
    for i in range(70):
        low += 2*power/(2*i+1)
        power *= z2
    high = low + 2*power/(141*(1-z2))
    return (low*SCALE).__floor__(), (high*SCALE).__ceil__()


def log_int(n):
    e = n.bit_length()-1
    u = 1 << e
    a, b = log_normalized(Fraction(n-u, n+u))
    l2, h2 = log_normalized(Fraction(1, 3))
    return a+e*l2, b+e*h2


def binomial_log_difference(m, j, n, k):
    """Rational enclosure of log(C(m,j)/C(n,k))."""
    low = high = Fraction()
    for sign, x in ((1,m), (-1,j), (-1,m-j), (-1,n), (1,k), (1,n-k)):
        a, b = log_int(x)
        l = (2*x+1)*Fraction(a, 2*SCALE)-x
        u = (2*x+1)*Fraction(b, 2*SCALE)-x+Fraction(1, 12*x)
        if sign > 0:
            low += l
            high += u
        else:
            low -= u
            high -= l
    return low, high


def main():
    fib = [0, 1]
    while len(fib) <= 25:
        fib.append(fib[-1]+fib[-2])
    assert (N, K) == (fib[24]*fib[25], fib[22]*fib[25])
    check_endpoint()
    hits = known_rows()
    lo, hi = binomial_log_difference(first_uncovered(DEEP), DEEP, N, K)
    assert 30 < lo <= hi < 31
    lo, hi = binomial_log_difference(first_uncovered(DEEP-1), DEEP-1, N, K)
    assert -6 < lo <= hi < -5
    lo, hi = binomial_log_difference(15, 5, 14, 6)
    assert lo <= 0 <= hi
    # A separate small anchor C(4,2)=6 gives the digit count without building A.
    lo, hi = binomial_log_difference(N, K, 4, 2)
    l6, h6 = log_int(6)
    l10, h10 = log_int(10)
    digits = (lo*SCALE + l6)//h10 + 1
    assert digits == (hi*SCALE + h6)//l10 + 1 == 1_004_713_714
    print(f"Decimal digits: {digits:,}.")
    print(f"Prime-multiple cover through row {first_uncovered(DEEP)-1:,}.")
    print(f"Only occurrences in columns at least {DEEP:,}: {hits}.")


if __name__ == "__main__":
    main()
