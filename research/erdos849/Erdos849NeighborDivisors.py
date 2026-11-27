"""Verify the integer constants in the two-neighbor divisor bounds."""

from math import comb, factorial, gcd, lcm, prod


def factors(value):
    result = {}
    p = 2
    while p * p <= value:
        while value % p == 0:
            result[p] = result.get(p, 0) + 1
            value //= p
        p += 1
    if value > 1:
        result[value] = 1
    return result


def constants(k, paired):
    denominator = factorial(k)
    derivative = sum(denominator // j for j in range(1, k + 1))
    if paired:
        assert k % 2 == 0 and derivative % (k + 1) == 0
        derivative //= k + 1
    g, f = factors(derivative), factors(denominator)
    loss = prod(p ** max(g.get(p, 0), f.get(p, 0) - g.get(p, 0))
                for p in g.keys() | f.keys())
    gain = derivative // gcd(derivative, denominator)
    return loss, gain, derivative


def test_assignment(k, paired, n, neighbor):
    d = n + 1 if neighbor == 1 else n - k
    if paired:
        d *= n + 1
    b = comb(n, k) + neighbor
    loss, gain, derivative = constants(k, paired)
    fd, fg = factors(d), factors(derivative)
    v = prod(p ** e for p, e in factors(b).items()
             if fd.get(p, 0) > fg.get(p, 0))
    assert d <= loss * v and v <= gain * d and gcd(v, b // v) == 1


def valuation(value, p):
    exponent = 0
    while value % p == 0:
        exponent += 1
        value //= p
    return exponent


def test_exceptional_primes(k, paired, neighbor):
    loss, gain, g = constants(k, paired)
    center = k if neighbor == -1 else -1
    for p in factors(g * factorial(k)):
        gval, fval = valuation(g, p), valuation(factorial(k), p)
        for j in range(1, max(gval, fval) + 4):
            n = center + (2*k*p+1) * p**j
            d = n - center
            if paired:
                d *= n + 1
            dv, bv = valuation(d, p), valuation(comb(n, k) + neighbor, p)
            if dv > gval:
                assert bv == dv + gval - fval
            selected = bv if dv > gval else 0
            assert dv - valuation(loss, p) <= selected <= dv + valuation(gain, p)


def main():
    three, five, seven = (constants(k, False) for k in (3, 5, 7))
    six, eight = (constants(k, True) for k in (6, 8))
    assert three[:2] == (66, 11) and five[:2] == (8220, 137)
    assert seven[1] == 363 and six[:2] == (1260, 7) and eight[1] == 761
    height = 10 ** 128
    for k in (3, 5, 6, 7, 8):
        assert (2*k)**k <= factorial(k)*height
    # For b=(k!a)^(1/k) we have b <= n <= b+k-1.
    # Thus b/2 <= n-k and n+1 <= 2b. For odd columns 5 and 7
    # the following tighter constants absorb the additive k.
    assert 4**8 >= factorial(8) and 10**3 > factorial(6) and 2**3 > factorial(3)
    assert 2**5 < factorial(5)
    assert 5040*100**7 < 399**7 and 7**7*100**7 < height
    assert 120 < 3**5 and 5**5 < height
    assert (2520 * 64 * eight[1])**12 < height
    assert (2 * 300 * (64*eight[1]))**12 < height**5
    assert (4*seven[1]*five[0])**35 < 2**35 * height**2
    assert (2*4*seven[1]*4*five[1])**35 < height**23
    for k, paired in ((3, False), (5, False), (7, False), (6, True), (8, True)):
        test_exceptional_primes(k, paired, -1)
        if k % 2:
            test_exceptional_primes(k, False, 1)
        for n in range(2*k, 45):
            test_assignment(k, paired, n, -1)
            if k % 2:
                test_assignment(k, False, n, 1)
    t = lcm(factorial(8), 9*eight[2], 9)
    assert (2*t+16)**8 < factorial(8)*height
    assert seven[0]**7 < height and five[0]**5 < height
    print("Verified unitary-divisor constants, height inequalities and direct controls.")


if __name__ == "__main__":
    main()
