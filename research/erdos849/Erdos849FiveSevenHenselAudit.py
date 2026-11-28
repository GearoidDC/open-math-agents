"""Check divisibility of an integral-function certificate on one smooth branch."""

from functools import lru_cache
from math import factorial, isqrt, prod

from Erdos849SaturatedCells import missing_denominator, normal_form


def falling(t, k):
    return prod(t - r for r in range(k))


def derivative(t, k):
    return sum(prod(t - r for r in range(k) if r != s) for s in range(k))


@lru_cache(maxsize=4096)
def branch_samples(p, E, x0, m0):
    """Solve 42 (x)_5 = (m)_7 one p-adic digit at a time."""
    dx = 42 * derivative(x0, 5) % p
    dm = -derivative(m0, 7) % p
    move_x = dm != 0
    assert move_x or dx, ("singular branch", p, x0, m0)
    inv = pow(dm if move_x else dx, -1, p)
    output = []
    for t in range(E):
        x = x0 + p*t if move_x else x0
        m = m0 if move_x else m0 + p*t
        precision = p
        for _ in range(1, E):
            error = 42*falling(x, 5) - falling(m, 7)
            assert error % precision == 0
            digit = (-(error // precision) * inv) % p
            if move_x:
                m += digit * precision
            else:
                x += digit * precision
            precision *= p
        assert (42*falling(x, 5)-falling(m, 7)) % precision == 0
        output.append((x, m))
    return tuple(output)


def check_local(i, j, cs, p, E, x, m, poly=None):
    """Prove p^E divides F on the residue branch (x,m) modulo p."""
    if not __debug__:
        raise RuntimeError("Run the Hensel verifier with assertions enabled")
    assert 0 <= i < 5 and 0 <= j < 7 and cs and all(type(c) is int for c in cs)
    assert type(E) is int and E >= 1
    assert p > max(7, len(cs)) and all(p % d for d in range(2, isqrt(p)+1))
    assert 0 <= x < p and 0 <= m < p and (x, m) != (i, j)
    assert (42*falling(x, 5)-falling(m, 7)) % p == 0
    q = p**E
    D = missing_denominator(5, 7, i, j)
    assert D % p != 0
    if poly is None:
        poly = normal_form(5, 7, i, j, cs)
    ordinary = [
        (a, b, (c.numerator * pow(c.denominator, -1, q)) % q)
        for (a, b), c in poly.items() if b >= 0
    ]
    inverses = [pow(d, -1, q) for d in range(1, len(cs)+1)]
    for t, (n, row) in enumerate(branch_samples(p, E, x, m)):
        y = row - j
        if x != i:
            z = D * prod(row-r for r in range(7) if r != j)
            z = z * pow(factorial(7)*(n-i), -1, q) % q
        else:
            z = D * prod(n-r for r in range(5) if r != i)
            z = z * pow(factorial(5)*y, -1, q) % q
        assert (factorial(5)*y*z - D*prod(n-r for r in range(5) if r!=i)) % q == 0
        assert (factorial(7)*(n-i)*z - D*prod(row-r for r in range(7) if r!=j)) % q == 0
        binomial = 1
        value = 0
        for d, (coefficient, inv) in enumerate(zip(cs, inverses), 1):
            binomial = binomial * (z+1-d) * inv % q
            value += coefficient * binomial
        value -= sum(c * pow(n, a, q) * pow(y, b, q) for a, b, c in ordinary)
        assert value % q == 0, ("failed Hensel sample", i, j, p, E, x, m, t)
    # With the unit derivative the dependent row is an integral formal
    # series in the displacement p*t of the free row from its base lift.
    # Both F and its chosen expression for Z have integral series there.
    # Modulo p^E the resulting function of t is a polynomial of degree < E.
    # The E samples determine its Newton differences; binom(t,d) is an
    # integer for every t in Z, including the negative integers.
    return True
