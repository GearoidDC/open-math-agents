"""Check that every position in either four-column pattern has a prime above 7."""

from functools import cache
from itertools import product
from math import comb, factorial, prod

from Erdos849Wheel import allowed_moduli


SMALL = (2, 3, 5, 7)
QUARTETS = ((3, 5, 7, 8), (5, 6, 7, 8))


def floor_root(n, k):
    estimate = 1 << ((n.bit_length() + k-1)//k)
    while True:
        better = ((k-1)*estimate + n//estimate**(k-1))//k
        if better >= estimate:
            assert estimate**k <= n < (estimate+1)**k
            return estimate
        estimate = better


def valuation(n, p):
    exponent = 0
    while n%p == 0:
        n //= p
        exponent += 1
    return exponent


def allowed_powers(k, upper):
    choices = []
    for p in SMALL:
        limit = (35519*p**valuation(420*factorial(k), p))**36 * 10**(upper-128)
        powers = [1]
        while (powers[-1]*p)**36 <= limit:
            powers.append(powers[-1]*p)
        choices.append(powers)
    return choices


def smooth_terms(choices, low, high):
    """Enumerate products in [low,high] using all powers in the four lists."""
    suffix_max = [prod(row[-1] for row in choices[j:]) for j in range(5)]

    def visit(j, current):
        if current*suffix_max[j] < low:
            return
        if j == 4:
            yield current
            return
        for power in choices[j]:
            following = current*power
            if following > high:
                break
            yield from visit(j+1, following)

    yield from visit(0, 1)


@cache
def filters(k, other):
    return [(p,frozenset(allowed)) for p,allowed in allowed_moduli(k,other)[:3]]


def exact_member(value, k):
    root = floor_root(factorial(k)*value,k)
    return any(comb(row,k) == value for row in range(max(2*k,root),root+k+1))


def finite_case(quartet, k):
    other = tuple(j for j in quartet if j != k)
    sieves = filters(k,other)
    terms = rows = exact = 0
    for lower in range(128,1000,8):
        upper = min(lower+8,1000)
        lower_value, upper_value = 10**lower,10**upper
        low = floor_root(factorial(k)*lower_value, k)-(k-1)
        high = floor_root(factorial(k)*upper_value,k)+(k-1)
        for term in smooth_terms(allowed_powers(k,upper), low, high):
            terms += 1
            for n in range(term,term+k):
                value = comb(n,k)
                if not lower_value < value <= upper_value:
                    continue
                rows += 1
                if all(n%p in allowed for p,allowed in sieves):
                    exact += 1
                    assert not all(exact_member(value, j) for j in other), (n,k,term)
    return terms, rows, exact


def main():
    if not __debug__:
        raise RuntimeError("Run this verifier with assertions enabled.")
    # At a >= 10^1000 the upper bound for any 7-smooth term is strictly
    # smaller than a^(1/8)/2, hence also than the smallest numerator term.
    assert 35519**36 < 10**(128+36)
    assert (2*factorial(8)*420*10**4)**72 < 10**1000
    # Independent short-interval control for generation and endpoints.
    test_choices = [[p**e for e in range(5)] for p in SMALL]
    brute = {prod(powers) for powers in product(*test_choices)}
    for low,high in ((1,1),(30,1000),(2,80000)):
        assert set(smooth_terms(test_choices,low,high)) == {x for x in brute if low<=x<=high}
    assert exact_member(3003,5) and exact_member(3003,6) and not exact_member(3003,8)
    for quartet in QUARTETS:
        for k in quartet:
            print(quartet, k, finite_case(quartet,k), flush=True)


if __name__ == "__main__":
    main()
