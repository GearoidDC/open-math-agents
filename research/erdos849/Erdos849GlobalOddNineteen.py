"""Check the bounded and large-height parts of the global odd-exponent bound."""

from argparse import ArgumentParser
from itertools import product
from math import comb, factorial, isqrt, prod

from Erdos849HigherSquare import certificate
from Erdos849WiderOdd import modular_data, repeat_mask, run


def high_columns(d, partner):
    if (d, partner) == (9, 7):
        return (5, 7, 9)
    return (partner, d)


def tail(columns):
    d = columns[-1]
    even = [k for k in columns if k % 2 == 0]
    for subset in product((0,1), repeat=len(even)):
        if sum(subset) and sum(subset) % 2 == 0:
            value = prod(factorial(k) for k, used in zip(even,subset) if used)
            assert isqrt(value)**2 != value
    # The parity map separates the sum(k-1) row coordinates at this height.
    # The only small primes used by these rows are among the eight through 19.
    assert sum(k-1 for k in columns) >= 15 and d <= 19
    return certificate(columns, 6)[-1]


def verify_deep_columns():
    assert comb(36**2+35, 36) < 10**128 and comb(5052,13) < 10**128
    primes = [q for q in range(2,587) if all(q%p for p in range(2,isqrt(q)+1))]
    assert sum(p<=19 for p in primes) == 8
    for d in range(37,294):
        count = sum(p<=d for p in primes)
        assert min(3*count//4-1, sum(d<p<=2*d for p in primes)-1) >= 8
    assert [p for p in primes if 17<p<=19] == [19]
    assert prod(p for p in primes if 19<p<=47) == 63392725189


def verify(d, finite=True):
    if d == 8:
        high = certificate((5,7,8),6)[-1]
        assert high <= 350000 and 5+7+8-3-8 >=7
        if finite:
            assert not run(8,(7,),19,350000)
        print("Largest column 8, high cutoff exponent",high,flush=True)
        return
    assert 9 <= d <= 16
    cutoffs = []
    # Six primes >19 mark at most six positions. The other d-6
    # positions have at least one pair separated by this gap or less.
    gap = (d-1)//(d-7)
    for k in range(7,d):
        high = tail(high_columns(d,k))
        assert high <= 1000000
        cutoffs.append(high)
        if finite:
            matches = run(d,(k,),19,1000000,gap)
            assert all(comb(n,d) <= 10**128 for n in matches)
            modular_data.cache_clear()
            repeat_mask.cache_clear()
    print("Largest column", d, "gap", gap, "high cutoff exponents", cutoffs, flush=True)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--largest", type=int, nargs="+", default=range(8,17))
    parser.add_argument("--bounds-only", action="store_true")
    args = parser.parse_args()
    if not __debug__:
        parser.error("the exact checks require assertions")
    verify_deep_columns()
    for d in args.largest:
        verify(d, not args.bounds_only)
