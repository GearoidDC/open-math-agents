"""Verify strict proportional neighborhood bounds between pairs of Pascal columns."""

from itertools import combinations
from math import comb, factorial, gcd, prod

from Erdos849LocalInterpolation import floor_root
from Erdos849PatternThree import check_hosts, host_loss


HEIGHT = 10**128
PAIRS = sorted(set(combinations((3,5,7,8),2)) | set(combinations((5,6,7,8),2)))


def endpoints(k):
    radicand = factorial(k)*HEIGHT
    z = floor_root(radicand,k)
    assert z**k <= radicand < (z+1)**k
    return z-k+1,z+k


def failed_product_tests(k,l):
    lo_k,hi_k = endpoints(k)
    lo_l,hi_l = endpoints(l)
    failed = set()
    for i in range(1,k):
        for j in range(i*l//k+1):
            # All factors assigned to S have to fit in N(S). The complement
            # of N(S) has all its factors in the complement of S.
            if (lo_k**i <= factorial(k)*hi_l**j and
                lo_l**(l-j) <= factorial(l)*hi_k**(k-i)):
                failed.add((k,l,i,j))
    return failed


def no_ratio(k,l,i,j):
    assert i*l==j*k
    lo_k,hi_k = endpoints(k)
    lo_l,hi_l = endpoints(l)
    checked = 0
    for b in range(1,factorial(k)+1):
        if factorial(k)%b:
            continue
        # Product ratio b/d has numerator b dividing k!, and d is positive.
        least = max(1,(b*lo_l**j+hi_k**i-1)//hi_k**i)
        greatest = (b*hi_l**j)//lo_k**i
        assert least>greatest
        checked += 1
    return checked


def coefficient(k,s):
    return prod(s-v for v in range(k) if v!=s)


def seven_needs_two():
    lo7,hi7 = endpoints(7)
    _,hi8 = endpoints(8)
    for r in range(7):
        for s in range(8):
            A = factorial(7)*abs(coefficient(8,s))
            B = factorial(8)*abs(coefficient(7,r))
            assert B*lo7 > A*hi8
            assert lo7**2 > factorial(7)**2*(A*hi8+B*hi7)
            # The low mirror equality C(15,7)=C(15,8) provides a direct
            # signed congruence control for every pair of shifts.
            x,y = 15-s,15-r
            common = gcd(x,y)
            delta = factorial(7)*coefficient(8,s)*x-factorial(8)*coefficient(7,r)*y
            assert comb(15,7)==comb(15,8) and delta % common**2 == 0


def four_column_profiles():
    # The same polynomial is evaluated for every prime in a joint assignment
    # class. Its single nonzero value bounds their product after denominator loss.
    q = 35519
    check_hosts(128,q,36)
    low,_ = endpoints(8)
    constants = [max(prod(host_loss(S,p) for p in (2,3,5,7))
                     for S in combinations(range(8),j)) for j in (1,4)]
    assert constants == [117600,8467200]
    assert low**24 * 10**(180-128) > (constants[0]*q**3)**24
    assert low**72 * 10**(370-128) > (constants[1]*q**16)**18


def main():
    if not __debug__:
        raise RuntimeError("The verifier requires Python assertions.")
    failed = set()
    count = 0
    for a,b in PAIRS:
        for k,l in [(a,b),(b,a)]:
            count += sum(1+i*l//k for i in range(1,k))
            failed |= failed_product_tests(k,l)
    assert failed=={(6,8,3,4),(8,6,4,3),(7,8,1,1),(8,7,7,6)}
    rationals = no_ratio(6,8,3,4)+no_ratio(8,6,4,3)
    seven_needs_two()
    four_column_profiles()
    print(f"{len(PAIRS)} column pairs, {count} directed subset sizes. "
          f"All four residuals excluded using {rationals} candidate numerators "
          "and 56 squared-divisibility inequalities.")
    print("Distinct four-column assignment tuples: at least 31 from 10^128, "
          "32 from 10^180, and 37 from 10^370.")


if __name__=="__main__":
    main()
