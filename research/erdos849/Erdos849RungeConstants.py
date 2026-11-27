"""Exact constants for applying Dèbes's height bound to four proper columns.

The geometric (full product degree) argument and the input theorem are
specified in Erdos849ReciprocalRunge.txt. This verifies their numerical
specialization. None of these computations construct the huge height itself.
"""

from itertools import combinations
from math import factorial, prod
from Erdos849FourteenPrimes import CLASSIFIED


def run():
    w = 839
    # Every mixed tuple with product <840 has largest member <= 839/(2*3*4).
    largest = 839//24
    small = [t for t in combinations(range(2,largest+1),4)
             if all(p not in CLASSIFIED for p in combinations(t,2))]
    assert min(prod(t) for t in small) == 840
    # A tuple may contain at most one element of {2,3,4,6}. Therefore its
    # second element is >=5 and its third >=7. If its last element is >=24
    # the last three already have product >=840; from 120 the last two do.
    clique = {2,3,4,6}
    assert all(p in CLASSIFIED for p in combinations(sorted(clique),2))
    assert 24*5*7 == 120*7 == 840
    for count,max_d,H in ((2,839,10000),(3,119,1000),(4,23,100)):
        D = max_d+2
        # e > 2; this also covers the archimedean sum of absolute coefficients.
        assert 2*factorial(max_d) < 2**H
        bound = w**2 * 2**(15*count+4) * D**(14*count) * (H**2+800)
        assert bound < 10**115
        print(f"{count} columns, max index {max_d}: logarithmic height bound <10^{len(str(bound))}")
    # The general deep-column bound at t=840 is (2^840 * 840!)^839.
    # Since 840! <= 2^(10*840), its natural logarithm is < 839*11*840.
    assert 840 < 2**10 and 839*11*840 < 10**115
    print("The height 10^(10^115) suffices in the 840-prime corollary.")


if __name__ == "__main__":
    run()
