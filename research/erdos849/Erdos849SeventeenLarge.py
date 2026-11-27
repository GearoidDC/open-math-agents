"""Check an explicit high-value obstruction for the pair of columns (7,8)."""

from itertools import combinations
from math import factorial, isqrt, comb, gcd, prod
from Erdos849FifteenPrimes import classify
from Erdos849SingletonCertificate import floor_root
from Erdos849FourteenBound import prime_free_part
from Erdos849ComponentBound import check as component_bound


def eight_seven(K):
    """Assume a=10^K*y with y>=1 and at most 16 distinct prime factors."""
    X = 10**K
    Rd = floor_root(factorial(8)*X,8)
    Rj = floor_root(factorial(7)*X,7)
    L, M = Rd-7, Rj+7
    # For any full prime power P, the signed falling-product difference
    # is divisible by P². Compare both weighted terms at X; the larger
    # grows at least y^(1/7), the smaller at most y^(1/8).
    bases = (2,3,5,7,None)
    differences = [0]*len(bases)
    for s in range(8):
        for r in range(7):
            A = factorial(7)*factorial(s)*factorial(7-s)
            B = factorial(8)*factorial(r)*factorial(6-r)
            if B*(Rj-r) <= A*(Rd+8-s):
                return False
            H = A*(Rd+8-s)+B*(Rj+7-r)
            for i,p in enumerate(bases):
                common = gcd(A,B)
                unit = prime_free_part(common,p) if p else common
                assert H%unit == 0
                differences[i] = max(differences[i], H//unit)
    bounds = [isqrt(v)+1 for v in differences]
    Q = max(bounds)
    # Every P <= Q*y^(1/14). Neither an empty nor a singleton slot can
    # account for n-s >= L*y^(1/8) if L>8!*Q. Thus the eight terms must
    # each host exactly two powers and there are exactly sixteen powers.
    if L <= factorial(8)*Q:
        return False
    # Three powers divide one term of the seven-column row. If all three
    # came from distinct eight-column slots, the product of the three
    # cofactors divides 8!, and their three partners have distinct bases.
    # The triple is at least L³/(8!*partners) * y^(9/56).
    partners = prod(sorted(bounds+[bounds[-1]]*2,reverse=True)[:3])
    distinct = L**3 > M*factorial(8)*partners
    # If a pair came from the same slot, its product is exactly (n-s)/b_s.
    # The third prime needs only one partner bound, and b_s*b_t divides 8!.
    # The triple is at least L²/(8!*Q) * y^(10/56). Both exponents exceed 1/7.
    shared = L**2 > M*factorial(8)*Q
    return distinct and shared


def residual(K):
    X = 10**K
    N = floor_root(X,16)
    assert comb(N,17)>N**16
    ruled = {e for e in combinations(range(2,17),2) if classify(*e,X,16)=="excluded"}
    return [p for p in combinations(range(2,17),4) if not any(e in ruled for e in combinations(p,2))]


if __name__ == "__main__":
    K = 524
    # The graph at 10^500 applies uniformly, including the requested larger range.
    remaining = residual(500)
    assert set(remaining) == {(3,5,7,8),(3,5,7,15),(5,6,7,8)}
    assert eight_seven(K)
    assert all(component_bound(188)) and K >= 188
    print("All three patterns are excluded: a>=10^524 with five rows needs at least 17 primes.")
