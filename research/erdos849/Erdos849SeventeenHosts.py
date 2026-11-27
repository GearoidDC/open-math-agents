"""Obstructions from empty and singleton numerator terms for 17 prime bases."""

from itertools import combinations
from math import comb, factorial, gcd, prod

from Erdos849EighteenPrimes import row_bounds
from Erdos849LocalInterpolation import HEIGHT
from Erdos849SingletonCertificate import factorial_divisors
from Erdos849TwelfthPower import equal_in_column
from Erdos849FourteenBound import floor_root


def quadratic_difference(n,b,c,r,s,t):
    m_numerator = b*(n-s)*(n-t)+c*r
    # Multiply C(n,17)-C(m,8) by the positive integer 17! 8! c^8.
    return (factorial(8)*c**8*prod(n-i for i in range(17))
            - factorial(17)*prod(m_numerator-c*i for i in range(8)))


def singleton_seventeen():
    lo, hi = row_bounds(17,HEIGHT)
    for j in (7,8):
        lj, _ = row_bounds(j,HEIGHT)
        assert lj>factorial(j)*hi and lj>factorial(j)
        bmax = floor_root(factorial(j),3*j-17)
        cmax = bmax*hi**2//lj
        if j==7:
            assert cmax==0
            continue
        assert 8*21<17*10 and 20*lo**2<21*((lo-16)**2-8*cmax)
        assert lo>100 and cmax<=6 and bmax<=4
        assert quadratic_difference(17,1,1,1,16,10)==0
        count = 0
        for b in range(1,bmax+1):
            for c in range(1,cmax+1):
                if gcd(b,c)!=1 or b*hi**2<c*lj:
                    continue
                for r in range(8):
                    for s,t in combinations(range(17),2):
                        low, high = lo, lo
                        while quadratic_difference(high,b,c,r,s,t)<0:
                            high *= 2
                        while low<high:
                            mid = (low+high)//2
                            if quadratic_difference(mid,b,c,r,s,t)<0:
                                low = mid+1
                            else:
                                high = mid
                        assert quadratic_difference(low,b,c,r,s,t)!=0,(low,b,c,r,s,t)
                        count += 1
        print(f"Column pair (8,17): {count} candidate quadratic substitutions excluded.")


def main():
    for d in range(9,15):
        low, _ = row_bounds(d,HEIGHT)
        deficit = 2*d-17
        assert low**15>HEIGHT and low**15<=HEIGHT**2
        assert low**(15*deficit)>factorial(d)**15*HEIGHT**deficit
    _, upper = row_bounds(20,HEIGHT)
    assert upper**17<HEIGHT
    for d in range(15,20):
        lower, _ = row_bounds(d,HEIGHT)
        ns = {term+s for term in factorial_divisors(d) for s in range(d)
              if term+s>=lower}
        tested = 0
        for n in ns:
            a = comb(n,d)
            if a<HEIGHT:
                continue
            assert all(not equal_in_column(a,j) for j in range(7,d)), (n,d)
            tested += 1
        print(f"Column {d}: {tested} rows with a possible empty term checked.")
    singleton_seventeen()


if __name__=="__main__":
    main()
