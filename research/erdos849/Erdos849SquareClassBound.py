"""Check the explicit constants for the square-class bound in columns 7 and 8."""

from fractions import Fraction
from math import comb, factorial, isqrt


def verify():
    length = 200
    scale = 1680
    alpha, beta = 8*10**8, 8*10**7
    assert beta**8 * factorial(7) == alpha**7 * factorial(8)
    delta = Fraction(1, 32)
    for k, weight, gamma in ((7,8,alpha), (8,7,beta)):
        error = sum(range(k)) * Fraction(1,gamma)
        error += sum(comb(k,j)*(delta+Fraction(k,gamma))**j for j in range(2,k+1))
        assert error < k*delta
        assert scale**weight % (4*k*k*gamma) == 0

    counts = []
    for u in range(4):
        for v in range(5):
            if u+v == 0:
                continue
            h = 8*u+7*v
            terms = [(i,j,b) for i in range(7) for j in range(length//7+1)
                     for b in (0,1) if 8*i+7*j+b*h <= length]
            assert all(i+j+b*(u+v) <= 28 for i,j,b in terms)
            counts.append(len(terms))
    assert min(counts) == 308 and max(counts) <= 360
    assert 2*max(alpha,beta) < 10**10 and 10**280 * scale**length < 10**1000
    # The coefficient cube has more points than possible Taylor data.
    assert 107*2100 > 201*1004 and 2*360+1 < 10**4
    assert 360*10**(2100+280) < 10**2400

    # Cleared determinant of multiplication on the free rank-14 module.
    assert factorial(7) + factorial(8)//8 + 7 < 10**5
    assert (10**5)**6*8**8 < 10**38
    assert 360*10**(2100+30+38)*8**12 < 10**2184
    assert factorial(14)*10**(2184*14) < 10**30600
    assert 8*30600 < 250000
    assert beta**8 * 10**(56*2400) < 10**250000

    # At smaller row heights the explicit prime counts for larger columns
    # use inequalities (3) and (5) of Mukhopadhyay and Shorey.
    assert comb(36**2+35,36) < 10**128
    assert comb(100000+12,13) < 10**128
    primes = [n for n in range(2,587) if all(n%p for p in range(2,isqrt(n)+1))]
    for k in range(37,294):
        pi = sum(p<=k for p in primes)
        assert min(3*pi//4-1, sum(k<p<=2*k for p in primes)-1) >= 8
    print("Checked coefficient bounds, determinant height, and large-column cutoffs.")


if __name__ == "__main__":
    verify()
