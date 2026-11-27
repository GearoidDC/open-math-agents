"""Close the finite large-prime-power exceptions between 10^128 and 10^174."""

from functools import cache
from math import comb, factorial, gcd, prod

from Erdos849LargestPower import bad_denominator, constant_bound, practical, valuation
from Erdos849FourteenBound import floor_root


LOW, HIGH = 10**128, 10**174
PMIN = floor_root(LOW,12)+1


@cache
def column_image(k, q):
    return {comb(i,k)%q for i in range(q)}


def equal_in_column(a, j):
    # Each q exceeds j. Lucas reduces the row modulo q.
    for q in (17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79):
        if q>j and a%q not in column_image(j,q):
            return False
    m = floor_root(factorial(j)*a,j)
    return any(comb(row,j)==a for row in range(max(2*j,m), m+j+1))


def small_base(p, j, d, s):
    count = 0
    power = p
    upper_n = floor_root(factorial(d)*HIGH,d)+d
    while power <= upper_n:
        if power >= PMIN:
            # m is not needed: from C(n,d)<=power^12 bound n directly.
            cap = min(upper_n, floor_root(factorial(d)*power**12,d)+d)
            first = max(1,(floor_root(factorial(d)*LOW,d)-s+power-1)//power)
            multiple = p**valuation(d*comb(d-1,s),p)
            for v in range(((first+multiple-1)//multiple)*multiple,
                           (cap-s)//power+1, multiple):
                n = v*power+s
                a = comb(n,d)
                if LOW <= a <= HIGH and power**12 >= a and a%power == 0:
                    assert not equal_in_column(a,j), (p,power,j,d,n)
                    count += 1
        power *= p
    return count


def quadratic_test(t, j, d, r, s, v, z):
    """Equality of binomials for a real quadratic row and a linear row."""
    ed, ej = d*comb(d-1,s), j*comb(j-1,r)
    sign = 1 if (d-1-s)%2 == (j-1-r)%2 else -1
    den = ed
    num = gcd(ed,ej)*z*t*t + sign*ej*v*t + den*r
    left = factorial(d)*prod(num-den*i for i in range(j))
    right = factorial(j)*den**j*prod(t*v+s-i for i in range(d))
    return left-right


def large_base(j,d,r,s,zmax):
    low_power = PMIN
    high_power = floor_root(factorial(d)*HIGH,d)+d
    # n/t <= (d!)^(1/d)*HIGH^(1/d-1/12) + (d-1)/LOW^(1/12)
    # because d<=12. The last summand is <1 throughout the interval.
    lower_root = floor_root(HIGH,12)
    vmax = (high_power+lower_root-1)//lower_root + 1
    assert vmax > 0 and 19*j>11*d
    # All rational factors are positive throughout. The derivative proof
    # in the accompanying note uses these integer inequalities.
    ed, ej = d*comb(d-1,s), j*comb(j-1,r)
    assert low_power > 100*(ej*vmax + ed*d + d)
    checks = 0
    for v in range(1,vmax+1):
        for z in range(1,zmax+1):
            lo,hi = low_power,high_power
            if quadratic_test(hi,j,d,r,s,v,z)<0:
                continue
            while lo<hi:
                t=(lo+hi)//2
                if quadratic_test(t,j,d,r,s,v,z)<0:
                    lo=t+1
                else:
                    hi=t
            assert quadratic_test(lo,j,d,r,s,v,z)!=0, (j,d,r,s,v,z,lo)
            checks += 1
    return checks


def check():
    assert practical(12,174) is not None
    assert (floor_root(factorial(13)*LOW,13)+13)**12 < LOW
    assert quadratic_test(5,2,3,1,0,2,1)==0
    assert quadratic_test(11,5,6,4,3,1,1)==0
    assert equal_in_column(3003,5) and not equal_in_column(3004,5)
    small = set()
    branches = []
    zeros = 0
    for d in range(8,13):
        rd = floor_root(factorial(d)*LOW,d)
        for j in range(7,d):
            rj = floor_root(factorial(j)*LOW,j)
            for r in range(j):
                for s in range(d):
                    ed, ej = d*comb(d-1,s), j*comb(j-1,r)
                    g = gcd(ed,ej)
                    same = (d-1-s)%2 == (j-1-r)%2
                    if same and ed*(rj-r)<=ej*(rd+d-s):
                        assert constant_bound(j,d,r,s)**12 < LOW
                        zeros += 1
                    x,y = ej*(rd+d-s), ed*(rj+j-r)
                    bound = (max(x,y) if same else x+y)//g
                    if bound**12 >= LOW**2:
                        branches.append((j,d,r,s,bound//floor_root(LOW,6)))
                    for p in (2,3,5,7,11):
                        if p>d:
                            break
                        vd,vj=valuation(ed,p),valuation(ej,p)
                        bonus=max(vd,vj)+min(vd-bad_denominator(d,s,p),
                                              vj-bad_denominator(j,r,p))
                        if (bound*p**max(0,-bonus))**12 >= LOW**2*p**(12*max(0,bonus)):
                            small.add((p,j,d,s))
    print("Zero branches checked:",zeros,"small-base jobs:",len(small),
          "quadratic branches:",len(branches),flush=True)
    count = sum(small_base(*args) for args in sorted(small))
    print("Small-base row cases checked:",count,flush=True)
    count = sum(large_base(*args) for args in branches)
    print("Quadratic searches reaching a crossing or the left endpoint:",count)


if __name__ == "__main__":
    check()
