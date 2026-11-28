"""Verify lower bounds for linear forms in prime logarithms on balanced 6/8 cuts."""

from fractions import Fraction
import json
from math import factorial, isqrt, lcm, prod
from pathlib import Path


def valuation(n, p):
    count = 0
    while n % p == 0:
        n //= p
        count += 1
    return count


def exponent_bounds(primes, cap):
    if cap > 10000:
        return [cap] * len(primes)
    result = []
    for p in primes:
        limit = p**(36*valuation(420,p)) * 35519**36 * 10**(cap-128)
        exponent = 0
        while p**(36*(exponent+1)) <= limit:
            exponent += 1
        result.append(2*(exponent+valuation(factorial(8),p))+valuation(56,p))
    return result


def log_interval(n, d, scale):
    """Outward integer bounds for scale*log(n/d), given 1 <= n/d <= 2."""
    a, b = n-d, n+d
    total = steps = 0
    power_a, power_b = a, b
    while 3*scale*power_a >= power_b:
        total += (2*scale*power_a)//((2*steps+1)*power_b)
        power_a *= a*a
        power_b *= b*b
        steps += 1
    # Tail <= 2*scale*z^(2s+1)/(1-z²) < 1, where z<=1/3.
    return total, total+steps+1


def rounded_logs(primes, scale):
    extra = 10**7
    low2, high2 = log_interval(2, 1, scale*extra)
    out = []
    for p in primes:
        j = p.bit_length()-1
        lo, hi = log_interval(p, 2**j, scale*extra)
        lo += j*low2
        hi += j*high2
        rounded = (2*lo+extra)//(2*extra)
        assert 2*hi < (2*rounded+1)*extra and 2*lo >= (2*rounded-1)*extra
        out.append(rounded)
    return out


def determinant(matrix):
    a = [row[:] for row in matrix]
    sign = previous = 1
    for i in range(len(a)-1):
        if not a[i][i]:
            pivot = next((j for j in range(i+1,len(a)) if a[j][i]), None)
            if pivot is None:
                return 0
            a[i], a[pivot] = a[pivot], a[i]
            sign = -sign
        for j in range(i+1,len(a)):
            for k in range(i+1,len(a)):
                value = a[i][i]*a[j][k]-a[j][i]*a[i][k]
                assert value % previous == 0
                a[j][k] = value//previous
        previous = a[i][i]
    return sign*a[-1][-1]


def norm_bound(rows):
    gram = [[sum(u*v for u,v in zip(x,y)) for x in rows] for y in rows]
    minors = [1]+[determinant([row[:i] for row in gram[:i]]) for i in range(1,len(rows)+1)]
    return min(Fraction(b,a) for a,b in zip(minors,minors[1:]))


def lattice(primes, scale, weights, transform):
    assert abs(determinant(transform)) == 1
    logs = rounded_logs(primes, scale)
    return [[a*w for a,w in zip(row,weights)]+[sum(a*b for a,b in zip(row,logs))]
            for row in transform]


def check_short_vectors(rows, transform, B, primes, limit, power):
    """Enumerate a closed Euclidean ball by the exact Gram-Schmidt coordinates."""
    m = len(rows)
    mu = [[Fraction(0)]*m for _ in rows]
    norm = []
    for i in range(m):
        for j in range(i+1):
            v = sum(a*b for a,b in zip(rows[i],rows[j]))
            v -= sum(mu[i][k]*mu[j][k]*norm[k] for k in range(j))
            if j == i:
                norm.append(v)
            else:
                mu[i][j] = Fraction(v,norm[j])
    coeff = [0]*m
    equations = [sum((row[j]%2)<<i for i,row in enumerate(transform))
                 | ((valuation(56,p)%2)<<m) for j,p in enumerate(primes)]
    for i in range(m):
        pivot = next(j for j in range(i,m) if (equations[j]>>i)&1)
        equations[i], equations[pivot] = equations[pivot], equations[i]
        for j in range(m):
            if j != i and (equations[j]>>i)&1:
                equations[j] ^= equations[i]
    parity = [eq>>m for eq in equations]
    assert all(eq == (1<<i) + (parity[i]<<m) for i,eq in enumerate(equations))
    leaves = 0

    def visit(i, remaining):
        nonlocal leaves
        if i < 0:
            leaves += 1
            b = [sum(c*row[j] for c,row in zip(coeff,transform)) for j in range(m)]
            if any(abs(e)>cap or (e+valuation(56,p))%2 for p,e,cap in zip(primes,b,B)):
                return
            numerator = prod(p**max(0,e) for p,e in zip(primes,b))
            denominator = prod(p**max(0,-e) for p,e in zip(primes,b))
            assert abs(numerator-denominator)*power >= 6*denominator, b
            return
        center = sum((coeff[j]*mu[j][i] for j in range(i+1,m)),Fraction(0))
        den = center.denominator
        radius2 = remaining*den**2/norm[i]
        r = isqrt(radius2.numerator//radius2.denominator)
        start = -((r+center.numerator)//den)
        stop = (r-center.numerator)//den
        start += (parity[i]-start)%2
        for c in range(start,stop+1,2):
            coeff[i] = c
            visit(i-1, remaining-(c+center)**2*norm[i])

    visit(m-1,Fraction(limit))
    return leaves


def verify():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    primes = [p for p in range(2,54) if all(p%q for q in range(2,isqrt(p)+1))]
    assert len(primes) == 16 and 2*30**19*16**5*4**16 < 10**45
    assert 10**55 > 5*(1+55*3)*10**45
    assert 3**8*factorial(8) > 11**8 and factorial(6) >= 2**6
    assert Fraction(32,7) + Fraction(9,10**6) < 5
    for d, constant, counts in [(8,33000,(2,3,4)), (6,60000,(3,4,5))]:
        assert constant**2 > (6 if d==8 else 11)**2*factorial(6)*factorial(8)
        power = lcm(d,36)
        for j in counts:
            assert 36 > d*j
            h = 144
            while 10**(h*(power//d)) <= (constant*420*35519**j)**power * 10**((h-128)*j*(power//36)):
                h += 1
            print("For denominator",d,"at least",j+1,"crossing tuples from 10^",h)
    path = Path(__file__).with_name("Erdos849BalancedCuts.json")
    stages = json.loads(path.read_text(encoding="utf-8"))
    cap = 10**55
    for stage in stages:
        lower = stage["lower"]
        assert stage["cap"] == cap and 144 <= lower < cap
        factor = stage["factor"]
        assert factor > 0
        weights = [factor*(p.bit_length()-1) for p in primes]
        scale = factor*10**stage["digits"]
        rows = lattice(primes,scale,weights,stage["transform"])
        B = exponent_bounds(primes,cap)
        threshold = 10**(lower//8)
        rounding = 5*Fraction(scale,threshold)+Fraction(sum(B),2)
        limit = sum((a*w)**2 for a,w in zip(B,weights))+rounding**2
        if norm_bound(rows) > limit:
            print("Excluded interval",lower,cap,"by the squared length bound.")
        else:
            count = check_short_vectors(rows,stage["transform"],B,primes,limit,threshold)
            print("Excluded interval",lower,cap,"with",count,"vectors of the required parity.")
        cap = lower
    assert cap == 144


if __name__ == "__main__":
    verify()
