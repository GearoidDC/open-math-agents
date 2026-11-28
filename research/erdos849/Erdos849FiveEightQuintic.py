"""Frobenius computation for the genus-six quotient of columns five and eight."""

from array import array
from itertools import product
from math import gcd as integer_gcd

from Erdos849PatternGeometryQuartics import branch_clear
from Erdos849ThreeFiveCurve import gcd, mul, polynomial_from_traces, power_x, prime, remainder, trim


def prime_factors(n):
    factors = []
    q = 2
    while q*q <= n:
        if n%q == 0:
            factors.append(q)
            while n%q == 0:
                n //= q
        q += 1
    return factors+[n] if n>1 else factors


def logs(p,d):
    size = p**d
    order = size-1
    factors = prime_factors(order)
    result = array("i",[-1])*size
    if d == 1:
        g = next(i for i in range(1,p) if all(pow(i,order//q,p)!=1 for q in factors))
        v = 1
        for j in range(order):
            result[v] = j
            v = v*g%p
        return result
    constants = [a for a in range(1,p) if all(
        pow((-1)**d*a,(p-1)//r,p)!=1 for r in prime_factors(p-1))]
    for rest in product(range(p),repeat=d-1):
        for a in constants:
            f = [a,*rest,1]
            if power_x(f,order,p) == [1] and all(power_x(f,order//q,p)!=[1] for q in factors):
                break
        else:
            continue
        break
    else:
        raise ValueError("no primitive polynomial")
    half = p**(d//2)
    def addition_table(coeffs):
        table = []
        for top in range(p):
            row = []
            for n in range(p**len(coeffs)):
                value = 0
                for i,c in enumerate(coeffs):
                    n, digit = divmod(n,p)
                    value += ((digit-top*c)%p)*p**i
                row.append(value)
            table.append(row)
        return table
    lo, hi = addition_table(f[:d//2]), addition_table(f[d//2:d])
    v = 1
    for j in range(order):
        result[v] = j
        top, rest = divmod(v*p,size)
        b,a = divmod(rest,half)
        v = lo[top][a]+half*hi[top][b]
    assert v == 1 and result.count(-1) == 1
    return result


def point_count(p,d):
    l = logs(p,d)
    q = len(l)
    def histogram(roots, factor):
        counts = array("I",[0])*q
        roots = [x%p for x in roots]
        c = l[factor%p]
        for block in range(0,q,p):
            digits = list(l[block:block+p])*2
            for i in range(p):
                vals = [digits[p+i-r] for r in roots]
                index = q-1 if -1 in vals else (c+sum(vals))%(q-1)
                counts[index] += 1
        return counts
    xs = histogram((-2,-1,0,1,2),86016)
    ys = histogram((1,9,25,49),1)
    return 1+sum(a*b for a,b in zip(xs,ys))


def frobenius(p):
    # At 5 the affine derivative with respect to x is the nonzero constant
    # 4*86016, and the single infinity point has nonzero z-derivative.
    assert prime(p) and (p == 5 or (p > 7 and branch_clear(5,p)))
    counts = [point_count(p,d) for d in range(1,7)]
    top = polynomial_from_traces([12]+[p**i+1-n for i,n in enumerate(counts,1)])
    f = [top[6-i]*p**(6-i) for i in range(6)]+top
    return counts,f


def irreducible_at(f,p):
    d = len(f)-1
    f = [v%p for v in f]
    for r in prime_factors(d):
        h = power_x(f,p**(d//r),p)+[0,0]
        h[1] = (h[1]-1)%p
        if len(gcd(f,trim(h),p))>1:
            return False
    return power_x(f,p**d,p) == [0,1]


def distinct_powers(f,q):
    degree = len(f)-1
    bound = degree*(degree-1)
    limit = 2*bound**2
    phi = list(range(limit+1))
    for p in range(2,limit+1):
        if phi[p] == p:
            for j in range(p,limit+1,p):
                phi[j] -= phi[j]//p
    candidates = {n for n in range(1,limit+1) if phi[n] <= bound}
    f = [a%q for a in f]
    assert irreducible_at(f,q)
    for r in prime_factors(degree):
        step = power_x(f,q**(degree//r)-1,q)
        v = [1]
        for n in range(1,max(candidates)+1):
            v = remainder(mul(v,step,q),f,q)
            assert n not in candidates or v != [1], (r,n)
    return len(candidates),max(candidates)


def real_polynomial(f,p):
    d = (len(f)-1)//2
    a,b = [2],[0,1]
    g = [f[d]]+[0]*d
    for j in range(1,d+1):
        for i,v in enumerate(b):
            g[i] += v*f[d+j]
        next_poly = [0,*b]
        for i,v in enumerate(a):
            next_poly[i] -= p*v
        a,b = b,next_poly
    return g


def factor_degrees(f,p):
    f = [v%p for v in f]
    d = len(f)-1
    if len(gcd(f,trim([i*f[i]%p for i in range(1,d+1)]),p))>1:
        return []
    degrees = []
    for i in range(1,d+1):
        poly = power_x(f,p**i,p)+[0,0]
        poly[1] = (poly[1]-1)%p
        count = len(gcd(f,trim(poly),p))-1-sum(j for j in degrees if i%j==0)
        assert count%i == 0
        degrees += [i]*(count//i)
        if sum(degrees)==d:
            break
    return degrees


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    data = {
        5: ([16,46,121,546,3126,15601],164791),
        11: ([25,137,1408,14601,160475,1776362],6256468),
        13: ([27,215,2109,28671,373762,4819625],14817888),
    }
    polys = {}
    for p,(expected,order) in data.items():
        counts,f = frobenius(p)
        assert counts == expected and sum(f)==order
        polys[p] = f
        print(p,counts,"Jacobian order",order,flush=True)
    for p,q in ((11,53),(13,43)):
        assert distinct_powers(polys[p],q) == (262,510)
        print("Frobenius and irreducible reduction",p,polys[p],q,flush=True)
    g11,g13 = (real_polynomial(polys[p],p) for p in (11,13))
    assert factor_degrees(g11,3) == [1,5] and factor_degrees(g11,5) == [1,2,3]
    assert factor_degrees(polys[11],23) == [2,5,5]
    assert factor_degrees(g11,59) == [1,5] and irreducible_at(g13,59)
    orders = [n for _,n in data.values()]
    assert integer_gcd(*orders)==1
    for p in data:
        assert any(n % p for q,(_,n) in data.items() if q != p)
    print("Full signed permutation group at 11; real sextics distinguished at 59.")
