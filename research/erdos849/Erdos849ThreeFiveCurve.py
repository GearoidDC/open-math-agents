"""Exact arithmetic certificates for the two genus-two factors of columns 3,5."""

from fractions import Fraction
from itertools import combinations
from math import isqrt


# Coefficients in ascending order. A point (a,b,c) denotes (a/b,c/b^3).
F0 = (9,-80,0,200,0,0,400)
F1 = (1936,800,48,0,-12,0,1)
POINTS0 = ((0,1,3),(-1,1,17),(1,1,23),(-1,2,44),(2,3,191))
POINTS1 = ((-8,1,460),(-2,1,20),(0,1,44),(2,1,60),(12,1,1660),
           (-9,2,415),(-5,2,27),(-4,3,820),(6,7,17660),(46,7,89060))


def trim(poly):
    while poly and poly[-1]==0:
        poly.pop()
    return poly


def mul(f,g,p):
    out = [0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g):
            out[i+j] = (out[i+j]+a*b)%p
    return trim(out)


def remainder(f,g,p=None):
    f = list(f)
    inverse = pow(g[-1],-1,p) if p else 1/Fraction(g[-1])
    while len(f)>=len(g):
        k = len(f)-len(g)
        c = f[-1]*inverse
        for i,b in enumerate(g):
            f[k+i] -= c*b
            if p:
                f[k+i] %= p
        trim(f)
    return f


def gcd(f,g,p=None):
    while g:
        f,g = g,remainder(f,g,p)
    return f


def power_x(f,n,p):
    a,out = [0,1],[1]
    while n:
        if n%2:
            out = remainder(mul(out,a,p),f,p)
        a = remainder(mul(a,a,p),f,p)
        n //= 2
    return out


def prime(p):
    return p>=2 and all(p%i for i in range(2,isqrt(p)+1))


def smooth(f,p):
    g = [c%p for c in f]
    dg = trim([i*g[i]%p for i in range(1,len(g))])
    return bool(g[-1]) and len(gcd(g,dg,p))==1


def irreducible_prime(f):
    for p in range(3,500):
        if not prime(p) or not smooth(f,p):
            continue
        g = [c%p for c in f]
        for d in (1,2,3):
            poly = power_x(g,p**d,p)+[0,0]
            poly[1] = (poly[1]-1)%p
            if len(gcd(g,trim(poly),p))>1:
                break
        else:
            return p
    raise AssertionError("no irreducible sextic reduction found")


def hom(f,a,b):
    return sum(c*a**i*b**(6-i) for i,c in enumerate(f))


def squareclass_rank(f,points,target):
    a0,b0,_ = points[0]
    assert all(hom(f,a,b)==y*y for a,b,y in points)
    pivots,rows = {},[]
    for p in range(7,500):
        if not prime(p) or not smooth(f,p):
            continue
        roots = [x for x in range(p) if hom(f,x,1)%p==0]
        for i,j in combinations(roots,2):
            v = []
            for a,b,_ in points[1:]:
                numerator = (a-i*b)*(a0-j*b)%p
                denominator = (a-j*b)*(a0-i*b)%p
                if not numerator or not denominator:
                    break
                v.append(int(pow(numerator*denominator,(p-1)//2,p)==p-1))
            if len(v)!=len(points)-1:
                continue
            row = sum(x<<h for h,x in enumerate(v))
            while row and row.bit_length() in pivots:
                row ^= pivots[row.bit_length()]
            if row:
                pivots[row.bit_length()] = row
                rows.append((p,i,j,''.join(map(str,v))))
            if len(rows)==target:
                return rows
    raise AssertionError("insufficient independent squareclass tests")


def frobenius(f,p):
    assert prime(p) and smooth(f,p) and pow(f[-1],(p-1)//2,p)==1
    nonsquare = next(c for c in range(2,p) if pow(c,(p-1)//2,p)==p-1)

    def char(x):
        return 0 if x%p==0 else 1 if pow(x%p,(p-1)//2,p)==1 else -1

    n1 = p+2+sum(char(hom(f,x,1)) for x in range(p))
    n2 = p*p+2
    for x in range(p):
        for y in range(p):
            left,right = 0,0
            for c in reversed(f):
                left,right = (x*left+nonsquare*y*right+c)%p,(y*left+x*right)%p
            n2 += char(left*left-nonsquare*right*right)
    a = p+1-n1
    twice_b = a*a-p*p-1+n2
    assert twice_b%2==0
    b = twice_b//2
    return n1,n2,(p*p,-p*a,b,-a,1)


def trace_powers(f,n):
    """Newton sums of the zeros of a monic integral polynomial."""
    d = len(f)-1
    traces = [d]
    for k in range(1,n+1):
        base = k*f[d-k] if k<=d else 0
        base += sum(f[d-i]*traces[k-i] for i in range(1,min(k-1,d)+1))
        traces.append(-base)
    return traces


def polynomial_from_traces(traces):
    out = [1]
    for k in range(1,len(traces)):
        value = -sum(out[k-i]*traces[i] for i in range(1,k+1))
        assert value%k==0
        out.append(value//k)
    return list(reversed(out))


def totient(n):
    result,m = n,n
    for q in range(2,n+1):
        if m%q==0:
            result = result//q*(q-1)
            while m%q==0:
                m //= q
    return result


def cyclotomic_indices_at_most(d):
    # phi(m)>=sqrt(m/2), from phi(q^e)^2/q^e>=1 at every prime power
    # except 2, where the ratio is 1/2. Therefore m<=2*d^2.
    return [k for k in range(1,2*d*d+1) if totient(k)<=d]


def picard_upper(p):
    # Frobenius on H^1 of the genus-four Jacobian is the direct sum on the
    # factors. On wedge^2, tr(F^k)=(tr(F^k)^2-tr(F^(2k)))/2.
    rows = [frobenius(f,p) for f in (F0,F1)]
    traces = [sum(v) for v in zip(*(trace_powers(c,56) for _,_,c in rows))]
    traces2 = [(traces[k]**2-traces[2*k])//2 for k in range(29)]
    poly = polynomial_from_traces(traces2)
    for _ in range(4):
        assert not remainder(poly,[-p,1])
        out = [poly[-1]]
        for j in range(len(poly)-2,0,-1):
            out.append(poly[j]+p*out[-1])
        poly = list(reversed(out))
    # The leftover 24 eigenvalues are p times roots of unity only if their
    # normalized polynomial has a root of cyclotomic degree at most 24.
    # Test gcd modulo a good auxiliary prime to avoid large rational powers.
    q = 1000003
    assert prime(q) and q!=p
    normalized = [a*pow(p,i,q)%q for i,a in enumerate(poly)]
    for m in cyclotomic_indices_at_most(24):
        z = power_x(normalized,m,q)+[0]
        z[0] = (z[0]-1)%q
        if len(gcd(normalized,trim(z),q))>1:
            return rows,False
    return rows,True


def split_prime_check():
    """Check the same Picard upper bound by splitting H^1 modulo 20479."""
    q,p = 20479,7
    assert prime(q)
    eigenvalues = []
    for f in (F0,F1):
        _,_,char = frobenius(f,p)
        roots = [x for x in range(1,q) if sum(c*pow(x,i,q) for i,c in enumerate(char))%q==0]
        assert len(roots)==4
        eigenvalues.extend(roots)
    products = [a*b*pow(p,-1,q)%q for a,b in combinations(eigenvalues,2)]
    assert products.count(1)==4
    orders = set()
    for v in set(products):
        order = next(d for d in range(1,q) if (q-1)%d==0 and pow(v,d,q)==1)
        assert order==1 or order>2*24**2
        orders.add(order)
    print("Split-prime check",q,eigenvalues,sorted(orders))


if __name__=="__main__":
    for f,pts,target in ((F0,POINTS0,4),(F1,POINTS1,6)):
        print("Irreducibility prime",irreducible_prime(f))
        print("Independent two-descent witnesses",squareclass_rank(f,pts,target))
    for p in (7,11,13,17,19,23,29,31):
        if not all(smooth(f,p) for f in (F0,F1)):
            continue
        counts,ok = picard_upper(p)
        if ok:
            print("Geometric Picard rank <= 4, certified by prime",p,counts)
            break
    else:
        raise AssertionError("no Picard-rank upper bound certificate")
    split_prime_check()
