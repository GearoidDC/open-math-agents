"""Eliminate single quadratic numerator slots by matching polynomial square roots."""

from fractions import Fraction
from math import comb, factorial, gcd, isqrt


def mul(f,g):
    out = [0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g):
            out[i+j] += a*b
    return out


def subtract(f,g):
    out = list(f)+[0]*max(0,len(g)-len(f))
    for i,b in enumerate(g):
        out[i] -= b
    while out and not out[-1]:
        out.pop()
    return out


def uniform_sign(f,U):
    translated = [sum(f[i]*comb(i,j)*U**(i-j) for i in range(j,len(f)))
                  for j in range(len(f))]
    return all(c>0 for c in translated) or all(c<0 for c in translated)


def proper_row(a,k):
    if a < comb(2*k,k):
        return None
    t = factorial(k)*a
    z = 1 << ((t.bit_length()+k-1)//k)
    while True:
        v = ((k-1)*z+t//z**(k-1))//k
        if v>=z:
            break
        z=v
    return next((x for x in range(max(z,2*k),z+k+1) if comb(x,k)==a),None)


def verify(k,h,d,r,U=20000):
    den = factorial(k)//gcd(factorial(k),factorial(h))
    c = 256*den**2*factorial(h)//factorial(k)
    scale, linear, constant = ((den**2,4096*den**2,0) if h==8
                               else (4*den**2,189*den**2,900*den**2))
    roots = tuple(s*s for s in range(1,h,2))
    A = [c]
    for i in range(k):
        A = mul(A,[r-i,0,d])
    lead = isqrt(A[-1])
    assert lead*lead == A[-1]
    high = [Fraction(lead)]
    for i in range(1,k+1):
        high.append((A[-1-i]-sum(high[j]*high[i-j] for j in range(1,i)))/(2*Fraction(lead)))
    assert all(a.denominator==1 for a in high)
    Q = [int(a) for a in reversed(high)]
    R = subtract(mul(Q,Q),A)
    assert len(R)<=k
    assert 2*sum(map(abs,Q[:-1])) < lead*U
    y_bound = 1
    while y_bound**len(roots) <= c*(d+k)**k:
        y_bound *= 2
    assert 2*k <= (k-1)*len(roots)
    assert 2*(linear*(roots[-1]+y_bound)+constant+sum(map(abs,R))) < lead*U
    F = [1]
    for j in roots:
        F = mul(F,subtract(R,[constant+linear*j]))
    F = subtract([scale*a for a in F],[linear**len(roots)*a for a in A])
    assert uniform_sign(F,U)
    hits = []
    for u in range(1,U):
        m = d*u*u+r
        if m>=2*k and (n:=proper_row(comb(m,k),h)) is not None:
            hits.append((u,m,n))
    assert not hits, (k,d,r,hits)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    for k,h,d in ((3,8,105),(5,8,21),(7,8,2),(5,6,6),(7,6,7)):
        for r in range(k):
            verify(k,h,d,r)
        print('columns',k,h,'square class',d,'all',k,'offsets excluded',flush=True)
