"""Check the geometric double-cover orbit and elliptic boundary specialization."""

from math import isqrt

from Erdos849ThreeFiveCurve import F0, gcd, power_x, prime, smooth, trim


def monic_sextic(p):
    assert prime(p) and smooth(F0,p)
    return [c*pow(F0[-1],-1,p)%p for c in F0]


def quotient(poly,divisor,p):
    assert divisor[-1] == 1
    a=poly.copy()
    q=[0]*(len(a)-len(divisor)+1)
    while len(a)>=len(divisor):
        i=len(a)-len(divisor)
        q[i]=a[-1]
        for j,v in enumerate(divisor):
            a[i+j]=(a[i+j]-q[i]*v)%p
        trim(a)
    return q,a


def irreducible(poly,p):
    for d in range(1,(len(poly)-1)//2+1):
        h=power_x(poly,p**d,p)+[0,0]
        h[1]=(h[1]-1)%p
        if len(gcd(poly,trim(h),p))>1:
            return False
    return True


def curve(quartic,p):
    m,b,a,c,leading=quartic
    assert leading==1
    B=c*pow(2,-1,p)%p
    C=(a-B**2)*pow(2,-1,p)%p
    L=(b-2*B*C)%p
    M=(m-C**2)%p
    return ((B**2-4*C)%p,(2*B*L-4*M)%p,L**2%p),(0,-L%p)


def point_order(abc,point,p):
    A,B,C=abc
    cubic=[C,B,A,1]
    assert len(gcd(cubic,[B,2*A%p,3],p))==1
    def on(P):
        x,y=P
        return (y**2-x**3-A*x*x-B*x-C)%p==0
    assert on(point)
    def plus(P,Q):
        if P is None: return Q
        if Q is None: return P
        x,y=P
        u,v=Q
        if x==u and (y+v)%p==0:
            return None
        slope=((v-y)*pow(u-x,-1,p) if x!=u else
               (3*x*x+2*A*x+B)*pow(2*y,-1,p))%p
        z=(slope*slope-A-x-u)%p
        R=(z,(slope*(x-z)-y)%p)
        assert on(R)
        return R
    P=None
    for k in range(1,p+2+isqrt(4*p)):
        P=plus(P,point)
        if P is None:
            return k
    raise AssertionError("order exceeds Hasse bound")


def main():
    if not __debug__:
        raise RuntimeError("Run with Python assertions enabled")
    assert F0 == (9, -80, 0, 200, 0, 0, 400)
    assert irreducible(monic_sextic(7), 7)
    q, rem = quotient(monic_sextic(41), [32, 1], 41)
    assert not rem and q == [37, 26, 12, 40, 9, 1] and irreducible(q, 41)
    print("Verified Frobenius cycle types (6) at 7 and (1,5) at 41.")

    sextic = monic_sextic(11)
    rows = (
        ([4, 3, 1], [4, 3, 5, 8, 1], (5, 8, 9), (0, 8), 17),
        ([6, 6, 1], [10, 5, 8, 5, 1], (0, 4, 4), (0, 9), 11),
        ([10, 4, 1], [6, 0, 6, 7, 1], (0, 8, 5), (0, 7), 15),
    )
    for divisor, expected_q, expected_abc, expected_point, order in rows:
        q, rem = quotient(sextic, divisor, 11)
        assert not rem and q == expected_q
        abc, point = curve(q, 11)
        assert (abc, point) == (expected_abc, expected_point)
        assert point_order(abc, point, 11) == order
        print(f"Quadratic {divisor} gives elliptic boundary order {order} modulo 11.")


if __name__ == '__main__':
    main()
