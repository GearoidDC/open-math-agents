"""Integral and local checks for individual positions in two falling factorials."""

from fractions import Fraction
from functools import cache
from math import factorial, gcd, isqrt, lcm, prod

from Erdos849CellSieve import row_states,valuation
from Erdos849SaturatedCells import add,floor_root,multiply,product_polynomial

def falling(x,k):
    return prod(x-r for r in range(k))


def derivative(x,k):
    return sum(prod(x-r for r in range(k) if r!=s) for s in range(k))


@cache
def missing_denominator(k,h,i,j):
    assert 0<=i<k<h and 0<=j<h
    D=1
    for p in range(2,h+1):
        if any(p%t==0 for t in range(2,isqrt(p)+1)):continue
        limit=3+max(valuation(factorial(r),p) for r in (k,h))
        left=row_states(k,(i,),p,limit);right=row_states(h,(j,),p,limit)
        cost=max(u+v-e for e in range(limit+1) for u,forced in left[e]
                 for v,other in right[e] if not(forced and other))
        D*=p**max(0,cost)
    return D


@cache
def slope_bounds(k,h,height):
    assert gcd(k,h)==1
    B=floor_root(factorial(h)*10**height,k*h)-1
    y=B**k
    assert (y+h-1)**h<factorial(h)*10**height
    ratio=Fraction(factorial(k),factorial(h));den=10**6
    n=floor_root(den**k*ratio.numerator//ratio.denominator,k)
    lo,hi=Fraction(n-1,den),Fraction(n+2,den)
    assert 0<lo**k<ratio*Fraction(y-h+1,y)**h
    high=hi-Fraction(k-1,B**h)
    assert high>0 and high**k>ratio*Fraction(y+h-1,y)**h
    return B,lo,hi


def integer_valued(poly):
    nonintegral=[(u,v,c.numerator%c.denominator,c.denominator)
                 for (u,v),c in poly.items() if c.denominator>1]
    if not nonintegral:return
    D=lcm(*(den for u,v,b,den in nonintegral))
    dx=max(u for u,v,b,den in nonintegral);dy=max(v for u,v,b,den in nonintegral)
    terms=[(u,v,b*(D//den)) for u,v,b,den in nonintegral]
    # The reduced numerator also depends only on the two residues modulo D.
    for x in range(min(dx+1,D)):
        coeffs=[0]*(dy+1)
        for u,v,c in terms:coeffs[v]+=c*x**u
        coeffs=[c%D for c in coeffs]
        for y in range(min(dy+1,D)):
            value=0
            for a in reversed(coeffs):value=(value*y+a)%D
            assert value==0


def normal_form(k,h,i,j,cs):
    rel=product_polynomial(range(k),0,(1,0));del rel[k,0]
    rel={key:-v for key,v in rel.items()}
    add(rel,product_polynomial(range(h),j,(0,1)),Fraction(factorial(k),factorial(h)))
    z={}
    add(z,product_polynomial([s for s in range(k) if s!=i],0,(1,0)),
        Fraction(missing_denominator(k,h,i,j),factorial(k)),offset_y=-1)
    P={(0,0):1};out={}
    for t,c in enumerate(cs,1):
        raw=multiply(P,z);add(raw,P,1-t)
        for u in range(2*k-2,k-1,-1):
            for key in [e for e in raw if e[0]==u]:add(raw,rel,raw.pop(key),u-k,key[1])
        P={e:Fraction(a,t) for e,a in raw.items() if a};add(out,P,c)
    return out


@cache
def lifted(k,h,p,E,x0,m0):
    ratio=factorial(h)//factorial(k)
    dx=ratio*derivative(x0,k)%p;dm=-derivative(m0,h)%p
    move_x=bool(dm);assert dx or dm
    inv=pow(dm if move_x else dx,-1,p);result=[]
    for t in range(E):
        x=x0+p*t if move_x else x0
        m=m0 if move_x else m0+p*t
        precision=p
        for _ in range(1,E):
            diff=ratio*falling(x,k)-falling(m,h)
            assert diff%precision==0
            digit=(-(diff//precision)*inv)%p
            if move_x:m+=digit*precision
            else:x+=digit*precision
            precision*=p
        assert (ratio*falling(x,k)-falling(m,h))%precision==0
        result.append((x,m))
    return result


def check_local(k,h,i,j,cs,p,E,x,m,poly):
    assert type(E) is int and E>=1 and cs and all(type(c) is int for c in cs)
    assert p>max(h,len(cs)) and not any(p%r==0 for r in range(2,isqrt(p)+1))
    assert 0<=x<p and 0<=m<p and (x,m)!=(i,j)
    modulus=p**E;D=missing_denominator(k,h,i,j);assert D%p
    reg=[(u,v,c.numerator*pow(c.denominator,-1,modulus)%modulus) for (u,v),c in poly.items() if v>=0]
    degree=max((v for _,v,_ in reg),default=0)
    inverses=[pow(t,-1,modulus) for t in range(1,len(cs)+1)]
    for n,row in lifted(k,h,p,E,x,m):
        y=row-j
        lhs=D*prod(n-r for r in range(k) if r!=i)
        rhs=D*prod(row-r for r in range(h) if r!=j)
        if x!=i:z=rhs*pow(factorial(h)*(n-i),-1,modulus)%modulus
        else:z=lhs*pow(factorial(k)*y,-1,modulus)%modulus
        assert (factorial(k)*y*z-lhs)%modulus==(factorial(h)*(n-i)*z-rhs)%modulus==0
        power=1;value=0
        for t,(c,inv) in enumerate(zip(cs,inverses),1):
            power=power*(z+1-t)*inv%modulus;value+=c*power
        nx=[1];my=[1]
        for _ in range(k-1):nx.append(nx[-1]*n%modulus)
        for _ in range(degree):my.append(my[-1]*y%modulus)
        value-=sum(c*nx[u]*my[v] for u,v,c in reg)
        assert value%modulus==0
    return True
