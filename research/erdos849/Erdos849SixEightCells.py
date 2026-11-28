"""Generate and check small rational functions on the reflected (6,8) curve."""

from fractions import Fraction as F
from math import factorial, gcd, lcm
from itertools import permutations

from Erdos849ThreeFiveCells import characteristic as reconstruct, plus, times, monomial, norm_at


S = (0,2,6)
R = (0,2,6,12)
BOUNDS = {
    120: ((138,9,363,21),(14,10,43,2),(33,1,92,35)),
    144: ((2981,169,10357,412),(253,268,770,41),(587,23,1663,634)),
}


def block_cofactor(k,s):
    # Each cofactor divides lcm(1,...,k). At each prime the smaller of
    # the two term valuations is bounded by that of their gap.
    gap = 1 + 2*s
    return gcd(factorial(k), lcm(*range(1,k+1))*gap)


def cubic_rhs(r):
    poly={0:F(1,56)}
    for q in R:
        poly=times(poly,{1:1,0:r-q})
    return poly


def multiply(a,b,rhs):
    out=[{} for _ in range(5)]
    for i,f in enumerate(a):
        for j,g in enumerate(b):
            out[i+j]=plus(out[i+j],times(f,g))
    for n in (4,3):
        out[n-1]=plus(out[n-1],monomial(out[n],0,8))
        out[n-2]=plus(out[n-2],monomial(out[n],0,-12))
        out[n-3]=plus(out[n-3],times(out[n],rhs))
    return out[:3]


def z_element(s,scale):
    u,v=[a for a in S if a!=s]
    return [{-1:scale*u*v},{-1:-scale*(u+v)},{-1:scale}]


def characteristic(f,rhs):
    x=[{},{0:1},{}]
    xf=multiply(x,f,rhs)
    cols=[f,xf,multiply(x,xf,rhs)]
    trace=plus(*(c[j] for j,c in enumerate(cols)))
    minors=[]
    for i in range(3):
        for j in range(i):
            minors.extend((times(cols[i][i],cols[j][j]),monomial(times(cols[j][i],cols[i][j]),0,-1)))
    det=[]
    for perm in permutations(range(3)):
        sign=(-1)**sum(perm[i]<perm[j] for i in range(3) for j in range(i))
        det.append(monomial(times(times(cols[0][perm[0]],cols[1][perm[1]]),cols[2][perm[2]]),0,-sign))
    return [monomial(trace,0,-1),plus(*minors),plus(*det)]


def linear(a,b,coeff):
    out=dict(a)
    for k,v in b.items():
        out[k]=out.get(k,0)+coeff*v
        if not out[k]:
            del out[k]
    return out


def candidates(s,r,scale,max_degree):
    rhs=cubic_rhs(r)
    z=z_element(s,scale)
    power=[{0:1},{},{}]
    pivots={}
    for c in range(1,max_degree+1):
        power=multiply(power,z,rhs)
        obj={(0,0,c):F(1)}
        remainder={}
        for i,col in enumerate(power):
            for j,a in col.items():
                if j>=0:
                    obj[i,j,0]=-a
                else:
                    remainder[i,j]=a
        while remainder:
            lead=max(remainder,key=lambda ij:4*ij[0]+3*ij[1])
            weight=4*lead[0]+3*lead[1]
            if lead in pivots:
                old,p=pivots[lead]
                coeff=-F(remainder[lead],old[lead])
                remainder=linear(remainder,old,coeff)
                obj=linear(obj,p,coeff)
            else:
                pivots[lead]=remainder,obj
                if weight<0:
                    denom=lcm(*(F(v).denominator for v in obj.values()))
                    common=gcd(*(int(v*denom) for v in obj.values()))
                    factor=F(denom,common)
                    f=[{} for _ in range(3)]
                    for (i,j),v in remainder.items():
                        f[i][j]=factor*v
                    yield c,weight,{key:int(v*factor) for key,v in obj.items()},characteristic(f,rhs)
                break


def cap_for(polys,degree,base):
    if any(j>=0 for p in polys for j in p) or not polys[-1]:
        return 0
    j=max(polys[-1])
    if abs(polys[-1][j])*F(base)**j<=norm_at({k:v for k,v in polys[-1].items() if k!=j},base):
        return 0
    bounds=[norm_at(p,base) for p in polys]
    def ok(n):
        return sum(v*n**(i*degree) for i,v in enumerate(bounds,1)) < 1
    lo,hi=0,1
    while ok(hi): lo,hi=hi,2*hi
    while hi-lo>1:
        m=(lo+hi)//2
        if ok(m): lo=m
        else: hi=m
    return lo


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    for i,s in enumerate(S):
        for j,r in enumerate(R):
            D = block_cofactor(6,i)*block_cofactor(8,j)
            assert D % factorial(6) == 0
            scale = D//factorial(6)
            options = list(candidates(s,r,scale,12))
            for height, matrix in BOUNDS.items():
                base = 14*10**(height//4)
                # sqrt(14) < 15/4 and every factor of the selected
                # pair is at least (8!a)^(1/8)-7.
                assert height % 4 == 0 and 14*16 < 15**2
                assert (15*10**(height//8)+28)**8 < 4**8*factorial(8)*10**height
                assert height % 8 == 0
                bound = matrix[i][j]
                degree, _, obj, polys = next(
                    item for item in options if cap_for(item[3],item[0],base) >= bound)
                # Check the entire integer polynomial against its computed
                # normal form by an independently implemented reduction.
                assert max(key[2] for key in obj)==degree
                terms = [(*key,c) for key,c in obj.items()]
                assert reconstruct(i,r,terms,cubic_roots=S,other_roots=R,
                                   ratio=F(1,56),multiplier=scale) == polys
                print(height,s,r,degree,bound)


if __name__ == "__main__":
    main()
