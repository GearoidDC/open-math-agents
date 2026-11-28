"""Eliminate empty prime assignments between individual Pascal numerator positions."""

from fractions import Fraction
from math import factorial, gcd, isqrt, lcm, prod
from pathlib import Path
import json
from Erdos849ThreeFiveCells import characteristic, norm_at


def valuation(x,p):
    assert x > 0
    count=0
    while x%p==0:
        count+=1
        x//=p
    return count


def row_states(k,chosen,p,limit):
    """For fixed exponent e in a, (selected valuation, forced host in block)."""
    period=p
    while period<=k:
        period*=p
    start=valuation(period,p)
    den=valuation(factorial(k),p)
    result=[set() for _ in range(limit+1)]
    for n in range(period):
        residues=[(n-i)%period for i in range(k)]
        deep=residues.index(0) if 0 in residues else None
        levels=[valuation(v,p) if v else 0 for v in residues]
        for power in ([0] if deep is None else range(start,limit+den+1)):
            if deep is not None:
                levels[deep]=power
            e=sum(levels)-den
            if 0<=e<=limit:
                top=max(levels)
                forced=bool(e) and all(i in chosen for i,v in enumerate(levels) if v==top)
                result[e].add((sum(levels[i] for i in chosen), forced))
    return result


def denominator(k,indices,j,other=5):
    D=1
    chosen=(j,) if other==5 else (3-j,4+j)
    for p in primes(max(k,other)):
        # Beyond this point both maxima are unique, and the same offset
        # in the period may be used at the previous exponent.
        limit=2+max(valuation(factorial(n),p) for n in (k,other))
        states=row_states(k,indices,p,limit)
        others=row_states(other,chosen,p,limit)
        cost=max(s+t-e for e in range(limit+1)
                 for s,u in states[e] for t,v in others[e] if not (u and v))
        D*=p**max(0,cost)
    return D


def bounds(terms,i,j,k,base,other=5):
    inds=(i,) if k==3 else (2-i,3+i)
    D=denominator(k,inds,j,other)
    roots=(-1,0,1) if k==3 else (0,2,6)
    other_roots=tuple(range(5)) if other==5 else (0,2,6,12)
    q=Fraction(factorial(k),factorial(other))
    coeffs=characteristic(i,other_roots[j],terms,cubic_roots=roots,
                          other_roots=other_roots,ratio=q,multiplier=Fraction(D,factorial(k)))
    assert all(d<0 for poly in coeffs for d in poly)
    norms=[norm_at(poly,base) for poly in coeffs]
    low,high=0,1
    def good(u):
        return norms[0]*u**2+norms[1]*u+norms[2] < u**3
    while not good(high):
        high*=2
    while high-low>1:
        middle=(low+high)//2
        if good(middle):
            high=middle
        else:
            low=middle
    return high,coeffs,D


def fixed_divisor(terms):
    """Integer values on a degree-bounding grid generate the fixed divisor."""
    amax,bmax,cmax=[max(t[i] for t in terms) for i in range(3)]
    regular=[sum(c*x**a*y**b for a,b,z,c in terms if not z)
             for x in range(amax+1) for y in range(bmax+1)]
    powers=[sum(c*v**z for a,b,z,c in terms if z) for v in range(cmax+1)]
    return gcd(*regular,*powers)


def evaluator(terms,q):
    amax,bmax,cmax=[max(t[i] for t in terms) for i in range(3)]
    regular=[[0]*(bmax+1) for _ in range(amax+1)]
    special=[0]*(cmax+1)
    for a,b,z,c in terms:
        if z:
            special[z]=c%q
        else:
            regular[a][b]=c%q
    def value(poly,x):
        out=0
        for c in reversed(poly):
            out=(out*x+c)%q
        return out
    table=[value(special,z) for z in range(q)]
    by_y=[[value(poly,y) for poly in regular] for y in range(q)]
    return lambda x,y,z: (value(by_y[y],x)+table[z])%q


def image(k,i,j,D,terms,divisor,q,other=5):
    """A superset of the possible F/divisor modulo q, a power of p."""
    roots=(-1,0,1) if k==3 else (0,2,6)
    xs=range(q) if k==3 else sorted({(n-2)*(n-3)%q for n in range(q)})
    evaluate=evaluator(terms,q)
    left=Fraction(D,factorial(k))
    right=Fraction(D,factorial(other))
    ratio=Fraction(factorial(k),factorial(other))
    other_roots=tuple(range(5)) if other==5 else (0,2,6,12)
    r=other_roots[j]
    by_val={}
    for x in xs:
        poly=prod(x-r for r in roots)
        by_val.setdefault(ratio.denominator*poly%q,[]).append(x)
    residues=set()
    ys=range(q) if other==5 else sorted({((m-3)*(m-4)-r)%q for m in range(q)})
    for y in ys:
        poly=prod(y+r-s for s in other_roots)
        for x in by_val.get(poly*ratio.numerator%q,[]):
            a=y*left.denominator%q
            b=left.numerator*prod(x-s for t,s in enumerate(roots) if t!=i)%q
            c=(x-roots[i])*right.denominator%q
            d=right.numerator*prod(y+r-s for s in other_roots if s!=r)%q
            # Solve both linear congruences for the integral third coordinate.
            if gcd(a,q)>gcd(c,q):
                a,b,c,d=c,d,a,b
            g=gcd(a,q)
            if b%g:
                continue
            step=q//g
            first=(b//g)*pow(a//g,-1,step)%step
            for z in range(first,q,step):
                if c*z%q==d:
                    residues.add(evaluate(x,y,z))
    return [s for s in range(q) if s*divisor%q in residues]


def primes(limit):
    return [p for p in range(2,limit+1) if all(p%t for t in range(2,isqrt(p)+1))]


def range_sieve(cap,rules):
    """Intersect periodic bitsets on successive closed integer intervals."""
    if cap==0:
        return [0] if all(0 in ids for _,ids in rules) else []
    # Factor out a single sparse residue wheel before building bitsets.
    q,allowed=min(rules,key=lambda row:len(row[1])/row[0])
    extra=list(sorted((r for r in rules if r[0]!=q),key=lambda r:len(r[1])/r[0]))
    # In each progression, the subsequent wheel indices only depend on the
    # index of the first residue modulo each other modulus.
    block=131072
    whole=(1<<block)-1
    masks=[]
    for mod,ids in extra:
        inverse=pow(q,-1,mod)
        one=sum(1<<(s*inverse%mod) for s in ids)
        rep=(block+2*mod-1)//mod
        masks.append((mod,inverse,one*(((1<<(mod*rep))-1)//((1<<mod)-1))))
    survivors=[]
    for r in allowed:
        first=-((cap+r)//q)
        last=(cap-r)//q
        for lo in range(first,last+1,block):
            size=min(block,last-lo+1)
            bits=whole if size==block else (1<<size)-1
            for mod,inv,mask in masks:
                bits &= mask >> ((lo+inv*r)%mod)
                if not bits:
                    break
            while bits:
                bit=bits&-bits
                survivors.append(r+q*(lo+bit.bit_length()-1))
                bits-=bit
    return sorted(survivors)


def direct_image(k,i,j,D,terms,divisor,q,other):
    # Independent small-modulus control. Enumerate actual row residues
    # and all q values of the auxiliary coordinate.
    roots=(-1,0,1) if k==3 else (0,2,6)
    ys=tuple(range(5)) if other==5 else (0,2,6,12)
    left=Fraction(D,factorial(k))
    right=Fraction(D,factorial(other))
    ratio=Fraction(factorial(k),factorial(other))
    observed=set()
    for n in range(q):
        x=n-1 if k==3 else (n-2)*(n-3)
        for m in range(q):
            Y=m if other==5 else (m-3)*(m-4)
            if (ratio.denominator*prod(x-t for t in roots)-
                ratio.numerator*prod(Y-t for t in ys))%q:
                continue
            y=Y-ys[j]
            for z in range(q):
                if (left.denominator*y*z-left.numerator*prod(x-t for t in roots if t!=roots[i]))%q:
                    continue
                if (right.denominator*(x-roots[i])*z-right.numerator*prod(Y-t for t in ys if t!=ys[j]))%q:
                    continue
                observed.add(sum(c*x**a*y**b*z**d for a,b,d,c in terms)%q)
    return [u for u in range(q) if divisor*u%q in observed]


def solve_cell(k,i,j,divisor,terms,other=5):
    if other==5:
        floor=2600000000000
        assert (floor+5)**5 < 120*10**60
    else:
        floor=14*10**15
        assert (isqrt(floor)+8)**8 < factorial(8)*10**60
    bound,_,D=bounds(terms,i,j,k,floor,other)
    assert divisor==fixed_divisor(terms)
    cap=(bound-1)//divisor
    rules=[]
    for p in primes(397):
        q={2:256,3:243,5:125}.get(p,p)
        residues=image(k,i,j,D,terms,divisor,q,other)
        if len(residues)<q:
            rules.append((q,residues))
    for q in (7,8,9):
        assert image(k,i,j,D,terms,divisor,q,other)==direct_image(k,i,j,D,terms,divisor,q,other)
    # Check the genuine common value 3003 wherever the auxiliary
    # coordinate is integral, including against the non-prime moduli.
    control=False
    if (k,other)==(6,5):
        x=(14-2)*(14-3)
        y=15-j
        z=Fraction(D*3003,(x-(0,2,6)[i])*y)
        if z.denominator==1:
            val=sum(c*x**a*y**b*int(z)**e for a,b,e,c in terms)
            assert val%divisor==0
            assert all((val//divisor)%q in ids for q,ids in rules)
            control=True
    assert not range_sieve(cap,rules), (k,other,i,j)
    return cap,control


if __name__=='__main__':
    import sys
    if not __debug__:
        raise RuntimeError("Enable assertions.")
    selectors=list(map(int,sys.argv[1:]))
    rows=json.loads(Path(__file__).with_suffix('.json').read_text())
    cells={(k,h,i,j) for k,h,t in ((3,5,5),(6,5,5),(6,8,4)) for i in range(3) for j in range(t)}
    assert len(rows)==len(cells)==42 and {(k,h,i,j) for k,i,j,g,f,h in rows}==cells
    rules=[(5,[0,3]),(7,[0,1,6]),(11,[3,7,9]),(13,[2,5,8])]
    for cap in (0,1,60,2000,350000):
        assert range_sieve(cap,rules)==[u for u in range(-cap,cap+1) if all(u%q in ids for q,ids in rules)]
    for k,i,j,divisor,terms,other in rows:
        if [k,other,i,j][:len(selectors)]!=selectors:
            continue
        cap,control=solve_cell(k,i,j,divisor,terms,other)
        print(k,other,i,j,cap,"3003 control" if control else "",flush=True)
