"""Replay the real interpolation certificate beginning at 10^184."""
import gzip
import json
from functools import lru_cache
from math import comb, factorial, prod
from pathlib import Path
from fractions import Fraction

from Erdos849RealInterval import integer_root, lebesgue_bound, scaled_row
from Erdos849ResidueDisks import fibers

COLUMNS = (8, 7, 5, 3)
START = 10**184
DIVISOR = 900
NODE_DEN = 1 << 28
SAMPLE_SCALE = 1 << 1250
ROW_SCALE = 1 << 2600
CONTROL_SCALE = 1 << 120


def ceil_div(a,b):
    return -((-a)//b)


def controls(nodes, powers, parents, start=START, divisor=DIVISOR):
    assert type(start) is int and start>1 and type(divisor) is int and divisor>=1
    assert nodes == sorted(set(nodes)) and nodes[0] == 0 and nodes[-1] == NODE_DEN
    J = len(nodes)
    assert J == 115
    assert all(len(es)==4 and all(type(e) is int and 0<=e<k for e,k in zip(es,COLUMNS)) for es in powers)
    assert all(len(row)==len(powers) and all(type(c) is int for c in row) for row in parents)
    S,D,T = SAMPLE_SCALE, ROW_SCALE, CONTROL_SCALE
    upper = []
    for k in COLUMNS:
        b = integer_root(factorial(k)*start,k)
        w = 840//k
        assert b*7**w > 100*k**4*8**w
        upper.append(ceil_div((b+1)*(9*divisor+8)**w,(8*divisor)**w)+4*k*k)
    maxima = [prod(x**e for x,e in zip(upper,es)) for es in powers]
    assert all(S*sum(es)*m<D for es,m in zip(powers,maxima))
    samples = []
    den = (divisor*NODE_DEN)**840
    sd = [D**sum(es) for es in powers]
    for r in nodes:
        num = start*(divisor*NODE_DEN+r)**840
        x = [scaled_row(k,factorial(k)*num*D**k//den,D) for k in COLUMNS]
        mon = [S*prod(y**e for y,e in zip(x,es))//div for es,div in zip(powers,sd)]
        samples.append([sum(c*v for c,v in zip(row,mon)) for row in parents])

    # The coefficient of z^j in (1+z)^(J-1) P(z/(1+z)) is
    # binom(J-1,j) times the j-th Bernstein control of P.
    full = [1]
    for r in nodes:
        full = [(NODE_DEN-r)*u-r*v for u,v in zip([0]+full,full+[0])]
    sums = [[0]*J for _ in parents]
    binoms = [comb(J-1,j) for j in range(J)]
    for r,vals in zip(nodes,samples):
        # Divide the full product by -r+(NODE_DEN-r)z exactly.
        if not r:
            partial = [v//NODE_DEN for v in full[1:]]
        else:
            partial = []
            last = 0
            for v in full[:-1]:
                last,rem = divmod((NODE_DEN-r)*last-v,r)
                assert rem==0
                partial.append(last)
        card_den = prod(r-h for h in nodes if h!=r)
        for j,(coef,bc) in enumerate(zip(partial,binoms)):
            bottom = S*bc*card_den
            for ans,val in zip(sums,vals):
                ans[j] += (T*val*coef)//bottom

    leb = lebesgue_bound(nodes)
    nodal = max(prod(max(abs(a-r),abs(b-r)) for r in nodes) for a,b in zip(nodes,nodes[1:]))
    errors = []
    for cs in parents:
        # At most one unit per cardinal summand was lost in storing each control.
        rounding = ceil_div(T*leb*2*sum(map(abs,cs)),S)
        remainder = ceil_div(T*sum(abs(c)*m for c,m in zip(cs,maxima))*8**J*nodal,
                             (divisor*NODE_DEN)**J)
        errors.append(J+rounding+remainder)
    return sums,errors


def bisect_controls(rows):
    left,right = [],[]
    for row in rows:
        layer = row
        l,r = [layer[0]],[layer[-1]]
        for j in range(1,len(row)):
            layer = [a+b for a,b in zip(layer,layer[1:])]
            l.append(layer[0]>>j)
            r.append(layer[-1]>>j)
        left.append(l)
        right.append(r[::-1])
    return left,right


@lru_cache(None)
def finite_values(p,powers,parents):
    assert p in (11,13,17,19,23,29,31)
    out = set()
    for pts in fibers(COLUMNS,p,False).values():
        for point in pts:
            m = [prod(pow(x,e,p) for x,e in zip(point,es))%p for es in powers]
            out.add(tuple(sum(c*v for c,v in zip(cs,m))%p for cs in parents))
    return sorted(out)


def small(combo,rows,errors):
    err = sum(abs(c)*e for c,e in zip(combo,errors))
    room = CONTROL_SCALE-err
    return room>0 and all(abs(sum(c*v for c,v in zip(combo,col)))<room for col in zip(*rows))


def verify(data,start=START,divisor=DIVISOR):
    if not __debug__:
        raise RuntimeError('Enable assertions to verify this certificate.')
    nodes,powers,parents,tree = data
    assert 1<=len(parents)<=20
    rows,errors = controls(nodes,powers,parents,start,divisor)
    powers,parents = tuple(map(tuple,powers)),tuple(map(tuple,parents))
    def replay(cover,vals,depth):
        if len(cover)==2 and isinstance(cover[0],list):
            left,right = bisect_controls(vals)
            return replay(cover[0],left,depth+1)+replay(cover[1],right,depth+1)
        p,combos = cover
        errs = [r+depth for r in errors]
        assert combos and all(len(z)==len(parents) and all(type(c) is int for c in z) and small(z,vals,errs) for z in combos)
        points = finite_values(p,powers,parents)
        assert all(any(sum(c*v for c,v in zip(z,pt))%p for z in combos) for pt in points)
        return 1
    return replay(tree,rows,0)


def verify_cover(data):
    """Check each closed band and its exact overlap with the previous bands."""
    assert data['lower']==10**184 and data['upper']==10**185
    right=Fraction(data['lower'])
    total=0
    for start,divisor,record in sorted(data['bands'],key=lambda item:item[0]):
        assert start<=right
        total+=verify(record,start,divisor)
        right=max(right,start*Fraction(divisor+1,divisor)**840)
    assert right>=data['upper']
    return total


if __name__=='__main__':
    with gzip.open(Path(__file__).with_suffix('.json.gz'),'rt') as f:
        data=json.load(f)
    if isinstance(data,dict):
        leaves=verify_cover(data)
        print('Certified [10^184,10^185] with',leaves,'Bernstein subintervals.')
    else:
        leaves=verify(data)
        print('Certified the full interval at 10^184 with',leaves,'Bernstein subintervals.')
