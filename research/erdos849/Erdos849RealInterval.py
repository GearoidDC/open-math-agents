"""Certify a binomial collision-free interval by real interpolation alone."""

import json
from math import factorial, lcm, prod
from pathlib import Path

from Erdos849ResidueDisks import fibers


def integer_root(value,k):
    r = 1<<((value.bit_length()+k-1)//k)
    while True:
        s = ((k-1)*r + value//r**(k-1))//k
        if s>=r:
            assert r**k<=value<(r+1)**k
            return r
        r = s


def scaled_row(k,target,scale):
    # Integer bracket for the real solution of the falling-factorial equation.
    y = integer_root(target,k)+k*scale
    while True:
        terms = [y-i*scale for i in range(k)]
        f = prod(terms)
        if f<=target:
            assert all(v>0 for v in terms) and target<prod(v+1 for v in terms)
            return y
        derivative = sum(f//v for v in terms)
        y -= max(1,(f-target)//derivative)


def lebesgue_bound(nodes):
    denominators = [prod(abs(x-y) for y in nodes if y!=x) for x in nodes]
    bound = 0
    for a,b in zip(nodes,nodes[1:]):
        sizes = [max(abs(a-x),abs(b-x)) for x in nodes]
        full = prod(sizes)
        bound = max(bound,sum((full-1)//(size*den)+1
                              for size,den in zip(sizes,denominators)))
    return bound


def integer_bounds(data):
    cols,A,d,node_den,nodes,degrees,polys,second = data
    assert cols==[8,7,5,3] and A>1 and d>=1 and second in (11,13,17,19)
    assert nodes==sorted(set(nodes)) and nodes[0]==0 and nodes[-1]==node_den
    assert len(nodes)>1 and all(len(es)==len(cols) for es in degrees)
    assert all(all(0<=e<k for k,e in zip(cols,es)) for es in degrees)
    assert all(len(cs)==len(degrees) and all(type(c) is int for c in cs) for cs in polys)
    g = lcm(*cols)
    S,D = 2**512,2**1800
    maxima = []
    for k in cols:
        b = integer_root(factorial(k)*A,k)
        power = g//k
        # Minimum |w| on every disk of complex radius 1/8.
        assert b*7**power > 100*k**4*8**power
        numerator = (b+1)*(9*d+8)**power
        denominator = (8*d)**power
        maxima.append((numerator+denominator-1)//denominator+4*k*k)
    M = [prod(v**e for v,e in zip(maxima,es)) for es in degrees]
    assert all(S*sum(es)*m<D for es,m in zip(degrees,M))
    sample_max = [0]*len(polys)
    for j in nodes:
        num = A*(d*node_den+j)**g
        den = (d*node_den)**g
        rows = [scaled_row(k,factorial(k)*num*D**k//den,D) for k in cols]
        vals = [prod(x**e for x,e in zip(rows,es))*S//D**sum(es) for es in degrees]
        for i,cs in enumerate(polys):
            sample_max[i] = max(sample_max[i],abs(sum(c*x for c,x in zip(cs,vals))))
    leb = lebesgue_bound(nodes)
    J = len(nodes)
    caps = []
    for cs,maximum in zip(polys,sample_max):
        # Sample rounding, row rounding, and analytic interpolation remainder.
        top = leb*(maximum+2*sum(map(abs,cs)))*d**J
        top += S*8**J*sum(abs(c)*m for c,m in zip(cs,M))
        caps.append(top//(S*d**J))
    return caps,leb


def check(data):
    caps,leb = integer_bounds(data)
    assert all(cap==0 for cap in caps)
    cols,A,d,node_den,nodes,degrees,polys,second = data
    for tuples in fibers(cols,second,False).values():
        for point in tuples:
            vals = [prod(pow(x,e,second) for x,e in zip(point,es))%second for es in degrees]
            assert any(sum(c*x for c,x in zip(cs,vals))%second for cs in polys)
    return leb


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    data = json.loads(Path(__file__).with_suffix('.json').read_bytes())
    print('Real interpolation and modular exclusion verified; Lebesgue bound',check(data))
