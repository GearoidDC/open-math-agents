"""Verify rational-function certificates for common prime factors in columns 3 and 5."""

from fractions import Fraction
from itertools import permutations
import json
from pathlib import Path


def plus(*terms):
    result = {}
    for term in terms:
        for degree, coefficient in term.items():
            result[degree] = result.get(degree, 0) + coefficient
    return {d: x for d, x in result.items() if x}


def times(left, right):
    result = {}
    for i, a in left.items():
        for j, b in right.items():
            result[i+j] = result.get(i+j, 0) + a*b
    return {d: x for d, x in result.items() if x}


def monomial(poly, degree, coefficient):
    return {i+degree: coefficient*x for i, x in poly.items() if coefficient*x}


def multiply_in_cubic(left, right, relation):
    # relation gives the three coefficients in X^3. They are Laurent
    # polynomials in the other row coordinate y.
    out = [{} for _ in range(5)]
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i+j] = plus(out[i+j], times(a, b))
    for n in (4, 3):
        for i,temp in enumerate(relation):
            out[n-3+i] = plus(out[n-3+i], times(out[n],temp))
    return out[:3]


def characteristic(i, j, certificate, cubic_roots=(-1,0,1), other_roots=range(5),
                   ratio=Fraction(1,20), multiplier=60):
    rhs = {0:ratio}
    for s in other_roots:
        rhs = times(rhs, {1:1, 0:j-s})
    a,b,c = cubic_roots
    relation = (plus(rhs,{0:a*b*c}),{0:-(a*b+a*c+b*c)},{0:a+b+c})
    u, v = [-val for s,val in enumerate(cubic_roots) if i != s]
    z = [{-1:multiplier*u*v}, {-1:multiplier*(u+v)}, {-1:multiplier}]
    zpower = [{0:1}, {}, {}]
    f = [{}, {}, {}]
    z_coefficients = {}
    for px, py, pz, coeff in certificate:
        assert all(isinstance(n,int) for n in (px,py,pz,coeff))
        assert 0 <= px < 3 and py >= 0 and pz >= 0
        if pz:
            assert px == py == 0 and pz not in z_coefficients
            z_coefficients[pz] = coeff
        else:
            f[px] = plus(f[px], {py:coeff})
    for degree in range(1, max(z_coefficients)+1):
        zpower = multiply_in_cubic(zpower,z,relation)
        coeff = z_coefficients.get(degree,0)
        f = [plus(a,monomial(b,0,coeff)) for a,b in zip(f,zpower)]
    # Columns of multiplication by f in the basis 1, X, X^2.
    x = [{},{0:1},{}]
    xf = multiply_in_cubic(x,f,relation)
    cols = [f,xf,multiply_in_cubic(x,xf,relation)]
    trace = plus(*(cols[t][t] for t in range(3)))
    minors = []
    for u,v in ((0,1),(0,2),(1,2)):
        minors.extend((times(cols[u][u],cols[v][v]),
                       monomial(times(cols[u][v],cols[v][u]),0,-1)))
    summands = []
    for perm in permutations(range(3)):
        sign = (-1)**sum(perm[u]>perm[v] for u in range(3) for v in range(u+1,3))
        summands.append(monomial(times(times(cols[0][perm[0]],cols[1][perm[1]]),
                                       cols[2][perm[2]]),0,sign))
    return [monomial(trace,0,-1),plus(*minors),monomial(plus(*summands),0,-1)]


def norm_at(poly, row_floor):
    return sum(abs(c)*Fraction(row_floor)**d for d,c in poly.items())


def verify_cell(i,j,certificate,row_floor,cap,**model):
    characteristic_coeffs = characteristic(i,j,certificate,**model)
    degree = max(t[2] for t in certificate)
    constant = characteristic_coeffs[-1]
    assert constant
    first = max(constant)
    assert abs(constant[first])*Fraction(row_floor)**first > norm_at(
        {d:c for d,c in constant.items() if d!=first},row_floor)
    assert all(d<0 for poly in characteristic_coeffs for d in poly)
    assert sum(norm_at(poly,row_floor)*cap**(degree*t)
               for t,poly in enumerate(characteristic_coeffs,1)) < 1


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError("Enable Python assertions.")
    data = json.loads(Path(__file__).with_suffix('.json').read_text())
    assert {(i,j) for i,j,*_ in data} == {(i,j) for i in range(3) for j in range(5)}
    for i,j,row_floor,cap,terms in data:
        verify_cell(i,j,terms,row_floor,cap)
        print(i,j,row_floor,cap)
