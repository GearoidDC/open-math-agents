"""Bitangent evaluation bounds for the two genus-three Jacobians."""

from itertools import product
from math import isqrt, prod

from Erdos849PatternGeometryQuartics import branch_clear, distinct_conjugate_powers, frobenius
from Erdos849ThreeFiveCurve import irreducible_prime, prime, smooth


def quartic(k):
    return ((0, 1, 2), 1720320) if k == 3 else ((1, 9, 25), 224)


ys = (1, 9, 25, 49)


def bitangent(k, p, slope, intercept):
    # Restriction of the plane quartic to y=slope*x+intercept.
    xs, c = quartic(k)
    a, b, d = -sum(xs), xs[0]*xs[1]+xs[0]*xs[2]+xs[1]*xs[2], -prod(xs)
    roots = [intercept-y for y in ys]
    v0 = prod(roots) - c*d
    v1 = slope*sum(prod(roots[:i]+roots[i+1:]) for i in range(4)) - c*b
    v2 = slope**2*sum(roots[i]*roots[j] for i in range(4) for j in range(i)) - c*a
    v3 = slope**3*sum(roots) - c
    lead = pow(slope, 4, p)
    u = v3 * pow(2*lead, -1, p) % p
    v = (v2 - lead*u*u) * pow(2*lead, -1, p) % p
    return (v0 - lead*v*v) % p == 0 and (v1 - 2*lead*u*v) % p == 0


def points(k):
    xs, c = quartic(k)
    pts = [(x,y,1) for x,y in product(xs, ys)]
    if k == 3:
        pts += [(3,81,1), (11,225,1), (-1,1203,27)]
    else:
        pts += [(49,81,1), (529,441,1), (273,273,1)]
    assert all(prod(y-z*e for e in ys) == c*z*prod(x-z*e for e in xs) for x,y,z in pts)
    return pts


WITNESSES = {
    3: [(31,22,20,13667), (47,3,13,11054), (47,16,14,6998),
        (67,5,56,15190), (71,44,2,11872), (71,56,7,12235),
        (73,71,52,15998), (73,72,13,680), (127,36,40,13059)],
    6: [(59,27,7,8243), (59,35,45,4790), (67,54,19,13901),
        (71,50,43,9552), (83,36,75,11645), (89,18,12,10187), (97,16,80,7035)],
}


def rank_rows(k):
    pts = points(k)
    basis = {}
    for p, m, b, expected in WITNESSES[k]:
        assert prime(p) and branch_clear(k,p) and bitangent(k,p,m,b)
        vals = [(y-m*x-b*z)*pow(z,-1,p)%p for x,y,z in pts]
        assert all(vals)
        mask = sum((pow(x*vals[0],(p-1)//2,p) != 1) << j
                   for j, x in enumerate(vals[1:]))
        assert mask == expected
        while mask and mask.bit_length() in basis:
            mask ^= basis[mask.bit_length()]
        assert mask
        basis[mask.bit_length()] = mask
    return len(basis)


def geometry(k):
    pair = (11,13) if k == 3 else (17,19)
    discs = []
    for j,p in enumerate(pair):
        counts, f = frobenius(k,p)
        q = irreducible_prime(f)
        assert distinct_conjugate_powers(f)
        a,b,c = f[5], f[4] - 3*p, f[3] - 2*p*f[5]
        disc = a*a*b*b - 4*b**3 - 4*a**3*c - 27*c*c + 18*a*b*c
        discs.append(disc)
        assert disc > 0 and isqrt(disc)**2 != disc
        if j == 0:
            torsion_order = sum(f)
            q_split = 79 if k == 3 else 61
            assert prime(q_split) and smooth(f,q_split)
            roots = [u for u in range(q_split)
                     if sum(v*pow(u,i,q_split) for i,v in enumerate(f))%q_split == 0]
            assert len(roots) == 4
            print(k,'single transposition',q_split,roots)
        print(k,p,'counts',counts,'polynomial',f,'irreducibility',q,'real discriminant',disc)
    assert discs == ([11476,29165] if k == 3 else [76448,3028])
    assert isqrt(prod(discs))**2 != prod(discs)
    p = 13 if k == 3 else 17
    assert branch_clear(k, p) and 4096 % p
    assert not any(bitangent(k, p, m, b) for m in range(1, p) for b in range(p))
    return torsion_order


if __name__ == '__main__':
    for k in (3,6):
        bound = rank_rows(k)
        order = geometry(k)
        loss = (order & -order).bit_length() - 1
        assert (bound-loss) == (8 if k == 3 else 7)
        print(k,'mod-2 independent rows',bound,'reduction order',order,'rank >=',bound-loss)
