"""Frobenius certificates for the genus-three plane-quartic quotients."""

from collections import Counter
from itertools import product

from Erdos849ThreeFiveCurve import (cyclotomic_indices_at_most, gcd,
                                    irreducible_prime, mul, polynomial_from_traces,
                                    prime, remainder, trim)


class Field:
    def __init__(self, p, d):
        self.p, self.d = p, d
        self.elements = tuple(product(range(p), repeat=d))
        # Degrees 2 and 3: a monic polynomial with no linear root is irreducible.
        self.modulus = None if d == 1 else next(
            (*c, 1) for c in self.elements
            if all((x**d + sum(a*x**i for i, a in enumerate(c))) % p for x in range(p)))

    def roots_product(self, x, roots, coeff=1):
        z = [coeff % self.p]
        for r in roots:
            y = [(x[0] - r) % self.p, *x[1:]]
            z = mul(z, y, self.p) if z else []
            if self.modulus:
                z = remainder(z, self.modulus, self.p)
        return tuple(z)


def branch_clear(k, p):
    # The checks in Erdos849SmallestCurve apply to the full (unreflected)
    # maps, so verifying them implies disjointness also for these quotients.
    from Erdos849SmallestCurve import critical_polynomial
    return len(gcd(critical_polynomial(k, p), critical_polynomial(8, p), p)) == 1


def frobenius(k, p):
    # Coordinates are the original column-three row, or the centered square
    # in column six; in column eight use the centered square in both cases.
    roots, coeff = ((0, 1, 2), 2**8 * 40320 // 6) if k == 3 else ((1, 9, 25), 224)
    assert k in (3, 6) and p > 7 and coeff % p and branch_clear(k, p)
    counts = []
    for d in (1, 2, 3):
        K = Field(p, d)
        lhs = Counter(K.roots_product(x, roots, coeff) for x in K.elements)
        rhs = Counter(K.roots_product(y, (1, 9, 25, 49)) for y in K.elements)
        counts.append(1 + sum(count * rhs[v] for v, count in lhs.items()))
    traces = [6] + [p**d + 1 - n for d, n in enumerate(counts, 1)]
    a3, a2, a1, _ = polynomial_from_traces(traces)
    return counts, [p**3, a1*p**2, a2*p, a3, a2, a1, 1]


def distinct_conjugate_powers(f):
    # Each nontrivial ratio has degree <=6*5 by permutation of the ordered
    # pair of distinct roots. Check separability of the powers modulo q.
    indices = cyclotomic_indices_at_most(30)
    q = 1000003
    assert prime(q)
    power_traces = [6]
    for j in range(1, 6*max(indices)+1):
        v = j*f[6-j] if j <= 6 else 0
        v += sum(f[6-i]*power_traces[j-i] for i in range(1, min(6, j-1)+1))
        power_traces.append(-v % q)
    for n in indices:
        # Newton's identities for the Frobenius conjugates raised to n.
        coeffs = [1]
        for j in range(1, 7):
            coeffs.append(-sum(coeffs[j-i]*power_traces[n*i] for i in range(1, j+1))
                          * pow(j, -1, q) % q)
        poly = list(reversed(coeffs))
        der = trim([i*poly[i] % q for i in range(1, 7)])
        if len(gcd(poly, der, q)) > 1:
            return False
    return True


if __name__ == '__main__':
    for k, p, expected_counts, expected_f, q in (
        (3, 11, [20, 128, 1358], [1331, 968, 385, 118, 35, 8, 1], 5),
        (6, 17, [19, 337, 4876], [4913, 289, 408, 11, 24, 1, 1], 31),
    ):
        counts, f = frobenius(k, p)
        assert (counts, f) == (expected_counts, expected_f)
        assert irreducible_prime(f) == q and distinct_conjugate_powers(f)
        print(k, p, counts, f, 'irreducible mod', q)
