"""Exact finite-field checks for the cubic étale covers of the (3,5) quotient."""

from itertools import combinations, product

from Erdos849ThreeFiveCurve import F0, frobenius, gcd, prime, trim


def projective(v):
    scale = next(x for x in v if x)
    return tuple(scale * x % 3 for x in v)


def projective_cycles(coefficients, lines):
    remaining = set(lines)
    cycles = []
    while remaining:
        v = next(iter(remaining))
        orbit = set()
        while v in remaining:
            remaining.remove(v)
            orbit.add(v)
            v = projective(tuple(((v[i-1] if i else 0) - coefficients[i]*v[3]) % 3
                                 for i in range(4)))
        cycles.append(orbit)
    return cycles


def check_orbits():
    # A unique ordinary double root and tame thickness one yield a transvection.
    bad_prime = 23470571
    assert prime(bad_prime)
    reduced = [value % bad_prime for value in F0]
    derivative = [i*reduced[i] % bad_prime for i in range(1, 7)]
    common = gcd(reduced, derivative, bad_prime)
    assert len(common) == 2
    double_root = -common[0]*pow(common[1], -1, bad_prime) % bad_prime
    assert sum(value*double_root**i for i, value in enumerate(F0)) % bad_prime**2 != 0
    assert sum(i*(i-1)*F0[i]*double_root**(i-2) for i in range(2, 7)) % bad_prime
    lines = {projective(v) for v in product(range(3), repeat=4) if any(v)}
    assert len(lines) == 40
    cycles = {}
    for p in (7, 11):
        coefficients = [x % 3 for x in frobenius(F0, p)[2]]
        derivative = trim([i*coefficients[i] % 3 for i in range(1, 5)])
        assert len(gcd(coefficients, derivative, 3)) == 1
        cycles[p] = projective_cycles(coefficients, lines)
    assert sorted(map(len, cycles[7])) == [4]*10
    assert sorted(map(len, cycles[11])) == [10]*4
    for a, b in combinations(cycles[11], 2):
        subset = a | b
        for direction in lines:
            for linear in lines:
                if sum(x*y for x, y in zip(direction, linear)) % 3:
                    continue
                def translate(v):
                    coefficient = sum(x*y for x, y in zip(v, linear))
                    return projective(tuple((x+coefficient*y) % 3
                                            for x, y in zip(v, direction)))
                assert any(translate(v) not in subset for v in subset)


class CubicField:
    """Elements of F_p[z]/(z^3-hz-k) as coefficient triples."""

    def __init__(self, p, h, k):
        assert all((x**3-h*x-k) % p for x in range(p))
        self.p, self.h, self.k = p, h, k
        self.zero = (0, 0, 0)
        self.one = (1, 0, 0)

    def scale(self, a, n):
        return tuple(x*n % self.p for x in a)

    def add(self, *args):
        return tuple(sum(v) % self.p for v in zip(*args))

    def mul(self, a, b):
        u = [0]*5
        for i in range(3):
            for j in range(3):
                u[i+j] += a[i]*b[j]
        for i in (4, 3):
            u[i-2] += self.h*u[i]
            u[i-3] += self.k*u[i]
        return tuple(x % self.p for x in u[:3])

    def power(self, a, n):
        out = self.one
        while n:
            if n % 2:
                out = self.mul(out, a)
            a = self.mul(a, a)
            n //= 2
        return out


def prime_divisors(n):
    d = 2
    while d*d <= n:
        if n % d == 0:
            yield d
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        yield n


def cover_test(p, lam, quadratic, cubic):
    # F = P^2 - lambda H^3, E: w^3 - 3 lambda H w - 2 lambda P = 0.
    for i in range(7):
        square = sum(cubic[j]*cubic[i-j] for j in range(4) if 0 <= i-j < 4)
        cube = sum(quadratic[j]*quadratic[k]*quadratic[i-j-k]
                   for j, k in product(range(3), repeat=2) if 0 <= i-j-k < 3)
        assert (square-lam*cube-F0[i]) % p == 0
    field = CubicField(p, 3*lam*quadratic[2], 2*lam*cubic[3])
    zero, one = field.zero, field.one
    add, mul, scale = field.add, field.mul, field.scale
    # Coordinates are (x,w,z); each monomial is stored as a list of indices.
    terms = [(1, (1,1,1))]
    for i, c in enumerate(quadratic):
        terms.append((-3*lam*c, (0,)*i+(2,)*(2-i)+(1,)))
    for i, c in enumerate(cubic):
        terms.append((-2*lam*c, (0,)*i+(2,)*(3-i)))

    def evaluate(v):
        return add(*(scale(mul(mul(v[i], v[j]), v[k]), c)
                     for c, (i,j,k) in terms))

    def derivative(v):
        gradient = [zero]*3
        for c, (i,j,k) in terms:
            for a, b, d in ((i,j,k),(j,i,k),(k,i,j)):
                gradient[a] = add(gradient[a], scale(mul(v[b], v[d]), c))
        return gradient

    def dot(v, w):
        return add(*(mul(x, y) for x, y in zip(v,w)))

    def same(v, w):
        return all(mul(v[i], w[j]) == mul(v[j], w[i])
                   for i,j in combinations(range(3), 2))

    def combine(a, v, b, w):
        out = tuple(add(mul(a, x), scale(mul(b, y), -1)) for x, y in zip(v,w))
        assert any(value != zero for value in out)
        assert evaluate(out) == zero
        return out

    def third(v, w):
        tangent = derivative(v)
        if not same(v, w):
            return combine(dot(derivative(w), v), v, dot(tangent, w), w)
        for i,j in combinations(range(3), 2):
            u = [zero]*3
            u[i], u[j] = tangent[j], scale(tangent[i], -1)
            if not same(v, u):
                return combine(evaluate(u), v, dot(derivative(u), v), u)
        raise AssertionError("singular point")

    root = (0,1,0)
    origin = (one, root, zero)
    point = (one, field.power(root, p), zero)
    assert not same(point, origin) and evaluate(point) == evaluate(origin) == zero

    def multiple(n):
        result, current = origin, point
        while n:
            if n % 2:
                result = third(third(result, current), origin)
            current = third(third(current, current), origin)
            n //= 2
        return result

    def poly(f, n):
        return sum(c*n**i for i,c in enumerate(f))

    affine = sum((w**3-3*lam*poly(quadratic,x)*w-2*lam*poly(cubic,x)) % p == 0
                 for x,w in product(range(p),repeat=2))
    trace = p+1-affine  # irreducible infinity cubic, so all F_p-points affine
    order = p**3+1-(trace**3-3*p*trace)
    assert same(multiple(order), origin)
    for divisor in prime_divisors(order):
        while order % divisor == 0 and same(multiple(order//divisor), origin):
            order //= divisor
    return affine, order


if __name__ == "__main__":
    check_orbits()
    for p, lam, quadratic, cubic, expected in (
        (13, 4, (8,2,1), (9,0,12,1), (15,12)),
        (61, 24, (43,5,1), (55,6,27,27), (68,665)),
    ):
        result = cover_test(p, lam, quadratic, cubic)
        assert result == expected
        print(f"p={p}, #E(F_p)={result[0]}, boundary difference order={result[1]}")
