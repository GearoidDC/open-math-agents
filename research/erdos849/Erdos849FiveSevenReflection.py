"""Frobenius and endomorphism tests for the diagonal reflection in columns 5,7."""

from math import gcd

from Erdos849FiveEightQuintic import distinct_powers, factor_degrees, logs, real_polynomial
from Erdos849SmallestCurve import critical_polynomial
from Erdos849ThreeFiveCurve import gcd as polynomial_gcd
from Erdos849ThreeFiveCurve import polynomial_from_traces


def counts(p, degree):
    log = logs(p, degree)
    q = len(log)
    zero = q-1
    shift = log[42 % p]
    left, right, squares_left, squares_right = (bytearray(q) for _ in range(4))
    for start in range(0, q, p):
        digits = list(log[start:start+p])*2
        for x in range(p):
            end = p+x
            y = digits[end]
            # The two odd centered polynomials differ by the factor x^2-9.
            factors = [digits[end-v] for v in (0, 1, 2, (-1) % p, (-2) % p)]
            h = zero if -1 in factors else sum(factors) % zero
            left[zero if h == zero else (shift+h) % zero] += 1
            a, b = digits[end-3], digits[end-((-3) % p)]
            right[zero if h == zero or min(a, b)<0 else (h+a+b) % zero] += 1
            # Square the equations and use u=X^2,v=Y^2 on the quotient.
            a, b, c = digits[end-1], digits[end-4], digits[end-(9 % p)]
            h = zero if min(y,a,b)<0 else (y+2*(a+b)) % zero
            squares_left[zero if h == zero else (2*shift+h) % zero] += 1
            squares_right[zero if h == zero or c<0 else (h+2*c) % zero] += 1
    full = 1+sum(x*y for x,y in zip(left,right))
    branches = len({1 % p,4 % p}) * len({1 % p,4 % p,9 % p})
    quotient = 1+branches+sum(x*y for x,y in zip(squares_left,squares_right))
    return full,quotient


def weil(p, traces):
    top = polynomial_from_traces([12]+traces)
    return [top[6-i]*p**(6-i) for i in range(6)] + top


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    expected = {
        5: ([26,46,146,726,2626,14926], [16,36,136,676,2876,15276]),
        11: ([40,144,1342,15580,159010,1769484], [27,131,1365,14915,160672,1767041]),
        13: ([40,186,2206,28862,372450,4835076], [26,176,2303,28408,371606,4834265]),
    }
    quotient, prym = {}, {}
    for p, (fc, qc) in expected.items():
        if p != 5:
            assert len(polynomial_gcd(critical_polynomial(5,p),critical_polynomial(7,p),p)) == 1
        assert [counts(p,d) for d in range(1,7)] == list(zip(fc,qc))
        quotient[p] = weil(p, [p**d+1-c for d,c in enumerate(qc,1)])
        prym[p] = weil(p, [y-x for x,y in zip(fc,qc)])
        print(p, "full counts", fc, "quotient counts", qc,
              "factor orders", sum(quotient[p]), sum(prym[p]), flush=True)
    orders = {p:sum(quotient[p])*sum(prym[p]) for p in expected}
    assert gcd(*orders.values()) == 1
    assert all(any(n % p for r,n in orders.items() if r != p) for p in orders)

    for polys, moduli, flip, swap, comparison, second_degrees in (
        (quotient,(17,31),137,7,3,[1,2,3]),
        (prym,(23,89),89,31,11,[1,1,1,3]),
    ):
        for p,mod in zip((11,13),moduli):
            assert distinct_powers(polys[p],mod) == (262,510)
        g,h = real_polynomial(polys[11],11),real_polynomial(polys[13],13)
        assert factor_degrees(g,2) == [1,5]
        assert factor_degrees(g,swap) in ([1,1,1,1,2],[1,2,3])
        assert factor_degrees(polys[11],flip) == [2,5,5]
        assert factor_degrees(g,comparison) == [6]
        assert factor_degrees(h,comparison) == second_degrees
    assert factor_degrees(quotient[11],17) == [12]
    assert factor_degrees(prym[11],17) == [4,8]
    print("The two six-dimensional factors are geometrically nonisogenous, with endomorphism ring Z.")


if __name__ == "__main__":
    main()
