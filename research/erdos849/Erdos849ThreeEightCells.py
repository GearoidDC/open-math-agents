"""Exact functions on the (3,8) curve testing each prime-assignment cell."""

from fractions import Fraction as Q
from math import factorial, gcd, isqrt, lcm

from Erdos849ThreeFiveCells import characteristic, multiply_in_cubic, norm_at, times


CUBIC = (-1, 0, 1)
QUARTIC = (0, 2, 6, 12)
SCALES = (840, 2520, 840, 840)


def subtract_multiple(left, right, coefficient):
    for key, value in right.items():
        left[key] = left.get(key, 0) - coefficient * value
        if not left[key]:
            del left[key]


def candidates(i, r, scale, max_degree=12):
    """Build integral polynomials with strictly negative weights at infinity."""
    rhs = {0: Q(1, 6720)}
    for q in QUARTIC:
        rhs = times(rhs, {1: 1, 0: r-q})
    relation = (rhs, {0: 1}, {})
    u, v = [root for t, root in enumerate(CUBIC) if t != i]
    z = [{-1: scale*u*v}, {-1: -scale*(u+v)}, {-1: scale}]
    power = [{0: 1}, {}, {}]
    pivots = {}
    for degree in range(1, max_degree+1):
        power = multiply_in_cubic(power, z, relation)
        expr = {(0, 0, degree): Q(1)}
        rem = {}
        for a, coeffs in enumerate(power):
            for b, coeff in coeffs.items():
                if b >= 0:
                    expr[a, b, 0] = -coeff
                else:
                    rem[a, b] = coeff
        while rem:
            key = max(rem, key=lambda term: 4*term[0] + 3*term[1])
            if key not in pivots:
                pivots[key] = (rem, expr)
                if 4*key[0]+3*key[1] < 0:
                    denominator = lcm(*(x.denominator for x in expr.values()))
                    content = gcd(*(int(x*denominator) for x in expr.values()))
                    cert = [(*term, int(x*Q(denominator,content)))
                            for term, x in expr.items()]
                    polys = characteristic(i, r, cert, CUBIC, QUARTIC, Q(1,6720), scale)
                    yield degree, polys, cert
                break
            old_rem, old_expr = pivots[key]
            multiplier = Q(rem[key], old_rem[key])
            subtract_multiple(rem, old_rem, multiplier)
            subtract_multiple(expr, old_expr, multiplier)


def disk_bounds(polys, base):
    if not polys[-1] or any(p and max(p) >= 0 for p in polys):
        return None
    degree = max(polys[-1])
    tail = {k:v for k,v in polys[-1].items() if k!=degree}
    if abs(polys[-1][degree])*Q(base)**degree <= norm_at(tail,base):
        return None
    return [norm_at(p,base) for p in polys]


def cap(degree, bounds):
    if bounds is None:
        return 0
    def small(g):
        return sum(x * g**(t*degree) for t,x in enumerate(bounds,1)) < 1
    lo, hi = 0, 1
    while small(hi):
        lo, hi = hi, 2*hi
    while hi-lo > 1:
        mid=(lo+hi)//2
        if small(mid):
            lo=mid
        else:
            hi=mid
    return lo


def row_floor(exponent, r):
    return isqrt(isqrt(factorial(8)*10**exponent))-r


def main():
    if not __debug__:
        raise RuntimeError("Enable assertions")
    reported=((37,18,52,100),(408,169,410,550),(38,21,63,138))
    for i in range(3):
        for b,(r,scale) in enumerate(zip(QUARTIC,SCALES)):
            choices = list(candidates(i,r,scale))
            result = [max(cap(d,disk_bounds(p,row_floor(e,r))) for d,p,_ in choices)
                      for e in (60,100,128,136)]
            assert result[-1]==reported[i][b]
            print(i,r, result,flush=True)


if __name__ == "__main__":
    main()
