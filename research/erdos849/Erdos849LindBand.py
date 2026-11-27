"""Check the Lind diagonal identities and find the first neighboring-column crossing.

All calculations use integers or exact rational numbers. The uniform proof for
every family member and arbitrarily large offsets is in Erdos849LindBand.md.
"""

from argparse import ArgumentParser
from fractions import Fraction
from math import comb, isqrt


def ratio(n, k, t):
    u = n-k
    top = (n+t+1)*(k-t)
    bottom = (u+2*t+1)*(u+2*t+2)
    assert bottom-top == t*(5*u+5*t+7)
    return Fraction(top, bottom)


def first_crossing(n, k, direction):
    """Return first offset where the next column fails to stay strictly above A."""
    t = 0
    normalized = Fraction(1)
    while True:
        if direction == 1:
            normalized *= ratio(n,k,t)
            t += 1
        else:
            t -= 1
            normalized /= ratio(n,k,t)
        if t == 1:
            assert normalized == 1
        else:
            assert normalized < 1
        if 2*(k-t+1) > n+t:
            return t, "half-row boundary"
        upper = normalized * Fraction(n-k+2*t,k-t+1)
        if upper <= 1:
            return t, "neighbor crossing"


def occurrences_in_band(n, k, radius):
    """Follow the adjacent coefficients bracketing the target in each row."""
    hits = [(n,k)]
    j = k
    z = Fraction(1)
    for m in range(n+1,n+radius+1):
        z *= Fraction(m,m-j)
        while z > 1:
            z *= Fraction(j,m-j+1)
            j -= 1
        assert 2*j <= m and (2*(j+1)>m or z*(m-j)>j+1)
        if z == 1:
            hits.append((m,j))
    j = k
    z = Fraction(1)
    for m in range(n-1,max(-1,n-radius-1),-1):
        z *= Fraction(m+1-j,m+1)
        j = min(j,m-j)
        assert z <= 1
        while 2*(j+1)<=m and z*(m-j)<=j+1:
            z *= Fraction(m-j,j+1)
            j += 1
        if z == 1:
            hits.append((m,j))
        if 2*(j+1)>m and z<1:
            break  # Central maxima increase with the row.
    return sorted(hits)


def classify_radius(radius):
    """The square-root theorem covers every subsequent family member."""
    assert radius >= 1
    a, b = 4, 6
    index = 1
    extras = []
    while True:
        n,k = 2*a+b,a+2
        if n >= max(100,100*radius**2):
            print(f"All family members from index {index}, lower row {n}, "
                  f"are covered by the uniform theorem.")
            break
        hits = occurrences_in_band(n,k,radius)
        assert (n,k) in hits and (n+1,k-1) in hits
        if n <= 103 and radius <= 64:
            target = comb(n,k)
            assert hits == [(m,j) for m in range(max(0,n-radius),n+radius+1)
                            for j in range(min(m//2,k+radius)+1)
                            if comb(m,j)==target]
        extra = [(m,j) for m,j in hits if m not in (n,n+1)]
        if extra:
            extras.extend((index,m,j) for m,j in extra)
        print(f"index {index}, n={n}: extras {extra}",flush=True)
        a,b = 5*a+3*b,3*a+2*b+3
        index += 1
    print(f"All extra occurrences within {radius} rows: {extras}",flush=True)
    return extras


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--radius',type=int,help='classify this entire row band for all family members')
    args = parser.parse_args()
    if args.radius is not None:
        classify_radius(args.radius)
        return
    # The lower row is n=2a+b and its column is k=a+2.
    a, b = 4, 6
    for index in range(1,9):
        n, k = 2*a+b, a+2
        assert k*(n+1) == (n-k+1)*(n-k+2)
        if n < 1000:
            target = comb(n,k)
            assert target == comb(n+1,k-1)
            for t in range(-3,4):
                assert ratio(n,k,t) == Fraction(comb(n+t+1,k-t-1),comb(n+t,k-t))
        left, left_event = first_crossing(n,k,-1)
        right, right_event = first_crossing(n,k,1)
        radius = isqrt(n//100)
        if n >= 100:
            assert -left > radius and right > radius
        print(f"{index}: ({n},{k}); uniform radius {radius}; "
              f"first left {left} ({left_event}), right +{right} ({right_event})")
        a,b = 5*a+3*b, 3*a+2*b+3


if __name__ == '__main__':
    main()
