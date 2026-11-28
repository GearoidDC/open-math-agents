"""Independent specialization audit of the 3/5 characteristic polynomials.

Uses python-flint for univariate rational resultants.
"""
import json
import sys
from fractions import Fraction
from math import prod
from pathlib import Path

from Erdos849ThreeFiveCells import characteristic


def main():
    local = Path(".lake/flint-discovery")
    if local.is_dir():
        sys.path.insert(0,str(local.resolve()))
    from flint import fmpq, fmpq_poly
    X = fmpq_poly([0,1])
    data = json.loads(Path(__file__).with_name("Erdos849ThreeFiveCells.json").read_text())
    count = 0
    for i,j,_,_,terms in data:
        C = characteristic(i,j,terms)
        c = max(t[2] for t in terms)
        if any(deg < -3*c or deg >= 0 for row in C for deg in row):
            raise ArithmeticError("unexpected characteristic coefficient degree")
        # After multiplying by y^(3c), the resultant has degree at most
        # 5*deg_X(F) + 3*(c+max_py) by Sylvester's determinant.
        degree = 5*max(max(t[0] for t in terms),2*c) + 3*(c+max(t[1] for t in terms))
        for y in range(1,degree+2):
            rhs = fmpq(prod(y+j-s for s in range(5)),20)
            eq = X**3-X-rhs
            z = fmpq(60,y)*prod(X+1-s for s in range(3) if i != s)
            F = sum(a*(X**p)*y**q*z**r for p,q,r,a in terms)
            coeff = [sum(a*Fraction(y)**d for d,a in poly.items()) for poly in C]
            for T in (-1,0,1):
                expected = T**3 + sum(v*T**(2-t) for t,v in enumerate(coeff))
                actual = eq.resultant(T-F)
                if actual != fmpq(expected.numerator, expected.denominator):
                    raise ArithmeticError((i,j,y,T))
                count += 1
    print(f"Independently verified all fifteen Laurent characteristic polynomials "
          f"by {count} ordinary univariate resultants.")


if __name__ == "__main__":
    main()
