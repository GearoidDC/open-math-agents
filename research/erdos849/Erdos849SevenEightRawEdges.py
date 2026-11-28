"""Verify individual prime assignments at two corners of the (7,8) curve."""

import json
from fractions import Fraction
from math import comb
from pathlib import Path

from Erdos849RawCellTools import integer_valued, missing_denominator, normal_form, slope_bounds


def reflected(coeffs):
    # Expand binom(-Z,t) in the binomial polynomials binom(Z,r).
    return [
        sum((-1)**t * comb(t-1,r-1) * coeffs[t-1] for t in range(r,len(coeffs)+1))
        for r in range(1,len(coeffs)+1)
    ]


def verify(i,j,height,coeffs):
    assert all(type(c) is int for c in coeffs)
    assert missing_denominator(7,8,i,j)==23520
    terms=normal_form(7,8,i,j,coeffs)
    integer_valued({key:c for key,c in terms.items() if key[1]>=0})
    rem={key:c for key,c in terms.items() if key[1]<0}
    base,lo,hi=slope_bounds(7,8,height)
    base=Fraction(base)
    def weight(key):
        return 8*key[0]+7*key[1]
    leading=max(rem,key=weight)
    assert weight(leading)<0 and len({weight(key) for key in rem})==len(rem)
    bounds={key:abs(c)*hi**key[0]*base**weight(key) for key,c in rem.items()}
    assert sum(bounds.values())<1
    lower=abs(rem[leading])*lo**leading[0]*base**weight(leading)
    assert lower>sum(bounds.values())-bounds[leading]
    return i,j,height,len(coeffs),weight(leading)


if __name__=="__main__":
    if not __debug__:
        raise RuntimeError("Enable assertions to verify the certificate")
    record=json.loads(Path(__file__).with_suffix(".json").read_text())
    assert record["height"]<=495 and len(record["coefficients"])==48
    for j,coeffs in [(0,record["coefficients"]),(7,reflected(record["coefficients"]))]:
        print(verify(0,j,record["height"],coeffs))
