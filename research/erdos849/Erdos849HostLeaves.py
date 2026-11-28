"""Rule out a numerator position all of whose assigned prime powers share one neighbor."""

from functools import lru_cache
import json
from math import comb, lcm
from pathlib import Path

from Erdos849FullHostCuts import PAIRS
from Erdos849PatternThree import candidates, certificate_bounds, lagrange_powers, root
from Erdos849InterpolatedPowers import denominator
from Erdos849EightSmoothTail import expansion
from Erdos849LocalInterpolation import multiply


def vp(v,p):
    if not v:
        raise ValueError("valuation of zero")
    e = 0
    while v % p == 0:
        v //= p
        e += 1
    return e


@lru_cache(None)
def jet(cols,ofs,L,n):
    return tuple(list(lagrange_powers(k,s,L,n)) for k,s in zip(cols,ofs))


def branch_powers(cols,ofs,L,n,exponents):
    rows=jet(cols,ofs,L,n)
    for row,degree in zip(rows,exponents):
        while len(row)<=degree:
            row.append(multiply(row[-1],row[1]))
    return rows


def power_loss(cols,ofs,terms,o):
    d,k = cols
    s,r = ofs
    L = lcm(denominator(d,s),denominator(k,r))
    w = d*comb(d-1,s)
    # For inactive bases the complete p-part of n-s is at most p^(f+w_p)
    # once its valuation exceeds log_p(d-1). For active bases use the full jet.
    losses = 1
    for p in (2,3,5,7):
        if p>max(cols):
            continue
        cut = 0
        while p**(cut+1) < max(cols):
            cut += 1
        f = vp(L,p)
        wp = vp(w,p)
        # e>cut: the slot is unique on both sides, and its unassigned part
        # has valuation wp. Otherwise compare the slot directly with p^(cut+wp).
        # Every monomial has total degree at least v, so active but low
        # exponents also give that much divisibility without denominators.
        terms_p = [(vp(c,p),i,j) for c,weight,(i,j) in terms]
        wk = vp(k*comb(k-1,r),p)
        def direct(y,x):
            return max(0,o*y-min(t+i*y+j*x for t,i,j in terms_p))
        def direct_active(e):
            # If e>cut, the recipient is also the unique maximal term in
            # its row, with valuation e+w_k. Otherwise e itself is safe.
            return direct(e+wp,e+(wk if e>cut else 0))
        choices = []
        for e0 in range(cut+1,cut+5):
            size = max(o,(o*(e0+wp)+e0-f-1)//(e0-f))
            series = [0]*size
            powers = branch_powers(cols,ofs,L,size,tuple(map(max,zip(*(es for c,w,es in terms)))))
            for c,weight,es in terms:
                for i,v in enumerate(expansion(powers,es,size)):
                    series[i] += c*v
            assert not any(series[:o])
            large = max([0]+[o*(e0+wp)-t*(e0-f)-vp(c,p) for t,c in enumerate(series) if c])
            # In the direct case F has no guaranteed p-factor if the slot
            # does not carry this prime. But when large p-parts give e>0
            # and a unique source slot, leafhood implies p^e divides both
            # shifted coordinates even if e<=cut.
            inactive = max(direct(t,0) for t in range(cut+1))
            small = max(inactive,*(direct_active(e) for e in range(e0)))
            choices.append(max(small,large))
        losses *= p**min(choices)
    return losses


def find_one(cols,ofs,K,options):
    d,k=cols
    cap = (root(d,K)-ofs[0])
    nh=lcm(*cols)
    for o,terms in options:
        ok,height,w=certificate_bounds(cols,ofs,o,terms,K)
        if not ok or w*d>nh*o:
            continue
        if height>=cap**o:
            continue
        if height*power_loss(cols,ofs,terms,o)<cap**o:
            return o,terms
    return None


def verify():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    data = json.loads(Path(__file__).with_suffix('.json').read_text())
    assert len(data) == sum(k*d for k,d in PAIRS)
    for k,d in PAIRS:
        thresholds = []
        for s in range(d):
            for r in range(k):
                K,o,terms = data[f'{k},{d},{s},{r}']
                assert 60 <= K <= 128 and o>0 and terms
                weights = []
                for c,w,(i,j) in terms:
                    assert isinstance(c,int) and c and min(i,j)>=0 and max(i,j)>0
                    assert w == i*(lcm(k,d)//d) + j*(lcm(k,d)//k)
                    weights.append(w)
                assert weights == sorted(weights)
                assert find_one((d,k),(s,r),K,[(o,terms)])
                thresholds.append(K)
        print(k,d,len(thresholds),max(thresholds),flush=True)
    return data


if __name__ == "__main__":
    verify()
