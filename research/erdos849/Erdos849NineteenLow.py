"""Exclude five-row values with at most 18 prime divisors and largest column at most 17."""

from functools import lru_cache
from fractions import Fraction
from math import factorial, lcm, prod
import gzip
import json

from Erdos849SingletonInterpolation import DATA, branch_bounds, endpoint


@lru_cache(None)
def occupancies(slots,total,minimum=0):
    if slots==0:
        return [()] if total==0 else []
    return [(count,)+tail for count in range(minimum,total//slots+1)
            for tail in occupancies(slots-1,total-count,count)]


def excludes_column(k,constants):
    Q = constants[0]
    exceptional = sorted([max(Fraction(1),Fraction(v,Q)) for v in constants[1:]],reverse=True)
    E = prod(exceptional)
    lower = endpoint(k)-k+1
    cofactor_cap = lcm(*range(1,k+1))
    # For t hosted prime powers, C_t bounds the cofactor from below, up
    # to the at most t exceptional prime-base losses at this slot.
    C = [max(Fraction(1),Fraction(lower,Q**t)) if t*k<=17 else Fraction(1)
         for t in range(19)]
    single_impossible = [value>cofactor_cap*prod(exceptional[:t])
                         for t,value in enumerate(C)]
    return all(any(single_impossible[t] for t in counts)
               or prod(C[t] for t in counts)>factorial(k)*E
               for counts in occupancies(k,18))


def main():
    with gzip.open(DATA,"rt",encoding="ascii") as handle:
        data = json.load(handle)
    exceptions = []
    for d in range(8,18):
        for j in range(7,d):
            rows = branch_bounds(j,d,data)
            constants = [max(v) for v in zip(*rows)]
            if excludes_column(j,constants) or excludes_column(d,constants):
                continue
            remaining = [k for k in range(2,j) if not excludes_column(k,constants)]
            exceptions.append((j,d,remaining))
    assert exceptions==[(9,17,[2,3,4,6])]
    print("All 55 column pairs checked. The only surviving pair is (9,17).")
    print("Its smaller proper columns lie in the published clique {2,3,4,6}.")
    print("Five rows with largest proper column at most 17 require at least 19 primes.")


if __name__=="__main__":
    main()
