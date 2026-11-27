"""Check the prime-host component obstruction to columns 7 and 15.

For a=C(n,d)=C(m,j), attach an edge of weight p^v_p(a) between the
chosen numerator factors on both sides for every distinct prime p|a.
Choose a factor with maximal p-adic valuation on each side. The valuation
of the other factors is at most v_p((d-1)!) on the d side, by counting
the multiples of p^i, and likewise on the j side. The edge weight thus
divides the chosen factor. After removing all its edge weights each
vertex has an integer cofactor; the products on the two sides are d!,j!.

A connected component using h vertices on the d side and q on the j
side has its same product of edge weights on both sides. Its numerator
product ratio is therefore D/J, where D,J are its two cofactor products.
Distinct components have disjoint cofactors. If d+j vertices have at
most W edges, there are at least d+j-W components, including isolates.
Numerator factors exceed k! when floor((k!X)^(1/k))-k+1>k!, excluding
isolated vertices on that side. The four comparisons below suffice when
X=10^188, d=15, j=7 and W=16.
"""
from argparse import ArgumentParser
from math import factorial


def root(value,k):
    hi=1 << ((value.bit_length()+k-1)//k)
    lo=0
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**k<=value:
            lo=mid
        else:
            hi=mid
    assert lo**k<=value<(lo+1)**k
    return lo


def check(K):
    """The special case j=7,d=15,W=16 takes just four root comparisons."""
    X=10**K
    r7=root(factorial(7)*X,7)
    r15=root(factorial(15)*X,15)
    l7,u7=r7-6,r7+7
    l15,u15=r15-14,r15+15
    # For a=X*y with y>=1, each numerator factor in column k is between
    # L_k*y^(1/k) and U_k*y^(1/k), by the two extreme factors in k!*a.
    # L_k>k! excludes isolated vertices since their whole row factor is a
    # cofactor. There are then at least 22-16=6 nonempty components. Of
    # these, at least 2*6-7=5 have only one 7-side vertex (q=1).
    # For q=1, h>=3 would force D/J>15!, as 3/15>1/7. For h<=2 the
    # opposite ratio J/D exceeds 5 because 1/7>2/15. Hence J>=6.
    # Five distinct such cofactors have product at least 6^5>7!.
    assert 3*7>15 and 15>2*7 and 6**5>factorial(7)
    return (l7>factorial(7), l15>factorial(15),
            l15**3>factorial(15)*u7, l7>5*u15**2)


if __name__=='__main__':
    parser=ArgumentParser(description=__doc__)
    parser.add_argument('powers',type=int,nargs='*',default=[188,500,10000])
    args=parser.parse_args()
    for K in args.powers:
        tests=check(K)
        print(f'a>=10^{K}: integer inequalities {tests}; '
              f'columns 7 and 15 ruled out for at most 16 primes={all(tests)}')
