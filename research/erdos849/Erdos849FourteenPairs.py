"""Square classes in short integer blocks and quadratic square classes in Pascal rows."""

from fractions import Fraction
from functools import cache
from itertools import combinations
from math import comb, factorial, isqrt, lcm, prod

from Erdos849HigherSquare import certificate
from Erdos849PatternThreeCRT import row_in_column
from Erdos849Wheel import allowed_moduli
from Erdos849WiderOdd import positive_unit
from Erdos849WiderOdd37 import actual_row, remaining_indices


H = 3_209_464
KERNELS = [d for d in range(1,211) if 210 % d == 0]
COUNTS = {(3,8): (49,50,1), (8,3): (542,518,2), (5,8): (180,174,2),
          (8,5): (542,528,2), (6,8): (277,263,2), (8,6): (542,513,2),
          (7,8): (399,377,2), (8,7): (542,513,2)}


def multiply(f, g):
    result = [0]*(len(f)+len(g)-1)
    for i,a in enumerate(f):
        for j,b in enumerate(g):
            result[i+j] += a*b
    return result


def even_products():
    maximum_bound = 0
    exceptions = []
    for size in (2,4,6,8):
        h = size//2
        for offsets in combinations(range(8),size):
            f = [1]
            for s in offsets:
                f = multiply(f,[-s,1])
            coeffs = [Fraction(1)]
            for i in range(1,h+1):
                prev = sum(coeffs[a]*coeffs[i-a] for a in range(1,i))
                coeffs.append((Fraction(f[2*h-i])-prev)/2)
            root = coeffs[::-1]
            den = lcm(*(v.denominator for v in root))
            rem = [a-b for a,b in zip(f,multiply(root,root))]
            assert not any(rem[h:]) and any(rem[:h])
            while not rem[-1]:
                rem.pop()
            bound = max(16, 2+int(2*sum(map(abs,root[:-1]))),
                        2+int(den*2**h*sum(map(abs,rem))),
                        2+int(sum(map(abs,rem[:-1]))/abs(rem[-1])))
            maximum_bound = max(maximum_bound,bound)
            for n in range(8,bound):
                value = prod(n-s for s in offsets)
                if isqrt(value)**2 == value:
                    exceptions.append((n,offsets))
    assert maximum_bound == 192542
    assert max(exceptions) == (55,(1,5,6,7))
    print('ordinary square products: bound',maximum_bound,'largest exception',max(exceptions),flush=True)


@cache
def seeds(d, gap):
    _,v = positive_unit(d)
    out = []
    for y in range(v*gap):
        value = d*y*y+gap*gap
        x = isqrt(value)
        if x*x == value:
            out.append((x,y))
    return out


@cache
def images(k, other):
    result = []
    for p,rows in allowed_moduli(k,(other,)):
        doubled = {(2*z)%p for z in rows}
        result.append((p,bytes(x in doubled for x in range(p))))
    return result


def masks(k, other, d, unit):
    result = []
    for p,allowed in images(k,other):
        u,v = unit[0]%p,unit[1]%p
        x,y = 1,0
        for period in range(1,2*p+1):
            x,y = (u*x+d*v*y)%p,(v*x+u*y)%p
            if (x,y) == (1,0):
                break
        else:
            raise AssertionError((d,p))
        result.append((period,p,u,v,allowed))
    return sorted(result)


def pair_finite(k, other):
    # If two squarefree parts divide 210, their product has squarefree part
    # dividing 210. For D=1 the ordinary square-product check bounds n by 55.
    def collision(n):
        a = comb(n,k)
        return a >= comb(2*other,other) and row_in_column(a,other)

    assert not any(collision(n) for n in range(2*k,56))
    total = [0,0,0]
    fourteen = None
    for d in KERNELS[1:]:
        unit = positive_unit(d)
        b = unit[0].bit_length()-1
        assert unit[0]**2-d*unit[1]**2 == 1 and b >= 1
        required = 2+(10*H+3*factorial(k).bit_length()+3*k-1)//(3*k)
        end = (required+b-1)//b
        assert 3*(k*(b*end-2)-factorial(k).bit_length()) >= 10*H
        data = masks(k,other,d,unit)
        repeats = {}
        orbits = actual = largest = 0
        survivors = set()
        for i,j in combinations(range(k),2):
            for seed in seeds(d,j-i):
                orbits += 1
                for t in remaining_indices(d,i+j,seed,data,repeats,end,b+1):
                    actual += 1
                    largest = max(largest,t)
                    n = actual_row(d,i,j,seed,unit,t)
                    if n is not None and n >= 2*k:
                        survivors.add(n)
        assert not any(collision(n) for n in survivors), (k,other,d)
        total[0] += orbits
        total[1] += actual
        total[2] = max(total[2],largest)
        if d == 14:
            fourteen = (orbits,actual,largest)
    assert tuple(total) == COUNTS[k,other]
    print('host',k,'other',other,'all kernels',tuple(total),'D=14',fourteen,flush=True)


if __name__ == '__main__':
    even_products()
    for k in (3,5,6,7):
        assert certificate((k,8),4)[-1] < H
        pair_finite(k,8)
        pair_finite(8,k)
