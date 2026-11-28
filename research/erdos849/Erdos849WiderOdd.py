"""Sieve squarefree kernels of pairs of eighth-column numerator terms."""

from functools import cache
from itertools import combinations
from math import comb, factorial, gcd, isqrt
from time import monotonic

from Erdos849PellSmall import primitive_solutions
from Erdos849PatternThreeCRT import row_in_column
from Erdos849Wheel import allowed_moduli


def kernels(prime_limit):
    primes = [p for p in range(2,prime_limit+1)
              if all(p%q for q in range(2,isqrt(p)+1))]
    values = [1]
    for prime in primes:
        values += [prime*v for v in values]
    return sorted(values)


@cache
def positive_unit(d):
    """Find a positive norm-one unit among the sqrt(d) convergents."""
    initial = isqrt(d)
    m, denominator, digit = 0, 1, initial
    old_p, numerator, old_q, convergent_q = 1, initial, 0, 1
    while numerator*numerator-d*convergent_q*convergent_q != 1:
        m = denominator*digit-m
        denominator = (d-m*m)//denominator
        digit = (initial+m)//denominator
        old_p, numerator = numerator, digit*numerator+old_p
        old_q, convergent_q = convergent_q, digit*convergent_q+old_q
    return numerator, convergent_q


@cache
def starting_pairs(d, gap):
    _, v = positive_unit(d)
    starts = {(gap,0)}
    for scale in range(1,gap+1):
        if gap % scale:
            continue
        h = gap//scale
        for x,y,_ in primitive_solutions(d,(h,),v*h):
            starts.add((scale*x,scale*y))
    assert all(x*x-d*y*y == gap*gap and 0 <= y < v*gap for x,y in starts)
    return sorted(starts)


def orbit_list(largest, prime_limit, max_gap):
    for d in kernels(prime_limit)[1:]:
        for left,right in combinations(range(largest),2):
            if right-left > max_gap:
                continue
            for x,y in starting_pairs(d,right-left):
                yield d,left,right,x,y


@cache
def modular_data(d, largest, other_columns):
    unit_x, unit_y = positive_unit(d)
    data = []
    for p,allowed in allowed_moduli(largest,other_columns):
        u,v = unit_x%p,unit_y%p
        x,y = 1,0
        for length in range(1,2*p+1):
            x,y = (u*x+d*v*y)%p,(u*y+v*x)%p
            if (x,y) == (1,0):
                break
        else:
            raise AssertionError((d,p,"unit period"))
        # n=(x+i+j)/2. Store the allowed classes of 2n.
        doubled = {(2*a)%p for a in allowed}
        twice_rows = bytes(i in doubled for i in range(p))
        data.append((length,p,u,v,twice_rows))
    return sorted(data)


@cache
def repeat_mask(period, length):
    blocks = (length+period-1)//period
    return ((1<<(blocks*period))-1)//((1<<period)-1)


def sieve(orbit, largest, other_columns, base_end):
    d,left,right,x0,y0 = orbit
    unit_x, _ = positive_unit(d)
    growth = unit_x.bit_length()-1
    end = (base_end+growth-1)//growth
    possible = (1<<end)-1
    for period,p,u,v,allowed in modular_data(d,largest,other_columns):
        x = x0%p
        next_x = (u*x+d*v*(y0%p))%p
        mask = 0
        for index in range(period):
            if allowed[(x+left+right)%p]:
                mask |= 1<<index
            x,next_x = next_x,(2*u*next_x-x)%p
        possible &= mask*repeat_mask(period,end)
        if possible.bit_length()<=12:
            break
    while possible:
        least = possible & -possible
        yield least.bit_length()-1
        possible ^= least


def exact_pair(orbit, index):
    d,left,right,x,y = orbit
    u,v = positive_unit(d)
    while index:
        if index%2:
            x,y = u*x+d*v*y,u*y+v*x
        index //= 2
        if index:
            u,v = u*u+d*v*v,2*u*v
    assert x*x-d*y*y == (right-left)**2
    if y%2 or (x+left+right)%2:
        return None
    n=(x+left+right)//2
    assert (n-left)*(n-right) == d*(y//2)**2
    return n


def square_pairs(largest, max_gap):
    for left,right in combinations(range(largest),2):
        if right-left > max_gap:
            continue
        gap2 = (right-left)**2
        for a in range(1,right-left+1):
            if gap2%a:
                continue
            b=gap2//a
            if (a+b)%2 or (b-a)%4:
                continue
            x=(a+b)//2
            if (x+left+right)%2==0:
                yield (x+left+right)//2,left,right


def controls(largest, prime_limit, orbits, max_gap):
    bound=2000
    allowed=set(kernels(prime_limit))
    direct=set()
    for n in range(2*largest,bound+1):
        square_classes=[]
        for offset in range(largest):
            m=n-offset
            for p in range(2,isqrt(m)+1):
                while m%(p*p)==0:
                    m//=p*p
            square_classes.append(m)
        for left,right in combinations(range(largest),2):
            if right-left > max_gap:
                continue
            d=square_classes[left]*square_classes[right]//gcd(square_classes[left],square_classes[right])**2
            if d in allowed:
                direct.add((n,left,right,d))
    generated={(n,i,j,1) for n,i,j in square_pairs(largest,max_gap) if 2*largest<=n<=bound}
    for orbit in orbits:
        d,left,right,x,y=orbit
        u,v=positive_unit(d)
        while x+left+right<=2*bound:
            if y%2==0 and (x+left+right)%2==0:
                n=(x+left+right)//2
                if n>=2*largest:
                    generated.add((n,left,right,d))
            x,y=u*x+d*v*y,u*y+v*x
    assert direct and generated==direct
    return len(direct)


def run(largest=8, other_columns=(7,), prime_limit=13, height_decade=250000, max_gap=None):
    assert __debug__ and largest>1 and other_columns and all(1<=k<largest for k in other_columns)
    other_columns=tuple(other_columns)
    max_gap=largest-1 if max_gap is None else max_gap
    assert 1<=max_gap<largest and prime_limit>=2 and height_decade>0
    started=monotonic()
    radicand=factorial(largest)*10**height_decade
    base_end=2+(radicand.bit_length()+largest-1)//largest
    assert 2**(base_end-2)>=largest and 2**((base_end-2)*largest)>radicand
    orbits=list(orbit_list(largest,prime_limit,max_gap))
    control_count=controls(largest,prime_limit,orbits,max_gap)
    candidates={n for n,_,_ in square_pairs(largest,max_gap) if n>=2*largest}
    checks=maximum=0
    for orbit in orbits:
        for index in sieve(orbit,largest,other_columns,base_end):
            checks+=1
            maximum=max(maximum,index)
            n=exact_pair(orbit,index)
            if n is not None and n>=2*largest:
                candidates.add(n)
    hits=[n for n in sorted(candidates)
          if all(row_in_column(comb(n,largest),k) for k in other_columns)]
    print(f"Columns {largest} and {other_columns}, primes through {prime_limit}, gaps through "
          f"{max_gap}, height 10^{height_decade}.")
    print(f"{control_count} small-row controls, {len(orbits)} Pell orbits, {checks} "
          f"surviving indices, largest index {maximum}, {len(candidates)} admissible "
          f"candidate rows, matches {hits}. Elapsed {monotonic()-started:.1f} s.",flush=True)
    return hits


if __name__ == "__main__":
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--largest",type=int,default=8)
    parser.add_argument("--others",type=int,nargs="+",default=[7])
    parser.add_argument("--prime-limit",type=int,default=13)
    parser.add_argument("--decade",type=int,default=250000)
    parser.add_argument("--max-gap",type=int)
    args=parser.parse_args()
    if not __debug__:
        parser.error("run with Python assertions enabled")
    assert not run(args.largest,tuple(args.others),args.prime_limit,args.decade,args.max_gap)
