"""Finite columns 7/8 square-class check through 3,210,000 decimal decades."""

from argparse import ArgumentParser
from concurrent.futures import ProcessPoolExecutor, as_completed
from functools import cache
from itertools import combinations
from math import comb, factorial, gcd, isqrt
from time import monotonic

from Erdos849Wheel import allowed_moduli
from Erdos849WiderOdd import kernels, positive_unit, square_pairs, starting_pairs


def fundamental_data(d):
    """Find one positive unit and all primitive seeds needed for norms h²."""
    if d <= 2401:
        return positive_unit(d), {h: starting_pairs(d,h) for h in range(1,8)}, 0

    root = isqrt(d)
    m, denominator, digit = 0, 1, root
    previous_x, x = 1, root
    previous_y, y = 0, 1
    small_norms = {h*h: h for h in range(2,8)}
    primitive = []
    index = 0
    while True:
        m = denominator*digit-m
        denominator = (d-m*m)//denominator
        next_digit = (root+m)//denominator
        # The convergent's norm is (-1)^(index+1) times the next
        # complete-quotient denominator. Compare these small integers.
        if index % 2:
            if denominator == 1:
                assert next_digit == 2*root and next_digit > 7
                break
            h = small_norms.get(denominator)
            if h is not None:
                primitive.append((h,x,y))
        previous_x, x = x, next_digit*x+previous_x
        previous_y, y = y, next_digit*y+previous_y
        digit = next_digit
        index += 1
    unit = x,y
    assert x*x-d*y*y == 1
    seeds = {gap: [(gap,0)] for gap in range(1,8)}
    for reduced_gap,sx,sy in primitive:
        assert sx*sx-d*sy*sy == reduced_gap**2
        for gap in range(reduced_gap,8,reduced_gap):
            scale=gap//reduced_gap
            seeds[gap].append((scale*sx,scale*sy))
    return unit,seeds,index+1


@cache
def doubled_images():
    result = []
    for prime,rows in allowed_moduli(8,(7,)):
        doubled = {(2*n)%prime for n in rows}
        result.append((prime,bytes(i in doubled for i in range(prime))))
    return result


def moduli_for_kernel(d, unit):
    u,v = unit
    result = []
    for prime,allowed in doubled_images():
        a,b = u%prime,v%prime
        x,y = 1,0
        for period in range(1,2*prime+1):
            x,y = (a*x+d*b*y)%prime,(b*x+a*y)%prime
            if (x,y) == (1,0):
                break
        else:
            raise AssertionError((d,prime,"no unit period"))
        result.append((period,prime,a,b,allowed))
    return sorted(result)


def remaining_indices(d, offset_sum, seed, data, repetitions, end, unit_bits):
    x0,y0 = seed
    possible = (1<<end)-1
    for period,prime,u,v,allowed in data:
        x = x0%prime
        next_x = (u*x+d*v*(y0%prime))%prime
        mask = 0
        for t in range(period):
            if allowed[(x+offset_sum)%prime]:
                mask |= 1<<t
            x,next_x = next_x,(2*u*next_x-x)%prime
        if period not in repetitions:
            blocks = (end+period-1)//period
            repetitions[period] = ((1<<(blocks*period))-1)//((1<<period)-1)
        possible &= mask*repetitions[period]
        if not possible:
            break
        largest = possible.bit_length()-1
        if largest<=8 and x0.bit_length()+largest*(unit_bits+2)<=160:
            break
        if possible == 1 and y0==0:
            break
    while possible:
        least = possible & -possible
        yield least.bit_length()-1
        possible ^= least


def actual_row(d,left,right,seed,unit,index):
    x,y=seed
    u,v=unit
    while index:
        if index%2:
            x,y=u*x+d*v*y,u*y+v*x
        index//=2
        if index:
            u,v=u*u+d*v*v,2*u*v
    if y%2 or (x+left+right)%2:
        return None
    n=(x+left+right)//2
    assert (n-left)*(n-right)==d*(y//2)**2
    return n


def in_seventh_column(n):
    value = comb(n,8)
    target = factorial(7)*value
    x = 1<<((target.bit_length()+6)//7)
    while True:
        following = (6*x+target//x**6)//7
        if following>=x:
            break
        x=following
    assert x**7<=target<(x+1)**7
    return any(comb(m,7)==value for m in range(x,x+8))


def check_kernel(d, base_end, cutoff):
    unit,seeds,steps = fundamental_data(d)
    # Controls exercise the large-radicand construction against the
    # independent continued-fraction-basis algorithm on the smaller shell.
    if d>2401 and 30030%d==0:
        assert unit==positive_unit(d)
        for gap in range(1,8):
            assert set(seeds[gap])==set(starting_pairs(d,gap))
    growth = unit[0].bit_length()-1
    end = (base_end+growth-1)//growth
    data = moduli_for_kernel(d,unit)
    repetitions = {}
    orbits = checks = maximum_index = 0
    controls = set()
    candidates = set()
    hits = set()
    for left,right in combinations(range(8),2):
        for seed in seeds[right-left]:
            orbits += 1
            x,y = seed
            while x+left+right<=2*cutoff:
                if y%2==0 and (x+left+right)%2==0 and x+left+right>=32:
                    controls.add(((x+left+right)//2,left,right))
                x,y = unit[0]*x+d*unit[1]*y,unit[1]*x+unit[0]*y
            for index in remaining_indices(d,left+right,seed,data,repetitions,end,growth+1):
                checks+=1
                maximum_index=max(maximum_index,index)
                n=actual_row(d,left,right,seed,unit,index)
                if n is not None and n>=16:
                    candidates.add(n)
    for n in candidates:
        if in_seventh_column(n):
            hits.add(n)
    return d,steps,orbits,checks,maximum_index,controls,candidates,hits


def brute_controls(cutoff, supported):
    squarefree = list(range(cutoff+1))
    for p in range(2,isqrt(cutoff)+1):
        for n in range(p*p,cutoff+1,p*p):
            while squarefree[n]%(p*p)==0:
                squarefree[n]//=p*p
    rows = {}
    for n in range(16,cutoff+1):
        for i,j in combinations(range(8),2):
            a,b = squarefree[n-i],squarefree[n-j]
            d = a*b//gcd(a,b)**2
            if d in supported:
                rows.setdefault(d,set()).add((n,i,j))
    return rows


def main(prime_limit,decade,workers):
    if not __debug__:
        raise RuntimeError("This verifier requires Python assertions.")
    started=monotonic()
    support=kernels(prime_limit)
    cutoff=2000
    direct=brute_controls(cutoff,set(support))
    # 10^3 < 2^10 and 8! < 2^16 avoid constructing 10^decade.
    base_end=2+(10*decade+3*16+23)//24
    assert base_end>=5 and 24*(base_end-2)>=10*decade+3*16
    squares=list(square_pairs(8,7))
    assert {(n,i,j) for n,i,j in squares if 16<=n<=cutoff}==direct.get(1,set())
    candidates={n for n,_,_ in squares if n>=16}
    assert not any(in_seventh_column(n) for n in candidates)
    steps=orbits=checks=maximum_index=0
    with ProcessPoolExecutor(workers) as pool:
        jobs=[pool.submit(check_kernel,d,base_end,cutoff) for d in reversed(support[1:])]
        for finished,job in enumerate(as_completed(jobs),1):
            d,period,count,kept,max_index,controls,rows,hits=job.result()
            assert controls==direct.get(d,set()), d
            assert not hits,(d,hits)
            steps+=period
            orbits+=count
            checks+=kept
            maximum_index=max(maximum_index,max_index)
            candidates.update(rows)
            if finished%500==0:
                print(f"Checked {finished}/{len(jobs)} nonsquare kernels.",flush=True)
    control_count = sum(map(len,direct.values()))
    if prime_limit == 37 and decade == 3210000:
        assert (len(support)-1,steps,orbits,checks,maximum_index,control_count) == (
            4095,436216,142200,114766,2,7484)
        assert candidates == {16}
    print(f"Primes through {prime_limit}, height 10^{decade}, {len(support)-1} nonsquare kernels, "
          f"{steps:,} large-kernel CF steps, {orbits:,} Pell orbits, {checks:,} surviving indices, "
          f"maximum index {maximum_index}, {len(candidates):,} distinct admissible rows, "
          f"zero common coefficients. Elapsed {monotonic()-started:.1f} s.",flush=True)
    print(f"Checked {control_count:,} direct row/offset controls.",flush=True)


if __name__=="__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--prime-limit",type=int,default=37,choices=(13,23,31,37))
    parser.add_argument("--decade",type=int,default=3210000)
    parser.add_argument("--workers",type=int,default=6)
    args=parser.parse_args()
    if args.decade<1 or args.workers<1:
        parser.error("height and workers must be positive")
    main(args.prime_limit,args.decade,args.workers)
