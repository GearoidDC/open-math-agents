"""Independent replay of the seven odd-exponent primes above 13 for columns 7 and 8."""

from functools import cache
from itertools import combinations
from math import comb, isqrt
from time import monotonic

from Erdos849SquareClassAudit import images, in_seventh_column
from Erdos849WiderOdd import positive_unit, starting_pairs


@cache
def centered_seeds(d, gap):
    """Enumerate signed solutions centered between reciprocal half-unit bounds."""
    unit_x, unit_y = positive_unit(d)
    limit = isqrt(gap**2*(unit_x-1)//(2*d))
    seeds = set()
    for signed_y in range(-limit, limit+1):
        radicand = d*signed_y**2+gap**2
        x = isqrt(radicand)
        if x*x != radicand:
            continue
        y = signed_y
        if y < 0:
            x, y = unit_x*x+d*unit_y*y, unit_y*x+unit_x*y
        assert x*x-d*y*y == gap**2 and 0 <= y < gap*unit_y
        seeds.add((x, y))
    assert seeds == set(starting_pairs(d, gap))
    return sorted(seeds)


def allowed_period(first, second, trace, offset_sum, prime, permitted_rows):
    """Build one period of the doubled row directly from its recurrence."""
    first, second = first%prime, second%prime
    x, y = first, second
    inverse_two = (prime+1)//2
    constant = (2-trace)*offset_sum % prime
    allowed = []
    while True:
        allowed.append(permitted_rows[x*inverse_two % prime])
        x, y = y, (trace*y-x+constant) % prime
        if (x,y) == (first,second):
            return allowed
        assert len(allowed) <= 2*prime


def audit_orbit(d, left, right, x, y, modular_images):
    unit_x, unit_y = positive_unit(d)
    trace = 2*unit_x
    offset_sum = left+right
    first = x+offset_sum
    second = unit_x*x+d*unit_y*y+offset_sum
    # Use a deliberately larger global cutoff and a slightly weaker
    # power-of-two bound than the primary verifier.
    exponent = unit_x.bit_length()-1
    end = 1+110000//exponent
    flags = bytearray(b"\x01")*end
    for prime, permitted_rows in modular_images:
        allowed = allowed_period(first, second, trace, offset_sum, prime, permitted_rows)
        period = len(allowed)
        for residue, ok in enumerate(allowed):
            if not ok and residue < end:
                flags[residue::period] = bytes((end-1-residue)//period+1)
        if flags.find(1,16) == -1:
            break
    # This checks an independently reproduced bound on the remaining indices.
    assert flags.find(1,16) == -1
    candidates = set()
    a, b = first, second
    for index in range(min(end,16)):
        if flags[index] and a%2 == 0 and a >= 32:
            candidates.add(a//2)
        a, b = b, trace*b-a+(2-trace)*offset_sum
    return candidates


def main():
    if not __debug__:
        raise RuntimeError("This audit requires Python assertions.")
    started = monotonic()
    assert 2**((110000-2)*8) > 40320*10**250000
    modular_images = tuple(images())
    candidates = set()
    orbits = 0
    for d in range(2,30031):
        if 30030 % d:
            continue
        for left,right in combinations(range(8),2):
            for x,y in centered_seeds(d,right-left):
                candidates.update(audit_orbit(d,left,right,x,y,modular_images))
                orbits += 1
    # For D=1, (x-y)(x+y)=gap^2<=49 gives x<=25 and n<=19.
    candidates.update(range(16,20))
    assert all(not in_seventh_column(comb(n,8)) for n in candidates)
    assert orbits == 2338
    print(f"Audited {orbits} Pell orbits with centered seeds and a doubled-row "
          f"recurrence. Exact checks on {len(candidates)} rows found no common value. "
          f"Elapsed {monotonic()-started:.1f} s.",flush=True)


if __name__ == "__main__":
    main()
