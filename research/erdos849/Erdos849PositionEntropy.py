"""Exact integer bounds for occupied four-column prime assignments."""

from functools import cache
from itertools import product
from math import comb, factorial, lcm, prod

from Erdos849LocalInterpolation import floor_root


# Coefficients in the binomial basis, in increasing degree.
POLYS = {
    3: [(1,), (-1,1), (0,0,1)],
    5: [(1,), (-2,1), (0,-1,1), (-1,1,-1,1), (0,0,0,0,1)],
    6: [(1,), (-3,1), (2,-2,1), (1,0,-1,1), (1,-1,1,-1,1), (0,0,0,0,0,1)],
    7: [(1,), (-3,1), (0,-2,1), (-1,2,-2,1), (-1,1,0,-1,1),
        (-1,1,-1,1,-1,1), (0,0,0,0,0,0,1)],
    8: [(1,), (-4,1), (3,-3,1), (-2,4,-3,1), (0,-1,2,-2,1),
        (0,-1,1,0,-1,1), (1,-1,1,-1,1,-1,1), (0,0,0,0,0,0,0,1)],
}


@cache
def intervals(k, height):
    base = factorial(k) * 10**height
    root = floor_root(base, k)
    assert root**k <= base < (root+1)**k
    scale = factorial(k-1)
    bounds = []
    for e, coeffs in enumerate(POLYS[k]):
        assert len(coeffs) == e+1 and coeffs[-1] == 1
        reflected = [(-1)**e*sum(c*comb(k-1-s,j) for j,c in enumerate(coeffs))
                     for s in range(e+1)]
        flipped = []
        while reflected:
            flipped.append(reflected[0])
            reflected = [b-a for a,b in zip(reflected,reflected[1:])]
        assert flipped[-1] == 1
        error = max(sum(abs(c)*(scale//factorial(j))*(root+k)**j
                        for j,c in enumerate(basis[:-1])) for basis in (coeffs,flipped))
        lower = (scale//factorial(e))*(root-e+1)**e - error
        upper = (scale//factorial(e))*(root+k)**e + error
        assert 0 < lower <= upper
        bounds.append((lower,upper))
    return bounds


@cache
def candidates(cols, height):
    g = lcm(*cols)
    scale = prod(factorial(k-1) for k in cols)
    limit = 10**height * scale
    choices = []
    for degrees in product(*(range(k) for k in cols)):
        weight = sum(e*(g//k) for e,k in zip(degrees,cols))
        if weight >= g:
            continue
        bounds = [intervals(k,height)[e] for k,e in zip(cols,degrees)]
        lower,upper = map(prod,zip(*bounds))
        if 420*upper < limit:
            choices.append((weight,lower,upper,degrees))
    return sorted(choices)


@cache
def row_max(k, e):
    return max(abs(sum(c*comb(s,j) for j,c in enumerate(POLYS[k][e]))) for s in range(k))


def digit_box(cols, height, spacing, cap):
    chosen = []
    for entry in candidates(cols,height):
        weight,lower,upper,degrees = entry
        if chosen and (weight == chosen[-1][0] or 10*lower < spacing*chosen[-1][2]):
            continue
        chosen.append(entry)
    total = 0
    digits = []
    scale = prod(factorial(k-1) for k in cols)
    last = (10**height*scale-1)//420 + 1
    for index,(_,lower,upper,degrees) in enumerate(chosen):
        next_lower = chosen[index+1][1] if index+1 < len(chosen) else last
        amplitude = prod(row_max(k,e) for k,e in zip(cols,degrees))
        c = min(cap//amplitude,(next_lower-total-1)//upper)
        assert lower > total and c >= 0
        if c:
            digits.append((degrees,c))
            total += c*upper
    assert 420*total < 10**height*scale
    return digits


@cache
def nonzero_grid_values(cols, degrees):
    row_values = []
    for k,e in zip(cols,degrees):
        coeffs = POLYS[k][e]
        values = [sum(c*comb(s,j) for j,c in enumerate(coeffs)) for s in range(k)]
        row_values.append([(s,v) for s,v in enumerate(values) if v])
    result = []
    for point in product(*row_values):
        offsets,values = zip(*point)
        index = 0
        for k,s in zip(cols,offsets):
            index = index*k + s
        result.append((index,prod(values)))
    return result


def entropy_budget(cols, height, spacing, cap):
    # Each exponent tuple uses a distinct pole weight. Coefficient ranges
    # ensure the largest differing term dominates for every a >= 10^height.
    digits = digit_box(cols,height,spacing,cap)
    count = prod(c+1 for _,c in digits)
    widths = [1]*prod(cols)
    variances = [1]*prod(cols)
    for degrees,c in digits:
        for index,v in nonzero_grid_values(cols,degrees):
            widths[index] += c*abs(v)
            variances[index] += c*(c+2)*v*v
    bounds = [min(2*w*w,3*v) for w,v in zip(widths,variances)]
    grid = list(product(*(range(k) for k in cols)))
    groups = {}
    for i,s in enumerate(grid):
        orbit = tuple(min(x,k-1-x) for x,k in zip(s,cols))
        groups.setdefault(orbit,[]).append(i)
    multiplicity = 2**len(cols)
    for indices in groups.values():
        value = prod(bounds[i] for i in indices)**(multiplicity//len(indices))
        for i in indices:
            bounds[i] = value
    return grid,bounds,multiplicity,count


def excludes_forty(cols, grid, bounds, multiplicity, count):
    # Forty occupied tuples force exactly one choice per (5,8) pair.
    maxima = {}
    for s,b in zip(grid,bounds):
        key = tuple(s[cols.index(k)] for k in (5,8,7))
        maxima[key] = max(maxima.get(key,0),b)
    limit = 1
    for i in range(5):
        best = {0:1}
        for j in range(8):
            following = {}
            for mask,value in best.items():
                for h in range(7):
                    updated = mask | (1<<h)
                    following[updated] = max(following.get(updated,0),value*maxima[i,j,h])
            best = following
        # All seven positions in column seven meet the same column-five term.
        limit *= best[127]
    return (count**2 * 2**40)**multiplicity > limit


def prime_bound(cols, height, spacing, cap):
    grid,bounds,multiplicity,count = entropy_budget(cols,height,spacing,cap)
    # Require one assignment per certified (5,8) pair.
    order = sorted(range(len(bounds)),key=bounds.__getitem__,reverse=True)
    required = {}
    for index in order:
        s = grid[index]
        required.setdefault((s[cols.index(5)],s[cols.index(8)]),index)
    assigned = set(required.values())
    assert len(assigned) == 40
    needed = len(assigned)
    numerator = prod(bounds[i] for i in assigned)
    for index in order:
        if (count**2 * 2**needed)**multiplicity <= numerator:
            break
        if index not in assigned:
            numerator *= bounds[index]
            needed += 1
    assert (count**2 * 2**needed)**multiplicity <= numerator
    if needed == 40 and excludes_forty(cols,grid,bounds,multiplicity,count):
        return 41
    return needed


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled")
    for cols,records in (
        ((8,7,5,3), [(204,35,255,41),(225,18,255,43),(250,25,255,46),(300,50,511,50),
                      (400,50,511,58),(600,50,2047,67),(1000,50,8191,78),
                      (2000,50,1048575,91),(5000,50,2**30-1,103)]),
        ((8,7,6,5), [(184,25,255,41),(225,35,511,45),(250,25,511,48),(300,25,1023,53),
                      (400,25,1023,62),(600,35,2047,76),(1000,50,8191,93),
                      (2000,50,1048575,114),(5000,50,2**30-1,136)]),
    ):
        for h,spacing,cap,expected in records:
            actual = prime_bound(cols,h,spacing,cap)
            assert actual == expected,(cols,h,actual,expected)
            print(cols,h,actual)
