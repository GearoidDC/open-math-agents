"""Independent audit of the fourteen-prime exclusion for Erdős 849.

No functions or tables are imported from the primary certificates. Given the
published nine fixed-column classifications above 10^100, Kummer's prime-power
host criterion, and the signed falling-factorial congruence, this program
checks every numerical and finite-graph step from 10^100 upwards. It also
checks the finite exceptional rows using exact binomial values and a fresh
set of modular primes. The earlier exclusion below 10^100 is a separate input.
"""

from bisect import bisect_left
from functools import lru_cache
from math import comb, factorial, gcd, isqrt, prod


LOW, HIGH, CAP = 10**100, 10**390, 13
FIXED = {(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,6),(4,6),(4,8)}
SMALL = (2,3,5,7,11,13)
# Independent finite obligations. For d=14 every row has an empty host.
OBLIGATIONS = {7: (5,), 8: (5,), 13: (12,), 14: tuple(range(7,14))}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def last_true(test, first=0):
    """Largest nonnegative index satisfying a monotone true/false predicate."""
    lo, hi = first, first+1
    while test(hi):
        lo, hi = hi, 2*hi
    while hi-lo > 1:
        mid = (lo+hi)//2
        if test(mid):
            lo = mid
        else:
            hi = mid
    return lo


@lru_cache(maxsize=None)
def root(X, k):
    return last_true(lambda n: n**k <= X)


@lru_cache(maxsize=None)
def divisors_of_factorial(k):
    D = factorial(k)
    factors = set()
    for i in range(1, isqrt(D)+1):
        if D % i == 0:
            factors.update((i, D//i))
    return tuple(sorted(factors))


@lru_cache(maxsize=None)
def unit_factor(g, p):
    if p:
        while g % p == 0:
            g //= p
    return g


def host_costs(X, j, d):
    """Necessary singleton multipliers. Columns are large base first, then small.

    At a=X*y, a host n-s lies between (floor_root(d!X)-s)*y^(1/d)
    and (ceil_root(d!X)+d-1-s)*y^(1/d); analogously in the jth column.
    A nonzero signed difference is divisible by Q^2 for the singleton Q.
    Divide its bound by the p-free gcd before comparing b^2*bound to (n-s)^2.
    Because d<2j, the lower bound on b increases with y>=1.
    """
    primes = (0,) + tuple(p for p in SMALL if p <= d)
    D, J = factorial(d), factorial(j)
    nd, mj = root(X*D,d), root(X*J,j)
    upper_d = nd + (nd**d < X*D) + d-1
    upper_j = mj + (mj**j < X*J) + j-1
    divisors = divisors_of_factorial(d)
    squares = [v*v for v in divisors]
    costs = []
    for s in range(d):
        largest = [0]*len(primes)
        left_weight = J*factorial(s)*factorial(d-1-s)
        for r in range(j):
            right_weight = D*factorial(r)*factorial(j-1-r)
            equality_possible = (d-1-s - (j-1-r)) % 2 == 0
            left = left_weight*(upper_d-s)
            right = right_weight*(upper_j-r)
            if equality_possible and right_weight*(mj-r) <= left:
                # Without excluding the exact signed equality, allow b=1.
                largest = None
                break
            ceiling = max(left,right) if equality_possible else left+right
            g = gcd(left_weight,right_weight)
            for i, p in enumerate(primes):
                largest[i] = max(largest[i], ceiling//unit_factor(g,p))
        row = []
        for i in range(len(primes)):
            if largest is None:
                row.append(1)
                continue
            numerator = (nd-s)**2
            lower_square = (numerator + largest[i]-1)//largest[i]
            ix = bisect_left(squares, lower_square)
            row.append(divisors[ix] if ix < len(divisors) else D+1)
        costs.append(row)
    return costs


def singleton_minima(costs, D):
    """Assign distinct small primes first, then choose cheapest other offsets.

    A bitmask tracks used row offsets, not used primes. Costs above the entire
    factorial budget may be pruned. Entries returned are minima truncated at
    D+1, for every possible number of singleton positions.
    """
    count = len(costs)
    states = {0: 1}
    for column in range(1, len(costs[0])):
        nxt = states.copy()
        for mask, current in states.items():
            for s,row in enumerate(costs):
                bit = 1 << s
                if mask & bit:
                    continue
                cost = current*row[column]
                newmask = mask | bit
                if cost <= D and cost < nxt.get(newmask,D+1):
                    nxt[newmask] = cost
        states = nxt
    minima = [D+1]*(count+1)
    for mask, cost in states.items():
        k = mask.bit_count()
        minima[k] = min(minima[k],cost)
        free = sorted(costs[s][0] for s in range(count) if not mask & (1 << s))
        for price in free:
            cost *= price
            if cost > D:
                break
            k += 1
            minima[k] = min(minima[k],cost)
    return minima


def edge_reason(X,j,d):
    if (j,d) in FIXED:
        return "published"
    if d > CAP:
        return "empty"
    if d >= 2*j:
        return "open"
    D = factorial(d)
    costs = host_costs(X,j,d)
    minima = singleton_minima(costs,D)
    least_row_term = root(D*X,d) - d + 1
    for empty in range(d+1):
        num_singles = max(0,2*(d-empty)-CAP)
        if least_row_term**empty * minima[num_singles] <= D:
            break
    else:
        return "analytic"
    large_only = sorted(row[0] for row in costs)
    if prod(large_only[:max(0,2*d-CAP)]) > D:
        return "small-or-empty"
    return "open"


def audit_graph(X, finite):
    N = root(X,CAP)
    first_deep = next(t for t in range(CAP+1,20) if comb(N,t)>N**CAP)
    # C(n,t)/n^CAP is increasing from N onwards for t>CAP; the collision
    # value is bounded by n^CAP from its prime-power factors. No column >=t.
    require(N >= 2*first_deep,"row cutoff is outside the admissible half")
    columns = tuple(range(2,first_deep))
    forbidden = set()
    for d in columns:
        for j in range(2,d):
            reason = edge_reason(X,j,d)
            if reason in ("published","analytic"):
                forbidden.add((j,d))
            if finite and j in OBLIGATIONS.get(d,()):
                expected = "empty" if d == 14 else "small-or-empty"
                require(reason in (expected,"published","analytic"),
                        f"missing necessary row condition for {(j,d)}: {reason}")
                forbidden.add((j,d))
    bad = []
    tested = 0
    for mask in range(1 << len(columns)):
        if mask.bit_count() != 4:
            continue
        tested += 1
        if not any(mask & (1 << (j-2)) and mask & (1 << (d-2)) for j,d in forbidden):
            bad.append(tuple(k for k in columns if mask & (1 << (k-2))))
    require(not bad,f"uncovered patterns: {bad}")
    return first_deep, tested


def exceptional_ranges(d, small):
    """Exact inclusive coefficient row bounds and the union of exceptional rows.

    For a small-base singleton, strip every factor p out of its cofactor.
    The resulting p-free divisor u of d! gives n-s=u*p^v, v>=1. This avoids
    reproducing the primary generator's many different b*p^e descriptions.
    """
    lo = last_true(lambda n: comb(n,d) < LOW) + 1
    hi = last_true(lambda n: comb(n,d) <= HIGH)
    require(comb(lo-1,d)<LOW<=comb(lo,d)<=comb(hi,d)<=HIGH<comb(hi+1,d),"row endpoints")
    lower, upper = lo-d+1, hi
    divisors = divisors_of_factorial(d)
    centers = {u for u in divisors if lower <= u <= upper}
    if small:
        for p in SMALL:
            if p>d:
                continue
            for u in divisors:
                if u%p == 0:
                    continue
                c = u*p
                while c < lower:
                    c *= p
                while c <= upper:
                    centers.add(c)
                    c *= p
    intervals = []
    for c in sorted(centers):
        start, stop = max(c,lo), min(c+d-1,hi)
        if intervals and start <= intervals[-1][1]+1:
            intervals[-1][1] = max(intervals[-1][1],stop)
        else:
            intervals.append([start,stop])
    return intervals, len(centers)


def primes_between(low,high):
    return [p for p in range(low,high) if all(p%q for q in range(2,isqrt(p)+1))]


@lru_cache(maxsize=None)
def residue_image(p,j):
    # Walk down the jth column in F_p. Because j<p, row residues modulo p
    # suffice; C(u,j)=0 for u<j, and all recurrence denominators are units.
    vals = {0,1}
    v = 1
    for u in range(j+1,p):
        v = v*u*pow(u-j,-1,p) % p
        vals.add(v)
    return vals


def audit_rows(d, js, small):
    intervals, ncenters = exceptional_ranges(d,small)
    checks = {}
    for j in js:
        options = [(p,residue_image(p,j)) for p in primes_between(607,1300)]
        # Fewer residues mean fewer survivors. Sorting is merely a speed choice.
        options.sort(key=lambda pair: len(pair[1])/pair[0])
        checks[j] = options
    rows = probes = exact = 0
    for start, stop in intervals:
        for n in range(start,stop+1):
            a = comb(n,d)
            rows += 1
            for j in js:
                for p,residues in checks[j]:
                    probes += 1
                    if a%p not in residues:
                        break
                else:
                    exact += 1
                    m = last_true(lambda u: comb(u,j) <= a)
                    require(comb(m,j) != a or m<2*j,
                            f"actual collision C({n},{d})=C({m},{j})={a}")
    return ncenters, rows, probes, exact


def main():
    for X, finite in ((LOW,True),(HIGH,False)):
        print("interval" if finite else "unbounded", "graph:", audit_graph(X,finite), flush=True)
    total = 0
    for d, js in OBLIGATIONS.items():
        centers,rows,probes,exact = audit_rows(d,js,d!=14)
        total += rows
        print(f"d={d}, smaller={js}: {centers} centers, {rows} distinct rows, "
              f"{probes} residue tests, {exact} exact inversions",flush=True)
    print(f"Verified all {total} distinct (row, larger column) candidates.",flush=True)


if __name__ == "__main__":
    main()
