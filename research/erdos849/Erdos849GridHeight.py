"""Integer height estimates for the four-column interpolation argument."""

from functools import cache
from itertools import combinations
from math import factorial


@cache
def log_s_bound(d):
    return len(str(3*factorial(d)))


def height_certificate(r, d, p):
    w = 839
    basis = min(p, 1680)
    m = (2*basis*r + basis-w-1)//(basis-w)
    n = basis*(m-r)
    rank = w*m
    spare = n-rank
    assert spare > 0
    # Every logarithm below is bounded above in base ten, with slack.
    log_s = log_s_bound(d)
    log_entries = (m+1)*r*d*log_s
    exponent = (rank+spare-1)//spare
    log_coeff = exponent*(1+len(str(n)) + log_entries)
    log_eval = (r*m*log_s + len(str(n)) + log_coeff
                + r*d*len(str(2*d)))
    log_norm = p*(len(str(p)) + len(str(n)) + log_coeff + r*d*log_s)
    return max(log_eval, log_norm)+1


if __name__ == "__main__":
    # The forbidden pairs force the second and third columns to be >=5 and >=7.
    forbidden = {(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,6),(4,6),(4,8)}
    from math import prod
    least = min(prod(cols) for cols in combinations(range(2,25),4)
                if forbidden.isdisjoint(combinations(cols,2)))
    assert least == 840 and 2*5*7*24 >= 840
    threshold = 230_000_000_000_000
    row_cutoff = max(1680, 2**840*factorial(840)+1)
    assert 839*len(str(row_cutoff)) < threshold
    # Take the largest columns first, stopping at product >=840.
    # For P>=1680, basis, m and rank are fixed for each r, so the
    # upper bound is monotone in d and P within that last regime.
    for r, divisor, cap in [(2,7,839),(3,35,119),(4,70,23)]:
        small = max(height_certificate(r, min(cap,p//divisor), p)
                    for p in range(840,1680))
        large = height_certificate(r,cap,839**2)
        assert max(small,large) < threshold
        print(f"{r} columns: log10 bound below {max(small,large):,}")
    smallest = height_certificate(4,8,840)
    assert smallest < 1_820_000_000_000
    print(f"Columns (3,5,7,8): log10 bound below {smallest:,}")
