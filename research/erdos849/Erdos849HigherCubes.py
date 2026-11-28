"""Explicit cubic-class height bounds for simultaneous binomial columns."""

from itertools import product
from math import factorial, lcm, prod

from Erdos849HigherSquare import branch_check, ceil_div, digits, valuation


def certificate(columns, multiple):
    largest = columns[-1]
    period = lcm(*columns)
    weights = tuple(period // k for k in columns)
    q = weights[-1]
    limit = multiple * period
    group_size = prod(columns) // period
    rows = group_size * (limit + 1)
    for k in columns:
        branch_check(k)
    histogram = [0] * period
    for exponents in product(*(range(k) for k in columns)):
        histogram[sum(e*w for e,w in zip(exponents, weights)) % period] += 1
    assert set(histogram) == {group_size}
    # Among row-constant exponent vectors, the zero-fiber tests kill all
    # coordinates when at most one column degree is a multiple of three.
    assert sum(k % 3 == 0 for k in columns) <= 1

    def monomial_count(root_weight):
        count = 0
        for exponents in product(*(range(k) for k in columns[:-1])):
            base = sum(e*w for e,w in zip(exponents,weights))
            for root_power in range(3):
                count += max(0, 1 + (limit-base-root_power*root_weight)//q)
        return count

    min_count = monomial_count(sum((2*k//3)*w for k,w in zip(columns,weights)))
    max_count = monomial_count(0)
    assert min_count > rows
    primes = (2,3,5,7)
    assert largest == 8
    overhead = {p: sum(valuation(factorial(k),p) for k in columns) for p in primes}
    slopes = {p: max(k*valuation(9*k*k,p)+valuation(factorial(k),p)
                     for k in columns) for p in primes}
    magnitude = 2**(limit//q) * factorial(largest)**multiple
    tuple_bound = (1+limit//q)**len(columns)
    box_digits = 0
    for h in range(limit+1):
        denominator = prod(p**(overhead[p]+h*slopes[p]//period) for p in primes)
        equation_height = denominator*tuple_bound*magnitude*1000**(h//q)
        box_digits += group_size*digits(2*max_count*equation_height+1)
    coefficient_digits = 1 + box_digits//(min_count-rows)
    branch_cutoff = period*(coefficient_digits+1+
        digits(2*max_count*magnitude*1000**ceil_div(limit+1,q)))

    degree = 3*prod(columns[:-1])
    reductions = sum(3*k-1 for k in columns[:-1])
    matrix_factor = max_count*prod(factorial(k)**2 for k in columns)*(2*factorial(largest))**reductions
    norm_cutoff = largest*(digits(factorial(degree))+degree*(coefficient_digits+digits(matrix_factor))+1)
    return (limit, group_size, min_count, max_count, coefficient_digits,
            branch_cutoff, norm_cutoff, max(branch_cutoff,norm_cutoff))


if __name__ == "__main__":
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    parameters = [((3,5,7,8),11,1771744), ((5,6,7,8),11,3963304),
                  ((5,7,8),8,447400), ((7,8),6,53592)]
    for columns,multiple,expected in parameters:
        result = certificate(columns,multiple)
        assert result[-1] == expected
        print(columns,result,flush=True)
