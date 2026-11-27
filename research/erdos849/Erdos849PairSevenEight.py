"""Check the eighteen-prime obstruction for common columns seven and eight."""

from math import factorial, gcd

from Erdos849EighteenPrimes import row_bounds
from Erdos849LargestPower import shifted_product
from Erdos849LocalInterpolation import HEIGHT
from Erdos849SingletonCertificate import factorial_divisors


def main():
    q = 46_862_860
    lo7, hi7 = row_bounds(7, HEIGHT)
    lo8, hi8 = row_bounds(8, HEIGHT)
    # A partner power pays p^v_p(420). The product of all such losses
    # divides 420, and the two largest losses for different primes are 7,5.
    assert lo8 > factorial(8)*7*q
    assert lo8**3 > factorial(8)*420*q**3*hi7
    assert lo8**2 > factorial(8)*7*q*hi7
    assert lo7**2 > factorial(7)*35*q**2*hi8

    ratios = set()
    for b in factorial_divisors(7):
        for c in factorial_divisors(8):
            if b*hi8 >= c*lo7:
                common = gcd(b,c)
                ratios.add((b//common,c//common))
    peak = 0
    for b,c in ratios:
        for r in range(7):
            for s in range(8):
                d8 = shifted_product(8,s,c)
                d7 = shifted_product(7,r,b) + [0]
                equation = [factorial(7)*u-factorial(8)*v for u,v in zip(d8,d7)]
                # Positive t with n=s+c*t, m=r+b*t divides the first
                # nonzero coefficient after making the equation primitive.
                bound = abs(next(a for a in equation if a))//gcd(*equation)
                peak = max(peak,c*bound)
    assert peak < lo8
    print(f"Checked {len(ratios)} reduced ratios and {56*len(ratios)} equations.")
    print(f"A complete pair in one receiving term would require n-s <= {peak}.")


if __name__ == "__main__":
    main()
