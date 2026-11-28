# A required prime factor in both four-column patterns

**If an admissible five-row example has exactly forty distinct prime divisors, one of them is 13.** The computation proves divisibility by 13 for every common value in the indicated columns and height interval. The finite lower exclusions and the 41-prime upper thresholds place every hypothetical exactly-forty example in one of these intervals. [Finite lower exclusions](Erdos849FourHostPairs.md) · [Upper bounds for forty primes](Erdos849ConditionalEntropy.md)

| Columns | Interval for the common value | Residue disks | Auxiliary polynomials | Real sign intervals |
| --- | --- | ---: | ---: | ---: |
| 3, 5, 7, 8 | $10^{137}\le a\le 10^{185}$ | 145 | 358 | 2,336 |
| 5, 6, 7, 8 | $10^{146}\le a\le 10^{170}$ | 13 | 58 | 401 |

Suppose the common value a is nonzero modulo 13. Direct enumeration gives a ≡ 1 modulo 13. For each even column the reflection n ↦ k−1−n preserves C(n,k). Choosing the appropriate reflections makes every row coordinate n_k congruent to k modulo 13. The derivative of the falling factorial (x)_k at x=k is a unit modulo 13 in all five column sizes.

Write a=A+bT. In the second pattern, b=169 and A runs over the thirteen lifts of 1 modulo 13. The first pattern retains two of these disks and divides each other disk into thirteen lifts modulo 2197. The checker confirms exactly one disk covers each residue in the nonzero fiber.

Hensel's lemma gives each row coordinate as a power series in bT with coefficients in the 13-adic integers. On a disk of modulus b the archive gives integer auxiliary polynomials and a precision E. For each polynomial, the verifier checks divisibility by b^E on the E inputs T=0,…,E−1. Modulo b^E its composition with the coordinate series has degree less than E in T. The Newton difference formula extends the divisibility to every integer T.

Let H denote the upper exponent in the table. The absolute value of each original or reflected coordinate is at most floor((k!·10^H)^(1/k))+k. Using these bounds, the verifier proves the sum of the absolute monomial contributions of each auxiliary polynomial is strictly less than b^E. All certified polynomials would therefore vanish at any point in the interval lying on their disk.

To exclude simultaneous vanishing, the verifier subdivides the interval in a using exact integer square roots. On a subinterval with endpoints L,U, each coordinate's magnitude lies between floor((k!L)^(1/k))−k and floor((k!U)^(1/k))+k. For every reflection it uses these magnitudes and the corresponding monomial signs to find a polynomial of strict sign on the whole subinterval. The final column in the table counts the covering subintervals separately for every disk and reflection.

Run `python -B Erdos849ThirteenFactor.py` beside its compressed certificate. The checker uses standard-library integer arithmetic throughout.
