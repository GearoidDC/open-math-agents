# Erdős problem 849

Can every positive integer be the exact number of rows sharing an entry in the left half of Pascal’s triangle? For example, 3003 occurs in rows 14, 15, 78, and 3003. Five is the first unknown multiplicity. [Official problem](https://lefttosolve.com/p/Erdos849.erdos_849)

Any entry $a$ shared by five or more admissible rows exceeds $10^{128}$ and has at least **21 distinct prime divisors**. At least six of its prime divisors exceed 100. For either proper-column pattern $\{3,5,7,8\}$ or $\{5,6,7,8\}$, at least seven primes exceed 100. Every full prime power $P$ in its factorization satisfies $P^{15}<a$. At or above $10^{230{,}000{,}000{,}000{,}000}$ it needs at least 840 distinct primes. The proofs combine published classifications, integer computations and mathematical arguments. Lean checks the final deductions with the external inputs exposed as hypotheses. The existence of a five-row entry remains open.

- [Finite search through 10¹²⁸ and verification commands](Erdos849Focused128.md)
- [Hypotheses in the Lean cutoff theorem](Erdos849Interval128.lean)
- [21-prime proof at all heights and reproduction commands](Erdos849TwentyOneAtAllHeights.md)
- [Lean theorem for 21 primes and its computational hypotheses](Erdos849TwentyOneGraph.lean)
- [Pell equations for the two four-column patterns and the all-height large-prime bounds](Erdos849PellPatterns.md)
- [Twenty-prime proof at all heights and reproduction commands](Erdos849TwentyAtAllHeights.md)
- [Lean theorem for twenty primes and its computational hypotheses](Erdos849TwentyGraph.lean)
- [Nineteen-prime proof and reproduction commands](Erdos849NineteenAtAllHeights.md)
- [Lean theorem for nineteen primes and its computational hypotheses](Erdos849NineteenGraph.lean)
- [Five primes above 100 and the exact multiplicities of 100-smooth values](Erdos849SmoothNeighbors.md)
- [Six primes above 100 through approximately 3.32535 × 10¹⁴⁹ and from 10³¹³³ onward](Erdos849EightSmooth.txt)
- [Twenty distinct primes at large heights](Erdos849TwentyLarge.txt)
- [Sixteen-prime argument](Erdos849-sixteen-primes.txt)
- [Eighteen-prime proof at all heights and reproduction commands](Erdos849EighteenAtAllHeights.md)
- [Lean theorem and its computational hypotheses](Erdos849EighteenGraph.lean)
- [Local interpolation proof for individual prime powers](Erdos849InterpolatedPowers.txt)
- [Elementary twelfth-power proof and an exponent of 839 at large heights](Erdos849LargestPower.txt)
- [Prime gaps containing repeated rows](Erdos849PrimeWindow.md)
- [Interpolation argument for 840 primes and explicit bounds on individual factors](Erdos849GridHeight.txt)
- [Earlier finite computations](Erdos849-current-results.txt)
- [Reciprocal height argument](Erdos849ReciprocalRunge.txt)
- [Lind–Singmaster family](Erdos849LindBand.md)

## A reduction to finite witnesses

The proposed reduction proves the first four cases in Lean. Their first witnesses in increasing order are 2, 6, 120, and 3003. For every multiplicity \(t\ge 5\), the two open steps ask for the following.

1. Exhibit a binomial coefficient shared by at least \(t\) distinct admissible rows.
2. Given \(t+1\) distinct rows sharing a value, exhibit a strictly smaller value shared by at least \(t\) rows.

If both statements hold, the least value with at least \(t\) rows has exactly \(t\). Otherwise the second step produces a smaller witness, contradicting minimality. Each step asks only for positive witnesses that can be checked by listing their rows. The descent condition is sufficient and may be stronger than necessary. The original question allows an exact \(t\)-row witness to occur later than the first value reaching \(t+1\) rows.

The project linter accepted the single-file reduction. Lean 4.33.1 checked it against the pinned problem statement and reported only `propext`, `Classical.choice`, and `Quot.sound`. [Read the reduction](https://github.com/GearoidDC/open-math-agents/blob/a6a891beb411b67eb2b8fb421549e99a79662d26/reductions/Erdos849.erdos_849.R1.lean)

## Additional shallow-column checks

For Lind–Singmaster indices 9 through 100, the modular certificates exclude every column from 2 through 64. For indices 101 through 160, they exclude column 2. For each excluded position, a prime gives a residue that the proposed column never attains. The following commands check the same 5,856 certificates by two methods.

```sh
node Erdos849LindShallow.cjs --verify Erdos849LindShallowExtended.json
node Erdos849LindShallowVerify.cjs Erdos849LindShallowExtended.json
```

The ninth Lind–Singmaster value has 21,386,570 decimal digits and exactly three admissible rows. A self-contained integer computation verified the count for all rows and columns. [Proof and reproduction commands](Erdos849LindShallow.md)

The tenth Lind–Singmaster value has 146,585,752 decimal digits and exactly three admissible rows, including the edge. An exact modular search, rigorously rounded row intervals and a locally certified prime cover account for every column. [Proof and verification commands](Erdos849LindTenth.md)

The eleventh Lind–Singmaster value has 1,004,713,714 decimal digits. Its only rows are 3,478,759,199, 3,478,759,200, and the edge. The count has two verifications of the deep columns, one using a published prime-gap table and one using 200,898 locally certified primes. [Proof and verifiers](Erdos849LindEleven.md)

## Fixed-column results

The four columns 6, 10, 34, and 36 have an effectively computable finite set of shared values. A square product of factorials gives the same conclusion for infinitely many fixed four-column patterns. For the harder pair of columns 3 and 5, the associated genus-four Jacobian has rational rank at least ten and geometric Picard rank at most four. These bounds explain why the usual rank tests for classical and quadratic Chabauty do not classify that pair. [Fixed-column arguments](Erdos849FixedColumnMethods.txt) · [Curve argument](Erdos849ThreeFiveCurve.txt) · [Arithmetic verifier](Erdos849ThreeFiveCurve.py)

For columns 7 and 8 to share a value, each of the eight consecutive factors in the eighth-column numerator must have at least two distinct prime divisors. This restriction applies at every height. For the four-column pattern (3,5,7,8), sufficiently large values require at least 105 distinct prime divisors in each of those eight factors. [Prime-power exclusion](Erdos849PrimePowerRow.txt) · [Explicit height bound](Erdos849GridHeight.txt) · [Other restrictions on the four-column pattern](Erdos849SmallestCurve.txt)

Every value at least $10^{128}$ shared by columns 7 and 8 has at least 24 distinct prime divisors, regardless of its other representations. Each numerator term in the eighth column receives at least three distinct prime powers. [Twenty-four-prime proof](Erdos849PairPowerSlots.txt)
