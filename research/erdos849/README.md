# Erdős problem 849

Can every positive integer be the exact number of rows sharing an entry in the left half of Pascal’s triangle? For example, 3003 occurs in rows 14, 15, 78, and 3003. Five is the first unknown multiplicity. [Official problem](https://lefttosolve.com/p/Erdos849.erdos_849)

Any entry $a$ shared by five or more admissible rows exceeds $10^{128}$ and has at least **21 distinct prime divisors**. At least seven of its prime divisors exceed 100. At least seven primes greater than both 19 and its largest proper column divide it to odd exponents, so its squarefree part is at least 63,392,725,189. Each of the proper-column patterns $\{3,5,7,8\}$ and $\{5,6,7,8\}$ requires at least 35 distinct prime divisors, including at least thirteen above 100. Each pattern also requires seven primes above 37 to odd exponents, and its squarefree part is at least 228,098,450,046,409. Its largest prime divisor is at least 173. The first pattern requires $a>10^{136}$ and the second requires $a>10^{144}$. Every full prime power $P$ in its factorization satisfies $P^{15}<a$. At or above $10^{230{,}000{,}000{,}000{,}000}$ it needs at least 840 distinct primes. The proofs combine published classifications, integer computations and mathematical arguments. Lean checks the deductions in the linked formal theorems, with external inputs exposed as hypotheses. The existence of a five-row entry remains open.

- [Merged Lean reduction for the first four multiplicities and the remaining hypotheses](https://github.com/lefttosolve2/open-math-agents/pull/12651)
- [Every one of the 35 numerator-term intersections in columns 5 and 7 above $10^{136}$](Erdos849FiveSevenCells.md) and [Lean deduction of the prime counts from coverage](Erdos849FiveSevenCoverage.lean)
- [At least 36 to 42 distinct primes as the height increases in the two four-column patterns](Erdos849ShallowPrimeCounts.md)
- [Every one of the 28 shared-prime intersections for columns 7 and 8 above $10^{136}$](Erdos849SevenEightCellsSieve.md)
- [How prime powers are distributed across all 840 or 1,680 individual four-column positions at explicit heights](Erdos849PrimePowerCells.md)
- [All-height shared-prime constraints in columns 3 and 5, 5 and 6, and 6 and 8](Erdos849CellSieve.md), [3 and 8](Erdos849ThreeEightCells.md), [5 and 8](Erdos849FiveEightCellsSieve.md), and [3 and 7 and 6 and 7](Erdos849SevenCellsSieve.md)
- [Direct integer-valued certificates for 62 pairs of numerator blocks](Erdos849SaturatedCells.md) and [quantitative factors in columns 6 and 8](Erdos849SixEightCells.md)
- [At least two distinct neighbours for each numerator position in the longer of two rows](Erdos849HostLeaves.md)
- [All equal triples for three bounded row and column spans](Erdos849RowTriples.md)
- [Cubic covers of the genus-two quotient for columns 3 and 5](Erdos849ThreeFiveCubicCovers.md) and [elementary abelian covers and their units](Erdos849ThreeFiveAbelianCovers.md)
- [All-height classification of disconnected prime assignments for the nine shallow column pairs](Erdos849FullHostCuts.md)
- [At most two components after removing primes through seven, using only two rows](Erdos849PairComponents.md)
- [Counting five-row candidates via simultaneous-column curves and two-torsion](Erdos849TorsionDensity.md)
- [Good reduction of the pair curves](Erdos849PairReduction.md) and [the underlying uniform integral-point count](Erdos849MultiplicityDensity.md)
- [Sharper counts for candidates occurring in column two or four](Erdos849HyperellipticDensity.md)
- [The obstruction to obtaining three equal descendants by a fixed Pascal translation](Erdos849PascalDescent.md)
- [The genus-six quotient of columns five and eight and the descents it excludes](Erdos849FiveEightQuintic.md)
- [Primes above seven connect every numerator term across both four-column patterns at every height](Erdos849CommonFactors.md)
- [Five all-height exclusions for individual numerator terms in the two four-column patterns](Erdos849SingletonSquareRows.md)
- [A prime above 53 across each split into halves in columns six and eight](Erdos849BalancedCuts.md)
- [Seven prime exponents nonzero modulo three in common values of columns seven and eight](Erdos849HigherCubes.md)
- [Lean equivalence between exactly five rows and nine or ten positions](Erdos849Reflection.lean)
- [November 28 Singmaster submissions and their connection to exact row counts](Erdos849SingmasterBridge.md)
- [Square and fourteen-times-square exclusions in both four-column patterns](Erdos849FourteenPairs.md)
- [Seven odd-exponent primes above both 19 and the largest proper column](Erdos849GlobalOddNineteen.md)
- [Seven odd-exponent primes above 37 in both four-column patterns](Erdos849WiderOdd37.md)
- [An odd-exponent prime above 100 in the finite range and a squarefree-part bound at all heights](Erdos849HundredOdd.md)
- [All-height restrictions on pairs of numerator terms with squarefree parts dividing 210](Erdos849OrbitDescent.md)
- [Finite search through 10¹²⁸ and verification commands](Erdos849Focused128.md)
- [Hypotheses in the Lean cutoff theorem](Erdos849Interval128.lean)
- [21-prime proof at all heights and reproduction commands](Erdos849TwentyOneAtAllHeights.md)
- [Lean theorem for 21 primes and its computational hypotheses](Erdos849TwentyOneGraph.lean)
- [Pell equations for the two four-column patterns and the all-height large-prime bounds](Erdos849PellPatterns.md)
- [Seven prime divisors above 100 for all five-row values](Erdos849SevenAtAllHeights.md)
- [Odd exponents, the squarefree part of a five-row value, and the Pell and Runge checks](Erdos849SquareClassRows.md)
- [How prime factors connect positions in different rows](Erdos849JointHosts.md)
- [Rank bounds and endomorphisms of the genus-three quotients](Erdos849QuarticDescent.txt)
- [Four assigned primes in each of the eight numerator terms and 32 in total](Erdos849HostCount.md)
- [Thirteen distinct prime divisors above 100 and the largest prime divisor](Erdos849RowThreshold.md)
- [Twelve distinct prime divisors above 100](Erdos849PatternThreshold.md)
- [Prime divisors of the preceding and following integers](Erdos849NeighborDivisors.md)
- [Prime counts in individual numerator terms and the genus-three quotient curves](Erdos849PatternGeometry.txt)
- [At least eleven primes above 100 for both remaining patterns](Erdos849PatternCapTen.md)
- [At least ten primes above 100 for columns 3, 5, 7 and 8](Erdos849PatternThree.txt)
- [At least ten primes above 100 for columns 5, 6, 7 and 8](Erdos849PatternSixHost.md)
- [Finite exclusions through 10¹³⁶ and 10¹⁴⁴ for the two patterns](Erdos849PatternHeights.md)
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

The upstream proof checker accepted the single-file reduction against the pinned problem statement on November 27, 2026. Its axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`. [Submitted reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12651) · [Upstream verification](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/46072753324)

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

In both four-column patterns, every numerator term in every represented proper column must have at least two distinct prime divisors. The pairwise proof uses the eighth column and a shorter column at a time. This restriction applies at every height. For the four-column pattern (3,5,7,8), sufficiently large values require at least 105 distinct prime divisors in each of those eight factors. [Prime-power exclusion](Erdos849PrimePowerRow.txt) · [Explicit height bound](Erdos849GridHeight.txt) · [Other restrictions on the four-column pattern](Erdos849SmallestCurve.txt)

Every value at least $10^{128}$ shared by columns 7 and 8 has at least 24 distinct prime divisors, regardless of its other representations. Each numerator term in the eighth column receives at least three distinct prime powers. [Twenty-four-prime proof](Erdos849PairPowerSlots.txt)
