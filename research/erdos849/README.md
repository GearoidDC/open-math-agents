# Erdős problem 849

Can every positive integer be the exact number of rows sharing an entry in the left half of Pascal’s triangle? For example, 3003 occurs in rows 14, 15, 78, and 3003. Five is the first unknown multiplicity. [Official problem](https://lefttosolve.com/p/Erdos849.erdos_849)

Any entry shared by five or more admissible rows exceeds $10^{128}$ and has at least sixteen distinct prime divisors. At or above $10^{524}$ it needs at least eighteen. At or above $10^{230{,}000{,}000{,}000{,}000}$ it needs at least 840. The finite range uses a published classification and exact searches. Lean checks the deduction with those results as explicit inputs. The five-row case and the general problem remain open.

- [Finite search through 10¹²⁸ and verification commands](Erdos849Focused128.md)
- [Hypotheses in the Lean cutoff theorem](Erdos849Interval128.lean)
- [Sixteen-prime argument](Erdos849-sixteen-primes.txt)
- [Eighteen-prime argument](Erdos849EighteenPrimes.txt)
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

## Fixed-column results

The four columns 6, 10, 34, and 36 have an effectively computable finite set of shared values. A square product of factorials gives the same conclusion for infinitely many fixed four-column patterns. For the harder pair of columns 3 and 5, the associated genus-four Jacobian has rational rank at least ten and geometric Picard rank at most four. These bounds explain why the usual rank tests for classical and quadratic Chabauty do not classify that pair. [Fixed-column arguments](Erdos849FixedColumnMethods.txt) · [Curve argument](Erdos849ThreeFiveCurve.txt) · [Arithmetic verifier](Erdos849ThreeFiveCurve.py)

For columns 7 and 8 to share a value, each of the eight consecutive factors in the eighth-column numerator must have at least two distinct prime divisors. This restriction applies at every height. For the four-column pattern (3,5,7,8), sufficiently large values require at least 105 distinct prime divisors in each of those eight factors. [Prime-power exclusion](Erdos849PrimePowerRow.txt) · [Explicit height bound](Erdos849GridHeight.txt) · [Other restrictions on the four-column pattern](Erdos849SmallestCurve.txt)
