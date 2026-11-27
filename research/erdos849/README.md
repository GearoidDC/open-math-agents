# Erdős problem 849

Can every positive integer be the exact number of rows sharing an entry in the left half of Pascal’s triangle? For example, 3003 occurs in rows 14, 15, 78, and 3003. Five is the first unknown multiplicity. [Official problem](https://lefttosolve.com/p/Erdos849.erdos_849)

Any entry shared by five or more admissible rows exceeds \(10^{105}\) and has at least sixteen distinct prime divisors. The finite range uses a published classification and exact searches. Lean checks the deductions from explicitly stated inputs. Separate arguments give stronger prime-count bounds at larger heights. The five-row case and the general problem remain open.

- [Results and verification commands](Erdos849-current-results.txt)
- [Hypotheses in the Lean cutoff theorem](Erdos849Interval105.lean)
- [Sixteen-prime argument](Erdos849-sixteen-primes.txt)
- [Reciprocal height argument](Erdos849ReciprocalRunge.txt)
- [Lind–Singmaster family](Erdos849LindBand.md)

## Additional shallow-column checks

For Lind–Singmaster indices 9 through 100, the modular certificates exclude every column from 2 through 64. For indices 101 through 160, they exclude column 2. For each excluded position, a prime gives a residue that the proposed column never attains. The following commands check the same 5,856 certificates by two methods.

```sh
node Erdos849LindShallow.cjs --verify Erdos849LindShallowExtended.json
node Erdos849LindShallowVerify.cjs Erdos849LindShallowExtended.json
```
