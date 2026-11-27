# The eleventh Lind–Singmaster value occurs in exactly three rows

The 1,004,713,714-digit integer

$$A=\binom{3\,478\,759\,200}{1\,328\,767\,775}$$

occurs in rows **3,478,759,199**, **3,478,759,200**, and **$A$** of the left half of Pascal's triangle. Its proper columns in the first two rows are 1,328,767,776 and 1,328,767,775 respectively. Each further occurrence would have to pass one of the exhaustive checks below. The tests use the row and column indices of $A$ without writing out the integer.

## Shallow columns

Write $N=3,478,759,200$ and $K=1,328,767,775$. For each candidate column $2\le j<1,200,000$, the verifier finds a prime $p>j$ such that $y=\binom NK\bmod p$ is nonzero and absent from column $j$ modulo $p$. Lucas's theorem gives $y$ from the base-$p$ digits of $N,K$. To reduce the size of the digit binomials, the calculation uses symmetry and the identity $\binom ab\equiv(-1)^b\binom{p-1-a+b}{b}\pmod p$. Controls test the residue routine against direct integer arithmetic and the other known representation.

For a candidate row $m$, Lucas gives $\binom mj\equiv\binom{m\bmod p}j\pmod p$. For $d=p-1-j$ its nonzero possibilities have the form $(-1)^{d-s}\binom ds$ for $0\le s\le d$. The verifier tests this finite image by recurrence. It found a witness prime for all **1,199,998** columns. The largest was **1,200,007**. [Shallow and middle verifier](Erdos849LindEleven.py)

## Middle columns

If $A=\binom mj$, put $R=(j!A)^{1/j}$ and $u=(j-1)/2$. Pairing numerator factors equidistant from their midpoint gives

$$R+u\ \le m\le\ R+u+\frac{u^2}{2R}.$$

Outward-rounded MPFR logarithms and exponentials enclose both endpoints. For an interval of candidate integers $[l,h]$, each of 32 certified prime divisors of $A$ must have a multiple in $[l-j+1,h]$. If any one lacks a multiple, all rows in the interval are excluded. The implementation checks that its interval routine retains the three known proper occurrences of 3003. [Interval proof in Lean](Erdos849FallingBounds.lean) · [Interval and divisibility routines](Erdos849LindTenth.py)

For columns **1,200,000 through 63,319,920**, every possible row exceeds 171,595,999,999,999,995,152,414 by an exact binomial comparison. All 62,119,921 tested column intervals missed the integers above the respective search floors. Each floor is below or equal to this certified lower bound. [Comparison proof](Erdos849LindElevenLocal.md)

## Two ways to finish the count

The shorter calculation uses the published maximum gap of 1,476 between consecutive primes below $4\cdot10^{18}$. If $h=\lceil m/E\rceil$ and $p$ is a prime just below $\lfloor m/h\rfloor$, the multiple $hp$ can lie in the numerator even when $m>E$. When $p>N$ and $hp$ lies in the numerator, the prime would divide $A$, which divides $N!$. Lean verifies how a gap bound through $E$ gives this larger range of excluded rows. This argument and exact binomial comparisons leave only the two listed proper positions in all columns from 63,319,921 upward. [Deep-column proof and digit count](Erdos849LindElevenDeep.md) · [Scaled prime cover in Lean](Erdos849ScaledPrimeCover.lean) · [Prime-gap data](https://sweet.ua.pt/tos/gaps.html)

The independent calculation uses the boundary row $B=2^{45}$. Exact logarithmic comparisons prove $\binom B{T-1}<A<\binom BT$ for $T=175,119,328$. A row at or below $B$ requires a column at least $T$. Beyond the known neighboring rows, a chain of 200,898 locally certified primes through this range has gaps smaller than $T$. A numerator then contains a prime larger than $N$. Conversely a row at or above $B$ in column $T$ or later already has coefficient larger than $A$. The intervening columns from 63,319,921 through $T-1$ are checked by the same outward-rounded interval test with row floor $B+1$. [Local prime chain and comparisons](Erdos849LindElevenLocal.md)

The intervening range comprises 111,799,407 columns. Of these, 50,187,627 intervals contained at least one candidate integer row. The prime-divisibility test rejected all 50,187,627.

In the 14 rows between the bounding primes near $N$, exact neighboring-coefficient ratios recover precisely the two stated proper positions. Column one supplies the edge at $m=A$. This determines the multiplicity of this family member. The existence of a value with five rows remains open.

## Reproduction

With Python and gmpy2 2.2.1, run the following command in this directory. It checks both proofs. The options `--part shallow`, `middle`, `deep`, `bridge`, and `local` run individual stages. The first three reproduce the shorter proof. The shallow, middle, bridge, and local stages give the result using a locally certified prime chain.

```sh
python Erdos849LindEleven.py --workers 6
```
