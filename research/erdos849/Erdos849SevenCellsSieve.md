# Complete prime assignments for columns 3 and 7, and columns 6 and 7

For each prime dividing an admissible common value, assign its full prime power to a numerator term of maximum valuation in each row. In columns 3 and 7 keep the individual terms. In column 6 take the three pairs of terms equidistant from the ends.

* For a collision in columns **3 and 7**, each one of the \(3\cdot7=21\) pairs of individual terms receives an assigned prime.
* For a collision in columns **6 and 7**, each of the three reflected pairs in the sixth-column numerator shares an assigned prime with **each** of the seven terms in the other numerator.

These conclusions hold at every height, for arbitrary choices among maximal terms, using only the indicated two rows. Each common value thus has at least 21 distinct prime divisors. For the second pair, a prime assigned to a reflected pair may belong to either of its terms.

## Finite pair intersections through \(10^{78}\)

Blokhuis, Brouwer and de Weger classified all admissible collisions up to \(10^{60}\); their list has none for either pair. On \((10^{60},10^{78}]\), the exact seventh-column row range is 1,259,932,332 through 469,651,583,456. For each possible row the coefficient must belong to the residue image of the other column at every modulus tested. The existing two-wheel CRT checker tested this condition exhaustively with the following counts. [Published base, Theorem 2.2](https://arxiv.org/pdf/1707.06893) · [CRT algorithm and controls](Erdos849Focused128.md)

| Columns | Seventh-column rows | CRT joins | Passing masks | Passing all local tests |
|---|---:|---:|---:|---:|
| 3, 7 | 468,391,651,125 | 30,405,641,632 | 1,996,578,630 | 0 |
| 6, 7 | 468,391,651,125 | 826,129,918 | 2,229,255 | 0 |

## Integral functions above \(10^{78}\)

Write \(k=3\) or \(6\); \(n,m\) are the rows in columns \(k,7\). For \(k=3\) take \(X=n\) and \(S=(0,1,2)\). For \(k=6\) take \(X=(n-2)(n-3)\) and \(S=(0,2,6)\). The block products in the first row are \(X-s\) for \(s\in S\). Let \(A(X)=\prod_{s\in S}(X-s)\) and \(B(m)=\prod_{j=0}^6(m-j)\), so \(A(X)=k!a,\ B(m)=7!a\).

Fix a block pair \(s,j\) and write \(y=m-j\). If the pair has no assigned prime in common, the small-prime valuation calculation gives an integer
\[
                         Z=\frac{Da}{(X-s)y}.
\]
It chooses \(D\) separately for each pair, by matching all possible numerator valuations at \(2,3,5,7\) for which the two assignments are not simultaneously forced. A prime exceeding seven needs no denominator correction. The proof that this enumeration covers arbitrarily large valuations is given in the earlier cell sieve. [Denominator proof](Erdos849CellSieve.md)

The certificate for each of the 42 choices consists solely of a vector of integers \(c_t\). Form \(\sum_{t\ge1} c_t\binom Zt\) in the function field, with
\[
 Z=\frac{D}{k!\,y}\prod_{u\in S,\ u\ne s}(X-u),\qquad
 A(X)=\frac{k!}{7!}B(y+j).
\]
Reduction in the monic cubic gives a Laurent polynomial in \(y\) with coefficients of degree at most two in \(X\). Split it into ordinary terms \(P(X,y)\) (nonnegative powers of \(y\)) and the remainder \(F(X,y)\) (negative powers). The verifier proves \(P\) integer-valued on the original row coordinates by evaluation on a grid through their respective degrees, using integer finite differences. Hence \(F\) is an integer at the proposed solution. [Exact function reconstruction](Erdos849SaturatedCells.py) · [42 vectors](Erdos849SevenCellsSieve.json)

All terms \(C X^u y^v\) of \(F\) have negative weight \(7u+3v\). For \(a\ge10^{78}\) the verifier bounds \(y^{1/3}\ge b\) and \(\ell<X/y^{7/3}<h\) by rational inequalities on the binomial products. Therefore the sum of \(|C|h^u b^{7u+3v}\) bounds \(|F|\). If the contribution of the unique leading weight, bounded below using \(\ell\), exceeds all other contributions at \(b\), its sign also determines the sign of \(F\); the other weights decay faster when \(y\) increases. The largest integer radii were 73,733,005 for columns 3 and 7 and 965,536,749 for columns 6 and 7.

The checker intersects the possible integer values with the images of \(F\) modulo primes up to 397 and greater than both seven and the vector length. When \(y\ne0\bmod p\) it evaluates the Laurent remainder directly. For \(y=0\bmod p\) and \(X\ne s\bmod p\), the alternative formula \(Z=(D/7!)\prod_{u\ne j}(m-u)/(X-s)\) gives the residue. The simultaneous residues \(y=X-s=0\bmod p\) are impossible because \(yZ=(D/k!)\prod_{u\ne s}(X-u)\) would be nonzero modulo \(p\). All these primes are units in the denominator of each \(\binom Zt\), so evaluation on a residue representative is valid. At the small sieve primes the checker cross-checks the Laurent evaluation with the unreduced binomial expression minus \(P\). None of the 42 intervals contains an integer satisfying all necessary conditions.

## Replay

Run from this directory with Python assertions enabled. Pass the path of Clang with the existing program's \(\texttt{--cc}\) option when necessary.

~~~sh
python -B Erdos849FocusedCRT.py --columns 3 7 --lower 60 --upper 78 --capacity 80000
python -B Erdos849FocusedCRT.py --columns 6 7 --lower 60 --upper 78 --capacity 80000
python -B Erdos849SevenCellsSieve.py
~~~
