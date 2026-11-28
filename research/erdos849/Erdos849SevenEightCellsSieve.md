# Prime assignments between columns seven and eight

**Theorem.** If a common value in columns seven and eight is at least $10^{136}$, each of the four reflected pairs in column eight shares an assigned prime with each of the seven terms in column seven. The 28 intersections require distinct prime divisors. This holds for every choice among terms of equal maximum valuation. In particular it applies at every possible height in both four-column patterns $\{3,5,7,8\}$ and $\{5,6,7,8\}$ by their finite height exclusions. [Bounds for the four-column patterns](Erdos849PatternHeights.md)

Suppose the same positive integer equals \(a=\binom n8=\binom m7\) on the left halves of two rows. For every prime dividing \(a\), choose a numerator term of greatest valuation in each row. Group the eight terms in reflected pairs, in offset order \((3,4),(2,5),(1,6),(0,7)\), and keep the seven terms in the other row separate. A cell consists of one reflected pair and one of the offsets \(j=0,\ldots,6\). A prime occupies that cell when its two chosen terms belong to it.

Write \(X=(n-3)(n-4)\) and \(S=(0,2,6,12)\). The four block products are \(X-s\) for \(s\in S\). Fix one block and one offset \(j\), and put \(y=m-j\). If the cell is empty, the small-prime denominator calculation produces an integer \(D\) for which

\[
Z=\frac{Da}{(X-s)y}\in\mathbb Z,\qquad
\prod_{v\in S}(X-v)=8\prod_{r=0}^6(y+j-r).
\]

The denominator counts the possible maximal-valuation assignments at primes \(2,3,5,7\), allowing arbitrary choices in ties. At a larger prime, divisibility of both selected factors would force the two assignments into this cell. [Denominator proof](Erdos849CellSieve.md) · [Exact denominator checker](Erdos849SaturatedCells.py)

For each certified cell the supplied vector \(c_t\) determines \(\sum_{t\ge1}c_t\binom Zt\). Substitute \(Z=D\prod_{v\ne s}(X-v)/(8!y)\) and reduce powers of \(X\) using the displayed monic quartic. This gives an ordinary polynomial \(P(X,y)\) and a remainder \(F(X,y)\) containing only negative powers of \(y\). The checker evaluates \(P\) on a grid up to its degrees in the row variables, which proves by finite differences that \(P\) is integer-valued. Thus \(F\) takes an integer value at the proposed collision. [Certificate vectors](Erdos849SevenEightCellsSieve.json)

Every term \(bX^u y^v\) of \(F\) has negative weight \(7u+4v\). Exact bounds on the row products give constants \(B,L,H\) with \(y^{1/4}\ge B\) and \(L<X/y^{7/4}<H\). Consequently

\[
|F|\le\sum_{u,v}|b|H^uB^{7u+4v}.
\]

The checker also verifies the sign when the leading weight, using the lower bound \(L\), dominates the sum of the other terms. Since each other weight is strictly smaller, dominance persists as \(y\) increases.

For each test prime \(p\) larger than the vector length and seven, enumerate the points of the curve modulo \(p\) with \(X=t(t-1)\). If \(y\ne0\), evaluate the Laurent remainder directly. If \(y=0\) and \(X\ne s\), reconstruct \(Z\) using \(7!(X-s)Z=D\prod_{r\ne j}(y+j-r)\). When \(y=0\) and \(X=s\), the alternative identity \(8!yZ=D\prod_{v\ne s}(X-v)\) excludes the point modulo \(p\). The resulting images contain every possible residue of the integer \(F\). Their intersection with its signed integer interval is empty for each supplied certificate. At primes below 53 the checker additionally compares the two expressions for \(F\) on all points with \(y\ne0\). [Exact residue images](Erdos849SevenCellsSieve.py) · [Verifier](Erdos849SevenEightCellsSieve.py)

```sh
python -B Erdos849SevenEightCellsSieve.py
```
