# Every reflected position pair for columns six and eight is occupied

Suppose \(a=\binom n6=\binom m8\) in the admissible half of Pascal's triangle. Each row partitions into pairs of terms equally distant from its center. In each numerator assign the full power of every prime dividing \(a\) to a term of maximal valuation, allowing any choices at ties. For a choice of one reflected pair from each row, let \(G\) be the product of the prime powers assigned to both chosen pairs. **All twelve products \(G\) exceed one when \(a\ge10^{120}\)**. This applies to the two columns alone. For the four-column pattern \((5,6,7,8)\), the previous lower bound \(a>10^{144}\) yields stronger conclusions. [Height bound for the four-column pattern](Erdos849PatternHeights.md)

Label the three pairs from the center outwards by \(s=0,2,6\), and the four pairs by \(r=0,2,6,12\). Each table entry gives strict lower bounds for \(G\) at the two indicated heights.

| \(s\) | \(r=0\) | \(r=2\) | \(r=6\) | \(r=12\) |
|---:|---:|---:|---:|---:|
| 0, at \(10^{120}\) | 138 | 9 | 363 | 21 |
| 2, at \(10^{120}\) | 14 | 10 | 43 | 2 |
| 6, at \(10^{120}\) | 33 | 1 | 92 | 35 |
| 0, at \(10^{144}\) | 2981 | 169 | 10357 | 412 |
| 2, at \(10^{144}\) | 253 | 268 | 770 | 41 |
| 6, at \(10^{144}\) | 587 | 23 | 1663 | 634 |

## An integral multiple of the extra coordinate

Write \(X=(n-2)(n-3),\ Y=(m-3)(m-4)\). The paired products are \(X-s,\ Y-r\) at these labels. Put \(y=Y-r\). Then
\[
 X(X-2)(X-6)=6!a=\frac{1}{56}\prod_{q\in\{0,2,6,12\}}(y+r-q).
\]

After removing assigned powers, the cofactor at each individual term of column \(k\) divides \(\operatorname{lcm}(1,\ldots,k)\), and the product of all cofactors is \(k!\). For a reflected pair of terms with gap \(g\), the smaller \(p\)-valuation of the terms is at most \(v_p(g)\). Hence their cofactor product divides
\(\gcd(k!,g\operatorname{lcm}(1,\ldots,k))\). The three resulting divisors for column six are \(60,180,60\); the four for column eight are \(840,2520,840,840\). [Proof of the individual cofactor bound](Erdos849PatternGeometry.txt)

Let \(D\) be the product of the two cofactor bounds at the selected labels. The assigned-power parts of the blocks are unitary divisors of \(a\) whose gcd is \(G\), so their product divides \(aG\). It follows that \(GZ\) is an integer for
\[
 Z=\frac{Da}{(X-s)y}=\frac{D}{720}\frac{\prod_{s'\ne s}(X-s')}{y}.
\]
Here \(D/720\) is an integer for every cell.

## Certifying a small nonzero value

The verifier builds an integer polynomial \(F(X,y,Z)\) of degree \(c\le12\) in \(Z\). Over the Laurent polynomial ring \(\mathbb Q[y,y^{-1}]\), reduce powers of \(X\) modulo the monic cubic above to the basis \(1,X,X^2\). Start with the successive powers \(Z^c\), subtract ordinary monomials with nonnegative \(y\)-exponent, then cancel terms \(X^iy^j\) shared with earlier reduced expressions in descending order of \(4i+3j\). Clearing rational denominators gives the integer polynomial in the original variables. This construction makes the polynomial easy to find; the following check certifies its value.

Compute \(T^3+b_1(y)T^2+b_2(y)T+b_3(y)\), the characteristic polynomial of multiplication by \(F\). The verifier reconstructs it from the original integer polynomial by a second implementation and checks equality. By Cayley–Hamilton the actual value is a root. Every coefficient is a Laurent polynomial using only negative exponents. For \(a\ge10^K\) with \(K=120,144\), each term in the eight-term row exceeds \((8!a)^{1/8}-7\), or equals that lower bound, giving \(y\ge B=14\cdot10^{K/4}\) by exact integer comparison.

For a Laurent polynomial \(b\), put \(N_B(b)=\sum_j|b_j|B^j\). The largest-exponent term of \(b_3\) dominates the remaining terms in absolute value at \(B\) and therefore at every \(y\ge B\). Hence \(F\ne0\). For each table entry \(M\), the checker verifies \(\sum_{t=1}^3 N_B(b_t)M^{ct}<1\). Dividing the cubic equation by \(F^3\) shows \(|F|<M^{-c}\). Since \(G^c F\) is a nonzero integer, \(G>M\) as claimed.

Run \(\texttt{python -B Erdos849SixEightCells.py}\) with assertions enabled. It regenerates the integer polynomials and prints each verified height, label pair, degree and bound. [Verifier](Erdos849SixEightCells.py)
