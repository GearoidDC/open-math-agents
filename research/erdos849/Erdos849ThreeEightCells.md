# All twelve block intersections in columns three and eight

Suppose \(a=\binom n3=\binom m8\) with \(n\ge6,m\ge16\). In each row assign each full prime power \(p^{v_p(a)}\) to a numerator term of greatest \(p\)-valuation, breaking ties arbitrarily. Separate the three terms in the first row. In the second row group the positions into pairs of offsets \((3,4),(2,5),(1,6),(0,7)\). **Each of the twelve possible pairs of groups receives at least one common prime assignment, at every height and for every choice of ties.** In particular \(a\) has at least twelve distinct prime divisors.

Let \(G\) be the product of the full prime powers assigned to a specified pair of groups. In the pattern with columns \(3,5,7,8\), the height exclusion \(a>10^{136}\) gives the following strict lower bounds on \(G\).

| Column-three term | \((3,4)\) | \((2,5)\) | \((1,6)\) | \((0,7)\) |
|---|---:|---:|---:|---:|
| \(n\) | 37 | 18 | 52 | 100 |
| \(n-1\) | 408 | 169 | 410 | 550 |
| \(n-2\) | 38 | 21 | 63 | 138 |

The twelve cells concern the two displayed columns alone. The finite height exclusion enters only when specializing the table to the four-column pattern. [Verifier for the bounds](Erdos849ThreeEightCells.py) · [Five-row pattern heights](Erdos849PatternHeights.md)

## The denominator of a rational function

Set \(X=n-1\), with cubic roots \(S=(-1,0,1)\), and \(Y=(m-3)(m-4)\), with quartic roots \(R=(0,2,6,12)\). Then \(\prod_{s\in S}(X-s)=6a\) and \(\prod_{r\in R}(Y-r)=8!a\). In particular each \(Y-r\) equals the product of the two actual numerator terms in one group. Choose \(s,r\) and write \(y=Y-r\).

In a block of length \(k\), each term divided by its assigned powers has cofactor dividing \(\operatorname{lcm}(1,\ldots,k)\). Indeed for a prime with maximum term valuation \(V\), the number \(N_h\) of multiples of \(p^h\) in the block is either \(\lfloor k/p^h\rfloor\) or that number plus one. There are no factorial levels beyond \(V\), since \(p^{V+1}>k\). The valuation of the chosen term's cofactor is \(\sum_{h=1}^V(1+\lfloor k/p^h\rfloor-N_h)\). Every summand is zero or one, and is zero when \(p^h>k\). The other terms have valuation at most \(\lfloor\log_p k\rfloor\) because two multiples of a larger power cannot fit in the block. The argument also works for primes absent from \(a\). All cofactors in the whole row multiply to \(k!\).

The cofactor in the column-three term divides 6. In a column-eight pair the product of its cofactors divides \(L_r\), respectively \(840,2520,840,840\). The two terms have odd difference, so at most one is even. Both can be divisible by 3 only in the pair with difference three, where the two 3-parts together divide the 3-part of \(8!\), namely 9. The total contributions of 5 and 7 already divide \(8!\) to their first powers.

The product of the assigned powers in \(X-s\) and \(Y-r\), counting both groups, divides \(aG\): only the common assignments were counted twice. Consequently \(GZ\) is integral, where
\[
 Z=\frac{6L_r a}{(X-s)y}
   =\frac{L_r\prod_{v\in S,\ v\ne s}(X-v)}{y}.
\]

## An integer polynomial small at the real point

The verifier constructs polynomials \(F(X,y,Z)\) with integer coefficients and \(Z\)-degree \(c\). Its working ring is the free cubic algebra over \(\mathbb Q[y,y^{-1}]\) with \(X^3=X+\prod_{q\in R}(y+r-q)/6720\). For successive powers of \(Z\) it reduces using this identity, then subtracts the terms \(X^i y^j\) with \(j\ge0\), recording the polynomial expression. It reduces against previously found expressions in descending order of \(4i+3j\), with \(0\le i<3\), until its leading weight is new. Clearing denominators yields an integer polynomial. This construction only chooses candidates: the exact checks below recompute the characteristic polynomial from the recorded integer expression.

Multiplication by \(F\) in the basis \(1,X,X^2\) has characteristic polynomial \(T^3+c_1(y)T^2+c_2(y)T+c_3(y)\), satisfied by the actual \(F\). Every nonzero term of the three coefficients is a negative power of \(y\). As \(Y\) is the largest of the four factors in its product, \(y\ge B=\lfloor(8!\,10^H)^{1/4}\rfloor-r\) when \(a\ge10^H\). Write \(\|f\|_B=\sum_j|f_j|B^j\). For \(c_3\) the magnitude of its leading term at \(B\) exceeds the sum of the remaining magnitudes, so \(c_3(y)\ne0\) for all \(y\ge B\). In particular \(F\ne0\).

If \(\sum_{t=1}^3\|c_t\|_B g^{ct}<1\), division of the characteristic equation by \(F^3\) shows \(|F|<g^{-c}\). Since \(G^c F\) is a nonzero integer, \(G>g\). The displayed table uses \(H=136\), searching the polynomial degrees through twelve. All calculations use rational arithmetic.

## Excluding an empty cell below the quantitative bounds

The published enumeration through \(10^{60}\) includes no admissible collision in columns 3 and 8. It remains to start the calculation at \(H=60\). For each cell choose the recorded function of degree five. If \(G=1\), then \(F\) itself is a nonzero integer. Choose an integer \(U>0\) with \(\sum_{t=1}^3\|c_t\|_B/U^t<1\). This implies \(|F|<U\). Here are the respective bounds \(U-1\) for its absolute value. [Blokhuis, Brouwer and de Weger, Theorem 2.2](https://arxiv.org/pdf/1707.06893)

| Column-three term | \((3,4)\) | \((2,5)\) | \((1,6)\) | \((0,7)\) |
|---|---:|---:|---:|---:|
| \(n\) | 7,506,604 | 396,682,759 | 2,068,278 | 1,620,265 |
| \(n-1\) | 153,756 | 6,356,150 | 27,425 | 24,810 |
| \(n-2\) | 12,707,177 | 418,189,618 | 1,533,710 | 947,515 |

For each prime \(11\le p\le191\), list all \(Y=(m-3)(m-4)\) over \(\mathbb F_p\), then all \(X\) with \(6720(X^3-X)=\prod_{q\in R}(Y-q)\). If \(y\ne0\), compute \(Z\) by its cubic expression. If \(y=0,\ X\ne s\), use the equal expression \(L_r\prod_{q\ne r}(Y-q)/(6720(X-s))\). If \(y=0,\ X=s\), no integral \(Z\) can reduce there, since \(yZ=L_r\prod_{v\ne s}(X-v)\) has nonzero right side in this field. Thus evaluating \(F\) on the retained points gives an exhaustive image for a putatively integral \(F\).

The program checks every nonzero integer in each displayed signed interval against these residue images. None survives in any of the twelve cases. The interval checker repeats prime-periodic bit masks in consecutive blocks, checks its alignment against direct enumeration on both signs, and recovers the residues of the common value one from rows 3 and 8 as a positive image control. Run both Python scripts with assertions enabled. [All-height sieve](Erdos849ThreeEightCellsSieve.py)
