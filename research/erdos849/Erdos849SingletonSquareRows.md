# Single numerator terms in five binomial collisions

Suppose \(\binom mk=\binom nh\), with \(m\ge2k\) and \(n\ge2h\). In each row of this table, **none** of the \(k\) integers \(m,m-1,\ldots,m-k+1\) can have squarefree part \(D\). These are all-height exclusions for individual terms.

| Odd column \(k\) | Even column \(h\) | Excluded squarefree part \(D\) |
|---:|---:|---:|
| 3 | 8 | 105 |
| 5 | 8 | 21 |
| 7 | 8 | 2 |
| 5 | 6 | 6 |
| 7 | 6 | 7 |

In the four-column pattern \((3,5,7,8)\) these exclude one square class in each odd column. In \((5,6,7,8)\) the fifth-column block avoids both 6 and 21, and the seventh-column block avoids both 2 and 7. Over \(\mathbb Q(\sqrt{14})\) this says that no fifth-column term is 6 times a square and no seventh-column term is 7 times a square: the two rational lifts of class 6 are 6 and \(14\cdot6\sim21\), those of class 7 are 7 and \(14\cdot7\sim2\). An earlier result on even subsets does not on its own exclude an individual term. The proof below uses the square coordinate from the even-column quotient and exact integer calculations. [Verifier](Erdos849SingletonSquareRows.py)

## Matching square polynomials

Write \((x)_k=x(x-1)\cdots(x-k+1)\). Suppose \(m=D u^2+r\) with \(0\le r<k\), \(u\ge1\). Let \(b=k!/\gcd(k!,h!)\), \(c=256b^2 h!/k!\), and

\[
  A(u)=c(Du^2+r)_k,\quad T=2n-h+1,\quad Y=T^2,
  \quad H_h(Y)=\prod_{s=1,3,\ldots,h-1}(Y-s^2).
\]

The binomial equation is exactly \(A=\lambda H_h(Y)\) with \(\lambda=b^2\) for \(h=8\) or \(4b^2\) for \(h=6\). The identities

\[
\begin{aligned}
 H_8(Y)&=(Y^2-42Y+105)^2-4096Y,\\
 4H_6(T^2)&=(2T^3-35T)^2-189T^2-900
\end{aligned}
\]

produce a positive integer \(V\) with \(V^2=A+eY+f\). Here \((V,e,f)=(b(Y^2-42Y+105),4096b^2,0)\) if \(h=8\), or \((b(2T^3-35T),189b^2,900b^2)\) if \(h=6\). Positivity follows from \(n\ge2h\).

The choice \(D=\operatorname{sf}(k!h!)\) makes the leading coefficient of \(A\) a rational square because \(k\) is odd. For each listed pair and each offset, the verifier checks that its positive square root \(a_0\) is an integer. It constructs the polynomial \(Q(u)\) of degree \(k\), with leading coefficient \(a_0\), by matching the coefficients of \(Q^2\) to those of \(A\) through degree \(k\). Each of the \(k\) successive coefficients is obtained by division by \(2a_0\). In every case the resulting coefficients are integers. Set \(R=Q^2-A\), so \(\deg R\le k-1\).

For \(U=20000\), write \(B\) for a positive integer satisfying \(B^{h/2}>c(D+k)^k\), obtained by doubling from 1. Since \(Y>(h-1)^2\),

\[
   (Y-(h-1)^2)^{h/2}\le H_h(Y)=A/\lambda\le c(D+k)^k u^{2k}.
\]

As \(2k/(h/2)\le k-1\) for the listed pairs, \(Y\le((h-1)^2+B)u^{k-1}\). The verifier checks both integer inequalities

\[
  2\lVert Q-a_0u^k\rVert_1<a_0U,\qquad
  2\big(e((h-1)^2+B)+f+\lVert R\rVert_1\big)<a_0U,
\]

where the norm is the sum of absolute polynomial coefficients. For \(u\ge U\) the first inequality gives \(Q(u)>a_0u^k/2\). The second gives

\[
  |V-Q(u)|=\frac{|eY+f-R(u)|}{V+Q(u)}<1.
\]

Integrality forces equality. Thus \(Y=(R(u)-f)/e\), and the polynomial

\[
   P(u)=\lambda\prod_{s=1,3,\ldots,h-1}\bigl(R(u)-f-e s^2\bigr)-e^{h/2} A(u)
\]

must vanish. For every offset the verifier expands \(P(U+v)\) in \(v\) by the binomial theorem. Its coefficients are all strictly positive or all strictly negative, excluding every real \(v\ge0\). This step is independent of any previous finite binomial search.

## The remaining finite intervals

For each of the 27 offsets the program tests every \(1\le u<20000\). It evaluates \(a=\binom{D u^2+r}{k}\) exactly for admissible rows. If \(a\ge\binom{2h}{h}\), it computes \(z=\lfloor(h!a)^{1/h}\rfloor\) by integer Newton iteration and checks the finitely many admissible integers between \(z\) and \(z+h\). This includes every possible row since \((n-h+1)^h\le h!a\le n^h\). There are no matches. Run `python Erdos849SingletonSquareRows.py` with assertions enabled to reproduce the result.

An independent replay reconstructs the polynomial from an integer square root, certifies the identities by interpolation and checks the polynomial signs by forward differences. Eight modular tests left 7,138 of the 539,949 admissible finite candidates for exact binary search. None matched. [Independent audit](Erdos849SingletonSquareAudit.py)
