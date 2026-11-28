# Square classes within individual Pascal numerator blocks

In a common value of columns **5, 6, 7 and 8**, take any one column \(k\) and write its row as \(n\). No nonempty even subset of \(n,n-1,\ldots,n-k+1\) has product equal to a square or to 14 times a square. This holds at every height. Equivalently, the \(k-1\) ratios \((n-s)/n\), \(1\le s<k\), represent independent square classes over \(\mathbb Q(\sqrt{14})\). Adjoining their square roots to that field gives degree exactly \(2^{k-1}\). In particular, every two different numerator terms have different square classes over that field. For the sixth and eighth columns the same conclusion requires only the pair \((6,8)\).

For the pattern **3, 5, 7 and 8**, the analogous independence over \(\mathbb Q\) holds in every numerator block. An elementary argument below proves the rational assertion for every block of eight consecutive positive integers ending at \(n\ge56\), independently of binomial representations. The second pattern's quadratic assertion uses the identity supplied by columns 6 and 8.

## From small squarefree parts to a finite check

Let \(H=3{,}209{,}464\). For each \(k=3,5,6,7\), suppose \(a\le10^H\) is common to proper columns \(k\) and 8. In **each** of the two numerator blocks, at most one term has squarefree part dividing 210. The following calculation tests each pair by itself. No other column is required in this range.

Suppose two terms at offsets \(i<j\) have squarefree parts dividing 210. Their product is \(Dw^2\) for some squarefree \(D\mid210\). For \(D=1\) the ordinary square-product result in the next section bounds the row by 55 (a block of length less than eight embeds in the eight-term block if its endpoint is at least eight). The verifier directly checks all admissible rows up to 55, including smaller endpoints. For the other fifteen \(D\) set \(g=j-i\), \(x=2n-i-j\), \(y=2w\). Then

\[
       x^2-Dy^2=g^2,\qquad n=(x+i+j)/2.
\]

Take a positive unit \(U+V\sqrt D>1\) of norm one with \(U,V>0\). Its inverse keeps \(x\) positive and decreases \(y>0\) while the resulting \(Uy-Vx\) stays nonnegative. Indeed \(x>\sqrt D\,y\) and \(U-V\sqrt D<1\). The next ordinate is negative exactly when \(y<Vg\), by squaring and using the norm. Thus all nonnegative solutions arise by forward iteration from \(0\le y<Vg\); the code enumerates this small seed interval directly. At index \(t\), \(x\ge U^t\ge2^{bt}\) with \(b=\lfloor\log_2 U\rfloor\). If the host column is \(h\), for the large indices in question each numerator term is at least \(2^{bt-2}\). The verifier stops once

\[
       3\bigl(h(bt-2)-\operatorname{bitlength}(h!)\bigr)\ge10H,
\]

which forces \(a>10^H\) since \(2^{10}>10^3\). For every sieve prime \(p\), the unit iteration is periodic modulo \(p\). A possible collision must put the coefficient of the row \((x+i+j)/2\bmod p\) in the other column's residue image. The sieve intersects the allowed index sets, reconstructs every survivor, checks the parity of the reconstructed coordinates, and tests the exact binomial equality with the other column's proper half-row condition. The mask routine can stop early, which leaves more indices for direct testing. [Pell sieve implementation](Erdos849WiderOdd37.py) · [Control and proof for the index sieve](Erdos849WiderOdd37.md)

| Host | Other column | Seed-offset orbits, all \(D>1\) | Exact index checks | Largest index checked | Orbits / checks for \(D=14\) |
|---:|---:|---:|---:|---:|---:|
| 3 | 8 | 49 | 50 | 1 | 3 / 3 |
| 8 | 3 | 542 | 518 | 2 | 34 / 32 |
| 5 | 8 | 180 | 174 | 2 | 10 / 10 |
| 8 | 5 | 542 | 528 | 2 | 34 / 34 |
| 6 | 8 | 277 | 263 | 2 | 17 / 16 |
| 8 | 6 | 542 | 513 | 2 | 34 / 33 |
| 7 | 8 | 399 | 377 | 2 | 25 / 23 |
| 8 | 7 | 542 | 513 | 2 | 34 / 32 |

There are no admissible collisions among the tested rows. In particular for these finite ranges, every nonempty even selection contains a term whose squarefree part has a prime \(p>7\). Such a prime divides no other term of the host block. Its odd valuation excludes a square even over \(\mathbb Q(\sqrt2,\sqrt3,\sqrt5,\sqrt7)\): this field is unramified at \(p>7\), so the odd valuation persists.

## The large-height quadratic conclusion

For \(a\ge10^H\) the explicit four-column Runge bound for \((5,6,7,8)\) excludes a square for every nonempty selection having even size in each row. Denote the selection of the complete sixth and eighth columns by \(B\). Its product is

\[
      (6!a)(8!a)=14(2\cdot6!a)^2.
\]

Consider a nonempty even selection \(S\) within one row. Both \(S\) and its symmetric difference \(S\mathbin\triangle B\) with \(B\) are nonempty and have even size in every row. Their square classes differ by 14, so neither the class 1 nor the class 14 can be the class of the product of \(S\). These are exactly the positive rational classes that become squares in \(\mathbb Q(\sqrt{14})\): expanding \((u+v\sqrt{14})^2\in\mathbb Q\) gives \(uv=0\). For the pair \((6,8)\) the same argument uses its own Runge certificate with multiplier 4, which gives exponent 31,184. This overlaps the finite range for both host rows. [Explicit height proof](Erdos849HigherSquare.txt) · [Height verifier](Erdos849HigherSquare.py)

Subsets of the ratios \((n-s)/n\) correspond bijectively in square classes to even subsets of the numerator block: include the term \(n\) precisely when the number of other selected terms is odd. This proves the independence and the stated field degrees.

For the pair \((6,8)\), let \(K=\mathbb Q(\sqrt{14})\) and let \(L_6,L_8\) be the two ratio fields just constructed over \(K\). At every height their intersection contains the nontrivial quadratic extension \(K(\sqrt{5a})\). Indeed the products of the entire even blocks represent square classes \(6!a=12^2\cdot5a\) and \(8!a=24^2\cdot70a\), equal over \(K\), and within-row independence proves this class nontrivial. For \(a\ge10^{31184}\) the intersection is exactly \(K(\sqrt{5a})\). The joint even-selector space has dimension \(5+7=12\) and embeds in the rational square classes by the pair's Runge bound. On passing to \(K\) its kernel has precisely two elements: the empty selection and the full two blocks, since the only rational classes lost are 1 and 14. Hence \([L_6L_8:K]=2^{11}\). The individual degrees are \(2^5,2^7\); the intersection of these Galois extensions therefore has degree two.

## A sharp rational result for every eight consecutive integers

For every \(n\ge56\), **no nonempty even subset of \(n-7,\ldots,n\) has square product**. At \(n=55\) the product of \(54,50,49,48\) is a square, so the endpoint is sharp. This result also gives rational square-class independence in each individual block of any of the admissible pairs \((3,8),(5,8),(6,8),(7,8)\): the finite direct check excludes every pair occurrence whose selected host has \(n<56\).

Fix one of the 127 nonempty even selections \(S\subseteq\{0,\ldots,7\}\), write \(|S|=2h\) and \(F(X)=\prod_{s\in S}(X-s)\). Obtain the monic rational polynomial \(R(X)\) of degree \(h\) by matching the coefficients of \(R^2\) and \(F\) down through degree \(h\). Each successive coefficient of \(R\) is uniquely determined by division by two. The remainder \(T=F-R^2\) has degree \(<h\) and is nonzero because the roots of \(F\) are distinct. Let \(D\) be the common denominator of \(R\).

For \(n\ge16\) one has \(\sqrt{F(n)}\ge(n/2)^h\). For \(n>2\sum_{i<h}|[X^i]R|\), the monic leading term gives \(R(n)>0\). For such \(n\),

\[
   |\sqrt{F(n)}-R(n)|\le\frac{2^h\|T\|_1}{n}.
\]

If \(n>D2^h\|T\|_1\), this is strictly below \(1/D\). If \(\sqrt{F(n)}\) were an integer then it would have to equal \(R(n)\), forcing \(T(n)=0\). A positive root of \(T\) is at most \(1+\sum_{i<\deg T}|[X^i]T|/|\operatorname{lc}(T)|\). The verifier computes these bounds for each selection by exact rational arithmetic. The largest cutoff is 192,542. It tests all integers from eight up to the respective cutoff by integer square root and finds that 55 is the largest exception. A separate audit uses translated polynomials with cutoffs at most 512. [Exact verifier for both results](Erdos849FourteenPairs.py) · [Independent audit](Erdos849FourteenPairsAudit.py)

Lean checks the factorial identity, the criterion for rational numbers to become squares after adjoining the square root of 14, and the square identity for the symmetric difference of two selections. The height estimates and Pell orbit checks are supplied separately. [Lean arithmetic lemmas](Erdos849FourteenSquareClass.lean)
