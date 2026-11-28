# How often can a triangular or fourth-column value occur in five rows?

Let \(A_H^{\{2,4\}}(x)\) count the values up to \(x\) in at least \(H\) distinct proper Pascal columns, at least one being 2 or 4. Proper means \(2\le k\le n/2\). For every fixed \(H\ge2\),

\[
 \log(1+A_H^{\{2,4\}}(x))\ll_H
 (\log x)^{3/(H+2)}(\log\log x)^{(H-1)/(H+2)}.
\]

For five or more rows, \(H=4\), so the upper bound is \(O(\sqrt{\log x\,\log\log x})\). With the quantitative Mordell theorem of Yu, Yuan and Zhou the bound improves to \(O((\log x)^{2/5}(\log\log x)^{6/5})\), as detailed below. For unrestricted \(A_H(x)\), the limsup constant in the simultaneous-column estimate improves from \(\tfrac12(\log5)^{(H-1)/4}\) to \(\tfrac13(\log5)^{(H-1)/4}\). These estimates allow infinitely many witnesses. [Definition and simultaneous-column estimate](Erdos849MultiplicityDensity.md)

## Counting intersections with a single deeper column

For \(k=2,4\) and \(d\ge5\), let \(J(k,d)\) count *all* common admissible values in columns \(k,d\), over all heights. Uniformly in \(d\),

\[
                  \log(1+J(k,d))\ll d^3\log d .
\]

Put \(c=8\) for \(k=2\) and \(c=24\) for \(k=4\). For a shared value \(a=\binom nd\), \(1+ca\) is a square by the identities for columns 2 and 4. Set \(F(X)=(X)_d+d!/c\), a monic integer polynomial with \(F(n)=(d!/c)(1+ca)\). It has distinct roots. Indeed the largest absolute critical value of \(\binom Xd\) strictly decreases with \(d\), and for \(d=4\) it is \(1/24\). Every complex root of \(F\) has absolute value at most \(2d\), since at larger modulus every factor of \((X)_d\) exceeds \(d\) in absolute value. [Critical values and square identities](Erdos849FixedColumnMethods.txt)

Choose three distinct roots \(\alpha_1,\alpha_2,\alpha_3\). For each root \(\alpha\) work first in its own number field \(K=\mathbb Q(\alpha)\), of degree \(m\le d\). Let \(S\) consist of the infinite places and the prime ideals dividing \((d!/c)F'(\alpha)\). If a prime ideal outside \(S\) divides \(n-\alpha\), then \(F(n)/(n-\alpha)\) reduces to \(F'(\alpha)\) at that prime, and is a unit there. As \(F(n)\) is a square times \(d!/c\), every valuation of \(n-\alpha\) outside \(S\) is even. Admissibility gives \(F(n)>0\), so all the elements considered are nonzero.

The number of possible classes of \(n-\alpha\) in \(K^*/K^{*2}\) is at most \(2^{|S|+\operatorname{rk}_2\mathrm{Cl}(K)}\). This follows from the ideal-class exact sequence and the \(S\)-unit theorem, or directly from Lemma 1 of Evertse and Silverman. The logarithm of this bound is \(O(d^2\log d)\), uniformly in the root. In fact \(|F'(\alpha)|\le (4d)^{d-1}\) in each embedding, so the logarithm of the absolute norm of \((d!/c)F'(\alpha)\) is \(O(d^2\log d)\). The field discriminant divides the discriminant of the minimal polynomial of \(\alpha\), hence \(\log|\Delta_K|\le m(m-1)\log(4d)\). Minkowski gives an integral ideal of norm \(\le 2^m\sqrt{|\Delta_K|}\) in each ideal class. For \(B\ge1\), the number of ideals of norm \(\le B\) is at most \(B^2\zeta_K(2)\le B^2\zeta(2)^m\), by the Euler product. Thus \(\log|\mathrm{Cl}(K)|\ll d^2\log d\) as well. [Evertse and Silverman, Lemma 1](https://ir.cwi.nl/pub/1788/1788D.pdf)

Fix one triple of these square classes with representatives \(\beta_i\). The field
\[
 E=\mathbb Q(\alpha_1,\alpha_2,\alpha_3,\sqrt{\beta_1},\sqrt{\beta_2},\sqrt{\beta_3})
\]
has degree \(M\le8d^3\). For every solution in this triple, it contains algebraic integers \(w_i\) with \(w_i^2=n-\alpha_i\). Include in \(T\) the infinite places of \(E\) and the prime divisors of the three differences \(\alpha_i-\alpha_j\). The product of their absolute norms is at most \((4d)^{3M}\). Hence \(|T|\ll M\log d\). The identity \((w_i-w_j)(w_i+w_j)=\alpha_j-\alpha_i\) shows that all six factors are \(T\)-units. Consequently
\[
 U=\frac{w_1-w_2}{w_1-w_3},\qquad 1-U=\frac{w_2-w_3}{w_1-w_3}
\]
are both \(T\)-units. The two-variable unit equation gives at most \(3\cdot7^{M+2|T|}\) choices for \(U\). This form of Evertse's bound is stated in the proof of Lemma 3 by Evertse and Silverman. [Unit-equation bound, p. 240](https://ir.cwi.nl/pub/1788/1788D.pdf)

Each \(U\) determines at most one \(n\). Put \(q=w_1-w_3\), \(A=\alpha_2-\alpha_1\) and \(B=\alpha_3-\alpha_1\). Subtraction of squares gives
\[
 q^2=\frac{A-UB}{U(1-U)},\qquad
 n=\alpha_1+\frac{(B+q^2)^2}{4q^2}.
\]
Distinct roots give \(q\ne0\) and \(U\notin\{0,1\}\). Multiplying the number of triples of square classes by the bound for \(U\) proves the asserted count.

## Combining short and long columns

Write \(L=\log x\) and take \(D=\lfloor(L/\log L)^{1/(H+2)}\rfloor\) for sufficiently large \(x\). Choose a representing tuple of \(H\) proper columns containing the distinguished column 2 or 4. If any other column is at most \(D\), summing the preceding pair estimate costs at most \(\exp(O(D^3\log D))\). The finitely many pairs from \(\{2,3,4\}\) have finite intersections by the existing classifications. Otherwise the product of the \(H\) column indices is at least \(2(D+1)^{H-1}\). The simultaneous-column integral-point estimate bounds this contribution by \(L^{O_H(1)}\exp(L/[2(D+1)^{H-1}])\). Substituting \(D\) gives the claim.

For the unrestricted limsup, these values contribute a logarithm \(o(L/(\log L)^{(H-1)/4})\). In the remaining tuples the smallest column is at least three, so the product bound in the large-column part of the unrestricted argument improves to \(3(D+1)^{H-1}\) with that argument's original cutoff. This proves the factor \(1/3\). [Uniform integral-point estimate and unrestricted cutoff](Erdos849MultiplicityDensity.md)

## Sharper bound from a 2026 preprint

Theorem 1.7 of Yu, Yuan and Zhou's February 2026 preprint gives a stronger estimate over the field \(K=\mathbb Q(\sqrt{d!/c})\), of degree at most two. The same monic \(F\) has genus \(\lfloor(d-1)/2\rfloor\ge2\) in the equation \(Y^2=F(X)\), and each admissible \(n\) gives a point over \(K\). The field discriminant has magnitude at most \(4d!\). The absolute norm of the polynomial discriminant is at most \((4d)^{2d(d-1)}\) by the root-difference bound. For both even and odd degrees, the exponents of these two discriminants in Theorem 1.7 are \(O(\log d)\), and the logarithm of the remaining factor is \(O((\log d)^2)\). Thus \(\log(1+J(k,d))\ll d^2(\log d)^2\). With \(D=\lfloor(L/(\log L)^2)^{1/(H+1)}\rfloor\) in the preceding split this gives
\[
 \log(1+A_H^{\{2,4\}}(x))\ll_H
 L^{2/(H+1)}(\log L)^{2(H-1)/(H+1)} .
\]
The first proof uses the classical unit-equation bound independently of this preprint. [Yu, Yuan and Zhou, Theorem 1.7](https://arxiv.org/html/2602.01820v1#S1.SS2)
