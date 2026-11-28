# Three equal Pascal entries at prescribed translations

Write three distinct admissible left-half positions, in increasing order of row, as
\[
 (n,k),\quad(n+h,k-v),\quad(n+H,k-V).
\]
Here \(0<h<H\) and \(0<v<V\): increasing the row strictly increases a fixed positive column, and the coefficients increase along the left half. Column one is allowed. The following all-height classifications use an ordinary exact-integer verifier.

| Maximum total row span \(H\) | Maximum total column span \(V\) | All triples |
|---:|---:|---|
| 24 | 24 | none |
| 64 | 4 | \(3003=\binom{14}6=\binom{15}5=\binom{78}2\) |
| 110 | 2 | \(120=\binom{10}3=\binom{16}2=\binom{120}1\) |

There is also a uniform algebraic result. **For every fixed choice of the four positive shifts, the two factorial-ratio equations have no common component even over \(\mathbb C\).** There are at most \((h+v)(H+V)\) complex starting positions satisfying both, counting distinct positions. Each fixed translation pattern can therefore be solved effectively by univariate resultants, independently of any assumption on the number of occurrences of the value.

## Elimination at infinity

Factorial cancellation gives the polynomial equation
\[
 P_{h,v}(n,k)=\prod_{i=1}^h(n+i)\prod_{i=0}^{v-1}(k-i)
                 -\prod_{i=1}^{h+v}(n-k+i)=0
\]
for the first translation; the second equation uses \(H,V\). The homogeneous leading part is \(n^h k^v-(n-k)^{h+v}\). There is no point of the projective curve at infinity with \(n=0\). Write \(\rho=k/n\) at infinity. A leading root satisfies \(\rho^v=(1-\rho)^{h+v}\); it differs from zero and one. It is simple since the relative derivative is
\[
 \frac{v}{\rho}+\frac{h+v}{1-\rho}
 =\frac{v+h\rho}{\rho(1-\rho)} .
\]
The sole candidate for a zero numerator, \(-v/h\), fails the leading equation in absolute value because \((v/h)^v<(1+v/h)^{h+v}\).

Use \(1/n\) as local coordinate. The unique branch has \(k=\rho n+c_{h,v}+O(1/n)\). Equating the next coefficient in the two products gives
\[
 \frac{h(h+1)}2+\frac{vc_{h,v}-v(v-1)/2}{\rho}
 =\frac{(h+v)(h+v+1)/2-(h+v)c_{h,v}}{1-\rho},
\]
or equivalently
\[
 2c_{h,v}=v+h\rho+(2\rho-1)+\frac{h\rho(1-\rho)}{v+h\rho}.
\]
If \((H,V)=\lambda(h,v)\), the difference of the doubled intercepts is \((\lambda-1)(v+h\rho)\ne0\). For a noncollinear pair, eliminating in the two leading equations gives \(\rho^{|hV-Hv|}=(1-\rho)^{|hV-Hv|}=1\). The intersection of the unit circles about zero and one gives only \(\rho=(1\pm i\sqrt3)/2\); now \(\rho(1-\rho)=1\). Choose the positive imaginary part, the other direction being conjugate. The imaginary part of \(1/(v/h+\rho)\) lies strictly between \(-\operatorname{Im}\rho\) and zero, since \(|v/h+\rho|>|\rho|=1\). The increase from \(h\operatorname{Im}\rho\) to \(H\operatorname{Im}\rho\) is at least \(\operatorname{Im}\rho\), so \(c_{h,v}\ne c_{H,V}\).

Thus the two smooth branches have different tangent lines at every common point at infinity. A common projective component would meet the line at infinity and would require the same branch there. Bézout gives the claimed bound. For literal elimination the coefficient of \(k^{h+v}\) in the first equation is a nonzero constant, and likewise for the second. Their resultant in \(k\) is a nonzero polynomial in \(n\) containing every affine solution among its roots. Roots caused by cancellation at nonadmissible positions can simply be discarded.

## A smaller finite search for the table

Prescribe row and column limits \(R,C\), and let \(G=\max(R,C)\). Along a line with positive row step and negative column step the successive binomial ratios strictly decrease. Hence a collinear triple is impossible. In the noncollinear case the integer determinant \(hV-Hv\) has absolute value at least one. The factorial-ratio estimate in the [prime-window proof](Erdos849PrimeWindow.md) then gives \(n<30G^3\). This use of that estimate needs only \(h,H,v,V\le G\); its original prime-gap hypothesis was used to establish these inequalities. In particular this is a row cutoff, not a truncation by the size of the common value.

Here is the refinement used for \(R\ge C\). Put \(u=n-k,\ L=\log(n/u),\ M=\log(u/k)\), and \(e_{h,v}=hL-vM\). For \(n\ge30G^2\) the prime-window estimate gives \(0<e_{h,v}\le10G^2/n<1\), also for \((H,V)\). The [row-gap inequality](Erdos849LindBand.md) yields \(n/k\le H+2\). Thus \(H k/n\le HL\le Cb+1\), where \(b=\lceil\log_2(R+2)\rceil\). The exact logarithm of the product identity is
\[
 e_{h,v}=\sum_{i=1}^h\left[\log(1+i/u)-\log(1+i/n)\right]
 +\sum_{i=h+1}^{h+v}\log(1+i/u)-\sum_{i=0}^{v-1}\log(1-i/k).
\]
The first sum is at most \(h(h+1)k/(2un)\le(R+1)(Cb+1)/n\). The second is at most \(4RC/n\). For the last sum, \(v\le k/2\) and \(v^2/k\le3RC/n\): when \(k\ge n/3\) this follows from \(v\le C\); when \(k\le n/3\), factorial cancellation gives \(v\log(u/k)\le h\log(n/u)\le hk/u\), hence \(v\le3hk/n\). Thus the final sum with its minus sign is at most \(v^2/k\). With \(E=(R+1)(Cb+1)+7RC\) we get \(0<e_{h,v},e_{H,V}\le E/n\). Since \(\max(L,M)>1/3\) and
\[
 L(hV-Hv)=Ve_{h,v}-v e_{H,V},\qquad
 M(hV-Hv)=He_{h,v}-h e_{H,V},
\]
we have \(n<3RE\). Together the two bounds permit the cutoff \(\min(30G^3,\max(30G^2,3RE))\).

For fixed \(n,h,v\), let \(\alpha\in(0,1/2)\) solve \(\alpha^v=(1-\alpha)^{h+v}\). A tie forces
\[
                       \alpha n-h\ \le k\le\ \alpha n+h+v .
\]
For the lower bound use \((n+h)^h k^v\ge(n-k)^{h+v}\). If \(k<\alpha n-h\), then \(k<\alpha(n+h)\) and \(n-k>(1-\alpha)(n+h)\), contradicting that inequality. For the upper bound use \(n^h(k-v+1)^v\le(n-k+h+v)^{h+v}\) and compare to \(\alpha n\) and \((1-\alpha)n\).

The [verifier](Erdos849RowTriples.cjs) brackets \(\alpha\) between consecutive multiples of \(2^{-24}\) by exact integer powers. It enumerates every candidate in the resulting integer interval and uses product residues modulo 251 and 65521 before checking the exact product equality. A table of modular jump distances skips only positions that fail modulo 251. The retained shifts are grouped by their identical source \((n,k)\). Run \(\texttt{node Erdos849RowTriples.cjs}\) to reproduce the three rows of the table.
