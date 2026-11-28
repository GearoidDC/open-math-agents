# Good reduction and rational-point counts for pairs of Pascal columns

For \(2\le r<d\), put \(A_k(X)=\prod_{i=0}^{k-1}(X-i)\), \(f_k=A_k/k!\), and let \(C_{r,d}\) be the smooth projective normalization of \(f_r(x)=f_d(y)\). The binomial pair curve is geometrically integral. Write \(g\) for its genus and \(N^0\) for the product of the rational primes of bad reduction of \(C_{r,d}\). Uniformly in the two columns,
\[
 2g\le (r-1)(d-1),\qquad \log N^0\ll d^3\log(2d).
\]
All constants implicit here are absolute and effective. When \(g\ge2\), a February 2026 preprint of Yu, Yuan and Zhou consequently gives
\[
 \log\!\big(1+\#C_{r,d}(\mathbb Q)\big)
 \ \ll\ 2^{8g^2}g^2\log(2g)\big(1+d^3\log(2d)\big)
 \ \le\ 2^{2(rd)^2}(rd)^{O(1)} .
\]
For the particular pair \(3,d\), its finite ramification gives \(g\le d-1\). Thus its rational-point count has logarithm at most \(2^{8(d-1)^2}d^{O(1)}\) when \(g\ge2\). This is a count, with no bound here on the sizes of the rational points. [Yu–Yuan–Zhou, Theorem 1.6](https://arxiv.org/html/2602.01820v1#S1.SS2) · [Geometric integrality of the binomial pair](Erdos849ReciprocalRunge.txt)

## A single integer containing every bad prime

For \(k=r,d\), form the nonzero integer polynomial
\[
  T_k(t)=\operatorname{Res}_X(A_k(X)-k!t,A'_k(X)).
\]
Let \(B(t)\) be the primitive squarefree part of \(T_rT_d\), chosen with positive leading coefficient. Write \(\operatorname{lc}\) for leading coefficient and take the discriminant of a linear polynomial to be one. Set
\[
 U_{r,d}=\left|d!\,\operatorname{lc}(B)\operatorname{disc}(B)
 \prod_{k\in\{r,d\}}\operatorname{lc}(T_k)\operatorname{disc}(A'_k)\right| .
\]
In particular the raw leading coefficient of \(T_k\) includes its content. \(A'_k\) has \(k-1\) distinct roots by Rolle's theorem applied in the gaps of \(A_k\); hence \(U_{r,d}\ne0\). The factors of \(B\) represent the union of the distinct finite branch values. Taking its squarefree part **after** multiplying the two resultants allows a common branch value in characteristic zero.

Take \(p\nmid U_{r,d}\) and form the fiber product of the two maps \(\mathbb P^1_{\mathbb Z_p}\to\mathbb P^1_{\mathbb Z_p}\) defined by the \(f_k\). Both maps are finite flat with unit leading coefficients because \(p>d\). Their fiber product is proper and flat over \(\mathbb Z_p\), and its generic fiber over \(\mathbb Q_p\) is a geometrically integral curve. It has no vertical component. Its normalization is finite because the rings are excellent. We show it is a smooth proper model of \(C_{r,d}\).

After a finite unramified extension large enough to split the reductions, all distinct critical points of either polynomial are disjoint integral sections within that polynomial. This follows from \(\operatorname{lc}(A'_k)=k\), its discriminant, and Hensel's lemma. The zeros of \(B\) likewise form disjoint sections. The primitive factorization of \(T_rT_d\), with a unit leading coefficient modulo \(p\), shows that these are precisely the distinct finite branch sections; no distinct generic branch values merge in the special fiber. For any point of the geometric special fiber at a finite base value, at least one map is smooth there unless both coordinates are critical. If one derivative is a unit the fiber product is smooth over the valuation ring at that point.

If both are critical, their lifted critical points have the same branch value \(\beta\). In a centered coordinate \(u\) about either section the corresponding map is
\[
 t-\beta=u^2 V(u),
\]
with \(V\) regular and invertible there: the derivative has a simple root and \(2\) is a unit. Adjoining a square root of \(V\) is étale. After this base change \(u\sqrt V\) is an étale coordinate near the section, since its derivative there is a unit. At infinity the same computation with \(u=1/X\) gives \(1/t=u^k V(u)\), with \(V(0)=k!\) a unit. Adjoining a \(k\)-th root of \(V\) is étale since \(p>k\).

It follows that each relevant fiber-product neighborhood is étale locally modeled on \(u^e=v^f\), with \((e,f)=(2,2)\) or \((r,d)\). Its normalization is smooth over the valuation ring. In detail, adjoining all required roots of unity by an unramified extension, the equation factors into \(\gcd(e,f)\) branches. On one branch put \(a=e/\gcd(e,f)\), \(b=f/\gcd(e,f)\), and absorb the root of unity by an invertible constant. Its local model ring is \(R[w^b,w^a]\subset R[w]\), with \(R\) the extended valuation ring. The coprimality of \(a,b\) gives the same fraction field and \(w\) is integral; \(R[w]\) is normal. The normalization is the disjoint union of these smooth branches. Finite normalization commutes with the étale coordinate changes and smoothness descends through them. This deals with intersections of branch loci as well as the point over infinity, and proves \(N^0\mid U_{r,d}\). [Stacks Project, Lemma 37.19.2](https://stacks.math.columbia.edu/tag/03GV)

For the magnitude bound use the coefficient \(\ell^1\)-norm. We have \(\|A_k\|_1=k!\) and \(\|A'_k\|_1\le k\,k!\). In the Sylvester determinant for \(T_k\) there are \(2k-1\) rows, and each entry, as a polynomial in \(t\), has norm at most \(2k\,k!\). Expansion gives
\[
 \log\|T_k\|_1\le \log((2k-1)!)+(2k-1)\log(2k\,k!)=O(d^2\log(2d)).
\]
It has degree \(k-1\) in \(t\) by the product of its values at the \(k-1\) roots of \(A'_k\). For an integer polynomial \(G\) its Mahler measure is at most \(\|G\|_1\); every primitive divisor \(D\) of \(G\) therefore has \(\|D\|_1\le2^{\deg D}\|G\|_1\), by multiplicativity of Mahler measure and the elementary-symmetric coefficient bounds. Hence \(\deg B<2d\) and \(\log\|B\|_1=O(d^2\log(2d))\). One more Sylvester determinant bounds \(\log|\operatorname{disc}B|=O(d^3\log(2d))\). The discriminants of the two derivatives have the smaller bound \(O(d^2\log(2d))\) by the same determinant estimate. This bounds \(\log U_{r,d}\) as asserted.

## Genus and the direct density consequence

The projection to the \(y\)-line has degree \(r\). Each of the \(r-1\) simple finite critical points of \(f_r\) contributes at most \(d\) to its ramification after base change along \(f_d\). In detail, over a root of \(f_d(y)-\beta\) of multiplicity \(m\), the local equation is \(u^2=v^m\) and contributes \(2-\gcd(2,m)\le1\). Above infinity the projection contributes \(r-\gcd(r,d)\) by the monomial parametrization. Riemann–Hurwitz gives
\[
 2g\le (r-1)(d-1)-\gcd(r,d)+1 .
\]
Yu–Yuan–Zhou, Theorem 1.6 over \(\mathbb Q\), states \(\#C(\mathbb Q)\le c_1(g,1)(N^0)^{c_2(g,1)}\), with \(\log c_1(g,1)\ll 2^{8g^2}g^2\log(2g)\) and \(c_2(g,1)\ll2^{8g^2}g^2\log(2g)\). The genus and bad-prime estimates give the stated rational-point bound. An admissible binomial solution has both row coordinates beyond the largest root of its polynomial. Both derivatives are positive there, so such a point lifts to the normalization.

For an application, let \(A_H(x)\) count shared values at most \(x\) with \(H\ge2\) proper column representations, and put \(E=\log\log x\). Take \(T=((E-c\log E)/(2\log 2))^{1/2}\), with a sufficiently large fixed \(c=c(H)\). For tuples whose two smallest indices have product \(rd\le T\), sum the pair bound over at most \(T^2\) pairs. Their log-count is \(o(\log x/E^{H/4})\). The pairs of genus less than two have a bounded number of admissible solutions by the separate low-genus classifications. For the remaining tuples, all \(H\) indices have product at least \((rd)^{H/2}>T^{H/2}\). The uniform determinant bound on the curve of simultaneous representations gives total count at most \((\log x)^{O_H(1)}x^{1/T^{H/2}}\). Thus
\[
 \limsup_{x\to\infty}
 \frac{(\log\log x)^{H/4}}{\log x}\log(1+A_H(x))
 \le (2\log 2)^{H/4}.
\]
This last estimate uses the preprint's general bad-reduction bound directly. The separate analysis via permutation modules sharpens the dependence on genus. [Determinant bound and the low-genus pairs](Erdos849MultiplicityDensity.md)

## Reflection quotients and the sharper density constant

For every pair with \(d\ge16\), there is a quotient \(D\) over \(\mathbb Q\) of genus \(h\ge2\) satisfying \(2h\le rd/2\). The map sends distinct admissible solutions to distinct rational points of \(D\). Write centered coordinates \(X=x-(r-1)/2,\ Y=y-(d-1)/2\). In these coordinates an even column polynomial is even and an odd column polynomial is odd. The following choices cover all pairs.

* For \(r=2\) use the original curve. Its genus is at least two for \(d\ge16\) by the pair genus classification above, and \(2g\le d-1<rd/2\).
* If \(r\ge3\) and at least one column is even, quotient by each even column's reflection separately, replacing its centered coordinate by its square. The model is again an equality of two polynomials of degrees \(u\le v\), with each even degree halved before sorting. The quotient is geometrically integral, and \(uv\le rd/2\). The genus upper bound already proved by projection and Riemann–Hurwitz applies verbatim, giving \(2h\le(u-1)(v-1)\le rd/2\).
* If both columns are odd, quotient by the simultaneous reflection \((X,Y)\mapsto(-X,-Y)\). This involution has at least one fixed point (the smooth affine origin) and at most \(1+\gcd(r,d)\), since the origin is the only affine possibility and the original normalization has exactly \(\gcd(r,d)\) points at infinity. If \(b\) denotes the number of geometric fixed points, Riemann–Hurwitz gives \(4h=2g+2-b\). In particular \(b\) is even, hence \(2h\le g\le rd/2\).

The even reflections preserve the common value. The simultaneous odd reflection reverses its sign. In both cases the quotient map has precisely the group orbits as geometric fibers. Each coordinate of an admissible point is strictly positive in the centered coordinates, so each orbit contains at most one admissible point.

For the genus lower bound, each odd column polynomial has simple critical points with distinct critical values. The polynomial of half degree obtained from an even column has the same property: reflected noncentral critical points give the degree-minus-one distinct simple critical points of this polynomial. Strict inequalities between absolute maxima in the successively inward gaps distinguish the critical values, apart from exactly the reflected pairs for even degrees. For a pair of resulting degrees \(2\le u\le v\), each critical value of the first map has at least \(v-2\) simple preimages under the second. Applying Riemann–Hurwitz to the degree-\(u\) projection, including its infinity contribution \(u-\gcd(u,v)\), shows that the genus \(q\) of this pair satisfies
\[
 2q\ge (u-1)(v-2)-u-\gcd(u,v)+2\ge(u-1)(v-4).
\]
For the even-reflection quotient, \(v\ge d/2\ge8\), so \(h=q\ge2\). For two odd columns apply this lower bound before quotienting: \(2g\ge(r-1)(d-4)\). Thus \(4h\ge(r-1)(d-4)+1-\gcd(r,d)\ge(r-1)(d-5)\ge8\). [Critical values of the centered polynomials](Erdos849ReciprocalRunge.txt)

All these quotient curves have good reduction at \(p\nmid U_{r,d}\). The reflections are defined over \(\mathbb Z_p\), preserve the original fiber product, and extend to its normalization by functoriality. The quotient of this smooth projective model by the chosen group of order at most four exists and is smooth over \(\mathbb Z_p\). To see local smoothness, pass to a complete strictly unramified valuation ring \(R\) with algebraically closed residue field. At a geometric special-fiber point the completed local ring is \(R[[z]]\). Its stabilizer \(H\) acts on the special-fiber tangent parameter by a character \(\chi\) with values in \(\{1,-1\}\), since every element has order at most two and \(p\) is odd. Lift these signs to \(R\). The average \(w=|H|^{-1}\sum_{\sigma\in H}\chi(\sigma)^{-1}\sigma(z)\) is again a parameter over \(R\), as its reduction has the same linear term as \(z\). It satisfies \(\sigma(w)=\chi(\sigma)w\). The invariant ring is therefore \(R[[w^e]]\), where \(e=|\chi(H)|\). This gives the quotient's completed local ring: completion at the image of a finite orbit splits the upstairs ring into the product over that orbit, and averaging makes invariants commute with flat base change. These local rings prove smoothness; the quotient is proper and has generic fiber \(D\). In particular its Jacobian has good reduction outside the primes already bounded.

Let \(J(r,d)\) count admissible common values for the pair. The permutation-module rank estimate for a genus-\(h\) Jacobian gives \(\operatorname{rk}\ll 2^{2h}(1+h)(1+\log U_{r,d})\). Applying Yu–Yuan–Zhou, Theorem 1.3, to \(D\), and using the finitely many fixed-pair finiteness results when \(d<16\), yields
\[
  \log(1+J(r,d))\ll 2^{rd/2}d^6 .
\]
For \(E=\log\log x\), choose \(T=2(E-(H+10)\log E)/\log 2\). The combined log-count for pairs \(rd\le T\) is \(O(\log T+2^{T/2}T^6)=o(\log x/E^{H/2})\). For the other tuples, the product of their \(H\) columns exceeds \(T^{H/2}\), so the simultaneous-column determinant estimate gives
\[
 \boxed{\displaystyle
 \limsup_{x\to\infty}
 \frac{(\log\log x)^{H/2}}{\log x}\log(1+A_H(x))
 \le \left(\frac{\log 2}{2}\right)^{H/2}.}
\]
[Permutation-module rank estimate](Erdos849TorsionDensity.md) · [Yu–Yuan–Zhou, preprint, Theorem 1.3](https://arxiv.org/html/2602.01820v1#S1) · [Simultaneous-column determinant estimate](Erdos849MultiplicityDensity.md)
