# The genus-twelve curve for columns five and seven

Put $X=n_5-2$, $Y=n_7-3$. Every admissible collision in columns 5 and 7 lies on the affine curve

$$
C:\quad 42X(X^2-1)(X^2-4)=Y(Y^2-1)(Y^2-4)(Y^2-9).
$$

Its smooth completion has genus twelve and one point at infinity $I$. The diagonal involution $\iota(X,Y)=(-X,-Y)$ has a genus-six quotient $D$. The full Jacobian is isogenous over $\mathbb Q$ to $J(D)\times A$, where the six-dimensional Prym $A$ is the identity component of the kernel of the norm to $J(D)$.

**Result.** The two factors are geometrically nonisogenous and each has geometric endomorphism ring $\mathbb Z$. Moreover $J(C)(\mathbb Q)$ and $J(D)(\mathbb Q)$ have trivial torsion. The curve $C$ admits no nonconstant map to a curve of genus one through five, even over $\overline{\mathbb Q}$. Its geometric automorphism group consists of the identity and $\iota$, so it admits no nonconstant Galois map to the projective line. These statements exclude several routes to applying effective integral-point theorems to this common pair. They do not determine its integral points. [Bilu's theorem for Galois maps](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/AB122815987867C6DD4F8BA5473C52FB/S0010437X97000225a.pdf/quantitative-siegels-theorem-for-galois-coverings.pdf)

## The quotient and its reductions

The original separated maps have disjoint finite branch sets, as checked by their critical-value resultants modulo 11. Their finite ramification contributions to the cover over the common value line are $7(5-1)$ and $5(7-1)$. At infinity there is one point of index $35$ because 5 and 7 are coprime. Riemann–Hurwitz gives $g(C)=12$. The two fixed points of $\iota$ are $(0,0)$ and $I$, so the same formula gives $g(D)=6$. The quotient is trigonal. Indeed $r=X/Y$, $s=Y^2$ satisfy the cubic

$$
42r(r^2s-1)(r^2s-4)=(s-1)(s-4)(s-9).
$$

These invariants generate the quotient field, since adjoining $Y$ recovers $X$. The function $r$ has three simple poles on $D$. Upstairs it has poles of order one at $(\pm1,0),(\pm2,0)$ and order two at $I$. The first four points pair under the involution and $I$ ramifies.

At 11 and 13 the finite branch polynomials are coprime modulo the prime, so the affine equation is smooth. At 5 its derivative in $X$ is a nonzero constant because $X(X^2-1)(X^2-4)=X^5-X\bmod 5$. At all three primes the completion is smooth at infinity. To see this, on the torus write $z=X^2/Y^3$, $w=X^5/Y^7$. This is a unimodular monomial substitution giving $X=z^{-7}w^3$, $Y=z^{-5}w^2$. After division by $Y^7$ the equation at $z=0$ is $42w=1$ with unit derivative. This chart adds the single point over infinity to the affine curve. Equivalently, it is the chart about the nonzero $X,Y$ torus in the closure in weighted projective space of weights $(7,5,1)$. The involution has order prime to these characteristics, hence its quotient also has good reduction.

For a simple point-count model of $D$, put $u=X^2$, $v=Y^2$. Squaring the equation gives

$$
42^2u(u-1)^2(u-4)^2=v(v-1)^2(v-4)^2(v-9)^2 .
$$

Away from simultaneous zeros this recovers the third invariant $XY$ by the original equation. Above simultaneous zeros with $u,v$ both nonzero there are two rational branches, distinguished by $XY=\pm\sqrt{uv}$, since the possible nonzero coordinates are squares in the prime field. If either coordinate is zero there is just one point on the quotient. Thus to count $D$ one adds one infinity point and one extra point per pair of distinct nonzero root values $u,v$ to the affine count for the squared equation. This correction is six at 11 and 13 and four at 5, where $9=4$. It also follows directly by taking simultaneous sign orbits over an algebraic closure and testing Frobenius on each orbit.

The checker uses finite-field frequency tables to count both equations, then obtains the degree-twelve Frobenius polynomial of each factor from the first six traces, Newton's identities and the functional equation. The trace for $A$ in degree $d$ is $\#D(\mathbb F_{p^d})-\#C(\mathbb F_{p^d})$.

| $p$ | $\#C(\mathbb F_{p^d})$, $1\le d\le6$ | $\#D(\mathbb F_{p^d})$, $1\le d\le6$ | $\#J(D)(\mathbb F_p)$ | $\#A(\mathbb F_p)$ |
|---|---|---|---:|---:|
| 5 | 26, 46, 146, 726, 2626, 14926 | 16, 36, 136, 676, 2876, 15276 | 145161 | 145161 |
| 11 | 40, 144, 1342, 15580, 159010, 1769484 | 27, 131, 1365, 14915, 160672, 1767041 | 7277567 | 6117249 |
| 13 | 40, 186, 2206, 28862, 372450, 4835076 | 26, 176, 2303, 28408, 371606, 4834265 | 12553952 | 14447264 |

The full Jacobian orders are the products in the last two columns. Their gcd is one, and each of the three residual primes fails to divide at least one order in another characteristic. Good reduction on prime-to-characteristic torsion proves $J(C)(\mathbb Q)_{\rm tors}=0$. The same order test applies separately to $J(D)$ and $A$. In particular no difference of two distinct rational points on $C$ or on $D$ is torsion. An open curve obtained by removing two such points therefore has only constant units.

The same order tests exclude geometrically connected, nontrivial solvable Galois covers over $\mathbb Q$ of either affine curve punctured just at its infinity, with all deck transformations defined over $\mathbb Q$ and no ramification on that affine curve. Indeed such a cover has a connected cyclic quotient of prime degree $\ell$. A small loop around a single puncture is a product of commutators, so this cyclic quotient extends étale over infinity. Its deck group would be a one-dimensional constant quotient of the geometric Jacobian $\ell$-torsion as a Galois module. At every good $p\ne\ell$, Frobenius would have eigenvalue one modulo $\ell$, forcing $\ell$ to divide the corresponding Jacobian order. The table excludes this for every prime. Covers with nonconstant deck groups or different ramification require separate arguments. [Cyclic quotient argument for the genus-six quintic](Erdos849FiveEightQuintic.md)

## The geometric endomorphism rings

Write $F$ for the Frobenius polynomial of a factor and $g$ for the polynomial of $\pi+p/\pi$ if $\pi$ is a root of $F$. The following table gives the auxiliary primes modulo which $F$ is irreducible. The verifier also confirms that no two roots in characteristic zero have a root of unity as their ratio. Indeed such a ratio has degree at most $12\cdot11$. There are 262 possible orders $m$ with $\varphi(m)\le132$; the largest is 510. At each indicated auxiliary prime the $m$-th powers of the roots retain full degree 12, checked in the two maximal proper subfields. Consequently every power of Frobenius has 12 distinct conjugate roots, giving a geometrically simple reduction with geometric rational endomorphism algebra $\mathbb Q(\pi)$ by the centralizer on the Tate module. [Details of this finite-field test for the quintic quotient](Erdos849FiveEightQuintic.md)

| Factor | Test prime at 11 | Test prime at 13 | $g$ at 11, ascending coefficients | $g$ at 13, ascending coefficients |
|---|---:|---:|---|---|
| $J(D)$ | 17 | 31 | 2303, −832, −1200, −184, 51, 15, 1 | 964, 1356, −913, −421, −3, 12, 1 |
| $A$ | 23 | 89 | 3225, 126, −1088, −272, 25, 13, 1 | 1924, −2104, −2071, −415, 25, 14, 1 |

For each factor at $p=11$, the group on the six inverse pairs is transitive. Modulo 2 the real polynomial $g$ has factor degrees $(1,5)$, giving primitivity. For $J(D)$ its degrees modulo 7 are $(1,1,1,1,2)$, and for $A$ the degrees modulo 31 are $(1,2,3)$. Each yields a transposition, so the group on pairs is $S_6$. The degree-twelve polynomial has factor degrees $(2,5,5)$ modulo 137 for $J(D)$ and modulo 89 for $A$. The fifth power of this permutation flips one pair. Its conjugates flip all individual pairs, giving the full signed permutation group.

In the signed group the only proper subgroup strictly between the stabilizer of one sheet and the whole group is its pair stabilizer. Indeed an intermediate subgroup that moves the marked pair projects onto $S_6$, since it contains the stabilizer $S_5$. Conjugating its five single-pair flips then gives the whole kernel. A subgroup preserving the marked pair lies in the pair stabilizer, which contains the sheet stabilizer with index two. Thus the only nontrivial proper subfield of $\mathbb Q(\pi)$ at 11 is its real sextic.

Specialization embeds characteristic-zero endomorphisms into the endomorphism field at both 11 and 13. At 13 the totally real subfield again has degree six. For $J(D)$ the real sextics at 11 and 13 have different unramified residue degrees at 3, respectively $(6)$ and $(1,2,3)$. For $A$ the degrees at 11 are $(6)$ and $(1,1,1,3)$. Hence for either factor the real sextic from 11 cannot embed in the field at 13. The two characteristic-zero geometric endomorphism rings are $\mathbb Z$.

The two factors cannot become isogenous over a number field. Such an isogeny would give an isogeny after good reduction over $\overline{\mathbb F}_{11}$ and hence isomorphic geometric endomorphism fields there. At the unramified auxiliary prime 17 these fields have residue degrees $(12)$ and $(4,8)$.

## Consequences for maps

Pullback from a nonconstant map of smooth curves has finite kernel on Jacobians. Every nonzero abelian subvariety of $J(C)_{\overline{\mathbb Q}}$ has dimension at least six, by the decomposition above, which proves the assertion on maps to smaller positive genera.

An automorphism acts faithfully on $J(C)$ and its finite-order action lies among the four sign pairs in $(\mathbb Q\times\mathbb Q)^\times$. The involution $\iota$ acts as $(1,-1)$. An automorphism acting as $(-1,-1)$ would fix the projectivized canonical map. Yet $C$ is nonhyperelliptic. It has a degree-five map to the $Y$-line; any degree-two map to a line would generate the full function field jointly with this degree-five map by coprimality. The image in $\mathbb P^1\times\mathbb P^1$ would then have arithmetic genus $(2-1)(5-1)=4$, smaller than twelve. Thus the canonical map is an embedding, ruling out $(-1,-1)$ and, by composition with $\iota$, $(-1,1)$. The only nontrivial automorphism has quotient $D$ of genus six. This excludes Galois maps from $C$ to a line for every choice of rational function. It leaves open methods involving covers above $C$ or other subvarieties of the four-column curves.

Run the exact standard-library verifier from the directory containing the other finite-field routines.

~~~sh
python -B Erdos849FiveSevenReflection.py
~~~
