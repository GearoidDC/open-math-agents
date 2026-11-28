# Boundary units on covers of the genus-two quotient for columns 3 and 5

Write $C_0$ for the smooth projective curve $v^2=400r^6+200r^3-80r+9$, and put $f(r)=(400r^6+200r^3-80r+9)/400$. The point at infinity of the binomial curve maps to the point $q$ of $C_0$ where $v/(20r^3)$ tends to $+1$. Work throughout over the algebraic closure of the rationals. The boundary of a cover means the full fiber over $q$. [Derivation of the quotient](Erdos849ThreeFiveCurve.txt)

**Proposition.** Let $Y\to C_0$ be any connected Galois étale cover with elementary abelian group of exponent two or three. Every invertible regular function on $Y$ with its boundary removed is constant. This includes the maximal elementary abelian covers of degrees 16 and 81. The proposition excludes these specific covers as sources of units in the integral-point method. The integral points for columns 3 and 5 remain undetermined.

## The fifteen double covers

For a pair of distinct roots of $f$, let $h$ be the monic quadratic they determine and let $k=f/h$. Adjoin $U$ with $U^2=h$ to the function field of $C_0$. All valuations of $h$ are even, since each root is a branch point of the hyperelliptic map and $h$ has poles of order two at both points at infinity. This gives an étale cover $D_h$.

A rational function of $r$ alone is a square in $\overline{\mathbb Q}(C_0)$ precisely when it is either a square or $f$ times a square in $\overline{\mathbb Q}(r)$. This follows by squaring $a+b\sqrt{f}$ and comparing its $\sqrt{f}$ coefficient. The set of roots of odd valuation of $h$ has size two. For a ratio of distinct pair polynomials the corresponding set has size two or four. These sizes exclude both squares and $f$ times squares. Thus the fifteen covers are connected and pairwise distinct. They exhaust the nontrivial quadratic characters, since the geometric 2-torsion of a genus-two Jacobian has order $2^4$.

The sextic $f$ is irreducible modulo 7. Modulo 41 it is $(r-9)(r^5+9r^4+40r^3+12r^2+26r+37)$, with irreducible quintic factor. Both reductions are squarefree. Frobenius therefore gives a transitive group on the six roots, with a stabilizer containing a 5-cycle on the other roots. By transitivity, this holds for each stabilizer. In particular Galois acts transitively on the fifteen pairs.

## Two incompatible specializations at the same prime

The function $W=v/(20U)$ induces a map from $D_h$ to the genus-one curve $E_h$ with equation $W^2=k(r)$. On the two branches over $q$, the signs of $U/r$ and $W/r^2$ in the limit agree. The two points therefore map to the distinct points $P_+,P_-$ at infinity on $E_h$. The ordered difference $P_--P_+$ is defined by the monic quartic and its choice of positive infinity. If it were torsion for any pair, its order would be the same for every pair by the Galois action just proved.

Write $k=S^2+Lr+M$ where $S=r^2+Br+C$. Put $u=2(W+S)$ and $z=2ur+Bu+L$. Substitution gives the elliptic model

$$
z^2=u^3+(B^2-4C)u^2+(2BL-4M)u+L^2 .
$$

The inverse on $u\ne0$ is $r=(z-Bu-L)/(2u)$, $W=u/2-S$. At $P_+$ the coordinate $u$ has a pole. At $P_-$ the identity $(W+S)(W-S)=Lr+M$ gives $u=-L/r+O(1/r^2)$. The point difference on the cubic with its usual origin is therefore $(0,-L)$.

The table uses ascending coefficient order for the monic polynomials. The cubic column lists $A,B',C'$ in $z^2=u^3+A u^2+B'u+C'$.

| $h\bmod 11$ | $k\bmod 11$ | Cubic coefficients | $(0,-L)$ | Exact order |
|---|---|---|---|---:|
| $(4,3,1)$ | $(4,3,5,8,1)$ | $(5,8,9)$ | $(0,8)$ | 17 |
| $(6,6,1)$ | $(10,5,8,5,1)$ | $(0,4,4)$ | $(0,9)$ | 11 |
| $(10,4,1)$ | $(6,0,6,7,1)$ | $(0,8,5)$ | $(0,7)$ | 15 |

The reduction of $f$ modulo 11 is squarefree, so each coprime factorization in the table lifts by Hensel's lemma to monic factors over the 11-adic integers. Their roots form subsets of the six algebraic roots in an algebraic closure of the 11-adic field. Each displayed cubic is smooth, giving good reduction for its lifted curve. Good reduction injects torsion of order prime to 11, so the prime-to-11 part of a torsion point's order agrees with that of its reduction. In the first and third rows these parts are 17 and 15. They cannot both be the prime-to-11 part of one geometric torsion order. By transitivity the boundary difference has infinite order for every pair.

The pushforward of the difference of the two points of $D_h$ above $q$ is this nontorsion point. Hence no nonzero multiple of their difference is principal. The divisor of a unit is supported on the boundary and has degree zero, so every such unit is constant. For the corresponding result for each of the forty connected cyclic triple covers, see [the cubic-cover proof and finite-field tests](Erdos849ThreeFiveCubicCovers.md).

## From cyclic quotients to every elementary abelian cover

Write $G=(\mathbb F_\ell)^s$ for the deck group, with $\ell=2$ or $3$ and $s\ge1$. Label the fiber above $q$ by $G$. If a unit has divisor $\sum_g n_g[g]$, then $\sum_g n_g=0$. For every hyperplane $H$ of $G$, the norm to $Y/H$ is a unit on the cyclic quotient with its boundary removed. The results for degrees two and three show that this norm is constant. Its divisor is the pushforward, so

$$
\sum_{x\in g+H} n_x=0
$$

for every coset of every hyperplane. Fix $g$ and sum these equalities over all $H$. The coefficient of $n_g$ is $(\ell^s-1)/(\ell-1)$. For each $x\ne g$ the coefficient is $(\ell^{s-1}-1)/(\ell-1)$, since $H$ must contain $x-g$. The degree-zero equality reduces the resulting sum to $\ell^{s-1}n_g=0$. Every coefficient vanishes, proving the proposition.

An elementary abelian Galois cover étale away from the single point $q$ is already étale there. After embedding in the complex numbers, a small loop around $q$ is a product of commutators in the punctured surface group and consequently maps trivially to every abelian quotient. The maximal elementary abelian deck group has rank four by the abelianization of the compact genus-two surface group.

## A ramified dihedral consequence

Suppose a connected Galois cover has dihedral group of order $2p$ with $p$ an odd prime, is étale off $q$, and ramifies at $q$. Its inertia group lies in the commutator subgroup by the same loop relation. This subgroup is the rotation group of order $p$. Since inertia is nontrivial, it equals the rotation group. The boundary has exactly two points, each mapping to a distinct point over $q$ on the unramified quadratic quotient. The norm of any boundary unit down to this quotient has zero divisor. Over the algebraically closed field the pushforward preserves both boundary coefficients, so both coefficients already vanish upstairs. This also excludes boundary units on every such ramified $S_3$ cover.

## Reproduction

Run both commands with Python 3 and its standard library in the directory containing the verifiers. The first checks squarefreeness, the two Frobenius cycle types, the three quadratic factorizations, the smooth cubics and the exact orders under repeated point addition. The second checks the cyclic triple-cover inputs.

~~~sh
python -B Erdos849ThreeFiveAbelianCovers.py
python -B Erdos849ThreeFiveCubicCovers.py
~~~
