# A density bound from the two-torsion of Pascal pair curves

Let $A_H(x)$ count integers $3\le a\le x$ occurring in at least $H$ distinct proper columns, for fixed $H\ge2$. A proper column has $2\le k\le n/2$. Column one supplies an additional row. With natural logarithms,

$$
\limsup_{x\to\infty}
\frac{(\log\log x)^{H/2}}{\log x}\log(1+A_H(x))
\ \le\ (\log 2)^{H/2}.
$$

For five or more rows, $H=4$. The resulting upper bound for the logarithm of the count is $((\log 2)^2+o(1))\log x/(\log\log x)^2$. Passing to the reflection quotients improves the leading coefficient to $(\log 2)^2/4$. Even this estimate leaves the existence of an individual five-row value open. [Reflection quotients and improved constant](Erdos849PairReduction.md)

## The rank of a Jacobian over the rationals

Let $J/\mathbb Q$ be a principally polarized abelian variety of dimension $g$, with polarization defined over $\mathbb Q$. Let $S$ consist of the real place, 2, and a finite set containing all remaining primes of bad reduction. Write $R=\sum_{p\in S,\,p<\infty}\log p$ and $N=2^{2g}$. There is an absolute implied constant in

$$
\operatorname{rk}J(\mathbb Q)\ \ll\ N(1+\log N)(1+R).
$$

To prove this, put $G=\operatorname{Gal}(\mathbb Q_S/\mathbb Q)$, where $\mathbb Q_S$ is the maximal extension unramified at finite places outside $S$. The group $V=J[2](\overline{\mathbb Q})$ is a $2g$-dimensional $\mathbb F_2$-space with $G$-action. At a prime of good reduction outside $S$, multiplication by 2 on the abelian scheme is finite étale. The properness of this scheme extends every rational point to an integral local section. The fiber of multiplication by 2 above that section is finite étale as well. Thus both the torsion representation and the division points giving the Kummer classes are unramified there. The Kummer injection consequently bounds the rank by $\dim_{\mathbb F_2}H^1(G,V)$. [Local Kummer condition, Mazur–Rubin–type descent for abelian varieties](https://msp.org/ant/2019/13-4/ant-v13-n4-p03-s.pdf)

The perfect Weil pairing embeds $V$ into the permutation module $W=\operatorname{Map}(V,\mathbb F_2)$ by evaluating each vector against all $N$ torsion points. Here $\mu_2$ is identified with the additive group of $\mathbb F_2$, with trivial Galois action. The long exact sequence for $0\to V\to W\to W/V\to0$ gives

$$
\dim H^1(G,V)\le N-2g+\dim H^1(G,W).
$$

Choose one point $P_i$ from each $G$-orbit on $V$, including zero. The corresponding point field $K_i=\mathbb Q(P_i)$ has degree $m_i$ equal to the orbit size, so $\sum_i m_i=N$. Shapiro's lemma on each permutation module identifies its first cohomology with the quadratic characters of the stabilizer of $P_i$. By inflation these are quadratic characters over $K_i$ unramified outside the places $S_i$ over $S$. At each finite place outside $S_i$, a representing square class must have even valuation. Thus their dimension is at most $|S_i|+\log_2|\operatorname{Cl}(K_i)|$, by the ideal-class exact sequence and the $S_i$-unit theorem. [Evertse and Silverman, Lemma 1](https://ir.cwi.nl/pub/1788/1788D.pdf)

For completeness, let $K$ be any such point field, of degree $m$. Its discriminant has no factors outside $S$. For a local prime above $p$ with ramification index $e$ and residue degree $f$, the exponent of the different is at most $e-1+e\,v_p(e)$. Indeed, over the maximal unramified subextension a uniformizer generates a totally ramified extension with Eisenstein minimal polynomial. The derivative at the uniformizer generates the different. Its nonzero terms have distinct valuations modulo $e$, so its valuation is at most that of the leading derivative term. Summing after multiplication by $f$, using $\sum ef=m$ and $v_p(e)\log p\le\log m$, gives

$$
\log|\Delta_K|\le m\left(R+\#S_{\rm fin}\log m\right).
$$

Minkowski supplies a representative of norm at most $2^m\sqrt{|\Delta_K|}$ in each ideal class. At most $B^2\zeta_K(2)\le B^2\zeta(2)^m$ integral ideals have norm at most $B$. Hence $\log|\operatorname{Cl}(K)|\ll m+\log|\Delta_K|$. Since $|S_i|\le m_i |S|$, $\#S_{\rm fin}\le R/\log 2$, and $\log m_i\le\log N$, summing the bounds over the orbits proves the rank estimate.

## The pair count

For $2\le k<d$ let $J(k,d)$ count admissible common values over all heights, and let $C$ be the smooth projective model of $\binom uk=\binom vd$. Its Jacobian is principally polarized over $\mathbb Q$. The pair reduction argument gives $2g\le(k-1)(d-1)$ and $R\ll d^3\log(2d)$ for the indicated set of primes. Good reduction of the curve gives good reduction of its Jacobian. In the geometric genus bound one may also count inertia on the $kd$ sheets over the value line. Finite ramification contributes at most $d(k-1)+k(d-1)$ and infinity contributes $kd-\gcd(k,d)$. Riemann–Hurwitz gives $2g\le kd-k-d+2-\gcd(k,d)$. [Pair reduction and bad primes](Erdos849PairReduction.md)

We use Theorem 1.3 in the **2 February 2026 preprint** of Yu, Yuan and Zhou. It bounds the number of rational points on any smooth projective curve of genus $g\ge2$ over a number field by

$$
10^{13}g^8
\min\left(1+\frac{5}{4\sqrt g},\ 1+\frac{3\log g}{g}\right)^{\operatorname{rk}J}.
$$

Each admissible solution is a smooth affine point, since the falling factorial has positive derivative above its largest root. It lifts to a rational point of $C$. The genus is at least two except for $(2,3)$ and $(2,4)$, whose admissible intersections have been completely determined. Combining the rank and genus bounds, and enlarging an absolute constant for those two pairs, yields

$$
 \log(1+J(k,d))\ \ll\ 2^{kd}d^6.
$$

Indeed $N\le2^{kd}$, $1+\log N\ll d^2$, and $1+R\ll d^3\log(2d)$. The logarithm of the rank-dependent base in the rational-point bound is bounded above by an absolute constant. [Yu–Yuan–Zhou, Theorem 1.3](https://arxiv.org/html/2602.01820v1#S1) · [Genus and exceptional pairs, Leshem–Sayag, Lemma 3.6 and Proposition 3.7](https://arxiv.org/html/2611.34736v1#S3)

## Counting the tuples

Put $L=\log x$ and $E=\log L$. For sufficiently large $x$ set

$$
 D=\left\lfloor\frac{E-(H+10)\log E}{\log 2}\right\rfloor .
$$

Write the $H$ selected proper columns in increasing order $k_1<\cdots<k_H$. If $k_1 k_2\le D$, there are at most $D^2$ choices of that pair, with $k_2\le D$. Their combined contribution has logarithm $O(\log D+2^D D^6)=o(L/E^{H/2})$. This bounds the values in this case irrespective of their other columns.

In the remaining case $k_1k_2>D$ and $k_2>\sqrt D$, giving $\prod_{i=1}^H k_i>D^{H/2}$. The simultaneous-column integral-point estimate, summed uniformly over the at most $(\log_2 x)^H$ choices, bounds this contribution by $L^{O_H(1)}\exp(L/D^{H/2})$. Since $D\sim E/\log2$, taking logarithms proves the limsup. [Simultaneous-column degree and count](Erdos849MultiplicityDensity.md)
