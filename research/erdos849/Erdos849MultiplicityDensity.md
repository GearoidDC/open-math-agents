# Counting values occurring in several rows of Pascal's triangle

For fixed $H\ge2$, let $A_H(x)$ count integers $3\le a\le x$ with at least $H$ distinct representations $a=\binom nk$ in proper columns $2\le k\le n/2$. The additional representation in column one puts these values in at least $H+1$ rows. This agrees with Leshem and Sayag's condition $N(a)>2H$ on the number of positions in the full triangle. Indeed, the edge row contributes two positions, every proper column contributes two except a central one, and at most one central representation is possible.

With natural logarithms, the following bound retains the dependence on the multiplicity.

$$
 \limsup_{x\to\infty}
 \frac{(\log\log x)^{(H-1)/4}}{\log x}\,
     \log(1+A_H(x))
 \ \le\ \tfrac12(\log 5)^{(H-1)/4}.
$$

For five or more rows, take $H=4$. The power of $\log\log x$ is then $3/4$. Leshem and Sayag's Proposition 3.7 bounds every $A_H$ by a common expression with power $1/4$. These estimates control the number of exceptional values up to $x$. Their right sides allow infinitely many witnesses. [Leshem and Sayag, 25 November 2026](https://arxiv.org/html/2611.34736v1)

## Degree of the curve of simultaneous representations

Fix $2\le k_1<\cdots<k_H$, and put $f_k(X)=\binom Xk$. In affine $H$-space with coordinates $n_1,\ldots,n_H$, impose $f_{k_i}(n_i)=f_{k_1}(n_1)$ for $i=2,\ldots,H$. The resulting curve is geometrically integral by the transitive-monodromy proof in sections 1–3 of the [simultaneous-column argument](Erdos849ReciprocalRunge.txt). That argument applies to arbitrary distinct columns, including even degrees. For $H=2$, Leshem and Sayag's Lemma 3.1 gives an independent proof.

The degree of this affine curve in the indicated coordinates is exactly

$$
 \delta=\prod_{i=2}^H k_i.
$$

The defining equations have degrees $k_2,\ldots,k_H$, so affine Bézout gives the upper bound. For the lower bound intersect with the hyperplane $n_1=u$. For generic complex $u$, the common value $f_{k_1}(u)$ is regular for each of the other polynomials. Their roots can be chosen independently and give exactly $\delta$ distinct affine points. A proper hyperplane section of the projective closure contains at most its degree in distinct points.

## Uniform count for the large columns

Write $L=\log x$, $E=\log L$, and $K=\lfloor\log_2 x\rfloor$, for $x$ sufficiently large. An admissible column satisfies $2^k\le\binom{2k}{k}\le x$, hence $k\le K$. Also $\binom nk\ge(n/k)^k$, by comparing each of the factors $(n-i)/(k-i)$ with $n/k$. Thus all row coordinates have absolute value at most $B=\lceil K x^{1/k_1}\rceil$.

Castryck, Cluckers, Dittmann and Nguyen's Theorem 3 bounds the number of integral points in this box by

$$
 c(H)\,\delta^3 B^{1/\delta}(\log B+\delta).
$$

The constant depends only on the ambient dimension. This uniformity permits the columns to increase with $x$. [Castryck, Cluckers, Dittmann and Nguyen, *Algebra & Number Theory* 14 (2020), Theorem 3](https://rcluckers.perso.math.cnrs.fr/prints/Cast-Cl-Ditt-Nguy.pdf)

There are at most $K^H$ tuples and $\delta\le K^{H-1}$. Since $B\le2Kx^{1/k_1}$, all factors other than $x^{1/(k_1\delta)}$ cost at most a fixed power of $L$, depending on $H$. For any integer $D\ge4$, tuples having at most one member at most $D$ satisfy

$$
 k_1\delta =\prod_{i=1}^H k_i\ \ge\ 2(D+1)^{H-1}.
$$

Their total contribution is at most $L^{O_H(1)}\exp(L/(2(D+1)^{H-1}))$. Counting a value once for each tuple containing it can only increase this upper bound.

## Two small columns

Equation $32$ in the proof of Leshem and Sayag's Proposition 3.7 gives a bound for the total number of common values, summed over all pairs of proper columns up to $D$, even without imposing an upper bound on $a$.

$$
 4+D^2\exp\!\bigl(D^3 5^{D^4}\bigr).
$$

This uses Rémond's bound on rational points and complete classifications of two low-genus pairs. Every value with a pair of proper columns at most $D$ is covered by this count. [Leshem and Sayag, equation (32)](https://arxiv.org/html/2611.34736v1#S3)

Set $D=\lfloor ((E-(H+3)\log E)/\log 5)^{1/4}\rfloor$. For sufficiently large $x$, $D\ge4$, $5^{D^4}\le L/E^{H+3}$, and $D^3=O(E^{3/4})$. The logarithm of the small-column contribution is $o(L/E^{(H-1)/4})$. Also $D+1\sim(E/\log5)^{1/4}$ and $\log L=E=o(L/E^{(H-1)/4})$. Taking the logarithm of the sum of the two contributions proves the displayed limsup.
