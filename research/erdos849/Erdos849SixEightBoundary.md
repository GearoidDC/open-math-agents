# The two points at infinity in columns six and eight

**Theorem.** On the curve for columns 6 and 8, the difference of its two geometric points at infinity has infinite order in the Jacobian. The same is true after adding either or both of columns 5 and 7. Consequently the affine curve for the four-column pattern $(5,6,7,8)$ has only constant units even over $\overline{\mathbb Q}$. Splitting the two points at infinity over $\mathbb Q(\sqrt{14})$ supplies no unit for an integral-point descent.

## A four-dimensional Prym

Put $X=2n_6-5$, $Y=(2n_8-7)^2$ and $G(Y)=(Y-1)(Y-9)(Y-25)(Y-49)$. The pair projects onto the curve $B$ defined by

$$
G(Y)=224(X^2-1)(X^2-9)(X^2-25).
$$

The involution $j(X,Y)=(-X,Y)$ gives the smooth plane quartic $K$ with $U=X^2$ and $G(Y)=224(U-1)(U-9)(U-25)$. Its genus is three. The two polynomial maps have disjoint finite branch values in characteristic zero and at the primes in the table below. This follows by computing the gcd of the finite branch polynomials for the original maps in columns 6 and 8. Passing to a reflected polynomial in one of the coordinates can only remove branch values. Thus the affine models at these primes are smooth. [Quartic model and smoothness test](Erdos849PatternGeometry.txt)

The completion of $B$ has two points at infinity $P_+,P_-$, distinguished by the sign of $X^3/Y^2=\pm1/(4\sqrt{14})$ in the residue field. More explicitly set $z=X/Y$, $w=X^3/Y^2$, so $X=w/z^2$, $Y=w/z^3$. On dividing the equation by $Y^4$, the equation at $z=0$ becomes $224w^2=1$. These two branches are smooth in the specified odd characteristics. They account for all infinity points since the two degrees are 6 and 4 and the common inertia cycle has two orbits. The involution swaps them. Its fixed points are the four points over $X=0$, which are distinct by smoothness. Riemann–Hurwitz gives $g(B)=7$.

The class $\delta=[P_+-P_-]$ belongs to the four-dimensional Prym $A=\operatorname{im}(1-j)$ in $J(B)$. Indeed one may take any geometric fixed point $O$ of $j$ and write $\delta=(1-j)[P_+-O]$. Galois acts on $\delta$ through the quadratic character of $\mathbb Q(\sqrt{14})$, by its sign. Thus $\delta$ represents a rational point on the quadratic twist of $A$ by this character and the involution $[-1]$.

## The order test

The exact verifier counts points of $K$ and $B$ by matching the frequencies of the polynomial values in each finite field. It adds one infinity point to $K$ and two or zero to $B$ according as 14 is or is not a square in the field. The Frobenius trace on $A$ is $\#K(\mathbb F_{p^d})-\#B(\mathbb F_{p^d})$. Its first four values determine the degree-eight polynomial $F_p$. For $\chi=(14/p)$ the quadratic twist has order $F_p(\chi)$ over $\mathbb F_p$.

| $p$ | $(\#K,\#B)$ for degrees 1 through 4 | $\chi$ | Twist order |
|---|---|---:|---:|
| 11 | $(18,28),(144,168),(1350,1348),(14524,14348)$ | $+1$ | 39,996 |
| 17 | $(19,32),(337,338),(4876,4928),(84053,84646)$ | $-1$ | 38,876 |
| 19 | $(32,37),(408,451),(6626,6910),(130148,129719)$ | $-1$ | 104,762 |

The orders have gcd two, and each residual characteristic fails to divide at least one order in a different characteristic. Good reduction injects prime-to-characteristic torsion, so a finite order for $\delta$ would divide two. An order of one would give a degree-one function on a positive-genus curve. An order of two would make $B$ hyperelliptic by giving a function with a single double pole. But $K$ is a smooth plane quartic and hence nonhyperelliptic. If $B$ were hyperelliptic, its central hyperelliptic involution would descend to a nontrivial involution of $K$, since $j$ has positive-genus quotient. The quotient of $K$ by that involution would be a quotient of the hyperelliptic projective line by the action induced by $j$, hence of genus zero. This contradicts nonhyperellipticity of $K$. Thus $\delta$ has infinite order.

## Pullback to the two four-column patterns

For any of $(6,8),(5,6,8),(6,7,8),(5,6,7,8)$ the simultaneous curve has exactly two geometric points above infinity. Indeed its degree over the value line is the product of the column indices, and its inertia orbits have length their least common multiple. The map to $B$ sends these points bijectively onto $P_+,P_-$, since it is surjective and the coordinate maps have no poles on the affine chart. Pushforward over $\overline{\mathbb Q}$ therefore sends the difference upstairs to $\pm\delta$. A principal divisor pushes to a principal divisor, so no nonzero multiple of the difference upstairs is principal. A unit would have precisely such a degree-zero divisor on the boundary, proving the theorem. [Geometric degree and infinity count](Erdos849ReciprocalRunge.txt)

For $(3,5,7,8)$ the boundary already consists of one geometric point, so its affine units are also constant. The assertion concerns the curves themselves; it leaves open integral-point methods on covers or with different auxiliary functions.

There is also an obstruction to using a Galois cover of the common value line $t$ in either four-column pattern. At the outer critical value $b$ of the smallest column, whose index is 3 or 5, the smallest-column map has one simply ramified point and an unramified point. Every larger column is unramified there because its greatest absolute finite critical value is strictly smaller. Thus two points of the full affine curve over $b$ have different ramification indices, one and two. If a further cover were étale over that affine curve, these indices would persist. Even on replacing $t$ by any nonconstant rational function $h(t)$ the indices at the two points would be $e_b(h)$ and $2e_b(h)$. A Galois cover in characteristic zero has equal indices at all points of each geometric fiber. Consequently no such further cover can be Galois over this choice of line, over any extension of the constant field. [Critical values and geometric fiber products](Erdos849ReciprocalRunge.txt)

## No elliptic or genus-two quotient of the original pair

The unreflected curve $C$ in coordinates $X=2n_6-5$, $T=2n_8-7$ has the two independent sign involutions. The invariant quadrant gives $K$, the two single reflections give $B$ and $E$, where $E$ has equation $224(U-1)(U-9)(U-25)=G(T^2)$. The genera of $K,B,E,C$ are $3,7,7,17$. For example the projections to the value line have ordered degree pairs $(3,4),(6,4),(3,8),(6,8)$. Disjoint finite branch sets give $2g=ab-a-b+2-\gcd(a,b)$ in each case. The four sign characters on the Jacobian therefore give factors of dimensions $3,4,4,6$ over $\mathbb Q$.

The three-dimensional factor $J(K)$ is already known to be geometrically simple. For the other three, the following triples of Frobenius traces are $\#K-\#B$, $\#K-\#E$, and $\#B+\#E-\#C-\#K$, respectively. The table supplies enough point counts at 11 to recover all three polynomials. [Three-dimensional factor](Erdos849QuarticDescent.txt)

| Extension degree | $\#K$ | $\#B$ | $\#E$ | $\#C$ |
|---:|---:|---:|---:|---:|
| 1 | 18 | 28 | 28 | 54 |
| 2 | 144 | 168 | 160 | 188 |
| 3 | 1350 | 1348 | 1336 | 1290 |
| 4 | 14524 | 14348 | 14748 | 15008 |
| 5 | 160578 | 160948 | 160008 | 160314 |
| 6 | 1772496 | 1768920 | 1770352 | 1769036 |

For the first and third characters the Frobenius polynomials are irreducible modulo 5 and 41, respectively. The roots of every positive power remain distinct in characteristic zero by the root-of-unity degree test in the verifier. For the middle character the real trace $\pi+11/\pi$ has polynomial

$$
g(s)=s^4+10s^3+14s^2-88s-176.
$$

Its squarefree factor degrees modulo 7 are $(2,2)$, excluding a linear factor over $\mathbb Q$. For a quadratic factorization $(s^2+as+b)(s^2+cs+d)$ we would have $c=10-a$, $bd=-176$, $a(d-b)=-88-10b$, and $b+d+a(10-a)=14$. The verifier checks the finite list of signed divisors $b$ and excludes each. Thus the real trace has degree four. Since $\pi$ has absolute value $\sqrt{11}$ it cannot be real, as then the real trace would be $\pm2\sqrt{11}$. Hence $\pi$ is quadratic over the totally real quartic, proving irreducibility of its degree-eight Frobenius polynomial over $\mathbb Q$.

If two of its Frobenius roots had a root of unity of order $m$ as their ratio, $\varphi(m)\le 8\cdot7=56$. At the auxiliary prime 1,000,003, the verifier computes the characteristic polynomial after raising the roots to each such candidate power by Newton sums, and checks squarefreeness in every case. The same separation for the first and third characters is checked using maximal proper finite subfields at the respective irreducible reductions. [Root-of-unity finite test](Erdos849FiveEightQuintic.md)

Every finite extension of the residue field therefore retains an irreducible Frobenius polynomial for each of these three factors. They are geometrically simple in characteristic eleven and consequently in characteristic zero. A geometric map to a curve of genus one or two would pull its Jacobian back with finite kernel, giving an abelian subvariety of dimension one or two. The decomposition into simple factors of dimensions $3,4,4,6$ rules this out.

~~~sh
python -B Erdos849SixEightBoundary.py
~~~
