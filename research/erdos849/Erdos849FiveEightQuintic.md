# A genus-six descent obstruction for columns five and eight

Every admissible common entry in columns \(5,8\), in particular in the pattern \(5,7,8\), gives an integral point of the smooth plane quintic
\[
 C:\quad 86016\,X(X^2-1)(X^2-4)=(Y-1)(Y-9)(Y-25)(Y-49).
\]
Here \(X=n_5-2\) and \(Y=(2n_8-7)^2\). The unique point at infinity is \(I=[0:1:0]\). This is the quotient of the two-column curve by reflection of the eighth-column row. Its Jacobian \(J\) satisfies
\[
 \operatorname{End}_{\overline{\mathbb Q}}(J)=\mathbb Z,\qquad J(\mathbb Q)_{\rm tors}=0.
\]
Consequently no nonconstant morphism from this quotient goes to a curve of genus \(1,\ldots,5\), even after extending the ground field. Its geometric automorphism group is trivial. For any distinct rational points \(P,Q\), every regular unit on \(C_{\overline{\mathbb Q}}\setminus\{P,Q\}\) is constant. Moreover the affine quintic \(C-\{I\}\) admits **no nontrivial geometrically connected finite Galois cover over \(\mathbb Q\) with solvable Galois group that is étale on the affine curve**. The latter statement includes every double cover over \(\mathbb Q\). A ramified cover, a cover with a larger constant field, or a non-Galois cover over \(\mathbb Q\) is outside its scope.

## Computations

At \(p=5\) the left side becomes \(86016(X^5-X)\), giving a nonzero constant affine derivative. At \(11,13\) the two polynomial maps have disjoint critical values, checked by an exact polynomial gcd as in the [quartic verifier](Erdos849PatternGeometryQuartics.py). In all three characteristics the derivative in the homogenizing variable at \(I\) is a unit. Thus these are smooth projective reductions. Smoothness at 5 alone also gives the smooth characteristic-zero plane quintic of genus six.

The [exact verifier](Erdos849FiveEightQuintic.py) counts, for each \(1\le d\le6\), the values of each side in \(\mathbb F_{p^d}\), takes the scalar product of their frequency lists and adds the point at infinity. Field elements are represented by base-\(p\) digits in the power basis of a certified primitive generator. Newton identities and the Weil polynomial functional equation then give the characteristic polynomial \(F_p(T)\) on \(H^1\) and the Jacobian order \(F_p(1)\).

| \(p\) | \(\#C(\mathbb F_{p^d}),\ d=1,\ldots,6\) | \(\#J(\mathbb F_p)\) |
|---|---|---:|
| 5 | 16, 46, 121, 546, 3126, 15601 | 164791 |
| 11 | 25, 137, 1408, 14601, 160475, 1776362 | 6256468 |
| 13 | 27, 215, 2109, 28671, 373762, 4819625 | 14817888 |

Their gcd is one. Each of the primes \(5,11,13\) also fails to divide at least one order in a different residual characteristic. Good reduction on prime-to-characteristic torsion now proves the assertion on \(J(\mathbb Q)_{\rm tors}\). In particular every difference of distinct rational points has infinite order: a principal divisor \(P-Q\) would give a degree-one function on a genus-six curve. A nonconstant unit after deleting two such points would have divisor a nonzero multiple of \(P-Q\). For the divisor characterization of units see Landesman and Poonen, Remark 1.1, [Obstructions to applying the Baker–Bilu method](https://arxiv.org/html/2306.11799v1).

## The endomorphism ring

The verifier records the degree-12 polynomials \(F_{11},F_{13}\). They are irreducible at \(q=53,43\), respectively. No ratio between distinct roots of either polynomial is a root of unity. Indeed its degree would be at most \(12\cdot11=132\), by the action on ordered pairs. For its order \(m\) one would have \(\varphi(m)\le132\), hence \(m\le2\cdot132^2\) by \(\varphi(m)\ge\sqrt{m/2}\). There are 262 candidate orders in this range, the largest being 510. In \(\mathbb F_{q^{12}}\), let \(z\) be a root of the appropriate irreducible polynomial. For each candidate, the verifier checks \(z^{m(q^4-1)}\ne1\) and \(z^{m(q^6-1)}\ne1\). Thus \(z^m\) lies in neither maximal proper subfield. Its 12 conjugates stay distinct modulo \(q\), which excludes a collision in characteristic zero.

Write \(E_p=\mathbb Q[T]/F_p(T)\), with root \(\pi\). Every power of the good-reduction Frobenius therefore has 12 distinct conjugate eigenvalues. Endomorphisms defined over any finite extension commute with the corresponding power of Frobenius. Their faithful action on a rational Tate module places their algebra in its 12-dimensional centralizer, while \(\mathbb Q[\pi]\) already has dimension 12. The geometric rational endomorphism algebra of each reduction equals \(E_p\). Specialization at good reduction embeds the characteristic-zero geometric endomorphism algebra in both fields; cf. [Smith, section 14](https://doi.org/10.1112/S1461157010000410).

The conjugate roots pair as \(\{\pi,p/\pi\}\), and the real sextics of \(\pi+p/\pi\) at \(11,13\) are respectively
\[
 g_{11}(u)=u^6+13u^5+26u^4-226u^3-788u^2+16u+340,\quad
 g_{13}(u)=u^6+13u^5+29u^4-216u^3-1057u^2-1249u-62 .
\]
These fields are totally real by the Weil absolute values and have degree six since \(\pi\) is quadratic over them. The splitting group of \(g_{11}\) is \(S_6\). Its action is transitive, and the squarefree factorization degrees \(1,5\) at 3 force primitivity, since a nontrivial block system would have blocks of size two or three and could not admit a five-cycle. The degrees \(1,2,3\) at 5 give a transposition on taking the third power. A primitive permutation group containing a transposition is symmetric: the graph formed by its conjugate transpositions has components forming an invariant partition, and a connected graph's edge transpositions generate the symmetric group. Finally the squarefree factorization of \(F_{11}\) at 23 has degrees \(2,5,5\), giving one transposition on taking the fifth power. A transposition preserving the conjugate pairs flips a single pair. Its conjugates flip each pair independently. The splitting group on the 12 roots is consequently \((C_2)^6\rtimes S_6\).

In this signed action the sheet stabilizer fixes one marked pair and allows every permutation and flip on the other pairs. Any larger subgroup inside the pair stabilizer must be the pair stabilizer itself, of index two over the sheet stabilizer. If its projection moves the marked pair, that projection contains \(S_5\) and must be \(S_6\); conjugating the available flips supplies every individual flip. Galois correspondence shows that the only proper nontrivial subfield of \(E_{11}\) is its real sextic \(R_{11}\). Any embedding of \(R_{11}\) into \(E_{13}\) would land in its real part \(R_{13}\), of the same degree. Yet at 59, \(g_{11}\) factors with degrees \(1,5\) and \(g_{13}\) is irreducible, both separably. The first field has a degree-one 59-adic completion and the second does not. Thus a subalgebra embedding in both \(E_p\) must be \(\mathbb Q\). This gives the geometric endomorphism ring \(\mathbb Z\), absolute simplicity, and geometric Picard number one for the Jacobian.

A morphism to a positive-genus curve would pull its Jacobian back with finite kernel, excluding all positive genera less than six. Any automorphism induces \(+1\) or \(-1\) on the Jacobian. Either action fixes the projectivized canonical map, which is an embedding because the canonical bundle of a plane quintic is \(\mathcal O_C(2)\). Hence the automorphism is the identity.

## Solvable Galois covers

Suppose a geometrically connected solvable Galois cover as stated exists. A nontrivial finite solvable group has a prime-order quotient \(C_\ell\), giving a geometrically connected cyclic cover with all deck transformations defined over \(\mathbb Q\). It extends étale over \(I\). Indeed in the geometric fundamental group of a once-punctured compact Riemann surface a loop about the puncture is a product of commutators, so it has trivial image in the cyclic quotient.

The resulting quotient of the geometric abelian fundamental group modulo \(\ell\), identified with \(J[\ell](\overline{\mathbb Q})\), is a one-dimensional quotient on which the absolute Galois group of \(\mathbb Q\) acts trivially. Thus geometric or arithmetic Frobenius at every good \(p\ne\ell\) has eigenvalue one on the reduction of the Tate module modulo \(\ell\), implying \(\ell\mid F_p(1)\). The three orders above exclude every \(\ell\). This obstructs solvable Galois descents of the indicated kind on this explicit quotient. The integral-point problem for the quintic, with the additional square condition on \(Y\), remains open here.
