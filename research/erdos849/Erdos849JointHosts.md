# How prime divisors connect positions in different Pascal rows

Let \(a\ge10^{128}\) have admissible representations in two columns \(k,l\) selected from \((3,5,7,8)\) or \((5,6,7,8)\). Assign each \(p^e\mathrel\Vert a\), independently in each numerator, to one position of maximum \(p\)-adic valuation. Join two positions when the same prime is assigned to both. For every nonempty proper subset \(S\) of the \(k\) positions, with neighboring positions \(N(S)\) among the \(l\) positions, one has
\[
                  k\,|N(S)|>l\,|S|.
\]
Both directions hold for each of the nine unordered column pairs. This result for a pair uses just the two representations. For a full exceptional pattern, the prior finite exclusion through \(10^{128}\) gives the same conclusion at all admissible heights.

The strict inequality forces each pair's graph to be connected. A component and its complement could not both have strictly larger neighbor proportions. For example, one may delete **any single** position of the eight-term numerator and still match the seven positions of the seven-term numerator to seven distinct positions joined to them by primes. Indeed, before deletion each nonempty set of seven-side positions has at least one more neighbor than its cardinality; apply Hall's marriage theorem after deletion. Every position has at least one assigned prime since its term is larger than the product of all the cofactors.

## The two-sided product test

In a row with \(k\) numerator terms, the chosen position for \(p\) absorbs \(p^e\): at each level \(p^j\), removal of a maximum leaves at most \(\lfloor k/p^j\rfloor\) multiples of \(p^j\). Dividing each term by its assigned powers leaves integer cofactors of product \(k!\). Put \(H=10^{128}\), \(y=a/H\), \(z_k=\lfloor(k!H)^{1/k}\rfloor\), \(L_k=z_k-k+1\), and \(U_k=z_k+k\). Each of the \(k\) terms belongs to \([L_k y^{1/k},U_k y^{1/k}]\), by bounding the binomial product between powers of its smallest and largest terms.

Suppose all assignments from \(i\) of the \(k\) positions enter \(j\) of the \(l\) positions and \(kj\le li\). Then their lower product must fit in the receiving positions after allowance for the source cofactors. Also all assignments from the \(l-j\) complementary positions enter the \(k-i\) complementary positions. Since \(i/k\ge j/l\), both inequalities become at least as restrictive as \(y\) increases, giving the necessary conditions
\[
 L_k^i\le k!\,U_l^j,\qquad L_l^{l-j}\le l!\,U_k^{k-i}.
\]
The exact verifier enumerates all 303 directed size choices. Only four pass.

* For \((k,l,i,j)=(8,6,4,3)\) or its reverse, equality of the exponents makes the ratio of the two term products lie in \([L_k^i/U_l^j,U_k^i/L_l^j]\). That ratio equals \(b/d\), where \(b\mid k!\) is the source cofactor product and \(d\) is the receiving cofactor product times all incoming prime powers from outside the source subset. For each of the 126 possible numerators across the two directions, the interval \([bL_l^j/U_k^i,bU_l^j/L_k^i]\) contains no positive integer \(d\).
* For \((7,8,1,1)\), write \(x=n-s\) and \(u=m-r\) for the relevant terms in columns eight and seven. The product \(P\) of the primes' full powers at the seven-side position divides both \(x\) and \(u\), and \(u\le7!P\). With signed \(A=7!\prod_{v\ne s}(s-v)\) for \(0\le v<8\) and \(B=8!\prod_{v\ne r}(r-v)\) for \(0\le v<7\), the binomial equality gives \(P^2\mid Ax-Bu\). To see this, retain the factor \(x\) on one side and \(u\) on the other, and reduce the other factors modulo \(P\). All 56 shift choices satisfy \(|B|L_7>|A|U_8\), so \(Ax-Bu\ne0\); they also satisfy \(L_7^2>(7!)^2(|A|U_8+|B|U_7)\). But \(P^2\le(|A|U_8+|B|U_7)y^{1/7}\) and \(P^2\ge(L_7/7!)^2y^{2/7}\), a contradiction.
* The complement of \((8,7,7,6)\) would place all powers from one seven-side position in a single eight-side position, the case just excluded.

## Full four-column assignments

When all four columns occur, at least **31 distinct four-column tuples of positions** are occupied. The minimum rises to **32** from \(10^{180}\) and **37** from \(10^{370}\). Several different primes assigned to exactly the same positions in all four rows contribute only one occupied tuple.

For this assertion use the complete polynomial archives for the indicated pattern. Fix a tuple \(v\). The integer polynomial value \(F_v\) at its four shifted rows is nonzero, and its order \(h\) and real bound are common to all primes with this same tuple. For each such \(p^e\mathrel\Vert a\), \(p^{h\max(0,e-v_p(420))}\mid F_v\). These divisibilities may thus be multiplied **before** applying the ordinary absolute bound. The resulting product \(G_v\) of the full prime powers assigned to \(v\) satisfies
\[
 G_v \le D_v Q y^{1/36},\qquad Q=35519,\qquad
 D_v=\prod_{p\ \text{assigned to }v}p^{v_p(420)} .
\]
The products \(D_v\) over distinct tuples jointly divide 420. This multiplication step uses divisibility of the same integer value, which the existing local-polynomial replays verify for each tuple.

Now count distinct occupied tuples in each eighth-column position. Its term is exactly the product of those \(G_v\) times its cofactor. The cofactor and the factors \(D_v\) on any one, two, or four positions have product bounded respectively by 117600, 705600, or 8467200, by the original residue enumeration. Thus the host product estimates apply with tuples as the units being counted. At \(H\) a position with at most two tuples or two positions containing at most six altogether violate the term lower bounds, giving \(7\cdot4+3=31\). At \(10^{180}\) a single position with at most three tuples already violates its lower bound. From \(10^{370}\), four positions with only four tuples each also violate theirs. At most 36 tuples with at least four in every position would require four such positions, so at least 37 are needed.

Run `python -B Erdos849JointHosts.py` to check the finite inequalities, the ratio exclusions, and the host constants. The two polynomial archives and their replays are `Erdos849PatternThree.py` and `Erdos849PatternSixHost.py`. The pairwise neighborhood result requires no polynomial-archive assumption.
