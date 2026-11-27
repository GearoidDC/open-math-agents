# Prime divisors of a binomial value in columns 5, 6, 7, and 8

Let \(a\ge 10^{128}\) occur in all four columns. The certificate gives at least 31 distinct prime divisors of \(a\), of which at least ten exceed 100. It applies to any four integer rows representing \(a\). Run the standard-library verifier from this directory with

    python -B Erdos849PatternSixHost.py

The archive uses column order \(8,7,6,5\). It contains a polynomial with integer coefficients and an order of vanishing for each of the \(8\cdot7\cdot6\cdot5=1680\) possible tuples of offsets. These tuples describe where a full prime power dividing \(a\) lands in each numerator. No lattice routines are required for replay.

## Uniform bound

Put \(H=10^{128}\), \(Q=35519\), and \(t=(a/H)^{1/36}\). For every \(p^e\mathrel\Vert a\), the certificate gives \(p^e\le p^{v_p(420)}Qt\). Here are the checks behind this estimate.

* Write \(s_k=n_k\bmod p^e\). The factorial floor formula counts \(e\) carry levels; some level \(i\ge e\) therefore satisfies \(n_k\bmod p^i<k\bmod p^i\). In particular \(s_k<k\), so \(x_k=n_k-s_k\) is one of the numerator factors.
* For that branch write \(c_k=k!/\prod_{v\ne s_k}(s_k-v)\), with \(0\le v<k\). Choose \(L\) as the least common denominator of the rational coefficients \(c_k/(s_k-v)\). The verifier checks \(L\mid420\). If \(e>v_p(420)\), each \(x_k/(s_k-v)\) has positive \(p\)-adic valuation. The binomial equation gives \(v_p(x_k)=e+v_p(c_k)\) and
  \[
  u_k\prod_{v\ne s_k}\bigl(1+Lc_k u_k/(s_k-v)\bigr)=a/L,\qquad u_k=x_k/(Lc_k).
  \]
  The polynomial on the left has integral coefficients and linear coefficient one. Its formal inverse through degree \(h-1\), evaluated at \(a/L\), agrees with the actual \(u_k\) modulo \(p^{h(e-v_p(L))}\): the divided difference at arguments of positive valuation is a unit. Replay uses Lagrange inversion to check that every coefficient of the certificate polynomial in the resulting parameter below degree \(h\) vanishes.
* On the real side, write \(z_k=\lfloor(k!H)^{1/k}\rfloor\). The scaled variable \(x_k/(a/H)^{1/k}\) lies in \([z_k-s_k,z_k+k-s_k]\) by the bounds from the binomial product. Positive and negative monomials use opposite interval ends in the lower bound. After the leading coefficient is oriented positively, every partial sum in descending weight order is positive. Summation by parts then guarantees the polynomial has nonzero value for every \(a\ge H\).
* For weight \(w=\sum_k(840/k)i_k\), the finite checks give \(36w\le840h\). Bounding the positive and negative parts separately gives absolute polynomial value less than \(Q^h t^h\). Comparing with its divisibility proves the uniform prime-power bound. For \(e\le v_p(420)\) that bound holds directly.

## Counting the prime divisors

Assign each full prime power to a column-eight numerator factor of greatest valuation at its prime. It divides that factor. The remaining cofactors have product \(8!\). For one or two selected factors, the verifier bounds their combined cofactor and all assigned denominator losses \(p^{v_p(420)}\) by 117600 or 705600 respectively. It enumerates the eight-term window modulo the first power of each \(p=2,3,5,7\) exceeding eight. Any hidden higher power in the unique zero residue increases the host valuation and the assigned exponent equally.

Every numerator factor is at least \(M(a/H)^{1/8}\), where \(M=z_8-7\). The integer checks \(M>117600Q^2\) and \(M^2>705600Q^6\) exclude a factor with at most two assigned powers and a pair having at most six altogether. The corresponding lower bounds grow at least as fast as their respective upper bounds because \(2/36\le1/8\) and \(6/36\le1/4\). Thus at least seven factors each have at least four assigned primes, and the eighth has at least three.

To bound the number exceeding 100, assume it is at most nine. For each interval of a tenth of a decade, the checker rounds \(Qt\) up to an integer \(q\). Then
\[
 a\le420\,q^9\prod_{p\le100}p^{\lfloor\log_p q\rfloor}.
\]
The product is over the 25 primes up to 100 and is evaluated using integer powers. At sufficiently large heights even \(420(Qt)^{34}<a\), leaving finitely many intervals. For intervals where the displayed bound \(U\) still reaches the lower endpoint \(V\), omitting a maximal power of a prime \(p\ge31\) costs a factor of at least 31. At most \(\lfloor\log_{31}(U/V)\rfloor\) such primes can miss their maximum. The checker chooses enough distinct bases that at least six must saturate. For each possibility it enumerates all admissible eighth-column rows by the Chinese remainder theorem, using residues \(0,\ldots,7\) for each required power. Testing the resulting rows by integer binomial arithmetic in columns 5, 6, and 7 eliminates every candidate.

The continuous product bound applies from \(10^{657}\). Below there, 2,081 exceptional tenth-decades merge into 182 ranges. Their residue conditions leave 4,828 distinct eighth-column rows, of which zero represent a common value in the four columns.

The verifier uses the common machinery in `Erdos849PatternThree.py` and `Erdos849PatternThreeCRT.py`. The finite column search through \(10^{128}\) is a separate input for extending the conclusion to all heights. This certificate alone makes the stated implication for \(a\ge10^{128}\).
