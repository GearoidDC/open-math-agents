# Nonvanishing of three numerator subset logarithms

Let \(K=(3,5,7)\) or \((5,6,7)\). Suppose an integer \(a\ge10^{128}\) has a representation \(a=\binom{n_k}k\) in each column. In each numerator choose an arbitrary nonempty proper set \(S_k\subset\{0,\dots,k-1\}\); put \(s_k=|S_k|,\ \alpha_k=s_k/k,\ X_k=\prod_{i\in S_k}(n_k-i)\). Let \((c_k)\) be a primitive nonzero integer solution of
\[
 \sum c_k=0,\qquad \sum c_k\alpha_k=0 .
\]
Then the positive rational number
\[
 W=\prod_{k\in K}X_k^{c_k}(k!)^{-c_k\alpha_k}
\]
differs from one. Indeed the three reduced denominators of the \(\alpha_k\) are pairwise coprime, so the \(\alpha_k\) are distinct, all \(c_k\ne0\), and from the second equation each \(c_k\alpha_k\) is an integer. The triple is determined up to sign by the cyclic differences of the \(\alpha_k\).

Here is the exact error estimate implemented in [the verifier](Erdos849ComponentMoments.py). At a threshold \(a_0=10^t\), write \(y=a/a_0\ge1\), \(z=n_k-(k-1)/2\), \(v_i=(k-1)/2-i\), \(h_i=1_{i\in S_k}-s_k/k\), \(d=(k-1)/2\). The geometric mean \((k!a)^{1/k}\) lies between \(z-d\) and \(z+d\). Consequently, with \(f=\lfloor(k!a_0)^{1/k}\rfloor,\ l=f-k,\ u=f+k\),
\[
 l\,y^{1/k}\le z\le u\,y^{1/k},\qquad z>2d .
\]
Define \(\delta_k=\log X_k-\alpha_k\log(k!a)=\sum_i h_i\log(1+v_i/z)\), using natural logarithms. Let \(r\) be the first positive degree for which \(\sum h_i v_i^r\ne0\). It lies between 1 and \(k-1\): degree zero has sum zero and the Vandermonde matrix for distinct \(v_i\) is invertible. Set
\[
 A=\frac{|\sum h_i v_i^r|}{r},\qquad E=\frac{2\sum|h_i|\,d^{r+1}}{(r+1)l^{r+1}} .
\]
The geometric-series bound on the Taylor tail after degree \(r\) gives
\[
 \left(A/u^r-E\right)y^{-r/k}\le|\delta_k|
 \le\left(A/l^r+E\right)y^{-r/k}.
\]
The verifier enumerates every subset. For each \((k,s_k,r)\) it keeps the smallest lower constant and the largest upper constant, checking strict positivity of the lower constant. The three exponents \(r/k\) are distinct because their reduced denominators divide different, pairwise coprime \(k\), and \(0<r/k<1\). For each choice of the three orders, the verifier multiplies the lower constant at the smallest exponent by \(|c_k|\) and compares it to the sum of the two similarly weighted upper constants. The ratio bounds in the following table hold already at \(y=1\), so continue to hold at every larger \(y\).

| Columns | Subset-size triples | Threshold \(t\) | Dominant contribution divided by the other two exceeds |
|---|---|---:|---:|
| \(3,5,7\) | all 48 | 128 | 57,765 |
| \(5,6,7\) | all 120 | 128 | 20 |

Therefore \(\log W=\sum c_k\delta_k\ne0\) for every stated subset selection. If the three subsets come from a common cut of the incidence graph of the primes \(p>7\), each \(v_p(X_k)\) is either \(v_p(a)\) in all three rows or zero in all three, and the factorials contain only small primes. Under this additional assumption \(W\) is a nontrivial rational product of powers of \(2,3,5,7\). The numerical dominance check itself requires only the three binomial representations.
