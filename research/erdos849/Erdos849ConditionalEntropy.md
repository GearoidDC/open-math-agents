# Bounds from noisy linear observations of the polynomial coefficients

The pattern with columns $3,5,7,8$ requires at least 41 distinct prime divisors for $a\ge10^{185}$. The pattern with columns $5,6,7,8$ requires at least 41 for $a\ge10^{170}$. Both use complete individual prime assignments in the pairs $(5,8)$ and $(5,7)$. [Five–eight assignments](Erdos849FiveEightRawBranches.md) · [Five–seven assignments](Erdos849FiveSevenCells.md)

Let $D_t$ be independent random variables uniform on the integer intervals $[0,c_t]$ in the certificate. Write $P_t$ for the corresponding products of integer-valued row polynomials, and $Y_s=\sum_t P_t(s)D_t$ for their values on an offset tuple $s$. For the set $S$ of occupied tuples, the map from the digits $D$ to $(Y_s)_{s\in S}$ is injective. Indeed, equality at every occupied tuple implies congruence of the two evaluations at the actual binomial rows modulo $a/\gcd(a,420)$. The complete digit range has real diameter less than $a/420$, and the largest differing weight dominates all smaller terms. The checker revalidates these strict inequalities at the stated cutoff using bounds valid under each coordinate reflection. [Polynomial bounds and digit-box proof](Erdos849PositionEntropy.py)

Use natural logarithms. Put $H=\operatorname{diag}(c_t(c_t+2))$, which is twelve times the covariance matrix of $D$. The certificate supplies an integer matrix $L$ and a positive diagonal matrix $N$. Introduce a Gaussian vector $\xi$ independent of $D$, with covariance $N/12$, and observe $Z=LD+\xi$. Set $G=N+LHL^\top$, $\delta=\det G$ and $\nu=\det N$. Gaussian maximal differential entropy gives

$$
I(D;Z)=h(Z)-h(\xi)\le\tfrac12\log(\delta/\nu).
$$

For a grid point $s$, let $v=(P_t(s))_t$ be a column vector and $b=LHv$. The possible values of $Y_s$ lie in an integer interval containing at most $W_s=1+\sum_t c_t|v_t|$ integers. Its expected conditional variance given $Z$ is at most the mean squared error of a centered linear predictor using coefficients $G^{-1}b$. Consequently

$$
1+12\,\mathbb E[\operatorname{Var}(Y_s\mid Z)]
\le V_s'=1+v^\top Hv-b^\top G^{-1}b.
$$

Add an independent random variable uniform on $[-1/2,1/2]$ to $Y_s$. Its conditional differential entropy is exactly the conditional discrete entropy of $Y_s$, since the translated intervals have disjoint interiors. Gaussian maximal differential entropy at fixed variance, followed by Jensen's inequality, gives

$$
\exp(2H(Y_s\mid Z))\le\min(W_s^2,(\pi e/6)V_s')
\le B_s/(40\delta),\qquad
B_s=\min(40\delta W_s^2,57\delta V_s').
$$

The last constant follows from $\pi<22/7$ and $e<68/25$. The checker forms the integer adjugate of $G$, verifies its product identity, and computes every $B_s$ with integers.

By injectivity, the entropy of the observation vector equals $\log\prod_t(c_t+1)$. Data processing and conditional subadditivity bound it above by $I(D;Z)+\sum_{s\in S}H(Y_s\mid Z)$. Apply this inequality for each of the sixteen coordinate reflections of the polynomial basis. A reflection replaces $P_t(s)$ by $\epsilon_tP_t(g(s))$ for a sign $\epsilon_t$ depending only on the degree tuple and reflection. Multiply column $t$ of $L$ by the same sign in that experiment. This preserves $G$ and gives the same $B_{g(s)}$ at the reflected grid position. Thus, if $|S|=40$, a necessary condition is

$$
\left(\nu\,\left[\prod_t(c_t+1)\right]^2(40\delta)^{40}\right)^{16}
\le \delta^{16}\prod_{s\in S}\prod_g B_{g(s)}.
$$

Exactly forty distinct prime divisors give exactly one occupied tuple for each of the forty $(5,8)$ position pairs. For each fifth-column offset, its eight tuples must cover all seven seventh-column offsets. They must also cover all three third-column offsets in the first pattern, or all three reflected sixth-column blocks in the second. The dynamic program tracks both sets. For each tuple score $w$ it uses the bit length of $w^8$ as a strict upper bound on $8\log_2 w$. Comparing eighth powers of the two sides gives an integer check. At both stated heights the upper bound violates the necessary condition. [Shallow block coverage](Erdos849CellSieve.md)

The replay uses the Python standard library and needs no numerical optimization package. [Exact verifier](Erdos849ConditionalEntropy.py) · [Integer certificate matrices](Erdos849ConditionalEntropy.json)

~~~sh
python -B Erdos849ConditionalEntropy.py
~~~
