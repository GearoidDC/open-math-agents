# Excluding a whole interval by real interpolation

No common value in columns $3,5,7,8$ belongs to

$$\left[10^{180},\,10^{180}(20001/20000)^{840}\right].$$

The right endpoint is about $1.0429\cdot10^{180}$. This separates a part of the surviving interval for a putative example with exactly 40 primes. The exclusion applies to every prime factorization. It uses three integer polynomials and 85 rational interpolation nodes. The standard-library verifier checks every real and finite-field bound. [Verifier](Erdos849RealInterval.py) · [Certificate](Erdos849RealInterval.json)

Set $A=10^{180}$, $g=840$, $d=20000$ and $a=A u^g$ with $1\le u\le1+1/d$. Write $n_k(u)$ for the positive real solution of $(n_k)_k=k!Au^g$ with $n_k>k-1$. The certificate supplies three integer polynomials $F$ in these four coordinates. Each has absolute value less than one on the whole interval, so each must vanish at any integer solution. Enumeration modulo 11 shows that none of the tuples satisfying the four binomial equations modulo 11 makes all three polynomials vanish.

## Bounding the derivatives

On the complex disk of radius $R=1/8$ around any point of the real parameter interval, put $w=(k!A)^{1/k}z^{g/k}$. The checker verifies $|w|>100k^4$ throughout the disk from $|z|\ge7/8$. Consider the map

$$v\longmapsto w\exp\left(-\frac1k\sum_{j=0}^{k-1}\log(1-j/v)\right).$$

On $|v-w|\le4k^2$ use the power-series logarithm. Both $|v|$ and $|v-j|$ exceed $|w|/2$. The exponent has absolute value at most $2k/|w|$, by $|\log(1-t)|\le2|t|$ for $|t|\le1/2$. Its derivative is bounded by $2k/|w|^2$. Consequently the map stays in this disk and has derivative of absolute value at most $4k/|w|<1/2$. Iterating from $v=w$ gives a holomorphic solution of $(v)_k=w^k$. At real positive $z$ it agrees with the positive row by uniqueness.

Thus $|n_k(z)|\le |w|+4k^2$. For each monomial $m_i$ the checker multiplies coordinate bounds, using $|z|\le1+1/d+1/8$, to obtain an integer upper bound $M_i$. Cauchy's estimate bounds the $J$th real derivative of $m_i$ by $J!M_i/R^J$.

## Bounding the polynomial between samples

The nodes include both endpoints. For consecutive nodes $t_i,t_{i+1}$, bound the numerator factors in each Lagrange cardinal polynomial by $\max(|t_i-t_h|,|t_{i+1}-t_h|)$. Dividing by the exact product of node differences, summing and taking the maximum over intervals bounds the Lebesgue constant by 545. The bound is invariant under the affine rescaling used to store the nodes. Lagrange's real interpolation remainder for each monomial is at most $M_i(8/d)^J$ since the interval width is $1/d$.

At each node, integer arithmetic brackets every real row to precision $1/D$, where $D=2^{1800}$. Scaling a monomial by $S=2^{512}$, rounding the rows down and then rounding the product down costs less than two units. The real-coordinate part follows from the product difference estimate and $S(\sum e_k)M_i<D$, checked for each exponent tuple. The verifier multiplies the maximum sample bound for $F$ by the Lebesgue bound and adds $\sum_i|c_i|M_i(8/d)^J$. All three results are strictly below one. Run `python -B Erdos849RealInterval.py` to reproduce the exclusion.
