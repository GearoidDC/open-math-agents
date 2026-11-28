# How the prime powers of a common binomial value are distributed

Fix distinct proper columns $k_1,\ldots,k_r$, put $P=\prod_i k_i$, and suppose $a=\binom{n_i}{k_i}$ for admissible rows $n_i\ge 2k_i$. For every $p\mid a$, choose one offset $s_i\in\{0,\ldots,k_i-1\}$ maximizing $v_p(n_i-s_i)$ in each row. Assign the full power $p^{v_p(a)}$ to the tuple $s=(s_1,\ldots,s_r)$. Write $b_s$ for the product assigned to that tuple, taking the empty product to be one.

**Theorem.** There are effectively computable constants $C,A$ depending only on the fixed columns such that every common value $a>A$, every choice at ties, and every one of the $P$ tuples satisfy

$$
\left|\log b_s-\frac{\log a}{P}\right|\le C\sqrt{\log a}.
$$

In particular, for two distinct columns $k,h$, the product in **every individual numerator-term intersection** is between $a^{1/(kh)-\epsilon}$ and $a^{1/(kh)+\epsilon}$ above an effective cutoff for each $\epsilon>0$. The argument applies to noncoprime column indices and to any number of fixed columns. All $P$ cells must eventually be occupied, and the exponent $1/P$ is their average because $\prod_s b_s=a$. The cutoff depends on the columns. This gives a necessary condition on collisions and leaves their full classification open.

## Interpolation at the zero fiber

Set $g_i(X)=\prod_{j=0}^{k_i-1}(X-j)$ and work in

$$
B_{\mathbb Z}=\mathbb Z[t,x_1,\ldots,x_r]/(g_i(x_i)-k_i!t:1\le i\le r).
$$

The monic relations make this algebra free over $\mathbb Z[t]$ with basis $x^e=\prod x_i^{e_i}$, $0\le e_i<k_i$. Over $\mathbb Q(t)$ it is a field of degree $P$ by geometric irreducibility of the simultaneous binomial curve. The critical-value and monodromy proof applies to all sets of distinct columns. Over $t=0$ its $P$ points are the rational tuples of offsets. [Irreducibility and zero fiber, sections 1–3](Erdos849ReciprocalRunge.txt)

Fix a target tuple $s$. For an integer $M\ge1$ take $N=P(M+r)$ and use the monomials

$$
t^j x^e,\qquad 0\le j\le N-M-r,\qquad 0\le e_i<k_i.
$$

There are $P(N-M-r+1)=(P-1)N+P$ of them. At each of the $P-1$ other zero tuples impose the vanishing of the first $N$ Taylor coefficients in the local parameter $t$. These homogeneous rational conditions number $(P-1)N$, so there is a nonzero polynomial $R_N$ in this span satisfying all of them. Its nonzero coefficient vector gives a nonzero element of the algebra by freeness. Each monomial has $j+\sum_i e_i/k_i\le N-M$, which will control its size at integral rows.

We record bounds for this interpolation with constants independent of $M$. At an offset $v$ in column $i$ put $c=g_i'(v)\ne0$. Choose the positive integer $D$ to be the least common multiple of $c^2$ over all columns and offsets. Substitute $x_i=v+cw$ and $t=Du$ in the defining equation and divide by $c^2$. The result has the form

$$
w+\sum_{m=2}^{k_i} h_m w^m=d u,\qquad h_m\in\mathbb Z,\qquad d=k_i!D/c^2\in\mathbb Z .
$$

It uniquely defines $w(u)\in u\mathbb Z[[u]]$ by coefficient recursion. The coefficients have an effective geometric bound. Indeed choose $0<\sigma\le1$ rational so that $\sum_{m\ge2}m|h_m|\sigma^{m-1}\le1/2$, then choose a common rational $0<\rho\le1$ with $|d|\rho\le \sigma/2$ for every branch. The iteration $w\mapsto du-\sum h_mw^m$ is a contraction on $|w|\le\sigma$ for $|u|\le\rho$. It yields the analytic solution there and Cauchy's estimate bounds each Taylor coefficient of the finitely many products $x^e$ by $C_0\rho^{-n}$ in degree $n$, with computable $C_0$. For example, use $\prod_i\max(1,|v_i|+|c_i|\sigma_i)^{k_i-1}$ and take the maximum over tuples.

Use $u$ for the vanishing conditions. The resulting integer matrix has entries bounded by $C_1^N$ for an effective $C_1\ge2$, since multiplying a product by $t^j$ shifts coefficients and multiplies them by $D^j$. A matrix of rank $m$ with more than $m$ columns has an integer kernel vector given by the signed maximal minors of $m$ independent rows on $m+1$ columns containing an invertible minor. If $m=0$ a single basis vector suffices. Since $m\le PN$, the bound $m!(C_1^N)^m$ on each minor lets us take the integer coefficients of $R_N$ to have absolute value at most $\exp(C_2 N^2)$, for an effectively computable $C_2$.

## How the assigned powers control the denominator

Let $p\mid a$, $e=v_p(a)$, and let $v_i$ be the chosen maximizing offset in row $i$. For $j\ne v_i$ the ultrametric inequality gives

$$
v_p(n_i-j)\le v_p(v_i-j).
$$

Summing the right sides gives $v_p(v_i!(k_i-1-v_i)!)\le v_p(k_i!)$. Since $g_i(n_i)=k_i!a$, this proves $v_p(n_i-v_i)\ge e$ even when there is a tie.

Suppose the assigned tuple $v$ differs from $s$, and $e>v_p(D)$. At this point $u=a/D\in p\mathbb Z_p$ and $w_i=(n_i-v_i)/g_i'(v_i)\in p\mathbb Z_p$, as $g_i'(v_i)^2$ divides $D$. The integral series for $w_i(u)$ converges there. It is the unique solution in $p\mathbb Z_p$ because the difference of two solutions factors as their difference times a unit congruent to one modulo $p$. The first $N$ coefficients of $R_N$ vanish at $v$ and all the remaining coefficients in $u$ are integral. Therefore

$$
v_p(R_N(a,n))\ge N(e-v_p(D)).
$$

When $e\le v_p(D)$ this bound follows already from integrality. For primes assigned to $s$ their full power in $a$ occurs in $b_s$. It follows at all primes that

$$
I_s=\frac{D^N b_s^N}{a^N}R_N(a,n_1,\ldots,n_r)\in\mathbb Z .
$$

## Controlling the exceptional zeros and the real size

The determinant $\Delta_N(t)$ of multiplication by $R_N$ in the free basis of $B_{\mathbb Z}$ is a nonzero integer polynomial, since this multiplication is invertible over the field $B_{\mathbb Z}\otimes_{\mathbb Z[t]}\mathbb Q(t)$. If $R_N$ vanishes at a tuple over $t=a$, then $\Delta_N(a)=0$. Indeed evaluation at that tuple yields a nonzero linear functional on the specialized algebra annihilating the image of the multiplication map.

The fixed basis multiplication table has entries in $\mathbb Z[t]$ with computably bounded sums of absolute coefficients. Multiplication by $t^j$ preserves those sums. As $R_N$ has $O_{\boldsymbol k}(N)$ terms of coefficient size at most $\exp(C_2N^2)$, each multiplication-matrix entry has sum of absolute coefficients at most $\exp(C_3N^2)$. Expanding its fixed-size determinant bounds the corresponding sum for $\Delta_N$ by $P!\exp(PC_3N^2)$. The Cauchy root bound for a nonzero integer polynomial now shows that $R_N(a,n)\ne0$ whenever $\log a>C_4 N^2$, with effective $C_4\ge1$ depending only on the columns.

The falling factorial gives $n_i\le (k_i!a)^{1/k_i}+k_i-1$. Applying this termwise to $R_N$ and using the weight bound from interpolation gives

$$
|R_N(a,n)|\le \exp(C_5N^2)a^{N-M}.
$$

Thus for $\log a>C_4 N^2$ the nonzero integer $I_s$ has

$$
1\le |I_s|\le\exp(C_6 N^2)b_s^N a^{-M},
\qquad
\log b_s\ge \frac{\log a}{P}-\frac{r\log a}{N}-C_6N.
$$

The constants can be chosen simultaneously for all $P$ target tuples. For large enough $\log a$, take the largest $N=P(M+r)$ with $M\ge1$ and $N\le\sqrt{\log a/(2C_4)}$. Then $N$ is between one-half and one times this square root, giving the claimed effective lower bound. Subtracting the lower bounds for the other $P-1$ cells from $\log a=\sum_s\log b_s$ yields the upper bound. Every constant used above can be obtained with finite integer arithmetic and rational majorants for logarithms.

## Explicit bounds for individual tuples

Let $H_0,H_1$ denote the binary exponents in the following table. For $a\ge2^{H_0}$ the indicated parameters give $b_s^N\ge 2^{-H_1}a^M$ for **every** tuple. In particular all cells are occupied at each displayed cutoff, since $MH_0>H_1$. The first two rows use individual terms in both columns, including all eight terms of column eight.

| Columns | Cells | $M$ | $N$ | $H_0$ | $H_1$ |
|---|---:|---:|---:|---:|---:|
| 3, 5 | 15 | 1 | 37 | 207,317 | 14,167 |
| 5, 8 | 40 | 1 | 107 | 7,752,962 | 196,389 |
| 3, 5, 7, 8 | 840 | 1 | 3,528 | 119,385,136,082 | 142,213,189 |
| 3, 5, 7, 8 | 840 | 4 | 8,567 | 289,882,098,242 | 345,311,738 |
| 3, 5, 7, 8 | 840 | 8 | 15,288 | 517,210,897,562 | 616,109,286 |
| 5, 6, 7, 8 | 1,680 | 1 | 7,334 | 993,204,186,242 | 591,376,112 |
| 5, 6, 7, 8 | 1,680 | 4 | 17,414 | 2,357,987,027,762 | 1,403,998,851 |
| 5, 6, 7, 8 | 1,680 | 8 | 30,854 | 4,177,695,569,042 | 2,487,494,697 |

For $w(e)=\sum_i e_i/k_i$ include every $t^jx^e$ with $0\le j\le N-M-\lceil w(e)\rceil$. Put $S=\sum_e\lceil w(e)\rceil$. For the tested $N\ge M+r$ this gives $L=P(N-M+1)-S$ unknowns and $Q=(P-1)N$ equations.

For smaller interpolation entries, use the scale $t=Eu$ where $E$ is the least common multiple of $c^2/\gcd(c^2,k_i!)$ over branches. The integral coefficient recursion still works because $c^2\mid k_i! E$. For the denominator bound retain the original $D$. We have $E\mid D$, so $e>v_p(D)$ still gives convergence at $a/E$ and the estimate $v_p(R_N)\ge N(e-v_p(D))$.

To bound the archimedean Taylor coefficients write $g_i(v+z)=\sum_{m\ge1}f_m z^m$ with $f_1=c$. Choose a positive power of two $l$ (allowing $l=1$) such that $2\sum_{m\ge2}m|f_m|l^{1-m}\le|c|$. For $|z|\le1/l$ the contraction in the variable $z$ has derivative norm at most $1/2$. Take $T$ at least $E$ and at least $\lceil 2l k_i!E/|c|\rceil$ on every branch, so the disk $|u|\le1/T$ maps to $|z|\le1/l$. There $|x_i|\le k_i$. With $U=\prod_i k_i^{k_i-1}$ every integer interpolation entry has absolute value at most $UT^N$. Indeed Cauchy's estimate applies to $x^e$ and $E\le T$ absorbs the factor from $t^j$.

Let $b(v)$ be the binary digit count of a positive integer $v$ and put $J=b(U)+Nb(T)$. Use the coefficient cube $\{0,\ldots,2^h\}^L$ where

$$
h=\left\lceil\frac{Q(b(3L)+J)}{L-Q}\right\rceil.
$$

Each of the $Q$ equations takes at most $2L2^J2^h+1\le3L2^J2^h$ integer values on this cube. The number of input vectors exceeds the product of these bounds by the choice of $h$. Subtracting two vectors with identical evaluations supplies a nonzero relation with coefficients of absolute value at most $2^h$.

Finally put $V=\prod_i(2k_i!)^{k_i-1}$ and $W=\prod_i(2k_i)^{k_i-1}$. Multiplication by $x_i$ in the monic basis increases the coefficient sum by a factor at most $2k_i!$, by its defining relation. Hence the basis monomial multiplication operators have norm at most $V$. The bound $n_i\le 2k_i a^{1/k_i}$ gives $|R_N(a,n)|\le L2^h W a^{N-M}$. Explicit allowable exponents are

$$
H_0=2+P\big(b(P)+b(L)+h+b(V)\big),\qquad
H_1=Nb(D)+b(L)+h+b(W).
$$

Indeed $\|\Delta_N\|_1\le P!(L2^hV)^P$, so the Cauchy root bound is strictly below $2^{H_0}$. Integrality of $I_s$ then gives $b_s^N\ge 2^{-H_1}a^M$.

Run the command below to reproduce the table using integer and rational arithmetic. For each prescribed $M$, the program compares the heights for $P(M-1)+S<N\le 3(P(M-1)+S)$. The earlier full-tuple bound for the first four-column pattern was $10^{1,820,000,000,000}$. The present estimates concern fixed tuples. The separate uniform bound for 840 distinct prime divisors in any five-row value is $10^{230,000,000,000,000}$. [Exact calculator](Erdos849PrimePowerCells.py) · [Earlier grid estimates, sections 4 and 5](Erdos849GridHeight.txt) · [All-height grouped results](Erdos849SaturatedCells.md)

~~~sh
python -B Erdos849PrimePowerCells.py
~~~
