# Isolation of the consecutive Lind–Singmaster rows

Suppose that two left-half coefficients satisfy

$$A=\binom nk=\binom{n+1}{k-1},\qquad 1\le k\le n/2.$$

If $n\ge100$ and $100h^2\le n$, the only occurrences of $A$ in the left half of the rows from $n-h$ to $n+h$ are the two displayed positions that fall in this interval. Moreover, the diagonal with fixed row plus column $n+k$ contains exactly these two occurrences throughout Pascal's triangle. Both conclusions apply to the entire Lind–Singmaster family.

## The exact diagonal identity

Put $u=n-k$ and $F(t)=\binom{n+t}{k-t}$. Cancellation of factorials gives

$$
 R_t=\frac{F(t+1)}{F(t)}
 =\frac{(n+t+1)(k-t)}{(u+2t+1)(u+2t+2)}.
$$

The tie says $k(n+1)=(u+1)(u+2)$. Subtracting the numerator from the denominator of $R_t$ now gives exactly $t(5u+5t+7)$. At every valid diagonal step, $u+2t\ge0$, so the second factor is positive. Therefore $F$ increases strictly up to $F(0)$, has $F(0)=F(1)$, and then decreases strictly. This proves the global diagonal assertion.

## A square-root band with an explicit constant

The tie implies $n/3\le k\le 2n/5$ when $n\ge100$. For the lower bound, $k<n/3$ would imply $k(n+1)<n(n+1)/3<4n^2/9<(u+1)(u+2)$. For the upper bound, $k>2n/5$ would imply $k(n+1)>2n(n+1)/5>(3n/5+1)(3n/5+2)>(u+1)(u+2)$. The middle inequality follows by expansion for $n\ge100$.

Take $h\ge1$ with $100h^2\le n$. Then $h\le n/100$, $3n/5\le u\le 2n/3$, and every column $k-t+1$ with $|t|\le h$ lies in the left half of row $n+t$. For an outward step to the right from $i\ge0$,

$$
 0\le 1-R_i
 =\frac{i(5u+5i+7)}{(u+2i+1)(u+2i+2)}
 \le\frac{5i}{u+2i+1}\le \frac{9i}{n}.
$$

For an outward step to the left ending at $-v$, $1\le v\le h$,

$$
 0\le1-\frac1{R_{-v}}
 =\frac{v(5u-5v+7)}{(n+1-v)(k+v)}
 \le\frac{11v}{n}.
$$

Indeed the denominator is at least $(99n/100)(n/3)$, while $5u+7\le(10/3+7/100)n$. On either side $F(t)/A$ is a product of such outward ratios. For factors $1-x_i$ between zero and one, induction gives $\prod(1-x_i)\ge1-\sum x_i$. Consequently

$$
 \frac{F(t)}A\ge1-\frac{11h(h+1)}{2n}
 \ge1-\frac{11h^2}{n}\ge\frac{89}{100}.
$$

In the same row, the coefficient one column to the right of $F(t)$ is larger by the factor

$$
 \frac{u+2t}{k-t+1}\ge\frac{(3/5-2/100)n}{(2/5+1/100+1/100)n}
 =\frac{29}{21}>\frac43.
$$

It is thus strictly greater than $A$. At $t\notin\{0,1\}$ the two adjacent coefficients bracket $A$ strictly, which excludes every left-half column by the strict increase up to the center. The two tied rows each have exactly one left-half occurrence. The case $h=0$ follows directly from strict increase.

## Distinct identities with general shifts

There is also an elementary obstruction for any pair of shift sizes. Fix positive integers $g,v$ and take consecutive lattice points along the line with step $(g,-v)$. The ratio of consecutive coefficients at $(r,c)$ is

$$
 \prod_{i=1}^{g}\frac{r+i}{r-c+i}\;
 \prod_{i=1}^{v}\frac{c+1-i}{r-c+g+i}.
$$

On taking the next step, each factor of the first product decreases strictly. Cross-multiplication gives the positive difference $gc+v(r+i)$. In the second product, the numerators decrease and the denominators increase. Thus consecutive ratios decrease strictly throughout the valid part of the line. Three distinct positions of one value cannot lie on such a line, since the sequence strictly increases and then strictly decreases with at most two tied adjacent maxima. In particular, if three left-half occurrences lie in equally spaced rows, the column drop over the second gap must be strictly smaller than that over the first. Otherwise the extrapolated second step has fallen strictly below the common value and moving its column further left decreases the coefficient. Distinct proper occurrences in increasing rows have strictly decreasing columns by monotonicity in rows and left-half columns.

For arbitrary gaps, a useful elementary inequality is

$$
 A=\binom mk=\binom{m+H}{l},\quad 1\le l<k\le m/2
 \quad\Longrightarrow\quad m+H+1\le (H+2)k.
$$

Set $B=\binom{m+H}{k-1}\ge A$ and $L=m-k+1$. Summing Pascal's recurrence and bounding each summand by its value in row $m+H$ gives

$$B\le\binom{m}{k-1}+H\binom{m+H}{k-2}.$$

On multiplying by $L$, the first term is $kA\le kB$. The second is at most $H(k-1)B$ since $L\le m+H-k+2$ and $(m+H-k+2)\binom{m+H}{k-2}=(k-1)B$. Cancelling $B>0$ gives the claimed inequality.

Now fix $2/3<\beta<1$. For all sufficiently large $A$, there can be at most **one pair** of left-half occurrences with row gap $1\le H\le m\exp(- (\log m)^\beta)$, measured at its smaller row $m$. In particular, no two distinct patterns of bounded row gaps can overlap at infinitely many values, even allowing the column offsets to vary. To see this, put $E=\exp((\log m)^\beta)$ and choose $2/3<\alpha<\beta$. For sufficiently large $m$, $H+2\le 2m/E$ so $k\ge E/2$ by the row-gap inequality. The bounds $2^k\le A\le(m+H)^l$ imply $l\ge k\log 2/\log(2m)$. Both $k$ and $l$ therefore exceed $\exp((\log(2m))^\alpha)$ for sufficiently large $m$. Both positions qualify for the interior theorem's two available left-half positions. Any second distinct pair would require a third such position. Since $A\le 2^m$, large $A$ indeed forces large $m$. [Matomäki et al., Theorem 1.3](https://arxiv.org/abs/2106.03335)

## Checks and the asymptotic exterior

The file `Erdos849LindBand.py` verifies the signed polynomial identity with direct integer binomial coefficients in the first three family members and computes the two bracketing coefficients by exact rational multiplication in the first eight. In lower row $10{,}803{,}703$ the brackets exclude every additional occurrence between offsets $-1132$ and $1134$. The first offsets at which this bracketing test fails are $-1133$ and $1135$. An actual equality at either endpoint would require an additional test.

The entire infinite family can also be classified within **10,000 rows** of its lower row $n$. For the first eleven members, running `python Erdos849LindBand.py --radius 10000` walks through the adjacent coefficients on each row using exact rational numbers. It finds only two extra positions, both for the first value $3003$. They are $(78,2)$ and the edge position $(3003,1)$. Starting with index 12, $n\ge23{,}843{,}770{,}273>100\cdot10000^2$, so the square-root theorem covers every remaining member. The finite computation updates $\binom mj/A$ by the standard factorial ratios for a horizontal or vertical step and maintains the largest left-half column with coefficient at most $A$. Moving toward smaller rows stops as soon as the central maximum falls below $A$.

The Lean declarations `Erdos849LindDiagonal.unique_on_diagonal` and `Erdos849LindDiagonal.earlier_column_bound` verify the full-diagonal conclusion and the general integer row-gap inequality. The square-root band and its analytic consequences above are ordinary mathematical proofs.

For an asymptotic restriction on any extra row $m$, fix $2/3<\alpha<1$. For sufficiently large $A$, there are at most two left-half occurrences satisfying $\exp((\log m)^\alpha)\le j\le m/2$. Both Lind positions meet this criterion for large $n$, since $k$ is proportional to $n$. Any extra position must satisfy $j<\exp((\log m)^\alpha)$. [Matomäki, Radziwiłł, Shao, Tao and Teräväinen, Theorem 1.3](https://arxiv.org/abs/2106.03335)

The elementary bounds $2^{n/3}\le 2^k\le(n/k)^k\le\binom nk=A\le m^j$ now imply

$$
 \log n+\log((\log 2)/3) < (\log m)^\alpha+\log\log m.
$$

Thus for every $0<c<1$ and all sufficiently large family rows, any extra row satisfies $m>\exp(c(\log n)^{1/\alpha})$. In particular it exceeds every fixed power of $n$. This leaves open the existence of proper occurrences in arbitrarily remote, shallow columns, including column 2. The square-root result gives an explicit threshold and the exact local bracketing, independently of the interior theorem.
