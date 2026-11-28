# A large prime separating every choice of half of the sixth and eighth rows

Suppose a positive integer $a$ has admissible representations in columns 5, 6, 7 and 8. Choose any three of the six numerator terms for column 6 and any four of the eight numerator terms for column 8. Let their products be $X$ and $Y$. **After reducing $Y/X$ to lowest terms, its numerator or denominator has a prime divisor greater than 53.**

Equivalently, some prime $p>53$ dividing $a$ has its unique sixth-column and eighth-column terms on opposite sides of the two selections. This holds for all $20\cdot70=1{,}400$ choices, at every height. It excludes a family of possible factorizations across two rows. The proof uses the full four-column pattern.

## Comparing the products

Write $M,N$ for the two row indices in columns 6 and 8. The earlier search gives $a>10^{144}$. Put $t=\log_{10}a$. Every full prime power $p^e$ dividing $a$ satisfies $p^e\le p^{v_p(420)}35519\,10^{(t-128)/36}$. [Height exclusion](Erdos849PatternHeights.md) · [Prime-power bound](Erdos849JointHosts.md)

Let $X',Y'$ be the products of the complementary terms. We have $XX'=6!a$ and $YY'=8!a$. Thus

$$W=\frac{Y^2}{56X^2}=\frac{Y/Y'}{X/X'}\ne1.$$

The inequality follows because 56 is not a rational square. For a block of $2h$ consecutive integers ending at $n$, the ratio between any two complementary half-products has absolute logarithm at most $h^2/(n-2h+1)$. The ratio is largest when the largest $h$ terms are divided by the smallest $h$. Pair terms at distance $h$ and use $\log(1+u)\le u$.

Since $N\ge (8!a)^{1/8}$ and $M\ge (6!a)^{1/6}$, we have $N-7>(7/2)a^{1/8}$ and $M-5>a^{1/6}$. The first inequality follows from $(8!)^{1/8}>11/3$ and $a^{1/8}>10^{18}$. In particular

$$|\log W|\le \frac{16}{N-7}+\frac{9}{M-5}<5\,10^{-t/8},\qquad |W-1|<6\,10^{-t/8}.$$

For the second bound use $e^z-1\le z/(1-z)$ for $0\le z<1$.

## How many primes cross the selections

**At least three distinct primes cross every such cut.** The number rises to four at $a\ge10^{244}$ and five at $a\ge10^{801}$. If the four selected eighth-column offsets sum to 14, at least four primes cross at every height, five at $10^{205}$ and six at $10^{446}$. These counts use the convention that each prime is assigned in each row to its first term of maximum valuation. The proof also counts distinct four-column tuples of assigned positions.

To see this, let $D=YX'-Y'X$. This nonzero integer is divisible by the full $p$-part of $a$ for each prime whose two assigned positions are both selected or both unselected. Let $V$ be the product of the remaining full prime powers. Then $a/V\le |D|$. Dividing by $a$ gives $|D|/a=\sqrt{6!8!}\,|2\sinh((\log W)/2)|<33000a^{-1/8}$. Here $|2\sinh(z/2)|\le |z|\exp(|z|/2)$ and $|z|<5a^{-1/8}$. Hence $V>a^{1/8}/33000$.

If the selected eighth-column offsets sum to 14, so do their complements. In $\log(Y/Y')$ the linear terms of $\log(1-j/N)$ cancel. The Taylor remainders give $|\log(Y/Y')|\le 70/(N-7)^2$, since $\sum_{j=0}^7j^2=140$. Thus $|\log W|\le70/(N-7)^2+9/(M-5)<10a^{-1/6}$, using $a>10^{144}$. This gives $V>a^{1/6}/60000$.

If just $j$ distinct four-column tuples cross, $V\le420\cdot35519^j 10^{j(t-128)/36}$ by the existing bound for all prime powers at the same tuple. Comparing with these two lower bounds gives the stated counts. [Bound for a tuple of assigned positions](Erdos849JointHosts.md)

## Bounding the exponents of a proposed smooth ratio

If $Y/X$ has only primes through 53 after cancellation, write $W=\prod_{p\le53}p^{b_p}$. The exponents at 2 and 7 are odd and all other exponents are even. For $e=v_p(a)$,

$$ |b_p|\le 2(e+v_p(8!))+v_p(56). $$

Indeed the total valuation of a whole numerator is $e+v_p(k!)$ and each selected product divides its whole numerator. This bounds the absolute difference of the two selected valuations. Together with the prime-power bound above it gives $|b_p|<t$ for $t\ge144$, using $35519<2^{16}$ and $\log_2 10<4$. On each smaller interval $t\le U$ the verifier computes each exponent bound by integer powers.

The real-field bound of Matveev applied to $W-1$ gives $\log|W-1|>-10^{45}(1+\log t)$. Indeed we can take field degree 1, at most 16 logarithms and each modified height at most 4, since $p\le53$. The exact numerical constant in the theorem is bounded by $2\cdot30^{19}16^5 4^{16}<10^{45}$. For $t\ge10^{55}$ our upper estimate gives $\log|W-1|<-t/5$. This contradicts the lower estimate since $t/(1+\log t)$ increases for $t>1$. Thus $t<10^{55}$. [Bugeaud, Mignotte and Siksek, Theorem 9.4](https://samirsiksek.github.io/siksek.github.io/papers/fibannalsfinal.pdf)

## Exact lattice calculation

For each interval $L\le t\le U$, the verifier bounds $|b_p|$ by integers $B_p$. Fix a scale $C$, positive integer weights $w_p$, and $d_p$ the nearest integer to $C\log p$. The lattice vector with first coordinates $w_pb_p$ and last coordinate $\sum_p d_p b_p$ must have squared length at most

$$\sum_p (w_p B_p)^2+\left(5C\,10^{-\lfloor L/8\rfloor}+\tfrac12\sum_p B_p\right)^2.$$

The verifier obtains every rounded logarithm with directed integer bounds from the series for $\log((1+z)/(1-z))$, reducing to $0\le z\le1/3$. The supplied change-of-basis matrices have determinant $\pm1$, which is checked before use. The squared Gram–Schmidt lengths are ratios of consecutive leading Gram determinants. If their minimum exceeds the length bound, every nonzero lattice vector is excluded. Otherwise the verifier recursively enumerates the closed ball in Gram–Schmidt coordinates with rational arithmetic, imposing the exponent parities modulo two. At each leaf it compares the rational value of $W$ with 1 by exact integer arithmetic.

| Interval for $t$ | Result |
|---|---|
| $8{,}000$ to $10^{55}$, and $640$ to $8{,}000$ | The length bound excludes every nonzero vector. |
| $256$ to $640$, and $184$ to $256$ | No vector of the required parity lies in the ball. |
| $152$ to $184$, and $144$ to $152$ | Eight and sixteen vectors respectively reached the leaf tests. None satisfied the necessary bounds. |

Run `python -B Erdos849BalancedCuts.py` with assertions enabled. Python's standard library suffices. [Verifier](Erdos849BalancedCuts.py) · [Integer basis certificates](Erdos849BalancedCuts.json)
