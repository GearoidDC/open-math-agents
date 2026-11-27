# Prime gaps containing repeated rows

Let $A>1$, let $P$ be its largest prime divisor, and let $Q$ be the next prime. An admissible occurrence has $A=\binom nk$ and $1\le k\le n/2$. Its numerator block consists of the integers in $(n-k,n]$.

**All occurrences whose numerator block contains a prime are in the single gap $P\le n<Q$.** Every row in a later prime gap has a wholly composite numerator block. If $P^2\mid A$, every occurrence has a wholly composite block.

Indeed, a prime in the block exceeds $k$, so divides $A$. If the block contains any prime, the greatest prime at most $n$ is in the same block and must equal $P$. Conversely $P\le n$ since $A\mid n!$. If $n<Q$, Bertrand's postulate gives $n<2P$, so $P\mid A$ is possible only if the numerator block contains $P$ itself. It then occurs just once in $n!$. This proves the assertions, including for the edge column.

## A second row in any later gap forces an Andrica violation

Suppose two distinct occurrences lie at rows $n$ and $n+H$ in a later consecutive-prime gap $[r,q)$, where $r>P$. Write their decreasing columns as $k>j$, put $s=n-r$ and $g=q-r$. Since the earlier block contains no prime, $k\le s$. The integer row-gap inequality $n+H+1\le(H+2)k$ gives

$$r\le (H+1)(s-1),\qquad 4r\le(H+s)^2\le(g-1)^2.$$

Thus $\sqrt q-\sqrt r\ge1$. This is a necessary condition on the actual endpoints at all heights. The integer proof also applies to any prime $r\le n$ that does not divide $A$, giving $4r\le(n+H-r)^2$ without requiring the two rows to lie in a common gap.

A stronger bound counts all $z\ge2$ occurrences in a later gap. Write $t=q-r-1$, and let $n$ and $n+H$ be the earliest and latest occupied rows. Write their columns as $k,k-v$. Then $v\ge z-1$, $k\le s$, $u=n-k\ge r$, and $H+s\le t$. The factorial ratios give

$$ (u+1)^v u^H\le k^v n^H,\qquad
v\log(u/k)\le H\log(n/u)\le Hk/u.$$

For the first inequality increase the row by $H$ at fixed column $k$, gaining at most $(n/u)^H$, and then decrease the column by $v$, gaining at most $(k/(u+1))^v$. Since Bertrand's postulate gives $t<r$, these inequalities imply

$$\boxed{\quad 4(z-1)r\log(r/t)\le t^2.\quad}$$

In fact $(z-1)r\log(r/t)\le Hs\le t^2/4$. A later gap occupied twice must therefore have length at least $(\sqrt2-o(1))\sqrt{r\log r}$ as $r\to\infty$. To see the stated constant, if $t>2\sqrt{r\log r}$ it already suffices. Otherwise $\log(r/t)\ge(\log r-\log\log r)/2-\log 2$.

## When the gap above $P$ has at most two occupied rows

Let $G\ge1$ be an integer. Suppose every integer $x$ with $P/2\le x<2P$ has a prime in $[x-G,x]$. If $P\ge30G^3$, then **at most two rows of $A$ have a prime in their numerator blocks**. In particular a five-row value satisfying this test requires at least two wholly composite proper numerator blocks.

Suppose three prime-containing rows exist and denote the first by $(n,k)$. For either later row write $(m,j)=(n+h,k-v)$ with $h,v>0$. As $P$ is the greatest prime at most $m$, the local gap bound gives $h\le m-P\le G$. Put $u=n-k$, $w=m-j$. Both blocks contain $P$, so $w<P\le n$. Take a prime $b$ in $[w-G,w]$ using $P/2\le w<2P$. If $b>u$ and $2b>m$, it is a prime of the first block but neither $b$ nor a positive multiple of it lies in the second. Its divisibility of $A$ would then be impossible. Thus $b\le u$ or $b\le m/2$. In either case $b\le u+h$, so $w\le u+h+G$ yields $v\le G$.

Set $L=\log(n/u)$ and $M=\log(u/k)$. For a tie with shifts $h,v$, exact factorial cancellation gives

$$ e=hL-vM=
\sum_{i=1}^{h+v}\log(1+i/u)
-\sum_{i=1}^h\log(1+i/n)
-\sum_{i=0}^{v-1}\log(1-i/k). $$

Here $e>0$ since $u<n$ and all contributions except the middle sum are nonnegative after combining the first $h$ terms. Also $e\le10G^2/n$. The first sum is at most $(2G)(2G+1)/(2u)\le6G^2/n$. To bound the last sum, first consider $k\le n/3$. The slope inequality above gives $v\log 2\le h k/u$, so $v\le3hk/n$ and $v\le k/2$ since $n\ge6G$. Hence $v^2/k\le3G^2/n$. If $k\ge n/3$, the same two conclusions follow from $v\le G$ and $n\ge6G$. In either case the last sum with its minus sign is at most $v(v-1)/(2(k-v+1))\le v^2/k\le3G^2/n$ by $-\log(1-x)\le x/(1-x)$.

Apply this estimate to both later points $(h_i,v_i)$, $i=1,2$. For $D=h_1v_2-h_2v_1$ one has $LD=e_1v_2-e_2v_1$ and $MD=e_1h_2-e_2h_1$. The absolute values of the right sides are at most $10G^3/n$. At least one of $L,M$ exceeds $1/3$, since $k\ge n/3$ gives $L\ge\log(3/2)$ and $k\le n/3$ gives $M\ge\log2$. Therefore $|D|<30G^3/n\le1$, so the three lattice points are collinear.

This is impossible. Along a primitive integer step $(a,-b)$ with $a,b>0$, the ratio between successive coefficients at $(x,y)$ is

$$\prod_{i=1}^a\frac{x+i}{x-y+i}\prod_{i=1}^b\frac{y+1-i}{x-y+a+i}.$$

Each factor strictly decreases on taking another step whenever the three lattice positions are valid. For a factor in the first product, cross multiplication gives the positive difference $ay+b(x+i)$. Strictly decreasing adjacent ratios permit each value at most twice.

## Concrete and asymptotic consequences

* The published prime-gap maximum 1,476 below $4\cdot10^{18}$ gives the two-prime-containing-row bound, for instance, for **every** integer $A$ whose largest prime divisor lies between $10^{11}$ and $10^{18}$. This bound is independent of $A$'s magnitude. The local hypothesis is checked well within the published interval since $2P\le2\cdot10^{18}$ and $30\cdot1476^3<10^{11}$. [Oliveira e Silva, Herzog and Pardi, computational results](https://sweet.ua.pt/tos/gaps.html)
* Every later gap with right endpoint $q\le4\cdot10^{18}$ holds at most one occurrence for any $A$. For $r\ge10^6$, $(1476-1)^2<4r$ already suffices. For smaller $r$, direct enumeration to $2\cdot10^6$ verifies the integer inequality for every consecutive pair. Run `python Erdos849PrimeWindowCheck.py` to reproduce this finite check. [Published upper-range data](https://sweet.ua.pt/tos/gaps.html)
* For sufficiently large $A$, at most one prime gap anywhere contains a pair of its rows, and no gap contains three. The Baker–Harman–Pintz estimate gives $H=O(n^{0.525})$ for any two rows in the same gap. Then the row-gap inequality gives $k\gg n^{0.475}$ in the earlier row; the other column satisfies $j\ge k\log 2/\log(n+H)$ since $2^k\le\binom nk\le(n+H)^j$. Thus both points qualify for the at-most-two left-half interior theorem. This applies uniformly for sufficiently large $A$ since $A\le2^n$. In particular a large five-row value has proper rows in at least three distinct prime gaps, including at least two wholly composite proper blocks. [Baker, Harman and Pintz](https://doi.org/10.1112/plms/83.3.532) [Matomäki, Radziwiłł, Shao, Tao and Teräväinen](https://arxiv.org/abs/2106.03335)

The local characterization, the upper-half square obstruction, the lower-endpoint prime test, the column-span bound, the Andrica-type integer inequality, and the integer slope inequality are in `Erdos849PrimeWindow.lean`. The logarithmic bounds, determinant argument and quoted external results are ordinary mathematical proofs.
