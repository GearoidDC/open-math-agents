# Deep columns of the eleventh Lind–Singmaster value

Let $N=3478759200$, $K=1328767775$ and $A=\binom NK$. The value has 1,004,713,714 decimal digits. In every admissible column $j\ge63,319,921$, its only occurrences are $(N-1,K+1)$ and $(N,K)$. The argument also restricts the rows to check for smaller columns.

## Covering rows with multiples of primes

Suppose all prime divisors of a positive integer $A$ are at most $N$. Let $E$ be a prime, let $Q$ be the first prime larger than $N$, and suppose every gap between consecutive primes up to $E$ is at most $G$. Assume $\lfloor E/2\rfloor-G>Q$. For any column $G\le j\le N$, an admissible row $m$ of $A$ cannot satisfy

$$Q\le m\le E\lfloor j/G\rfloor.$$

Indeed put $h=\lceil m/E\rceil$ and $x=\lfloor m/h\rfloor$. For $m\le E$ we have $h=1$ and $Q\le x\le E$. For $m>E$ we have $\lfloor E/2\rfloor\le x\le E$. Let $p$ be the greatest prime at most $x$. Thus $p>N$ and $0\le x-p\le G-1$. Writing $m=hx+r$ with $0\le r<h$ gives

$$0\le m-hp=h(x-p)+r\le hG-1<j.$$

The numerator of $\binom mj$ contains $hp$. Since $p>N\ge j$, division by $j!$ preserves this prime factor, contrary to the hypothesis on $A$.

In this application $A\mid N!$ and every admissible column satisfies $2^j\le\binom mj=A\le2^N$, so $j\le N$. Use $E=3999999999999999887$ and $G=1476$ from the published computation of all gaps between primes below $4\cdot10^{18}$. Its authors list 1,476 as the largest gap. The verifier proves $E$ prime using successively certified prime factors of $E-1$ and rejects all larger odd candidates below the published cutoff by Fermat witnesses. [Oliveira e Silva, Herzog and Pardi, gap enumeration and maximum](https://sweet.ua.pt/tos/gaps.html)

Prime certification uses the following elementary test. If a prime $q\mid n-1$ satisfies $q^2>n$, $5^{n-1}\equiv1\bmod n$, and $\gcd(5^{(n-1)/q}-1,n)=1$, every prime factor $\ell$ of $n$ has $q$ dividing the order of 5 modulo $\ell$. Thus $\ell\ge q+1>\sqrt n$, proving primality. The chain uses $2712263549$ (trial division), $181818181818181813$, and then $E$.

## The cutoff

Set $M(j)=E\lfloor j/G\rfloor+1$ and $J=63319921$. The integer log comparisons in the verifier give

$$30<\log\binom{M(J)}{J}-\log A<31,\qquad
-6<\log\binom{M(J-1)}{J-1}-\log A<-5.$$

Here $M(J)-1=171595999999999995152413$. For any admissible occurrence with $j\ge J$, a row $m\ge M(J)$ would give $\binom mj\ge\binom mJ\ge\binom{M(J)}J>A$. All smaller rows from $Q$ upward are covered by the prime-multiple result because $M(j)\ge M(J)$. This is the first column where the displayed comparison works, since both arguments of the binomial increase on these left-half ranges.

The prime $3478759199$ lies in the defining numerator of $A$ and exceeds $K$, so every row of $A$ is at least this prime. Trial division gives $Q=3478759213$. In each remaining row $3478759199\le m<Q$ the verifier computes the exact ratio $\binom mK/\binom NK$ by factorial cancellation. It uses adjacent-column ratios until it crosses one. Strict increase in the left half of the row shows that it finds every equality. Exactly the two stated proper occurrences remain.

## Rational verification of the logarithms

For positive integers $n$ define $f(n)=\log(n!)-(n+\tfrac12)\log n+n$. With $z=1/(2n+1)$,

$$0<f(n)-f(n+1)=\sum_{i\ge1}\frac{z^{2i}}{2i+1}
\le\frac{z^2}{3(1-z^2)}=\frac1{12n(n+1)}.$$

For any common $D\ge n$ this gives $0\le f(n)-f(D)<1/(12n)$. In a log ratio of two binomials, the three positive and three negative factorials cancel the same constant $f(D)$, where $D$ is the largest factorial argument. Thus each signed $\log(n!)$ can use the enclosure between $(n+\tfrac12)\log n-n$ and that quantity plus $1/(12n)$, reversing endpoints for negative signs.

To enclose $\log n$, write $n=2^e u$ with $1\le u<2$. Both $\log 2$ and $\log u$ use $2\sum_{i\ge0}z^{2i+1}/(2i+1)$ with $0\le z\le1/3$. After 70 terms the positive tail is at most $2z^{141}/(141(1-z^2))$. Rational arithmetic and outward rounding to multiples of $2^{-192}$ suffice. A positive control uses $\binom{15}{5}=\binom{14}{6}$. Comparing $A$ with the anchor $\binom42=6$ independently checks its decimal digit count.

Run **python Erdos849LindElevenDeep.py** using the Python standard library. The prime-gap maximum is a published theorem input. Verification of the column cutoff and the local rows requires no floating-point library.
