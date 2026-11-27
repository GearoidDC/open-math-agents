# The integers immediately below and above a common value

If either four-column pattern occurs, the preceding integer has at least four distinct prime divisors and the following integer has at least three. These bounds concern the neighbors themselves. They follow from just two columns at a time and explicit divisor estimates.

More precisely, let $a\ge 10^{128}$ be a common admissible binomial value. Columns 3 and 8, or columns 6 and 8, imply $\omega(a-1)\ge4$. Columns 5 and 7 imply $\omega(a+1)\ge3$. The existing search through $10^{128}$ covers smaller values of the two four-column patterns. [Finite search](Erdos849Focused128.md)

## Extracting a divisor from a numerator

Write $b=a-1$ or $a+1$. We use integer factorizations $k!b=dG(d)$, where $g=|G(0)|>0$.

- For $b=a-1$ take $d=n-k$. The constant $g$ is the derivative of the falling factorial at $k$, namely $k!\sum_{j=1}^k1/j$.
- For $b=a+1$ and odd $k$ take $d=n+1$. The root at $n=-1$ gives the same absolute derivative.
- For $b=a-1$ and even $k$ take $d=(n-k)(n+1)$. Pairing the numerator terms writes the falling factorial as $\prod_{j=0}^{k/2-1}(d+(k-j)(j+1))$. Subtracting $k!$ and dividing by $d$ gives $G(d)$ with $g=(k!/(k+1))\sum_{j=1}^k1/j$.

Form $V$ by taking the full power of each prime in $b$ for which $v_p(d)>v_p(g)$. Thus $V$ and $b/V$ are coprime. If $v_p(d)>v_p(g)$ then $v_p(G(d))=v_p(g)$, so $v_p(b)=v_p(d)+v_p(g)-v_p(k!)$. At each other prime we omit at most $v_p(g)$ powers from $d$. Consequently

$$d/L\le V\le A d,\qquad
L=\prod_{p\mid gk!}p^{\max(v_p(g),\,v_p(k!)-v_p(g))},
\qquad A=g/\gcd(g,k!).$$

## Four primes in the preceding integer

For column 8 use the paired factors. Its divisor $V_8$ satisfies $V_8\le761d\le48704a^{1/4}$. Indeed if $z=(k!a)^{1/k}$ then $z\le n\le z+k-1$, and at the stated height $n-k\ge z/2$ and $n+1\le2z$.

The divisor $V_8$ contains at least two distinct primes. Put $T=\operatorname{lcm}(8!,9g,9)$, with $g=12176$. Both $n-8$ and $n+1$ exceed $T$. Each therefore has a prime valuation greater than the corresponding valuation of $T$. The two primes are distinct because the factors differ by nine. Each qualifies for $V_8$ and has positive valuation in $a-1$.

For column 3 take $d=n-3$, with $(L,A)=(66,11)$. For column 6 take the paired $d$, with $(L,A)=(1260,7)$. For either available column, the resulting divisor $V$ of $b=a-1$ satisfies

$$a^{1/3}/2520\le V\le300a^{1/3}.$$

For $a\ge10^{128}$ these inequalities give $V_8<V<b/V_8$. If $b$ had at most three prime divisors, the complement $b/V_8>1$ would consist of exactly one full prime power. A product of full prime powers of $b$ that is smaller than $b/V_8$ must then divide $V_8$. The strict inequality $V>V_8$ rules this out.

## Three primes in the following integer

In columns 5 and 7 take $d=n+1$ with $b=a+1$. For $k=5$ we have $(L,A)=(8220,137)$, and for $k=7$ we have $A=363$. In column 5, $2a^{1/5}<n+1<4a^{1/5}$, and in column 7, $n+1<4a^{1/7}$. The divisor estimates give

$$1<V_7<V_5,\qquad V_7V_5<a+1.$$

For the strict middle comparison it suffices that $4\cdot363\cdot8220<2a^{2/35}$. With two distinct prime factors, the only two proper divisors greater than one formed from full prime powers are complementary. Their product would equal $a+1$. With fewer prime factors there cannot be two such divisors.

Combining these results with the 32-prime bound shows that $(a-1)a(a+1)$ has at least **38 distinct prime divisors**, or at least 39 when $a$ is even. Consecutive integers are coprime, and the only possible common prime of $a-1$ and $a+1$ is two. [32-prime bound](Erdos849HostCount.md)

The standard-library verifier checks the constants by integer arithmetic, replays the divisor construction on small rows, and checks the valuation changes at primes dividing $gk!$. Run `python -B Erdos849NeighborDivisors.py` with assertions enabled.
