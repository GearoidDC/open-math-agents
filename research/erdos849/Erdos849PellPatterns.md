# Large prime factors in the two remaining column patterns

The two patterns are the proper columns $\{3,5,7,8\}$ and $\{5,6,7,8\}$ in the left half of Pascal's triangle. For each pattern the question here is how many **distinct prime divisors greater than 100** a common coefficient must have. The edge occurrence is an additional row. The results use the earlier height and small-column exclusions. [Prior reduction to two patterns](Erdos849EightSmooth.txt) · [Finite height search](Erdos849Focused128.md)

**Both patterns require at least seven distinct prime divisors greater than 100. Every five-row value, with any column pattern, requires at least six.** Indeed the earlier reduction put every potential exception to the six-prime statement in these two patterns. Their simultaneous occurrence remains open.

Subsequent checks use this Pell enumeration to prove seven large primes for every five-row value. Pattern-specific interpolation and an exact row search give at least thirteen for each named pattern. [Thirteen-prime argument](Erdos849RowThreshold.md) [Global seven-prime argument](Erdos849SevenAtAllHeights.md) · [Columns 3, 5, 7 and 8](Erdos849PatternThree.txt) · [Columns 5, 6, 7 and 8](Erdos849PatternSixHost.md)

Lean checks that either four-column pattern supplies five distinct rows, that at most six large primes force two smooth numerator terms in column eight, and that at least 32 prime divisors force seven above 100. It combines these facts with the finite exclusions and the interpolation bound as explicit hypotheses. The continued-fraction enumerations run outside Lean. [Lean source](Erdos849LargePrimePatterns.lean)

For the two patterns, the finite test proves more about the equality case. If exactly seven prime divisors exceed 100, the value is below $10^{5000}$, and precisely one of the eight numerator terms in column eight is 100-smooth. Each of the other seven terms then contains exactly one of the seven larger prime bases. Above the cutoff the interpolation check with cap 32 forces at least 33 prime factors, of which at least eight exceed 100.

## From smooth pairs to a finite list of equations

Suppose $10^{128}\le a=\binom n8<10^{5000}$ and at most six primes greater than 100 divide $a$. A prime greater than 100 divides at most one of the eight consecutive numerator terms and survives the denominator $8!$. Therefore at least two terms, say $A<B$, have all prime factors at most 100. Their gap is at most seven. Put $s=\gcd(A,B)$, $u=A/s$, $v=B/s$ and $e=v-u$. Thus $s e\le7$ and $u,v$ are coprime.

The complete Luca–Najman smooth-neighbor tables supply the normalized pairs with $e=1,2$, including every eligible scaling. For $e=4$ the endpoints are odd and the center $u+2$ is odd. Najman's bound on the largest such center is less than the lower bound on a numerator term, even allowing the additive offset. The only other normalized gaps are $3,5,6,7$. [Smooth-neighbor inputs](Erdos849SmoothNeighbors.md) · [Najman, Theorem 3(a)](https://web.math.pmf.unizg.hr/~fnajman/smooth.pdf)

Let $d$ be the squarefree part of $uv$ and write $uv=dw^2$. Its primes belong to the set of 25 primes at most 100. An odd gap $e=h$ gives $x=u+v$, $y=2w$ and $x^2-dy^2=h^2$. A gap of six gives $h=3$, $x=(u+v)/2$ and $y=w$. In each case $h\in\{3,5,7\}$ and $\gcd(x,y)=1$. Indeed a common prime would divide $h$, whereas $x$ is nonzero modulo $h$ by coprimality of the endpoints. Also $d$ is a nonzero square modulo $h$, since $u\equiv v\not\equiv0\pmod h$. Every prime divisor of $y$ is at most 100.

Since $(n-7)^8\le8!a$ and $(2^{2099}-7)^8>8!10^{5000}$, the search only needs $y\le2n<2^{2100}$. Every numerator term is at least $L=\lfloor(8!10^{128})^{1/8}\rfloor-7$. The required $x$ is at least $L$. For odd gaps, $s\le2$ and $x=u+v>su$; for normalized gap six, $s=1$ and $x=u+3$.

## Exhaustion by continued fractions

For $d>2401$ a solution has

$$\left|\frac{x}{y}-\sqrt d\right|
=\frac{h^2}{y^2(x/y+\sqrt d)}<\frac1{2y^2}.$$

By Legendre's continued-fraction criterion a reduced fraction with this accuracy is a convergent of $\sqrt d$. Squarefree $d\le2401$ are handled separately by exact enumeration in the basis of two consecutive convergents, including the square case $d=1$. [Small-radicand proof and controls](Erdos849PellSmall.md)

One way to see the criterion is to use both finite continued-fraction expansions of the reduced fraction $x/y$. For $y>1$ their preceding convergents have denominators $q$ and $y-q$ strictly between zero and $y$. The open intervals of real extensions run from $x/y$ to the respective mediants with these predecessors, on opposite sides. The distances to the mediants are $1/(y(y+q))$ and $1/(y(2y-q))$, both greater than $1/(2y^2)$. This covers every irrational within the stated accuracy. For $y=1$, the nearest integer is either the zeroth convergent or the next one.

Here is the large-radicand calculation. Put $r=\lfloor\sqrt d\rfloor$. Starting at $(P_0,Q_0)=(0,1)$ the complete quotients have $a_i=\lfloor(r+P_i)/Q_i\rfloor$,

$$P_{i+1}=a_iQ_i-P_i,\qquad Q_{i+1}=(d-P_{i+1}^2)/Q_i.$$

For the convergent $x_i/y_i$, its norm is $(-1)^{i+1}Q_{i+1}$. To see this, substitute the complete quotient $(\sqrt d+P_{i+1})/Q_{i+1}$ after the $i$th convergent. Comparing rational and irrational parts gives $x_i=P_{i+1}y_i+Q_{i+1}y_{i-1}$ and $dy_i=P_{i+1}x_i+Q_{i+1}x_{i-1}$. Subtraction and the determinant identity give the claimed norm. Only odd $i$ can contribute. For $i\ge1$, the equivalent formula $Q_{i+1}=Q_{i-1}+a_i(P_i-P_{i+1})$ avoids a division and uses unsigned word arithmetic. The true $Q_{i+1}$ is positive and less than $2\sqrt d+1$, so its 64-bit residue determines it exactly for these radicands.

The first pass retains every required positive norm before the bound on $y$. It can stop when all eligible norms have appeared, or when it has traversed a full period of even length. In the latter case $i$ is odd and $Q_{i+1}=1$. The conjugate of each complete quotient after the zeroth lies in $(-1,0)$, forcing $P_{i+1}=r$ in this case. From there the state returns to $(r,d-r^2)$ with the same parity as on its first visit. The alternate stopping rule uses lower bounds on consecutive convergent denominators: add and multiply by the exact partial quotient, occasionally shift both right, and accumulate the power of two removed. Rounding down preserves lower bounds. The pass can stop as soon as the scaled lower bound reaches $2^{2100}$.

The second pass takes every retained radicand through the **entire** denominator range with exact multiword integers. At a matching norm it divides the denominator by the 25 permitted primes. For each surviving index, the Python verifier reconstructs $x,y$ independently from the ordinary continued fraction, checks the norm, recovers the endpoint pairs, and tests their possible multiples. A lower-end filter uses $x\le(r+1)y+7$. Brute-force controls exercise both ordinary and multiword radicands with known solutions. A separate count of subset products by residue modulo 105 checks that the radicand generation is exhaustive. [Large-radicand verifier](Erdos849PellPairs.py) · [Native arithmetic](Erdos849PellPairs.c)

For every resulting pair $(A,B)$ within the numerator window, the only possible row endings satisfy $B\le n\le A+7$. Each such row is tested for the common value in columns 5 and 7 using exact modular exclusions and integer inversion. For values at least $10^{5000}$, the three-column interpolation verifier independently gives 32 distinct prime factors using `--cap 31 --decade 5000`. Exactly 25 primes are at most 100, so at least seven of these prime factors exceed 100. [Three-column argument](Erdos849EightSmooth.txt) · [Height verifier](Erdos849EightSmoothTail.py)

The large-radicand pass tested 19,398,233 squarefree kernels. It retained 993,977 for exact replay. Four convergents passed the smooth-denominator and coordinate-size filters. Combining these with the smaller radicands and the tabulated gaps gave **36 pairs in 120 possible rows**. No row yielded a value common to columns 5, 7 and 8. Thus a value in these columns in the tested interval can have at most one 100-smooth numerator term in column eight, independently of the count of its prime factors. A second replay with cap 32 at the same height proved the stronger large-height statement above.

## A separate check on the six-prime conclusion

If a five-row value has at most five primes above 100, the previous classifications force one of the two named patterns. A remaining exception would lie below $10^{3133}$ and have three 100-smooth terms $t,t+3,t+6$, all coprime to 3, in its column-eight numerator. Among the three terms, at most one is divisible by 97. Choose a pair of the others. Its squarefree product kernel consequently omits both 3 and 97 and is congruent to 1 modulo 3. For an adjacent pair take $x$ to be the sum of its terms and for the two outer terms take $x=t+3$. The resulting primitive equation has norm nine. For $d>81$ the same Legendre argument applies; for smaller radicands the verifier reduces orbits by a Pell unit. If $u+v\sqrt d$ is the positive fundamental unit, a seed with $|y|\le3\sqrt{(u-1)/(2d)}$ is obtained by scaling $x+y\sqrt d$ to between $3/\sqrt{u+v\sqrt d}$ and $3\sqrt{u+v\sqrt d}$. Both signs of the seed are tested. The case $d=1$ uses the divisors of nine.

This check uses a separate native implementation of the complete quotients with an explicit 128-bit numerator and division. Exact Python convergents then test each retained radicand. Its denominator cutoff is $2^{1310}$, sufficient because $(2^{1309}-7)^8>8!10^{3133}$. The earlier 64-bit enumeration covers smaller starts. [Progression verifier](Erdos849SmoothPell.py) · [Native sieve](Erdos849SmoothPell.c)

The independent search checked 18 small and 4,194,286 large radicands. Exactly 171,751 of the latter reached the Python replay. It found no qualifying triple with starting term between $2^{64}-7$ and $2^{1309}-7$, inclusive.

## Reproduction

Run from this directory with Python assertions enabled and a C compiler supporting 128-bit unsigned integers. On Windows pass the path to Lean's bundled `clang.exe` via `--cc`.

```sh
python Erdos849PellSmall.py
python Erdos849PellPairs.py --cc clang
python Erdos849EightSmoothTail.py --cap 31 --decade 5000
python Erdos849EightSmoothTail.py --cap 32 --decade 5000
python Erdos849SmoothPell.py --cc clang
```
