# Columns 18 and higher with eighteen prime divisors

Let $X=10^{128}$ and $a\ge X$. Suppose $a$ occurs in two left-half columns $7\le j<d$ with $d\ge18$. Then $a$ has at least **19 distinct prime divisors**.

## Endpoints and empty numerator terms

Suppose there are at most 18 distinct primes. For each prime divisor $p$, let $P=p^{v_p(a)}$. In a row $(n,k)$ with value $a$, there is an offset $0\le s<k$ such that $P\mid n-s$. Indeed the factorial valuation formula has $v_p(a)$ nonzero terms, each equal to one. Some contributing level $h\ge v_p(a)$ therefore satisfies $n\bmod p^h<k\bmod p^h\le k$. Choose one such term for each $P$ independently in each row. Dividing each term by its assigned prime powers gives positive integer cofactors of product $k!$.

Write $y=a/X$, $R_k=\lfloor(k!X)^{1/k}\rfloor$, $L_k=R_k-k+1$ and $U_k=R_k+k$. Every numerator term lies between $L_k y^{1/k}$ and $U_k y^{1/k}$, since $n-k+1\le(k!a)^{1/k}\le n$. If $d\ge21$, half-row monotonicity gives $\binom n{21}\le a$ in the deep row. Hence every full power is at most $n\le U_{21}y^{1/21}$. The check $U_{21}^{18}<X$ contradicts the product of those powers being $a$.

When $k\le20$, an empty term (one assigned no prime) equals its cofactor and divides $k!$. Its row therefore has the form $n=u+s$ with $u\mid k!$ and $0\le s<k$. The verifier enumerates these rows and checks all required partner columns. For $k=18,19,20$ those partners are $7,\dots,k-1$. For $7\le k<18$ the partner is 18. All rows with $a\ge X$ are covered. Column membership uses Lucas congruences to reject impossible residues modulo primes greater than the column. For the surviving cases, the integer root $v=\lfloor(j!a)^{1/j}\rfloor$ brackets the row between $v$ and $v+j$.

Since $d>18$ forces an empty term whenever there are at most 18 primes, only $d=18$ remains. Both rows now have no empty term. The 18 deep terms must each contain exactly one assigned power, so there must be exactly 18 distinct primes.

## The occupied column 18

For $j=7,8,9$ we have $L_j>j!U_{18}$. A shallow term containing only one prime power could be at most $j!U_{18}y^{1/18}$, less than its required size. Thus every shallow term contains at least $q=2$ prime powers. For $10\le j\le17$ put $q=1$, supplied by occupancy alone.

At least $h=(q+1)j-18>0$ shallow terms must contain exactly $q$ powers. If there were fewer, the row would use more than 18 powers. The smallest cofactor at one of those terms is at most $B=\lfloor(j!)^{1/h}\rfloor$. Suppose its shallow offset is $r$ and its $q$ distinct deep offsets form a set $S$. With $n,m$ the deep and shallow rows, respectively, there are coprime positive integers $b,c$ satisfying

$$
m-r=\frac{b}{c}\prod_{s\in S}(n-s),\qquad b\le B.
$$

Indeed the unreduced numerator is the shallow cofactor and the unreduced denominator is the product of the deep cofactors at $S$. Since $jq\le18$, the endpoints give $cL_j\le bU_{18}^q$. In the equal-degree case $j=9$ the endpoints also give $bL_{18}^q\le cU_j$. No coprime pair satisfies both in that case.

The remaining parameter ranges leave 2,448 substitutions for $j=8$, 576 for $j=16$ and 2,754 for $j=17$. Every other case fails the endpoint bounds. To verify these 5,778 substitutions write $T(n)=\prod_{s\in S}(n-s)$ and $V_i(n)=bT(n)+c(r-i)$. Test the exact integer polynomial

$$
 j!\,c^j(n)_{18}-18!\prod_{i=0}^{j-1}V_i(n).
$$

Here $(n)_{18}=n(n-1)\cdots(n-17)$. On the real interval $n\ge L_{18}$ the factors $V_i$ are positive. The logarithmic derivative of $(n)_{18}$ is at least $18/n$, and that of the other product is at most

$$
\frac{jq\, n^{q-1}}{(n-17)^q-17c}.
$$

This follows from $T'(n)\le qn^{q-1}$ and $V_i(n)\ge b((n-17)^q-17c)$. The verifier checks $jq\,n^q<18((n-17)^q-17c)$ at $n=L_{18}$, which suffices throughout the interval because $(1-17/n)^q-17c/n^q$ is increasing. Thus the ratio of the products is strictly increasing. It tends to infinity since $jq<18$. The verifier doubles an upper bound, locates the first integer where the polynomial is nonnegative by binary search, and checks it is nonzero. Two exact equalities at small rows independently exercise the polynomial sign convention.

Run **python Erdos849EighteenHosts.py** with its repository imports. The proof uses exact integer arithmetic and the displayed monotonicity argument.
