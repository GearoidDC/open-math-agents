# A five-row value needs at least eighteen distinct prime divisors

Let $a$ occur in at least five distinct rows of Pascal's triangle, counting columns $1\le k\le n/2$ in row $n$. Then **at least 18 different primes divide $a$**, and **every full prime power $P=p^{v_p(a)}$ satisfies $P^{15}<a$**. Whether such a value exists remains open.

The argument uses the earlier finite exclusion through $X=10^{128}$, the published small-column classifications, and the integer certificates below. Lean checks the final deduction with these inputs exposed as hypotheses. [Finite exclusion](Erdos849Focused128.md) · [Blokhuis, Brouwer and de Weger, Theorem 2.2](https://arxiv.org/abs/1707.06893) · [Lean theorem](Erdos849EighteenGraph.lean)

## The common setup

Assume there are at most 17 prime bases. Write $Y=a/X$. The finite exclusion gives $Y>1$. Each fixed column represents at most one row. Four proper columns are needed in addition to the edge, and at most one can belong to the classified clique $\{2,3,4,6\}$. The two largest proper columns therefore obey $7\le j<d$.

Assign each $P$ to the factor $n-s$ of the numerator of $\binom nk$ with $s=n\bmod P$. Kummer's carry formula gives $s<k$ and $P\le n$. Each factor divided by its assigned powers has an integer cofactor, and these cofactors multiply to $k!$. Put $R_k=\lfloor(k!X)^{1/k}\rfloor$, $L_k=R_k-k+1$, and $U_k=R_k+k$. Each numerator term lies between $L_kY^{1/k}$ and $U_kY^{1/k}$, by comparison with the extreme factors.

Integer polynomial certificates give $P^{15}<a$ and at least 17 prime bases. The checker verifies divisibility and nonvanishing at all 7,865 offset pairs for $7\le j<d\le17$. Larger columns satisfy the required power bound by direct comparison with column 18. [Interpolation proof](Erdos849InterpolatedPowers.txt) · [Verifier](Erdos849InterpolatedPowers.py)

## Excluding the possible columns under the 17-prime assumption

* **Largest column 8.** The other large column is 7. Fourteen prime powers would have to occupy seven pairs on the 8 side. Redistributing these powers on the 7 side forces a pair either to exceed its entire numerator term or to satisfy one of 1,176 impossible equations. [Two-column proof](Erdos849PairSevenEight.txt)
* **Any column $9\le k\le14$.** Set $S=L_kY^{1/k}$, $M=a^{1/15}$, and $\lambda=S/M$. The checker verifies $\lambda>1$ and $S\le M^2$ at $X$, and the exponents preserve both inequalities. A term hosting one power has cofactor at least $\lambda$. An empty term has cofactor at least $S\ge\lambda^2$. If there are $e$ empty terms and $t$ singletons, then $2e+t\ge2k-17$. Hence the product of the cofactors is at least $\lambda^{2k-17}>k!$, where the last comparison holds at $X$ and only strengthens with $Y$.
* **Largest column 15 or 16.** Using the interpolation bound for each offset and each small prime base separately gives the same cofactor contradiction for every $7\le j<d$. For $d=17$, the calculation also excludes $12\le j\le16$. [Cofactor proof](Erdos849SingletonInterpolation.txt)
* **Largest column 17.** Only $j=7,8$ remain, since columns 9 through 14 were excluded at any position. An empty term would divide $17!$. The verifier enumerates every candidate row $n=D+s$ with $D\mid17!$ and $0\le s<17$ and tests the other columns by exact inversion. No common value survives. Each of the 17 terms therefore hosts exactly one prime power.
* **Largest column 18 or 19.** At least one term is empty. The same divisor enumeration tests 128,538 rows in column 18 and 355,984 in column 19 above the cutoff. None has an additional representation in a column between 7 and $d-1$.
* **Largest column at least 20.** Monotonicity gives $\binom n{20}\le a$. Thus $n\le U_{20}Y^{1/20}$. Since $U_{20}^{17}<X$, the product of at most 17 full prime powers, each at most $n$, is smaller than $a$.

## The last two column pairs

For $d=17$ and $j=7,8$, every $j$-side term must receive at least two powers. One power is at most a whole 17-side term, whereas $L_j>j!U_{17}$ and $1/j>1/17$. The 17 powers therefore give at least $3j-17$ receiving terms hosting exactly two. In any such term, the two powers are the only powers in their respective 17-side terms. For distinct $s,t$ and some $r$, this gives

$$m-r=\frac bc(n-s)(n-t),$$

with $b,c$ positive coprime integers. The numerator $b$ divides the receiving term's cofactor. The product of the numerators over all these pairs divides $j!$, so choose a pair with $b\le B=\lfloor(j!)^{1/(3j-17)}\rfloor$. Since $1/j>2/17$, it obeys $c\le BU_{17}^2/L_j$. For $j=7$ this upper bound is below one. For $j=8$ we have $b\le4$ and $c\le6$.

For each remaining choice substitute the quadratic expression for $m$ in $\binom n{17}=\binom m8$, treating the two sides as falling products. The ratio of the left side to the right side strictly increases for $n\ge L_{17}$. Its numerator has logarithmic derivative at least $17/n$, while each denominator factor $m-i$ satisfies

$$\frac{n m'}{m-i}\le\frac{2n^2}{(n-16)^2-8c}<\frac{21}{10}.$$

The last comparison holds at $L_{17}$ even with the largest $c$, and the denominator divided by $n^2$ increases thereafter. All factors are positive and $8\cdot21/10<17$. The ratio tends to infinity by degree. A doubling bracket followed by integer binary search consequently tests the first possible integer crossing. All 9,792 substitutions miss equality. This exhausts the possible column pairs.

## Reproduction

Run these files from the research directory with Python assertions enabled. The search programs use exact integer arithmetic, and the cofactor bounds use exact rational numbers.

```sh
python Erdos849LocalInterpolation.py
python Erdos849InterpolatedPowers.py
python Erdos849PairSevenEight.py
python Erdos849SingletonInterpolation.py
python Erdos849SeventeenHosts.py
```
