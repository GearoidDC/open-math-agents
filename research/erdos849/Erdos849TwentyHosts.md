# Common values when the larger column is at least 19

If $a\ge X=10^{128}$ occurs in two left-half columns $7\le j<d$ with $d\ge19$, then $a$ has at least 21 distinct prime factors. The calculation below checks the case of at most 20.

For a column $k$ write $M_k=\operatorname{lcm}(1,\ldots,k)$, $R_k=\lfloor(k!X)^{1/k}\rfloor$, $L_k=R_k-k+1$, $U_k=R_k+k$. Each numerator term lies between $L_kY^{1/k}$ and $U_kY^{1/k}$, where $Y=a/X\ge1$. Assign each full power $p^{v_p(a)}$ to a term of largest $p$-valuation. Dividing the terms by their assigned powers leaves cofactors which individually divide $M_k$ and multiply to $k!$. [Cofactor lemma](Erdos849NineteenLow.txt)

If $d\ge24$, the row number $n$ satisfies $\binom n{24}\le a$ by half-row monotonicity, so $n\le U_{24}Y^{1/24}$. The exact inequality $U_{24}^{20}<X$ contradicts $a\le n^{20}$, as every full prime power is at most $n$.

A term receiving no prime must divide $M_k$. The verifier enumerates the rows ending at $D+s$ with $D\mid M_k$ and $0\le s<k$. The first relevant column is 19. Columns 19 through 23 yield 95, 220, 441, 704 and 6,555 such rows above the threshold, respectively. It checks every potential partner $7\le j<k$ and tests column 20 against the possible empty-term rows in column 19. There are no possible empty-term rows in columns 7 through 18 at these heights. For $d=21,22,23$ at least one deep term must be empty. Hence only fully occupied rows in columns $d=19,20$ remain.

## Selecting a shallow term

For a shallow column $j$, start at $q=1$. Whenever $qj\le d$ and $L_j>M_jU_d^q$, any shallow term containing at most $q$ powers would be too small. Increase $q$ by one. Thus every shallow term holds at least $q$ powers, and $qj>20$ is impossible.

At least $(q+1)j-20$ shallow terms contain exactly $q$ powers. Each deep term containing at least two powers accounts for at least one power in excess of the $d$ needed for occupancy. At most $2(20-d)$ powers occur in all such terms combined. Therefore at least

$$h=(q+1)j-20-2(20-d)$$

of the shallow terms of size $q$ use only powers that occupy their deep term alone. Each remaining case has $h>0$. For any of those shallow terms, at offset $r$, its powers come from $q$ distinct deep terms with offsets $S$. Define $T(n)=\prod_{s\in S}(n-s)$. The shallow row $m$ satisfies $m-r=bT(n)/c$, where $b/c$ is reduced. Before reduction the numerator is the shallow cofactor, and the denominator is the product of the deep cofactors at $S$. Always $b\mid M_j$ and $c\mid d!$.

* For $qj\le d$ choose the shallow term with smallest cofactor among the $h$ terms. This gives $b\le\lfloor(j!)^{1/h}\rfloor$ and $cL_j\le bU_d^q$. If $qj=d$, one also has $bL_d^q\le cU_j$. No reduced ratio meets both for the equal-degree cases.
* For $qj>d$ choose the term with smallest product of deep cofactors instead. The $h$ sets of deep offsets are disjoint, since each of their deep terms contains one power and that power is assigned to exactly one shallow term. Thus some product is at most $\lfloor(d!)^{1/h}\rfloor$. Now $c\le\lfloor(d!)^{1/h}\rfloor$ and $bL_d^q\le cU_j$. This occurs only for $(j,d)=(10,19)$, giving $h=8$, $c\le136$, $b\le2$.

## Integer inversions in both orientations

For each allowed $b,c,r,S$, the equation is

$$ j!\,c^j(n)_d=d!\prod_{i=0}^{j-1} V_i,\qquad V_i=bT(n)+c(r-i). $$

All these factors are positive on $n\ge L_d$. When $d>jq$ the logarithmic derivatives show that the ratio of the left and right sides is strictly increasing, as in the earlier verifier. More explicitly, the left product has logarithmic derivative at least $d/n$, and the right product has logarithmic derivative at most $jq n^{q-1}/((n-d+1)^q-jc)$. The verifier compares the bounds at $L_d$; the denominator divided by $n^q$ increases thereafter.

When $d<jq$, the left logarithmic derivative is at most $d/(n-d+1)$, whereas the right is at least $jq(n-d+1)^{q-1}/(n^q+jc)$. The check $d(n^q+jc)<jq(n-d+1)^q$ at $n=L_d$ suffices for all larger $n$ upon division by $n^q$. The inverse ratio now increases strictly. In each orientation the increasing ratio tends to infinity by its degree. Doubling an upper bound and binary-searching for the first nonnegative oriented difference checks the only possible integer crossing. Two small exact identities exercise both degree orientations.

Run **python Erdos849TwentyHosts.py** alongside its repository imports. The finite checks use integer arithmetic throughout.
