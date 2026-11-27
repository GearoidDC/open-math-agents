# A value shared by five rows needs at least twenty distinct primes

Suppose $a$ occurs in at least five distinct rows of the left half of Pascal's triangle. Then **at least 20 different primes divide $a$**. The finite search through $10^{128}$, the published small-column classifications, and the calculations below are inputs. Lean checks how these inputs imply the row-count theorem and independently proves its deep-column cutoff. The existence of a five-row value remains open. [Finite search](Erdos849Focused128.md) · [Blokhuis, Brouwer and de Weger, Theorem 2.2](https://arxiv.org/abs/1707.06893) · [Lean theorem](Erdos849TwentyGraph.lean)

Set $X=10^{128}$ and $Y=a/X>1$. Besides the edge, five rows require at least four different proper columns. At most one belongs to $\{2,3,4,6\}$. Hence the two largest chosen proper columns satisfy $7\le j<d$. Assume there are at most nineteen prime bases.

For each prime $p\mid a$, assign its full power $p^{v_p(a)}$ to a numerator term $n-s$ of maximal $p$-valuation in each row. In column $k$, division by the assigned powers leaves cofactors that individually divide $M_k=\operatorname{lcm}(1,\ldots,k)$ and together multiply to $k!$. Write $L_k=\lfloor(k!X)^{1/k}\rfloor-k+1$ and $U_k=\lfloor(k!X)^{1/k}\rfloor+k$. Every numerator term is between $L_kY^{1/k}$ and $U_kY^{1/k}$. [Proof of the cofactor bound](Erdos849NineteenLow.txt)

## Columns up to 17

The verifier tests every four-column subset, using the published exclusions, the 24-prime bound for columns 7 and 8, and interpolation bounds on the sizes of the assigned powers. The eight patterns left by this test all include column 5 and one of $(8,17),(9,16),(9,17)$. Across all 433 offsets of these pairs, the refined polynomial certificates give every full prime power the bound $P\le120013011\,Y^{1/15}$. In column 5, each cofactor is at most 60 and $60(120013011)^3<L_5$. Thus a term with only three assigned powers would be smaller than the term's lower bound. Five terms need at least twenty prime powers, each with a different base. [Low-column proof](Erdos849TwentyLow.txt) · [Columns 7 and 8](Erdos849PairPowerSlots.txt)

## Columns 18 and higher

If $d\ge23$, compare with column 23 in the same row. The inequality $U_{23}^{19}<X$ gives $n^{19}<a$, but every full prime power of $a$ is at most $n$. Thus $d\le22$.

A term hosting no power equals its cofactor. Its row must be $n=D+s$ with $D\mid M_k$ and $0\le s<k$. The checker enumerates these rows for all relevant columns, retaining $a\ge X$ and testing other columns by exact inversion. No necessary collision survives. In columns 20 through 22 the nineteen powers cannot occupy every term, so these columns are excluded.

It remains to consider fully occupied rows for $d=18,19$. With nineteen powers there are at most $19-d$ terms in the deep row that host multiple powers. Together those terms host at most $2(19-d)$ powers. The remaining powers are each the sole power in their deep term.

For each tested shallower column $j$, the checker establishes a minimum number $q$ of powers per term. Start at one by occupancy. If $tj\le d$ and $L_j>M_jU_d^t$, then at most $t$ powers would make a term too small, so it needs at least $t+1$. If $qj>19$, the pair is excluded.

Otherwise at least $(q+1)j-19$ shallow terms have exactly $q$ powers. At most $2(19-d)$ of these terms receive a power from a multiply occupied deep term. In the remaining $h=(q+1)j-19-2(19-d)$ terms, all $q$ powers are sole occupants of distinct deep terms. The checker verifies $h>0$ and $qj\le d$ in each remaining case. One such shallow term has cofactor at most $B=\lfloor(j!)^{1/h}\rfloor$. It follows that

$$m-r=\frac bc\prod_{s\in S}(n-s),\qquad |S|=q,\quad b\mid j!,\quad c\mid d!,\quad b\le B.$$

Here $m$ and $n$ are the two row numbers, and $b/c$ is in lowest terms. Comparing the endpoint bounds gives $c\le bU_d^q/L_j$. When $qj=d$ the opposite endpoint comparison excludes every remaining ratio. When $qj<d$, substitute this expression for $m$ into $\binom nd=\binom mj$. For real $n\ge L_d$ the ratio of the falling products increases strictly: the logarithmic derivative of the numerator, multiplied by $n$, is at least $d$. Each of the $j$ denominator factors contributes at most

$$\frac{q n^q}{(n-d+1)^q-jc}.$$

The verifier checks that the denominator is positive and that $j$ times this upper bound is below $d$ at $L_d$. It decreases thereafter, as its denominator divided by $n^q$ increases. The ratio tends to infinity, so an integer binary search at its unique possible crossing is exhaustive. The 50,598 substitutions for column 18 and the 29,336 for column 19 yield no equality.

For $d=19$ this tests every $7\le j<d$. For $d=18$ it tests all such $j$ except 11 and also excludes column 5. If 11 and 18 occur, two additional proper columns are needed. At most one comes from $\{2,3,4,6\}$, and every other possible column has been excluded. This exhausts the remaining four-column patterns. [High-column verifier](Erdos849NineteenHosts.py)

## Reproduction

Run the three verifiers with Python assertions enabled. The earlier finite search and its controls have separate reproduction commands. The numerical certificates and the published classifications remain explicit hypotheses in the Lean theorem.

```sh
python Erdos849PairPowerSlots.py
python Erdos849TwentyLow.py
python Erdos849NineteenHosts.py
```
