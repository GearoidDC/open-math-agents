# A five-row value needs at least 21 distinct primes

Let $a$ occur in at least five distinct rows of the left half of Pascal's triangle. Then $a$ has at least **21 distinct prime divisors**. The proof uses the previous finite search through $10^{128}$, the published classifications for pairs of small columns, and the exact computations below. It gives a necessary condition. The existence of a five-row value remains open. [Finite search](Erdos849Focused128.md) · [Small-column classifications, Theorem 2.2](https://arxiv.org/abs/1707.06893)

Write $X=10^{128}$ and $Y=a/X$. The search gives $Y>1$. Column 1 accounts for the edge occurrence. In the left half, each other column contributes at most one row. Choose four distinct proper columns, and let $j<d$ be the largest two. At most one of the four belongs to $\{2,3,4,6\}$ by the classifications. Hence $7\le j<d$. Suppose that $a$ has at most twenty prime divisors.

For $d\le17$ the low-column verifier exhausts the four-column patterns. For $d\ge19$ the high-column verifier rules out every pair $(j,d)$ with $7\le j<d$. The high-column proof covers $d=19,20$ by 269,567 substitutions, $d=21,22,23$ by enumerating rows with an unoccupied numerator term, and $d\ge24$ by a size bound. [Low-column calculation](Erdos849TwentyOneLow.txt) · [High-column proof](Erdos849TwentyHosts.md)

## The remaining column, 18

For $k\in\{j,18\}$ assign each full prime power of $a$ to a numerator term of largest valuation for its prime. The remaining cofactor of each term divides $M_k=\operatorname{lcm}(1,\ldots,k)$, and the cofactors multiply to $k!$. Put $R_k=\lfloor(k!X)^{1/k}\rfloor$, $L_k=R_k-k+1$ and $U_k=R_k+k$. Each numerator term lies between $L_kY^{1/k}$ and $U_kY^{1/k}$. For $7\le k\le18$, we have $M_k<L_k$, so every term must receive a power. At most two terms in column 18 receive multiple powers. Together they receive at most four powers. [Cofactor lemma](Erdos849NineteenLow.txt)

For $j=7,9,10,13,14,15,16,17$ the size and counting argument in the high-column proof applies directly at $d=18$. Its two orientations cover cases where the substituted product grows faster or slower than the deep falling factorial. The three remaining shallower columns need more precise counts.

- **Column 11.** At least two of its eleven terms contain a single power. With at most one such term the row would require at least $1+2\cdot10=21$ powers. One of these single-power terms has cofactor at most $\lfloor\sqrt{11!}\rfloor$. Its power is at most $U_{18}Y^{1/18}$, since it divides a deep term. The inequality $\lfloor\sqrt{11!}\rfloor U_{18}<L_{11}$ contradicts the shallow term's lower bound.
- **Columns 8 and 12.** Write $q=2$ for column 8 and $q=1$ for column 12. Every term receives at least $q$ powers by occupancy and $L_8>M_8 U_{18}$. At least $(q+1)j-20=4$ terms receive exactly $q$. Suppose three of them each use a power from a multiply occupied deep term. Select one such power from each. The three distinct selected powers divide the product of at most two deep terms. The other $3(q-1)$ powers are each at most one deep term. The product of the three shallow terms is therefore at most $j!(U_{18}Y^{1/18})^{3q-1}$. The checker verifies $L_j^3>j!U_{18}^{3q-1}$ and $3/j\ge(3q-1)/18$, contradicting the lower bound. Thus at least two shallow terms of size $q$ draw exclusively from singly occupied deep terms.

For the latter two pairs, one of these shallow terms has cofactor at most $\lfloor\sqrt{j!}\rfloor$. Its row $m$ at offset $r$ satisfies $m-r=(b/c)\prod_{s\in S}(n-s)$ for $q$ distinct deep offsets. The reduced numerator divides $M_j$, the denominator divides $18!$, and $c\le bU_{18}^q/L_j$. For every admissible ratio and offset choice, the verifier tests the unique possible crossing of the two falling-factorial polynomials by the derivative bounds in the high-column proof. The column-18 calculations across all eleven partners took 266,688 exact substitutions and found no equality. [Column-18 verifier](Erdos849TwentyColumn18.py)

## Reproduction

With the files from this directory together, run Python with assertions enabled.

```sh
python Erdos849TwentyOneLow.py
python Erdos849TwentyColumn18.py
python Erdos849TwentyHosts.py
```

Lean proves the deep-column cutoff and combines the finite search, classifications and column exclusions into the 21-prime conclusion. The external results are explicit hypotheses of that Lean theorem. [Lean theorem](Erdos849TwentyOneGraph.lean)
