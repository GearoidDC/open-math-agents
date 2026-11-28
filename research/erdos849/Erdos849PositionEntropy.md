# Counting distinct prime assignments by polynomial evaluation

Suppose $a$ occurs in all four indicated columns. The following numbers are lower bounds on the number of distinct prime divisors of $a$, and in fact on the number of different four-way positions those primes occupy. Every bound persists above its stated height.

| Columns | $a\ge10^{225}$ | $10^{300}$ | $10^{400}$ | $10^{600}$ | $10^{1000}$ | $10^{2000}$ | $10^{5000}$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| 3, 5, 7, 8 | 43 | 50 | 58 | 67 | 78 | 91 | 103 |
| 5, 6, 7, 8 | 45 | 53 | 62 | 76 | 93 | 114 | 136 |

Exactly 40 distinct primes would require $10^{137}<a<10^{204}$ in the first pattern or $10^{146}<a<10^{184}$ in the second. The lower endpoints come from complete finite searches. The upper endpoints use coverage of all 40 pairs in columns five and eight and all 35 pairs in columns five and seven. Run `python -B Erdos849PositionEntropy.py` for the exact arithmetic at both endpoints and all fourteen table entries. [Finite searches](Erdos849FourHostPairs.md) · [Five and eight](Erdos849FiveEightRawBranches.md) · [Five and seven](Erdos849FiveSevenCells.md)

## Separating polynomials at the four rows

Write $a=\binom{n_k}{k}$ at each of the four columns. Assign each $p^v\parallel a$ to a tuple $s$ by choosing an offset $s_k$ maximizing the valuation of $n_k-s_k$. Then $p^v\mid n_k-s_k$. Indeed, among the $k$ successive terms, the count divisible by $p^t$ is at most $\lceil k/p^t\rceil$. Removing a maximum leaves at most $\lfloor k/p^t\rfloor$ such terms at each power, hence their total valuation is at most $v_p(k!)$.

For any integer linear combination $P$ of $\binom Xj$ with $0\le j\le 7$, this implies $p^v\mid420(P(n_k)-P(s_k))$. Expand by Vandermonde and use $r\binom{n_k-s_k}{r}=(n_k-s_k)\binom{n_k-s_k-1}{r-1}$ and $r\mid420$ for $1\le r\le7$. A telescoping product gives the same statement, with a single factor 420, for any product of four such polynomials and for any integral sum of these products.

The verifier lists explicit polynomials $P_{k,e}$ for $0\le e<k$, with leading binomial coefficient one. Form monomials $M_i=\prod_kP_{k,e_k}(X_k)$ and give each weight $w_i=\sum_k e_k/k<1$. Choose increasing distinct weights and integer coefficients $0\le X_i\le C_i$. The argument uses all sixteen independent choices of reflecting each column. In a reflected column use $(-1)^eP_{k,e}(k-1-X)$, which again has leading binomial coefficient one. Newton differences give its integer coefficients.

At $A=10^H$ write $T=a/A\ge1$ and $b=\lfloor(k!A)^{1/k}\rfloor$. Then $bT^{1/k}\le n_k\le(b+k)T^{1/k}$ by the falling-factorial equation. Bounds on $\binom{n_k}e$ use $(b-e+1)^e/e!$ and $(b+k)^e/e!$ times $T^{e/k}$. Bound each lower coefficient by its absolute value times $(b+k)^j/j!$, also times $T^{e/k}$. The verifier takes the larger error for the original and reflected polynomials and checks the lower bounds are positive. Multiplication gives $L_i T^{w_i}\le M_i(n)\le U_iT^{w_i}$. All bounds in the code have the same explicit factorial denominator.

The box is chosen to satisfy $L_i>\sum_{r<i} C_rU_r$ and $420\sum C_iU_i<A$. Thus two distinct coefficient choices give distinct values at the actual rows, by the largest index where they differ. Their difference $F$ also satisfies $|420F(n)|<a$. If the two choices produced identical evaluations at every occupied tuple $s$, the congruences above would give $a\mid420F(n)$. Therefore the evaluations on the occupied tuples distinguish all $D=\prod_i(C_i+1)$ choices.

## How many evaluations are needed

Choose coefficients independently and uniformly in their boxes. The joint entropy of the evaluations on the occupied tuples is $\log D$ by injectivity. At a fixed tuple put $v_i=M_i(s)$ and $Y=\sum_i v_i X_i$. Its support has size at most $W=1+\sum_i C_i|v_i|$. Its variance is $\sum_i C_i(C_i+2)v_i^2/12$. Add an independent uniform variable on $[-1/2,1/2]$. The new density is constant on unit intervals with disjoint interiors, so its differential entropy equals the discrete entropy of $Y$. Its variance is $V/12$ where $V=1+\sum_i C_i(C_i+2)v_i^2$. The Gaussian with the same mean and variance maximizes differential entropy, by nonnegativity of relative entropy. Hence

$$e^{2H(Y)}\le\min(W^2,2\pi e V/12)\le B_s/2,\qquad B_s=\min(2W^2,3V).$$

Entropy subadditivity gives $D^2 2^{|S|}\le\prod_{s\in S} B_s$ for the occupied set $S$. Under reflection the signs of the individual $v_i$ can change, while $W,V$ depend only on their absolute values. Reflecting permutes the finite grid. Multiply the sixteen bounds to replace $B_s$ by the product of the bounds at its reflected positions, counting repetitions, and raise the left side to the sixteenth power.

Every projected $(5,8)$ pair must occur. For a trial size $m$, take the largest bound in each of the forty groups, then the $m-40$ largest remaining bounds. This maximizes the product subject to that coverage, by exchanging choices within each group. A product below the required left side excludes $m$. The verifier starts at forty and tests successively.

When $m=40$ there is exactly one choice for each $(5,8)$ pair. For a fixed fifth-column offset, traverse its eight eighth-column offsets. At each step try all seven seventh-column positions, maximizing over the remaining coordinate. Keep the largest product for each subset of seventh-column positions visited. Only the final state containing all seven is admissible, since the $(5,7)$ projection is also full. Multiplying these five maxima gives the sharper test used at the two upper endpoints. All comparisons after the analytic entropy inequality use integers. [Verifier](Erdos849PositionEntropy.py)
