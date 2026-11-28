# Prime counts at seven heights for the two four-column patterns

If a value $a$ occurs in columns $(3,5,7,8)$ or $(5,6,7,8)$, its number of distinct prime divisors satisfies the bounds below. Each entry applies at the cutoff and at every greater height.

| Lower bound for $a$ | $10^{350}$ | $10^{370}$ | $10^{400}$ | $10^{456}$ | $10^{611}$ | $10^{1850}$ | $10^{2350}$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| Minimum distinct primes | 36 | 37 | 38 | 39 | 40 | 41 | 42 |

Assign each prime power $p^e$ exactly dividing $a$ to the first numerator term of maximum $p$-valuation in each row. Each column-eight term receives at least four primes. In the last two table entries all 35 column-five and column-seven intersections are occupied, so each column-seven term receives at least five. The four-column polynomial certificates give $p^e\le p^{v_p(420)} Q(a/10^{128})^{1/36}$ with $Q=35519$. [Four primes per column-eight term](Erdos849HostCount.md) · [Column-five and column-seven intersections](Erdos849FiveSevenCells.md) · [First pattern bound](Erdos849PatternThree.txt) · [Second pattern bound](Erdos849PatternSixHost.md)

Fix a subset $S$ of the $k$ terms, where $k=7$ or $8$. Their product is the product of the assigned powers times a cofactor dividing $k!$. For $p=2,3,5,7$, let $m$ be the first power of $p$ greater than $k$. Enumerate the row modulo $m$ and compute the valuations $v_i$ on its $k$ terms, initially using $v_p(m)$ for a zero residue. If the maximizing position lies in $S$, subtract $e=\sum_i v_i-v_p(k!)$ from the summed valuations on $S$. Add $v_p(420)$ when the maximizing position lies there and $e>0$ or can become positive on lifting a zero residue there. Increasing the valuation of a zero residue increases both its valuation and $e$ by the same amount. Taking the maximum of this corrected sum per prime and multiplying the resulting powers gives an integer bound $C(S)$ on the cofactor times the small-prime allowances. Primes larger than seven contribute to neither.

At a cutoff $10^H$ let $L=\lfloor(k!10^H)^{1/k}\rfloor-k+1$. Each numerator term is at least $L(a/10^H)^{1/k}$. If $S$ receives at most $t$ primes, the prime-power bound rules out that allocation whenever both inequalities below hold.

$$
kt\le36|S|,\qquad
L^{36|S|}>C(S)^{36}Q^{36t}10^{(H-128)t}.
$$

The first inequality ensures the contradiction persists as $a$ grows. The verifier builds the resulting lower bounds for all subsets. For a claimed prime count $w$, it enumerates every allocation of $w-1$ primes consistent with the starting per-term minimum and discards each allocation that fails a subset bound. A smaller valid allocation could be padded to $w-1$ while preserving every lower bound. No allocation survives at any of the seven cutoffs.

Run the standard-library verifier with assertions enabled. [Exact integer calculation](Erdos849ShallowPrimeCounts.py)
