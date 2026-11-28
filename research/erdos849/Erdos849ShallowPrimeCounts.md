# Prime counts at seven heights for the two four-column patterns

If a value $a$ occurs in columns $(3,5,7,8)$ or $(5,6,7,8)$, its number of distinct prime divisors satisfies the bounds below. Each entry applies at the cutoff and at every greater height.

| Lower bound for $a$ | $10^{350}$ | $10^{370}$ | $10^{400}$ | $10^{456}$ | $10^{611}$ | $10^{1850}$ | $10^{2350}$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| Minimum distinct primes | 36 | 37 | 38 | 39 | 40 | 41 | 42 |

For the first step there are sharper pattern-specific cutoffs. A value with **exactly 35** distinct primes in columns $(3,5,7,8)$ must satisfy $10^{136}<a<10^{291}$. In columns $(5,6,7,8)$ it must satisfy $10^{144}<a<10^{319}$. The lower endpoints are the previously established finite exclusions. [Finite searches](Erdos849PatternHeights.md)

Assign each prime power $p^e$ exactly dividing $a$ to the first numerator term of maximum $p$-valuation in each row. Each column-eight term receives at least four primes. In the last two table entries all 35 column-five and column-seven intersections are occupied, so each column-seven term receives at least five. The four-column polynomial certificates give $p^e\le p^{v_p(420)} Q(a/10^{128})^{1/36}$ with $Q=35519$. [Four primes per column-eight term](Erdos849HostCount.md) · [Column-five and column-seven intersections](Erdos849FiveSevenCells.md) · [First pattern bound](Erdos849PatternThree.txt) · [Second pattern bound](Erdos849PatternSixHost.md)

Fix a subset $S$ of the $k$ terms, where $k=7$ or $8$. Their product is the product of the assigned powers times a cofactor dividing $k!$. For $p=2,3,5,7$, let $m$ be the first power of $p$ greater than $k$. Enumerate the row modulo $m$ and compute the valuations $v_i$ on its $k$ terms, initially using $v_p(m)$ for a zero residue. If the maximizing position lies in $S$, subtract $e=\sum_i v_i-v_p(k!)$ from the summed valuations on $S$. Add $v_p(420)$ when the maximizing position lies there and $e>0$ or can become positive on lifting a zero residue there. Increasing the valuation of a zero residue increases both its valuation and $e$ by the same amount. Taking the maximum of this corrected sum per prime and multiplying the resulting powers gives an integer bound $C(S)$ on the cofactor times the small-prime allowances. Primes larger than seven contribute to neither.

At a cutoff $10^H$ let $L=\lfloor(k!10^H)^{1/k}\rfloor-k+1$. Each numerator term is at least $L(a/10^H)^{1/k}$. If $S$ receives at most $t$ primes, the prime-power bound rules out that allocation whenever both inequalities below hold.

$$
kt\le36|S|,\qquad
L^{36|S|}>C(S)^{36}Q^{36t}10^{(H-128)t}.
$$

The first inequality ensures the contradiction persists as $a$ grows. The verifier builds the resulting lower bounds for all subsets. For a claimed prime count $w$, it enumerates every allocation of $w-1$ primes consistent with the starting per-term minimum and discards each allocation that fails a subset bound. A smaller valid allocation could be padded to $w-1$ while preserving every lower bound. No allocation survives at any of the seven cutoffs.

Run the standard-library verifier with assertions enabled. [Exact integer calculation](Erdos849ShallowPrimeCounts.py)

## The case of exactly 35 primes

Every one of the 35 intersections $(i,j)$ between columns five and seven must receive exactly one prime. Fix an eighth-column position $s$. In the four-column polynomial archive, take all tuples extending $(s,i,j)$. At the chosen cutoff $10^H$ bound the corresponding polynomial in absolute value by $B$ and write $d$ for its vanishing order. Take $q_{sij}$ to be the largest $1+\lfloor B^{1/d}\rfloor$ among these tuples. The archived divisibility certificate and its real weight bound imply that a full prime power assigned to these positions is at most $p^{v_p(420)}q_{sij}(a/10^H)^{1/36}$. The verifier recalculates the real bound and weight inequality for every archived tuple. [Polynomial certificate and divisibility argument](Erdos849PatternThree.txt) · [Four-column tuple bounds](Erdos849JointHosts.md)

Enumerate the small primes at all eight positions of a **single** column-eight row, using the first power of each prime greater than eight. A nonzero residue gives the exact prime part of the term, and counts towards its assigned primes if it is the chosen host and the exponent in $a$ is positive. A zero residue is the unique maximum. Its cofactor and small-prime allowance together are bounded by $p^{v_s-e+v_p(420)}$, evaluating $v_s,e$ at the minimal lift. Their difference stays fixed as the valuation increases. Let $b$ be the product of the exact factors and these cofactor allowances at position $s$, and $c$ the number of exactly known hosted primes there.

If this position receives four primes in total, the other $4-c$ primes come from distinct $(i,j)$ intersections. Their contributions, after accounting for the factors in $b$, are bounded by the product $U$ of the $4-c$ largest $q_{sij}$ times $(a/10^H)^{(4-c)/36}$. Comparing $bU$ with $L=\lfloor(8!10^H)^{1/8}\rfloor-7$ suffices because $(4-c)/36<1/8$. The exact comparison forces at least four of the eight positions to receive five or more primes in each of 11,200 possible small-prime configurations at each stated cutoff. The other four positions receive at least four each. This requires at least 36 primes and excludes exactly 35. [Exact calculation for both patterns](Erdos849ExactlyThirtyFive.py)
