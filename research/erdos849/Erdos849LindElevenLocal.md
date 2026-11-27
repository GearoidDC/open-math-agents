# A locally certified prime cover for the eleventh Lind value

Let $A=\binom{3478759200}{1328767775}$ and $B=2^{45}=35184372088832$. The only admissible occurrences in rows $m\le B$ are $(3478759199,1328767776)$ and $(3478759200,1328767775)$. No row $m\ge B$ can give an occurrence in a column $j\ge175119328$.

Put $T=175119328$. Exact rational bounds give

$$-11<\log\binom B{T-1}-\log A<-10,\qquad
1<\log\binom BT-\log A<2.$$

Thus every occurrence with $m\le B$ requires $j\ge T$. Otherwise $\binom mj\le\binom Bj\le\binom B{T-1}<A$, by monotonicity in the row and strict increase in the left half at row $B$. Conversely, $m\ge B$ and $j\ge T$ give $\binom mj\ge\binom mT\ge\binom BT>A$ for any admissible occurrence. The rational factorial and logarithm bounds used for these signed comparisons are proved separately. [Logarithm bounds](Erdos849LindElevenDeep.md)

The prime $3478759199$ occurs in the numerator of the defining coefficient and exceeds its column, so every row of $A$ must be at least that prime. Exact adjacent-column comparisons in the rows through $3478759212$ yield just the two stated occurrences. Starting at the prime $Q=3478759213$, the verifier constructs a chain of 200,898 certified primes. Its largest spacing is 175,118,616, at most $T$. The final prime, 35,184,225,499,447, is less than $T$ below $B$.

It follows that for every $Q\le m\le B$ and $j\ge T$, the interval $(m-j,m]$ contains one of the selected primes $p$. For an admissible column $p>m-j\ge j$, so the numerator of $\binom mj$ contains $p$ and its denominator cannot cancel it. Yet $p\ge Q>3478759200$ cannot divide $A$. This proves the bounded-row assertion.

The verifier uses a probable-prime search only to propose the chain entries. It tests each candidate against the exact primorial of $\lfloor\sqrt{B+1000}\rfloor$ using a product/remainder tree. Each candidate is at most $B+1000$, and coprimality to this primorial proves primality. Trial division checks the initial prime.

## Independence of the earlier middle-column scan

Let $j_0=63319920$ and $m_0=171595999999999995152414$. The verifier establishes

$$-6<\log\binom{m_0}{j_0}-\log A<-5.$$

If $j\le j_0$ and $m\le m_0$, then $\binom mj\le\binom{m_0}j\le\binom{m_0}{j_0}<A$. Hence every occurrence in these columns lies strictly above $m_0$. The earlier numerical scan kept candidates at or above $3999999999999999887\lfloor j/1476\rfloor+1$, which is at most $m_0$ throughout that range. Its exclusions therefore remain valid without a published prime-gap table. For the additional columns $63319921\le j<T$ it suffices to check rows $m>B$ after the two known rows are accounted for.

Run **python Erdos849LindElevenLocal.py** alongside the existing modules with gmpy2 installed. This program verifies the two crossover comparisons, the row bound for earlier columns, the entire local prime chain and the two exceptional rows.
