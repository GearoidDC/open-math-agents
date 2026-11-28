# Finite searches for the two four-column patterns

The finite searches below exclude every collision in columns $3,5,7,8$ through $10^{137}$ and every collision in columns $5,6,7,8$ through $10^{146}$. They apply for any number of prime divisors. The independent argument later in this note bounds how individual primes can occupy the numerator terms. The full individual coverage of columns five and eight now rules out exactly 35 prime divisors altogether. [Individual coverage](Erdos849FiveEightRawBranches.md)

## Lower endpoints from the complete row intervals

The preceding searches exclude every coefficient through $10^{136}$ in the first pattern and through $10^{144}$ in the second. We tested every subsequent eighth-column row through the new endpoints. Each candidate value had to occur in the residue images of all three other columns at every chosen modulus. None passed. [Previous intervals](Erdos849PatternHeights.md)

| Columns | New coefficient interval | Column-eight rows | CRT joins | Passed the bit masks | Passed every local test |
|---|---|---:|---:|---:|---:|
| 3, 5, 7, 8 | $(10^{136},10^{137}]$ | 125,549,160,311,115,083 | 1,292,348,228,908 | 231,609,133 | 0 |
| 5, 6, 7, 8 | $(10^{144},10^{146}]$ | 2,929,716,563,760,960,290 | 633,705,063,061 | 2,241,701 | 0 |

The second interval runs from row 3,764,350,599,503,128,604 to row 6,694,067,163,264,088,893 inclusive. The translated sieve represents a row by its displacement from the lower endpoint. The native kernel handles the displacement, while Python reconstructs the row using full-precision integers. Controls include direct residue enumeration above $2^{93}$ and recovery of the known common value 3003. [First checker](Erdos849FocusedCRT.py) · [Translated checker](Erdos849OffsetRows.py)

~~~sh
python -B Erdos849FocusedCRT.py --columns 3 5 7 8 --lower 136 --upper 137
python -B Erdos849OffsetRows.py --columns 5 6 7 8 --lower 144 --upper 146
~~~

## Upper endpoints from the two terms in a reflected pair

For the earlier conditional upper bounds, suppose that $a$ has exactly 35 distinct prime factors. Choose the first maximizing numerator term for each prime in each column. Then exactly one prime occupies each of the 35 individual $(i,j)$ cells in columns five and seven. Each of the eight terms of column eight receives at least four primes. Every reflected pair of eighth-column positions receives a prime from every individual offset in column five and every individual offset in column seven. [Five–seven cells](Erdos849FiveSevenCells.md) · [Four primes per position](Erdos849HostCount.md) · [Five–eight cells](Erdos849FiveEightCellsSieve.md) · [Seven–eight cells](Erdos849SevenEightCellsSieve.md)

Call an eighth-column position light if it receives four primes. If both positions of a reflected pair are light, their eight primes represent all seven values of $j$. Therefore exactly one $j$ occurs twice, and the other six occur once. At the repeated $j$ the two primes must have different $i$. The eight primes also represent all five values of $i$.

For each eighth-column position $s$, obtain an upper multiplier $b_s$ and the number $c_s$ of exactly known hosted small prime powers from the existing enumeration at $2,3,5,7$. Write $q_{sij}$ for the polynomial bound at height $10^H$ with the fourth-column offset maximized out. A light position contributes at most $b_s$ times the product of its $4-c_s$ chosen $q_{sij}$, times $(a/10^H)^{(4-c_s)/36}$. [Bounds and small-prime proof](Erdos849ShallowPrimeCounts.md)

For positions $s$ and $7-s$, the verifier computes the largest product of the unknown bounds consistent with the pair restrictions. It processes the seven $j$ in order, keeping the counts assigned to each position, whether a $j$ has already appeared twice, and the set of five-column offsets already represented. At the end, missing five-column offsets must be supplied by the known small primes. Allowing those primes to fill any missing offsets gives an upper bound.

Each eighth-column term is at least $L(a/10^H)^{1/8}$ for $L=\lfloor(8!10^H)^{1/8}\rfloor-7$. The product of two light terms has upper exponent at most $8/36<2/8$. Whenever its upper coefficient is below $L^2$, at least one position in the pair must receive five primes. The verifier combines that conclusion with the individual position bounds, summing over four disjoint reflected pairs. At $H=284$ and $H=318$ all 11,200 small-prime configurations need at least four positions receiving five primes. The four other positions receive at least four each, requiring 36 distinct primes. [Exact integer verifier](Erdos849FourHostPairs.py)

~~~sh
python -B Erdos849FourHostPairs.py
~~~

## Higher prime counts from the seven numerator terms

| Columns | At least 41 primes from | At least 42 primes from |
|---|---:|---:|
| 3, 5, 7, 8 | $10^{1072}$ | $10^{1602}$ |
| 5, 6, 7, 8 | $10^{1689}$ | $10^{2235}$ |

Every seventh-column term already receives at least five distinct primes. If it receives exactly five, those primes cover all five positions in column five and all four reflected blocks in column eight. Fix this seventh-column offset $j$. Process the five offsets $i$ in order. For each unknown prime, select its eighth-column position $s$ and multiply the upper bound by $q_{sij}$. If a known small prime occupies the offset instead, leave the product unchanged. Keep the largest product for each count of unknown primes and set of covered eighth-column blocks. Any missing blocks must be accounted for by the remaining known small primes.

Apply the small-prime calculation to the seven consecutive terms, using $7!$ in the valuation of the binomial coefficient. The real exponent for five primes is at most $5/36<1/7$, so a term too large for the computed upper bound needs at least six primes at every greater height. The checker finds at least six such terms at each 41-prime cutoff and all seven at each 42-prime cutoff. This argument uses individual five–seven coverage and reflected seven–eight coverage. [Integer checks](Erdos849FourHostPairs.py)
