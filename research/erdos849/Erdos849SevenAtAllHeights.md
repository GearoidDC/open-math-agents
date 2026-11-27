# Every five-row value has at least seven distinct prime divisors above 100

Suppose a value $a$ occurs in at least five distinct rows of the left half of Pascal's triangle. Then at least **seven distinct primes greater than 100** divide $a$. This strengthens the earlier result of six. The two special four-column patterns have further restrictions described in the research index.

Lean 4.33.1 verifies the deduction, including the existence of four proper columns and their exhaustive split into cases. The finite searches, published classifications and interpolation bounds are explicit hypotheses. The kernel reported only `propext`, `Classical.choice` and `Quot.sound`. [Lean theorem](Erdos849GlobalLargePrimes.lean)

The finite search gives $a>10^{128}$. Choose four proper columns and write $d$ for their largest member. At most one of the four belongs to $\{2,3,4,6\}$ by the small-column classifications. Thus $d\ge8$ and at least two earlier columns belong to $\{5\}\cup\{7,\ldots,d-1\}$. If $d=8$, both of the possible patterns have already been shown to require seven large primes. If $d\ge11$, the smooth-neighbor theorem for a single column gives seven directly. It remains to check $d=9,10$. [Finite search](Erdos849Focused128.md) · [Column classifications, Theorem 2.2](https://arxiv.org/abs/1707.06893) · [Column-eight proof](Erdos849PellPatterns.md) · [Single-column theorem and extended verifier](Erdos849SmoothNeighbors.md)

## Bounded heights in columns 9 and 10

Assume $10^{128}<a<10^{5000}$ and at most six of its prime factors exceed 100. In a numerator of length $d=9$ or $10$, each such prime can affect at most one term. There must be at least $d-6$ terms having only primes up to 100. Two of these terms have distance at most $\lfloor(d-1)/(d-7)\rfloor$, which equals four for $d=9$ and three for $d=10$.

All numerator terms are at least $L_d=\lfloor(d!10^{128})^{1/d}\rfloor-d+1$. Here $L_9=691,789,029,017,937$ and $L_{10}=28,574,346,269,245$. The smooth-neighbor tables supply all pairs of gap one or two and their eligible multiples. In column nine the remaining normalized gap-four case has odd center bounded by 407,479,035,814,853, too small. This leaves coprime gap-three pairs. [Smooth-neighbor data](Erdos849SmoothNeighbors.md) · [Odd gap-four bound, Theorem 3(a)](https://web.math.pmf.unizg.hr/~fnajman/smooth.pdf)

For a smaller endpoint at least $L_8=37,643,505,995,031,279$, the column-eight Pell enumeration already covers every such gap-three pair. The variable $x$ is the sum of the two endpoints, so $x\ge L_8$. Its denominator satisfies $y\le2n<2^{2100}$ because $\binom n8\le\binom nd<10^{5000}$. There were no qualifying large-radicand norm-nine candidates, and all small-radicand pairs lay below $L_8$. At smaller endpoints the additional search enumerated 228,952,657 odd smooth integers coprime to three from $L_{10}$ through $L_8+7$, and found 13 coprime pairs at gap three. The overlap includes both endpoints of a pair crossing $L_8$. [Pell enumeration](Erdos849PellPatterns.md) · [Additional search and row verifier](Erdos849NineTenLow.py)

In column nine, 90 eligible pairs gave 569 possible row endings. In column ten, 302 pairs gave 2,356. The checker evaluates the binomial coefficient and tests the eligible earlier columns by exact modular exclusions and integer inversion. No candidate had the two required earlier occurrences.

## Heights at or above $10^{5000}$

The largest column and either two eligible earlier columns give three simultaneous representations. For $d=9$ there are three choices, and for $d=10$ there are six. For each of these nine triples the checker proves at least 32 prime factors, so at least seven exceed 100.

The argument follows the three-column interpolation proof with cap 31. For each local choice of offsets it constructs integer polynomial combinations of the shifted row variables, using increasing weights $w=\sum e_k\operatorname{lcm}(k)/k$. Here the least common multiple is taken over the three columns. The checker keeps distinct monomials of the same weight. After exact elimination it independently checks that the first $h$ coefficients of the substituted power series vanish. The formal inverse and the full prime-power divisibility are the same as in the original argument. [Local divisibility proof](Erdos849EightSmooth.txt)

For nonvanishing, group monomials by weight and use signed lower and upper coefficient bounds at the base height. If all partial sums of the groups from highest weight downward are positive, summation by parts gives positivity at every scale $t\ge1$. Either sign of the polynomial may be used. In each case the largest weight $W$ satisfies $31W\le h\operatorname{lcm}(k)$, and its absolute bound $B$ satisfies $B<Q^h$, where $Q=\lfloor((10^{5000}-1)/D)^{1/31}\rfloor$ and $D=\operatorname{lcm}(1,\ldots,d-1)$. For a prime power $p^e$ fully dividing $a$ this gives $p^e<p^{v_p(D)}(a/D)^{1/31}$. Multiplication contradicts $a=\prod p^e$ if at most 31 primes divide $a$.

The verifier regenerated all 4,289 local certificates, with maximal vanishing order 18. [Nine-triple verifier](Erdos849NineTenTail.py)

## Reproduction

The first command checks the larger-column smooth-neighbor bound and its published finite inputs. The next three replay the column-eight and additional calculations. The earlier finite search and column-eight proof have their own controls and commands.

```sh
python Erdos849SmoothNeighbors.py --extended
python Erdos849PellPairs.py --cc clang
python Erdos849NineTenLow.py --cc clang
python Erdos849NineTenTail.py
```
