# Eleven prime divisors above 100 for both four-column patterns

Suppose \(a\ge 10^{128}\) occurs in Pascal columns \(3,5,7,8\) or \(5,6,7,8\). Then at least **eleven distinct primes above 100** divide \(a\).

The two four-column archives establish the following estimate for every full prime power \(p^e\mathrel{\Vert}a\), with \(H=10^{128}\).

\[
p^e\le p^{v_p(420)}Y,\qquad
Y=Q(a/H)^{1/36}.
\]

The first pattern gives \(Q=34800\) and the second gives \(Q=35519\). The larger constant also bounds the first pattern. Both patterns contain columns 5, 7 and 8, which makes a single calculation sufficient for both. The archived local estimates can be replayed with `python -B Erdos849PatternThree.py` and `python -B Erdos849PatternSixHost.py`.

## Bounding the missing prime powers

If at most ten prime divisors exceed 100, there are at most 35 distinct prime divisors altogether. Multiplication gives \(a\le420Y^{35}\). For \(Q=35519\) this is impossible from \(10^{1349}\) onward.

For the remaining heights the verifier considers bands \(10^{i/10}\le a\le10^{(i+1)/10}\). It calculates an integer upper bound \(q\) on \(Y\) using the right endpoint. Write \(z_p\) for the largest power of \(p\) at most \(q\), and set

\[
U=420q^{10}\prod_{p\le 100}z_p.
\]

Then \(a\le U\). If \(p>7\) is a prime at most 100 and its maximal power \(z_p\) does not divide \(a\), this upper bound loses a factor of at least \(p\). Thus the product of any set of such missed primes is at most \(\lfloor U/10^{i/10}\rfloor\). All comparisons use integer roots and powers.

In each surviving band the verifier selects a set of \(t\) primes between 11 and 97. The product of the smallest \(t-5\) selected prime bases exceeds the allowed loss. Hence at least six of the selected maximal powers divide \(a\). The verifier checks every six-element subset. Adjacent bands with identical required congruences are searched in one interval.

## Checking the eighth-column rows

Write \(a=\binom n8\). Each required prime power \(z_p\) divides exactly one of the eight numerator terms, since \(p>7\). Therefore \(n\bmod z_p\) lies in \(\{0,\ldots,7\}\). The product bounds for \(\binom n8\) give a finite row interval for each band.

The six moduli are split into two sets of three. Each gives 512 allowed residues. For coprime moduli \(M,N\) and residues \(b,c\), an admissible row has the form \(n=b+Mk\), with \(k+bM^{-1}\equiv cM^{-1}\pmod N\). Sorting the transformed residues on the right lets the checker stream exactly those rows in the specified interval. A direct six-modulus construction cross-checks the join on a small interval.

For each row, the eighth-column coefficient modulo each of 13 checking primes must belong to both the fifth- and seventh-column images at that prime. Each checking prime exceeds 8, so the polynomial defining each binomial coefficient is periodic in the row modulo that prime. For survivors, the verifier computes \(a\) exactly and checks the integer rows in columns 5 and 7 using the binomial product bounds.

## Replay

Run the common check for both patterns with

```
python -B Erdos849PatternCapTen.py --budget 35519 --workers 6
```

This covers 5,681 exceptional tenth-decades in 524 merged ranges and 415,860 six-prime choices. It streams 408,762 row visits. Six survive the modular tests and none has its value in both columns 5 and 7. A row may be visited through more than one choice of six primes.

The smaller budget is replayable independently with

```
python -B Erdos849PatternCapTen.py --budget 34800 --workers 4
```

It has 5,547 exceptional tenth-decades in 510 merged ranges and 366,034 six-prime choices. It streams 430,569 row visits. Six survive the modular tests and none has its value in both columns 5 and 7. Its continuous tail starts at \(10^{1337}\). The optional `--plan-only` flag reproduces the finite coverage counts.
