# Twelve prime divisors above 100 for the two four-column patterns

If \(a\ge10^{128}\) occurs in columns \(3,5,7,8\) or \(5,6,7,8\), then at least twelve distinct prime divisors of \(a\) exceed 100.

Both four-column certificates give \(p^e\le p^{v_p(420)}Y\) for each full prime power \(p^e\Vert a\), where \(H=10^{128}\), \(Q=35519\), and \(Y=Q(a/H)^{1/36}\). The certificate for the first pattern gives the stronger constant 34800. Both patterns contain columns 5, 7 and 8. The local estimates replay with `python -B Erdos849PatternThree.py` and `python -B Erdos849PatternSixHost.py`.

## The tail from the eight numerator factors

If at most eleven prime divisors exceed 100, there are at most 36 distinct primes in total. Assign each prime power to the first eighth-column numerator term of maximum valuation at its prime. At every level \(p^j\), removing that term leaves at most \(\lfloor8/p^j\rfloor\) multiples of \(p^j\). The sum of the other valuations is therefore at most \(v_p(8!)\), so the assigned full power divides its term. The resulting cofactors have product \(8!\). For each subset \(S\) of positions, let \(C(S)\) bound the product of the cofactors on \(S\) and the factors \(p^{v_p(420)}\) for the primes assigned there. The row terms at those positions then have product at most \(C(S)Y^j\), where \(j\) counts their assigned primes.

The verifier enumerates each possible row residue modulo the least power \(p^u>8\), for \(p=2,3,5,7\). These primes supply all the cofactor and denominator factors. In particular, a numerator term that is zero modulo \(p^u\) is the unique term of highest valuation. Raising its valuation raises its assigned exponent by the same amount. Taking independent maxima over the four primes gives \(C(S)\le117600\) at a single position and \(C(S)\le8467200\) at any four positions.

Put \(L=\lfloor(8!H)^{1/8}\rfloor-7\) and \(T=a/H\). Each numerator term is at least \(LT^{1/8}\). For \(a\ge10^{370}\), integer comparisons give

\[
LT^{1/8}>117600Y^3,\qquad L^4T^{1/2}>8467200Y^{16}.
\]

The first inequality forces at least four primes at every position. With at most 36 primes in all, at least four of the eight positions must then have exactly four primes each. The second inequality makes this impossible.

## The finite interval

On a tenth-decade band \(10^{i/10}\le a\le10^{(i+1)/10}\), the verifier computes an integer upper bound \(q\) on \(Y\) from the right endpoint. The largest possible contribution of a prime \(p\le100\) is

\[
z_p=p^{v_p(420)}\max\{p^h:p^h\le q\}.
\]

The upper bound for \(a\) is therefore \(U=q^{11}\prod_{p\le100}z_p\). Whenever \(z_p\nmid a\), the actual contribution loses at least a factor \(p\). The product of the bases of any such missing powers cannot exceed \(\lfloor U/10^{i/10}\rfloor\). The checker uses all 25 bases, including 2, 3, 5 and 7 with their denominator factors.

The 2,420 bands merge into 140 intervals on which the 25 maximal powers are fixed. The verifier retains the greatest allowed loss from the constituent bands. In each interval the product of the smallest 20 prime bases exceeds that loss, so at least six maximal powers divide \(a\). A recursive enumeration considers each prime in turn, either requiring the power or paying its base from the loss allowance. A branch can stop after four or five required powers when they already give a useful row modulus. Every surviving branch stops by its sixth required power.

If \(p^e\Vert a=\binom n8\), the assignment argument above gives a numerator term divisible by \(p^e\). Thus for each required maximal power the row lies in one of the eight residue classes represented by 0 through 7. The checker joins these congruences by the Chinese remainder theorem and streams the rows in the interval supplied by the binomial product bounds. It first tests the common column-5 and column-7 images modulo 13 primes exceeding 8 and checks the remaining rows by exact binomial membership.

Replay using standard Python with

```
python -B Erdos849PatternThreshold.py --workers 6
```

The calculation uses 93 four-modulus choices, 655,444 five-modulus choices and 329,224 six-modulus choices. It yields 3,541,277 row visits, including duplicates. Of those, 45 pass all modular checks and none has its value in both columns 5 and 7. Use `--plan-only` to reproduce the endpoint and the three choice counts.

## Independent replay

The audit reads the interval plan, checks every tenth-decade directly, and recomputes the host bounds over two additional prime-power levels. It enumerates combinations of four, five and six moduli, reverses their order before the Chinese remainder join, builds the modular images from falling products, and tests exact membership by binary search.

```
python -B Erdos849PatternThresholdAudit.py --workers 6
```

The audit reproduced all three choice counts and all 3,541,277 row visits. It confirmed that the 45 rows reaching exact tests were distinct. None had its eighth-column coefficient in both columns 5 and 7.
