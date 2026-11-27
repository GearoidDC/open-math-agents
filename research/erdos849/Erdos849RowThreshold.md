# Prime divisors in the eighth column

Let \(H=10^{128}\), \(Q=35519\), and \(Y=Q(a/H)^{1/36}\). The four-column certificates for \((3,5,7,8)\) and \((5,6,7,8)\) show that every full power \(p^e\Vert a\) satisfies \(p^e\le p^{v_p(420)}Y\) when \(a\ge H\). Both patterns contain columns 5, 7 and 8.

For either four-column pattern, **at least thirteen distinct primes dividing \(a\) exceed 100, and the largest prime divisor is at least 173**. The `count` calculation excludes the case of at most twelve. More generally, any eighth-column value at least \(H\) satisfying the displayed full-power bound has a prime factor exceeding 167. The `largest` calculation proves this using the divisibility of the eight numerator terms and requires no other column membership once the full-power bound is given.

## Finite endpoints

Write \(a=\binom n8\), \(T=a/H\), and \(L=\lfloor(8!H)^{1/8}\rfloor-7\). Each numerator term is at least \(LT^{1/8}\). Assign each full prime power to a numerator term with greatest valuation at that prime, breaking ties by the first offset. After deleting that term there are at most \(\lfloor8/p^j\rfloor\) other multiples at each level \(p^j\). It follows that the full power divides its term. The product of the eight remaining cofactors is \(8!\).

For positions \(S\), let \(C(S)\) bound the product of their cofactors and the losses \(p^{v_p(420)}\) for primes assigned to them. If \(j\) primes are assigned there, the product of the corresponding terms is at most \(C(S)Y^j\). Enumerating all row residues modulo the least power \(p^u>8\) for each of \(p=2,3,5,7\) gives a bound of 117600 for one position and 2822400 for three positions together. A zero residue on a term can hide additional powers of \(p\). This term is the unique maximum, and increasing its valuation increases its assigned exponent by the same amount. The verifier takes independent maxima at the four primes.

If there are at most \(w\) distinct primes and each position receives at least four, at least \(r=40-w\) positions receive exactly four. They would have product at most \(C_rY^{4r}\). For \(w=37\) take \(r=3\), and for \(w=39\) take \(r=1\). The checker finds the first integer decade at which both \(LT^{1/8}>117600Y^3\) and \(L^rT^{r/8}>C_rY^{4r}\) hold. Both inequalities then persist because \(1/8-3/36=1/24\) and \(1/8-4/36=1/72\). These conditions rule out \(w\le37\) from \(10^{400}\) and \(w\le39\) from \(10^{611}\).

There are 25 primes through 100, so at most twelve larger primes gives \(w\le37\). There are 39 primes through 167, so a 167-smooth value gives \(w\le39\).

## Using lower prime-power divisibility requirements

In a band \(10^{i/10}\le a\le10^{(i+1)/10}\), let \(q\) be an integer upper bound on \(Y\) calculated from the right endpoint. For each prime \(p\) in the prescribed set let

\[
z_p=p^{v_p(420)}\max\{p^h:p^h\le q\}.
\]

For at most \(m\) outside primes the upper bound on the full product is \(U=q^m\prod_p z_p\). In the two cases \(m\) equals 12 and 0 respectively. The product of any known losses from this upper bound cannot exceed \(\lfloor U/10^{i/10}\rfloor\). Bands having identical maximal powers can share their largest loss allowance.

For a selected prime take a target power \(d_p=z_p/p^h>7\). If \(d_p\) does not divide \(a\), its actual contribution is at most \(d_p/p\), so the missed target costs a factor of at least \(p^{h+1}\). Allowing smaller targets gives larger penalties for missing them. For any group of \(t\) selected targets, the product of the smallest \(t-5\) penalties exceeding the loss allowance guarantees at least six successes. The verifier checks this condition and each exact relation \(d_p p^{h+1}=p z_p\). Integer estimates of CRT work only select which valid targets to use.

The search branches on whether each target divides the value. It charges its penalty on the unsuccessful branch. A successful target forces the eighth-column row modulo \(d_p\) into \(\{0,\ldots,7\}\), since the full power at its prime divides one numerator term. The search joins the congruences and enumerates the row interval from the binomial product bounds. It may stop after four or five successful targets when those already provide a useful modulus. Every possible row remains covered.

In the count case, the checker filters rows against the fifth- and seventh-column images modulo 13 primes, then tests exact membership by integer binomial coefficients. In the 167-smooth case, the entire numerator \(8!a\) must divide \(8!\prod_p z_p\). The checker tests whether the row and each of its seven predecessors can divide that integer.

## Replay

```
python -B Erdos849RowThreshold.py --case count --workers 6
python -B Erdos849RowThreshold.py --case largest --workers 6
```

For the count bound, 2,720 tenth-decades form 159 ranges. The integer-only replay uses 32,045 five-modulus choices and 1,102,740 six-modulus choices. Of 51,666,644 row visits, 661 reach exact binomial membership tests. None gives a common value. A separate search with a different selection of valid targets made 51,927,130 visits and found no common value in 662 exact tests.

For the largest-prime bound, 4,830 tenth-decades form 364 ranges. The replay uses 83,217 five-modulus choices and 2,219,475 six-modulus choices. Of 100,308,163 row visits, the end factor divides the upper numerator multiple in 7,672 cases. In every such case at least one of the other seven factors fails divisibility. Thus no row survives. Row-visit totals can include a row reached through more than one choice.
