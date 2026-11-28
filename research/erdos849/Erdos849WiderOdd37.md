# Seven odd-exponent primes above 37 in two four-column patterns

Let \(a\) occur in each proper column in \((3,5,7,8)\) or \((5,6,7,8)\), using row indices \(n_k\ge 2k\). **At least seven distinct primes greater than 37 divide \(a\) to odd exponent.** In particular, the largest such prime is at least 67.

The finite statement only requires columns 7 and 8. If \(a=\binom n8=\binom m7\le 10^{3210000}\), with \(n\ge16\) and \(m\ge14\), at most one of \(n,n-1,\ldots,n-7\) can have its squarefree part supported on primes at most 37. Each prime above 37 divides at most one of these terms and survives division by \(8!\). Thus at least seven distinct such primes have odd valuation in \(a\).

For the two four-column patterns the large-height square-class bound supplies at least 15 and 18 odd-exponent primes above 7 respectively, starting at \(10^{1399280}\) and \(10^{3209464}\). Only eight primes lie strictly above 7 and at most 37. Both thresholds overlap the finite range. [Large-height proof and explicit cutoffs](Erdos849HigherSquare.txt)

There is also an all-height consequence for the pair \((7,8)\) alone. Its common value has squarefree part at least \(41\cdot43\cdot47\cdot53\cdot59\cdot61\cdot67=1{,}058{,}967{,}640{,}189\). For the upper range the two-column result gives at least nine odd-exponent primes above 7, starting at \(10^{250000}\). The nine smallest possibilities there have product \(1{,}448{,}810{,}778{,}701\). [Two-column large-height proof](Erdos849SquareClassRows.md)

## The finite search

Suppose the squarefree parts of both \(n-i\) and \(n-j\), where \(0\le i<j\le7\), are supported on primes at most 37. Their product is \(D w^2\), where the squarefree positive integer \(D\) divides \(37\#=7{,}420{,}738{,}134{,}810\). Define \(g=j-i,\ x=2n-i-j,\ y=2w\). Then

\[
x^2-Dy^2=g^2,\qquad 1\le g\le7 .
\]

For \(D=1\), the positive factors of \(g^2=(x-y)(x+y)\) determine all possibilities. If \(D>1\), let \(U+V\sqrt D\) be a positive unit of norm one, \(U,V>0\). Its inverse sends \((x,y)\) to \((Ux-DVy,Uy-Vx)\). The first coordinate stays positive. For \(y>0\) the second strictly decreases and becomes negative exactly when \(y<Vg\). Every solution is therefore a nonnegative iterate of a seed with \(0\le y<Vg\).

The seed with \(y=0\) is \((g,0)\). For each positive seed, divide both coordinates by \(s=\gcd(x,y)\), which divides \(g\). The primitive coordinates \(X,Y\) have norm \(h^2\), where \(h=g/s\), and \(0<Y<Vh\). For \(D\le2401\) the enumeration in two consecutive convergents finds every such seed. [Small-radicand proof](Erdos849PellSmall.md)

For \(D>2401\) one has

\[
\left|X/Y-\sqrt D\right|
 = \frac{h^2}{Y^2(X/Y+\sqrt D)} < \frac{1}{2Y^2}.
\]

Legendre's criterion makes \(X/Y\) a regular convergent of \(\sqrt D\). With convergents indexed from zero, their norms satisfy \(p_i^2-Dq_i^2=(-1)^{i+1}Q_{i+1}\), where \(Q_{i+1}\) is the next complete-quotient denominator. The search retains the odd indices with \(Q_{i+1}\in\{4,9,16,25,36,49\}\) up to the first odd index with \(Q_{i+1}=1\), giving the unit \((U,V)\). The next digit equals \(2\lfloor\sqrt D\rfloor>7\), which the verifier checks for each radicand. Its denominator exceeds \(7V\), so every primitive seed with \(Y<Vh\) has been found. The unit itself is at \(Y=V\) and is outside the strict bound for \(h=1\). The retained primitive solutions give the seeds for all multiples of their respective gaps. [Derivation of the norm identity and convergent criterion](Erdos849PellPatterns.md)

For an orbit with seed \((x_0,y_0)\), its \(t\)-th first coordinate \(x_t\) is at least \(U^t\). Put \(b=\lfloor\log_2 U\rfloor\) and \(E=1{,}337{,}504\). If \(bt\ge E\), then \(n\ge2^{E-1}\), \(n-7\ge2^{E-2}\) and \(\binom n8\ge(n-7)^8/8!>10^{3210000}\). The last comparison follows from \(24(E-2)\ge10\cdot3210000+48,\ 10^3<2^{10},\ 8!<2^{16}\). Every index with \(bt<E\) is covered.

For each sieve prime \(p>8\), the two binomial coefficients depend only on their respective row residues. The verifier follows the unit modulo \(p\) until it returns to \((1,0)\). For each orbit it uses \(x_{t+2}=2U x_{t+1}-x_t\) and retains the indices for which the coefficient at \((x_t+i+j)/2\bmod p\) lies in the seventh-column image. It reconstructs each surviving index and checks the parity conditions for \(n\) and \(w\). At an admissible row it directly compares the eighth-column value \(a\) with seventh-column coefficients. If \(r=\lfloor(7!a)^{1/7}\rfloor\), the inequalities \((m-6)^7\le7!a\le m^7\) justify checking \(m=r,\ldots,r+7\).

## Replay

Run with standard-library Python and assertions enabled from this directory.

```sh
python -B Erdos849WiderOdd37.py --workers 6
python -B Erdos849WiderOdd37Audit.py --workers 6
python -B Erdos849HigherSquare.py
```

The primary run checked all 4,095 nonsquare divisors of the primorial. It took 436,216 continued-fraction steps for the large radicands. Across 142,200 offset/seed orbits, it passed 114,766 indices to direct reconstruction, all at index 0, 1 or 2. After checking parity and the lower bound on the row, the only candidate including the square-kernel case was row 16. Its coefficient 12,870 does not occur in column 7. Direct factorization through row 2,000 reproduced all 7,484 row/offset controls.

The audit obtains each unit by testing the convergent's actual norm, with a modular prefilter. It independently enumerates all primitive seeds in unimodular bases even for the large radicands and checks them against the primary seed sets. It tracks parity modulo two and uses the affine recurrence for the doubled row, independently generated prime images, and ordinary byte arrays. It runs through the larger horizon given by the integer part of 1,340,000 divided by the binary logarithm rounded down of the unit's first coordinate, inclusive. No admissible index survives for any of the 142,200 nonsquare-kernel orbits. For the square kernel it directly rules out every row from 16 to 19, which includes every possible admissible row because the factorization gives a first coordinate at most 25. [Finite verifier](Erdos849WiderOdd37.py) · [Independent audit](Erdos849WiderOdd37Audit.py)
