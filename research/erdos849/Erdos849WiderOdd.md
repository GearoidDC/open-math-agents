# Seven odd-exponent primes above 13 in common values of columns 7 and 8

Suppose \(a=\binom n8=\binom m7\) with \(n\ge16\) and \(m\ge14\). At least **seven distinct primes greater than 13** divide \(a\) to odd exponent. Consequently the squarefree part of \(a\) is at least

\[
17\cdot19\cdot23\cdot29\cdot31\cdot37\cdot41=10{,}131{,}543{,}907.
\]

Both four-column patterns containing 7 and 8 inherit the result. For \(a\ge10^{250000}\) the existing two-column Runge bound gives nine odd-exponent primes greater than 8. Only 11 and 13 can be lost when the threshold is raised to 13. The calculation below covers all smaller values, including the upper endpoint. [Large-height proof](Erdos849SquareClassRows.md) · [Height verifier](Erdos849SquareClassBound.py)

## A fixed norm depending only on the gap

A prime greater than 13 divides at most one of the eight consecutive numerator terms and survives division by \(8!\). If at most six such primes have odd valuation in \(a\), there are two terms \(n-i,n-j\), with \(0\le i<j\le7\), in which every prime above 13 has even valuation. Write

\[
(n-i)(n-j)=Dw^2,\qquad g=j-i,\qquad x=2n-i-j,\qquad y=2w.
\]

Here \(D\) is squarefree and divides \(2\cdot3\cdot5\cdot7\cdot11\cdot13=30030\). The identity \(x^2-Dy^2=g^2\) follows by subtracting four times the product from the squared sum. Its norm depends only on the gap, irrespective of the individual square classes of the two terms.

For \(D=1\), factor \((x-y)(x+y)=g^2\) and enumerate its positive divisor pairs. For every nonsquare \(D\), take a positive norm-one unit \(U+V\sqrt D>1\) from the continued fraction of \(\sqrt D\). The inverse unit sends \((x,y)\) to \((Ux-DVy,Uy-Vx)\). The first coordinate stays positive. For \(y>0\) the second coordinate decreases and becomes negative exactly when \(y<Vg\). Each orbit thus has a seed with \(0\le y<Vg\). The seed with \(y=0\) is \((g,0)\).

For a positive seed let \(s=\gcd(x,y)\). Then \(s\mid g\), and the primitive coordinates have norm \((g/s)^2\) and denominator less than \(Vg/s\). The verifier enumerates those solutions in consecutive unimodular convergent bases, using the previously proved bound on their coordinates. Scaling back by each divisor \(s\) gives the complete set of seeds. [Continued-fraction derivation](Erdos849PellSmall.md) · [Primitive enumeration](Erdos849PellSmall.py)

## Finite index sieve

Let \(x_t+y_t\sqrt D=(x_0+y_0\sqrt D)(U+V\sqrt D)^t\). In forward iteration \(x_t\ge U^t\ge2^{bt}\), where \(b=\lfloor\log_2 U\rfloor\). The verifier uses an integer \(E\) with \(2^{8(E-2)}>8!10^{250000}\). For \(bt\ge E\), the row \(n=(x_t+i+j)/2\) has \(n-7\ge2^{E-2}\), and its coefficient exceeds the height bound. It suffices to inspect indices smaller than \(\lceil E/b\rceil\).

Modulo a prime \(p>8\) the binomial polynomial in either column depends only on its row modulo \(p\). For each Pell orbit the verifier computes the period of the unit by multiplying it until the pair \((1,0)\) returns. The trace recurrence \(x_{t+2}=2U x_{t+1}-x_t\) gives the admissible index residues within that period. They must send \((x_t+i+j)/2\bmod p\) to a row whose eighth coefficient lies in the seventh-column image. Period masks from primes below 1100 eliminate indices from the finite range. Every surviving index is reconstructed by integer arithmetic. Integral rows also require \(y_t\) and \(x_t+i+j\) both even.

The primary run reproduces all 1,936 small-row pairs in direct enumeration through row 2,000. Its 2,338 Pell orbits leave 1,871 indices, the largest being 3. After parity checks and the lower bound \(n\ge16\), the two distinct candidate rows are 16 and 1,066,850,438, including the square-kernel case. Neither eighth-column coefficient occurs in column 7.

## Independent audit

The audit regenerates seeds using signed coordinates. Multiply a norm-\(g^2\) solution by a power of the unit so that \((x+y\sqrt D)/g\) lies between \((U+V\sqrt D)^{-1/2}\) and \((U+V\sqrt D)^{1/2}\). Then \(|y|\le g\sqrt{(U-1)/(2D)}\). Exhausting these signed coordinates and multiplying a negative-\(y\) seed once by the unit gives precisely the primary seed sets. The audit enumerates the periodic residues of the doubled row itself and removes rejected indices from an ordinary byte array. It uses a larger finite horizon and an independent binary search for seventh-column membership. Its exact checks on four rows, including a superset for \(D=1\), find no shared value.

```
python -B Erdos849WiderOdd.py
python -B Erdos849WiderOddAudit.py
python -B Erdos849SquareClassBound.py
```
