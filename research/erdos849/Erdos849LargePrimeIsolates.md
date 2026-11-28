# Every numerator term in the two four-column patterns has a prime above 7

Let \(K=(3,5,7,8)\) or \((5,6,7,8)\), and suppose \(a=\binom{n_k}{k}\) in every column \(k\in K\), with \(n_k\ge2k\). For every offset \(0\le s<k\), **\(n_k-s\) has a prime divisor greater than 7**. Such a prime divides \(a\) and occurs at a unique position in each row. In the incidence hypergraph formed by these primes, every vertex meets an edge.

The finite five-row search gives \(a>10^{128}\). The four-column prime-power bound implies, for each prime \(p\) dividing \(a\),

\[
p^{v_p(a)}\le p^{v_p(420)}35519(a/10^{128})^{1/36}.
\]

It also holds when \(p\) does not divide \(a\), since its right side exceeds one. [Height exclusion](Erdos849Focused128.md) · [Prime-power argument and dependencies](Erdos849JointHosts.md)

## The large-height bound

A term \(x=n_k-s\) divides the complete numerator \(k!a\). If all its prime factors are at most 7, then

\[
x\le k!\prod_{p\in\{2,3,5,7\}}p^{v_p(a)}
   \le 8!\cdot420\cdot10^4\,a^{1/9},
\]

where \(35519^{36}<10^{164}\). On the other hand \(x\ge(k!a)^{1/k}-(k-1)>a^{1/8}/2\) in the range considered. At \(a\ge10^{1000}\) the two inequalities contradict \((2\cdot8!\cdot420\cdot10^4)^{72}<10^{1000}\).

## Finite enumeration

Partition \((10^{128},10^{1000}]\) into intervals \((10^L,10^U]\) with \(U-L\le8\). For a 7-smooth term \(x\), its \(p\)-part \(P=p^{v_p(x)}\) must satisfy

\[
P^{36}\le (35519\,p^{v_p(420k!)})^{36}10^{U-128}
\]

for \(p=2,3,5,7\). This follows directly from \(v_p(x)\le v_p(k!)+v_p(a)\). The verifier enumerates products from the four finite lists of allowed powers, pruning only when all completions miss the integer interval

\[
\lfloor(k!10^L)^{1/k}\rfloor-(k-1)\le x
\le\lfloor(k!10^U)^{1/k}\rfloor+(k-1).
\]

Indeed \((n_k-k+1)^k\le k!a\le n_k^k\). Every possible row ending \(n=x,\ldots,x+k-1\) is then tested against the original coefficient interval. At each of three sieve primes \(p>8\), its binomial coefficient must occur in the images of the other three binomial polynomials on all row residues modulo \(p\). Each surviving value is tested for membership in those columns by integer root bounds and direct binomial comparison. For another column \(j\), \(r=\lfloor(j!a)^{1/j}\rfloor\) guarantees any admissible row is in \([r,r+j]\).

| Quartet | Column | Candidate terms | Rows in coefficient interval | Rows reaching exact checks |
|---|---:|---:|---:|---:|
| 3, 5, 7, 8 | 3 | 0 | 0 | 0 |
| 3, 5, 7, 8 | 5 | 0 | 0 | 0 |
| 3, 5, 7, 8 | 7 | 3,212 | 22,484 | 40 |
| 3, 5, 7, 8 | 8 | 33,186 | 265,488 | 2,107 |
| 5, 6, 7, 8 | 5 | 0 | 0 | 0 |
| 5, 6, 7, 8 | 6 | 35 | 210 | 0 |
| 5, 6, 7, 8 | 7 | 3,212 | 22,484 | 11 |
| 5, 6, 7, 8 | 8 | 33,186 | 265,488 | 466 |

No row passed the exact checks. Run the verifier with standard-library Python and assertions enabled. [Verifier](Erdos849LargePrimeIsolates.py)
