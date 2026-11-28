# Squareclass pairs in the numerators of common entries in columns 7 and 8

Suppose \(\binom n8=\binom m7\), \(n\ge16\), \(m\ge14\), and \(n-i=du^2,\ n-j=ev^2\) with \(0\le i<j\le7\) and \(d,e\mid210\). The ordered tuple \((i,j,d,e)\) must be realized in at least one of the small rows \(0,\ldots,8,15\), allowing zero squares in the small row. In particular, **if \(d,e>7\), there are just three possibilities**:

| \(i\) | \(j\) | \(d\) | \(e\) |
|---:|---:|---:|---:|
| 0 | 1 | 15 | 14 |
| 0 | 5 | 15 | 10 |
| 1 | 5 | 14 | 10 |

In all cases \(d\le15\). If \(e>15\), the small row must be \(j\), and \(j-i\) must equal \(d\) times a square. For example, a term of squarefree part 21 can never be followed, among the remaining terms \(n-j\), by one whose squarefree part divides 210. These restrictions hold at every height.

## Exact congruence classification

Equal classes force \(d(u+v)\le7\) by subtracting the two squares. This gives \(n\le56\), where the preceding direct binomial test excludes admissible collisions. For distinct classes, put \(g=\gcd(d,e)\), \(D=de/g^2,\ x=du,\ y=gv\). Then \(x^2-Dy^2=d(j-i)\). Use the 928 seeds from the prior Pell reduction and write \(\epsilon=U+V\sqrt D>1\) for its positive norm-one unit. Successive indices multiply \(x+y\sqrt D\) by \(\epsilon\). Each nonnegative solution belongs to a forward orbit because multiplication by \(\epsilon^{-1}\) lowers \(y\) until the next step would make it negative. The exact seed construction is given in [the preceding calculation](./Erdos849SquareClassRows.md).

Set \(W=27720\). **Every possible index is congruent modulo \(W\) to a signed index in its own orbit whose row is one of \(0,\ldots,8,15\).** The verifier finds all such signed indices by walking in each direction from the seed. Once the row exceeds 15 it continues growing in that direction, since \(x>0\) and the sign of \(y\) agrees with the direction after the first inverse step.

| Signed representatives of possible indices modulo \(W\) | Orbits |
|---|---:|
| None | 398 |
| \(0\) | 437 |
| \(-1\) | 25 |
| \(-1,0\) | 60 |
| \(-1,0,1\) | 8 |

There are 606 surviving orbit/residue pairs, spread across 530 orbits and 505 of the 836 ordered offset/class choices. The small rows really do give a common binomial value: 0 in rows below 8, 1 at row 8, and the reversed-column equality at row 15. They do not meet the admissibility bounds.

## Sieve and controls

For each prime \(p>8\), compute all \(n\bmod p\) such that \(\binom n8\bmod p\) belongs to the image of \(\binom m7\bmod p\). Both binomial polynomials have invertible denominators modulo \(p\). At an orbit index \(k\), the residue of \(n\) is \(x_k^2/d+i\bmod p\), where \(x_k+y_k\sqrt D=(x+y\sqrt D)\epsilon^k\). The pair \(\epsilon^T\equiv(1,0)\) or \((-1,0)\pmod p\) makes this **row residue** periodic with period dividing \(T\).

Start with the earlier index mask at \(T=W\), which already excludes 360 entire orbits. For each residue still requiring exclusion, apply additional primes with period dividing \(W\); when necessary lift the residue \(r\) to all \(r+jW\), \(0\le j<f\), at \(T=fW\). Remove \(r\) only when every lift is excluded. The tested multipliers are \(2,4,6,8,9,12,16,13\), using primes up to 40000 and the additional prime 49279. One need not assume coprimality between \(f\) and \(W\). All matrix powers, lifts, polynomial residues and class tests use integers. The controls compare binary powering with forward iteration across three periods, and derive the 505 permitted offset/class choices independently by direct examination of the small rows.

Run `python -B Erdos849OrbitDescent.py` alongside the existing Pell and binomial modules. The finite classification only cuts down potential indices. For any genuine small index \(k_0\), a finite collection of good-prime residue tests also admits arbitrarily large indices congruent to \(k_0\) modulo the common period of those tests. This accounts for the remaining infinite progressions and explains why their surviving residues alone do not establish an admissible collision.
