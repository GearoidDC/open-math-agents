# Which pairs of numerator blocks must share an assigned prime?

Assign the full power of each prime dividing a common Pascal value \(a\) to a numerator term of maximal valuation in each row. Choices at ties may be made independently. In columns 3 and 5 take the individual terms. In an even column pair the first and last numerator terms, the second and penultimate, and so on.

| Columns | Pairs of blocks tested | Conclusion at every admissible collision |
|---|---:|---|
| 3 and 5 | \(3\cdot5=15\) | Every pair receives a common assigned prime. |
| 5 and 6 | \(5\cdot3=15\) | Every pair receives a common assigned prime, except possibly at \(a=3003\). |
| 6 and 8 | \(3\cdot4=12\) | Every pair receives a common assigned prime. |

These conclusions hold for every assignment. In particular an admissible common value of columns 3 and 5 must have at least fifteen distinct prime divisors. The same is true of columns 5 and 6 above 3003. The small value 3003 itself has four prime divisors, so it always leaves at least eleven of its fifteen block pairs empty. The two shallow four-column patterns exceed \(10^{128}\), and consequently satisfy all the applicable conclusions. [Height bound](Erdos849Focused128.md)

The computation below excludes every empty pair for \(a>10^{60}\). The published classification up to \(10^{60}\) gives no collision in columns 3 and 5 or 6 and 8, and just 3003 in columns 5 and 6. [Blokhuis, Brouwer and de Weger, Theorem 2.2](https://arxiv.org/pdf/1707.06893)

## An integer coordinate for an empty pair

Use the ordered polynomials \(A(X)=\prod_i(X-s_i)\) of degree three and \(B(Y)=\prod_j(Y-r_j)\) of degree five or four according to this table. A symbol \(n\) denotes the cubic-side Pascal row and \(m\) the other row.

| Pascal columns \(k,h\) | \(X\) | \((s_i)\) | \(Y\) | \((r_j)\) |
|---|---|---|---|---|
| 3, 5 | \(n-1\) | \(-1,0,1\) | \(m\) | \(0,1,2,3,4\) |
| 6, 5 | \((n-2)(n-3)\) | \(0,2,6\) | \(m\) | \(0,1,2,3,4\) |
| 6, 8 | \((n-2)(n-3)\) | \(0,2,6\) | \((m-3)(m-4)\) | \(0,2,6,12\) |

Here \(A(X)=k!a,\ B(Y)=h!a\). For an empty pair choose \(x=X-s_i,\ y=Y-r_j\). The checker calculates a positive integer \(D\) such that
\[
                            Z=\frac{Da}{xy}\ \in\mathbb Z .
\]
At \(p>\max(k,h)\), a numerator contains at most one multiple of \(p\), and the factorial denominators are units. Thus \(v_p(x)+v_p(y)\le v_p(a)\) at an empty pair. For the smaller primes the program bounds the excess \(v_p(x)+v_p(y)-v_p(a)\) as follows.

In a row of length \(l\), take \(P\) to be the smallest power of \(p\) greater than \(l\). Enumerate all row residues modulo \(P\). If no term vanishes, all valuations are exact. Otherwise just one term vanishes, and all its possible valuations from \(v_p(P)\) upwards are represented by a single variable. For each value \(e=v_p(a)\) record the sum of valuations on the selected block, and whether *every* maximal term lies in that block when \(e>0\). Match two such states at the same \(e\), discarding the case in which both block assignments are forced. For \(e=0\) there is no assignment. The maximum resulting positive excess determines the exponent of \(p\) in \(D\).

It suffices to enumerate \(0\le e\le 2+\max(v_p(k!),v_p(h!))\). Above this cutoff each row contains a unique term divisible by \(P\). Indeed \(e\) is the sum of carries in the binomial factorial-floor formula, with at most one contribution for each power of \(p\) up to the largest numerator valuation. Decreasing that exceptional term's valuation until the stated cutoff is reached still leaves it divisible by \(P\), since the sum of the other valuations is at most \(v_p(l!)\). The latter follows by subtracting the maximal term: the remaining valuations are bounded by the valuations of the nonzero differences of offsets, whose product divides \(l!\). Raising \(e\) again increases the selected valuation by one only in rows whose maximal term belongs to the selected block. At most one of the two can do this in an empty pair, so the excess cannot increase.

## Bounding and sieving an integer

For each of the 42 cells the certificate supplies an integer polynomial
\[
 F=P(X,y)+Q(Z),\qquad \deg_X P\le2,\quad Q(0)=0 .
\]
Substitute \(Z=(D/k!)\prod_{u\ne i}(X-s_u)/y\) and reduce in the cubic algebra given by \(A(X)=(k!/h!)B(y+r_j)\). The exact characteristic polynomial of multiplication by \(F\) has the form \(T^3+C_1(y)T^2+C_2(y)T+C_3(y)\), and each \(C_i\) is a Laurent polynomial having only strictly negative degrees when nonzero. The checker reconstructs this identity solely from the list of integer coefficients. The value \(T=F\) is a root by Cayley–Hamilton. [Characteristic-polynomial arithmetic](Erdos849ThreeFiveCells.py) · [Certificates](Erdos849CellSieve.json)

When \(a>10^{60}\), one has \(y\ge 2{,}600{,}000{,}000{,}000\) for \(h=5\) and \(y\ge14\cdot10^{15}\) for \(h=8\). Indeed \((h!a)^{1/h}\le m\); each original numerator term is at least \(m-h+1\), and in the eighth column \(y\) is the product of two such terms. For the appropriate lower bound \(L\), set \(M_i=\sum_e|[y^e]C_i|L^e\). An integer \(b>0\) satisfying \(M_1/b+M_2/b^2+M_3/b^3<1\) gives \(|F|<b\).

The checker divides \(F\) by \(g\), a fixed divisor known to divide every integer value of \(P(X,y)+Q(Z)\). It takes the gcd of separate evaluations of \(P\) and \(Q\) on the grid \(0,\ldots,d\) in each variable with \(d\) its degree in that variable. Interpolation by integer finite differences proves divisibility everywhere. Thus \(u=F/g\) is an integer with \(|u|\le\lfloor(b-1)/g\rfloor\).

For every prime \(p\le397\), use the modulus \(q=p\), replaced by 256, 243 and 125 for \(p=2,3,5\), respectively. Enumerate the residues of \(X,Y\) from the row formulas in the table. Require all three equations
\[
 A(X)=\frac{k!}{h!}B(Y),\qquad
 yZ=\frac{D}{k!}\prod_{v\ne i}(X-s_v),\qquad
 xZ=\frac{D}{h!}\prod_{v\ne j}(Y-r_v)
\]
after reducing each fraction and clearing its denominator. The last two equations are linear congruences in \(Z\). The search includes residues at which \(x\) or \(y\) vanishes and every permissible \(Z\). Record every residue \(u\bmod q\) with \(g u=F(X,y,Z)\bmod q\). All integer solutions must survive simultaneously at all moduli. The largest initial absolute bounds on \(u\) for the three column pairs were 363,522,742; 15,130,700,861; and 16,201,226,110, respectively. No integer in any of the 42 bounded intervals passed all the modular tests.

Run the standard-library verifier with ordinary Python assertions enabled. It compares its congruence solver with direct enumeration at moduli 7, 8 and 9, checks its bitset sieve against direct enumeration including both signs, and confirms the known value 3003 survives the modular tests at every one of its block pairs that gives an integral auxiliary coordinate. [Verifier](Erdos849CellSieve.py)
