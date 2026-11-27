# Later members of the Lind–Singmaster family

Write $F_i$ for the Fibonacci numbers, starting with $F_0=0,F_1=1$. The value at index $i$ is

$$A_i=\binom{N}{K}=\binom{N-1}{K+1},\qquad
N=F_{2i+2}F_{2i+3},\quad K=F_{2i}F_{2i+3}.$$

Index 1 gives 3003. We count the usual left half of the triangle, with $1\le j$ and $2j\le m$. Every value has its edge occurrence $\binom{A_i}{1}$.

## Finite shallow-column exclusions

For every index from **9 through 100**, none of columns **2 through 64** contains $A_i$. The triangular column 2 is also excluded at every index **101 through 160**. These 5,856 integer certificates use 684 distinct primes, the largest being 32,106,583.

For each index and column $j$, the certificate supplies a prime $p>j$. Lucas's theorem gives $A_i\bmod p$ by multiplying binomial coefficients of the base-$p$ digits. It also gives $\binom mj\equiv\binom{m\bmod p}{j}\pmod p$. For $y=A_i\bmod p$, a field element $x$ represents the target exactly when

$$f(x)=x(x-1)\cdots(x-j+1)-j! y=0.$$

The search tests that $\gcd(f(X),X^p-X)=1$, or, for $j=2$, that $8y+1$ is a quadratic nonresidue. The search uses the lower Lind row. A separate verifier computes the same values from the upper Fibonacci row, obtains the digit binomials by direct modular products, tests triangularity by quadratic reciprocity, and enumerates all nonzero column values for $j\ge3$. Its enumeration steps from row $j$ through row $p-1$ by the exact adjacent-row ratio. These calculations do not expand the Lind coefficients.

Run the two checks from this directory.

```text
node Erdos849LindShallow.cjs --verify Erdos849LindShallowExtended.json
node Erdos849LindShallowVerify.cjs Erdos849LindShallowExtended.json
```

To regenerate the prime table in search order, run the following command.

```text
node Erdos849LindShallow.cjs --last 100 --columns 64 --triangular 160 --limit 65000000 --certificate Erdos849LindShallowExtended.json
```

## The ninth value has exactly three rows

The 21,386,570-digit value $A_9=\binom{74{,}049{,}690}{28{,}284{,}464}$ has exactly two proper occurrences. The other is $\binom{74{,}049{,}689}{28{,}284{,}465}$. Including column 1 gives exactly three rows.

```text
node Erdos849LindNine.cjs --local
```

This mode verifies its own cover by primes. Put $T=\lceil N/19\rceil=3{,}897{,}353$. The program sieves through $N$ and constructs $A_9$ by Legendre's formula and a product tree. It checks the two exact powers of ten that bracket $A_9$. For primes up to $T+100{,}000$ that do not divide $A_9$, a remainder tree computes the residues used for the low columns.

For each $2\le j<T$, take a prime $p>j$ and write $d=p-1-j$. All possible nonzero values in column $j$ are

$$\binom{p-1-s}{j}=\binom{p-1-s}{d-s}\equiv(-1)^{d-s}\binom ds\pmod p,\qquad 0\le s\le d.$$

The program enumerates these residues by multiplication by $(d-s)/(s+1)$, using symmetry to cover both $s$ and $d-s$. It requires a missing residue for the target in every column. The modular multiplication operands in this loop have product below $2^{53}$. An estimate for the integer quotient using the reciprocal of $p$ can differ by at most one, and both directions are corrected by exact integer comparisons. Tests against ordinary integer binomial coefficients cover the signs, symmetry, and endpoint cases.

For a remaining candidate $j\ge T$ with $2j\le m$, monotonicity in the left half and the product formula give

$$ (m/T)^T\le\binom mT\le\binom mj=A_9\le 2^N\le 2^{19T}.$$

Thus $m\le M=T2^{19}$. The largest prime below $N$ is $b=74{,}049{,}683$, and the program checks that it divides $A_9$, forcing $m\ge b$. The first prime above $N$ is $f=74{,}049{,}697$. For $f\le m\le M$, the program verifies there is a prime $p$ between $m-T+1$ and $m$ with $p\ge f$. Then $p>m-j\ge j$, so it divides the numerator of $\binom mj$ and does not divide $j!$. This is impossible since every prime divisor of $A_9$ is at most $N$.

To verify this local prime cover, the program places a short interval of length 2,000 every $T-2{,}000$ integers. It finds a candidate in each interval. A Fermat test only selects candidates. The program proves primality by a gcd with the product of **all** primes through $\lceil\sqrt{M+2000}\rceil$, obtaining the gcds with product and remainder trees. If a candidate is composite, its replacement is checked by trial division. It verifies directly that the gap between successive selected primes is less than $T$, including both ends of the covered range.

The completed local run covered all 3,897,351 low columns with witnesses at most 3,897,389. It checked 524,539 prime intervals up to row 2,043,335,409,664. The largest difference between successive selected primes was 3,895,630.

Only $b\le m<f$ remains. Starting with $\binom NK/A_9=1$, the program uses exact integer ratios to compare $\binom mK$ to $A_9$ and then walks within row $m$ to the only possible crossing in columns $j\ge T$. Exact equality occurs in the two Lind positions.

The faster command `node Erdos849LindNine.cjs` uses $T=\lceil N/41\rceil=1{,}806{,}090$ and the published maximum prime gap of 1,476 below $4\cdot10^{18}$. Its row ceiling is $3{,}971{,}633{,}911{,}619{,}911{,}680$. It also certifies a prime between this ceiling and $4\cdot10^{18}$ by a Proth certificate, so the upper endpoint falls within the published run of consecutive primes. [Oliveira e Silva, Herzog and Pardi, prime gap computation](https://sweet.ua.pt/tos/gaps.html)
