# The tenth Lind–Singmaster value has exactly three rows

The 146,585,752-digit value $A=\binom{507544127}{193864605}$ occurs in exactly three admissible rows. The proper positions are $(507544126,193864606)$ and $(507544127,193864605)$. Its remaining occurrence is the edge at $(A,1)$. Admissibility means $1\le j\le m/2$ in row $m$.

The verifier uses the exact integer $A$ for the shallow columns, outward-rounded intervals for the middle columns, and a finite prime cover for the deep columns. The default run builds its own prime cover. [Verifier](Erdos849LindTenth.py)

## Shallow columns

Let $N=507544127$ and $K=193864605$. These are the Fibonacci products $F_{22}F_{23}$ and $F_{20}F_{23}$ for family index ten. GMP computes $\binom NK$ as an integer. Two integer powers of ten bracket it and certify the decimal digit count. A product and remainder tree computes its residues modulo the primes up to 320,000.

For each $2\le j<300000$, find a prime $p>j$ such that the nonzero residue $A\bmod p$ is absent from column $j$. By Lucas's theorem it suffices to check $\binom mj$ for $j\le m<p$. Writing $d=p-1-j$ and $m=p-1-s$, the residues are $(-1)^{d-s}\binom ds$ for $0\le s\le d$. Symmetry and an exact modular recurrence test these residues. All 299,998 columns are excluded. The largest prime witness is 300,007.

## An interval for the row of a given column

Lean verifies the product inequality and the resulting interval used for each column. [Lean proof](Erdos849FallingBounds.lean)

If $A=\binom mj$, put $R=(j!A)^{1/j}$, $u=(j-1)/2$, and $z=m-u$. The numerator factors pair as $z-t,z+t$ with $0\le t\le u$. The geometric mean of each pair lies between $\sqrt{z^2-u^2}$ and $z$. An unpaired middle factor is $z$ itself. Taking the full geometric mean gives

$$R+u\ \le\ m\ \le\ u+\sqrt{R^2+u^2}\ \le\ R+u+\frac{u^2}{2R}.$$

To enclose $R$, compute lower and upper bounds on $\log A$ by subtracting log-gamma endpoints in opposite rounding directions. At the start of each block of columns, initialize $\log((j-1)!)$ the same way, then add intervals for $\log j$. Exponentiating $(\log A+\log(j!))/j$ with downward and upward rounding gives $R_{\rm low},R_{\rm high}$. MPFR supplies the rounded arithmetic. The final interval uses the lower $R$ in the correction denominator. Its real endpoints are rounded outward before taking the integer ceiling and floor. [MPFR manual](https://www.mpfr.org/mpfr-current/mpfr.html)

If a candidate integer row lies between $l$ and $h$, then every prime dividing $A$ must have a multiple in $[l-j+1,h]$. The verifier chooses 32 primes in $(N-K,N]$, proves each prime by trial division, and checks the interval condition by integer division. On the known value 3003 the interval calculation recovers all three proper positions.

## The prime cover and the two known proper rows

Take $T=\lceil N/15\rceil=33836276$ and $B=T\,2^{15}=1108747091968$. If $j\ge T$, half-row monotonicity and the binomial product give

$$(m/T)^T\le \binom mT\le A\le 2^N\le 2^{15T}.$$

Thus $m\le B$ throughout these deep columns. Also $2^K\le A\le m^j$, so whenever $m\le B$ one has $j\ge S=\lceil K/\operatorname{bitlength}(B)\rceil$.

The prime 507,544,123 divides $A$ and forces $m\ge507544123$. The next prime after $N$ is 507,544,159. Starting there, the verifier selects 234,429 primes through the range ending at $B$. The largest gap between selected primes is 4,727,664, at most $S$, and the final uncovered tail is shorter than $S$. For each tested row from the first of those primes to $B$, a prime $p>N$ consequently lies in $(m-j,m]$. Since $p>m-j\ge j$, it would divide the binomial coefficient. This contradicts $A\mid N!$. The verifier certifies each selected prime by coprimality to the product of all primes up to the square root of the largest possible candidate. The prime finder only proposes numbers.

In the remaining rows from 507,544,123 through 507,544,158, exact ratios to $\binom NK$ locate the only possible crossing in each row. They give precisely the two proper positions above.

For rows above $B$, only the 33,536,276 columns $300000\le j<T$ remain after the shallow tests. Exactly 9,020,688 computed intervals contain a candidate integer above $B$. The prime-divisibility check rejects every one. This accounts for every admissible row and column.

## Reproduction

Run the following commands in a Python environment with gmpy2 2.2.1. The completed run used GMP 6.3.0 and MPFR 4.2.1. Each stage can also be run separately with the low, middle, or high option.

```sh
python -m pip install gmpy2==2.2.1
python Erdos849LindTenth.py --workers 6
```

An optional shorter calculation uses the published maximum gap of 1,476 between consecutive primes below $4\cdot10^{18}$. Pass `--published-gaps` to use that input. [Oliveira e Silva, Herzog and Pardi](https://sweet.ua.pt/tos/gaps.html)
