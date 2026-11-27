# Five admissible rows require a value greater than $10^{128}$

No value in $(10^{105},10^{128}]$ occurs in five distinct rows of the left half of Pascal's triangle. Combining this computation with the earlier base through $10^{105}$ gives the stated lower bound. This result has no assumption on the number of prime divisors. It is a finite integer computation outside the Lean kernel.

## Coverage

For an integer $a>1$, an admissible occurrence is $(n,k)$ with $1\le k$, $2k\le n$, and $\binom nk=a$. Each column supplies at most one row as its entries increase strictly. Column 1 supplies exactly the row $n=a$. Five rows therefore require four distinct proper columns $k\ge2$.

Above $10^{105}$ the nine pairs $(2,3),(2,4),(2,5),(2,6),(2,8),(3,4),(3,6),(4,6),(4,8)$ are excluded by the fixed-pair classifications. In particular, at most one of the four columns belongs to $\{2,3,4,6\}$. [Blokhuis, Brouwer and de Weger, Theorem 2.2](https://arxiv.org/abs/1707.06893)

Take $d$ to be the largest of the four proper columns.

* **$d\le9$.** All ten four-column subsets avoiding the nine forbidden pairs were checked.
* **$10\le d\le14$.** At least two of the three earlier columns belong to $G_d=\{5\}\cup\{7,8,\ldots,d-1\}$. All 80 triples $(j,k,d)$ with $j<k$ in $G_d$ were checked.
* **$d\ge15$.** Each row was tested for the simultaneous presence of at least two earlier columns from $G_d$. The last possible column is 214, since the central binomial coefficients increase and $\binom{428}{214}\le10^{128}<\binom{430}{215}$.

For each largest column the first and last rows are found by integer binary search, using comparisons of exact binomial coefficients and requiring $2d\le n$. The interval is open at the previous verified upper bound and closed at the new bound.

## Computation

For a prime power $q=p^e$ and columns through $d$, all row values are periodic modulo $q$ with period $P=p^{e+\lfloor\log_p d\rfloor}$. Vandermonde's identity proves this because $v_p(\binom Pi)=v_p(P)-v_p(i)\ge e$ for $1\le i\le d$. The valuation identity follows from $\binom Pi=(P/i)\binom{P-1}{i-1}$ and the base-$p$ digits of $P-1$. The program tabulates every residue in each required column over the complete period. A retained largest-column row must land in the image of every earlier column being tested.

For $d\le14$, two coprime CRT wheels of moduli $M$ and $N$ first restrict the largest-column row. With $a$ a left-wheel class, an integer row has the form $a+Mt$. If $b$ is an allowed right-wheel class, the corresponding sorted right coordinate is $bM^{-1}\bmod N$. Therefore $aM^{-1}+t\bmod N$ must belong to the sorted right coordinates. The bounded interval of $t$ needs at most two nonwrapping ranges in these coordinates after splitting the row interval into pieces of length at most $MN$. The C kernel uses exact integer endpoint calculations. It intersects the right coordinates with additional modular rules in 64-bit blocks before testing every surviving row against the remaining image tables. Prime powers and wheel sizes affect speed only.

For $d\ge15$, each prime $p>d$ gives a bit set for each largest-column residue. Bit $j$ is set precisely when the value in column $d$ lies in the image of column $j$ modulo $p$. For each integer row the program intersects these bit sets. If fewer than two elements of $G_d$ remain, the row cannot supply a necessary triple. The program uses fixed-width words when every column fits and Python integers for larger indices. In both paths a surviving bit is checked by exact inversion at the full coefficient. Every row in the stated interval was eliminated by the modular tests.

| Search on $(10^{105},10^{128}]$ | Rows or row-pattern pairs | CRT joins | Surviving the block masks | Surviving all local tests |
|---|---:|---:|---:|---:|
| Ten low-column patterns | 80,705,527,825,617,550 | 406,273,903,459 | 70,286,104 | 0 |
| Eighty middle-column triples | 196,353,887,142,951 | 227,513,444,613 | 358,174,026 | 0 |
| Largest columns 15 through 214 | 3,193,104,632 | — | — | 0 |

The two CRT counts of row-pattern pairs include repetitions across different column patterns. Earlier runs also verified the two intervals $(10^{105},10^{120}]$ and $(10^{120},10^{128}]$ separately.

## Reproduction and controls

The driver compiles the C kernel into a temporary library. On Linux it uses `cc` or `clang`. A Windows installation can use the Clang bundled with Lean via `--cc PATH`. Run these commands with Python's ordinary assertions enabled.

```text
python Erdos849FocusedCRT.py --lower 105 --upper 128 --all-low
python Erdos849FocusedCRT.py --lower 105 --upper 128 --middle --capacity 80000
python Erdos849FocusedHigh.py --lower 105 --upper 128
```

Every CRT run first compares its native join with direct enumeration of synthetic congruences on small rows and on rows above $2^{55}$. These controls require positive examples, negative examples, wrapped and unwrapped right ranges, multiple 64-bit words, and agreement at all three filtering stages. A separate control recovers the known proper triple $\binom{14}{6}=\binom{15}{5}=\binom{78}{2}=3003$. The high-column driver compares its surviving bits with direct integer binomial evaluations on a small interval and on an interval starting above $10^{12}$.
