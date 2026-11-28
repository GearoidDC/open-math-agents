# A finite search with two large Chinese remainder wheels

The columns $5,6,7,8$ have no common binomial coefficient through $10^{170}$. The columns $3,5,7,8$ have no common binomial coefficient through $10^{141}$. The following searches extend the earlier cutoffs of $10^{146}$ and $10^{137}$ respectively and apply to every factorization. For $a\ge10^{170}$ the conditional-entropy bound for columns $5,6,7,8$ requires at least 41 distinct prime divisors. Thus every common value in that pattern has at least 41 distinct prime divisors. [Earlier finite searches](Erdos849FourHostPairs.md) · [Entropy proof](Erdos849ConditionalEntropy.md)

| Columns | Exponents $L,H$ in $(10^L,10^H]$ | First and last row in column 8, inclusive | After both wheels | After eight masks | After all local tests |
|---|---|---|---:|---:|---:|
| 3, 5, 7, 8 | 137, 141 | 501,984,220,261,427,947 to 1,587,413,485,489,756,716 | 1,294,426,086,893 | 204,881,620 | 0 |
| 5, 6, 7, 8 | 146, 150 | 6,694,067,163,264,088,894 to 21,168,499,046,056,743,538 | 158,142,826,851 | 1,894,625 | 0 |
| 5, 6, 7, 8 | 150, 160 | 21,168,499,046,056,743,539 to 376,435,059,950,312,860,011 | 3,881,523,731,408 | 46,484,766 | 0 |
| 5, 6, 7, 8 | 160, 170 | 376,435,059,950,312,860,012 to 6,694,067,163,264,088,890,240 | 762,969,479,576 | 6,765,331 | 0 |

For each prime power, take the full periodic residue image of each of the other three binomial columns. A row $n$ in column eight must give a coefficient in the intersection. The first pattern uses only these ordinary images. For columns $5,6,7,8$, a separate polynomial certificate leaves only $a\equiv0,1\pmod {113}$ through height $10^{175}$. The verifier replays this certificate before using the stronger residue set. [Prime-power periods](Erdos849FocusedCRT.py) · [Six disk certificates](Erdos849ResidueDisks.json)

The last interval also uses $53\mid a$ and excludes the following coefficient residues. The verifier checks the complete relevant fibers before applying these restrictions to the eighth row. [Divisibility by 53](Erdos849RequiredPrime.py) · [Mixed residue exclusions](Erdos849MixedDisks.py)

| Prime | Excluded values of $a$ modulo the prime |
|---:|---|
| 103 | 66 |
| 107 | 100 |
| 211 | 21, 197, 207, 210 |
| 293 | 73, 239 |
| 349 | 227, 240 |

Let $b$ be the first row in the interval. Translate the admissible sets by $-b$ and divide the selected moduli between two coprime products $M,N$. Write $n=b+c+a+Mt$, where $c$ is a multiple of $MN$, $0\le a<M$ is an allowed left residue, and $0\le t<N$. If $r$ is an allowed right residue, put $y=rM^{-1}\bmod N$ and $s=aM^{-1}\bmod N$. Then $t=(y-s)\bmod N$. For each $a$ the interval imposes $0\le t<d$ for an explicitly computed $d\le N$. This selects a cyclic interval starting at $s$ in the sorted array of $y$ values. The verifier processes the left residues in order of $s$ and advances a cursor to each endpoint. Equal phases can shift the upper endpoint backwards by one. Cutting the right array into contiguous blocks preserves this selection.

On each side of the cyclic wrap, $t=y-s+e$ with $e=0$ or $N$. For an additional period $q$, the translated row has residue $c+a+M(e-s)+My\pmod q$. The verifier precomputes a bit mask over the right residues for every phase $c+a+M(e-s)\bmod q$. It intersects these masks and tests every survivor against the remaining prime-power images. For any row surviving every modular test it checks the original binomial equalities with exact integers. [Native join](Erdos849WideRows.c) · [Verifier and controls](Erdos849WideRows.py)

The two wheel periods for the first pattern are 28,389,481,111 and 11,177,154,623. In the second pattern the initial periods are 108,653,242,447 and 4,009,686,221. On the last interval the periods are 6,241,759,568,533 and 969,740,313,809, with 41,932,800 and 17,432,576 residues. Products modulo a wheel period are computed from four precomputed 16-bit digit tables. The reconstructed row and interval endpoints use Python integers. Controls compare all three stage counts with direct enumeration on small intervals, including negative and 149-bit translations. Independent CRT reconstruction tests a range longer than three full periods with combined period above $2^{80}$, both with and without splitting the sorted right array into blocks.

Run with Python 3.10 or newer and a C compiler. The verifier looks for `clang` or `cc` on `PATH` and accepts a compiler path with `--cc`. On Windows use Clang with LLD. The final command used approximately 1.5 GiB during sorting and 83 seconds for the wheel setup and join on the reference machine.

```sh
python Erdos849WideRows.py --pattern 3 --lower 137 --upper 141 --optimize --left 35000000 --right 12000000
python Erdos849WideRows.py --lower 146 --upper 150
python Erdos849WideRows.py --lower 150 --upper 160
python Erdos849WideRows.py --lower 160 --upper 170 --optimize --left 42000000 --right 19000000 --required-53 --mixed 103=66 107=100 211=21,197,207,210 293=73,239 349=227,240
```
