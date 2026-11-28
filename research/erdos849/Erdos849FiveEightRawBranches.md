# Individual prime assignments in columns five and eight

Every common value `a = C(n,5) = C(m,8) ≥ 10^136` has at least **40 distinct prime factors**. In each column, assign every prime divisor of `a` to a numerator position having greatest valuation at that prime. All 40 ordered pairs `(i,j)` are occupied. Each prime chooses precisely one ordered pair, so the 40 prime witnesses are distinct. This uses only columns five and eight.

Run `python -B Erdos849FiveEightRawBranches.py --all-cells` with the adjacent compressed certificate. The verifier checks 20 source families and their reflections, covering 6,792 residue-branch and position combinations. The largest absolute integer bound is 1,080,690. The table gives the maximum for each family across its residue branches. Each of the two reflected offsets uses the stated bound independently.

| Column-five offset | Column-eight offsets 0 and 7 | 1 and 6 | 2 and 5 | 3 and 4 |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 321,007 | 11,921 | 1,080,690 | 394,382 |
| 1 | 46,047 | 17 | 0 | 0 |
| 2 | 492,294 | 2,112 | 0 | 0 |
| 3 | 1,072,604 | 9 | 0 | 0 |
| 4 | 84,135 | 2,859 | 849,982 | 367,252 |

The certificate file uses the original eight positions `j=0,…,7`. It stores one representative from each pair `j,7−j`. The identity `(7−m)_8=(m)_8` preserves the binomial value and sends `m−j` and the auxiliary integer below to their negatives. The verifier expands `binom(−Z,t)` in the integer basis `binom(Z,r)`, then checks its integrality, height, local divisibility and sieve separately for the reflected position.

## The auxiliary integer

For a missing pair, set `y=m−j` and `Z=D a/((n−i)y)`. The program computes a sufficient integer `D` prime by prime. For `p≤8` and `e=v_p(a)`, enumerate the possible valuations `u=v_p(n−i)`, `v=v_p(m−j)` and whether their positions are forced by the maximal-valuation assignment. Discard pairs where both are forced. The factor in `D` is `p` to the maximum of `0` and `u+v−e`. The finite state enumeration distinguishes the one numerator term divisible by the least power of `p` greater than the column length, if that term exists. All other valuations are then fixed. Past `e=3+max(v_p(5!),v_p(8!))`, this term is the unique maximizer. The missing-pair condition allows at most one selected position to have that unbounded valuation. Thus the maximal cost stays constant or decreases after the enumerated range. For `p>8`, a positive valuation in a column belongs to exactly one term and equals `e`. A missing intersection incurs zero cost. These facts give `Z∈Z`.

More explicitly, when the deeply divisible numerator term of a column of length `k` is at position `s`, all other terms together have valuation `v_p(s!(k−1−s)!)`. Translating `e` by one translates the deep valuation `e + v_p(k!) − v_p(s!(k−1−s)!)` by precisely one. The stated cutoff already makes this term strictly deeper than every other term of both columns. Every larger `e` consequently reproduces the same choice of deep positions at the cutoff, with equal or smaller cost.

The resulting `D` is 25,200 for `i=2`. For each other `i` it is 50,400 when `j` is 2 or 5, and 16,800 for the other six offsets.

Reduce `Σ c_t binom(Z,t)` by the row equation `336 (n)_5=(m)_8`, using `Z=D ∏_{r≠i}(n−r)/(120y)`. The result is a regular polynomial `P(n,y)` plus a Laurent polynomial `F(n,y)` supported on `n^u y^v`, where `u<5` and `8u+5v<0`. A rectangular grid of degree plus one in each variable verifies that `P` takes integral values on integer pairs, using the Newton difference formula. Therefore `F` is integral on a missing intersection. If `T=y^(1/5)`, the positive row relation gives `T>B` and `lo*T^8<n<hi*T^8` for the explicit rational bounds in the verifier. These inequalities bound `|F|` at all heights simultaneously. The weights are distinct because `u<5` and `gcd(5,8)=1`. If the leading weighted term dominates in absolute value at `B`, its sign remains fixed as `T` increases.

## Divisibility on a residue class

At a good prime `p` larger than the certificate degree, the finite-field residue `(n,m)=(i,j)` is impossible for a missing pair because `40320(n−i)Z=D ∏_{r≠j}(m−r)`. The verifier exhausts all remaining residue pairs on the curve. On each pair, at least one partial derivative of the row equation is a unit. Fix the free coordinate to its residue plus `pT` and Hensel-lift the dependent coordinate. Its implicit series in `pT` has coefficients in `Z_p`. One of `n−i,y` is a unit, so the appropriate denominator identity for `Z` expresses `F` as an integral series in `pT`. Modulo `p^E` this gives a polynomial in `T` of degree at most `E−1`. Checking `F=0 mod p^E` on `T=0,…,E−1` proves that congruence for all integral `T`, by Newton differences. Thus `F/p^E` is integral on the entire residue class.

The program bounds this integer by the real inequalities and sieves the interval with images of `F/p^E` at other good primes. The finite-field computation includes points with `m=j` by using the identity with denominator `n−i`. Controls enumerate the auxiliary coordinate directly at two good primes for every original and reflected family. All divisibility checks, real bounds and finite sieves use standard Python integer arithmetic and rational arithmetic. The Hensel and residue method for columns five and seven is documented separately in [the five and seven argument](Erdos849FiveSevenCells.md).

For example, the `(4,2)` certificate at the row residues `(61,180)` modulo 251 leaves the integer 83,398 after the test primes through 383. Its residue modulo 389 is 152. Direct enumeration of the curve and auxiliary coordinate gives 266 possible residues modulo 389, and 152 is absent. The reflected certificate has the same finite-field image.
