# Fifty-six distinct prime factors for high common values in columns seven and eight

Every `a = C(n,7) = C(m,8) ≥ 10^662` has at least **56 distinct prime factors**. Assign each prime power to a numerator term of greatest valuation in each column. Every pair `(n−i,m−j)`, `0 ≤ i < 7` and `0 ≤ j < 8`, receives an assigned prime. In particular each seventh-column term receives at least eight, and each eighth-column term receives at least seven.

Run `python -B Erdos849SevenEightRawFull.py`. The checker evaluates each family at its recorded lower height and verifies both members of the reflected pair `j,7−j` independently. It uses only standard Python integer and rational arithmetic.

The entries below are exponents `H` for which the corresponding cell is occupied for every `a≥10^H`.

| Seventh-column offset | Eighth-column offsets 0 and 7 | 1 and 6 | 2 and 5 | 3 and 4 |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 633 | 602 | 640 | 658 |
| 1 | 633 | 601 | 556 | 629 |
| 2 | 620 | 635 | 593 | 590 |
| 3 | 654 | 547 | 572 | 491 |
| 4 | 619 | 639 | 587 | 584 |
| 5 | 662 | 575 | 546 | 630 |
| 6 | 619 | 598 | 622 | 662 |

Counting the occupied pairs in this table already gives at least 42 distinct primes at `10^633`, 44 at `10^635`, 46 at `10^639`, 48 at `10^640`, 50 at `10^654`, and 52 at `10^658` from columns seven and eight alone. If column five is also present, its [coverage with column eight](Erdos849FiveEightRawBranches.md) gives every eighth-column term at least five assigned primes. At `10^622` the reflected offsets 2 and 5 each meet six seventh-column positions, so the three-column bound there is `2×6 + 6×5 = 42`.

If a pair were empty, the valuation calculation in `Erdos849RawCellTools.py` would give an integral `Z=D a/((n−i)(m−j))`. For each relevant prime `p≤8`, `D` accounts for the maximum of the sum of the selected term valuations minus `v_p(a)` subject to this emptiness. The unique potentially deep term in a block of length `k` at position `s` has valuation `v_p(a)+v_p(k!)−v_p(s!(k−1−s)!)`. Once both deep positions are uniquely determined, increasing `v_p(a)` cannot raise this maximum cost, because at most one of the selected terms may be a forced host. For `p>8` the cost is zero.

Put `x=n` and `y=m−j`. The curve equation is `8 (x)_7=(y+j)_8`, with falling factorial notation. Substitute `Z=D ∏_{r≠i}(x−r)/(5040 y)` into the stored integer combination of `binom(Z,t)`. Reduce powers of `x` using the curve equation. The nonnegative powers of `y` form a polynomial `P` which takes integral values on the full integer grid, as verified by a finite degree grid and Newton differences. The remainder `F` must therefore be an integer whenever the position pair is empty.

Every term `b x^u y^v` of `F` has `0≤u<7` and strictly negative weight `w=8u+7v`. The weights are distinct by coprimality. For `T=y^(1/7)`, the row equation proves `T≥B` and `lo*T^8 < x < hi*T^8`. At the recorded height, the sum of `|b|hi^u B^w` is less than one. The leading weighted term, evaluated with `lo`, exceeds the combined upper bounds for all other terms. After division by the leading power of `T`, those other upper bounds decrease as `T` grows. Hence `0<|F|<1` for every higher value, contradicting integrality. Reflection of the eighth-column row sends `Z` to `−Z`, and the program reconstructs and checks the corresponding binomial coefficients for the reflected position.
