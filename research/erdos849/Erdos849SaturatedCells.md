# Integer-valued certificates for shared prime divisors

For a value at least $10^{128}$ shared by columns 5 and 8, every one of the 20 intersections of a column-five numerator term and a symmetric pair of column-eight terms receives a prime. Columns 3 and 7 require all 21 intersections, as do columns 6 and 7 when symmetric terms in column 6 are paired. Each statement holds for every choice among maximal-valuation terms when assigning primes. Each prime occupies exactly one intersection for a given pair of rows. The respective values therefore have at least 20, 21 and 21 distinct prime divisors.

The following argument uses only integer and rational arithmetic. Complementary modular sieves extend the conclusions to every height. [Columns 5 and 8](Erdos849FiveEightCellsSieve.md) · [Pairs with column 7](Erdos849SevenCellsSieve.md)

## Construction

For an odd column of length $k$, take $X=n$ with offsets $s=0,1,\ldots,k-1$. For even $k$, put $t=n-k/2+1$ and $X=t(t-1)$. The offsets are then $s=i(i+1)$ for $0\le i<k/2$. The factors $X-s$ multiply to $k!a$, and each quadratic factor in the even case is the product of two original numerator terms. Write $A(X)$ for their monic product and $B(Y)$ for the corresponding polynomial in the second column of length $h$.

Fix offsets $s,r$ and set $y=Y-r$. If no prime is assigned to the intersection, enumeration of the small-prime valuations gives an integer $D$ for which $Z=Da/((X-s)y)$ is integral. For primes larger than both column indices there is at most one divisible term in each numerator, so those primes require no factor in $D$. [Small-prime enumeration and the valuation cutoff](Erdos849CellSieve.md)

The certificate supplies integers $c_d$. Expand the integer-valued expression $\sum_d c_d\binom Zd$, substituting $Z=D A(X)/(k!(X-s)y)$ and reducing powers of $X$ using $A(X)=(k!/h!)B(y+r)$. Write the resulting Laurent polynomial as $P+F$, where $P$ contains precisely the nonnegative powers of $y$. To check that $P$ is integer-valued on the original row parameters, the verifier evaluates it on the rectangular grid from zero through its degree in each original parameter. Its Newton coefficients are finite differences of those values, so integrality on this grid implies integrality on every integer pair. An empty intersection would therefore make $F$ an integer.

## Exact bounds

Let $u=\deg A$ and $v=\deg B$. The verifier obtains rational constants $L,U$ and a positive integer $b$ by bounding each factor between the smallest and largest numerator factors. It checks $y>b^u$ and $L<X/y^{v/u}<U$ for all rows above the stated cutoff. A monomial $cX^i y^j$ in $F$ has weight $w=vi+uj<0$. All remaining powers satisfy $0\le i<u$, and $u,v$ are coprime, so different monomials have different weights.

At $y=b^u$, the sum of the upper bounds $|c|U^i b^w$ is less than one. For the term of largest weight its lower bound $|c|L^i b^w$ exceeds the combined upper bounds for all other terms. At every larger $y$, all terms shrink in the upper estimate and the ratios of the other bounds to the leading lower bound decrease. Thus $0<|F|<1$, contradicting integrality.

Run `python -B Erdos849SaturatedCells.py` with assertions enabled. The three output lines verify all 62 intersections. [Verifier](Erdos849SaturatedCells.py) · [Integer coefficients](Erdos849SaturatedCells.json)
