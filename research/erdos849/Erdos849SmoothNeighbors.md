# Large prime divisors of repeated binomial values

Every binomial value $a\ge10^{128}$ in a column $8\le k\le n/2$ has **at least five distinct prime divisors greater than 100**. Thus any value occurring in five admissible rows would have at least five such divisors. The latter implication uses the existing five-row exclusion through $10^{128}$ and the classified small column pairs. The single-column result is independent of that exclusion and of the interpolation certificates.

There is also a complete count for 100-smooth values. For $a\ge2$ with all prime factors at most 100, exactly 16,748 values have multiplicity two. The six values with multiplicity three are 120, 210, 1540, 7140, 11628 and 24310. The only value of higher multiplicity is 3003, with four rows. Multiplicity includes the edge occurrence at $(a,1)$.

## The finite input

The corrected theorem of Luca and Najman counts 16,223 integers $x\ge2$ for which $x^2-1$ is 100-smooth. The two tables on Najman's publication page give the even and odd solutions. The accompanying compressed file merges and sorts them. The checker verifies that all 16,223 entries are distinct and that every prime factor of both $x-1$ and $x+1$ is at most 100. The published count supplies completeness. [Corrected paper, Theorem 1(e)](https://web.math.pmf.unizg.hr/~fnajman/FLFNMC.pdf) · [Published erratum](https://doi.org/10.1090/S0025-5718-2013-02696-8) · [Odd entries](https://web.math.pmf.unizg.hr/~fnajman/oddsort.txt) · [Even entries](https://web.math.pmf.unizg.hr/~fnajman/evensort.txt)

Every pair of positive 100-smooth integers two apart is $(x-1,x+1)$ for a listed $x$. Every adjacent pair is $((x-1)/2,(x+1)/2)$ for a listed odd $x$. This gives 29,597 pairs in all.

## Five prime divisors above 100

Suppose $a=\binom nk\ge X=10^{128}$ has at most four prime divisors above 100. It has at most 29 prime divisors in total. Every full prime power $P=p^{v_p(a)}$ satisfies $P\le n$. Indeed, the valuation of a binomial coefficient counts contributing prime-power levels, each of which is at most $n$. Hence $a\le n^{29}$.

If $k\ge40$, half-row monotonicity gives $\binom n{40}\le a$, so $n\le(40!a)^{1/40}+39$. Put $y=a/X\ge1$ and $U=\lceil(40!X)^{1/40}\rceil+40$. Then $n\le U y^{1/40}$, and the integer check $U^{29}<X$ implies $n^{29}<a$. This leaves $8\le k\le39$.

Each prime above 100 divides at most one of the $k$ numerator terms because their differences are less than 100. It survives the denominator $k!$. Hence at least $k-4$ terms are 100-smooth. Some two of those terms are one or two apart. Otherwise they would occupy a span of at least $3(k-5)>k-1$.

For every listed pair $(u,v)$, an ending row whose numerator of length at most 39 contains it satisfies $v\le n\le u+38$. The verifier checks every such row, counts nonsmooth terms in order, and computes the largest admissible binomial with at most four nonsmooth terms. The maximum is

$$
  \binom{11997652}{8}
  =10647522077356773685402580893147631379066786471945450
  <10^{128}.
$$

For the five-row corollary, five distinct rows require at least four distinct columns above column one. By the classified pairs, at most one of columns 2, 3, 4 and 6 occurs at these heights. Alongside 5 and 7 that yields at most three columns below 8. [Blokhuis, Brouwer and de Weger, Theorem 2.2](https://arxiv.org/abs/1707.06893)

## Exact multiplicities among 100-smooth values

For $2\le k\le n/2$, Sylvester's theorem gives a prime exceeding $k$ in the $k$ consecutive numerator terms. It survives division by $k!$. If $a$ is 100-smooth it follows that $k<100$, so all of the numerator terms are 100-smooth. Conversely a smooth numerator makes $a$ smooth. Thus any admissible proper row must end in an adjacent pair $n-1,n$ on the list. For each such pair the checker walks backward through the smooth terms to obtain every eligible column and groups the values by their integer binomial coefficient. Every eligible $a\ge2$ also has its edge row. [Sylvester's theorem as stated by Laishram and Shorey](https://www.impan.pl/shop/en/publication/transaction/download/product/82021)

Run `python Erdos849SmoothNeighbors.py` beside `Erdos849SmoothNeighbors.txt.gz` using the Python standard library. This is an exact integer calculation with the published enumeration as a theorem input.

The optional `--extended` check repeats the same argument with up to $t$ exceptional prime divisors. The smallest tested column $k_0$ satisfies $3(k_0-t-1)>k_0-1$. For $t=5,6,7,8,9,10,11,12$, the respective values of $k_0$ are 9, 11, 12, 14, 15, 17, 18 and 20. At or above each of those columns the number of distinct prime divisors above 100 is at least $t+1$ whenever the value is at least $10^{128}$.
