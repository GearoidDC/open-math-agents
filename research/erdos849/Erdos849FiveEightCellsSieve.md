# Every block intersection in columns five and eight is occupied

Suppose \(a=\binom{m}{5}=\binom{n}{8}\), with \(m\ge10\) and \(n\ge16\). Assign each full prime power of \(a\) in each row to a numerator factor of greatest valuation, with arbitrary tie breaking. **Every one of the five numerator terms in column five shares an assigned prime with each of the four symmetric pairs of numerator terms in column eight.** This applies to every admissible common value at every height. In particular at least twenty distinct primes divide such a value. Both proposed four-column patterns contain this pair.

## Complete search through \(10^{90}\)

The published search through \(10^{60}\) contains no \((5,8)\) collision. Above that bound we reused the exact CRT checker, specifying only columns 5 and 8. Its column-eight row intervals include every possible occurrence, and every surviving coefficient must lie in the column-five image at every test modulus. No row survived the local tests in either interval. [Blokhuis, Brouwer and de Weger, Theorem 2.2](https://arxiv.org/pdf/1707.06893) · [CRT checker](Erdos849FocusedCRT.py)

| Coefficient range | Column-eight row interval, inclusive | CRT joins | After block masks | After all residue tests |
|---|---:|---:|---:|---:|
| \((10^{60},10^{82}]\) | 119,039,222–66,940,671,636 | 4,629,246,665 | 121,390,202 | 0 |
| \((10^{82},10^{90}]\) | 66,940,671,637–669,406,716,329 | 30,860,161,500 | 773,419,868 | 0 |

~~~sh
python -B Erdos849FocusedCRT.py --columns 5 8 --lower 60 --upper 82 --capacity 20000 --mask-mib 16
python -B Erdos849FocusedCRT.py --columns 5 8 --lower 82 --upper 90 --capacity 35000 --mask-mib 64
~~~

On Windows both commands accept the existing verifier's optional --cc argument followed by the path to Lean's bundled Clang.

## A bounded integer in each putatively empty intersection

Write \(X=(n-3)(n-4)\), \(S=(0,2,6,12)\), \(R=(0,1,2,3,4)\). The factors \(X-s\) for \(s\in S\) are the paired terms at offsets \((3,4),(2,5),(1,6),(0,7)\), in that order. Their product equals \(8!a\), while \(\prod_{j\in R}(m-j)=5!a\). Fix \(s=S_i,j\in R\) and put \(y=m-j\). If this intersection receives no prime, the integer \(D\) supplied by the missing-cell denominator calculation makes
\[
                  Z=\frac{Da}{(X-s)y}
\]
integral. This denominator calculation uses all local maximal-valuation assignments compatible with an empty intersection, including ties. [Prime-state and denominator verifier](Erdos849SaturatedCells.py)

For each intersection the certificate gives integer coefficients \(c_d\), with at most 24 coefficients. Form \(\sum_d c_d\binom Zd\). On replacing \(Z\) by \(D\prod_{v\ne s}(X-v)/(8!y)\) and \(X^4\) by its polynomial expression from \(\prod_{s\in S}(X-s)=336\prod_{q\in R}(m-q)\), the result is \(P(X,y)+F(X,y)\). The former collects the nonnegative powers of \(y\). The program verifies that \(P\) is integer-valued on the original rows by its finite grid of degree-bounding size and the integer-valued Newton basis. Thus \(F\) is integral under the empty-intersection hypothesis.

Every monomial \(bX^u y^v\) of \(F\) has \(5u+4v<0\). The row comparison at \(10^{90}\) gives explicit \(B,H\) with \(y\ge B^4\) and \(0<X\le H y^{5/4}\). Consequently
\[
 |F|\le\sum_{u,v}|b|H^u B^{5u+4v}.
\]
All calculations use exact rational arithmetic. In the following table each entry is the resulting integer upper bound on \(|F|\). [Certificate](Erdos849FiveEightCellsSieve.json) · [Exact height and integrality calculations](Erdos849SaturatedCells.py)

| Column-eight offsets | \(j=0\) | \(j=1\) | \(j=2\) | \(j=3\) | \(j=4\) |
|---|---:|---:|---:|---:|---:|
| \((3,4)\) | 1,968 | 120,453 | 1,619,113 | 191,349 | 1,771 |
| \((2,5)\) | 97,469 | 1,853 | 7,868 | 1,244 | 104,640 |
| \((1,6)\) | 213 | 0 | 0 | 0 | 199 |
| \((0,7)\) | 21,645 | 2,485,865 | 52 | 0 | 1,060 |

## No integer, including zero, survives

For each prime exceeding both 8 and the length of the certificate, up to 139, enumerate all \(X=t(t-1)\) and all \(m\) modulo that prime for which the curve equation holds. When \(y\ne0\), the Laurent expression evaluates \(F\) directly. When \(y=0,\ X\ne s\), evaluate \(\sum_d c_d\binom Zd-P(X,0)\) using \(Z=D\prod_{q\ne j}(m-q)/(5!(X-s))\). All indicated denominators are units at the chosen prime. At \(y=0,\ X=s\) the identity \(8!yZ=D\prod_{v\ne s}(X-v)\) has nonzero right side, excluding this residue for an integral \(Z\).

The resulting residue tests eliminate every integer in each signed interval, also when the interval consists solely of zero. Controls reconstruct the first two images in each cell by enumerating \(Z\) and using both multiplied identities. A second control compares the intersection of periodic bitsets with a direct signed-interval enumeration. Run the final checker with assertions enabled. [All twenty finite sieves](Erdos849FiveEightCellsSieve.py)

~~~sh
python -B Erdos849FiveEightCellsSieve.py
~~~
