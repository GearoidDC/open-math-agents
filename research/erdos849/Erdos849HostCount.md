# At least 32 primes in the two exceptional column patterns

Let \(a\ge10^{128}\) be a common binomial value in columns \(3,5,7,8\) or \(5,6,7,8\). Each of the eight factors in its column-eight numerator receives at least four distinct primes dividing \(a\). Consequently, **at least 32 distinct primes divide \(a\)**. The finite five-row exclusion through \(10^{128}\) extends the conclusion to every admissible common value in either pattern. The prime-power input uses the complete four-column pattern. The finite sieve needs only the common columns 5, 7, and 8.

Run the verifier with

    python -B Erdos849HostCount.py

The prime-power bounds used below are independently replayable with `Erdos849PatternThree.py` and `Erdos849PatternSixHost.py`. Together they give, for \(Y=a/10^{128}\ge1\) and every \(p^e\mathrel\Vert a\),
\[
 p^e\le p^{v_p(420)}QY^{1/36},\qquad Q=35519 .
\]

## A term with at most three assigned primes

Write \(a=\binom n8\). Assign each \(p^e\mathrel\Vert a\) to the first position of maximum \(p\)-adic valuation in \(n,n-1,\ldots,n-7\). The other seven terms together have valuation at most \(v_p(8!)\), as can be seen by counting multiples of \(p^i\) after removing a maximum. Hence the chosen term absorbs \(p^e\) and the eight remaining cofactors multiply to \(8!\).

Every term is at least \(LY^{1/8}\), where \(L=\lfloor(8!10^{128})^{1/8}\rfloor-7=37{,}643{,}505{,}995{,}031{,}279\). Suppose that one term \(n-s\) receives at most three primes. If none of the four bases \(2,3,5,7\) is assigned there, their contributions to the term divide \(8\cdot3\cdot5\cdot7=840\). All larger prime powers in the term are assigned there because they do not divide \(8!\). This would give \(n-s\le840Q^3Y^{1/12}<LY^{1/8}\), since \(840Q^3=37{,}641{,}028{,}070{,}821{,}560<L\). Thus the term receives at least one small base.

For a small prime \(p\), enumerate \(n\) modulo the first power \(M=p^u>8\). Nonzero residues of the eight terms have known valuations. If a zero occurs, it is unique, and it stays the maximum as its valuation increases. Starting its valuation at \(u\), every increase also increases \(e=v_p(a)\) by one. Thus the enumeration gives all possible pairs consisting of the exact \(p\)-part of \(n-s\) and a flag recording whether a positive power of \(p\) is assigned to the position. This enumeration checks the cofactor bound in the preceding paragraph. It also checks that the product of any one cofactor and its assigned factors \(p^{v_p(420)}\) is at most 117600. A term with at most three assigned primes therefore satisfies \(n-s\le117600Q^3Y^{1/12}\). Since \((117600Q^3)^{24}<L^{24}10^{181-128}\), this excludes every \(a\ge10^{181}\).

## Finite enumeration

For each decade \(10^d\le a\le10^{d+1}\), \(128\le d<181\), take \(q=1+\lfloor Q10^{(d+1-128)/36}\rfloor\). Retain each small-prime choice with \(p^e\le p^{v_p(420)}q\). Their prime parts multiply to \(B\); if \(c\) of their flags are set, then \(1\le c\le3\) and \(n-s=Bz\) where \(z\) is a product of at most \(3-c\) prime powers of bases at least 11, each at most \(q\). The value 1 pads products shorter than the maximum. We bound \(z\) both by \(q^{3-c}\) and by the interval for the eighth-column row obtained from the integer roots of \(8!10^d\) and \(8!10^{d+1}\).

The resulting 296 intervals with no additional prime power, 984 with one, and 332 with two are checked by modular sieving. For two powers \(u\le v\), each prime modulus imposes a bitmask on the possible \(v\), using \(n=Bu v+s\). Since the sieving primes exceed eight, the binomial polynomials are periodic modulo each prime. Their value in column eight must occur in both columns five and seven. All intervals together give **zero modular survivors**.

Replay also checks the residue-based small-prime options against direct factorizations for rows 16 through 2047, and checks the two-power bitset sieve against direct enumeration on a shorter interval with positive survivors. This is an exact integer computation in Python.

The Lean file checks the counting deductions from the per-term hypotheses. The Python verifiers establish those numerical hypotheses. [Counting lemmas](Erdos849EightHostCounts.lean)
