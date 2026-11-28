# A term in the longer numerator needs two neighbors

Suppose \(a=\binom nd=\binom mk\), \(2\le k<d,\ n\ge2d,\ m\ge2k\). Assign every full prime power \(p^{v_p(a)}\) to a maximum-valuation term in each numerator, with any choices at ties. Join the assigned terms for each prime, counting distinct *neighbors* even if several primes join the same two terms.

Above the thresholds in this table **each of the \(d\) positions in the longer numerator has at least two distinct neighbors among the \(k\) positions**. The bounds are inclusive and apply to each pair of columns independently.

| \(k,d\) | 3,5 | 3,7 | 3,8 | 5,6 | 5,7 | 5,8 | 6,7 | 6,8 | 7,8 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Exponent \(K\) in \(a\ge10^K\) | 60 | 80 | 128 | 60 | 60 | 90 | 60 | 90 | 70 |

For the four pairs with exponent 60, the published classification through \(10^{60}\) shows that 3003, in columns five and six, is the only collision allowing a longer-row position with fewer than two neighbors. For all nine pairs in either four-column pattern the known height exceeds every threshold. The earlier strict neighborhood inequality gives at least two neighbors on the shorter side there as well. In particular the pair graph has at least \(2d\) distinct occupied position pairs. [Blokhuis, Brouwer and de Weger, Theorem 2.2 and Section 2](https://arxiv.org/pdf/1707.06893) · [Four-column heights](Erdos849PatternHeights.md) · [Shorter-side neighborhoods](Erdos849JointHosts.md)

## Local divisibility

Fix a position \(y=n-s\) and suppose every prime power assigned to it is assigned to \(x=m-r\) in the other row. An unused position satisfies this assumption for every \(r\). Each certificate is an integer polynomial \(F(y,x)=\sum C_{ij}y^ix^j\) and a positive order \(o\).

For a column \(q\) and offset \(b\), write \(c=q!/\prod_{v\ne b}(b-v)\). Thus \(|c|=q\binom{q-1}{b}\). Let \(L\) be the least positive integer for which \(Lc/(b-v)\) is integral for both columns and all their offsets \(v\ne b\). The branch series at the common value zero, in the parameter \(z=a/L\), is obtained by setting \(u=(\text{row}-b)/(Lc)\) and inverting
\[
 z=u\prod_{v\ne b}(1+Lc\,u/(b-v)).
\]
This power series has integer coefficients and linear term \(u\). For \(p^{e}\Vert a\) assigned at both chosen positions with \(e>\lfloor\log_p(d-1)\rfloor\), the actual \(u\) in each row has valuation \(e-v_p(L)>0\). Indeed every other term has valuation \(v_p(b-v)\), so the chosen term has valuation \(e+v_p(c)\). The branch series gives its value modulo arbitrary powers of \(p\) by recursive inversion. The verifier recomputes the series for \(F\) by integer Lagrange inversion and checks that its first \(o\) coefficients vanish. [Local branch identities](Erdos849InterpolatedPowers.txt) · [Lagrange power calculation](Erdos849PatternThree.py)

For \(p>d\), any \(p\mid y\) is unique in this row, is assigned here, and also divides \(x\) by assumption. The valuations of \(y\) and \(z\) both equal \(e\), giving \(v_p(F)\ge o\,v_p(y)\). At \(p\le d\) the checker computes an explicit loss \(\ell_p\) with \(v_p(F)\ge o\,v_p(y)-\ell_p\). Set \(t=\lfloor\log_p(d-1)\rfloor\), \(f=v_p(L)\) and \(w=v_p(d\binom{d-1}s)\). If \(v_p(y)\le t\), test each such ordinate, using only \(v_p(x)\ge0\). Otherwise \(y\) is the unique maximal term and \(v_p(y)=e+w\). If \(e>0\) the position \(x\) receives this power, so \(v_p(x)\ge e\); for \(e>t\) it has valuation exactly \(e+v_p(k\binom{k-1}r)\). The direct tests lower-bound \(v_p(F)\) by the minimum valuation of its monomials.

For a threshold \(e_0\in\{t+1,\ldots,t+4\}\) use the direct test below \(e_0\). For all \(e\ge e_0\), write the series of \(F\) as \(\sum_{j\ge o}A_j z^j\). Each nonzero term has deficit
\[
   o(e+w)-j(e-f)-v_p(A_j)
\]
relative to \(o\,v_p(y)\). Since \(j\ge o\), this is largest at \(e=e_0\). Every \(j\ge\lceil o(e_0+w)/(e_0-f)\rceil\) already has nonpositive deficit, so a finite truncation suffices. Take the maximum loss across both ranges and then the minimum over the four valid thresholds. This proves \(y^o\mid F\prod_{p\le d}p^{\ell_p}\).

## The size comparison

Write \(a=10^K b,\ b\ge1\). In a row of column \(q\), an offset term at \(v\) lies between \((R_q-v)b^{1/q}\) and \((R_q+q-v)b^{1/q}\), where \(R_q=\lfloor(q!10^K)^{1/q}\rfloor\). This follows by comparing the row's terms with their geometric mean. Order the monomials by their weight \(w=\operatorname{lcm}(k,d)(i/d+j/k)\), denote the largest weight by \(w_*\), and give the last coefficient positive sign by multiplying the whole polynomial by \(-1\) if necessary. The verifier checks that every suffix sum of the signed lower term bounds at \(b=1\) is strictly positive. Summation by parts then gives the same strict sign at every \(b\ge1\), since the factors \(b^{w/\operatorname{lcm}(k,d)}\) are nondecreasing. Separately bounding all positive and all negative terms at \(b=1\) gives an absolute upper bound \(B b^{w_*/\operatorname{lcm}(k,d)}\).

For each certificate the verifier checks \(d w_*\le o\operatorname{lcm}(k,d)\) and
\[
             B\prod_{p\le d}p^{\ell_p}<(R_d-s)^o.
\]
Together these give \(0<|F|\prod p^{\ell_p}<y^o\), contradicting divisibility. All \(311\) choices of a pair and its two offsets have certificates. Run \(\texttt{python -B Erdos849HostLeaves.py}\) with assertions enabled. [Verifier](Erdos849HostLeaves.py) · [Integer certificates](Erdos849HostLeaves.json)
