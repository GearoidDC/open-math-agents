# Disconnected prime assignments in two Pascal rows

Suppose \(a=\binom mk=\binom nh\), where \(2\le k<h,\ m\ge2k,\ n\ge2h\). For every prime \(p\mid a\), assign \(p^{v_p(a)}\) to a numerator term of maximal \(p\)-adic valuation in each row. Join the two assigned terms with an edge labelled \(p\). The graph has \(k+h\) vertices, including any unused terms. Choices at tied maxima are independent for every prime and every row.

**For the nine column pairs in \((3,5,7,8)\) or \((5,6,7,8)\), the only collision allowing a disconnected graph is \(\binom{15}5=\binom{14}6=3003\).** Both assignments for 3003 have seven components. At all other collisions in these pairs every assignment is connected. In particular such a collision has at least \(k+h-1\) distinct prime divisors.

More generally, for **every** \(2\le k<h\), disconnectedness implies the explicit bound
\[
               (h!a)^{1/h}\le 4 k h^2 (h!)^k .
\]
This also applies whenever \(a\) has fewer than \(k+h-1\) distinct prime divisors. The finite computations for the nine pairs use much narrower intervals.

## The denominator of a component ratio

For a chosen maximal term \(m-j\), any other \(m-i\) has \(v_p(m-i)\le v_p(i-j)\), by subtracting the two terms. Thus the product of the other terms has \(p\)-valuation at most \(v_p(j!(k-1-j)!)\le v_p(k!)\). Since the product of all terms is \(k!a\), the full \(p\)-part of \(a\) divides the chosen term. Divide each numerator term by all powers assigned to it; the resulting positive integers multiply to \(k!\). The analogous statement holds on the \(h\)-side.

In a disconnected graph choose a nonempty proper union of components. If this selects \(s\) terms of the first row and \(r\) of the second, the products \(X,Y\) of those terms contain the same product of assigned powers. Hence \(X/Y=q=C/D\) for some positive divisors \(C\mid k!\) and \(D\mid h!\). This includes one-sided cuts from unused vertices, with empty product one. Write \(e=hs-kr\). Passing to the complementary cut changes its sign, so it suffices to consider \(e\ge0\).

## Bounding the row without bounding the coefficient in advance

Write \(x=(k!a)^{1/k},\ y=(h!a)^{1/h}\) and \(H=h!/k!\). Assume \(y\ge h!\), which guarantees \(x\ge y\) because \(x^k=y^h/H\). We also have \(y\ge2(h-1)\). Each first-row term differs from its geometric mean \(x\) by at most \(k-1\), and each second-row term differs from \(y\) by at most \(h-1\). By integrating \(1/t\) between a term and its mean, each absolute logarithmic error is at most \(2(k-1)/y\) or \(2(h-1)/y\), respectively. Put \(S=s(k-1)+r(h-1)\). It follows that
\[
           |\log q-\log(x^s/y^r)|\le 2S/y.
\]

When \(e>0\), put \(y_*=(q^k H^s)^{1/e}\) and \(T=2kS/e\). The preceding inequality gives \(|\log(y/y_*)|\le T/y\). If \(y\ge2T\), then \(e^{T/y}-1\le 2T/y\), so \(|y-y_*|\le2T\). Since \(y\le n\le y+h-1\), all large admissible \(n\) lie in an explicit interval of width at most \(4T+h+2\) for each ratio, regardless of \(a\). Also \(y_*\le(h!)^k\) since \(q\le k!,\ s\le k,\ e\ge1\), and \(2T\le8kh^2\). These bounds, including the alternatives \(y<h!\) or \(y<2T\), imply \(y\le4kh^2(h!)^k\).

When \(e=0\), write \(s/k=r/h=b/t\) in lowest terms. A proper nonempty cut has \(0<b<t\), and \(t\) divides both \(k\) and \(h\). Thus \(h-k\ge t\ge2\), and \(H=(k+1)\cdots h\) is a product of at least two consecutive positive integers. By the Erdős–Selfridge theorem it is not a perfect \(t\)-th power. It follows that \(q^tH^b\ne1\). Before reduction the numerator \(C^tH^b\) and denominator \(D^t\) are at most \((h!)^t\). Integrating \(1/t'\) between two different positive integers \(u,v\) gives \(|\log(u/v)|\ge |u-v|/\max(u,v)\). Consequently
\[
             \frac{1}{k(h!)^k}
      \le |\log q+(b/t)\log H|\le \frac{2S}{y}\le\frac{4h^2}{y}.
\]
This proves the general bound. [Erdős and Selfridge, Theorem 1](https://www.renyi.hu/~p_erdos/1975-46.pdf)

## Exact search for the nine pairs

The standalone verifier checks every \(2h\le n\le100{,}000\) directly. For larger rows it uses \(y\ge n-h+1\), checks \(y\ge h!,2T\), enumerates all reduced factorial-divisor ratios and all nonbalanced oriented cut sizes, and merges their intervals before searching. The central estimate only requires the exact integer \(\lfloor y_*\rfloor\), computed by an integer root followed by a check of its defining inequalities. The only balanced size is \(s=3,r=4\) for \((k,h)=(6,8)\). For every ratio \(u/v\) in that case the verifier checks \(450|56u^2-v^2|\ge2\max(56u^2,v^2)\); this gives \(|\log(q\sqrt{56})|\ge1/450\), hence \(y\le450\cdot2(3\cdot5+4\cdot7)=38{,}700\). This calculation proves the concrete classification without using the general perfect-power theorem.

For each merged interval the program screens rows modulo ten primes larger than \(h\). In each modulus it enumerates the complete image of the degree-\(k\) binomial polynomial. Every survivor is tested with exact integer binomials: if \(z=\lfloor(k!a)^{1/k}\rfloor\), the possible first rows lie between \(z\) and \(z+k\). The program factors every matching value, enumerates all maximal-valuation choices, and calculates the graph's component counts.

| Columns | Rows checked after merging | Exact first-row tests |
|---|---:|---:|
| 3,5 | 99,991 | 5,802 |
| 3,7 | 100,331 | 8,582 |
| 3,8 | 125,500 | 16,460 |
| 5,6 | 105,127 | 3,171 |
| 5,7 | 168,255 | 3,708 |
| 5,8 | 208,053 | 29,676 |
| 6,7 | 142,331 | 690 |
| 6,8 | 201,203 | 3,117 |
| 7,8 | 307,892 | 33,532 |

Altogether the search inspected 1,458,683 row-and-column-pair candidates. Only \(3003=3\cdot7\cdot11\cdot13\) matched. Its first-row host for 3 can be either 15 or 12; the second-row host is 9. All other prime assignments are forced. The four edges form four disjoint pairs, leaving three isolated vertices.

Run Python with the filename below. The program uses only the standard library and keeps its verification checks active under optimization. [Erdos849FullHostCuts.py](Erdos849FullHostCuts.py)
