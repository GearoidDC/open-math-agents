# Prime exponents modulo three in simultaneous Pascal columns

Suppose \(a=\binom{n}{8}=\binom{m}{7}\) with \(n\ge16\) and \(m\ge14\). **At least seven distinct primes \(p>13\) satisfy \(3\nmid v_p(a)\).** In particular the cubefree part \(a/\prod_p p^{3\lfloor v_p(a)/3\rfloor}\) is at least \(17\cdot19\cdot23\cdot29\cdot31\cdot37\cdot41=10{,}131{,}543{,}907\). Either four-column pattern in the table inherits this all-height conclusion.

There are stronger bounds for large values. Let \(K\) denote the set of columns and write \(a=\binom{n_k}{k}\), with \(n_k\ge2k\). For \(a\ge10^H\) the third column bounds the number of distinct \(p>7\) with \(3\nmid v_p(a)\) from below.

| \(K\) | \(H\) | Number of primes |
|---|---:|---:|
| \(7,8\) | 53,592 | 9 |
| \(5,7,8\) | 447,400 | 13 |
| \(3,5,7,8\) | 1,771,744 | 15 |
| \(5,6,7,8\) | 3,963,304 | 18 |

## Cubic relations at large height

Let \(e_{ks}\in\{0,1,2\}\) for \(0\le s<k\), with \(\sum_s e_{ks}=3u_k\) in each row. At \(a\ge10^H\), the integer

\[
F=\prod_{k,s}(n_k-s)^{e_{ks}}
\]

can be a cube only if all exponents vanish. To see the geometric obstruction, take the simultaneous column curve defined by \((x_k)_k=k!t\), where the falling factorial has roots \(0,\ldots,k-1\). The curve is geometrically irreducible of degree \(\prod_{k<8}k\) over \(\mathbb Q(x_8)\). At the fiber \(t=0\) all offset tuples occur, each smooth with uniformizer \(t\). At the tuple \((s_k)_k\) the order of \(F\) equals \(\sum_k e_{k,s_k}\). If all these orders vanish modulo three, varying one offset forces that entire row constant modulo three. The row sum then forces this constant to zero unless \(3\mid k\). Each listed column set has at most one such \(k\), so the tuple condition forces its constant to zero too. Thus any nonzero exponent vector has some order prime to three and \(Z^3=F\) defines a geometrically irreducible cover of degree three. [Proof of the degree and zero-fiber assertions](Erdos849ReciprocalRunge.txt)

Here are the changes needed to the explicit Runge calculation for squares. We use its positive-branch expansion, weight notation, pigeonhole argument and norm calculation. Put \(d=8\), \(E=\operatorname{lcm}(K)\), \(W_k=E/k\), \(q=E/d\) and \(L=mE\). Basis monomials are \(\prod x_k^{i_k}Z^b\) for \(i_k<k\) when \(k<d\), \(i_d\ge0\), \(0\le b\le2\). Their weights are \(\sum W_k\beta_k\) where \(\beta_k=i_k+b u_k\). Count those of weight at most \(L\). Using \(u_k=0\) and \(u_k=\lfloor2k/3\rfloor\) gives upper and lower counts respectively. [Square-cover proof, §§2–4](Erdos849HigherSquare.txt)

On the disk \(|T|\le1/1000\), write \(U_k(0)=1\), \(\prod_s(U_k-sT)=1\). The bound \(|U_k-1|<1/20\) gives analytic cube roots of every shifted factor taking value one at zero. The row series is \(U_k^{i_k}\prod_s (U_k-sT)^{b e_{ks}/3}\); its magnitude is bounded by \(2^{\beta_k}\). Its coefficient of \(T^l\) has denominator dividing \((9k^2)^l\). Indeed replace \(T\) by \(9k^2T\), put \(U_k=1+9kV\), and divide the defining equation minus one by \(9k^2\). The resulting integral polynomial has \(V\)-derivative one at the origin, so coefficient recursion makes \(V\) integral. Each shifted factor lies in \(1+9T\mathbb Z[[T]]\); the cube root of \(1+9J\) is \(1+3B\), where \(B+3B^2+3B^3=J\) has a unique integral solution with constant term zero.

The rational coefficient group count is \(g=\prod k/E\) as in the square argument because all \(\beta_k\) are integers. The code checks the fiber count explicitly. It uses \(g(L+1)\) homogeneous conditions and the same coefficient bounds with the local denominator \(9k^2\). More explicitly let \(c_p=\sum_kv_p(k!)\), \(b_p=\max_k(kv_p(9k^2)+v_p(k!))\), \(D_h=\prod_{p\le d}p^{c_p+\lfloor hb_p/E\rfloor}\) with prime \(p\), and \(V=2^{\lfloor L/q\rfloor}(d!)^m\). At order \(h\le L\) each cleared equation has entries at most \(H_h=D_h(1+\lfloor L/q\rfloor)^{|K|}V1000^{\lfloor h/q\rfloor}\). The integer coefficient exponent \(C\) and the branch cutoff in the checker follow from the coefficient-box count and Cauchy's inequality in the cited proof. In particular the nonzero auxiliary polynomial vanishes on the integral solution if \(a\) reaches the branch cutoff.

For its norm the rank is \(D'=3\prod_{k<d}k\). Multiplying a basis element by a monomial requires at most one substitution \(Z^3=F\), since the raw \(Z\)-degree is at most four. The coefficient sum of \(F\) is at most \(\prod_k(k!)^2\). Each raw \(x_k\)-degree for \(k<d\) is at most \(2(k-1)+2k=4k-2\), giving at most \(3k-1\) rounds of monic reduction. A denominator-cleared round costs a factor of at most \(2d!\) in coefficient sum. Hence use \(T=N_{\max}\prod (k!)^2(2d!)^{\sum_{k<d}(3k-1)}\). The norm determinant is a nonzero integer polynomial after clearing denominators, with coefficient sum at most \(D'!(10^C T)^{D'}\). At an integral zero of the auxiliary polynomial this norm vanishes, which bounds the positive integer \(n_d\) by the coefficient sum and gives the tabulated cutoff. [Exact constants and monomial counts](Erdos849HigherCubes.py)

The allowed exponent vectors have dimension \(\sum(k-1)\) over \(\mathbb F_3\). Sending a vector to the class of \(F\) in \(\mathbb Q_{>0}^{\times}/(\mathbb Q_{>0}^{\times})^3\) is injective by the cube exclusion. A prime \(p>7\) occurs in only one term per row and has exponent \(v_p(a)\) there. The image is therefore supported on \(2,3,5,7\) and primes \(p>7\) with \(3\nmid v_p(a)\). Subtracting four dimensions gives the stated counts.

## Two small cubefree parts

For \(a<10^{53592}\), suppose two of the eight consecutive terms have cubefree part supported on \(S=\{2,3,5,7,11,13\}\). Write them as \(A_0x^3,B_0y^3\), where \(A_0,B_0\) are cubefree and supported on \(S\). Their gap is between one and seven. Divide both coefficients by their gcd, which divides the gap. After exchanging the terms if necessary the reduced coefficients satisfy \(A\le B,\ \gcd(A,B)=1,\ 1\le |Ax^3-By^3|\le7\), and \(\gcd(x,y)=1\). Each prime may occur to exponent one or two in either reduced coefficient or be absent. Up to exchange this gives \((5^6+1)/2=7,813\) coefficient pairs.

Choose \(b=2+\lceil 10\cdot53592/72\rceil\), \(Y=2^b\). A row with \(y\ge Y\) satisfies \(n\ge B y^3\ge2^{3b}\), so \((n-7)^8/8!\) exceeds the cutoff by \(8!<2^{16}\) and \(10^3<2^{10}\). It suffices to treat \(y<Y\). For \(y\le28\) exact integer cube roots give all possibilities. When \(A=B=1\), differences of cubes greater than seven have already excluded every \(y>28\).

For the other coefficients put \(\alpha=(B/A)^{1/3}\ge1\). The identity for the difference of cubes gives \(|x/y-\alpha|\le7/y^3\). Compute the dyadic rational \(\beta=\lfloor 4Y^3\alpha\rfloor/(4Y^3)\) using an integer cube root, so \(|x/y-\beta|<8/y^3\). For \(y>28\) this is less than \(1/(2y^2)\); the reduced fraction \(x/y\) is a regular continued-fraction convergent of \(\beta\) by Legendre's criterion. This also holds for rational \(\beta\), from the usual two mediant intervals for the two expansions of \(x/y\). The only discrepancy between the two finite expansions of \(\beta\) is the optional penultimate convergent in the expansion ending in 1; its distance from \(\beta\) is at least \(1/(2y^2)\).

For a convergent with denominator \(y\) and following digit \(c\), the determinant formula gives \(|x/y-\beta|\ge1/((c+2)y^2)\). Consequently one only needs to cube the coordinates when \(y<8(c+2)\), or at the final convergent if its denominator is still in range. Each surviving primitive pair of terms is multiplied by every positive integer that leaves its gap at most seven. For the resulting pair \(u<v\), all possible rows are \(v\le n\le u+7\), \(n\ge16\). Each is checked for exact seventh-column membership.

The finite verifier visited 33,997,978 convergents, found 306 unscaled pairs and 682 pairs after scaling. Across 1,227 possible rows the largest was 101,847,565. No eighth-column value appeared in column 7. Direct factorization of every endpoint through 20,000 cross-checks the pair construction. Thus in the finite range at most one of the eight terms has cubefree part supported on \(S\), and each of the other seven supplies a distinct prime \(p>13\) with \(3\nmid v_p(a)\). Above the finite cutoff the pair result supplies nine primes above 7, of which only 11 and 13 can be lost. [Finite verifier](Erdos849CubePairs.py)

Run with the Python standard library and assertions enabled.

```sh
python -B Erdos849HigherCubes.py
python -B Erdos849CubePairs.py --support 13 --workers 6
```
