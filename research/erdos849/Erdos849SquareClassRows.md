# Odd prime exponents in repeated Pascal entries

Every admissible common value of columns 7 and 8 has at least **seven distinct primes greater than 8 that occur to odd exponents**. Above $10^{250000}$ it has at least **nine**. Thus these primes still divide the value after its largest square divisor is removed. The two four-column patterns inherit both bounds. The finite and large-height proofs overlap.

More generally, if an entry occurs in at least five admissible rows and $d$ is its largest proper column, at least seven primes **greater than $d$** occur to odd exponents. For $d\ge10$ there are at least eight. The last section gives the additional published input for this generalization.

In particular **no positive integer of the form $b s^2$ with $b<955{,}049{,}953$ can occur in five rows**. Indeed $d\ge8$, and the smallest possible product of seven distinct primes greater than 8 is $11\cdot13\cdot17\cdot19\cdot23\cdot29\cdot31=955{,}049{,}953$. Every prime occurring to odd exponent in $b s^2$ must divide $b$.

## Two small square classes in eight consecutive integers

Write $a=\binom n8$. A prime greater than 7 divides at most one of the eight numerator terms, and does not divide $8!$. A term with no such prime to an odd exponent is $d u^2$ for a positive divisor $d$ of 210. The computation proves that for $a\le10^{1000000}$, at most one of the eight terms can have this form when $a$ is also in column 7.

Suppose $n-i=du^2$ and $n-j=ev^2$ with $0\le i<j\le7$. If $d=e$, the difference gives $d(u+v)\le7$, hence $n\le56$. Direct binomial inversion excludes rows 16 through 56. Otherwise put $g=\gcd(d,e)$, $D=de/g^2$, $x=du$, $y=gv$. Then $D>1$ is squarefree and

$$x^2-Dy^2=d(j-i)=N.$$

For each $D$ the verifier finds a positive unit $U+V\sqrt D$ of norm one. Its inverse sends $(x,y)$ to $(Ux-DVy,Uy-Vx)$. The first coordinate stays positive, and while the second stays nonnegative it strictly decreases for $y>0$. The inverse makes it negative exactly when $y^2<V^2N$. All possibilities therefore come from the finite list $0\le y\le\lfloor\sqrt{V^2N-1}\rfloor$ by nonnegative powers of the unit. Both forward and inverse multiplication preserve $d\mid x$, $g\mid y$ since $d\mid Dg$ and $g\mid d$. An initial $y=0$ is retained. Across all offsets and distinct classes this gives 928 orbits covering 836 choices of $(i,j,d,e)$.

At each prime $p>8$ used in the sieve, the binomial polynomial in any tested column depends only on its row modulo $p$. The Pell recurrence is periodic modulo $p$. For each index in its computed period the verifier forms the eighth-column row $x^2/d+i$ modulo $p$ and tests its coefficient for membership in the other column images. A mask of residues modulo 27,720 combines all tested periods dividing that modulus. Each additional period filters the finite interval of indices from 0 through 209,999. This covers the claimed heights because after $t$ forward steps $x\ge2^t$, $n\ge4^t/210$ and $a\ge(n-7)^8/8!$. The verifier checks the endpoint with integers.

For columns 7 and 8, 360 of the 928 orbits have no allowed index at any height. The finite sieve leaves 513 orbit/index pairs, all at indices 0 or 1. Direct binomial evaluation finds no admissible collision. The small-row control compares the Pell construction with every pair of actual terms through row 3,000.

There is also a restriction that applies at **every height** to each four-column pattern. If two terms have distinct small square classes $d,e$, the same two offsets and classes must occur at some row $1\le n_0\le8$, allowing zero as a square there. Exactly 492 pairs of offsets and classes survive the periodic sieve in either pattern. The verifier compares the entire surviving set with the set from those eight small rows. These small rows explain the surviving congruences and provide no admissible example.

## An explicit bound for a square product across two rows

Let $X$ and $Y$ be the seventh- and eighth-column row indices. Choose an even number $2u$ of the seven terms $X-i$ and an even number $2v$ of the eight terms $Y-j$, with at least one term chosen. Let $F(X,Y)$ be their product. We prove that if $F(X,Y)=Z^2$ at an admissible point, then $a<10^{250000}$. The proof builds a polynomial with integer coefficients which must vanish at any larger integral point.

Write $(X)_7=(Y)_8/8$ for falling factorials. Over $\overline{\mathbb Q}(Y)$ the equation has degree seven and is irreducible. At infinity each root has valuation $-8/7$ with $v(Y)=-1$. A proper monic factor would have a constant term of nonintegral valuation. At the zero fiber the choices $X=i$, $Y=j$ are independent simple roots. The common value is a local parameter there. Some choice makes exactly one of the two terms for these offsets selected, so $F$ has order one at that point. Indeed the seventh column cannot be wholly selected, and if its selection is empty some eighth-column term is selected. Thus $F$ is not a square in the function field. Adjoining $Z$ gives a field of degree 14 over $\mathbb Q(Y)$ with basis $X^iZ^b$, $0\le i<7$, $0\le b\le1$.

Put $\alpha=8\cdot10^8$, $\beta=8\cdot10^7$ and write $a=\beta^8 w^{56}/8!$, $z=1/w$. Since $\beta^8/8!=\alpha^7/7!$, the positive row branches at infinity have leading terms $\alpha w^8$ and $\beta w^7$. For $k=7,8$ respectively use $(h,\gamma)=(8,\alpha),(7,\beta)$. The normalized row is the branch $U(0)=1$ of

$$\prod_{i=0}^{k-1}(U-i z^h/\gamma)=1.$$

It is holomorphic in a neighborhood of the closed unit disk with $|U-1|<1/32$. On the circle $|U-1|=\delta=1/32$, the difference between the left side minus one and $k(U-1)$ is bounded by $\sum i/\gamma+\sum_{j=2}^k\binom kj(\delta+k/\gamma)^j<k\delta$. Rouché's theorem gives one simple root, varying holomorphically. For real $w\ge1$ the binomial product bounds identify it with the actual positive row. Each shifted normalized factor lies in the disk of radius $1/2$ about one and has a holomorphic square root taking the value one at zero. Their product describes the positive $Z$ branch.

These expansions have integral coefficients after replacing $z$ by $1680t$ and removing the leading poles and constants. To see this, $s=(1680t)^h/\gamma$ is divisible by $4k^2$ in $\mathbb Z[t]$. Substitute $U=1+4kV$ and divide the equation minus one by $4k^2$. The resulting polynomial is integral with derivative one in $V$ at the origin, so coefficient recursion gives $V\in\mathbb Z[[t]]$. Each shifted factor is $1+4A$ with $A(0)=0$ integral. Its square root is $1+2B$ where $B+B^2=A$, again integral by recursion.

Use the monomials $X^iY^jZ^b$ with $i<7$, $j\ge0$, $b=0,1$, of weight $8i+7j+b(8u+7v)\le200$. There are between 308 and 360. They are linearly independent over $\mathbb Q$ by the field basis. After multiplication by $z^{200}$ each is holomorphic on the disk with absolute value at most $10^{280}$: $i+j+b(u+v)\le28$ and $2\max(\alpha,\beta)<10^{10}$. Its first 201 coefficients, after the substitution $z=1680t$, are integers bounded by $10^{280}1680^{200}<10^{1000}$ by Cauchy's estimate.

There is a nonzero integer linear combination $P$ of these monomials, with coefficients at most $10^{2100}$ in absolute value, which cancels those 201 coefficients. In the cube of side $C=10^{2100}$ the number of integer vectors exceeds the number of possible outputs in the 201 equations: for $m$ unknowns the counts are $(C+1)^m$ and at most $(2mC10^{1000}+1)^{201}$. Subtract two vectors with the same output. The maximum-modulus principle on $z^{200}P/z^{201}$ now gives $|P|\le360\,10^{2380}/w$ for $w\ge1$. If $w\ge10^{2400}$, integrality forces $P=0$ at the point. Smaller $w$ already gives $a<10^{250000}$.

The field norm of $P$ is nonzero. Here is a height bound including the cost of taking the norm. In the rank-seven basis over $\mathbb Q[Y]$, multiplication by $X$ or $X-i$ has maximum column sum of polynomial coefficient norms less than $10^5$, with denominators dividing 8, by the monic seventh-degree relation. The norm of a polynomial here is the sum of the absolute values of its coefficients. Multiplication by $F$ costs at most $(10^5)^6 8^8<10^{38}$ and has denominators dividing $8^6$. The rank-14 matrix for multiplication by $Z$ uses only the identity and this last matrix as its nonzero blocks. Multiplication by $Y^j$ has norm one. The matrix for $P$, cleared by $8^{12}$, consequently has integer polynomial entries of norm less than $360\,10^{2100+30+38}8^{12}<10^{2184}$. Its determinant has norm at most $14!10^{2184\cdot14}<10^{30600}$. At an integral zero of $P$ the specialized determinant vanishes since the evaluation homomorphism kills $P$. A positive integer root $Y$ of a nonzero integer polynomial is at most its coefficient norm, by removing any power of $Y$ and applying divisibility to the constant term. Thus $a<Y^8\le10^{244800}$ in this case.

Finally, the vectors of selected offsets with even parity in both columns form a 13-dimensional vector space over $\mathbb F_2$. Map these vectors to rational square classes by multiplying their selected terms. The preceding bound makes this map injective for $a\ge10^{250000}$. Its image is generated inside a space spanned by $2,3,5,7$ and primes greater than 7 dividing $a$ to odd exponent. Each prime greater than 7 occurs in at most one term of either row separately, so its parity there equals its parity in $a$. At least nine primes beyond those four are necessary. This also supplies the large-height part of the seven-prime result.

## Using all four columns at sufficiently large heights

The same square-class argument gives at least 15 odd-exponent primes greater than 7 for $(3,5,7,8)$ and at least 18 for $(5,6,7,8)$ above effectively computable thresholds. Numerical cutoffs for these stronger bounds have not been evaluated.

On the geometrically irreducible four-column curve, choose a nonempty product $F$ with an even number of terms in each row. If some column has a proper nonempty selection, varying that coordinate above the unramified zero fiber gives a point of odd valuation. If only full columns are selected, a single full even column also has odd valuation. The only remaining possibility is both full columns 6 and 8, whose product is $56(6!a)^2$, never a square at an admissible point. In all other cases $Z^2=F$ gives a geometrically connected double cover. At every point above infinity all rows have a pole, and $F/\prod n_k^{2u_k}$ has residue one, where $2u_k$ is the number of selected factors in column $k$. Each such point splits on the cover, with residues $+1$ and $-1$ of $Z/\prod n_k^{u_k}$. The two signs are preserved by arithmetic Galois action. The common value function thus has at least two Galois orbits of poles. Ordinary Runge over $\mathbb Q$ gives an effective height bound for its integral values at rational points on the cover. Taking the maximum over the finite set of selections gives injectivity of the parity map beyond an effective bound. The vector spaces have dimensions $23-4=19$ and $26-4=22$; subtracting the four small primes gives the stated counts. [Irreducibility and zero-fiber argument](Erdos849ReciprocalRunge.txt) · [Beukers and Tengely, Theorem 1.2](https://shrek.unideb.hu/~tengely/BTRunge.pdf)

## Other possible largest columns in five rows

The finite five-row search and pair classifications give $a>10^{128}$, $d\ge8$, and columns 7 and 8 when $d=8$. Let the $d$-column numerator start at $m=n-d+1>d$. For $d=9$, $m>100000$ by the binomial size bound. Equation (6) and Theorem 2 with Table 1 of Mukhopadhyay and Shorey exclude counts from zero through six for the number of numerator terms carrying a prime greater than 9 to odd exponent. All relevant tabulated exceptions have $m<100000$. For $d\ge10$ and $m>d^2$, their Corollary 2 gives eight distinct primes greater than $d$ to odd exponents. Its extra condition for $10\le d\le13$ holds because $a>10^{128}$ forces $m>100000$. These primes survive division by $d!$. [Five-row reduction](Erdos849SevenAtAllHeights.md) · [Mukhopadhyay and Shorey, pp. 82–87](https://publi.math.unideb.hu/paper/924/download/10_5486_PMD_2004_2881.pdf)

If $m\le d^2$, the largest term is below $(d+1)^2$, so every prime greater than $d$ dividing a numerator term occurs just once. For $d\le36$ the row size contradicts $a>10^{128}$. For $37\le d\le293$ formula (5) in the same paper supplies at least eight such terms by direct prime counts. For $d>293$ formula (3) applies without exceptions and is larger than eight. [Mukhopadhyay and Shorey, pp. 80–82](https://publi.math.unideb.hu/paper/924/download/10_5486_PMD_2004_2881.pdf)

Lean checks that seven distinct numerator positions outside the small square classes give seven distinct primes above 8 of odd exponent. The all-height Lean theorem takes the finite exclusion and the nine-prime tail as explicit hypotheses. [Lean deduction](Erdos849OddExponentBridge.lean)

The independent finite replay generates the seeds directly as rows $n=e b^2+j$ and searches the indices with a byte per possible index. It uses a recurrence for the row numbers themselves. With $A=4U^2-2$, this recurrence is $n_{t+2}=A n_{t+1}-n_t+(2-A)(i+j)/2$, as follows by squaring the Pell coordinates and using their norm. It rebuilds the seventh-column images independently and uses binary search for exact membership.

Run the three verifiers from this directory with Python assertions enabled.

```sh
python -B Erdos849SquareClassRows.py
python -B Erdos849SquareClassAudit.py
python -B Erdos849SquareClassBound.py
```
