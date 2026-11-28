# An odd-exponent prime above 100 in a bounded common value of columns 7 and 8

Suppose $a=\binom n8=\binom m7$ with $n\ge16$, $m\ge14$, and $a\le 10^{3{,}210{,}000}$. At least one prime above 100 divides $a$ to odd exponent. This applies to both four-column patterns containing columns 7 and 8. The argument uses the upper bound on $a$.

Suppose instead that every prime above 100 has even exponent in $a$. A prime $p>7$ can divide only one of the eight integers $n,n-1,\ldots,n-7$, and $p$ does not divide $8!$. Thus each term has squarefree part supported on primes at most 97. For each term count the primes from 11 through 97 occurring to odd exponent in that term. These eight counts sum to at most 21, the number of primes in that interval.

The two smallest counts sum to at most four. Indeed, if the smallest count is $0,1,2$ and the two smallest sum to at least five, the total is at least $35,29,23$ respectively. A smallest count of at least three gives a total of at least 24. Take the two offsets $i,j$ corresponding to the two smallest counts. The squarefree part $D$ of $(n-i)(n-j)$ is the product of a divisor of 210 and at most four distinct primes from 11 through 97. This yields exactly

$$16\sum_{r=0}^4\binom{21}r=120{,}752$$

possible squarefree values of $D$, including 1. For each, the positive integer $w$ defined by $(n-i)(n-j)=D w^2$ satisfies

$$(2n-i-j)^2-D(2w)^2=(j-i)^2.$$

The verifier checks all 28 choices of offsets. It handles $D=1$ by factoring the difference of two squares. For every other $D$, it enumerates the starting points of the Pell recurrences for each gap, follows every orbit up to the height bound, filters indices by the possible seventh-column values modulo small primes, and checks surviving rows by exact binomial membership. It also compares the enumerated pairs for rows 16 through 2,000 against direct squarefree factorization. The elementary bounds for the orbit indices depend on the height and the unit for $D$, so the same argument applies to the whole list of kernels. [Pell completeness proof and height bound](Erdos849WiderOdd37.md)

## An all-height consequence for columns 5, 7 and 8

If $a$ occurs in all three columns 5, 7 and 8, its squarefree part is at least

$$101\cdot103\cdot107\cdot109\cdot113\cdot127\cdot131=228{,}098{,}450{,}046{,}409.$$

This holds at every height for both four-column patterns and for every five-row value whose largest proper column is eight.

To obtain the finite part, write $t$ for the number of primes greater than 100 dividing $a$ to odd exponent. If $t\ge7$, the product of the seven smallest such primes gives the bound immediately. If $t\le6$, at least $m=8-t$ numerator terms have no such prime at odd exponent. In any two of these terms the counts of odd-exponent primes from 11 through 97 sum to at least five. Otherwise the kernel of their product appears in the finite search. With the counts arranged in increasing order and the least one equal to $s$, their sum is at least $s+(m-1)\max(s,5-s)\ge3m-1$. The primes represented in different terms are distinct. Thus $t\le6$ requires at least $23-3t$ odd-exponent primes between 11 and 97. For $t=0$ this is impossible. For each $1\le t\le6$, multiplying the smallest $23-3t$ primes in that interval and the smallest $t$ primes above 100 gives a product exceeding the displayed bound. This also proves that, throughout the finite range, columns 7 and 8 alone force the displayed squarefree part.

For $a\ge10^{346896}$, columns 5, 7 and 8 require at least thirteen distinct odd-exponent primes greater than seven. The product of the thirteen smallest such primes already exceeds the displayed bound. This overlaps the finite check, giving the claim at every height. [Three-column height bound](Erdos849HigherSquare.txt) · [Why largest column eight forces columns five and seven](Erdos849GlobalOddNineteen.md)

The same argument gives a count valid at every height for the triple. Either seven odd-exponent primes exceed 100, or at least eleven odd-exponent primes exceed seven. In the finite range the second count is at least $t+(23-3t)\ge11$ when $t\le6$. The large-height count of thirteen covers the other range.

For the pair of columns 7 and 8 alone, the all-height lower bound on the squarefree part is $1{,}448{,}810{,}778{,}701$. The finite bound above exceeds this number. At $a\ge10^{250000}$ the two columns require nine odd-exponent primes above seven, whose smallest possible product is this number. [Two-column height bound](Erdos849SquareClassRows.md)

## Replay

Run the verifier with the neighboring research scripts on the import path and assertions enabled.

```sh
python -B Erdos849HundredOdd.py
```

The run checked all 120,751 nonsquare kernels and the square kernel. The large-radicand continued fractions took 26,560,278 steps. The sieve examined 4,155,552 Pell orbits, retained 3,381,150 indices for reconstruction and reproduced 18,084 directly factored nonsquare controls. Twelve distinct rows reached exact coefficient comparison. None gave a common entry.
