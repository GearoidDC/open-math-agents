# A five-row value needs nineteen distinct primes

If an integer $a$ occurs in at least five distinct rows of the left half of Pascal's triangle, then **at least 19 distinct primes divide $a$**. At least five of those primes exceed 100. Whether such an integer exists remains open. Here a row $n$ represents $a$ when $\binom nk=a$ for some $1\le k\le n/2$. [Large prime divisors](Erdos849SmoothNeighbors.md)

## Why eighteen primes cannot suffice

The earlier finite search gives $a>10^{128}$. Each column occurs in at most one row. Column 1 gives the edge, so five rows require at least four distinct proper columns. The published small-column classifications allow at most one of the columns 2, 3, 4 and 6. Consequently the two largest chosen proper columns satisfy $7\le j<d$. [Finite range and its verification](Erdos849Focused128.md) · [Blokhuis, Brouwer and de Weger, Theorem 2.2](https://arxiv.org/abs/1707.06893)

* **Largest column at most 17.** Assign each prime power in $a$ to the numerator term where its base has maximal valuation. Dividing each term by its assigned powers leaves a cofactor dividing $\operatorname{lcm}(1,\ldots,k)$ in column $k$. All these cofactors multiply to $k!$. Integer interpolation certificates bound the individual powers. Testing every distribution of eighteen powers rules out 54 of the 55 possible pairs $(j,d)$. For the remaining pair $(9,17)$, every smaller proper column must lie in $\{2,3,4,6\}$, so at most one can join the two larger columns. [Cofactor argument and certificate](Erdos849NineteenLow.txt)
* **Largest column 18, 19 or 20.** An empty numerator term divides $d!$, and exact column inversion excludes the finitely many rows this allows. More than eighteen terms force an empty term. If all eighteen terms are occupied, each holds one prime power. Grouping these powers on the other row gives a finite family of linear and quadratic substitutions. Exact arithmetic excludes all 5,778 that need an integer root search. [Large-column argument and checks](Erdos849EighteenHosts.md)
* **Largest column at least 21.** Every full prime power in $a$ is at most the row $n$. The binomial bound $\binom n{21}\le a$ forces $n^{18}<a$ at the stated height. Eighteen prime powers therefore cannot multiply to $a$. [Lean proof of the cutoff](Erdos849NineteenGraph.lean)

The Lean theorem checks the row count and the deep-column inequality. It takes the earlier finite range, published classifications and the new finite exclusions as explicit hypotheses. The arithmetic certificates run outside the Lean kernel. For values at least $10^{310}$, a further count of factors shared between numerator terms raises the minimum to 20 primes. Any value at least $10^{128}$ shared by columns 7 and 8 already requires 24. [Lean theorem and hypotheses](Erdos849NineteenGraph.lean) · [Twenty-prime proof](Erdos849TwentyLarge.txt) · [Columns 7 and 8](Erdos849PairPowerSlots.txt)

## Reproduction

Run the following commands with Python assertions enabled. The first two programs check the additional exclusions for the nineteen-prime bound, using the existing interpolation constants. The third checks the independent claim about primes above 100. Each proof note gives the source and status of its inputs.

```sh
python Erdos849NineteenLow.py
python Erdos849EighteenHosts.py
python Erdos849SmoothNeighbors.py
```
