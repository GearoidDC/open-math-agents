# How many equal entries can share a Pascal translation?

Fix a positive depth \(h\) and \(0\le r\le h\). Map a source \((n,k)\) to its descendant \((n-h,k-r)\). This amounts to deleting \(r\) selected and \(h-r\) unselected items. A source is admissible for this translation if \(k\ge r\) and \(n-k\ge h-r\). The descendant is allowed to lie on either side of the triangle or on its boundary.

**At most two** positive half-row witnesses of one value \(A\) can map under this fixed translation to the same value \(B\). More precisely, suppose \(1\le k\le n/2,\ 1\le l\le m/2,\ n<m\) and

\[
\binom nk=\binom ml,\qquad \binom{n-h}{k-r}=\binom{m-h}{l-r}.
\]

Then the deletion slope satisfies the strict bounds

\[
                     \frac{l}{m+1}<\frac rh<\frac{k}{n+1}.
\]

In particular a translation removing at least as many selected as unselected items has at most one such source, since \(k/(n+1)<1/2\). At depth one neither of the two available translations can take two source rows to a common value. More generally, for any depth \(h\le l\), even choosing the two extreme translations separately for each source cannot produce a common descendant. The precise inequalities are

\[
 \binom{m-h}{l-h}<\binom{n-h}{k-h}\le\binom{n-h}{k}<\binom{m-h}{l}.
\]

The extreme inequalities have a separate Lean proof. [Erdos849PascalDescent.lean](Erdos849PascalDescent.lean)

## Proof for arbitrary translations

Define the positive rational function
\[
 F(n,k)=\binom{n-h}{k-r}/\binom nk.
\]
Equality of the source values forces \(k>l\), since increasing the row strictly increases any positive fixed column, and the coefficients are nondecreasing through the left half of a row. Join \((n,k)\) to \((m,l)\) by unit steps increasing the row or decreasing the column. Every intermediate point is admissible: the selected count stays at least \(l\ge r\), and the unselected count never decreases.

Set \(S(n,k)=hk-r(n+1)\). The following ratios follow by cancellation of factorials:

\[
\frac{F(n+1,k)}{F(n,k)}=
\frac{(n+1-h)(n+1-k)}{(n+1)(n+1-k-h+r)},\qquad
\frac{F(n,k-1)}{F(n,k)}=
\frac{(k-r)(n+1-k)}{k(n+1-k-h+r)} .
\]

The denominators are positive on every step used. In both ratios the numerator minus the denominator is exactly \(S(n,k)\). Thus both moves increase \(F\) at positive score, fix \(F\) at zero score, and decrease \(F\) at negative score. For \(r=0\) the score is positive at every step, so a tie is impossible. For \(r>0\) each move strictly decreases the score, by \(r\) or \(h\). There are at least two moves because \(n<m\) and \(k>l\). If the initial score were nonpositive, at least one move would strictly decrease \(F\) and none would increase it. If the final score were nonnegative, every move would strictly increase \(F\). Equality of the two endpoint values of \(F\) therefore requires strictly positive initial score and strictly negative final score. These are the two displayed slope bounds.

For three ordered source rows with a common image value, applying the bounds to consecutive pairs would require the middle slope to be both greater and smaller than \(r/h\). This proves the limit of two. It also allows two: deleting \(h=89\) rows and \(r=34\) columns maps the Lind pair \((103,40),(104,39)\) to \((14,6),(15,5)\), where both entries equal \(3003\). A direct check through row 250 tests 39 pairs of source witnesses and 3,507 admissible translations. This Lind example is the only common descendant pair of value greater than one in that finite test. [Exact integer check](Erdos849PascalDescent.py)

## Varying the column shift

At fixed depth \(h\), even when each source can choose its own \(r\), at most
\[
                         h+\lfloor(h-1)/2\rfloor
\]
distinct source rows of \(A\) can give the same \(B\). In particular **depths one, two, and three can yield at most one, two, and four rows**, respectively.

To count the two extreme shifts as one, consider a source taking \(r=h\) and a second source taking \(r=0\). If the later source takes \(r=h\), its column is at least \(h\), so the four nested endpoint inequalities apply. If the earlier source takes \(r=h\), its column is likewise at least \(h\). Its left endpoint is at most its right endpoint because
\[
 \binom{n-h}{k-h}=\frac{\binom nk\binom kh}{\binom nh}
 \le\frac{\binom nk\binom{n-k}h}{\binom nh}=\binom{n-h}{k}.
\]
Its right endpoint is strictly below the later right endpoint by the \(r=0\) step argument; this applies even if the later column is less than \(h\). The same-shift bounds above also exclude two sources both taking \(r=0\) or both taking \(r=h\). Thus all extreme shifts collectively contribute at most one source. Among the remaining \(h-1\) shifts, each contributes at most one except the \(\lfloor(h-1)/2\rfloor\) shifts with \(0<r<h/2\), for which the maximum is two.

For the descent hypothesis H2 of the Erdős 849 reduction, five witnessed rows therefore cannot be obtained by one common translation at any depth, or even by individually chosen column shifts at a common depth at most three. The hypothesis also permits different depths and independently found smaller coefficients, so it remains open.
