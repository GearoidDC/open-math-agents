# Bounded Pell solutions for small radicands

For positive $D\le2401$, the generator enumerates all positive primitive solutions of

$$x^2-Dy^2=h^2,\qquad 1\le y<2^{2100},$$

for each requested $h$, including $1,2,3,5,7$. Applied to squarefree 100-smooth radicands and the primitive gaps $3,5,6,7$, it finds 891 distinct smooth pairs after including all multiples with gap at most seven. The pair with largest lower endpoint is $(15364343808,15364343813)$.

## Why the continued-fraction search is exhaustive

For nonsquare $D$ take the regular continued-fraction convergents $p_i/q_i$ to $\sqrt D$. Their consecutive vectors form a unimodular basis, and $|q_i\sqrt D-p_i|<1/q_{i+1}$. The latter follows from the exact tail formula: writing the remaining complete quotient as $\alpha_{i+1}>a_{i+1}$ makes the reciprocal error $q_i\alpha_{i+1}+q_{i-1}>q_{i+1}$.

Partition all positive denominators into the intervals $q_i\le y<q_{i+1}$; if the first two denominators equal one, the first interval is empty. In the corresponding basis write

$$ (x,y)=a(p_i,q_i)+b(p_{i-1},q_{i-1}). $$

The determinant formula and $x>\sqrt D\,y$ give

$$ |b|=|q_i x-p_i y|
 \le q_i\frac{h^2}{x+\sqrt D\,y} +y|q_i\sqrt D-p_i|
 < \frac{h^2}{2\sqrt D}+1. $$

The code uses the inclusive integer bound $1+\lfloor\sqrt{\lfloor h^4/(4D)\rfloor}\rfloor$. Write

$$A=p_i^2-Dq_i^2,\quad B=p_ip_{i-1}-Dq_iq_{i-1},\quad
C=p_{i-1}^2-Dq_{i-1}^2.$$

Here $A\ne0$ and $B^2-AC=D$ by unimodularity. Substituting the basis into the norm equation gives

$$ (Aa+Bb)^2=Db^2+Ah^2. $$

Thus for each permitted $b$ an integer square-root test and division by $A$ enumerate all possible $a$. Primitivity is equivalent to $\gcd(a,b)=1$. The generator keeps positive coordinates in the current denominator interval and below the strict cutoff. When the next continued-fraction digit is $c$, the new form coefficients are $(c^2A+2cB+C,cA+B,A)$, allowing identical small tests to be cached. Squares $D=d^2$ are handled directly by factoring $(x-dy)(x+dy)=h^2$. The enumeration uses no fundamental unit.

## From a solution to a pair

Let $u<v$ be coprime positive 100-smooth integers. Write $uv=Dz^2$ with $D$ squarefree. For odd $v-u=h$ in $\{3,5,7\}$ take $x=u+v$ and $y=2z$. This is a primitive solution of norm $h^2$, with $u=(x-h)/2$ and $v=(x+h)/2$. For $v-u=6$, both endpoints are odd; take $x=(u+v)/2$, $y=z$, $h=3$. Here $x$ is even and the endpoints are $x-3,x+3$. In each case $D$ is 100-smooth. Since $h$ is prime, primitivity and squarefreeness imply $h\nmid D$ and $D$ is a nonzero square modulo $h$. Indeed $h\mid D$ would force $h\mid x$ and then $h\mid y$ by the norm equation. If $h\nmid D$ a primitive solution has $h\nmid y$ and $D\equiv(x/y)^2\bmod h$.

Conversely, for supported $D$ and smooth $y$ the product $(x-h)(x+h)=Dy^2$ is smooth. The indicated parity recovers the coprime endpoints. Multiplying both by every positive integer at most $\lfloor7/(v-u)\rfloor$ accounts for all unreduced pairs of gap at most seven with those primitive gaps. Primitive gaps one, two and four use separate published enumerations.

Run **python Erdos849PellSmall.py**. The standard-library checker independently compares the generic solver against direct integer-square tests for $1\le D\le110$, $1\le y<650$ and all five requested square norms. It also checks the conversion on small directly factored pairs. To reuse the generator, import **smooth_gap_pairs** or **primitive_solutions** from this module. The bound applies to the normalized Pell denominator $y$.
