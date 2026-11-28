# Excluding the entire decade from \(10^{184}\) to \(10^{185}\)

There is no common binomial value in columns 3, 5, 7 and 8 in the closed interval

\[
  \left[10^{184},\;10^{185}\right].
\]

The result holds for every prime factorization. Run `python -B Erdos849BernsteinBand.py` beside its compressed certificate and the other research modules. The verifier reconstructs the bounds from 115 rational nodes per band and checks all 481 subintervals. [Verifier](Erdos849BernsteinBand.py) · [Certificate](Erdos849BernsteinBand.json.gz)

Put \(d=900\), \(u=1+s/d\) and \(a=A u^{840}\) for \(0\le s\le1\). The three bases \(A\) are \(10^{184},2\cdot10^{184},4\cdot10^{184}\). The verifier compares exact rational endpoints. Consecutive bands overlap because \((901/900)^{840}>2\), and the final band reaches approximately \(1.0166617508\cdot10^{185}\). The three bands use 151, 162 and 168 subintervals respectively. The positive real row \(n_k(u)>k-1\) satisfies \((n_k)_k=k!a\). Each band uses ten polynomials with integer coefficients in the variables \(n_8,n_7,n_5,n_3\).

## Interpolation with a uniform error

The verifier brackets each row at node \(s_i=r_i/B\) to precision \(1/D\), where \(B=2^{28}\) and \(D=2^{2600}\). It stores monomial samples scaled by \(S=2^{1250}\). Rounding each coordinate down and rounding the resulting scaled monomial down cost less than two units in total. The checker verifies the sufficient bound \(S(\sum e_k)M_e<D\), where \(M_e\) bounds the monomial on the complex disks of radius \(1/8\) centered on the real \(u\) interval. The holomorphic row construction and the monomial bounds are given in the [real interpolation argument](Erdos849RealInterval.md).

For \(J=115\), Cauchy's estimate and the Lagrange remainder formula bound the analytic error for monomial \(e\) by

\[
M_e\left(\frac8{dB}\right)^J
\max_i \prod_j\max\bigl(|r_i-r_j|,|r_{i+1}-r_j|\bigr).
\]

The verifier sums these bounds with the absolute polynomial coefficients. It also bounds the error from the sampled values by the maximum sample error times an upper bound on the Lebesgue constant, using the same adjacent pairs of nodes.

## Bernstein controls and subdivision

Let \(m=J-1\). For the Lagrange cardinal function of node \(r_i/B\), the \(j\)th Bernstein control is

\[
\frac{[z^j]\prod_{h\ne i}(-r_h+(B-r_h)z)}
     {\binom{m}{j}\prod_{h\ne i}(r_i-r_h)}.
\]

This follows by substituting \(s=z/(1+z)\) and multiplying by \((1+z)^m\). The verifier computes these integers exactly, multiplies by the scaled polynomial samples and floors each summand at scale \(2^{120}\). The loss per reconstructed control is at most \(J/2^{120}\). The Bernstein basis functions are nonnegative and sum to one, so this control error is also a uniform function error. Each of the ten total errors is below \(8.81\cdot10^{-35}\) before subdivision.

The certificate specifies a binary partition of \([0,1]\). At every midpoint the verifier computes the de Casteljau sums as integers and divides by the corresponding power of two, rounding only each stored child control. This adds at most \(2^{-120}\) to the uniform error per level. At a leaf, an integer combination of the ten parent polynomials has absolute value strictly below one if its largest absolute Bernstein control plus its weighted error bound is below one. Every combination accepted at that leaf must therefore vanish at an integer solution. The verifier enumerates the tuples over a small prime field having equal binomial values and checks that none makes all the required combinations vanish.

The deepest leaf has depth ten. The modular witness uses 11 on 476 leaves, 17 on four leaves and 13 on one leaf.
