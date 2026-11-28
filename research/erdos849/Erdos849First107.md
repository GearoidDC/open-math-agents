# Divisibility by 107 in the first four-column pattern

Every common value of columns 3, 5, 7 and 8 in the closed interval from `10^136` to `10^185` is divisible by 107. This applies regardless of the number of prime factors of the common value.

Run `python -B Erdos849First107.py` beside the compressed certificate and `Erdos849LocalInterpolation.py`. The verifier enumerates the four row residues with a common nonzero value modulo 107, up to the symmetry of the even column. There are fourteen canonical classes above common residues 7, 10, 37, 43, 51 and 100, and six above residue 1. Each canonical class is checked both with its stated eighth-row residue and with its reflection. At common residue zero the eighth-row index belongs to one of the eight classes 0 through 7 modulo 107.

The certificate uses 48 integer polynomials across the 20 classes. All use 122 monomials, local modulus `107^122` and Chebyshev degree 65.

Let the common value be `a`, the four column lengths be `k`, and the row indices be `n_k`. The stored polynomials have integer coefficients in the four centered variables `X_k = 2 n_k − (k−1)`.

## Local divisibility

For a prime `p` exceeding all the column lengths, fix residues `r_k` with the same value `a_0` modulo `p`. The derivative of the falling factorial at each `r_k` must be invertible modulo `p`. Substitute `a=a_0+pT` into each row equation. The implicit function theorem gives a convergent integral power series in `pT` on this residue class. Composition with a stored polynomial `F` gives, modulo `p^N`, a polynomial in `T` of degree at most `N−1`. At the integers `0,…,N−1` the verifier Hensel-lifts each row and checks divisibility by `p^N`. The Newton forward differences through degree `N−1` are therefore multiples of `p^N`. Since the binomial basis is integral on every integer, the divisibility holds throughout this residue class. This step also applies when `N>p`.

## A uniform archimedean bound

Write `g` for the least common multiple of the column lengths. In a band `10^l ≤ a ≤ 10^h`, put `s=(a/10^h)^(1/g)`. The positive root satisfies

```
U_k^k = X_k^k ∏(1−r²/X_k²),   U_k=2(k!a)^(1/k),
```

where the positive integers `r` range over `k−1,k−3,…`. Thus `X_k≥U_k≥B_k=2 floor((k!10^l)^(1/k))`. The product is at least `1−Σ r²/B_k²`. Rounding `2(k!10^h)^(1/k)` downward to an integer multiple `A_k` of `2/2^100` gives

```
1 ≤ X_k/(A_k s^(g/k)) ≤ [1+2/(2^100 A_k)]/[1−Σ r²/B_k²].
```

Put `lo=floor(1000(10^(l−h))^(1/g))` and map `t∈[−1,1]` linearly onto `s∈[lo/1000,1]`. For each power `s^w`, the verifier computes its first Chebyshev coefficients by substituting `t=(z+z^−1)/2` and multiplying Laurent polynomials over the integers. Every coefficient is nonnegative, and their sum over all degrees is one. The bound for each centered monomial includes its omitted coefficients, the integer floors of retained coefficients, and the error of replacing its row variables by the displayed approximation. Summing these absolute error bounds with the absolute coefficients of `F` gives a rigorous uniform error `R`.

For a dyadic interval with midpoint `t_0` and radius `d`, let `P=Σ b_j T_j` be the scaled projected polynomial. The exact value of `F`, with the same scaling factor, lies in the closed interval of radius `R + d Σ j² |b_j|` centered at `P(t_0)`. This follows from `|T'_j|≤j²`. The checker evaluates the center exactly with integers. It accepts a dyadic interval only when one of its certified polynomials avoids every scaled multiple of `p^N`. Otherwise it divides the interval in half. The archive specifies a checked maximum depth. For each even column the involution `n_k ↦ k−1−n_k` negates its centered variable and preserves the binomial value. The verifier checks both real signs.
