import Erdos849Factors
import Erdos849HostCofactors

/-! Numerical thresholds for cutting off columns and occupying every
numerator offset of a binomial representation. -/

namespace Erdos849Threshold

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) : n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Given X ≥ N^w, an integer scale S certifies that C(n,w+1)>n^w for
    n>N. A value above X with at most w prime factors therefore occurs in no
    admissible column beyond w. -/
theorem column_bound_of_scale {a n d w X N S : ℕ} (ha : X<a)
    (hf : a.primeFactors.card ≤ w) (hh : 2*d≤n) (he : n.choose d=a)
    (hS : 0<S) (hX : N^w≤X) (hN : (S+1)*w≤N)
    (hfact : (S+1)^(w+1)*(w+1).factorial ≤ N*S^(w+1)) : d≤w := by
  by_contra! hdeep
  have hnpos : 0<n := by omega
  have hva : a ≤ n^w := (Erdos849Factors.value_le_row_pow_prime_factors hnpos
    (by omega) he).trans (Nat.pow_le_pow_right hnpos hf)
  have hn : N<n := by
    by_contra! h
    exact ha.not_ge (hva.trans ((Nat.pow_le_pow_left h w).trans hX))
  have hmono : n.choose (w+1) ≤ n^w := ((half_mono hdeep hh).trans he.le).trans hva
  have hdesc := n.pow_sub_le_descFactorial (w+1)
  rw [Nat.descFactorial_eq_factorial_mul_choose, show n+1-(w+1)=n-w by omega] at hdesc
  have hscale : S*n ≤ (S+1)*(n-w) := by rw [Nat.mul_sub, Nat.succ_mul]; omega
  have hpow : (n*S^(w+1))*n^w ≤ ((S+1)^(w+1)*(w+1).factorial)*n^w := calc
    _ = (S*n)^(w+1) := by rw [mul_pow, pow_succ n]; ring
    _ ≤ ((S+1)*(n-w))^(w+1) := Nat.pow_le_pow_left hscale _
    _ = (S+1)^(w+1)*(n-w)^(w+1) := mul_pow _ _ _
    _ ≤ (S+1)^(w+1)*((w+1).factorial*n^w) :=
      Nat.mul_le_mul_left _ (hdesc.trans (Nat.mul_le_mul_left _ hmono))
    _ = _ := (mul_assoc _ _ _).symm
  have hupper := (Nat.le_of_mul_le_mul_right hpow (pow_pos hnpos w)).trans hfact
  exact hn.not_ge (Nat.le_of_mul_le_mul_right hupper (pow_pos hS _))

/-- A numerical threshold ensuring every numerator slot hosts a complete
    prime power, for any d and X. -/
theorem factorial_lt_first {n d X N : ℕ} (ha : X<n.choose d) (hpower : N^d≤X)
    (hN : d.factorial+d≤N+1) : d.factorial < n+1-d := by
  have hn : N<n := by
    by_contra! h
    exact ha.not_ge ((Nat.choose_le_pow n d).trans ((Nat.pow_le_pow_left h d).trans hpower))
  omega

/-- Above a googol the column index is at most eleven if at most eleven
    distinct primes divide the value. -/
theorem column_le_eleven {a n d : ℕ} (ha : 10^100<a) (hf : a.primeFactors.card≤11)
    (hh : 2*d≤n) (he : n.choose d=a) : d≤11 :=
  column_bound_of_scale (N := 10^9) (S := 100) ha hf hh he
    (by decide) (by decide) (by decide) (by decide)

theorem first_above_factorial {n d : ℕ} (ha : 10^100<n.choose d) (hd : d≤11) :
    d.factorial < n+1-d := by
  apply factorial_lt_first (N := 10^8) ha
  · exact (Nat.pow_le_pow_right (by decide) hd).trans (by decide)
  · have hl := Nat.factorial_le hd
    have hv : Nat.factorial 11 = 39916800 := by decide
    omega

theorem all_offsets_occupied {n d : ℕ} (ha : 10^100<n.choose d) (hd₁ : 1≤d)
    (hd₂ : d≤11) (hn : d≤n) (s : ℕ) (hs : s<d) :
    (Erdos849HostCofactors.assigned n d s).Nonempty := by
  have h := first_above_factorial ha hd₂
  exact Erdos849HostCofactors.occupied hd₁ hn hs (by omega)

end Erdos849Threshold
