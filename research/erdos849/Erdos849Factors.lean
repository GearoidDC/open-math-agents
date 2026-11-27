import Erdos849Bound
import Erdos849Finite
import Mathlib.Data.Nat.Choose.Factorization

/-! Prime-power constraints on values repeated in Pascal's triangle. -/

namespace Erdos849Factors

private theorem half_mono {i k n : ℕ} (hi : i ≤ k) (hk : 2*k ≤ n) :
    n.choose i ≤ n.choose k := by
  induction k, hi using Nat.le_induction with
  | base => exact le_rfl
  | succ k _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Every prime power dividing a represented value bounds its row from below. -/
theorem prime_power_le_row {p e n k : ℕ} (hp : p.Prime) (hn : 0 < n) (hk : k ≤ n)
    (hd : p^e ∣ n.choose k) : p^e ≤ n :=
  (Nat.pow_le_pow_right hp.pos
    ((hp.pow_dvd_iff_le_factorization (Nat.choose_pos hk).ne').1 hd)).trans
    (Nat.pow_factorization_choose_le hn)

/-- The lower bound on a witness applies to entire prime powers in it. -/
theorem prime_power_choose_le {a t p e : ℕ} (ht : 1 ≤ t) (hp : p.Prime) (hd : p^e ∣ a)
    (hc : (Erdos849Cases.rows a).ncard = t) : (p^e).choose t ≤ a := by
  obtain ⟨n,k,htk,hkn,hv⟩ := Erdos849Bound.exists_large_column_of_row_count ht hc
  rw [← hv] at hd ⊢
  exact (Nat.choose_le_choose t (prime_power_le_row hp (by omega) (by omega) hd)).trans
    (half_mono htk hkn)

/-- Each of the distinct primes contributes at most one row-sized prime power. -/
theorem value_le_row_pow_prime_factors {a n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (hv : n.choose k = a) : a ≤ n^a.primeFactors.card := by
  have ha : a ≠ 0 := hv ▸ (Nat.choose_pos hk).ne'
  calc
    a = ∏ p ∈ a.primeFactors, p ^ a.factorization p := Nat.prod_primeFactors_pow_factorization ha
    _ ≤ _ := Finset.prod_le_pow_card _ _ _ fun p _ => hv ▸ Nat.pow_factorization_choose_le hn

/-- A single deep representation bounds a value with few prime factors. -/
theorem small_of_deep_representation {a t n k : ℕ} (ht : 1 ≤ t)
    (htk : t ≤ k) (hkn : 2*k ≤ n) (hv : n.choose k = a) (hf : a.primeFactors.card < t) :
    a ≤ (2^t * t.factorial)^(t-1) := by
  have hn : 0 < n := by omega
  have ha : a ≤ n^(t-1) := (value_le_row_pow_prime_factors hn (by omega) hv).trans
    (Nat.pow_le_pow_right hn (by omega))
  have hdesc := n.pow_sub_le_descFactorial t
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hbin : n.choose t ≤ a := hv ▸ half_mono htk hkn
  have hp : n^t ≤ (2^t * t.factorial) * n^(t-1) := calc
    n^t ≤ (2*(n+1-t))^t := Nat.pow_le_pow_left (by omega) t
    _ = 2^t * (n+1-t)^t := mul_pow _ _ _
    _ ≤ 2^t * (t.factorial * n^(t-1)) := Nat.mul_le_mul_left _ (hdesc.trans
      (Nat.mul_le_mul_left _ (hbin.trans ha)))
    _ = _ := (mul_assoc _ _ _).symm
  have hn' : n ≤ 2^t * t.factorial := by
    have he : n^t = n * n^(t-1) := by
      conv_lhs => rw [show t = (t-1)+1 by omega, pow_succ, mul_comm]
    rw [he] at hp
    exact Nat.le_of_mul_le_mul_right hp (pow_pos hn _)
  exact ha.trans (Nat.pow_le_pow_left hn' _)

/-- A value with fewer distinct prime factors than its multiplicity lies in
an explicit finite range. -/
theorem small_of_fewer_prime_factors {a t : ℕ} (ht : 1 ≤ t)
    (hc : t ≤ (Erdos849Cases.rows a).ncard) (hf : a.primeFactors.card < t) :
    a ≤ (2^t * t.factorial)^(t-1) := by
  obtain ⟨n,k,hMk,hkn,hv⟩ := Erdos849Bound.exists_large_column_of_row_count (ht.trans hc) rfl
  exact small_of_deep_representation ht (hc.trans hMk) hkn hv hf

private theorem choose_five_gt_fourth {n : ℕ} (hn : 1000 ≤ n) : n^4 < n.choose 5 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h := (1000+q).pow_sub_le_descFactorial 5
  rw [Nat.descFactorial_eq_factorial_mul_choose, show 1000+q+1-5 = 996+q by omega] at h
  norm_num [Nat.factorial] at h
  nlinarith [Nat.zero_le (q^2), Nat.zero_le (q^3), Nat.zero_le (q^4), Nat.zero_le (q^5)]

/-- Every possible witness to five or more distinct rows must have at least
five distinct prime factors, with no upper bound imposed on its size. -/
theorem five_distinct_prime_factors {a : ℕ} (hcount : 5 ≤ (Erdos849Cases.rows a).ncard) :
    5 ≤ a.primeFactors.card := by
  by_contra! hf
  obtain ⟨n,k,htk,hkn,hv⟩ := Erdos849Bound.exists_large_column_of_row_count
    (by omega : 1 ≤ (Erdos849Cases.rows a).ncard) rfl
  have hk : 5 ≤ k := by omega
  have ha : a ≤ n^4 := (value_le_row_pow_prime_factors (by omega) (by omega) hv).trans
    (Nat.pow_le_pow_right (by omega) (by omega))
  have hlarge : 10^12 < a := by
    by_contra! h
    have := Erdos849Finite.at_most_four_through_trillion a h
    omega
  have hn : 1000 ≤ n := by
    by_contra! h
    have := Nat.pow_le_pow_left (show n ≤ 1000 by omega) 4
    omega
  have hbin : n.choose 5 ≤ a := hv ▸ half_mono hk hkn
  exact (choose_five_gt_fourth hn).not_ge (hbin.trans ha)

/-- The fixed-column clique rules out five rows confined to columns 1 through 7. -/
theorem exists_column_eight_or_larger {a : ℕ} (hc : 5 ≤ (Erdos849Cases.rows a).ncard)
    (small : ∀ {n m k j : ℕ}, k ∈ ({2,3,4,6} : Finset ℕ) →
      j ∈ ({2,3,4,6} : Finset ℕ) → k ≠ j → 2*k ≤ n → 2*j ≤ m →
      n.choose k = a → m.choose j = a → False) :
    ∃ n k : ℕ, 8 ≤ k ∧ 2*k ≤ n ∧ n.choose k = a := by
  by_contra! h
  have upper := Erdos849FiniteBridge.at_most_four_of_column_groups a small (by
    intro n m k j hk hj hd hkn hjm hnv hmv
    by_cases h8 : 8 ≤ k
    · exact h n k h8 hkn hnv
    · exact h m j (by omega) hjm hmv)
  change (Erdos849Cases.rows a).ncard ≤ 4 at upper
  omega

/-- Conditional on the fixed-column exclusions at the candidate, a value above
10^60 with five rows needs eight distinct prime factors. -/
theorem eight_factors_of_clique {a : ℕ} (ha : 10^60 < a) (hc : 5 ≤ (Erdos849Cases.rows a).ncard)
    (small : ∀ {n m k j : ℕ}, k ∈ ({2,3,4,6} : Finset ℕ) →
      j ∈ ({2,3,4,6} : Finset ℕ) → k ≠ j → 2*k ≤ n → 2*j ≤ m →
      n.choose k = a → m.choose j = a → False) : 8 ≤ a.primeFactors.card := by
  by_contra! hf
  obtain ⟨n,k,hk,hn,hv⟩ := exists_column_eight_or_larger hc small
  have hb := small_of_deep_representation (by decide : 1 ≤ 8) hk hn hv hf
  have hlim : (2^8 * Nat.factorial 8)^(8-1) < 10^60 := by decide
  omega

/-- With at most eight prime factors, no value above 10^60 can occur in any
admissible column from nine onwards. This implication has no external hypotheses. -/
theorem column_lt_nine_of_eight_factors {a n k : ℕ} (ha : 10^60 < a)
    (hf : a.primeFactors.card ≤ 8) (hkn : 2*k ≤ n) (hv : n.choose k = a) : k < 9 := by
  by_contra! hk
  have hn : 0 < n := by omega
  have hvalue : a ≤ n^8 := (value_le_row_pow_prime_factors hn (by omega) hv).trans
    (Nat.pow_le_pow_right hn hf)
  have hnlarge : 10^7 < n := by
    by_contra! h
    have := Nat.pow_le_pow_left h 8
    omega
  have hdesc := n.pow_sub_le_descFactorial 9
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hbin : n.choose 9 ≤ a := hv ▸ half_mono hk hkn
  have hh : (3^9*n)*n^8 ≤ (4^9*Nat.factorial 9)*n^8 := calc
    _ = (3*n)^9 := by ring
    _ ≤ (4*(n+1-9))^9 := Nat.pow_le_pow_left (by omega) _
    _ = 4^9 * (n+1-9)^9 := mul_pow _ _ _
    _ ≤ 4^9*(Nat.factorial 9*n^8) := Nat.mul_le_mul_left _ (hdesc.trans
      (Nat.mul_le_mul_left _ (hbin.trans hvalue)))
    _ = _ := (mul_assoc _ _ _).symm
  have hh' := Nat.le_of_mul_le_mul_right hh (pow_pos hn _)
  norm_num [Nat.factorial] at hh'
  omega

end Erdos849Factors
