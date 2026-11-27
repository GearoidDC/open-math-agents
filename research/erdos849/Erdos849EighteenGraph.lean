import Erdos849Factors
import Erdos849PatternBridge

namespace Erdos849EighteenGraph

open Erdos849PatternBridge

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) : n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Above the finite base, seventeen full prime powers cannot supply a column ≥20. -/
theorem column_bound {a n k : ℕ} (ha : 10^128 < a) (hf : a.primeFactors.card ≤ 17)
    (hkn : 2*k ≤ n) (hv : n.choose k = a) : k ≤ 19 := by
  by_contra! hk
  have hn : 0 < n := by omega
  have hval := (Erdos849Factors.value_le_row_pow_prime_factors hn (by omega : k ≤ n) hv).trans
    (Nat.pow_le_pow_right hn hf)
  have hN : 10^7 ≤ n := by
    by_contra! h
    have hlim := Nat.pow_le_pow_left h.le 17
    have : ((10:ℕ)^7)^17 < 10^128 := by decide
    omega
  have hchoose := ((half_mono (show 20 ≤ k by omega) hkn).trans hv.le).trans hval
  have hdesc := n.pow_sub_le_descFactorial 20
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hp : (4^20*n^3)*n^17 ≤ (5^20*Nat.factorial 20)*n^17 := calc
    _ = (4*n)^20 := by ring
    _ ≤ (5*(n+1-20))^20 := Nat.pow_le_pow_left (by omega) _
    _ = 5^20 * (n+1-20)^20 := mul_pow _ _ _
    _ ≤ 5^20 * (Nat.factorial 20 * n^17) := Nat.mul_le_mul_left _ (hdesc.trans
      (Nat.mul_le_mul_left _ hchoose))
    _ = _ := (mul_assoc _ _ _).symm
  have h := Nat.le_of_mul_le_mul_right hp (pow_pos hn _)
  have hh := (Nat.mul_le_mul_left (4^20) (Nat.pow_le_pow_left hN 3)).trans h
  exact (by decide : ¬ (4^20*((10:ℕ)^7)^3 ≤ 5^20*Nat.factorial 20)) hh

/-- Inputs supplied by the local interpolation and the accompanying integer checks. -/
structure Exclusions (a : ℕ) : Prop where
  sevenEight : ¬ (occurs a 7 ∧ occurs a 8)
  middle : ∀ k, 9 ≤ k → k ≤ 14 → ¬ occurs a k
  upper : ∀ j d, 7 ≤ j → j < d → 15 ≤ d → d ≤ 19 →
    ¬ (occurs a j ∧ occurs a d)

/-- The published classifications, finite base and external computations are explicit hypotheses. -/
theorem eighteen_distinct_prime_factors {a : ℕ} (rows : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : a ≤ 10^128 → (Erdos849Cases.rows a).ncard ≤ 4)
    (classified : 10^128 < a → ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k)
    (computed : 10^128 < a → a.primeFactors.card ≤ 17 → Exclusions a) :
    18 ≤ a.primeFactors.card := by
  by_contra! h
  have hf : a.primeFactors.card ≤ 17 := by omega
  have ha : 10^128 < a := by by_contra! hle; have := base hle; omega
  have ex := computed ha hf
  have incompatible {j d : ℕ} (h7 : 7 ≤ j) (hlt : j < d)
      (oj : occurs a j) (od : occurs a d) : False := by
    obtain ⟨n, hkn, hv⟩ := od
    have hd := column_bound ha hf hkn hv
    by_cases hu : 15 ≤ d
    · exact ex.upper j d h7 hlt hu hd ⟨oj,n,hkn,hv⟩
    by_cases hm : 9 ≤ d
    · exact ex.middle d hm (by omega) ⟨n,hkn,hv⟩
    have : j = 7 := by omega
    have : d = 8 := by omega
    subst j; subst d
    exact ex.sevenEight ⟨oj,n,hkn,hv⟩
  have bound : (Erdos849Cases.rows a).ncard ≤ 4 := by
    apply Erdos849FiniteBridge.at_most_four_of_column_groups
    · intro n m k j hk hj hn hnk hmj hnv hmv
      have all : ∀ i ∈ ({2,3,4,6} : Finset ℕ), ∀ l ∈ ({2,3,4,6} : Finset ℕ),
          i ≠ l → ({i,l} : Finset ℕ) ∈ classifiedPairs := by decide
      apply classified ha {k,j} (all k hk j hj hn)
      intro i hi
      rcases (show i = k ∨ i = j by simpa using hi) with rfl | rfl
      · exact ⟨n,hnk,hnv⟩
      · exact ⟨m,hmj,hmv⟩
    · intro n m k j hk hj hn hnk hmj hnv hmv
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact incompatible hk hlt ⟨n,hnk,hnv⟩ ⟨m,hmj,hmv⟩
      · exact incompatible hj hgt ⟨m,hmj,hmv⟩ ⟨n,hnk,hnv⟩
  omega

end Erdos849EighteenGraph
