import Erdos849Cases
import Erdos849FiniteBridge
import Erdos849FiniteData

/-! A kernel-checked finite exclusion for Erdős 849 through one trillion. -/

namespace Erdos849Finite

private def limit : ℕ := 10^12

/-- Exclusive row limits for columns 4 through 21. -/
private def rowLimit (k : ℕ) : ℕ :=
  (#[2215,657,302,179,123,94,77,66,59,54,51,48,47,45,44,44,44,43] : Array ℕ)[k-4]!

private def checkColumn (k : ℕ) : Bool :=
  decide (limit < Nat.fast_choose (rowLimit k) k) &&
    (List.range' (2*k) (rowLimit k - 2*k)).all fun n =>
      let a := Nat.fast_choose n k
      a == 3003 || Erdos849FiniteData.column a == k

set_option maxRecDepth 32768 in
set_option maxHeartbeats 10000000 in
private theorem all_columns_checked : (List.range' 4 18).all checkColumn = true := by
  decide +kernel

/-- Number of admissible positions visited by the finite classification. -/
theorem checked_position_count :
    ((List.range' 4 18).map fun k => rowLimit k - 2*k).sum = 3742 := by decide

private theorem deep_column {a n k : ℕ} (ha : a ≤ 10^12) (hex : a ≠ 3003)
    (hk : 4 ≤ k) (hkn : 2*k ≤ n) (hv : n.choose k = a) :
    Erdos849FiniteData.column a = k := by
  have h22 : 10^12 < Nat.centralBinom 22 := by
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.choose_eq_fast_choose]
    decide
  have hcent : Nat.centralBinom k ≤ a := hv ▸ Nat.choose_le_choose k hkn
  have hk22 : k < 22 := by
    by_contra! h
    have := Nat.centralBinom_strictMono.monotone h
    omega
  have hmem : k ∈ List.range' 4 18 := List.mem_range'.mpr ⟨k-4, by omega, by omega⟩
  have hc := List.all_eq_true.mp all_columns_checked k hmem
  simp only [checkColumn, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hcap, hrows⟩ := hc
  have hnlim : n < rowLimit k := by
    by_contra! h
    have hm := Nat.choose_le_choose k h
    rw [← Nat.choose_eq_fast_choose] at hcap
    change 10^12 < _ at hcap
    omega
  have hmemn : n ∈ List.range' (2*k) (rowLimit k - 2*k) :=
    List.mem_range'.mpr ⟨n-2*k, by omega, by omega⟩
  have hp := List.all_eq_true.mp hrows n hmemn
  simpa [← Nat.choose_eq_fast_choose, hv, hex] using hp

/-- Each value through one trillion appears in at most four admissible rows. -/
theorem at_most_four_through_trillion (a : ℕ) (ha : a ≤ 10^12) :
    (Erdos849Cases.rows a).ncard ≤ 4 := by
  by_cases h3003 : a = 3003
  · subst a
    rw [Erdos849Cases.rows_3003, Set.ncard_coe_finset]
    decide
  apply Erdos849FiniteBridge.at_most_four
  intro n m k j hk hn hv hj hm hv'
  have he := (deep_column ha h3003 hk hn hv).symm.trans (deep_column ha h3003 hj hm hv')
  subst j
  exact Erdos849FiniteBridge.same_column (by omega) (by omega) (by omega) (hv.trans hv'.symm)

/-- A witness to the first unresolved multiplicity would have to exceed one trillion. -/
theorem trillion_lt_of_five_rows {a : ℕ} (h : (Erdos849Cases.rows a).ncard = 5) :
    10^12 < a := by
  by_contra! hle
  have := at_most_four_through_trillion a hle
  omega

end Erdos849Finite
