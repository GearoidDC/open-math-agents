import Mathlib

/-! Exact small multiplicities for Erdős problem 849.
    The row set is the set appearing in the pinned Formal Conjectures statement. -/

namespace Erdos849Cases

def rows (a : ℕ) : Set ℕ :=
  {n | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}

private theorem column_mono {n i j : ℕ} (hij : i ≤ j) (hj : 2 * j ≤ n) :
    n.choose i ≤ n.choose j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- The first column contributes row a. All other candidates are checked in
    a finite rectangle with exclusive row and column cutoffs. -/
def candidates (a rowLimit colLimit : ℕ) : Finset ℕ :=
  insert a ((Finset.range rowLimit).filter fun n =>
    ∃ k ∈ Finset.range colLimit, 2 ≤ k ∧ 2 * k ≤ n ∧
      n.descFactorial k / k.factorial = a)

theorem rows_eq_candidates {a r c : ℕ} (ha : 2 ≤ a)
    (hr : a < r.choose 2) (hc : a < (2 * c).choose c) :
    rows a = (candidates a r c : Set ℕ) := by
  ext n
  simp only [rows, Set.mem_ofPred_eq, candidates, Finset.mem_coe, Finset.mem_insert,
    Finset.mem_filter, Finset.mem_range, ← Nat.choose_eq_descFactorial_div_factorial]
  constructor
  · rintro ⟨k, hk, hkn, heq⟩
    by_cases h : k = 1
    · subst k
      exact Or.inl (by simpa using heq)
    · have hk2 : 2 ≤ k := by omega
      right
      constructor
      · by_contra! hn
        have := (Nat.choose_le_choose 2 hn).trans (column_mono hk2 hkn)
        omega
      · refine ⟨k, ?_, hk2, hkn, heq⟩
        by_contra! hck
        have hnc : 2 * c ≤ n := by omega
        have := (Nat.choose_le_choose c hnc).trans (column_mono hck hkn)
        omega
  · rintro (rfl | ⟨_, k, _, hk, hkn, heq⟩)
    · exact ⟨1, by decide, by omega, by simp⟩
    · exact ⟨k, by omega, hkn, heq⟩

theorem rows_two : rows 2 = ({2} : Finset ℕ) := by
  rw [rows_eq_candidates (r := 3) (c := 2) (by decide) (by decide) (by decide)]
  exact congrArg (fun s : Finset ℕ => (s : Set ℕ)) (by decide)

theorem rows_six : rows 6 = ({4, 6} : Finset ℕ) := by
  rw [rows_eq_candidates (r := 5) (c := 3) (by decide) (by decide) (by decide)]
  exact congrArg (fun s : Finset ℕ => (s : Set ℕ)) (by decide)

theorem rows_120 : rows 120 = ({10, 16, 120} : Finset ℕ) := by
  rw [rows_eq_candidates (r := 17) (c := 5) (by decide) (by decide) (by decide)]
  exact congrArg (fun s : Finset ℕ => (s : Set ℕ)) (by decide)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem rows_3003 : rows 3003 = ({14, 15, 78, 3003} : Finset ℕ) := by
  rw [rows_eq_candidates (r := 79) (c := 7) (by decide)
    (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide)
    (by rw [Nat.choose_eq_descFactorial_div_factorial]; decide)]
  exact congrArg (fun s : Finset ℕ => (s : Set ℕ)) (by decide)

theorem first_four (t : ℕ) (h₁ : 1 ≤ t) (h₄ : t ≤ 4) :
    ∃ a : ℕ, (rows a).ncard = t := by
  interval_cases t
  · exact ⟨2, by rw [rows_two, Set.ncard_coe_finset]; decide⟩
  · exact ⟨6, by rw [rows_six, Set.ncard_coe_finset]; decide⟩
  · exact ⟨120, by rw [rows_120, Set.ncard_coe_finset]; decide⟩
  · exact ⟨3003, by rw [rows_3003, Set.ncard_coe_finset]; decide⟩

end Erdos849Cases
