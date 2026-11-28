import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Set.Card

namespace Erdos849SingmasterBridge

/-- The full-triangle positions in the pinned upstream definition
`Singmaster.solutions`. The local name keeps both open conjectures out of the imports. -/
def positions (t : ℕ) : Set (ℕ × ℕ) :=
  {(n, k) | 1 ≤ k ∧ k < n ∧ Nat.choose n k = t}

/-- A row in the admissible half is the first coordinate of a full-triangle
position. Finiteness of the latter lets us compare their natural cardinalities. -/
theorem rows_ncard_le_positions (a : ℕ) (h : (positions a).Finite) :
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.ncard ≤
      (positions a).ncard := by
  have hs : {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a} ⊆
      Prod.fst '' positions a := by
    rintro n ⟨k, hk, hkn, he⟩
    exact ⟨(n, k), ⟨hk, by omega, he⟩, rfl⟩
  exact (Set.ncard_le_ncard hs (h.image _)).trans (Set.ncard_image_le h)

/-- The statement of Singmaster's conjecture implies a negative answer to
the exact question posed in Erdős 849. Both propositions are stated explicitly. -/
theorem not_erdos_849_of_singmaster
    (hb : ∃ C : ℕ, ∀ a : ℕ, a > 1 →
      (positions a).Finite ∧ (positions a).ncard ≤ C) :
    ¬ (∀ t ≥ 1, ∃ a : ℕ,
      {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.ncard = t) := by
  obtain ⟨C, hC⟩ := hb
  intro hall
  obtain ⟨a, hcount⟩ := hall (C + 1) (by omega)
  have hpos : 0 < {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.ncard := by omega
  obtain ⟨n, k, hk, hkn, he⟩ := (Set.ncard_pos (Set.finite_of_ncard_pos hpos)).mp hpos
  have hle := Nat.choose_le_choose k (show k + 1 ≤ n by omega)
  rw [Nat.choose_succ_self_right, he] at hle
  obtain ⟨hfin, hbound⟩ := hC a (by omega)
  have := (rows_ncard_le_positions a hfin).trans hbound
  omega

#print axioms not_erdos_849_of_singmaster

end Erdos849SingmasterBridge
