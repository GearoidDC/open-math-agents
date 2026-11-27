import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Set.Nat

namespace Erdos849FiniteBridge

theorem same_column {n m k : ℕ} (hk : 1 ≤ k) (hn : k ≤ n) (hm : k ≤ m)
    (h : n.choose k = m.choose k) : n = m := by
  have strict {r s : ℕ} (hr : k ≤ r) (hrs : r < s) : r.choose k < s.choose k := by
    have hpos : 0 < r.choose (k-1) := Nat.choose_pos (by omega)
    have hstep := Nat.choose_succ_left r k hk
    have hmono := Nat.choose_le_choose k (show r+1 ≤ s by omega)
    omega
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have := strict hn hlt; omega
  · exact heq
  · have := strict hm hgt; omega

/-- The first three columns each contribute at most one row. If all remaining
    representations use the same row, the whole half-triangle has at most four. -/
theorem at_most_four (a : ℕ)
    (deep : ∀ {n m k j : ℕ}, 4 ≤ k → 2*k ≤ n → n.choose k = a →
      4 ≤ j → 2*j ≤ m → m.choose j = a → n = m) :
    {n : ℕ | ∃ k ≥ 1, 2*k ≤ n ∧ n.choose k = a}.ncard ≤ 4 := by
  classical
  let rows : Set ℕ := {n | ∃ k ≥ 1, 2*k ≤ n ∧ n.choose k = a}
  let col (n : ℕ) := if h : n ∈ rows then h.choose else 0
  have spec (n : ℕ) (hn : n ∈ rows) :
      1 ≤ col n ∧ 2 * col n ≤ n ∧ n.choose (col n) = a := by
    simpa only [col, dif_pos hn] using hn.choose_spec
  let tag (n : ℕ) := min (col n) 4
  have maps : Set.MapsTo tag rows (Set.Icc 1 4) := by
    intro n hn
    have := (spec n hn).1
    exact ⟨by dsimp [tag]; omega, min_le_right _ _⟩
  have inj : Set.InjOn tag rows := by
    intro n hn m hm htag
    obtain ⟨hkn, hhn, hen⟩ := spec n hn
    obtain ⟨hkm, hhm, hem⟩ := spec m hm
    dsimp only [tag] at htag
    by_cases hdeep : 4 ≤ col n
    · exact deep hdeep hhn hen (by omega) hhm hem
    · have heq : col n = col m := by omega
      rw [← heq] at hhm hem
      exact same_column hkn (by omega) (by omega) (hen.trans hem.symm)
  have hc := Set.ncard_le_ncard_of_injOn tag maps inj (Set.finite_Icc 1 4)
  simpa only [Set.ncard_Icc_nat] using hc

/-- To exclude five rows it suffices to exclude pair collisions within two
    groups of columns. The other two columns, 1 and 5, each give at most one
    row. The first group is covered by the published fixed-column results,
    and the second is the domain of the interval search. -/
theorem at_most_four_of_column_groups (a : ℕ)
    (small : ∀ {n m k j : ℕ}, k ∈ ({2,3,4,6} : Finset ℕ) →
      j ∈ ({2,3,4,6} : Finset ℕ) → k ≠ j → 2*k ≤ n → 2*j ≤ m →
      n.choose k = a → m.choose j = a → False)
    (large : ∀ {n m k j : ℕ}, 7 ≤ k → 7 ≤ j → k ≠ j → 2*k ≤ n → 2*j ≤ m →
      n.choose k = a → m.choose j = a → False) :
    {n : ℕ | ∃ k ≥ 1, 2*k ≤ n ∧ n.choose k = a}.ncard ≤ 4 := by
  classical
  let rows : Set ℕ := {n | ∃ k ≥ 1, 2*k ≤ n ∧ n.choose k = a}
  let col (n : ℕ) := if h : n ∈ rows then h.choose else 0
  have spec (n : ℕ) (hn : n ∈ rows) :
      1 ≤ col n ∧ 2 * col n ≤ n ∧ n.choose (col n) = a := by
    simpa only [col, dif_pos hn] using hn.choose_spec
  let tag (n : ℕ) := if col n = 1 then 0 else if col n = 5 then 1
    else if 7 ≤ col n then 2 else 3
  have maps : Set.MapsTo tag rows (Set.Iio 4) := by
    intro n _
    change tag n < 4
    simp only [tag]; split_ifs <;> decide
  have inj : Set.InjOn tag rows := by
    intro n hn m hm he
    obtain ⟨hk, hkn, hnv⟩ := spec n hn
    obtain ⟨hj, hjm, hmv⟩ := spec m hm
    by_cases heq : col n = col m
    · rw [← heq] at hjm hmv
      exact same_column hk (by omega) (by omega) (hnv.trans hmv.symm)
    · have cluster (x : ℕ) (hx : 1 ≤ x) (h1 : x ≠ 1) (h5 : x ≠ 5) (h7 : ¬ 7 ≤ x) :
            x ∈ ({2,3,4,6} : Finset ℕ) := by simp; omega
      simp only [tag] at he
      split_ifs at he <;> first
        | omega
        | exact False.elim (large (by omega) (by omega) heq hkn hjm hnv hmv)
        | exact False.elim (small (cluster _ hk (by omega) (by omega) (by omega))
            (cluster _ hj (by omega) (by omega) (by omega)) heq hkn hjm hnv hmv)
  have hc := Set.ncard_le_ncard_of_injOn tag maps inj (Set.finite_Iio 4)
  simpa only [Set.ncard_Iio_nat] using hc

end Erdos849FiniteBridge
