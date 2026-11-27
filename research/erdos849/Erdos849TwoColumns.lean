import Erdos849Cases
import Erdos849PatternBridge

namespace Erdos849TwoColumns

open Erdos849PatternBridge

/-- If there are more rows than L, two different occupied columns are at
    least L. Truncating every column number to L proves the contrapositive. -/
theorem two_large_columns {a L : ℕ} (hL : 1 ≤ L) (hc : L < (Erdos849Cases.rows a).ncard) :
    ∃ j d : ℕ, L ≤ j ∧ j < d ∧ occurs a j ∧ occurs a d := by
  classical
  by_contra h
  let rows := Erdos849Cases.rows a
  let col (n : ℕ) := if hn : n ∈ rows then hn.choose else 0
  have spec (n : ℕ) (hn : n ∈ rows) :
      1 ≤ col n ∧ 2 * col n ≤ n ∧ n.choose (col n) = a := by
    simpa only [col, dif_pos hn] using hn.choose_spec
  let tag (n : ℕ) := min (col n) L
  have maps : Set.MapsTo tag rows (Set.Icc 1 L) := by
    intro n hn
    exact ⟨le_min (spec n hn).1 hL, min_le_right _ _⟩
  have inj : Set.InjOn tag rows := by
    intro n hn m hm he
    obtain ⟨hk,hkn,hev⟩ := spec n hn
    obtain ⟨hj,hjm,hew⟩ := spec m hm
    change min (col n) L = min (col m) L at he
    have hnocc : occurs a (col n) := ⟨n,hkn,hev⟩
    have hmocc : occurs a (col m) := ⟨m,hjm,hew⟩
    rcases lt_trichotomy (col n) (col m) with hlt | heq | hgt
    · exact False.elim (h ⟨_,_,by omega,hlt,hnocc,hmocc⟩)
    · rw [← heq] at hjm hew
      exact Erdos849FiniteBridge.same_column hk (by omega) (by omega) (hev.trans hew.symm)
    · exact False.elim (h ⟨_,_,by omega,hgt,hmocc,hnocc⟩)
  have upper := Set.ncard_le_ncard_of_injOn tag maps inj (Set.finite_Icc 1 L)
  rw [Set.ncard_Icc_nat] at upper
  change (Erdos849Cases.rows a).ncard ≤ _ at upper
  omega

end Erdos849TwoColumns
