import Erdos849Cases
import Erdos849PatternBridge

namespace Erdos849Interval128

open Erdos849PatternBridge

/-- The proper columns outside the classified clique {2,3,4,6}. -/
def eligible (k : ℕ) : Prop := k = 5 ∨ 7 ≤ k

/-- The high search tests triples in increasing order. -/
def highExclusion (a : ℕ) : Prop :=
  ∀ i j d : ℕ, eligible i → eligible j → i < j → j < d → 10 ≤ d →
    occurs a i → occurs a j → occurs a d → False

private theorem other_unique {a d i j : ℕ} (high : highExclusion a) (hd : 10 ≤ d)
    (hi : eligible i) (hj : eligible j) (hid : i ≠ d) (hjd : j ≠ d) (hij : i ≠ j)
    (oi : occurs a i) (oj : occurs a j) (od : occurs a d) : False := by
  have ed : eligible d := Or.inr (by omega)
  rcases lt_or_gt_of_ne hij with h | h
  · by_cases h₁ : d < i
    · exact high d i j ed hi h₁ h (by omega) od oi oj
    by_cases h₂ : d < j
    · exact high i d j hi ed (by omega) h₂ (by omega) oi od oj
    · exact high i j d hi hj h (by omega) hd oi oj od
  · by_cases h₁ : d < j
    · exact high d j i ed hj h₁ h (by omega) od oj oi
    by_cases h₂ : d < i
    · exact high j d i hj ed (by omega) h₂ (by omega) oj od oi
    · exact high j i d hj hi h (by omega) hd oj oi od

private def clique : Finset ℕ := {2,3,4,6}

private def group (d k : ℕ) : ℕ :=
  if k = 1 then 0 else if k ∈ clique then 1 else if k = d then 2 else 3

/-- In the presence of an occupied column at least 10, the four groups
    are column 1, the clique, the chosen high column, and the other eligible
    columns. The last group has at most one occupied column. -/
theorem at_most_four (a : ℕ)
    (pairs : ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k)
    (low : ∀ t ∈ fourColumnPatterns, ¬∀ k ∈ t, occurs a k)
    (high : highExclusion a) : (Erdos849Cases.rows a).ncard ≤ 4 := by
  classical
  by_cases hd : ∃ d ≥ 10, occurs a d
  · obtain ⟨d, hd, od⟩ := hd
    have cl : ∀ i ∈ clique, ∀ j ∈ clique, i ≠ j → ({i,j} : Finset ℕ) ∈ classifiedPairs :=
      by decide
    have eqCol {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (he : group d i = group d j)
        (oi : occurs a i) (oj : occurs a j) : i = j := by
      by_contra h
      have rest {k : ℕ} (hk : 1 ≤ k) (hn : k ≠ 1) (hc : k ∉ clique) : eligible k := by
        simp [clique] at hc
        unfold eligible
        omega
      unfold group at he
      split_ifs at he <;> first
        | omega
        | exact other_unique high hd (rest hi (by assumption) (by assumption))
            (rest hj (by assumption) (by assumption)) (by assumption) (by assumption) h oi oj od
        | apply pairs {i,j} (cl i (by assumption) j (by assumption) h)
          intro k hk
          rcases (show k = i ∨ k = j by simpa using hk) with rfl | rfl
          · exact oi
          · exact oj
    let rows := Erdos849Cases.rows a
    let col (n : ℕ) := if hn : n ∈ rows then hn.choose else 0
    have spec (n : ℕ) (hn : n ∈ rows) :
        1 ≤ col n ∧ 2 * col n ≤ n ∧ n.choose (col n) = a := by
      simpa only [col, dif_pos hn] using hn.choose_spec
    let tag (n : ℕ) := group d (col n)
    have maps : Set.MapsTo tag rows (Set.Iio 4) := by
      intro n _
      change group d (col n) < 4
      unfold group
      split_ifs <;> decide
    have inj : Set.InjOn tag rows := by
      intro n hn m hm ht
      obtain ⟨hk, hkn, hv⟩ := spec n hn
      obtain ⟨hj, hjm, hw⟩ := spec m hm
      have h := eqCol hk hj ht ⟨n,hkn,hv⟩ ⟨m,hjm,hw⟩
      rw [← h] at hjm hw
      exact Erdos849FiniteBridge.same_column hk (by omega) (by omega) (hv.trans hw.symm)
    simpa only [Set.ncard_Iio_nat] using
      Set.ncard_le_ncard_of_injOn tag maps inj (Set.finite_Iio 4)
  · apply Erdos849PatternBridge.at_most_four a pairs _ low
    intro i d _ h _ od
    exact (hd ⟨d,h,od⟩).elim

/-- The lower endpoint can be instantiated with any previously verified base
    range. All computational and published exclusions are hypotheses. -/
theorem five_rows_above_cutoff {a lower : ℕ} (hc : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : ∀ b ≤ lower, (Erdos849Cases.rows b).ncard ≤ 4)
    (published : lower < a → ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k)
    (low : lower < a → a ≤ 10^128 → ∀ t ∈ fourColumnPatterns, ¬∀ k ∈ t, occurs a k)
    (high : lower < a → a ≤ 10^128 → highExclusion a) : 10^128 < a := by
  have ha : lower < a := by by_contra! h; have := base a h; omega
  by_contra! hb
  have := at_most_four a (published ha) (low ha hb) (high ha hb)
  omega

end Erdos849Interval128
