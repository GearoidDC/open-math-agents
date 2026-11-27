import Erdos849FiniteBridge
import Mathlib.Data.Finset.Powerset

/-! The finite graph reduction for five admissible rows in Erdős problem 849.
The two lists expose the exact hypotheses supplied by the published pair
classifications and the interval computation. -/

namespace Erdos849PatternBridge

def occurs (a k : ℕ) : Prop := ∃ n : ℕ, 2*k ≤ n ∧ n.choose k = a

/-- Fixed-column pairs in Theorem 2.2 of Blokhuis, Brouwer and de Weger. -/
def classifiedPairs : List (Finset ℕ) :=
  [{2,3}, {2,4}, {2,5}, {2,6}, {2,8}, {3,4}, {3,6}, {4,6}, {4,8}]

/-- Exactly the four-column patterns avoiding the classified pairs. -/
def fourColumnPatterns : List (Finset ℕ) :=
  [{3,5,7,8}, {3,5,7,9}, {3,5,8,9}, {3,7,8,9}, {4,5,7,9},
   {5,6,7,8}, {5,6,7,9}, {5,6,8,9}, {5,7,8,9}, {6,7,8,9}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
private theorem graph_check :
    ∀ s ∈ (Finset.Icc 2 9).powerset, 4 ≤ s.card →
      ∃ t ∈ classifiedPairs ++ fourColumnPatterns, t ⊆ s := by decide

private theorem clique_check :
    ∀ i ∈ ({2,3,4,6} : Finset ℕ), ∀ j ∈ ({2,3,4,6} : Finset ℕ),
      i ≠ j → ({i,j} : Finset ℕ) ∈ classifiedPairs := by decide

/-- Nine classified pair exclusions, the exclusion of any collision between
    columns at least 7 when one is at least 10, and ten four-column exclusions suffice
    to bound the row count in the upstream statement. -/
theorem at_most_four (a : ℕ)
    (pairs : ∀ t ∈ classifiedPairs, ¬ ∀ j ∈ t, occurs a j)
    (high : ∀ j k : ℕ, 7 ≤ j → 10 ≤ k → occurs a j → occurs a k → j = k)
    (patterns : ∀ t ∈ fourColumnPatterns, ¬ ∀ j ∈ t, occurs a j) :
    {n : ℕ | ∃ k ≥ 1, 2*k ≤ n ∧ n.choose k = a}.ncard ≤ 4 := by
  classical
  by_cases hhi : ∃ k ≥ 10, occurs a k
  · obtain ⟨k, hk, hocc⟩ := hhi
    apply Erdos849FiniteBridge.at_most_four_of_column_groups a
    · intro n m i j hi hj hne hin hjm hev hew
      apply pairs {i,j} (clique_check i hi j hj hne)
      intro t ht
      rcases (show t = i ∨ t = j by simpa using ht) with rfl | rfl
      · exact ⟨n, hin, hev⟩
      · exact ⟨m, hjm, hew⟩
    · intro n m i j hi hj hne hin hjm hev hew
      have he₁ := high i k hi hk ⟨n, hin, hev⟩ hocc
      have he₂ := high j k hj hk ⟨m, hjm, hew⟩ hocc
      exact hne (he₁.trans he₂.symm)
  let s := (Finset.Icc 2 9).filter (occurs a)
  have hcard : s.card ≤ 3 := by
    by_contra! h
    have hs : s ∈ (Finset.Icc 2 9).powerset := Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    obtain ⟨t, ht, hsub⟩ := graph_check s hs h
    have hall : ∀ j ∈ t, occurs a j := fun j hj => (Finset.mem_filter.mp (hsub hj)).2
    rcases List.mem_append.mp ht with hp | hf
    · exact pairs t hp hall
    · exact patterns t hf hall
  let rows : Set ℕ := {n | ∃ k ≥ 1, 2*k ≤ n ∧ n.choose k = a}
  let col (n : ℕ) := if h : n ∈ rows then h.choose else 0
  have spec (n : ℕ) (hn : n ∈ rows) :
      1 ≤ col n ∧ 2 * col n ≤ n ∧ n.choose (col n) = a := by
    simpa only [col, dif_pos hn] using hn.choose_spec
  have maps : Set.MapsTo col rows (↑(insert 1 s) : Set ℕ) := by
    intro n hn
    obtain ⟨hk, hkn, hv⟩ := spec n hn
    have ho : occurs a (col n) := ⟨n, hkn, hv⟩
    have hsmall : col n < 10 := by by_contra! hh; exact hhi ⟨col n, hh, ho⟩
    by_cases h : col n = 1
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ho⟩))
  have inj : Set.InjOn col rows := by
    intro n hn m hm heq
    obtain ⟨hk, hkn, hev⟩ := spec n hn
    obtain ⟨_, hkm, hew⟩ := spec m hm
    rw [← heq] at hkm hew
    exact Erdos849FiniteBridge.same_column hk (by omega) (by omega) (hev.trans hew.symm)
  have hb := Set.ncard_le_ncard_of_injOn col maps inj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hb
  exact hb.trans ((Finset.card_insert_le 1 s).trans (by omega))

end Erdos849PatternBridge
