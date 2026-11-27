import Erdos849LargePrimePatterns

namespace Erdos849GlobalLargePrimes

open Erdos849PatternBridge Erdos849LargePrimePatterns

/-- The triples tested in the height bands for columns nine and ten. -/
def nineTenTriples : List (Finset ℕ) :=
  [{5,7,9}, {5,8,9}, {7,8,9},
   {5,7,10}, {5,8,10}, {5,9,10}, {7,8,10}, {7,9,10}, {8,9,10}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
private theorem graph_check :
    ∀ s ∈ (Finset.Icc 2 10).powerset, 4 ≤ s.card →
      (∃ t ∈ classifiedPairs, t ⊆ s) ∨
      (5 ∈ s ∧ 7 ∈ s ∧ 8 ∈ s ∧ (3 ∈ s ∨ 6 ∈ s)) ∨
      (∃ t ∈ nineTenTriples, t ⊆ s) := by decide

private theorem four_proper_columns {a : ℕ} (rows : 5 ≤ (Erdos849Cases.rows a).ncard)
    (upper : ∀ k, occurs a k → k ≤ 10) :
    ∃ s ∈ (Finset.Icc 2 10).powerset, 4 ≤ s.card ∧ ∀ k ∈ s, occurs a k := by
  classical
  let s := (Finset.Icc 2 10).filter (occurs a)
  refine ⟨s, Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_,
    fun _ hk => (Finset.mem_filter.mp hk).2⟩
  let R := Erdos849Cases.rows a
  let col (n : ℕ) := if hn : n ∈ R then hn.choose else 0
  have spec (n : ℕ) (hn : n ∈ R) : 1 ≤ col n ∧ 2*col n ≤ n ∧ n.choose (col n) = a := by
    simpa only [col, dif_pos hn] using hn.choose_spec
  have maps : Set.MapsTo col R (↑(insert 1 s) : Set ℕ) := by
    intro n hn
    obtain ⟨h1, h2, hv⟩ := spec n hn
    by_cases he : col n = 1
    · exact Finset.mem_insert.mpr (Or.inl he)
    · have ok : occurs a (col n) := ⟨n, h2, hv⟩
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, upper _ ok⟩, ok⟩))
  have inj : Set.InjOn col R := by
    intro n hn m hm he
    obtain ⟨h1, h2, hv⟩ := spec n hn
    obtain ⟨_, h3, hw⟩ := spec m hm
    rw [← he] at h3 hw
    exact Erdos849FiniteBridge.same_column h1 (by omega) (by omega) (hv.trans hw.symm)
  have hb := Set.ncard_le_ncard_of_injOn col maps inj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hb
  change (Erdos849Cases.rows a).ncard ≤ _ at hb
  have hc := Finset.card_insert_le 1 s
  omega

/-- With the finite searches, pair classifications, interpolation bounds and
single-column theorem as explicit inputs, five rows require seven primes above 100. -/
theorem seven_for_five_rows {a : ℕ} (rows : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : a ≤ 10^128 → (Erdos849Cases.rows a).ncard ≤ 4)
    (classified : 10^128 < a → ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k)
    (eightPell : 10^128 < a → a < 10^5000 → ∀ n, 16 ≤ n → n.choose 8 = a →
      2 ≤ (smoothOffsets n).card → ¬(occurs a 5 ∧ occurs a 7))
    (eightTail : 10^5000 ≤ a → pattern a → 32 ≤ a.primeFactors.card)
    (nineTenLow : 10^128 < a → a < 10^5000 → (largeFactors a).card ≤ 6 →
      ∀ t ∈ nineTenTriples, ¬∀ k ∈ t, occurs a k)
    (nineTenTail : 10^5000 ≤ a → ∀ t ∈ nineTenTriples,
      (∀ k ∈ t, occurs a k) → 32 ≤ a.primeFactors.card)
    (deep : 10^128 < a → ∀ d ≥ 11, occurs a d → 7 ≤ (largeFactors a).card) :
    7 ≤ (largeFactors a).card := by
  by_contra! h
  have ha : 10^128 < a := by by_contra! hb; have := base hb; omega
  have upper (k : ℕ) (hk : occurs a k) : k ≤ 10 := by
    by_contra! hh
    have := deep ha k (by omega) hk
    omega
  obtain ⟨s, hs, hc, occ⟩ := four_proper_columns rows upper
  rcases graph_check s hs hc with ⟨t, ht, hsub⟩ | ⟨h5, h7, h8, h36⟩ | ⟨t, ht, hsub⟩
  · exact classified ha t ht fun k hk => occ k (hsub hk)
  · have hp : pattern a := ⟨occ 5 h5, occ 7 h7, occ 8 h8, h36.imp (occ 3) (occ 6)⟩
    have := seven_for_patterns hp base eightPell eightTail
    omega
  · have allOcc : ∀ k ∈ t, occurs a k := fun k hk => occ k (hsub hk)
    by_cases high : 10^5000 ≤ a
    · have := seven_of_thirty_two (nineTenTail high t ht allOcc)
      omega
    · exact nineTenLow ha (by omega) (by omega) t ht allOcc

#print axioms seven_for_five_rows

end Erdos849GlobalLargePrimes
