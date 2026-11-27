import Erdos849Factors
import Erdos849PatternBridge

namespace Erdos849BoundedOmega

open Erdos849PatternBridge

private theorem proper_pair {a : ℕ} (hc : 3 ≤ (Erdos849Cases.rows a).ncard) :
    ∃ j d : ℕ, 2 ≤ j ∧ j < d ∧ occurs a j ∧ occurs a d := by
  classical
  obtain ⟨n,k,hk,hn,he⟩ := Erdos849Bound.exists_large_column_of_row_count
    (by omega : 1 ≤ (Erdos849Cases.rows a).ncard) rfl
  have hok : occurs a k := ⟨n,hn,he⟩
  by_contra h
  have hsub : Erdos849Cases.rows a ⊆ (↑({a,n} : Finset ℕ) : Set ℕ) := by
    rintro m ⟨j,hj,hm,hv⟩
    by_cases h1 : j = 1
    · subst j
      have : m = a := by simpa using hv
      simp [this]
    have hoj : occurs a j := ⟨m,hm,hv⟩
    rcases lt_trichotomy j k with hlt | rfl | hgt
    · exact False.elim (h ⟨j,k,by omega,hlt,hoj,hok⟩)
    · have heq := Erdos849FiniteBridge.same_column hj (by omega) (by omega) (hv.trans he.symm)
      simp [heq]
    · exact False.elim (h ⟨k,j,by omega,hgt,hok,hoj⟩)
  have hcard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hcard
  have htwo : ({a,n} : Finset ℕ).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  omega

/-- Siegel's theorem on the fixed-column curves supplies the individual
    finiteness hypotheses. All other steps of the deduction are formalized. -/
theorem finite_three_rows_with_bounded_omega
    (fixed : ∀ j d : ℕ, 2 ≤ j → j < d → {a : ℕ | occurs a j ∧ occurs a d}.Finite)
    (r : ℕ) : {a : ℕ | a.primeFactors.card ≤ r ∧ 3 ≤ (Erdos849Cases.rows a).ncard}.Finite := by
  classical
  let lim := (2^(r+1) * (r+1).factorial)^r
  let pieces (j d : ℕ) : Set ℕ :=
    if 2 ≤ j ∧ j < d then {a | occurs a j ∧ occurs a d} else ∅
  have hp (j d : ℕ) : (pieces j d).Finite := by
    by_cases h : 2 ≤ j ∧ j < d
    · simpa [pieces,h] using fixed j d h.1 h.2
    · simp [pieces,h]
  have hu : (⋃ j ∈ Set.Iic r, ⋃ d ∈ Set.Iic r, pieces j d).Finite :=
    (Set.finite_Iic r).biUnion fun j _ => (Set.finite_Iic r).biUnion fun d _ => hp j d
  apply ((Set.finite_Iic lim).union hu).subset
  rintro a ⟨hf,hc⟩
  by_cases small : a ≤ lim
  · exact Or.inl small
  right
  obtain ⟨j,d,hj,hjd,hoj,hod⟩ := proper_pair hc
  have hdr : d ≤ r := by
    by_contra! h
    obtain ⟨n,hn,hv⟩ := hod
    have hlim := Erdos849Factors.small_of_deep_representation (by omega : 1 ≤ r+1)
      (by omega : r+1 ≤ d) hn hv (by omega)
    exact small (by simpa [lim] using hlim)
  apply Set.mem_iUnion₂.mpr ⟨j,by exact (show j ≤ r by omega),?_⟩
  apply Set.mem_iUnion₂.mpr ⟨d,hdr,?_⟩
  simpa [pieces,hj,hjd] using (show occurs a j ∧ occurs a d from ⟨hoj,hod⟩)

end Erdos849BoundedOmega
