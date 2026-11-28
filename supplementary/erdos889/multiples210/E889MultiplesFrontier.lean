import E889UnboundedNineteen
import E889Finite30

/-! Further solutions must exceed ten to the thirtieth power and be divisible by
every prime through nineteen. For prime-square successors, two additional powers of two divide n. -/

namespace Erdos889.Multiples
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

theorem further_solutions {n : ℕ} (big : 330<n) (sol : v_l 1 n=1) :
    1000000000000000000000000000000<n ∧ 9699690∣n := by
  obtain ⟨lo,d⟩ := large_solution_bounds_30030 big sol
  have high : 1000000000000000000000000000000<n := by
    by_contra! upper
    exact FiniteThirty.no_multiple_through_30 ((by decide : 2310∣30030).trans d) lo upper sol
  exact ⟨high,large_multiple_9699690 big sol⟩

theorem classified_frontier {n : ℕ} (pos : 0<n) (region : n≤1000000000000000000000000000000 ∨ ¬9699690∣n) :
    v_l 1 n=1 ↔ n∈[1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330] := by
  by_cases low : n≤330
  · exact solutions_through_330 pos low
  constructor
  · intro sol
    obtain ⟨high,d⟩ := further_solutions (by omega) sol
    exact (region.elim (Nat.not_le_of_lt high) (fun miss => miss d)).elim
  · intro mem
    have bound : ∀ k∈([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
        48,60,70,78,80,96,120,190,222,330] : List ℕ), k≤330 := by decide
    exact (low (bound n mem)).elim

/-- A necessary condition on every positive multiplier of 210. -/
theorem remaining_frontier {k : ℕ} (pos : 0<k) (sol : v_l 1 (210*k)=1) :
    1000000000000000000000000000000<210*k ∧ 46189∣k := by
  have h := (remaining_multipliers pos sol).1
  obtain ⟨high,d⟩ := further_solutions (by omega) sol
  exact ⟨high,by omega⟩

end Erdos889.Multiples

#print axioms Erdos889.Multiples.classified_frontier
#print axioms Erdos889.Multiples.remaining_frontier
