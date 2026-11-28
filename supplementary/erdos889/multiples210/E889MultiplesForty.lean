import E889MultiplesTwentyNine
import E889Finite40
import E889FortyOneResidues
import E889SquareThirtySeven

/-! The exact list through ten to the fortieth power and restrictions beyond it. -/
namespace Erdos889.Multiples

theorem further_solutions_40 {n : ℕ} (big : 330<n) (sol : v_l 1 n=1) :
    10^40<n ∧ n<2^650917 ∧ 6469693230∣n ∧ n%41 ∉ [21,25,26,27,28,33,34,37,40] := by
  obtain ⟨lo,hi,_⟩ := further_solutions_through_prime_23 big sol
  have div := all_primes_through_29 big sol
  have lower : 10^40<n := by
    by_contra! cap
    exact Finite40.no_further_solution div lo cap sol
  exact ⟨lower,hi,div,FortyOne.forbidden_residues big sol⟩

/-- The 29 positive values listed by Erdős and Selfridge are all the solutions
in the stated range. -/
theorem classified_through_40 {n : ℕ} (pos : 0<n) (upper : n≤10^40) :
    v_l 1 n=1 ↔ n∈[1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330] := by
  by_cases low : n≤330
  · exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.solutions_through_330 pos low
  constructor
  · intro sol
    exact ((Nat.not_lt_of_ge upper) (further_solutions_40 (by omega) sol).1).elim
  · intro h
    have bound : ∀ j∈([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330] : List ℕ), j≤330 := by decide
    exact (low (bound n h)).elim

/-- In the entire checked interval the greatest solution is exactly 330. -/
theorem largest_solution_through_40 :
    IsGreatest {n : ℕ | 0 < n ∧ n ≤ 10^40 ∧ v_l 1 n = 1} 330 := by
  constructor
  · exact ⟨by decide, by decide,
      (classified_through_40 (n:=330) (by decide) (by decide)).mpr (by decide)⟩
  · intro n hn
    obtain ⟨_,upper,sol⟩ := hn
    by_contra! big
    exact (Nat.not_lt_of_ge upper) (further_solutions_40 big sol).1

end Erdos889.Multiples

#print axioms Erdos889.Multiples.further_solutions_40
#print axioms Erdos889.Multiples.classified_through_40
#print axioms Erdos889.Multiples.largest_solution_through_40
#print axioms Erdos889.SquareThirtySeven.prime_square_outside_29682952539240
