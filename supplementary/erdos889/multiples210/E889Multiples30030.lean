import E889Multiples210
import E889SquareThirteen
import Erdos889PrimeThirteenFull

/-! Classification outside the remaining multiples of 30030, or through ten to the twenty-first power. -/

namespace Erdos889.Multiples
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

theorem large_solution_bounds_30030 {n : ℕ} (big : 330<n) (sol : v_l 1 n=1) :
    1000000000000000000000<n ∧ 30030∣n := by
  obtain ⟨high,d⟩ := large_solution_bounds big sol
  refine ⟨high,?_⟩
  rcases PowerPairs.large_successor big sol with prime|⟨p,pp,shape⟩
  · exact PrimeThirteen.primorial_thirteen (by omega) d prime sol
  · exact (by decide : 30030∣120120).trans (SquareThirteen.square_multiple_of_120120 big pp shape sol)

theorem classified_30030 {n : ℕ} (pos : 0<n) (region : n≤1000000000000000000000 ∨ ¬30030∣n) :
    v_l 1 n=1 ↔ n∈[1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330] := by
  by_cases low : n≤1000000000000000000000
  · exact classified pos (Or.inl low)
  constructor
  · intro sol
    exact ((region.resolve_left low) (large_solution_bounds_30030 (by omega) sol).2).elim
  · intro mem
    have cap : ∀ k∈([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
        48,60,70,78,80,96,120,190,222,330] : List ℕ), k≤330 := by decide
    have := cap n mem
    omega

/-- Every remaining solution among the positive multiples of 210 must be above the cutoff
and have multiplier divisible by 143 = 11 × 13. -/
theorem remaining_multipliers {k : ℕ} (pos : 0<k) (sol : v_l 1 (210*k)=1) :
    1000000000000000000000<210*k ∧ 143∣k := by
  have large : 330<210*k := by
    by_contra! low
    exact no_positive_multiple_of_210 (by omega) (dvd_mul_right 210 k) (Or.inl (by omega)) sol
  obtain ⟨hi,d⟩ := large_solution_bounds_30030 large sol
  exact ⟨hi,by omega⟩
end Erdos889.Multiples

#print axioms Erdos889.Multiples.classified_30030
#print axioms Erdos889.Multiples.remaining_multipliers
