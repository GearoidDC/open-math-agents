import E889MultiplesFrontier
import E889PrimeTwentyThree
import E889SquareTwentyNine
import E889FixedInterval

/-! Restrictions on every possible exception to the conjectured maximum 330. -/

namespace Erdos889.Multiples

/-- Any further solution lies strictly between these bounds and is divisible by
the product of all primes through 23. -/
theorem further_solutions_through_prime_23 {n : ℕ} (big : 330 < n) (sol : v_l 1 n = 1) :
    10^30 < n ∧ n < 2^650917 ∧ 223092870 ∣ n := by
  obtain ⟨lower, primes⟩ := further_solutions big sol
  refine ⟨lower, FixedInterval.solution_upper_bound sol, ?_⟩
  rcases PowerPairs.large_successor big sol with hp | ⟨p, hp, hs⟩
  · exact PrimeTwentyThree.primorial_twenty_three (by omega) primes hp sol
  · exact (by decide : 223092870 ∣ 892371480).trans
      (SquareTwentyThree.square_multiple_of_892371480 big hp hs sol)

/-- Outside the remaining range and congruence class, the original 29 values
are the complete list. -/
theorem classified_outside_remaining_range {n : ℕ} (pos : 0 < n)
    (outside : ¬(10^30 < n ∧ n < 2^650917 ∧ 223092870 ∣ n)) :
    v_l 1 n = 1 ↔ n ∈ [1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330] := by
  by_cases low : n ≤ 330
  · exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.solutions_through_330 pos low
  constructor
  · intro sol
    exact (outside (further_solutions_through_prime_23 (by omega) sol)).elim
  · intro mem
    have bound : ∀ j ∈ ([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330] : List ℕ), j ≤ 330 := by decide
    exact (low (bound n mem)).elim

/-- The multiplier of 210 has five additional mandatory prime factors. -/
theorem remaining_multipliers_through_prime_23 {k : ℕ} (pos : 0 < k) (sol : v_l 1 (210*k) = 1) :
    10^30 < 210*k ∧ 210*k < 2^650917 ∧ 1062347 ∣ k := by
  have low := (remaining_multipliers pos sol).1
  obtain ⟨lo,hi,dvd⟩ := further_solutions_through_prime_23 (by omega) sol
  exact ⟨lo,hi,by omega⟩

/-- In the prime-square case the divisor contains 29 and two additional powers of two. -/
theorem further_square_solutions {n p : ℕ} (big : 330 < n) (pp : p.Prime)
    (shape : n+1=p^2) (sol : v_l 1 n = 1) :
    10^30 < n ∧ n < 2^650917 ∧ 25878772920 ∣ n :=
  ⟨(further_solutions big sol).1, FixedInterval.solution_upper_bound sol,
    SquareTwentyNine.square_multiple_of_25878772920 big pp shape sol⟩

end Erdos889.Multiples

#print axioms Erdos889.Multiples.further_solutions_through_prime_23
#print axioms Erdos889.Multiples.classified_outside_remaining_range
#print axioms Erdos889.Multiples.remaining_multipliers_through_prime_23
#print axioms Erdos889.Multiples.further_square_solutions
