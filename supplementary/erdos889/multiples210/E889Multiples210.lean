import E889VerifiedHigher
import E889VerifiedPrime
import E889VerifiedSquare
import E889ElevenLower
import Erdos889PrimeElevenUpper
import E889Finite21

/-! Unconditional finite and divisibility restrictions on the remaining multiples of 210. -/

namespace Erdos889.Multiples
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

theorem large_multiple_2310 {n : ℕ} (big : 330<n) (sol : Erdos889.v_l 1 n=1) : 2310∣n := by
  obtain ⟨hn,_,d30⟩ := Erdos889.MissingPrimeSieve.further_solution_bounds_thirty big sol
  rcases Erdos889.PowerPairs.large_successor big sol with prime|⟨p,pp,shape⟩
  · have d210 := Erdos889.PrimeSeven.prime_multiple_of_210 (by omega) d30 prime sol
    suffices 11∣n by omega
    by_contra missing
    let j := 11-n%11
    have lt := Nat.mod_lt n (by decide : 0<11)
    have nz : n%11≠0 := fun h => missing (Nat.dvd_of_mod_eq_zero h)
    have pos : 0<j := by dsimp only [j]; omega
    have upper : j≤10 := by dsimp only [j]; omega
    have hit : 11∣n+j := by
      have step : n%11+j=11 := by dsimp only [j]; omega
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod,Nat.mod_eq_of_lt (by omega : j<11),step,Nat.mod_self]
    by_cases small : j≤5
    · exact Erdos889.PrimeElevenLower.SmallOffsets.exclude (by omega) d210 prime sol pos small hit
    · exact Erdos889.PrimeEleven.exclude_upper hn d210 prime sol (by omega) upper hit
  · exact (by decide : 2310∣9240).trans (Erdos889.SquareEleven.square_multiple_of_9240 big pp shape sol)

theorem large_solution_bounds {n : ℕ} (big : 330<n) (sol : Erdos889.v_l 1 n=1) :
    1000000000000000000000<n ∧ 2310∣n := by
  have d := large_multiple_2310 big sol
  refine ⟨?_,d⟩
  by_contra! low
  have start := (Erdos889.MissingPrimeSieve.further_solution_bounds_thirty big sol).1
  exact Erdos889.FiniteMultiple.no_multiple_through_21 ((by decide : 210∣2310).trans d) start low sol

/-- The exact list on the union of the finite interval and the complement of the multiples of 2310. -/
theorem classified {n : ℕ} (pos : 0<n) (region : n≤1000000000000000000000 ∨ ¬2310∣n) :
    Erdos889.v_l 1 n=1 ↔ n∈[1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330] := by
  by_cases low : n≤330
  · exact solutions_through_330 pos low
  constructor
  · intro sol
    obtain ⟨bound,d⟩ := large_solution_bounds (by omega) sol
    exact (region.elim (Nat.not_le_of_lt bound) (fun missing => missing d)).elim
  · intro mem
    have check : ∀ k∈([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
        48,60,70,78,80,96,120,190,222,330] : List ℕ), k≤330 := by decide
    exact (low (check n mem)).elim

theorem no_positive_multiple_of_210 {n : ℕ} (pos : 0<n) (d : 210∣n)
    (region : n≤1000000000000000000000 ∨ ¬2310∣n) : Erdos889.v_l 1 n≠1 := by
  intro sol
  have mem := (classified pos region).mp sol
  have check : ∀ k∈([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330] : List ℕ), ¬210∣k := by decide
  exact check n mem d
end Erdos889.Multiples

#print axioms Erdos889.Multiples.no_positive_multiple_of_210
