import E889MultiplesTwentyThree
import E889PrimeTwentyNine

/-! Necessary conditions on any further solution of the lowercase Erdős–Selfridge problem. -/
namespace Erdos889.Multiples

/-- Every prime through 29 divides any solution above 330. -/
theorem all_primes_through_29 {n : ℕ} (big : 330<n) (sol : v_l 1 n=1) : 6469693230∣n := by
  obtain ⟨lo,_,div⟩ := further_solutions_through_prime_23 big sol
  rcases PowerPairs.large_successor big sol with pp|⟨p,pp,shape⟩
  · exact PrimeTwentyNine.primorial_twenty_nine (by omega) div pp sol
  · exact (by decide : 6469693230∣25878772920).trans
      (SquareTwentyNine.square_multiple_of_25878772920 big pp shape sol)

end Erdos889.Multiples

#print axioms Erdos889.Multiples.all_primes_through_29
