import E889Multiples30030
import E889SquareNineteen
import Erdos889PrimeSeventeenFull
import Erdos889PrimeNineteenFull

/-! Every exception above 330 is divisible by every prime through nineteen. -/

namespace Erdos889.Multiples

theorem large_multiple_9699690 {n : ℕ} (big : 330<n) (sol : v_l 1 n=1) : 9699690∣n := by
  obtain ⟨lo,d⟩ := large_solution_bounds_30030 big sol
  rcases PowerPairs.large_successor big sol with prime|⟨p,pp,shape⟩
  · have d17 := PrimeSeventeen.primorial_seventeen (by omega) d prime sol
    exact PrimeNineteen.primorial_nineteen (by omega) d17 prime sol
  · exact (by decide : 9699690∣38798760).trans (SquareNineteen.square_multiple_of_38798760 big pp shape sol)

end Erdos889.Multiples

#print axioms Erdos889.Multiples.large_multiple_9699690
