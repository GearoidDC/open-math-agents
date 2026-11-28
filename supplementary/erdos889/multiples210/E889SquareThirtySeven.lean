import E889SquareThirtyOne
import E889SquareThirtySevenCore

/-! The prime-square successor branch through the prime 37. -/

namespace Erdos889.SquareThirtySeven

theorem square_multiple_of_29682952539240 {n p : ℕ} (big : 330<n) (pp : p.Prime)
    (shape : n+1=p^2) (sol : v_l 1 n=1) : 29682952539240∣n :=
  force_thirty_seven big pp shape sol (SquareThirtyOne.square_multiple_of_802241960520 big pp shape sol)

theorem prime_square_outside_29682952539240 {n p : ℕ} (pp : p.Prime) (shape : n+1=p^2)
    (miss : ¬29682952539240∣n) : v_l 1 n=1 ↔ n∈[3,8,24,48,120] := by
  by_cases large : 330<n
  · constructor
    · intro sol
      exact (miss (square_multiple_of_29682952539240 large pp shape sol)).elim
    · intro mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      omega
  · apply Erdos889.SquareThirtyOne.prime_square_outside_802241960520 pp shape
    have := Nat.pow_le_pow_left pp.two_le 2
    omega
end Erdos889.SquareThirtySeven

#print axioms Erdos889.SquareThirtySeven.prime_square_outside_29682952539240
