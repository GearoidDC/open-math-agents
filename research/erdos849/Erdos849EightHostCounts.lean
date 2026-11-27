import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Erdos849EightHostCounts

/-- Each prime divisor is assigned to one of the eight numerator terms. -/
def count (a : ℕ) (host : ℕ → Fin 8) (i : Fin 8) : ℕ :=
  (a.primeFactors.filter fun p => host p = i).card

private theorem sum_counts (a : ℕ) (host : ℕ → Fin 8) :
    a.primeFactors.card = ∑ i, count a host i := by
  apply Finset.card_eq_sum_card_fiberwise
  simp

/-- Four distinct assigned primes per term imply 32 distinct primes overall. -/
theorem thirty_two {a : ℕ} {host : ℕ → Fin 8}
    (four : ∀ i, 4 ≤ count a host i) : 32 ≤ a.primeFactors.card := by
  rw [sum_counts a host]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 8)))
    (fun i _ => four i)
  simpa using h

/-- With at most 36 prime factors and four in every term, at least four
terms have exactly four. This is the counting step in the high-value bound. -/
theorem four_exact {a : ℕ} {host : ℕ → Fin 8} (four : ∀ i, 4 ≤ count a host i)
    (cap : a.primeFactors.card ≤ 36) :
    4 ≤ (Finset.univ.filter fun i => count a host i = 4).card := by
  have point (i : Fin 8) :
      5 ≤ count a host i + (if count a host i = 4 then 1 else 0) := by
    have := four i
    split_ifs <;> omega
  have bound := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 8)))
    (fun i _ => point i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at bound
  rw [← sum_counts a host] at bound
  omega

#print axioms thirty_two
#print axioms four_exact

end Erdos849EightHostCounts
