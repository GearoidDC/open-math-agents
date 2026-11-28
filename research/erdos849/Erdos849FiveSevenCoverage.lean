import Erdos849PairCoverage

namespace Erdos849FiveSevenCoverage

open Erdos849PatternBridge Erdos849LargePrimePatterns

abbrev Maximizing := Erdos849PairCoverage.Maximizing

abbrev Occupied (a : ℕ) (f : ℕ → Fin 5) (g : ℕ → Fin 7) : Prop :=
  Erdos849PairCoverage.Occupied a f g

abbrev CoverageAboveCutoff (a : ℕ) := Erdos849PairCoverage.CoverageAbove a 5 7 136

/-- Counting works for any two assignment maps that occupy all 35 cells. -/
theorem counts_of_occupied {a : ℕ} {f : ℕ → Fin 5} {g : ℕ → Fin 7}
    (hit : Occupied a f g) :
    35 ≤ a.primeFactors.card ∧
    (∀ i, 7 ≤ (a.primeFactors.filter fun p => f p = i).card) ∧
    (∀ j, 5 ≤ (a.primeFactors.filter fun p => g p = j).card) :=
  Erdos849PairCoverage.counts_of_occupied hit

/-- Each actual numerator term inherits the count of primes assigned to it. -/
theorem counts_for_pair {a n m : ℕ} (cert : CoverageAboveCutoff a) (high : 10^136 ≤ a)
    (hn : 10 ≤ n) (hm : 14 ≤ m) (h5 : n.choose 5 = a) (h7 : m.choose 7 = a) :
    35 ≤ a.primeFactors.card ∧ (∀ i : Fin 5, 7 ≤ (n-i.val).primeFactors.card) ∧
    (∀ j : Fin 7, 5 ≤ (m-j.val).primeFactors.card) :=
  Erdos849PairCoverage.counts_for_pair cert high hn hm h5 h7

/-- The two finite exclusions put each four-column pattern in the covered range. -/
theorem counts_for_patterns {a : ℕ} (pat : pattern a) (cert : CoverageAboveCutoff a)
    (cut3 : a ≤ 10^136 → ¬(occurs a 3 ∧ occurs a 5 ∧ occurs a 7 ∧ occurs a 8))
    (cut6 : a ≤ 10^144 → ¬(occurs a 5 ∧ occurs a 6 ∧ occurs a 7 ∧ occurs a 8)) :
    35 ≤ a.primeFactors.card ∧
    (∀ n, 10 ≤ n → n.choose 5 = a → ∀ i : Fin 5, 7 ≤ (n-i.val).primeFactors.card) ∧
    (∀ m, 14 ≤ m → m.choose 7 = a → ∀ j : Fin 7, 5 ≤ (m-j.val).primeFactors.card) :=
  Erdos849PairCoverage.pattern_counts pat pat.1 pat.2.1 cert cut3 cut6

#print axioms counts_of_occupied
#print axioms counts_for_pair
#print axioms counts_for_patterns

end Erdos849FiveSevenCoverage
