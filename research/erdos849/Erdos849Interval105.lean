import Erdos849Cases
import Erdos849PatternBridge

namespace Erdos849Interval105

open Erdos849PatternBridge

/-- Deduce the new value cutoff from the three independently identifiable
    inputs in the added interval and the previous base case. -/
theorem five_rows_above_cutoff {a : ℕ} (hc : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : ∀ b ≤ 10^100, (Erdos849Cases.rows b).ncard ≤ 4)
    (published : 10^100 < a → ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k)
    (low : 10^100 < a → a ≤ 10^105 → ∀ t ∈ fourColumnPatterns, ¬∀ k ∈ t, occurs a k)
    (high : 10^100 < a → a ≤ 10^105 →
      ∀ j k : ℕ, 7 ≤ j → 10 ≤ k → occurs a j → occurs a k → j = k) : 10^105 < a := by
  have ha : 10^100 < a := by by_contra! h; have := base a h; omega
  by_contra! hab
  have h := at_most_four a (published ha) (high ha hab) (low ha hab)
  change (Erdos849Cases.rows a).ncard ≤ 4 at h
  omega

end Erdos849Interval105
