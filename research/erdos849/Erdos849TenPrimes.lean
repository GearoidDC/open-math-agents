import Erdos849Factors
import Erdos849HostSelection
import Erdos849PatternBridge
import Erdos849PowerCollision
import Mathlib.Data.Nat.Choose.Bounds

/-! The prime support of a five-row value. The numerical exclusion through
    a googol and the published fixed-column classifications are explicit
    hypotheses of the final result. -/

namespace Erdos849TenPrimes

open Erdos849PatternBridge

private theorem pattern_pair : ∀ t ∈ fourColumnPatterns,
    ∃ j ∈ t, ∃ d ∈ t, 7 ≤ j ∧ j < d ∧ d ≤ 9 := by decide

private theorem deep_pair {a : ℕ} (ha : 10^100 < a) (hf : a.primeFactors.card ≤ 9)
    (hc : 5 ≤ (Erdos849Cases.rows a).ncard)
    (pairs : ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k) :
    ∃ j d : ℕ, 7 ≤ j ∧ j < d ∧ d ≤ 9 ∧ occurs a j ∧ occurs a d := by
  by_contra h
  have upper := Erdos849PatternBridge.at_most_four a pairs (by
    intro j k _ hk _ ⟨n, hn, he⟩
    have hbound := Erdos849Factors.small_of_deep_representation
      (by decide : 1 ≤ 10) hk hn he (by omega)
    have hcut : (2^10 * Nat.factorial 10)^(10-1) < 10^100 := by decide
    omega) (by
    intro t ht allCols
    obtain ⟨j,hj,d,hd,h7,hjd,hd9⟩ := pattern_pair t ht
    exact h ⟨j,d,h7,hjd,hd9,allCols j hj,allCols d hd⟩)
  change (Erdos849Cases.rows a).ncard ≤ 4 at upper
  omega

private theorem large_eighth_row {n : ℕ} (h : 10^100 < n.choose 8) : 10^12 ≤ n := by
  by_contra! hl
  have hh := (Nat.choose_le_pow n 8).trans (Nat.pow_le_pow_left hl.le 8)
  have : (10^12 : ℕ)^8 < 10^100 := by decide
  omega

private theorem large_ninth_row {n : ℕ} (h : 10^100 < n.choose 9) : 10^11 < n := by
  by_contra! hl
  have hh := (Nat.choose_le_pow n 9).trans (Nat.pow_le_pow_left hl 9)
  have : (10^11 : ℕ)^9 < 10^100 := by decide
  omega

/-- The finite certificate and nine fixed-column results are the only two
    external inputs. The prime-factor restriction extends to every size. -/
theorem ten_distinct_prime_factors {a : ℕ}
    (hc : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : ∀ b ≤ 10^100, (Erdos849Cases.rows b).ncard ≤ 4)
    (classified : 10^100 < a → ∀ t ∈ classifiedPairs, ¬∀ j ∈ t, occurs a j) :
    10 ≤ a.primeFactors.card := by
  have ha : 10^100 < a := by
    by_contra! h
    have := base a h
    omega
  by_contra! hf
  obtain ⟨j,d,h7,hjd,hd,⟨m,hjm,hm⟩,⟨n,_,hn⟩⟩ :=
    deep_pair ha (by omega) hc (classified ha)
  have hcoll : m.choose j = n.choose d := hm.trans hn.symm
  rcases (by omega : d = 8 ∨ d = 9) with rfl | rfl
  · obtain rfl : j = 7 := by omega
    have hrow := large_eighth_row (n:=n) (by rwa [hn])
    obtain ⟨p,e,b,s,hp,h11,_,hdiv,hb,h34,hs,heq⟩ :=
      Erdos849HostSelection.column_eight (by omega : 10^11 < n) (by rw [hn]; omega)
    subst n
    exact Erdos849PowerCollision.no_eight hp h11 hb h34 hs hrow hjm
      (by rwa [hcoll]) hcoll
  · have hrow := large_ninth_row (n:=n) (by rwa [hn])
    obtain ⟨p,e,b,s,hp,h11,_,hdiv,hb,h71,hs1,hs7,heq⟩ :=
      Erdos849HostSelection.column_nine hrow (by rw [hn]; omega)
    subst n
    exact Erdos849PowerCollision.no_nine hp h11 hb h71 hs1 (by omega) hrow.le h7 hjd hjm
      (by rwa [hcoll]) hcoll

end Erdos849TenPrimes
