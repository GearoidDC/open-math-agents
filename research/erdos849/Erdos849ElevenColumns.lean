import Erdos849Factors
import Erdos849PatternBridge

namespace Erdos849ElevenColumns

open Erdos849PatternBridge

/-- Above a googol, a coefficient with at most ten prime divisors can only
    occur in the first ten columns of the half-triangle. -/
theorem column_bound {a n k : ℕ} (ha : 10^100 < a)
    (hf : a.primeFactors.card ≤ 10) (hkn : 2*k ≤ n) (hv : n.choose k = a) : k ≤ 10 := by
  by_contra! hk
  have hn : 0 < n := by omega
  have hval : a ≤ n^10 := (Erdos849Factors.value_le_row_pow_prime_factors hn (by omega) hv).trans
    (Nat.pow_le_pow_right hn hf)
  have hnlarge : 10^10 < n := by
    by_contra! h
    have hh := Nat.pow_le_pow_left h 10
    have he : ((10:ℕ)^10)^10 = 10^100 := by decide
    omega
  have hmono (i l : ℕ) (hi : i ≤ l) (hl : 2*l ≤ n) : n.choose i ≤ n.choose l := by
    induction l, hi using Nat.le_induction with
    | base => exact le_rfl
    | succ l _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  have hchoose : n.choose 11 ≤ n^10 := (hmono 11 k hk hkn).trans (hv ▸ hval)
  have hdesc := n.pow_sub_le_descFactorial 11
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hp : (3^11*n)*n^10 ≤ (4^11*Nat.factorial 11)*n^10 := calc
    _ = (3*n)^11 := by ring
    _ ≤ (4*(n+1-11))^11 := Nat.pow_le_pow_left (by omega) _
    _ = 4^11 * (n+1-11)^11 := mul_pow _ _ _
    _ ≤ 4^11 * (Nat.factorial 11 * n^10) := Nat.mul_le_mul_left _ (hdesc.trans
      (Nat.mul_le_mul_left _ hchoose))
    _ = _ := (mul_assoc _ _ _).symm
  have h := Nat.le_of_mul_le_mul_right hp (pow_pos hn _)
  norm_num [Nat.factorial] at h
  omega

/-- Five rows force a collision between columns seven through ten under
    the prime-count hypothesis and the published small-column exclusions. -/
theorem deep_pair {a : ℕ} (ha : 10^100 < a) (hf : a.primeFactors.card ≤ 10)
    (hc : 5 ≤ (Erdos849Cases.rows a).ncard)
    (pairs : ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k) :
    ∃ j d : ℕ, 7 ≤ j ∧ j < d ∧ d ≤ 10 ∧ occurs a j ∧ occurs a d := by
  by_contra h
  have clique : ∀ i ∈ ({2,3,4,6} : Finset ℕ), ∀ j ∈ ({2,3,4,6} : Finset ℕ),
      i ≠ j → ({i,j} : Finset ℕ) ∈ classifiedPairs := by decide
  have upper := Erdos849FiniteBridge.at_most_four_of_column_groups a (by
    intro n m i j hi hj hne hin hjm hev hew
    apply pairs {i,j} (clique i hi j hj hne)
    intro t ht
    rcases (show t = i ∨ t = j by simpa using ht) with rfl | rfl
    · exact ⟨n,hin,hev⟩
    · exact ⟨m,hjm,hew⟩) (by
    intro n m k j hk hj hne hkn hjm hn hm
    rcases lt_or_gt_of_ne hne with hkj | hjk
    · exact h ⟨k,j,hk,hkj,column_bound ha hf hjm hm,⟨n,hkn,hn⟩,⟨m,hjm,hm⟩⟩
    · exact h ⟨j,k,hj,hjk,column_bound ha hf hkn hn,⟨m,hjm,hm⟩,⟨n,hkn,hn⟩⟩)
  change (Erdos849Cases.rows a).ncard ≤ 4 at upper
  omega

end Erdos849ElevenColumns
