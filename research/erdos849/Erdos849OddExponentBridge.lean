import Erdos849PatternBridge
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Factorial.BigOperators

namespace Erdos849OddExponentBridge

open Erdos849PatternBridge

def oddPrimesAbove (a k : ℕ) : Finset ℕ :=
  a.primeFactors.filter (fun p => k < p ∧ a.factorization p % 2 = 1)

def smallSquareClass (x : ℕ) : Prop := ∃ d u : ℕ, d ∣ 210 ∧ x = d*u^2

noncomputable def smallOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range 8).filter (fun s => smallSquareClass (n-s))

/-- The squarefree part of a positive integer with no odd exponent above eight divides 210. -/
theorem small_of_no_odd {x : ℕ} (hx : 0 < x)
    (h : ¬∃ p : ℕ, p.Prime ∧ 8 < p ∧ x.factorization p % 2 = 1) : smallSquareClass x := by
  obtain ⟨d,u,hd,hu,hm,hsq⟩ := Nat.sq_mul_squarefree_of_pos hx
  refine ⟨d,u,?_, by simpa only [mul_comm] using hm.symm⟩
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  apply (Nat.prod_primeFactors_dvd_iff (by decide : 210 ≠ 0)).mpr
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hone := Nat.factorization_eq_one_of_squarefree hsq hprime (Nat.dvd_of_mem_primeFactors hp)
  have he : x.factorization p = 2*u.factorization p + 1 := by
    rw [← hm, Nat.factorization_mul (pow_ne_zero 2 hu.ne') hd.ne', Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hone]
  have hsmall : p ≤ 8 := by
    by_contra! hgt
    exact h ⟨p,hprime,hgt,by omega⟩
  have at_most_eight : ∀ q ∈ Finset.range 9, q.Prime → q ∣ 210 := by decide
  exact Nat.mem_primeFactors.mpr ⟨hprime,
    at_most_eight p (Finset.mem_range.mpr (by omega)) hprime, by decide⟩

private theorem unique_offset {n k p s t : ℕ} (hk : k ≤ n) (hkp : k < p)
    (hs : s < k) (ht : t < k) (h₁ : p ∣ n-s) (h₂ : p ∣ n-t) : s = t := by
  have no_lt {i j : ℕ} (hi : i < k) (hj : j < k)
      (di : p ∣ n-i) (dj : p ∣ n-j) (hlt : i < j) : False := by
    have hd := Nat.dvd_sub di dj
    have := Nat.le_of_dvd (show 0 < (n-i)-(n-j) by omega) hd
    omega
  rcases lt_trichotomy s t with hlt | he | hgt
  · exact (no_lt hs ht h₁ h₂ hlt).elim
  · exact he
  · exact (no_lt ht hs h₂ h₁ hgt).elim

/-- An assigned prime above the column size has the same exponent in the
numerator term and the binomial coefficient. -/
theorem exponent_at_offset {n k p s : ℕ} (hk : k ≤ n) (hkp : k < p) (hp : p.Prime)
    (hs : s < k) (hd : p ∣ n-s) : (n.choose k).factorization p = (n-s).factorization p := by
  have hfac : ¬ p ∣ k.factorial := fun h => (not_le_of_gt hkp) (hp.dvd_factorial.mp h)
  calc
    (n.choose k).factorization p = (k.factorial * n.choose k).factorization p := by
      rw [Nat.factorization_mul (Nat.factorial_ne_zero k) (Nat.choose_ne_zero hk),
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hfac, zero_add]
    _ = (∏ i ∈ Finset.range k, (n-i)).factorization p := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
    _ = ∑ i ∈ Finset.range k, (n-i).factorization p := by
      apply Nat.factorization_prod_apply
      intro i hi
      have := Finset.mem_range.mp hi
      omega
    _ = (n-s).factorization p := by
      apply Finset.sum_eq_single_of_mem s (Finset.mem_range.mpr hs)
      intro t ht he
      apply Nat.factorization_eq_zero_of_not_dvd
      intro htdiv
      exact he (unique_offset hk hkp (Finset.mem_range.mp ht) hs htdiv hd)

/-- Distinct numerator positions outside the small square classes supply
distinct large primes of odd exponent in the common value. -/
theorem seven_of_one_small {a n : ℕ} (hn : 16 ≤ n) (hv : n.choose 8 = a)
    (small : (smallOffsets n).card ≤ 1) : 7 ≤ (oddPrimesAbove a 8).card := by
  classical
  let S := (Finset.range 8).filter (fun s => ¬smallSquareClass (n-s))
  have witness (s : ℕ) (hs : s ∈ S) : ∃ p : ℕ, p.Prime ∧ 8 < p ∧ (n-s).factorization p % 2 = 1 := by
    have hs8 := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    by_contra h
    exact (Finset.mem_filter.mp hs).2 (small_of_no_odd (by omega) h)
  let f (s : ℕ) := if h : s ∈ S then (witness s h).choose else 0
  have spec {s : ℕ} (hs : s ∈ S) : (f s).Prime ∧ 8 < f s ∧ (n-s).factorization (f s) % 2 = 1 := by
    simpa only [f, dif_pos hs] using (witness s hs).choose_spec
  have divides {s : ℕ} (hs : s ∈ S) : f s ∣ n-s := by
    apply Nat.dvd_of_factorization_pos
    have he := (spec hs).2.2
    omega
  have maps : Set.MapsTo f (↑S) (↑(oddPrimesAbove a 8)) := by
    intro s hs
    obtain ⟨hp,hgt,he⟩ := spec hs
    have eq := exponent_at_offset (by omega : 8 ≤ n) hgt hp
      (Finset.mem_range.mp (Finset.mem_filter.mp hs).1) (divides hs)
    rw [hv] at eq
    have ha : a ≠ 0 := hv ▸ Nat.choose_ne_zero (by omega)
    have hd : f s ∣ a := Nat.dvd_of_factorization_pos (by omega)
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,hd,ha⟩,hgt,by omega⟩
  have inj : Set.InjOn f (↑S) := by
    intro s hs t ht he
    have h₂ := divides ht
    rw [←he] at h₂
    exact unique_offset (by omega) (spec hs).2.1 (Finset.mem_range.mp (Finset.mem_filter.mp hs).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp ht).1) (divides hs) h₂
  have lower := Finset.card_le_card_of_injOn f maps inj
  have split := Finset.card_filter_add_card_filter_not (s := Finset.range 8)
    (fun s => smallSquareClass (n-s))
  change (smallOffsets n).card + S.card = (Finset.range 8).card at split
  rw [Finset.card_range] at split
  omega

private theorem decimal_height_mono {j k : ℕ} (h : j ≤ k) : (10 : ℕ)^j ≤ 10^k :=
  Nat.pow_le_pow_right (by decide) h

/-- The explicit finite Pell search and the independent large-height
square-class bound overlap and hence give the all-height result. -/
theorem seven_for_columns_seven_eight {a : ℕ} (h7 : occurs a 7) (h8 : occurs a 8)
    (bounded : a ≤ 10^1000000 → occurs a 7 → ∀ n, 16 ≤ n → n.choose 8 = a →
      (smallOffsets n).card ≤ 1)
    (tail : 10^250000 ≤ a → occurs a 7 → occurs a 8 → 9 ≤ (oddPrimesAbove a 8).card) :
    7 ≤ (oddPrimesAbove a 8).card := by
  by_cases high : 10^250000 ≤ a
  · exact (by decide : 7 ≤ 9).trans (tail high h7 h8)
  · have overlap := decimal_height_mono (by decide : 250000 ≤ 1000000)
    obtain ⟨n,hn,hv⟩ := h8
    exact seven_of_one_small hn hv (bounded ((Nat.le_of_lt (lt_of_not_ge high)).trans overlap) h7 n hn hv)

#print axioms small_of_no_odd
#print axioms exponent_at_offset
#print axioms seven_of_one_small
#print axioms seven_for_columns_seven_eight

end Erdos849OddExponentBridge
