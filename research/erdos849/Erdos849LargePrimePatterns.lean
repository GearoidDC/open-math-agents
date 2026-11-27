import Erdos849PatternBridge
import Erdos849Cases
import Mathlib

namespace Erdos849LargePrimePatterns

open Erdos849PatternBridge

def largeFactors (a : ℕ) : Finset ℕ := a.primeFactors.filter (100 < ·)

theorem prime_count_through_100 : ((Finset.range 101).filter Nat.Prime).card = 25 := by decide

theorem seven_of_thirty_two {a : ℕ} (h : 32 ≤ a.primeFactors.card) :
    7 ≤ (largeFactors a).card := by
  have sub : a.primeFactors.filter (fun p => ¬ 100 < p) ⊆
      (Finset.range 101).filter Nat.Prime := by
    intro p hp
    obtain ⟨hm, hb⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_of_mem_primeFactors hm⟩
  have small := (Finset.card_le_card sub).trans_eq prime_count_through_100
  have total := Finset.card_filter_add_card_filter_not (s := a.primeFactors) (100 < ·)
  unfold largeFactors
  omega

/-- Offsets in the eight-term numerator block whose corresponding integer is 100-smooth. -/
noncomputable def smoothOffsets (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range 8).filter (fun s => ¬ ∃ p : ℕ, 100 < p ∧ p.Prime ∧ p ∣ n-s)

theorem two_smooth_of_at_most_six {a n : ℕ} (hn : 16 ≤ n) (hv : n.choose 8 = a)
    (hcap : (largeFactors a).card ≤ 6) : 2 ≤ (smoothOffsets n).card := by
  classical
  let bad (s : ℕ) := ∃ p : ℕ, 100 < p ∧ p.Prime ∧ p ∣ n-s
  let S := (Finset.range 8).filter bad
  let f (s : ℕ) := if h : bad s then h.choose else 0
  have spec {s : ℕ} (hs : s ∈ S) : 100 < f s ∧ (f s).Prime ∧ f s ∣ n-s := by
    have h := (Finset.mem_filter.mp hs).2
    simpa only [f, dif_pos h] using h.choose_spec
  have maps : Set.MapsTo f (↑S) (↑(largeFactors a)) := by
    intro s hs
    have ⟨hp,prime,hd⟩ := spec hs
    have hprod := hd.trans (Finset.dvd_prod_of_mem (fun i : ℕ => n-i) (Finset.mem_filter.mp hs).1)
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose, hv] at hprod
    have ha : a ≠ 0 := hv ▸ Nat.choose_ne_zero (by omega)
    have hdiv := (prime.dvd_mul.mp hprod).resolve_left (fun h => by
      have := prime.dvd_factorial.mp h; omega)
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨prime,hdiv,ha⟩,hp⟩
  have uniq {s t : ℕ} (hs : s ∈ S) (ht : t ∈ S) (he : f s=f t) : ¬ s<t := by
    intro hst
    have h₁ := (spec hs).2.2
    have h₂ := (spec ht).2.2
    rw [←he] at h₂
    have hd := Nat.dvd_sub h₁ h₂
    have sit := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
    have tit := Finset.mem_range.mp (Finset.mem_filter.mp ht).1
    have hp := (spec hs).1
    have := Nat.le_of_dvd (show 0 < (n-s)-(n-t) by omega) hd
    omega
  have inj : Set.InjOn f (↑S) := by
    intro s hs t ht he
    have := uniq hs ht he
    have := uniq ht hs he.symm
    omega
  have card := (Finset.card_le_card_of_injOn f maps inj).trans hcap
  have split := Finset.card_filter_add_card_filter_not (s := Finset.range 8) bad
  change (S.card + (smoothOffsets n).card = (Finset.range 8).card) at split
  rw [Finset.card_range] at split
  omega

def pattern (a : ℕ) : Prop :=
  occurs a 5 ∧ occurs a 7 ∧ occurs a 8 ∧ (occurs a 3 ∨ occurs a 6)

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) : n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem half_strict {n i j : ℕ} (h : i < j) (hj : 2*j ≤ n) : n.choose i < n.choose j := by
  have pos := Nat.choose_pos (show i ≤ n by omega)
  have step := Nat.mul_lt_mul_of_pos_left (show i+1 < n-i by omega) pos
  rw [← Nat.choose_succ_right_eq] at step
  exact (Nat.lt_of_mul_lt_mul_right step).trans_le (half_mono h hj)

private theorem count_columns {a : ℕ} (S : Finset ℕ) (pos : ∀ k ∈ S, 1 ≤ k)
    (occ : ∀ k ∈ S, occurs a k) : S.card ≤ (Erdos849Cases.rows a).ncard := by
  classical
  let row (k : ℕ) := if hm : k ∈ S then (occ k hm).choose else 0
  have spec {k : ℕ} (hm : k ∈ S) : 2*k ≤ row k ∧ (row k).choose k = a := by
    simpa only [row, dif_pos hm] using (occ k hm).choose_spec
  have maps : Set.MapsTo row (↑S) (Erdos849Cases.rows a) := fun k hk =>
    ⟨k,pos k hk,(spec hk).1,(spec hk).2⟩
  have uniq {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) (he : row i = row j) : ¬ i<j := by
    intro h
    obtain ⟨h₁,h₂⟩ := spec hj
    rw [← he] at h₁ h₂
    exact (half_strict h h₁).ne ((spec hi).2.trans h₂.symm)
  have inj : Set.InjOn row (↑S) := by
    intro i hi j hj he
    have := uniq hi hj he
    have := uniq hj hi he.symm
    omega
  have finite : (Erdos849Cases.rows a).Finite := by
    apply (Set.finite_Iic a).subset
    rintro n ⟨k,hk,hh,rfl⟩
    simpa using half_mono hk hh
  simpa using Set.ncard_le_ncard_of_injOn row maps inj finite

theorem pattern_has_five_rows {a : ℕ} (hp : pattern a) : 5 ≤ (Erdos849Cases.rows a).ncard := by
  obtain ⟨h5,h7,h8,h36⟩ := hp
  have h1 : occurs a 1 := by
    obtain ⟨n,hh,he⟩ := h8
    have hna : n ≤ a := by simpa [he] using half_mono (show 1 ≤ 8 by decide) hh
    exact ⟨a,by omega,Nat.choose_one_right _⟩
  rcases h36 with h3 | h6
  · let S : Finset ℕ := {1,3,5,7,8}
    have hb := count_columns S (by decide) (by
      intro k hk
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> assumption)
    exact (by decide : 5 = S.card) ▸ hb
  · let S : Finset ℕ := {1,5,6,7,8}
    have hb := count_columns S (by decide) (by
      intro k hk
      simp only [S,Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> assumption)
    exact (by decide : 5 = S.card) ▸ hb

/-- The bounded Pell scan excludes a row in column eight with two smooth terms
when both columns five and seven occur. The tail is a distinct-prime bound
for the four indicated columns. Both computations remain explicit inputs. -/
theorem seven_for_patterns {a : ℕ} (hp : pattern a)
    (base : a ≤ 10^128 → (Erdos849Cases.rows a).ncard ≤ 4)
    (pell : 10^128 < a → a < 10^5000 → ∀ n, 16 ≤ n → n.choose 8 = a →
      2 ≤ (smoothOffsets n).card → ¬ (occurs a 5 ∧ occurs a 7))
    (tail : 10^5000 ≤ a → pattern a → 32 ≤ a.primeFactors.card) :
    7 ≤ (largeFactors a).card := by
  by_cases upper : 10^5000 ≤ a
  · exact seven_of_thirty_two (tail upper hp)
  have rows := pattern_has_five_rows hp
  have ha : 10^128 < a := by by_contra! h; have := base h; omega
  obtain ⟨h5,h7,⟨n,hn,hv⟩,_⟩ := hp
  by_contra! h
  exact pell ha (by omega) n (by omega) hv (two_smooth_of_at_most_six (by omega) hv (by omega)) ⟨h5,h7⟩

/-- Previous column exclusions force either exceptional pattern if a five-row
value has at most five large primes. The preceding result rules both out. -/
theorem six_for_five_rows {a : ℕ} (rows : 5 ≤ (Erdos849Cases.rows a).ncard)
    (previous : 5 ≤ (Erdos849Cases.rows a).ncard → (largeFactors a).card ≤ 5 → pattern a)
    (base : a ≤ 10^128 → (Erdos849Cases.rows a).ncard ≤ 4)
    (pell : 10^128 < a → a < 10^5000 → ∀ n, 16 ≤ n → n.choose 8 = a →
      2 ≤ (smoothOffsets n).card → ¬ (occurs a 5 ∧ occurs a 7))
    (tail : 10^5000 ≤ a → pattern a → 32 ≤ a.primeFactors.card) :
    6 ≤ (largeFactors a).card := by
  by_contra! h
  have := seven_for_patterns (previous rows (by omega)) base pell tail
  omega

#print axioms prime_count_through_100
#print axioms seven_of_thirty_two
#print axioms two_smooth_of_at_most_six
#print axioms pattern_has_five_rows
#print axioms seven_for_patterns
#print axioms six_for_five_rows

end Erdos849LargePrimePatterns
