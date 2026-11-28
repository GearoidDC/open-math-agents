import Erdos849LargePrimePatterns
import Erdos849PrimeHosts

namespace Erdos849FiveSevenCoverage

open Erdos849PatternBridge Erdos849LargePrimePatterns

/-- Each prime divisor chooses an offset attaining its largest term valuation. -/
def Maximizing (a n k : ℕ) (f : ℕ → Fin k) : Prop :=
  ∀ p ∈ a.primeFactors, ∀ i : Fin k,
    (n-i.val).factorization p ≤ (n-(f p).val).factorization p

def Occupied (a : ℕ) (f : ℕ → Fin 5) (g : ℕ → Fin 7) : Prop :=
  ∀ i j, ∃ p ∈ a.primeFactors, f p = i ∧ g p = j

/-- The numerical input concerns both choices of maximizing offsets, including ties. -/
def CoverageAboveCutoff (a : ℕ) : Prop :=
  10^136 ≤ a → ∀ n m, 10 ≤ n → 14 ≤ m → n.choose 5 = a → m.choose 7 = a →
    ∀ f g, Maximizing a n 5 f → Maximizing a m 7 g → Occupied a f g

private theorem count_image {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset ℕ} (f : ℕ → α) (hit : ∀ i, ∃ p ∈ s, f p = i) :
    Fintype.card α ≤ s.card := by
  have sub : Finset.univ ⊆ s.image f := by
    intro i _
    exact Finset.mem_image.mpr (hit i)
  simpa using (Finset.card_le_card sub).trans Finset.card_image_le

/-- Counting works for any two assignment maps that occupy all 35 cells. -/
theorem counts_of_occupied {a : ℕ} {f : ℕ → Fin 5} {g : ℕ → Fin 7}
    (hit : Occupied a f g) :
    35 ≤ a.primeFactors.card ∧
    (∀ i, 7 ≤ (a.primeFactors.filter fun p => f p = i).card) ∧
    (∀ j, 5 ≤ (a.primeFactors.filter fun p => g p = j).card) := by
  constructor
  · have h := count_image (s := a.primeFactors) (fun p => (f p, g p)) (by
      rintro ⟨i,j⟩
      obtain ⟨p,hp,hf,hg⟩ := hit i j
      exact ⟨p,hp,Prod.ext hf hg⟩)
    simpa using h
  constructor
  · intro i
    simpa using count_image (s := a.primeFactors.filter fun p => f p = i) g (by
      intro j
      obtain ⟨p,hp,hf,hg⟩ := hit i j
      exact ⟨p,Finset.mem_filter.mpr ⟨hp,hf⟩,hg⟩)
  · intro j
    simpa using count_image (s := a.primeFactors.filter fun p => g p = j) f (by
      intro i
      obtain ⟨p,hp,hf,hg⟩ := hit i j
      exact ⟨p,Finset.mem_filter.mpr ⟨hp,hg⟩,hf⟩)

private theorem has_maximizer (a n k : ℕ) [NeZero k] : ∃ f, Maximizing a n k f := by
  classical
  have maxAt (p : ℕ) := Finset.exists_max_image (Finset.univ : Finset (Fin k))
    (fun i => (n-i.val).factorization p) Finset.univ_nonempty
  exact ⟨fun p => (maxAt p).choose,
    fun p _ i => (maxAt p).choose_spec.2 i (Finset.mem_univ i)⟩

private theorem assigned_divisors {a n k : ℕ} {f : ℕ → Fin k}
    (hk : 0 < k) (hn : k ≤ n) (ha : n.choose k = a) (hm : Maximizing a n k f)
    (i : Fin k) : (a.primeFactors.filter fun p => f p = i) ⊆ (n-i.val).primeFactors := by
  intro p hp
  obtain ⟨hp,hi⟩ := Finset.mem_filter.mp hp
  have prime := Nat.prime_of_mem_primeFactors hp
  have divides : p^1 ∣ n.choose k := by simpa [ha] using Nat.dvd_of_mem_primeFactors hp
  have hr : n % p < k := by
    simpa using Erdos849PrimeHosts.residue_lt_column prime hk hn divides
  have pos := prime.factorization_pos_of_dvd (by omega : n - n % p ≠ 0) (Nat.dvd_sub_mod n)
  have bound := hm p hp ⟨n%p,hr⟩
  rw [hi] at bound
  exact prime.mem_primeFactors (Nat.dvd_of_factorization_pos (ne_of_gt (lt_of_lt_of_le pos bound)))
    (by have := i.isLt; omega)

/-- The counts apply to the actual numerator terms of any admissible pair of rows. -/
theorem counts_for_pair {a n m : ℕ} (cert : CoverageAboveCutoff a) (high : 10^136 ≤ a)
    (hn : 10 ≤ n) (hm : 14 ≤ m) (h5 : n.choose 5 = a) (h7 : m.choose 7 = a) :
    35 ≤ a.primeFactors.card ∧ (∀ i : Fin 5, 7 ≤ (n-i.val).primeFactors.card) ∧
    (∀ j : Fin 7, 5 ≤ (m-j.val).primeFactors.card) := by
  obtain ⟨f,hf⟩ := has_maximizer a n 5
  obtain ⟨g,hg⟩ := has_maximizer a m 7
  obtain ⟨total,left,right⟩ := counts_of_occupied (cert high n m hn hm h5 h7 f g hf hg)
  exact ⟨total, fun i => (left i).trans (Finset.card_le_card
    (assigned_divisors (by decide) (by omega) h5 hf i)),
    fun j => (right j).trans (Finset.card_le_card
    (assigned_divisors (by decide) (by omega) h7 hg j))⟩

/-- The two independent finite exclusions put each four-column pattern in the
range of the occupancy computation. Every admissible row in either column qualifies. -/
theorem counts_for_patterns {a : ℕ} (pat : pattern a) (cert : CoverageAboveCutoff a)
    (cut3 : a ≤ 10^136 → ¬(occurs a 3 ∧ occurs a 5 ∧ occurs a 7 ∧ occurs a 8))
    (cut6 : a ≤ 10^144 → ¬(occurs a 5 ∧ occurs a 6 ∧ occurs a 7 ∧ occurs a 8)) :
    35 ≤ a.primeFactors.card ∧
    (∀ n, 10 ≤ n → n.choose 5 = a → ∀ i : Fin 5, 7 ≤ (n-i.val).primeFactors.card) ∧
    (∀ m, 14 ≤ m → m.choose 7 = a → ∀ j : Fin 7, 5 ≤ (m-j.val).primeFactors.card) := by
  obtain ⟨occ5,occ7,occ8,occ36⟩ := pat
  have high : 10^136 ≤ a := by
    by_contra! low
    rcases occ36 with occ3 | occ6
    · exact cut3 low.le ⟨occ3,occ5,occ7,occ8⟩
    · exact cut6 (low.le.trans (by decide)) ⟨occ5,occ6,occ7,occ8⟩
  obtain ⟨n,hn,h5⟩ := occ5
  obtain ⟨m,hm,h7⟩ := occ7
  exact ⟨(counts_for_pair cert high hn hm h5 h7).1,
    fun _ hn' h5' => (counts_for_pair cert high hn' hm h5' h7).2.1,
    fun _ hm' h7' => (counts_for_pair cert high hn hm' h5 h7').2.2⟩

#print axioms counts_of_occupied
#print axioms counts_for_pair
#print axioms counts_for_patterns

end Erdos849FiveSevenCoverage
