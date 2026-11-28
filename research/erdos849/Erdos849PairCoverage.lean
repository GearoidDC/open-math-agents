import Erdos849LargePrimePatterns
import Erdos849PrimeHosts

namespace Erdos849PairCoverage

open Erdos849PatternBridge Erdos849LargePrimePatterns

/-- Any choice of a maximal-valuation offset is allowed at each prime. -/
def Maximizing (a n k : ℕ) (f : ℕ → Fin k) : Prop :=
  ∀ p ∈ a.primeFactors, ∀ i : Fin k,
    (n-i.val).factorization p ≤ (n-(f p).val).factorization p

def Occupied {k h : ℕ} (a : ℕ) (f : ℕ → Fin k) (g : ℕ → Fin h) : Prop :=
  ∀ i j, ∃ p ∈ a.primeFactors, f p = i ∧ g p = j

/-- The separate numerical certificate for individual positions at the given height. -/
def CoverageAbove (a k h exponent : ℕ) : Prop :=
  10^exponent ≤ a → ∀ n m, 2*k ≤ n → 2*h ≤ m → n.choose k = a → m.choose h = a →
    ∀ f g, Maximizing a n k f → Maximizing a m h g → Occupied a f g

private theorem count_image {α : Type*} [Fintype α] [DecidableEq α]
    {s : Finset ℕ} (f : ℕ → α) (hit : ∀ i, ∃ p ∈ s, f p = i) :
    Fintype.card α ≤ s.card := by
  have sub : Finset.univ ⊆ s.image f := by
    intro i _
    exact Finset.mem_image.mpr (hit i)
  simpa using (Finset.card_le_card sub).trans Finset.card_image_le

theorem counts_of_occupied {a k h : ℕ} {f : ℕ → Fin k} {g : ℕ → Fin h}
    (hit : Occupied a f g) :
    k*h ≤ a.primeFactors.card ∧
    (∀ i, h ≤ (a.primeFactors.filter fun p => f p = i).card) ∧
    (∀ j, k ≤ (a.primeFactors.filter fun p => g p = j).card) := by
  constructor
  · have b := count_image (s := a.primeFactors) (fun p => (f p,g p)) (by
      rintro ⟨i,j⟩
      obtain ⟨p,hp,hf,hg⟩ := hit i j
      exact ⟨p,hp,Prod.ext hf hg⟩)
    simpa using b
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

theorem has_maximizer (a n k : ℕ) [NeZero k] : ∃ f, Maximizing a n k f := by
  classical
  have maxAt (p : ℕ) := Finset.exists_max_image (Finset.univ : Finset (Fin k))
    (fun i => (n-i.val).factorization p) Finset.univ_nonempty
  exact ⟨fun p => (maxAt p).choose,fun p _ i => (maxAt p).choose_spec.2 i (Finset.mem_univ i)⟩

theorem assigned_divisors {a n k : ℕ} {f : ℕ → Fin k}
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

theorem counts_for_pair {a n m k h exponent : ℕ} [NeZero k] [NeZero h]
    (cert : CoverageAbove a k h exponent) (high : 10^exponent ≤ a)
    (hn : 2*k ≤ n) (hm : 2*h ≤ m) (hk : n.choose k = a) (hh : m.choose h = a) :
    k*h ≤ a.primeFactors.card ∧ (∀ i : Fin k, h ≤ (n-i.val).primeFactors.card) ∧
    (∀ j : Fin h, k ≤ (m-j.val).primeFactors.card) := by
  obtain ⟨f,hf⟩ := has_maximizer a n k
  obtain ⟨g,hg⟩ := has_maximizer a m h
  obtain ⟨total,left,right⟩ := counts_of_occupied (cert high n m hn hm hk hh f g hf hg)
  exact ⟨total, fun i => (left i).trans (Finset.card_le_card
    (assigned_divisors (Nat.pos_of_ne_zero (NeZero.ne k)) (by omega) hk hf i)),
    fun j => (right j).trans (Finset.card_le_card
    (assigned_divisors (Nat.pos_of_ne_zero (NeZero.ne h)) (by omega) hh hg j))⟩

def ThreeCutoff (a : ℕ) : Prop :=
  a ≤ 10^136 → ¬(occurs a 3 ∧ occurs a 5 ∧ occurs a 7 ∧ occurs a 8)

def SixCutoff (a : ℕ) : Prop :=
  a ≤ 10^144 → ¬(occurs a 5 ∧ occurs a 6 ∧ occurs a 7 ∧ occurs a 8)

theorem pattern_height {a : ℕ} (pat : pattern a) (cut3 : ThreeCutoff a) (cut6 : SixCutoff a) :
    10^136 ≤ a := by
  obtain ⟨occ5,occ7,occ8,occ36⟩ := pat
  by_contra! low
  rcases occ36 with occ3 | occ6
  · exact cut3 low.le ⟨occ3,occ5,occ7,occ8⟩
  · exact cut6 (low.le.trans (by decide)) ⟨occ5,occ6,occ7,occ8⟩

def RowCounts (a k required : ℕ) : Prop :=
  ∀ n, 2*k ≤ n → n.choose k = a → ∀ i : Fin k, required ≤ (n-i.val).primeFactors.card

theorem pattern_counts {a k h : ℕ} [NeZero k] [NeZero h] (pat : pattern a)
    (ok : occurs a k) (oh : occurs a h) (cert : CoverageAbove a k h 136)
    (cut3 : ThreeCutoff a) (cut6 : SixCutoff a) :
    k*h ≤ a.primeFactors.card ∧ RowCounts a k h ∧ RowCounts a h k := by
  have high := pattern_height pat cut3 cut6
  obtain ⟨n,hn,hk⟩ := ok
  obtain ⟨m,hm,hh⟩ := oh
  exact ⟨(counts_for_pair cert high hn hm hk hh).1,
    fun _ hn' hk' => (counts_for_pair cert high hn' hm hk' hh).2.1,
    fun _ hm' hh' => (counts_for_pair cert high hn hm' hk hh').2.2⟩

theorem five_eight {a : ℕ} (pat : pattern a) (cert : CoverageAbove a 5 8 136)
    (cut3 : ThreeCutoff a) (cut6 : SixCutoff a) :
    40 ≤ a.primeFactors.card ∧ RowCounts a 5 8 ∧ RowCounts a 8 5 :=
  pattern_counts pat pat.1 pat.2.2.1 cert cut3 cut6

/-- This 56-cell hypothesis is stronger than the 28-cell reflected certificate below. -/
theorem seven_eight {a : ℕ} (pat : pattern a) (cert : CoverageAbove a 7 8 136)
    (cut3 : ThreeCutoff a) (cut6 : SixCutoff a) :
    56 ≤ a.primeFactors.card ∧ RowCounts a 7 8 ∧ RowCounts a 8 7 :=
  pattern_counts pat pat.2.1 pat.2.2.1 cert cut3 cut6

/-- Reflected pairs (3,4), (2,5), (1,6), (0,7), in the order used by the verifier. -/
def eighthBlock (s : Fin 8) : Fin 4 :=
  ⟨if s.val < 4 then 3-s.val else s.val-4, by have := s.isLt; split <;> omega⟩

def ReflectedCoverage (a : ℕ) : Prop :=
  10^136 ≤ a → ∀ n m, 14 ≤ n → 16 ≤ m → n.choose 7 = a → m.choose 8 = a →
    ∀ f g, Maximizing a n 7 f → Maximizing a m 8 g → Occupied a f (eighthBlock ∘ g)

def blockProduct (m : ℕ) (b : Fin 4) := (m-(3-b.val))*(m-(4+b.val))

private theorem block_divisors {a m : ℕ} {g : ℕ → Fin 8} (hm : 16 ≤ m)
    (h8 : m.choose 8 = a) (hg : Maximizing a m 8 g) (b : Fin 4) :
    (a.primeFactors.filter fun p => (eighthBlock ∘ g) p = b) ⊆ (blockProduct m b).primeFactors := by
  intro p hp
  obtain ⟨hp,hb⟩ := Finset.mem_filter.mp hp
  have prime := Nat.prime_of_mem_primeFactors hp
  have hits := assigned_divisors (by decide : 0<8) (by omega) h8 hg (g p)
    (Finset.mem_filter.mpr ⟨hp,rfl⟩)
  have divisor := Nat.dvd_of_mem_primeFactors hits
  have hval := congrArg Fin.val hb
  change (if (g p).val<4 then 3-(g p).val else (g p).val-4) = b.val at hval
  have bb := b.isLt
  have gg := (g p).isLt
  apply prime.mem_primeFactors
  · unfold blockProduct
    split at hval
    · have h : (g p).val = 3-b.val := by omega
      exact dvd_mul_of_dvd_left (h ▸ divisor) _
    · have h : (g p).val = 4+b.val := by omega
      exact dvd_mul_of_dvd_right (h ▸ divisor) _
  · exact Nat.mul_ne_zero (by omega) (by omega)

/-- The 28 reflected cells bound the number of distinct primes in each actual block product. -/
theorem seven_eight_reflected {a : ℕ} (pat : pattern a) (cert : ReflectedCoverage a)
    (cut3 : ThreeCutoff a) (cut6 : SixCutoff a) :
    28 ≤ a.primeFactors.card ∧ RowCounts a 7 4 ∧
    (∀ m, 16 ≤ m → m.choose 8 = a → ∀ b, 7 ≤ (blockProduct m b).primeFactors.card) := by
  have high := pattern_height pat cut3 cut6
  have pair (n m : ℕ) (hn : 14 ≤ n) (hm : 16 ≤ m) (h7 : n.choose 7 = a) (h8 : m.choose 8 = a) :
      28 ≤ a.primeFactors.card ∧ (∀ i : Fin 7, 4 ≤ (n-i.val).primeFactors.card) ∧
      (∀ b, 7 ≤ (blockProduct m b).primeFactors.card) := by
    obtain ⟨f,hf⟩ := has_maximizer a n 7
    obtain ⟨g,hg⟩ := has_maximizer a m 8
    obtain ⟨total,left,right⟩ := counts_of_occupied (cert high n m hn hm h7 h8 f g hf hg)
    exact ⟨total,fun i => (left i).trans (Finset.card_le_card
      (assigned_divisors (by decide) (by omega) h7 hf i)),
      fun b => (right b).trans (Finset.card_le_card (block_divisors hm h8 hg b))⟩
  obtain ⟨n,hn,h7⟩ := pat.2.1
  obtain ⟨m,hm,h8⟩ := pat.2.2.1
  exact ⟨(pair n m hn hm h7 h8).1,fun v hv ha => (pair v m hv hm ha h8).2.1,
    fun v hv ha => (pair n v hn hv h7 ha).2.2⟩

#print axioms counts_for_pair
#print axioms five_eight
#print axioms seven_eight
#print axioms seven_eight_reflected

end Erdos849PairCoverage
