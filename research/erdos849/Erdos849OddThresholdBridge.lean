import Erdos849OddExponentBridge
import Mathlib.Data.Finset.Sort

namespace Erdos849OddThresholdBridge

open Erdos849OddExponentBridge

def primorial (B : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (B+1)).filter Nat.Prime, p

def smallAt (B x : ℕ) : Prop := ∃ d u : ℕ, d ∣ primorial B ∧ x = d*u^2

theorem primorial_nineteen : primorial 19 = 9699690 := by decide

theorem small_of_no_witness {B x : ℕ} (hx : 0 < x)
    (h : ¬∃ p : ℕ, p.Prime ∧ B < p ∧ x.factorization p % 2 = 1) : smallAt B x := by
  obtain ⟨d,u,hd,hu,hm,hsq⟩ := Nat.sq_mul_squarefree_of_pos hx
  refine ⟨d,u,?_,by simpa only [mul_comm] using hm.symm⟩
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors hp
  have hone := Nat.factorization_eq_one_of_squarefree hsq prime (Nat.dvd_of_mem_primeFactors hp)
  have he : x.factorization p = 2*u.factorization p + 1 := by
    rw [← hm, Nat.factorization_mul (pow_ne_zero 2 hu.ne') hd.ne', Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hone]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_,prime⟩
  by_contra! hb
  exact h ⟨p,prime,by omega,by omega⟩

/-- Each of the positions in S provides a distinct prime of odd exponent
above B. The hypothesis d ≤ B makes the associates in the numerator unique. -/
theorem count_of_positions {a n d B : ℕ} (hd : d ≤ n) (hB : d ≤ B)
    (hv : n.choose d = a) (S : Finset ℕ) (sub : S ⊆ Finset.range d)
    (outside : ∀ s ∈ S, ¬smallAt B (n-s)) : S.card ≤ (oddPrimesAbove a B).card := by
  classical
  have witness (s : ℕ) (hs : s ∈ S) : ∃ p : ℕ, p.Prime ∧ B < p ∧ (n-s).factorization p % 2 = 1 := by
    have hs' := Finset.mem_range.mp (sub hs)
    by_contra bad
    exact outside s hs (small_of_no_witness (by omega) bad)
  let f (s : ℕ) := if h : s ∈ S then (witness s h).choose else 0
  have spec {s : ℕ} (hs : s ∈ S) : (f s).Prime ∧ B < f s ∧ (n-s).factorization (f s) % 2 = 1 := by
    simpa only [f,dif_pos hs] using (witness s hs).choose_spec
  have divides {s : ℕ} (hs : s ∈ S) : f s ∣ n-s := by
    apply Nat.dvd_of_factorization_pos
    have := (spec hs).2.2
    omega
  have maps : Set.MapsTo f (↑S) (↑(oddPrimesAbove a B)) := by
    intro s hs
    obtain ⟨hp,hgt,he⟩ := spec hs
    have eq := exponent_at_offset hd (hB.trans_lt hgt) hp (Finset.mem_range.mp (sub hs)) (divides hs)
    rw [hv] at eq
    have ha : a ≠ 0 := hv ▸ Nat.choose_ne_zero hd
    have dv : f s ∣ a := Nat.dvd_of_factorization_pos (by omega)
    exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,dv,ha⟩,hgt,by omega⟩
  have remainder {s : ℕ} (hs : s ∈ S) : n % f s = s := by
    have hsd := Finset.mem_range.mp (sub hs)
    have hsp : s < f s := by have := (spec hs).2.1; omega
    calc
      n % f s = ((n-s)+s) % f s := by congr 1; omega
      _ = s := by rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (divides hs), zero_add,
                       Nat.mod_eq_of_lt hsp, Nat.mod_eq_of_lt hsp]
  apply Finset.card_le_card_of_injOn f maps
  intro s hs t ht he
  exact (remainder hs).symm.trans (he ▸ remainder ht)

/-- An increasing list of r+1 selected positions in a length-d window has
two at distance at most g whenever r gaps of g+1 do not fit. -/
theorem close_pair {d g r : ℕ} (S : Finset ℕ) (sub : S ⊆ Finset.range d)
    (many : r+1 ≤ S.card) (space : d ≤ r*(g+1)) :
    ∃ i ∈ S, ∃ j ∈ S, i < j ∧ j-i ≤ g := by
  by_contra none
  let e := S.orderEmbOfFin rfl
  have grow (i : ℕ) (hi : i < S.card) : i*(g+1) ≤ e ⟨i,hi⟩ := by
    induction i with
    | zero => simp
    | succ i ih =>
      have prev : i < S.card := by omega
      have hlt : e ⟨i,prev⟩ < e ⟨i+1,hi⟩ := e.strictMono (by exact_mod_cast Nat.lt_succ_self i)
      have gap : ¬ e ⟨i+1,hi⟩ - e ⟨i,prev⟩ ≤ g := fun bad => none
        ⟨_,S.orderEmbOfFin_mem rfl _,_,S.orderEmbOfFin_mem rfl _,hlt,bad⟩
      have hrec := ih prev
      rw [Nat.succ_mul]
      omega
  have hr : r < S.card := by omega
  have hlast := Finset.mem_range.mp (sub (S.orderEmbOfFin_mem rfl ⟨r,hr⟩))
  change e ⟨r,hr⟩ < d at hlast
  have := grow r hr
  omega

theorem close_small_of_at_most_six {a n d B : ℕ} (hn : d ≤ n) (hB : d ≤ B)
    (hv : n.choose d = a) (hd : d ∈ Finset.Icc 8 16)
    (cap : (oddPrimesAbove a B).card ≤ 6) :
    ∃ i < d, ∃ j < d, i < j ∧ j-i ≤ (d-1)/(d-7) ∧ smallAt B (n-i) ∧ smallAt B (n-j) := by
  classical
  let S := (Finset.range d).filter (fun s => smallAt B (n-s))
  let T := (Finset.range d).filter (fun s => ¬smallAt B (n-s))
  have low := (count_of_positions hn hB hv T (Finset.filter_subset _ _) (by
    intro s hs; exact (Finset.mem_filter.mp hs).2)).trans cap
  have total := Finset.card_filter_add_card_filter_not (s := Finset.range d) (fun s => smallAt B (n-s))
  change S.card + T.card = (Finset.range d).card at total
  rw [Finset.card_range] at total
  have limits : ∀ j ∈ Finset.Icc 8 16, j ≤ (j-7)*((j-1)/(j-7)+1) := by decide
  have lower := (Finset.mem_Icc.mp hd).1
  obtain ⟨i,hi,j,hj,hlt,hgap⟩ := close_pair S (Finset.filter_subset _ _)
    (show d-7+1 ≤ S.card by omega) (limits d hd)
  obtain ⟨hi',hsi⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj',hsj⟩ := Finset.mem_filter.mp hj
  exact ⟨i,Finset.mem_range.mp hi',j,Finset.mem_range.mp hj',hlt,hgap,hsi,hsj⟩

def boundedDecade (d : ℕ) := if d=8 then 350000 else 1000000

/-- All-height assembly for a finite pair search and an independently
established high-height bound. Their ranges may overlap. -/
theorem seven_above_nineteen {a n d H : ℕ} (hn : d ≤ n) (hv : n.choose d = a)
    (hd : d ∈ Finset.Icc 8 16) (overlap : H ≤ boundedDecade d)
    (bounded : a ≤ 10^(boundedDecade d) → ∀ i < d, ∀ j < d, i < j →
      j-i ≤ (d-1)/(d-7) → ¬(smallAt 19 (n-i) ∧ smallAt 19 (n-j)))
    (tail : 10^H ≤ a → 7 ≤ (oddPrimesAbove a 19).card) :
    7 ≤ (oddPrimesAbove a 19).card := by
  by_cases high : 10^H ≤ a
  · exact tail high
  · have bound := (Nat.le_of_lt (lt_of_not_ge high)).trans
        (Nat.pow_le_pow_right (by decide : 0 < (10:ℕ)) overlap)
    by_contra! cap
    have hle := (Finset.mem_Icc.mp hd).2
    obtain ⟨i,hi,j,hj,hlt,gap,si,sj⟩ := close_small_of_at_most_six hn
      (by omega : d ≤ 19) hv hd (by omega)
    exact bounded bound i hi j hj hlt gap ⟨si,sj⟩

#print axioms primorial_nineteen
#print axioms small_of_no_witness
#print axioms count_of_positions
#print axioms close_pair
#print axioms close_small_of_at_most_six
#print axioms seven_above_nineteen

end Erdos849OddThresholdBridge
