import Erdos849Cases
import FormalConjectures.Wikipedia.Singmaster
import Mathlib.Data.Nat.Choose.Central

/-! Count full-triangle positions by reflecting the admissible half row in
Erdős 849. A row contributes twice, except at a positive central coefficient. -/

namespace Erdos849Reflection

open Erdos849Cases (rows)
open Singmaster (solutions)
open scoped Classical

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) :
    n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem half_strict {n i j : ℕ} (h : i < j) (hj : 2*j ≤ n) :
    n.choose i < n.choose j := by
  have pos := Nat.choose_pos (show i ≤ n by omega)
  have step := Nat.mul_lt_mul_of_pos_left (show i+1 < n-i by omega) pos
  rw [← Nat.choose_succ_right_eq] at step
  exact (Nat.lt_of_mul_lt_mul_right step).trans_le (half_mono h hj)

private def half (a : ℕ) : Set (ℕ × ℕ) :=
  {(n,k) | 1 ≤ k ∧ 2*k ≤ n ∧ n.choose k = a}

private def reflect (x : ℕ × ℕ) : ℕ × ℕ := (x.1, x.1 - x.2)

private theorem half_finite (a : ℕ) : (half a).Finite := by
  apply ((Set.finite_Iic a).prod (Set.finite_Iic a)).subset
  rintro ⟨n,k⟩ ⟨hk, hkn, he⟩
  have hn : n ≤ a := by simpa [← he] using half_mono hk hkn
  exact ⟨hn, by change k ≤ a; omega⟩

private theorem half_count (a : ℕ) : (half a).ncard = (rows a).ncard := by
  have himg : Prod.fst '' half a = rows a := by
    ext n
    constructor
    · rintro ⟨⟨m,k⟩, hk, rfl⟩
      exact ⟨k,hk⟩
    · rintro ⟨k,hk⟩
      exact ⟨(n,k),hk,rfl⟩
  have hinj : Set.InjOn Prod.fst (half a) := by
    rintro ⟨n,i⟩ ⟨hi,hni,hci⟩ ⟨m,j⟩ ⟨hj,hnj,hcj⟩ hnm
    change n = m at hnm
    subst m
    rcases lt_trichotomy i j with h | rfl | h
    · have := half_strict h hnj
      omega
    · rfl
    · have := half_strict h hni
      omega
  rw [← himg, hinj.ncard_image]

private theorem reflect_inj (a : ℕ) : Set.InjOn reflect (half a) := by
  rintro ⟨n,i⟩ ⟨_,hni,_⟩ ⟨m,j⟩ ⟨_,hmj,_⟩ h
  have hm : n=m := congrArg Prod.fst h
  have hk : n-i=m-j := congrArg Prod.snd h
  subst m
  congr 1
  omega

private theorem union_eq (a : ℕ) : half a ∪ reflect '' half a = solutions a := by
  ext ⟨n,k⟩
  constructor
  · rintro (⟨hk,hkn,he⟩ | ⟨⟨m,i⟩,⟨hi,him,he⟩,hh⟩)
    · exact ⟨hk,by omega,he⟩
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj hh
      exact ⟨by omega,by omega,(Nat.choose_symm (by omega)).trans he⟩
  · rintro ⟨hk,hkn,he⟩
    by_cases hs : 2*k ≤ n
    · exact Or.inl ⟨hk,hs,he⟩
    · exact Or.inr ⟨(n,n-k),⟨by omega,by omega,(Nat.choose_symm hkn.le).trans he⟩,
        Prod.ext rfl (show n-(n-k)=k by omega)⟩

private theorem mem_inter {a n k : ℕ} :
    (n,k) ∈ half a ∩ reflect '' half a ↔ 1 ≤ k ∧ n = 2*k ∧ k.centralBinom = a := by
  constructor
  · rintro ⟨⟨hk,hkn,he⟩,⟨⟨m,i⟩,⟨_,him,_⟩,hh⟩⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj hh
    have h : m=2*(m-i) := by omega
    exact ⟨hk,h,by simpa only [Nat.centralBinom, ← h] using he⟩
  · rintro ⟨hk,rfl,he⟩
    have hh : (2*k,k) ∈ half a := ⟨hk,le_rfl,he⟩
    exact ⟨hh,⟨(2*k,k),hh,Prod.ext rfl (show 2*k-k=k by omega)⟩⟩

/-- The unique undoubled position is the central one, when it exists.
This also covers the empty interiors at values zero and one. -/
theorem reflection_count (a : ℕ) :
    (solutions a).ncard + (if ∃ k ≥ 1, Nat.centralBinom k = a then 1 else 0) =
      2 * (rows a).ncard := by
  classical
  have hc := Set.ncard_union_add_ncard_inter (half a) (reflect '' half a)
    (half_finite a) ((half_finite a).image _)
  rw [union_eq, (reflect_inj a).ncard_image, half_count] at hc
  by_cases hs : ∃ k ≥ 1, Nat.centralBinom k = a
  · obtain ⟨k,hk,hv⟩ := hs
    have hs' : half a ∩ reflect '' half a = {(2*k,k)} := by
      ext ⟨n,i⟩
      rw [mem_inter]
      constructor
      · rintro ⟨_,rfl,hi⟩
        obtain rfl := Nat.centralBinom_strictMono.injective (hi.trans hv.symm)
        rfl
      · rintro hm
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp hm)
        exact ⟨hk,rfl,hv⟩
    simp only [hs', Set.ncard_singleton] at hc
    rw [if_pos (show ∃ i ≥ 1, Nat.centralBinom i = a from ⟨k,hk,hv⟩)]
    omega
  · have hs' : half a ∩ reflect '' half a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ⟨n,k⟩ hm
      obtain ⟨hk,_,hv⟩ := mem_inter.mp hm
      exact hs ⟨k,hk,hv⟩
    simp only [hs', Set.ncard_empty, Nat.add_zero] at hc
    rw [if_neg hs]
    omega

theorem full_positions_dichotomy (a : ℕ) :
    (solutions a).ncard = 2 * (rows a).ncard ∨
      (solutions a).ncard = 2 * (rows a).ncard - 1 := by
  classical
  have h := reflection_count a
  split at h <;> omega

theorem five_rows_iff_nine_or_ten_positions (a : ℕ) :
    (rows a).ncard = 5 ↔ (solutions a).ncard = 9 ∨ (solutions a).ncard = 10 := by
  rcases full_positions_dichotomy a with h | h <;> omega

#print axioms reflection_count
#print axioms full_positions_dichotomy
#print axioms five_rows_iff_nine_or_ten_positions

end Erdos849Reflection
