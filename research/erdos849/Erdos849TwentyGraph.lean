import Erdos849Factors
import Erdos849PatternBridge

namespace Erdos849TwentyGraph

open Erdos849PatternBridge

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) : n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem column_bound {a n k : ℕ} (ha : 10^128 < a) (hf : a.primeFactors.card ≤ 19)
    (hkn : 2*k ≤ n) (hv : n.choose k = a) : k ≤ 22 := by
  by_contra! hk
  have hn : 0 < n := by omega
  have hval := (Erdos849Factors.value_le_row_pow_prime_factors hn (by omega : k ≤ n) hv).trans
    (Nat.pow_le_pow_right hn hf)
  have hN : 10^6 ≤ n := by
    by_contra! h
    have hlim := Nat.pow_le_pow_left h.le 19
    have : ((10:ℕ)^6)^19 < 10^128 := by decide
    omega
  have hchoose := ((half_mono (show 23 ≤ k by omega) hkn).trans hv.le).trans hval
  have hdesc := n.pow_sub_le_descFactorial 23
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hp : (19^23*n^4)*n^19 ≤ (20^23*Nat.factorial 23)*n^19 := calc
    _ = (19*n)^23 := by ring
    _ ≤ (20*(n+1-23))^23 := Nat.pow_le_pow_left (by omega) _
    _ = 20^23 * (n+1-23)^23 := mul_pow _ _ _
    _ ≤ 20^23 * (Nat.factorial 23 * n^19) := Nat.mul_le_mul_left _ (hdesc.trans
      (Nat.mul_le_mul_left _ hchoose))
    _ = _ := (mul_assoc _ _ _).symm
  have h := Nat.le_of_mul_le_mul_right hp (pow_pos hn _)
  have hh := (Nat.mul_le_mul_left (19^23) (Nat.pow_le_pow_left hN 4)).trans h
  exact (by decide : ¬ (19^23*((10:ℕ)^6)^4 ≤ 20^23*Nat.factorial 23)) hh

/-- Exclusions for a four-element set of proper columns. The arithmetic proof
    is supplied separately for the ranges below and above column 18. -/
def excluded (a : ℕ) (T : Finset ℕ) : Prop :=
  (∀ t ∈ classifiedPairs, ¬ t ⊆ T) → ¬ ∀ k ∈ T, occurs a k

theorem twenty_distinct_prime_factors {a : ℕ} (rows : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : a ≤ 10^128 → (Erdos849Cases.rows a).ncard ≤ 4)
    (classified : 10^128 < a → ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k)
    (small : 10^128 < a → a.primeFactors.card ≤ 19 → ∀ T : Finset ℕ,
      T ⊆ Finset.Icc 2 17 → T.card = 4 → excluded a T)
    (large : 10^128 < a → a.primeFactors.card ≤ 19 → ∀ T : Finset ℕ,
      T ⊆ Finset.Icc 2 22 → T.card = 4 → (∃ d ∈ T, 18 ≤ d) → excluded a T) :
    20 ≤ a.primeFactors.card := by
  classical
  by_contra! h
  have hf : a.primeFactors.card ≤ 19 := by omega
  have ha : 10^128 < a := by by_contra! hle; have := base hle; omega
  let s := (Finset.Icc 2 22).filter (occurs a)
  have hs : s.card ≤ 3 := by
    by_contra! hh
    obtain ⟨T,hTs,hT⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
    have ht : T ⊆ Finset.Icc 2 22 := hTs.trans (Finset.filter_subset _ _)
    have occ : ∀ k ∈ T, occurs a k := fun k hk => (Finset.mem_filter.mp (hTs hk)).2
    have avoid : ∀ t ∈ classifiedPairs, ¬t ⊆ T := by
      intro t mem sub
      exact classified ha t mem fun k hk => occ k (sub hk)
    by_cases hd : ∃ d ∈ T, 18 ≤ d
    · exact large ha hf T ht hT hd avoid occ
    · apply small ha hf T _ hT avoid occ
      intro d hmem
      have := Finset.mem_Icc.mp (ht hmem)
      exact Finset.mem_Icc.mpr ⟨this.1,by by_contra! h; exact hd ⟨d,hmem,by omega⟩⟩
  let R := Erdos849Cases.rows a
  let col (n : ℕ) := if hn : n ∈ R then hn.choose else 0
  have spec (n : ℕ) (hn : n ∈ R) :
      1 ≤ col n ∧ 2*col n ≤ n ∧ n.choose (col n)=a := by
    simpa only [col,dif_pos hn] using hn.choose_spec
  have maps : Set.MapsTo col R (↑(insert 1 s) : Set ℕ) := by
    intro n hn
    obtain ⟨h1,h2,hv⟩ := spec n hn
    by_cases he : col n = 1
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega,column_bound ha hf h2 hv⟩,⟨n,h2,hv⟩⟩))
  have inj : Set.InjOn col R := by
    intro n hn m hm he
    obtain ⟨h1,h2,hv⟩ := spec n hn
    obtain ⟨_,h3,hw⟩ := spec m hm
    rw [← he] at h3 hw
    exact Erdos849FiniteBridge.same_column h1 (by omega) (by omega) (hv.trans hw.symm)
  have hb := Set.ncard_le_ncard_of_injOn col maps inj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hb
  have h4 : (insert 1 s).card ≤ 4 := (Finset.card_insert_le _ _).trans (by omega)
  change (Erdos849Cases.rows a).ncard ≤ _ at hb
  omega

end Erdos849TwentyGraph
