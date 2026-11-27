import Erdos849Factors
import Erdos849PatternBridge

namespace Erdos849SixteenGraph

open Erdos849PatternBridge

def lastColumn (a : ℕ) : ℕ := if 10^500 < a then 15 else 17

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) : n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

set_option exponentiation.threshold 600 in
theorem column_bound {a n k : ℕ} (ha : 10^100 < a) (hf : a.primeFactors.card ≤ 15)
    (hkn : 2*k ≤ n) (hv : n.choose k = a) : k ≤ lastColumn a := by
  unfold lastColumn
  split
  next hlarge =>
    by_contra! hk
    have hb := Erdos849Factors.small_of_deep_representation (by decide : 1 ≤ 16)
      hk hkn hv (by omega)
    have : (2^16 * Nat.factorial 16)^(16-1) < 10^500 := by decide
    omega
  next =>
    by_contra! hk
    have hn : 0 < n := by omega
    have hval : a ≤ n^15 := (Erdos849Factors.value_le_row_pow_prime_factors hn (by omega) hv).trans
      (Nat.pow_le_pow_right hn hf)
    have hN : 10^6 ≤ n := by
      by_contra! h
      have hlim := Nat.pow_le_pow_left h.le 15
      have : ((10:ℕ)^6)^15 < 10^100 := by decide
      omega
    have hchoose := ((half_mono hk hkn).trans hv.le).trans hval
    have hdesc := n.pow_sub_le_descFactorial 18
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
    have hp : (4^18*n^3)*n^15 ≤ (5^18*Nat.factorial 18)*n^15 := calc
      _ = (4*n)^18 := by ring
      _ ≤ (5*(n+1-18))^18 := Nat.pow_le_pow_left (by omega) _
      _ = 5^18 * (n+1-18)^18 := mul_pow _ _ _
      _ ≤ 5^18 * (Nat.factorial 18 * n^15) := Nat.mul_le_mul_left _ (hdesc.trans
        (Nat.mul_le_mul_left _ hchoose))
      _ = _ := (mul_assoc _ _ _).symm
    have h := Nat.le_of_mul_le_mul_right hp (pow_pos hn _)
    have hsmall := (Nat.mul_le_mul_left (4^18) (Nat.pow_le_pow_left hN 3)).trans h
    exact (by decide : ¬ (4^18*((10:ℕ)^6)^3 ≤ 5^18*Nat.factorial 18)) hsmall

/-- The numerical certificate describes only four-element subsets of the
    permitted proper columns that avoid all published classified pairs. -/
theorem sixteen_distinct_prime_factors {a : ℕ} (hc : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : ∀ b ≤ 10^100, (Erdos849Cases.rows b).ncard ≤ 4)
    (classified : 10^100 < a → ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k)
    (computed : 10^100 < a → a.primeFactors.card ≤ 15 → ∀ T : Finset ℕ,
      T ⊆ Finset.Icc 2 (lastColumn a) → T.card = 4 →
      (∀ t ∈ classifiedPairs, ¬ t ⊆ T) → ¬∀ k ∈ T, occurs a k) :
    16 ≤ a.primeFactors.card := by
  classical
  by_contra! h
  have hf : a.primeFactors.card ≤ 15 := by omega
  have ha : 10^100 < a := by by_contra! hle; have := base a hle; omega
  let s := (Finset.Icc 2 (lastColumn a)).filter (occurs a)
  have hsmall : s.card ≤ 3 := by
    by_contra! hh
    obtain ⟨T,hTs,hT⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
    have hall : ∀ k ∈ T, occurs a k := fun k hk => (Finset.mem_filter.mp (hTs hk)).2
    apply computed ha hf T (hTs.trans (Finset.filter_subset _ _)) hT _ hall
    intro t ht hsub
    exact classified ha t ht fun k hk => hall k (hsub hk)
  let rows := Erdos849Cases.rows a
  let col (n : ℕ) := if hn : n ∈ rows then hn.choose else 0
  have spec (n : ℕ) (hn : n ∈ rows) :
      1 ≤ col n ∧ 2 * col n ≤ n ∧ n.choose (col n) = a := by
    simpa only [col,dif_pos hn] using hn.choose_spec
  have maps : Set.MapsTo col rows (↑(insert 1 s) : Set ℕ) := by
    intro n hn
    obtain ⟨hk,hkn,hv⟩ := spec n hn
    by_cases he : col n = 1
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega,column_bound ha hf hkn hv⟩,⟨n,hkn,hv⟩⟩))
  have inj : Set.InjOn col rows := by
    intro n hn m hm he
    obtain ⟨hk,hkn,hv⟩ := spec n hn
    obtain ⟨_,hjm,hw⟩ := spec m hm
    rw [← he] at hjm hw
    exact Erdos849FiniteBridge.same_column hk (by omega) (by omega) (hv.trans hw.symm)
  have hb := Set.ncard_le_ncard_of_injOn col maps inj (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hb
  have h4 : (insert 1 s).card ≤ 4 := (Finset.card_insert_le _ _).trans (by omega)
  change (Erdos849Cases.rows a).ncard ≤ _ at hb
  omega

end Erdos849SixteenGraph
