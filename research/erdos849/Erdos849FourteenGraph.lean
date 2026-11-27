import Erdos849Factors
import Erdos849PatternBridge

namespace Erdos849FourteenGraph

open Erdos849PatternBridge

private def first : Finset ℕ := {2,3,4,6}
private def second : Finset ℕ := {5,7,8}

/-- The numerical verifier only needs three pairs in {5,7,8} and the
    pairs of distinct columns in 9..14 in its middle range. -/
def numericalPair (j d : ℕ) : Prop :=
  j < d ∧ ((j ∈ second ∧ d ∈ second) ∨ (9 ≤ j ∧ d ≤ 14))

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) : n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem column_le_fourteen {a n k : ℕ} (ha : 10^100 < a) (hf : a.primeFactors.card ≤ 13)
    (hkn : 2*k ≤ n) (hv : n.choose k = a) : k ≤ 14 := by
  by_contra! hk
  have hn : 0 < n := by omega
  have hval : a ≤ n^13 := (Erdos849Factors.value_le_row_pow_prime_factors hn (by omega) hv).trans
    (Nat.pow_le_pow_right hn hf)
  have hN : 10^7 ≤ n := by
    by_contra! h
    have hlim := Nat.pow_le_pow_left h.le 13
    have : ((10:ℕ)^7)^13 < 10^100 := by decide
    omega
  have hchoose := ((half_mono hk hkn).trans hv.le).trans hval
  have hdesc := n.pow_sub_le_descFactorial 15
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hp : (3^15*n^2)*n^13 ≤ (4^15*Nat.factorial 15)*n^13 := calc
    _ = (3*n)^15 := by ring
    _ ≤ (4*(n+1-15))^15 := Nat.pow_le_pow_left (by omega) _
    _ = 4^15 * (n+1-15)^15 := mul_pow _ _ _
    _ ≤ 4^15 * (Nat.factorial 15 * n^13) := Nat.mul_le_mul_left _ (hdesc.trans
      (Nat.mul_le_mul_left _ hchoose))
    _ = _ := (mul_assoc _ _ _).symm
  have h := Nat.le_of_mul_le_mul_right hp (pow_pos hn _)
  have hsmall := (Nat.mul_le_mul_left (3^15) (Nat.pow_le_pow_left hN 2)).trans h
  exact (by decide : ¬ (3^15*((10:ℕ)^7)^2 ≤ 4^15*Nat.factorial 15)) hsmall

private theorem low_checks {a : ℕ} (classified : ∀ t ∈ classifiedPairs, ¬∀ j ∈ t, occurs a j)
    {k j : ℕ} (hk : k ∈ first) (hj : j ∈ first) (hne : k ≠ j) (hok : occurs a k)
    (hoj : occurs a j) : False := by
  have clique : ∀ i ∈ first, ∀ l ∈ first, i ≠ l → ({i,l} : Finset ℕ) ∈ classifiedPairs := by decide
  apply classified {k,j} (clique k hk j hj hne)
  intro u hu
  rcases (show u = k ∨ u = j by simpa using hu) with rfl | rfl
  · exact hok
  · exact hoj

private def group (k : ℕ) : ℕ := if k=1 then 0 else if k ∈ first then 1
  else if k ∈ second then 2 else 3

private theorem middle_bound {a : ℕ} (ha : 10^100 < a) (hf : a.primeFactors.card ≤ 13)
    (classified : ∀ t ∈ classifiedPairs, ¬∀ j ∈ t, occurs a j)
    (numerical : ∀ j d, numericalPair j d → occurs a j → occurs a d → False) :
    (Erdos849Cases.rows a).ncard ≤ 4 := by
  classical
  let rows := Erdos849Cases.rows a
  let col (n : ℕ) := if hn : n ∈ rows then hn.choose else 0
  have spec (n : ℕ) (hn : n ∈ rows) :
      1 ≤ col n ∧ 2 * col n ≤ n ∧ n.choose (col n) = a := by
    simpa only [col,dif_pos hn] using hn.choose_spec
  let tag (n : ℕ) := group (col n)
  have maps : Set.MapsTo tag rows (Set.Iio 4) := by
    intro n _
    change group (col n) < 4
    unfold group
    split_ifs <;> decide
  have same (k j : ℕ) (hk : 1 ≤ k) (hj : j ≤ 14) (hlt : k < j) (he : group k = group j)
      (hok : occurs a k) (hoj : occurs a j) : False := by
    have cert : ∀ k ∈ Finset.Icc 1 14, ∀ j ∈ Finset.Icc 1 14, k < j → group k = group j →
        (k ∈ first ∧ j ∈ first) ∨ (k ∈ second ∧ j ∈ second) ∨ (9 ≤ k ∧ j ≤ 14) := by decide
    rcases cert k (Finset.mem_Icc.mpr ⟨hk,by omega⟩) j
        (Finset.mem_Icc.mpr ⟨by omega,hj⟩) hlt he with hh | hh
    · exact low_checks classified hh.1 hh.2 hlt.ne hok hoj
    · exact numerical k j ⟨hlt,hh⟩ hok hoj
  have inj : Set.InjOn tag rows := by
    intro n hn m hm he
    obtain ⟨hk,hkn,hev⟩ := spec n hn
    obtain ⟨hj,hjm,hew⟩ := spec m hm
    rcases lt_trichotomy (col n) (col m) with hlt | heq | hgt
    · exact False.elim (same _ _ hk (column_le_fourteen ha hf hjm hew) hlt he
        ⟨n,hkn,hev⟩ ⟨m,hjm,hew⟩)
    · rw [← heq] at hjm hew
      exact Erdos849FiniteBridge.same_column hk (by omega) (by omega) (hev.trans hew.symm)
    · exact False.elim (same _ _ hj (column_le_fourteen ha hf hkn hev) hgt he.symm
        ⟨m,hjm,hew⟩ ⟨n,hkn,hev⟩)
  have bound := Set.ncard_le_ncard_of_injOn tag maps inj (Set.finite_Iio 4)
  simpa only [Set.ncard_Iio_nat] using bound

set_option exponentiation.threshold 500 in
/-- The published classifications, finite base range and two explicitly
    stated numerical certificates are external inputs. -/
theorem fourteen_distinct_prime_factors {a : ℕ} (hc : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : ∀ b ≤ 10^100, (Erdos849Cases.rows b).ncard ≤ 4)
    (classified : 10^100 < a → ∀ t ∈ classifiedPairs, ¬∀ j ∈ t, occurs a j)
    (middle : 10^100 < a → a ≤ 10^390 → a.primeFactors.card ≤ 13 →
      ∀ j d, numericalPair j d → occurs a j → occurs a d → False)
    (high : 10^390 < a → a.primeFactors.card ≤ 13 →
      ∀ j d : ℕ, 7 ≤ j → j < d → d ≤ 13 → occurs a j → occurs a d → False) :
    14 ≤ a.primeFactors.card := by
  by_contra! h
  have hf : a.primeFactors.card ≤ 13 := by omega
  have ha : 10^100 < a := by by_contra! hle; have := base a hle; omega
  by_cases hsize : a ≤ 10^390
  · have := middle_bound ha hf (classified ha) (middle ha hsize hf)
    omega
  have column {n k : ℕ} (hkn : 2*k ≤ n) (hn : n.choose k = a) : k ≤ 13 := by
    by_contra! hdeep
    have hb := Erdos849Factors.small_of_deep_representation (by decide : 1 ≤ 14)
      hdeep hkn hn (by omega)
    have : (2^14 * Nat.factorial 14)^(14-1) < 10^390 := by decide
    omega
  have upper := Erdos849FiniteBridge.at_most_four_of_column_groups a (by
    intro n m k j hk hj hne hkn hjm hn hm
    exact low_checks (classified ha) hk hj hne ⟨n,hkn,hn⟩ ⟨m,hjm,hm⟩) (by
    intro n m k j hk hj hne hkn hjm hn hm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact high (by omega) hf k j hk hlt (column hjm hm) ⟨n,hkn,hn⟩ ⟨m,hjm,hm⟩
    · exact high (by omega) hf j k hj hgt (column hkn hn) ⟨m,hjm,hm⟩ ⟨n,hkn,hn⟩)
  change (Erdos849Cases.rows a).ncard ≤ 4 at upper
  omega

end Erdos849FourteenGraph
