import Erdos849TwentyGraph

namespace Erdos849TwentyOneGraph

open Erdos849PatternBridge

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) : n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- The 24th and all larger left-half columns are impossible at the given prime cap. -/
theorem column_bound {a n k : ℕ} (ha : 10^128 < a) (hf : a.primeFactors.card ≤ 20)
    (hkn : 2*k ≤ n) (hv : n.choose k = a) : k ≤ 23 := by
  by_contra! hk
  have hn : 0 < n := by omega
  have hval := (Erdos849Factors.value_le_row_pow_prime_factors hn (by omega : k ≤ n) hv).trans
    (Nat.pow_le_pow_right hn hf)
  have hN : 2000000 ≤ n := by
    by_contra! h
    have hlim := Nat.pow_le_pow_left h.le 20
    have : (2000000:ℕ)^20 < 10^128 := by decide
    omega
  have hchoose := ((half_mono (show 24 ≤ k by omega) hkn).trans hv.le).trans hval
  have hdesc := n.pow_sub_le_descFactorial 24
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hp : (19^24*n^4)*n^20 ≤ (20^24*Nat.factorial 24)*n^20 := calc
    _ = (19*n)^24 := by ring
    _ ≤ (20*(n+1-24))^24 := Nat.pow_le_pow_left (by omega) _
    _ = 20^24 * (n+1-24)^24 := mul_pow _ _ _
    _ ≤ 20^24 * (Nat.factorial 24 * n^20) := Nat.mul_le_mul_left _ (hdesc.trans
      (Nat.mul_le_mul_left _ hchoose))
    _ = _ := (mul_assoc _ _ _).symm
  have h := Nat.le_of_mul_le_mul_right hp (pow_pos hn _)
  have hh := (Nat.mul_le_mul_left (19^24) (Nat.pow_le_pow_left hN 4)).trans h
  exact (by decide : ¬ (19^24*(2000000:ℕ)^4 ≤ 20^24*Nat.factorial 24)) hh

/-- Assemble the separate interval, published classification, and numerical exclusions. -/
theorem twenty_one_distinct_prime_factors {a : ℕ} (rows : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : a ≤ 10^128 → (Erdos849Cases.rows a).ncard ≤ 4)
    (classified : 10^128 < a → ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k)
    (small : 10^128 < a → a.primeFactors.card ≤ 20 → ∀ T : Finset ℕ,
      T ⊆ Finset.Icc 2 17 → T.card = 4 → Erdos849TwentyGraph.excluded a T)
    (eighteen : 10^128 < a → a.primeFactors.card ≤ 20 → ∀ T : Finset ℕ,
      T ⊆ Finset.Icc 2 18 → T.card = 4 → 18 ∈ T → Erdos849TwentyGraph.excluded a T)
    (upper : 10^128 < a → a.primeFactors.card ≤ 20 → ∀ j d,
      7 ≤ j → j < d → 19 ≤ d → d ≤ 23 → ¬ (occurs a j ∧ occurs a d)) :
    21 ≤ a.primeFactors.card := by
  classical
  by_contra! h
  have hf : a.primeFactors.card ≤ 20 := by omega
  have ha : 10^128 < a := by by_contra! hle; have := base hle; omega
  have bound {k : ℕ} (hk : occurs a k) : k ≤ 23 := by
    obtain ⟨n, hkn, hv⟩ := hk
    exact column_bound ha hf hkn hv
  by_cases deep : ∃ d ≥ 19, occurs a d
  · obtain ⟨d, hd, od⟩ := deep
    have unique {k : ℕ} (hk : 7 ≤ k) (ok : occurs a k) : k = d := by
      rcases lt_trichotomy k d with hl | he | hg
      · exact (upper ha hf k d hk hl hd (bound od) ⟨ok, od⟩).elim
      · exact he
      · exact (upper ha hf d k (by omega) hg (by omega) (bound ok) ⟨od, ok⟩).elim
    have few : (Erdos849Cases.rows a).ncard ≤ 4 := by
      apply Erdos849FiniteBridge.at_most_four_of_column_groups
      · intro n m i j hi hj hne hin hjm hev hew
        have clique : ∀ i ∈ ({2,3,4,6} : Finset ℕ), ∀ j ∈ ({2,3,4,6} : Finset ℕ),
            i ≠ j → ({i,j} : Finset ℕ) ∈ classifiedPairs := by decide
        apply classified ha {i,j} (clique i hi j hj hne)
        intro k hk
        rcases (show k=i ∨ k=j by simpa using hk) with rfl | rfl
        · exact ⟨n,hin,hev⟩
        · exact ⟨m,hjm,hew⟩
      · intro n m i j hi hj hne hin hjm hev hew
        exact hne ((unique hi ⟨n,hin,hev⟩).trans (unique hj ⟨m,hjm,hew⟩).symm)
    omega
  let s := (Finset.Icc 2 18).filter (occurs a)
  have hs : s.card ≤ 3 := by
    by_contra! hh
    obtain ⟨T,hTs,hT⟩ := Finset.exists_subset_card_eq (show 4 ≤ s.card by omega)
    have ht : T ⊆ Finset.Icc 2 18 := hTs.trans (Finset.filter_subset _ _)
    have occ : ∀ k ∈ T, occurs a k := fun k hk => (Finset.mem_filter.mp (hTs hk)).2
    have avoid : ∀ t ∈ classifiedPairs, ¬t ⊆ T := by
      intro t mem sub
      exact classified ha t mem fun k hk => occ k (sub hk)
    by_cases hd : 18 ∈ T
    · exact eighteen ha hf T ht hT hd avoid occ
    · apply small ha hf T _ hT avoid occ
      intro d hmem
      have hbound := Finset.mem_Icc.mp (ht hmem)
      have hne : d ≠ 18 := by rintro rfl; exact hd hmem
      exact Finset.mem_Icc.mpr ⟨hbound.1, by omega⟩
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
    · have ok : occurs a (col n) := ⟨n,h2,hv⟩
      have h18 : col n ≤ 18 := by by_contra! hl; exact deep ⟨_,hl,ok⟩
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega,h18⟩,ok⟩))
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

#print axioms column_bound
#print axioms twenty_one_distinct_prime_factors

end Erdos849TwentyOneGraph
