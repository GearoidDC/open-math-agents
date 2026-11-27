import Erdos849Factors
import Erdos849PatternBridge

namespace Erdos849NineteenGraph

open Erdos849PatternBridge

private def clique : Finset ℕ := {2,3,4,6}

/-- The numerical exclusions for collisions apart from the classified clique. -/
structure Exclusions (a : ℕ) : Prop where
  low : ∀ j d, 7 ≤ j → j < d → d ≤ 17 → occurs a j → occurs a d → j = 9 ∧ d = 17
  upper : ∀ j d, 7 ≤ j → j < d → 18 ≤ d → d ≤ 20 → ¬ (occurs a j ∧ occurs a d)
  exceptional : occurs a 9 → occurs a 17 → ¬ occurs a 5

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) : n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem column_bound {a n k : ℕ} (ha : 10^128 < a) (hf : a.primeFactors.card ≤ 18)
    (hkn : 2*k ≤ n) (hv : n.choose k = a) : k ≤ 20 := by
  by_contra! hk
  have hn : 0 < n := by omega
  have hval := (Erdos849Factors.value_le_row_pow_prime_factors hn (by omega : k ≤ n) hv).trans
    (Nat.pow_le_pow_right hn hf)
  have hN : 10^7 ≤ n := by
    by_contra! h
    have hlim := Nat.pow_le_pow_left h.le 18
    have : ((10:ℕ)^7)^18 < 10^128 := by decide
    omega
  have hchoose := ((half_mono (show 21 ≤ k by omega) hkn).trans hv.le).trans hval
  have hdesc := n.pow_sub_le_descFactorial 21
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
  have hp : (19^21*n^3)*n^18 ≤ (20^21*Nat.factorial 21)*n^18 := calc
    _ = (19*n)^21 := by ring
    _ ≤ (20*(n+1-21))^21 := Nat.pow_le_pow_left (by omega) _
    _ = 20^21 * (n+1-21)^21 := mul_pow _ _ _
    _ ≤ 20^21 * (Nat.factorial 21 * n^18) := Nat.mul_le_mul_left _ (hdesc.trans
      (Nat.mul_le_mul_left _ hchoose))
    _ = _ := (mul_assoc _ _ _).symm
  have h := Nat.le_of_mul_le_mul_right hp (pow_pos hn _)
  have hh := (Nat.mul_le_mul_left (19^21) (Nat.pow_le_pow_left hN 3)).trans h
  exact (by decide : ¬ (19^21*((10:ℕ)^7)^3 ≤ 20^21*Nat.factorial 21)) hh

/-- The external computations and published inputs appear in the hypotheses. -/
theorem nineteen_distinct_prime_factors {a : ℕ} (hrows : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : a ≤ 10^128 → (Erdos849Cases.rows a).ncard ≤ 4)
    (classified : 10^128 < a → ∀ t ∈ classifiedPairs, ¬∀ k ∈ t, occurs a k)
    (computed : 10^128 < a → a.primeFactors.card ≤ 18 → Exclusions a) :
    19 ≤ a.primeFactors.card := by
  classical
  by_contra! h
  have hf : a.primeFactors.card ≤ 18 := by omega
  have ha : 10^128 < a := by by_contra! hle; have := base hle; omega
  have ex := computed ha hf
  have pair {j d : ℕ} (h7 : 7 ≤ j) (hlt : j < d) (oj : occurs a j) (od : occurs a d) :
      j = 9 ∧ d = 17 := by
    by_cases hlow : d ≤ 17
    · exact ex.low j d h7 hlt hlow oj od
    obtain ⟨n,hkn,hv⟩ := od
    exact (ex.upper j d h7 hlt (by omega) (column_bound ha hf hkn hv) ⟨oj,n,hkn,hv⟩).elim
  have cl : ∀ {i j}, i ∈ clique → j ∈ clique → occurs a i → occurs a j → i = j := by
    intro i j hi hj oi oj
    by_contra hne
    have hs : ∀ i ∈ clique, ∀ j ∈ clique, i ≠ j → ({i,j} : Finset ℕ) ∈ classifiedPairs := by decide
    apply classified ha {i,j} (hs i hi j hj hne)
    intro k hk
    rcases (show k = i ∨ k = j by simpa using hk) with rfl | rfl <;> assumption
  by_cases special : occurs a 9 ∧ occurs a 17
  · have alternatives {k : ℕ} (hk : 1 ≤ k) (ok : occurs a k) :
        k=1 ∨ k∈clique ∨ k=9 ∨ k=17 := by
      have h5 := ex.exceptional special.1 special.2
      by_cases h : 7 ≤ k
      · rcases lt_trichotomy k 9 with hlt | heq | hgt
        · have := (pair h hlt ok special.1).1; omega
        · tauto
        · have := (pair (by decide : 7 ≤ 9) hgt special.1 ok).2; tauto
      · by_cases he : k=5
        · exact (h5 (he ▸ ok)).elim
        · simp [clique]; omega
    let rows := Erdos849Cases.rows a
    let col (n : ℕ) := if hn : n ∈ rows then hn.choose else 0
    have spec (n : ℕ) (hn : n ∈ rows) :
        1 ≤ col n ∧ 2*col n ≤ n ∧ n.choose (col n)=a := by
      simpa only [col,dif_pos hn] using hn.choose_spec
    let tag (k : ℕ) := if k=1 then 0 else if k=9 then 1 else if k=17 then 2 else 3
    have maps : Set.MapsTo (fun n => tag (col n)) rows (Set.Iio 4) := by
      intro n hn
      dsimp [tag]
      split_ifs <;> decide
    have inj : Set.InjOn (fun n => tag (col n)) rows := by
      intro n hn m hm ht
      obtain ⟨h1,h2,hv⟩ := spec n hn
      obtain ⟨h3,h4,hw⟩ := spec m hm
      have on : occurs a (col n) := ⟨n,h2,hv⟩
      have om : occurs a (col m) := ⟨m,h4,hw⟩
      have hN := alternatives h1 on
      have hM := alternatives h3 om
      have eq : col n = col m := by
        dsimp only [tag] at ht
        split_ifs at ht <;> first | omega | exact cl (by tauto) (by tauto) on om
      rw [← eq] at h4 hw
      exact Erdos849FiniteBridge.same_column h1 (by omega) (by omega) (hv.trans hw.symm)
    have hb := Set.ncard_le_ncard_of_injOn _ maps inj (Set.finite_Iio 4)
    rw [Set.ncard_Iio_nat] at hb
    change (Erdos849Cases.rows a).ncard ≤ _ at hb
    omega
  · have hb : (Erdos849Cases.rows a).ncard ≤ 4 := by
      apply Erdos849FiniteBridge.at_most_four_of_column_groups
      · intro n m k j hk hj hne hn hm hv hw
        exact hne (cl hk hj ⟨n,hn,hv⟩ ⟨m,hm,hw⟩)
      · intro n m k j hk hj hne hn hm hv hw
        have ok : occurs a k := ⟨n,hn,hv⟩
        have oj : occurs a j := ⟨m,hm,hw⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · obtain ⟨rfl,rfl⟩ := pair hk hlt ok oj
          exact special ⟨ok,oj⟩
        · obtain ⟨rfl,rfl⟩ := pair hj hgt oj ok
          exact special ⟨oj,ok⟩
    omega

end Erdos849NineteenGraph
