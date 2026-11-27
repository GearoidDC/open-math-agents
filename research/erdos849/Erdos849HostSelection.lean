import Erdos849HostCofactors
import Mathlib

/-! Small cofactors belonging to large-base prime powers in columns 8 and 9. -/

namespace Erdos849HostSelection

open Erdos849HostCofactors

def singles (n k : ℕ) := (Finset.range k).filter fun s => (assigned n k s).card = 1

private def smallPrimes : Finset ℕ := {2,3,5,7}

/-- Singleton hosts after removing the offsets of primes below 11. -/
def good (n k : ℕ) := singles n k \ smallPrimes.image (offset n k)

theorem singles_count {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hbig : k.factorial < n+1-k) :
    2*k ≤ (n.choose k).primeFactors.card + (singles n k).card := by
  have hm (p : ℕ) (hp : p ∈ (n.choose k).primeFactors) : offset n k p ∈ Finset.range k := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    apply Finset.mem_range.mpr
    exact Erdos849PrimeHosts.residue_lt_column hprime hk hkn
      ((hprime.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hkn)).mpr (le_refl _))
  have hsum : (n.choose k).primeFactors.card = ∑ s ∈ Finset.range k, (assigned n k s).card :=
    Finset.card_eq_sum_card_fiberwise hm
  have hpoint (s : ℕ) (hs : s ∈ Finset.range k) :
      2 ≤ (assigned n k s).card + (if (assigned n k s).card = 1 then 1 else 0) := by
    have hsk := Finset.mem_range.mp hs
    have hpos := Finset.card_pos.mpr (occupied hk hkn hsk (by omega))
    split_ifs <;> omega
  have h := Finset.sum_le_sum hpoint
  simpa [Finset.sum_add_distrib, Finset.sum_boole, singles, ← hsum, Nat.mul_comm] using h

theorem good_count {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hbig : k.factorial < n+1-k) :
    2*k ≤ (n.choose k).primeFactors.card + (good n k).card + 4 := by
  have h := singles_count hk hkn hbig
  have h₁ : (singles n k).card ≤ (good n k).card + (smallPrimes.image (offset n k)).card :=
    Finset.card_le_card_sdiff_add_card
  have h₂ : (smallPrimes.image (offset n k)).card ≤ 4 :=
    Finset.card_image_le.trans (by decide : smallPrimes.card ≤ 4)
  omega

theorem good_mem {n k s : ℕ} (hs : s ∈ good n k) : s ∈ Finset.range k :=
  (Finset.mem_filter.mp (Finset.mem_sdiff.mp hs).1).1

theorem small_cofactor {n k B t : ℕ} {S : Finset ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hsub : S ⊆ Finset.range k) (hc : t ≤ S.card) (hbound : k.factorial < (B+1)^t) :
    ∃ s ∈ S, cofactor n k s ≤ B := by
  by_contra! hbad
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq hc
  have hlow : (B+1)^t ≤ ∏ s ∈ T, cofactor n k s := calc
    _ = ∏ _ ∈ T, (B+1) := by simp [hT]
    _ ≤ _ := Finset.prod_le_prod' fun s hs => hbad s (hTS hs)
  have hdiv := Finset.prod_dvd_prod_of_subset T (Finset.range k) (cofactor n k) (hTS.trans hsub)
  rw [prod_cofactors hk hkn] at hdiv
  exact hbound.not_ge (hlow.trans (Nat.le_of_dvd (Nat.factorial_pos _) hdiv))

theorem represent {n k s : ℕ} (hkn : k ≤ n) (hs : s ∈ good n k) :
    ∃ p e : ℕ, p.Prime ∧ 11 ≤ p ∧ 1 ≤ e ∧ p^e ∣ n.choose k ∧
      1 ≤ cofactor n k s ∧ n = cofactor n k s * p^e + s := by
  obtain ⟨hsing, hsmall⟩ := Finset.mem_sdiff.mp hs
  obtain ⟨hsk, hcard⟩ := Finset.mem_filter.mp hsing
  obtain ⟨p, he⟩ := Finset.card_eq_one.mp hcard
  have hp : p ∈ assigned n k s := he ▸ Finset.mem_singleton_self p
  obtain ⟨hdivs, hofs⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hdivs
  have hbig : 11 ≤ p := by
    by_contra! h
    have low : ∀ q ∈ Finset.range 11, Nat.Prime q → q ∈ smallPrimes := by decide
    exact hsmall (Finset.mem_image.mpr ⟨p, low p (Finset.mem_range.mpr h) hprime, hofs⟩)
  have hpos := hprime.factorization_pos_of_dvd (Nat.choose_ne_zero hkn) (Nat.dvd_of_mem_primeFactors hdivs)
  refine ⟨p, _, hprime, hbig, hpos, (hprime.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hkn)).mpr le_rfl, ?_, ?_⟩
  · have hrow := host_factorization n k s
    have hlt := Finset.mem_range.mp hsk
    by_contra! hzero
    have hz : cofactor n k s = 0 := by omega
    rw [hz, mul_zero] at hrow
    omega
  · have hrow := host_factorization n k s
    have hlt := Finset.mem_range.mp hsk
    have hprod : n-s = cofactor n k s * p^(n.choose k).factorization p := by
      simpa [hostPart, he, component, Nat.mul_comm] using hrow.symm
    omega

/-- A one-prime host in the eighth column with multiplier at most 34. -/
theorem column_eight {n : ℕ} (hn : 10^11 < n) (hf : (n.choose 8).primeFactors.card ≤ 9) :
    ∃ p e b s : ℕ, p.Prime ∧ 11 ≤ p ∧ 1 ≤ e ∧ p^e ∣ n.choose 8 ∧
      1 ≤ b ∧ b ≤ 34 ∧ s < 8 ∧ n = b*p^e+s := by
  have hgc := good_count (n := n) (by decide : 1 ≤ 8) (by omega)
    (by norm_num [Nat.factorial]; omega)
  obtain ⟨s, hs, hb⟩ := small_cofactor (n := n) (B := 34) (by decide : 1 ≤ 8) (by omega)
    (fun _ h => good_mem h) (by omega : 3 ≤ (good n 8).card) (by decide)
  obtain ⟨p,e,hp,hbase,he,hd,hpos,hnr⟩ := represent (by omega : 8 ≤ n) hs
  exact ⟨p,e,_,s,hp,hbase,he,hd,hpos,hb,Finset.mem_range.mp (good_mem hs),hnr⟩

/-- In the ninth column an interior one-prime host has multiplier at most 71. -/
theorem column_nine {n : ℕ} (hn : 10^11 < n) (hf : (n.choose 9).primeFactors.card ≤ 9) :
    ∃ p e b s : ℕ, p.Prime ∧ 11 ≤ p ∧ 1 ≤ e ∧ p^e ∣ n.choose 9 ∧
      1 ≤ b ∧ b ≤ 71 ∧ 1 ≤ s ∧ s ≤ 7 ∧ n = b*p^e+s := by
  have hgc := good_count (n := n) (by decide : 1 ≤ 9) (by omega)
    (by norm_num [Nat.factorial]; omega)
  let mid := good n 9 \ ({0,8} : Finset ℕ)
  have hm : (good n 9).card ≤ mid.card + ({0,8} : Finset ℕ).card :=
    Finset.card_le_card_sdiff_add_card
  have hc : 3 ≤ mid.card := by
    have : ({0,8} : Finset ℕ).card = 2 := by decide
    omega
  obtain ⟨s, hs, hb⟩ := small_cofactor (n := n) (B := 71) (by decide : 1 ≤ 9) (by omega)
    (fun _ h => good_mem (Finset.mem_sdiff.mp h).1) hc (by decide)
  obtain ⟨hg, hends⟩ := Finset.mem_sdiff.mp (show s ∈ mid from hs)
  have hsk := Finset.mem_range.mp (good_mem hg)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hends
  obtain ⟨p,e,hp,hbase,he,hd,hpos,hnr⟩ := represent (by omega : 9 ≤ n) hg
  exact ⟨p,e,_,s,hp,hbase,he,hd,hpos,hb,by omega,by omega,hnr⟩

end Erdos849HostSelection
