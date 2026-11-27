import Erdos849HostSelection

/-! Large-base prime-power hosts when the coefficient has at most ten distinct
prime factors. The thresholds use the product of all host cofactors. -/

namespace Erdos849ElevenHosts

open Erdos849HostSelection

private theorem interior {n k B t : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n)
    (hg : t + 2 ≤ (good n k).card) (hbound : k.factorial < (B+1)^t) :
    ∃ p e b s : ℕ, p.Prime ∧ 11 ≤ p ∧ 1 ≤ e ∧ p^e ∣ n.choose k ∧
      1 ≤ b ∧ b ≤ B ∧ 1 ≤ s ∧ s ≤ k-2 ∧ n = b*p^e+s := by
  let mid := good n k \ ({0,k-1} : Finset ℕ)
  have hm : (good n k).card ≤ mid.card + ({0,k-1} : Finset ℕ).card :=
    Finset.card_le_card_sdiff_add_card
  have hc : t ≤ mid.card := by
    have hsize : ({0,k-1} : Finset ℕ).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨s, hs, hb⟩ := small_cofactor (by omega : 1 ≤ k) hkn
    (fun _ h => good_mem (Finset.mem_sdiff.mp h).1) hc hbound
  obtain ⟨hsg, hends⟩ := Finset.mem_sdiff.mp (show s ∈ mid from hs)
  have hsk := Finset.mem_range.mp (good_mem hsg)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hends
  obtain ⟨p,e,hp,hbase,he,hd,hpos,hnr⟩ := represent hkn hsg
  exact ⟨p,e,_,s,hp,hbase,he,hd,hpos,hb,by omega,by omega,hnr⟩

/-- At least two large-prime singleton hosts remain in column 8. -/
theorem column_eight {n : ℕ} (hn : 10^7 < n) (hf : (n.choose 8).primeFactors.card ≤ 10) :
    ∃ p e b s : ℕ, p.Prime ∧ 11 ≤ p ∧ 1 ≤ e ∧ p^e ∣ n.choose 8 ∧
      1 ≤ b ∧ b ≤ 200 ∧ s < 8 ∧ n = b*p^e+s := by
  have hgc := good_count (n := n) (by decide : 1 ≤ 8) (by omega)
    (by norm_num [Nat.factorial]; omega)
  obtain ⟨s, hs, hb⟩ := small_cofactor (n := n) (B := 200) (by decide : 1 ≤ 8) (by omega)
    (fun _ h => good_mem h) (by omega : 2 ≤ (good n 8).card) (by decide)
  obtain ⟨p,e,hp,hbase,he,hd,hpos,hnr⟩ := represent (by omega : 8 ≤ n) hs
  exact ⟨p,e,_,s,hp,hbase,he,hd,hpos,hb,Finset.mem_range.mp (good_mem hs),hnr⟩

/-- At least two large-prime singleton hosts remain after removing the endpoints in column 9. -/
theorem column_nine {n : ℕ} (hn : 10^7 < n) (hf : (n.choose 9).primeFactors.card ≤ 10) :
    ∃ p e b s : ℕ, p.Prime ∧ 11 ≤ p ∧ 1 ≤ e ∧ p^e ∣ n.choose 9 ∧
      1 ≤ b ∧ b ≤ 602 ∧ 1 ≤ s ∧ s ≤ 7 ∧ n = b*p^e+s := by
  have hgc := good_count (n := n) (by decide : 1 ≤ 9) (by omega)
    (by norm_num [Nat.factorial]; omega)
  exact interior (t := 2) (by decide : 2 ≤ 9) (by omega) (by omega) (by decide)

/-- At least four large-prime singleton hosts remain after removing the endpoints in column 10. -/
theorem column_ten {n : ℕ} (hn : 10^7 < n) (hf : (n.choose 10).primeFactors.card ≤ 10) :
    ∃ p e b s : ℕ, p.Prime ∧ 11 ≤ p ∧ 1 ≤ e ∧ p^e ∣ n.choose 10 ∧
      1 ≤ b ∧ b ≤ 43 ∧ 1 ≤ s ∧ s ≤ 8 ∧ n = b*p^e+s := by
  have hgc := good_count (n := n) (by decide : 1 ≤ 10) (by omega)
    (by norm_num [Nat.factorial]; omega)
  exact interior (t := 4) (by decide : 2 ≤ 10) (by omega) (by omega) (by decide)

end Erdos849ElevenHosts
