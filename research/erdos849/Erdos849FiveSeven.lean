import Erdos849Threshold
import Erdos849SparseCollision
import Erdos849ElevenCollision
import Erdos849HostSelection

/-! Exclusion of a common value above a googol in columns five and seven
when it has at most twelve distinct prime divisors. -/

namespace Erdos849FiveSeven

open Erdos849HostCofactors Erdos849HostSelection Erdos849SparseCollision

private theorem small_host {n : ℕ} (ha : 10^100 < n.choose 7)
    (hf : (n.choose 7).primeFactors.card ≤ 12) (hn : 7 ≤ n) :
    ∃ p e b s : ℕ, p.Prime ∧ p^e ∣ n.choose 7 ∧ b ≤ 70 ∧ s < 7 ∧ n = b*p^e+s := by
  have hc := singles_count (n := n) (by decide : 1≤7) hn
    (Erdos849Threshold.first_above_factorial ha (by decide))
  obtain ⟨s, hs, hb⟩ := small_cofactor (n := n) (B := 70) (by decide : 1≤7) hn
    (S := singles n 7) (Finset.filter_subset _ _) (by omega : 2 ≤ (singles n 7).card) (by decide)
  obtain ⟨hsk, hcard⟩ := Finset.mem_filter.mp hs
  obtain ⟨p, hsingle⟩ := Finset.card_eq_one.mp hcard
  have hp : p ∈ assigned n 7 s := hsingle ▸ Finset.mem_singleton_self p
  have hpf := (Finset.mem_filter.mp hp).1
  have hprime := Nat.prime_of_mem_primeFactors hpf
  have hrow := host_factorization n 7 s
  have hlt := Finset.mem_range.mp hsk
  have hprod : n-s = cofactor n 7 s * p^(n.choose 7).factorization p := by
    simpa [hostPart, hsingle, component, Nat.mul_comm] using hrow.symm
  exact ⟨p, _, _, s, hprime,
    (hprime.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hn)).mpr le_rfl, hb, hlt, by omega⟩

theorem no_collision {n m : ℕ} (ha : 10^100 < n.choose 7)
    (hf : (n.choose 7).primeFactors.card ≤ 12) (hn : 14 ≤ n) (hm : 10 ≤ m) :
    m.choose 5 ≠ n.choose 7 := by
  intro he
  obtain ⟨p,e,b,s,hp,hdvd,hb,hs,hnr⟩ := small_host ha hf (by omega)
  let P := p^e
  let q := m/P
  let r := m%P
  have hP : 0 < P := pow_pos hp.pos _
  have hr : r<5 := Erdos849PrimeHosts.residue_lt_column hp (by decide : 1≤5) (by omega) (he ▸ hdvd)
  have hmr : m=q*P+r := by simpa [q,r,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div m P).symm
  change n=b*P+s at hnr
  have hN : 600000000000000 ≤ n := by
    by_contra! h
    have h₁ := n.descFactorial_le_pow 7
    rw [Nat.descFactorial_eq_factorial_mul_choose] at h₁
    have h₂ := Nat.mul_lt_mul_of_pos_left ha (Nat.factorial_pos 7)
    have h₃ := Nat.pow_le_pow_left h.le 7
    exact (by decide : ¬(Nat.factorial 7*10^100 < 600000000000000^7)).elim
      (h₂.trans_le (h₁.trans h₃))
  have hbP := Nat.mul_le_mul_right P hb
  have hPlarge : 10^12 ≤ P := by omega
  let U := (Nat.factorial 5 : ℤ)*omitted 7 s s
  let V := (Nat.factorial 7 : ℤ)*omitted 5 r r
  have hu : U.natAbs ≤ 86400 := by dsimp [U]; interval_cases s <;> decide
  have hv : V.natAbs ≤ 120960 := by dsimp [V]; interval_cases r <;> decide
  have hv₀ : 5040 ≤ V.natAbs := by dsimp [V]; interval_cases r <;> decide
  have hc : (b:ℤ)*U ≡ (q:ℤ)*V [ZMOD P] := by
    simpa only [U,V,mul_left_comm,mul_comm,mul_assoc] using
      raw_congruence hP hs hr (by omega) (by omega) hnr hmr he.symm
  by_cases heq : (b:ℤ)*U = (q:ℤ)*V
  · have habs := congrArg Int.natAbs heq
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at habs
    have hq : q ≤ 18*b := by
      have := Nat.mul_le_mul_left q hv₀
      have := Nat.mul_le_mul_left b hu
      omega
    have hqP := Nat.mul_le_mul_right P hq
    rw [Nat.mul_assoc] at hqP
    have hml : 12 ≤ m := by
      by_contra! h
      have hlow := ha.trans_le he.ge
      have hsmall := Nat.choose_le_pow m 5
      have hupp := Nat.pow_le_pow_left h.le 5
      omega
    have hentry : n.choose 7 ≤ m.choose 6 := he.ge.trans (Nat.choose_le_succ_of_lt_half_left (by omega))
    have hg := Erdos849PowerCollision.next_row_bound (k := 6) (c := 19) (by omega) hentry
    omega
  · have hdiff := Int.natAbs_le_of_dvd_ne_zero hc.dvd (sub_ne_zero.mpr (Ne.symm heq))
    have hsum := Int.natAbs_sub_le ((q:ℤ)*V) ((b:ℤ)*U)
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at hsum hdiff
    have hadd := hdiff.trans (hsum.trans
      (Nat.add_le_add (Nat.mul_le_mul_left q hv) (Nat.mul_le_mul_left b hu)))
    have hscale : P ≤ 125000*(q-1) := by omega
    have hstep : (q-1)*P+P=q*P := by
      rw [← Nat.succ_mul]
      congr 1
      omega
    have hlift : (q-1)*P ≤ m+1-5 := by omega
    have hnP : n ≤ 71*P := by omega
    have hsq : n^2 ≤ 630125000*(m+1-5) := calc
      _ ≤ (71*P)^2 := Nat.pow_le_pow_left hnP 2
      _ = 5041*(P*P) := by ring
      _ ≤ 5041*((125000*(q-1))*P) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right P hscale)
      _ = 630125000*((q-1)*P) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hlift
    have hbound := Erdos849ElevenCollision.square_cutoff (by omega : 0<n) (by decide : 7≤2*5) hsq he
    have hlow := Nat.mul_le_mul_right (Nat.factorial 7) (Nat.pow_le_pow_left hN (2*5-7))
    exact (by decide : ¬(600000000000000^(2*5-7)*Nat.factorial 7 ≤
      630125000^5*Nat.factorial 5)).elim (hlow.trans hbound)

end Erdos849FiveSeven
