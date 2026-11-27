import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.GCDMonoid.Finset

/-! Locating every prime-power divisor of a binomial coefficient in its
numerator block. The offset is the ordinary least nonnegative residue. -/

namespace Erdos849PrimeHosts

private theorem small_residue_of_carry {n k P : ℕ} (hP : 0 < P) (hk : k ≤ n)
    (hc : P ≤ k % P + (n-k) % P) : n % P < k := by
  have hx := Nat.mod_lt k hP
  have hy := Nat.mod_lt (n-k) hP
  have hs : n % P = (k%P + (n-k)%P) % P := by
    simpa only [Nat.add_sub_cancel' hk] using Nat.add_mod k (n-k) P
  calc
    n % P = _ := hs
    _ = (k%P + (n-k)%P - P) % P := Nat.mod_eq_sub_mod hc
    _ = k%P + (n-k)%P - P := Nat.mod_eq_of_lt (by omega)
    _ < k := by have := Nat.mod_le k P; omega

/-- If a positive-column binomial coefficient is divisible by a prime power,
the row index reduced modulo that prime power is strictly below its column. -/
theorem residue_lt_column {n k p e : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hd : p^e ∣ n.choose k) : n % p^e < k := by
  by_cases he : e = 0
  · rw [he, pow_zero, Nat.mod_one]
    omega
  let carries := (Finset.Ico 1 (Nat.log p n + 1)).filter
    fun i => p^i ≤ k % p^i + (n-k) % p^i
  have hcard : (n.choose k).factorization p = carries.card :=
    Nat.factorization_choose hp hkn (Nat.lt_succ_self _)
  have hcount : e ≤ carries.card := hcard ▸
    (hp.pow_dvd_iff_le_factorization (Nat.choose_pos hkn).ne').1 hd
  by_contra! hbad
  have hsub : carries ⊆ Finset.Ico 1 e := by
    intro i hi
    obtain ⟨hmem, hcarry⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hmem).1, ?_⟩
    by_contra! hie
    have remainder : n % p^e ≤ n % p^i := by
      rw [← Nat.mod_mod_of_dvd n (pow_dvd_pow p hie)]
      exact Nat.mod_le _ _
    exact (small_residue_of_carry (pow_pos hp.pos _) hkn hcarry).not_ge (hbad.trans remainder)
  have hb := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hb
  omega

/-- The canonical offset supplies an actual numerator term divisible by the
entire prime power. -/
theorem exists_host {n k p e : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hkn : k ≤ n)
    (hd : p^e ∣ n.choose k) : ∃ s < k, p^e ∣ n-s :=
  ⟨n % p^e, residue_lt_column hp hk hkn hd, Nat.dvd_sub_mod n⟩

/-- The coefficient divides the lcm of its own numerator block of length k. -/
theorem choose_dvd_lcm_block {n k : ℕ} (hkn : k ≤ n) :
    n.choose k ∣ (Finset.range k).lcm (fun s => n-s) := by
  by_cases hk : k = 0
  · simp [hk]
  have hpos : (Finset.range k).lcm (fun s => n-s) ≠ 0 := by
    apply Finset.lcm_ne_zero_iff.mpr
    intro s hs
    have := Finset.mem_range.mp hs
    omega
  rw [← Nat.factorization_prime_le_iff_dvd (Nat.choose_ne_zero hkn) hpos]
  intro p hp
  apply (hp.pow_dvd_iff_le_factorization hpos).mp
  obtain ⟨s, hsk, hd⟩ := exists_host hp (by omega : 1 ≤ k) hkn
    ((hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hkn)).mpr (le_refl _))
  exact hd.trans (Finset.dvd_lcm (Finset.mem_range.mpr hsk))

end Erdos849PrimeHosts
