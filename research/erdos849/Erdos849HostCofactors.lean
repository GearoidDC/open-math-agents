import Erdos849PrimeHosts
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas

/-! Group the prime powers of a binomial coefficient by their canonical
numerator offsets. The remaining cofactors account for exactly the factorial. -/

namespace Erdos849HostCofactors

def component (a p : ℕ) : ℕ := p ^ a.factorization p

def offset (n k p : ℕ) : ℕ := n % component (n.choose k) p

def assigned (n k s : ℕ) : Finset ℕ :=
  (n.choose k).primeFactors.filter fun p => offset n k p = s

def hostPart (n k s : ℕ) : ℕ :=
  ∏ p ∈ assigned n k s, component (n.choose k) p

def cofactor (n k s : ℕ) : ℕ := (n-s) / hostPart n k s

theorem hostPart_dvd (n k s : ℕ) : hostPart n k s ∣ n-s := by
  apply Finset.prod_dvd_of_isRelPrime
  · intro p hp q hq hpq
    have h₁ := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    have h₂ := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    exact Nat.coprime_iff_isRelPrime.mp (Nat.coprime_pow_primes _ _ h₁ h₂ hpq)
  · intro p hp
    rw [← (Finset.mem_filter.mp hp).2]
    exact Nat.dvd_sub_mod n

theorem host_factorization (n k s : ℕ) : hostPart n k s * cofactor n k s = n-s :=
  Nat.mul_div_cancel' (hostPart_dvd n k s)

theorem prod_hostParts {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∏ s ∈ Finset.range k, hostPart n k s = n.choose k := by
  have hmap (p : ℕ) (hp : p ∈ (n.choose k).primeFactors) :
      offset n k p ∈ Finset.range k := by
    have hprime := Nat.prime_of_mem_primeFactors hp
    exact Finset.mem_range.mpr (Erdos849PrimeHosts.residue_lt_column hprime hk hkn
      ((hprime.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hkn)).mpr (le_refl _)))
  exact (Finset.prod_fiberwise_of_maps_to hmap (component (n.choose k))).trans
    (Nat.prod_primeFactors_pow_factorization (Nat.choose_ne_zero hkn)).symm

/-- After assigning every complete prime power, the product of the leftover
integer factors equals the denominator factorial. Several primes may share
one host. -/
theorem prod_cofactors {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∏ s ∈ Finset.range k, cofactor n k s = k.factorial := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.choose_pos hkn)
  calc
    _ = (∏ s ∈ Finset.range k, hostPart n k s) * ∏ s ∈ Finset.range k, cofactor n k s := by
      rw [prod_hostParts hk hkn]
    _ = ∏ s ∈ Finset.range k, (n-s) := by rw [← Finset.prod_mul_distrib]; simp_rw [host_factorization]
    _ = k.factorial * n.choose k := by
      rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose]
    _ = _ := mul_comm _ _

theorem cofactor_dvd_factorial {n k s : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hs : s < k) :
    cofactor n k s ∣ k.factorial := by
  rw [← prod_cofactors hk hkn]
  exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hs)

/-- A numerator term larger than the denominator factorial must host a prime. -/
theorem occupied {n k s : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hs : s < k)
    (hlarge : k.factorial < n-s) : (assigned n k s).Nonempty := by
  by_contra! hempty
  have he : hostPart n k s = 1 := by simp [hostPart, hempty]
  have hc : n-s ∣ k.factorial := by
    simpa [cofactor, he] using cofactor_dvd_factorial hk hkn hs
  exact hlarge.not_ge (Nat.le_of_dvd (Nat.factorial_pos _) hc)

/-- If every numerator term exceeds the denominator factorial, the value has
at least as many distinct prime factors as the column index. -/
theorem distinct_prime_count_ge_column {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hlarge : k.factorial < n+1-k) : k ≤ (n.choose k).primeFactors.card := by
  have hsub : Finset.range k ⊆ (n.choose k).primeFactors.image (offset n k) := by
    intro s hs
    have hsk := Finset.mem_range.mp hs
    obtain ⟨p, hp⟩ := occupied hk hkn hsk (by omega)
    let h := Finset.mem_filter.mp hp
    exact Finset.mem_image.mpr ⟨p, h.1, h.2⟩
  simpa using (Finset.card_le_card hsub).trans Finset.card_image_le

end Erdos849HostCofactors
