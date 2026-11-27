import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Order.Interval.Set.Nat

namespace Erdos849Bound

/-- Entries in a positive column strictly increase once its diagonal is reached. -/
private theorem column_lt {k n m : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hnm : n < m) :
    n.choose k < m.choose k := by
  have hpos : 0 < n.choose (k - 1) := Nat.choose_pos (by omega)
  calc
    n.choose k < (n + 1).choose k := by rw [Nat.choose_succ_left n k hk]; omega
    _ ≤ m.choose k := Nat.choose_le_choose k hnm

/-- Distinct rows realizing a value must use distinct positive columns. -/
theorem exists_large_column_of_row_count {a t : ℕ} (ht : 1 ≤ t)
    (hcount : {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.ncard = t) :
    ∃ n k : ℕ, t ≤ k ∧ 2 * k ≤ n ∧ n.choose k = a := by
  classical
  let rows : Set ℕ := {n | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}
  let column (n : ℕ) := if h : n ∈ rows then h.choose else 0
  have spec (n : ℕ) (hn : n ∈ rows) :
      1 ≤ column n ∧ 2 * column n ≤ n ∧ n.choose (column n) = a := by
    simpa [column, dif_pos hn] using hn.choose_spec
  by_contra! hsmall
  have maps : ∀ n ∈ rows, column n ∈ Set.Ico 1 t := by
    intro n hn
    obtain ⟨hk, hkn, hval⟩ := spec n hn
    refine ⟨hk, ?_⟩
    by_contra! hbig
    exact hsmall n (column n) hbig hkn hval
  have inj : Set.InjOn column rows := by
    intro n hn m hm heq
    obtain ⟨hk, hkn, hval⟩ := spec n hn
    obtain ⟨_, hkm, hval'⟩ := spec m hm
    rw [← heq] at hkm hval'
    rcases lt_trichotomy n m with h | h | h
    · have := column_lt hk (by omega : column n ≤ n) h
      omega
    · exact h
    · have := column_lt hk (by omega : column n ≤ m) h
      omega
  have hbound := Set.ncard_le_ncard_of_injOn column maps inj (Set.finite_Ico 1 t)
  change rows.ncard = t at hcount
  rw [hcount, Set.ncard_Ico_nat] at hbound
  omega

/-- A value occurring in exactly `t` admissible rows is at least the middle of row `2*t`. -/
theorem centralBinom_le_of_row_count {a t : ℕ} (ht : 1 ≤ t)
    (hcount : {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.ncard = t) :
    Nat.centralBinom t ≤ a := by
  obtain ⟨n, k, htk, hkn, rfl⟩ := exists_large_column_of_row_count ht hcount
  exact (Nat.centralBinom_strictMono.monotone htk).trans (Nat.choose_le_choose k hkn)

private theorem half_mono {i j n : ℕ} (hij : i ≤ j) (hjn : 2 * j ≤ n) :
    n.choose i ≤ n.choose j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem prime_le_row {p n k : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hdvd : p ∣ n.choose k) : p ≤ n := by
  by_contra! hn
  exact hp.dvd_iff_not_coprime.mp hdvd (hp.coprime_choose_of_lt hn hkn)

/-- A prime divisor of a candidate of multiplicity `t` gives a second lower bound. -/
theorem prime_choose_le_of_row_count {p a t : ℕ} (ht : 1 ≤ t)
    (hp : p.Prime) (hdvd : p ∣ a)
    (hcount : {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.ncard = t) :
    p.choose t ≤ a := by
  obtain ⟨n, k, htk, hkn, rfl⟩ := exists_large_column_of_row_count ht hcount
  exact (Nat.choose_le_choose t (prime_le_row hp (by omega) hdvd)).trans (half_mono htk hkn)

private theorem lt_choose_two {p : ℕ} (h : 5 ≤ p) : p < p.choose 2 := by
  rw [Nat.choose_two_right]
  have : 4 * p ≤ p * (p - 1) := by
    rw [Nat.mul_comm 4 p]
    exact Nat.mul_le_mul_left p (by omega)
  omega

/-- The prime factor p rules out every interior row smaller than p.
    Every later row has even its second column above the target. -/
theorem prime_triangular_rows {p : ℕ} (hp : p.Prime) (h : 5 ≤ p) :
    {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = p.choose 2} =
      (↑({p, p.choose 2} : Finset ℕ) : Set ℕ) := by
  have hlarge := lt_choose_two h
  have hdvd : p ∣ p.choose 2 := hp.dvd_choose_self (by decide) (by omega)
  ext n
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨k, hk, hkn, heq⟩
    by_cases hk1 : k = 1
    · subst k
      exact Or.inr (by simpa using heq)
    · left
      have hpn : p ≤ n := prime_le_row hp (by omega) (heq ▸ hdvd)
      by_contra! hne
      have hlt := column_lt (k := 2) (by decide) (by omega : 2 ≤ p) (by omega : p < n)
      have hle := half_mono (by omega : 2 ≤ k) hkn
      omega
  · rintro (rfl | rfl)
    · exact ⟨2, by decide, by omega, rfl⟩
    · exact ⟨1, by decide, by omega, by simp⟩

theorem arbitrarily_large_exactly_two (B : ℕ) :
    ∃ a > B, {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.ncard = 2 := by
  obtain ⟨p, hB, hp⟩ := Nat.exists_infinite_primes (max B 5)
  have h : 5 ≤ p := (le_max_right B 5).trans hB
  have hlarge := lt_choose_two h
  refine ⟨p.choose 2, lt_of_le_of_lt ((le_max_left B 5).trans hB) hlarge, ?_⟩
  rw [prime_triangular_rows hp h, Set.ncard_coe_finset]
  simp [ne_of_lt hlarge]

/-- In particular, realizing a large multiplicity requires a value growing exponentially in it. -/
theorem four_pow_lt_mul_of_row_count {a t : ℕ} (ht : 4 ≤ t)
    (hcount : {n : ℕ | ∃ k ≥ 1, 2 * k ≤ n ∧ n.choose k = a}.ncard = t) :
    4 ^ t < t * a :=
  (Nat.four_pow_lt_mul_centralBinom t ht).trans_le
    (Nat.mul_le_mul_left t (centralBinom_le_of_row_count (by omega) hcount))

end Erdos849Bound
