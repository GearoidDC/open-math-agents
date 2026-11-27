import FormalConjectures.ErdosProblems.«889»

/-!
A reduction of the lowercase Erdős 889 finiteness problem. The odd case has
also been settled in the earlier R1 reduction. Here the new restriction on
even solutions comes from factoring an odd power plus one at offset two
and applying the lifting-the-exponent lemma to its odd cofactor.
-/

namespace OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

open Erdos889

open Finset

lemma fresh_iff {n k p : ℕ} (hp : 0 < p) (hd : p ∣ n+k) :
    (∀ i ∈ range k, ¬p ∣ n+i) ↔ k < p := by
  constructor
  · intro h
    by_contra! hle
    have hdiff : n + (k-p) = n+k-p := by omega
    exact h (k-p) (mem_range.mpr (by omega)) (hdiff ▸ Nat.dvd_sub hd (dvd_refl p))
  · intro h i hi hdiv
    have hi' := mem_range.mp hi
    have hsub : n+k-(n+i) = k-i := by omega
    have hd' : p ∣ k-i := hsub ▸ Nat.dvd_sub hd hdiv
    have := Nat.le_of_dvd (by omega : 0 < k-i) hd'
    omega

theorem v_as_card (n k : ℕ) :
    v n k = ((n+k).primeFactors.filter (k < ·)).card := by
  unfold v
  congr 1
  ext p
  simp only [mem_filter]
  exact and_congr_right fun h => fresh_iff (Nat.prime_of_mem_primeFactors h).pos
    (Nat.dvd_of_mem_primeFactors h)

lemma offset_le {n k : ℕ} (hk : 1 ≤ k) :
    (v n k : ℕ∞) ≤ v_l 1 n :=
  le_iSup_of_le k (le_iSup_of_le hk le_rfl)

lemma offset_le_one {n k : ℕ} (h : v_l 1 n = 1) (hk : 1 ≤ k) : v n k ≤ 1 := by
  have hh := offset_le (n := n) hk
  rw [h] at hh
  exact_mod_cast hh

lemma two_primes {n k p q : ℕ} (hk : 0 < k)
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hkp : k < p) (hkq : k < q) (dp : p ∣ n+k) (dq : q ∣ n+k) : v_l 1 n ≠ 1 := by
  intro h
  have hh := offset_le_one h hk
  rw [v_as_card, Finset.card_le_one] at hh
  exact hne (hh p (mem_filter.mpr ⟨hp.mem_primeFactors dp (by omega), hkp⟩)
    q (mem_filter.mpr ⟨hq.mem_primeFactors dq (by omega), hkq⟩))

lemma prime_power_at {n k : ℕ} (h : v_l 1 n = 1) (hk : 0 < k)
    (hn : 2 ≤ n+k) (eligible : ∀ p, p.Prime → p ∣ n+k → k < p) :
    IsPrimePow (n+k) := by
  by_contra bad
  obtain ⟨p, hp, q, hq, hpq⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hn).mp bad
  obtain ⟨pp, dp, _⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨pq, dq, _⟩ := Nat.mem_primeFactors.mp hq
  exact two_primes hk pp pq hpq (eligible p pp dp) (eligible q pq dq) dp dq h

theorem prime_power_succ {n : ℕ} (hn : 0 < n) (h : v_l 1 n = 1) : IsPrimePow (n+1) :=
  prime_power_at h (by decide) (by omega) (fun _ hp _ => hp.one_lt)

lemma square_power_neighbor {y a : ℕ} (hy : 2 ≤ y) (he : y^2 = 2^a+1) :
    a = 3 := by
  have fac : (y-1)*(y+1) = 2^a := by
    have : y-1+1=y := by omega
    nlinarith
  obtain ⟨u, _, hu⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (fac ▸ dvd_mul_right (y-1) (y+1))
  obtain ⟨w, _, hw⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (fac ▸ dvd_mul_left (y+1) (y-1))
  have small : y ≤ 3 := by
    by_contra! large
    have hu2 : 2 ≤ u := by by_contra! z; interval_cases u <;> omega
    have hw2 : 2 ≤ w := by by_contra! z; interval_cases w <;> omega
    have du : 4 ∣ y-1 := hu ▸ (pow_dvd_pow (2 : ℕ) hu2)
    have dw : 4 ∣ y+1 := hw ▸ (pow_dvd_pow (2 : ℕ) hw2)
    omega
  have yy : y = 3 := by
    interval_cases y
    · have h3 : 3 ∣ 2^a := by norm_num at he; exact ⟨1, by omega⟩
      have := Nat.prime_three.dvd_of_dvd_pow h3
      omega
    · rfl
  subst y
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  norm_num at he ⊢
  omega

lemma prime_power_neighbor {a : ℕ} (ha : a ≠ 0) (h : IsPrimePow (2^a+1)) :
    a = 3 ∨ ∃ t : ℕ, a = 2^t := by
  obtain ⟨p, b, pp, hb, he⟩ := (isPrimePow_nat_iff _).mp h
  by_cases even : Even b
  · obtain ⟨j, rfl⟩ := even
    left
    apply square_power_neighbor (y := p^j)
    · have := pp.two_le
      exact Nat.succ_le_of_lt (Nat.one_lt_pow (by omega : j ≠ 0) pp.one_lt)
    · rw [pow_two, ← pow_add, he]
  · have ob := Nat.not_even_iff_odd.mp even
    have op : Odd p := pp.odd_of_ne_two (by
      rintro rfl
      have d₁ := dvd_pow_self (2 : ℕ) ha
      have d₂ := dvd_pow_self (2 : ℕ) hb.ne'
      omega)
    let s := ∑ i ∈ range b, p^i
    have os : Odd s := by
      dsimp [s]
      rw [Finset.odd_sum_iff_odd_card_odd]
      simpa [op.pow] using ob
    have prod : s*(p-1) = 2^a := by
      simpa [s, he] using geom_sum_mul_of_one_le pp.one_le b
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (prod ▸ dvd_mul_right s (p-1))
    have j0 : j = 0 := by
      by_contra bad
      have d := dvd_pow_self (2 : ℕ) bad
      rw [← hj] at d
      obtain ⟨w, hw⟩ := os
      omega
    have s1 : s = 1 := by simp [hj, j0]
    have peq : p = 2^a+1 := by rw [s1, one_mul] at prod; have := pp.two_le; omega
    exact Or.inr (Nat.pow_of_pow_add_prime (by decide) ha (peq ▸ pp))

/-- Six modular orbits rule out every exponent index at least three. -/
lemma orbit {s m r : ℕ} (base : Nat.ModEq m (2^(2^s)) r)
    (step : Nat.ModEq m (r^64) r) (j : ℕ) : Nat.ModEq m (2^(2^(s+6*j))) r := by
  induction j with
  | zero => simpa using base
  | succ j ih =>
    rw [show s+6*(j+1) = (s+6*j)+6 by omega, pow_add, pow_mul]
    exact (ih.pow 64).trans step

lemma orbit_witness {n t s k p q r : ℕ} (hn : n+1 = 2^(2^t))
    (j : ℕ) (ht : t = s+6*j) (hk : 0 < k)
    (pp : p.Prime) (pq : q.Prime) (hne : p ≠ q) (hp : k < p) (hq : k < q)
    (base : Nat.ModEq (p*q) (2^(2^s)) r) (step : Nat.ModEq (p*q) (r^64) r)
    (hit : Nat.ModEq (p*q) (r+(k-1)) 0) : v_l 1 n ≠ 1 := by
  have hh := (orbit base step j).add_right (k-1)
  rw [← ht, ← hn, show n+1+(k-1) = n+k by omega] at hh
  have d := Nat.modEq_zero_iff_dvd.mp (hh.trans hit)
  exact two_primes hk pp pq hne hp hq ((dvd_mul_right p q).trans d) ((dvd_mul_left q p).trans d)

set_option maxRecDepth 8192 in
lemma orbit_excluded {n t : ℕ} (hn : n+1 = 2^(2^t)) (ht : 3 ≤ t) : v_l 1 n ≠ 1 := by
  let j := (t-3)/6
  have cases : t=3+6*j ∨ t=4+6*j ∨ t=5+6*j ∨ t=6+6*j ∨ t=7+6*j ∨ t=8+6*j := by
    dsimp [j]; omega
  rcases cases with h|h|h|h|h|h
  · apply orbit_witness (k:=4) (p:=7) (q:=37) (r:=256) hn j h <;> decide
  · apply orbit_witness (k:=5) (p:=29) (q:=113) (r:=3273) hn j h <;> decide
  · apply orbit_witness (k:=14) (p:=19) (q:=29) (r:=538) hn j h <;> decide
  · apply orbit_witness (k:=6) (p:=7) (q:=29) (r:=198) hn j h <;> decide
  · apply orbit_witness (k:=5) (p:=13) (q:=29) (r:=373) hn j h <;> decide
  · apply orbit_witness (k:=17) (p:=241) (q:=433) (r:=104337) hn j h <;> decide

lemma odd_forward {n : ℕ} (odd : Odd n) (h : v_l 1 n = 1) :
    n = 1 ∨ n = 3 ∨ n = 7 ∨ n = 15 := by
  obtain ⟨w, hw⟩ := odd
  have hp := prime_power_succ (by omega : 0 < n) h
  have h2 : (n+1).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr (by omega)
  obtain ⟨a, ha⟩ : ∃ a : ℕ, n+1 = 2^a := ⟨_, by simpa [h2] using hp.minFac_pow_factorization_eq.symm⟩
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha; omega
  have hnext : IsPrimePow (n+2) := prime_power_at h (by decide) (by omega) (by
    intro p pp dp
    have := pp.two_le
    by_contra! hh
    have : p=2 := by omega
    subst p
    omega)
  rw [show n+2=2^a+1 by omega] at hnext
  rcases prime_power_neighbor ha0 hnext with rfl | ⟨t, rfl⟩
  · norm_num at ha; omega
  · have ht : t < 3 := by by_contra! ht; exact orbit_excluded ha ht h
    interval_cases t <;> norm_num at ha <;> omega

lemma square_bound {n k : ℕ} (hk : 0 < k) (h : 1 < v n k) : k*k < n+k := by
  rw [v_as_card, Finset.one_lt_card_iff_nontrivial] at h
  obtain ⟨p, hp, q, hq, hne⟩ := h
  obtain ⟨pm, pk⟩ := mem_filter.mp hp
  obtain ⟨qm, qk⟩ := mem_filter.mp hq
  obtain ⟨pp, dp, _⟩ := Nat.mem_primeFactors.mp pm
  obtain ⟨pq, dq, _⟩ := Nat.mem_primeFactors.mp qm
  exact (Nat.mul_lt_mul_of_lt_of_le (by omega) (by omega) (by omega)).trans_le
    (Nat.le_of_dvd (by omega) (Nat.Prime.dvd_mul_of_dvd_ne hne pp pq dp dq))

lemma small_solution {n : ℕ} (hn : n ≤ 26) (lo : 1 ≤ v n 1)
    (vals : ∀ k : Fin 7, 0 < k.val → v n k.val ≤ 1) : v_l 1 n = 1 := by
  apply le_antisymm
  · apply iSup_le; intro k; apply iSup_le; intro hk
    have hv : v n k ≤ 1 := by
      by_cases small : k < 7
      · exact vals ⟨k, small⟩ hk
      · by_contra! hh
        have := square_bound hk hh
        nlinarith [show 7 ≤ k by omega, Nat.zero_le ((k-7)*(k-7))]
    exact_mod_cast hv
  · exact (by exact_mod_cast lo : (1 : ℕ∞) ≤ (v n 1 : ℕ∞)).trans (offset_le (by decide))

theorem odd_classification {n : ℕ} (h : Odd n) :
    v_l 1 n = 1 ↔ n = 1 ∨ n = 3 ∨ n = 7 ∨ n = 15 := by
  refine ⟨odd_forward h, ?_⟩
  rintro (rfl|rfl|rfl|rfl) <;> apply small_solution <;> decide +kernel


/-- If a solution is one less than an odd cube, its cube root is one
less than a power of two. -/
theorem cube_root_neighbor {n u : ℕ} (hu : Odd u) (large : 1 < u)
    (hn : n+1 = u^3) (h : v_l 1 n = 1) : ∃ b : ℕ, u+1 = 2^b := by
  obtain ⟨w, hw⟩ := hu
  have wpos : 0 < w := by omega
  let y := 4*w^2 + 2*w + 1
  have ybig : 3 < y := by dsimp [y]; nlinarith [Nat.mul_self_le_mul_self wpos]
  have yodd : y = 2*(2*w^2+w)+1 := by dsimp [y]; ring
  have no9 : ¬9 ∣ y := by
    change ¬9 ∣ 4*w^2+2*w+1
    rw [Nat.dvd_iff_mod_eq_zero]
    have z := Nat.mod_lt w (by decide : 0 < 9)
    have reduce : (4*w^2+2*w+1)%9 = (4*(w%9)^2+2*(w%9)+1)%9 := by
      have m := (Nat.mod_modEq w 9).symm
      exact (((m.pow 2).mul_left 4).add (m.mul_left 2)).add_right 1
    rw [reduce]
    interval_cases hmod : w%9 <;> decide
  have other : ∃ q : ℕ, q.Prime ∧ q ∣ y ∧ q ≠ 3 := by
    by_contra! none
    have eq := Nat.eq_prime_pow_of_unique_prime_dvd (n := y) (p := 3) (by omega)
      (fun {q} => none q)
    let e := y.primeFactorsList.length
    change y = 3^e at eq
    have e2 : 2 ≤ e := by
      by_contra! small
      interval_cases e <;> simp_all
    exact no9 (eq ▸ pow_dvd_pow (3 : ℕ) e2)
  obtain ⟨q, pq, dy, q3⟩ := other
  have qbig : 2 < q := by
    have := pq.two_le
    by_contra! small
    have eq : q=2 := by omega
    rw [eq, yodd] at dy
    omega
  have fac : n+2 = (u+1)*y := by
    rw [hw] at hn ⊢
    dsimp [y]
    nlinarith
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
  intro p pp dp
  by_contra p2
  have pbig := lt_of_le_of_ne pp.two_le (Ne.symm p2)
  have neq : p ≠ q := by
    rintro rfl
    have eq : y + 3*(u+1) = (u+1)^2+3 := by dsimp [y]; rw [hw]; ring
    have dl := dvd_add dy (dvd_mul_of_dvd_right dp 3)
    rw [eq] at dl
    have ds : p ∣ (u+1)^2 := dp.trans (dvd_pow_self _ (by decide : 2 ≠ 0))
    exact q3 ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_three).mp ((Nat.dvd_add_iff_right ds).mpr dl))
  apply two_primes (k := 2) (by decide) pp pq neq pbig qbig _ _ h
  · rw [fac]; exact dvd_mul_of_dvd_left dp _
  · rw [fac]; exact dvd_mul_of_dvd_right dy _


/-- Reduce an exponent modulo a verified multiplicative period. -/
lemma pow_cycle {a d m : ℕ} (period : Nat.ModEq m (a^d) 1) (j : ℕ) :
    Nat.ModEq m (a^j) (a^(j%d)) := by
  calc
    a^j = a^(j%d) * (a^d)^(j/d) := by rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    _ ≡ a^(j%d) * 1^(j/d) [MOD m] := (period.pow _).mul_left _
    _ = _ := by simp

lemma small_prime {p : ℕ} (hp : p.Prime) (le : p ≤ 9) :
    p=2 ∨ p=3 ∨ p=5 ∨ p=7 := by
  interval_cases p <;> norm_num at *

lemma large_factor {m p : ℕ} (hm : 0 < m)
    (small : ∀ q : ℕ, q.Prime → q ∣ m → q ≤ 9 → q=p)
    (exclude : ∀ e : ℕ, m ≠ p^e) : ∃ q : ℕ, q.Prime ∧ 9 < q ∧ q ∣ m := by
  by_contra! none
  exact exclude _ (Nat.eq_prime_pow_of_unique_prime_dvd hm.ne'
    (fun {q} hq dq => small q hq dq (by by_contra! z; exact none q hq z dq)))

lemma seven_pow_mod_eight (b : ℕ) : 7^b%8=1 ∨ 7^b%8=7 := by
  have h := pow_cycle (a:=7) (d:=2) (m:=8) (by decide) b
  change 7^b%8 = 7^(b%2)%8 at h
  have bound := Nat.mod_lt b (by decide : 0<2)
  interval_cases z : b%2 <;> simp_all

lemma three_pow_mod_eight (b : ℕ) : 3^b%8=1 ∨ 3^b%8=3 := by
  have h := pow_cycle (a:=3) (d:=2) (m:=8) (by decide) b
  change 3^b%8 = 3^(b%2)%8 at h
  have bound := Nat.mod_lt b (by decide : 0<2)
  interval_cases z : b%2 <;> simp_all

lemma odd_index_offsets {j : ℕ} (hj : Odd j) :
    2^j%3=2 ∧ ¬5 ∣ 2^j+1 ∧ ¬7 ∣ 2^j+1 := by
  have h3 := pow_cycle (a:=2) (d:=2) (m:=3) (by decide) j
  have h5 := pow_cycle (a:=2) (d:=4) (m:=5) (by decide) j
  have h7 := pow_cycle (a:=2) (d:=3) (m:=7) (by decide) j
  change 2^j%3=2^(j%2)%3 at h3
  change 2^j%5=2^(j%4)%5 at h5
  change 2^j%7=2^(j%3)%7 at h7
  obtain ⟨w, hw⟩ := hj
  have odd : j%2=1 := by omega
  rw [odd] at h3
  refine ⟨h3, ?_, ?_⟩
  · have cases : j%4=1 ∨ j%4=3 := by omega
    rcases cases with e|e <;> rw [e] at h5 <;> norm_num at h5 <;> omega
  · have bound := Nat.mod_lt j (by decide : 0<3)
    interval_cases e : j%3 <;> norm_num at h7 <;> omega

/-- Offset nine supplies two large primes when the cube root is
one less than two to an odd exponent of at least five. -/
lemma cube_offset_nine {n u j : ℕ} (hn : n+1=u^3) (hu : u+1=2^j)
    (hj : 5 ≤ j) (oj : Odd j) : v_l 1 n ≠ 1 := by
  obtain ⟨m3, m5, m7⟩ := odd_index_offsets oj
  have d8 : 8 ∣ 2^j := pow_dvd_pow (2 : ℕ) (by omega : 3 ≤ j)
  have u8 : u%8=7 := by omega
  obtain ⟨p, pp, pbig, dp⟩ : ∃ p : ℕ, p.Prime ∧ 9 < p ∧ p ∣ u+2 := by
    apply large_factor (p:=3) (by omega)
    · intro q pq dq lq
      rcases small_prime pq lq with rfl|rfl|rfl|rfl <;> omega
    · intro e eq
      have epos : 0 < e := by
        by_contra! z
        have e0 : e=0 := by omega
        rw [e0, pow_zero] at eq
        omega
      have hprime : IsPrimePow (2^j+1) := (isPrimePow_nat_iff _).mpr
        ⟨3, e, Nat.prime_three, epos, by omega⟩
      rcases prime_power_neighbor (by omega) hprime with z|⟨t, ht⟩
      · omega
      · by_cases t0 : t=0
        · simp [t0] at ht; omega
        · have d2 := dvd_pow_self (2 : ℕ) t0
          obtain ⟨w, hw⟩ := oj
          omega
  let z := (u-1)/3
  have uz : u=3*z+1 := by dsimp [z]; omega
  let y := 3*z^2+1
  have z8 : z%8=2 := by omega
  have y8 : y%8=5 := by
    have m : Nat.ModEq 8 z 2 := z8
    exact ((m.pow 2).mul_left 3).add_right 1
  have no5 : ¬5 ∣ y := by
    have m := (Nat.mod_modEq z 5).symm
    have v := ((m.pow 2).mul_left 3).add_right 1
    change y%5 = (3*(z%5)^2+1)%5 at v
    have bound := Nat.mod_lt z (by decide : 0<5)
    interval_cases e : z%5 <;> norm_num at v <;> omega
  obtain ⟨q, pq, qbig, dq⟩ : ∃ q : ℕ, q.Prime ∧ 9 < q ∧ q ∣ y := by
    apply large_factor (p:=7) (by dsimp [y]; omega)
    · intro q pq dq lq
      have y3 : y%3=1 := by simp [y]
      rcases small_prime pq lq with rfl|rfl|rfl|rfl <;> omega
    · intro e eq
      have := seven_pow_mod_eight e
      omega
  have neq : p ≠ q := by
    rintro rfl
    have eq : 3*y+6*(u+2)=(u+2)^2+12 := by dsimp [y]; rw [uz]; ring
    have dl := dvd_add (dvd_mul_of_dvd_right dq 3) (dvd_mul_of_dvd_right dp 6)
    rw [eq] at dl
    have ds := dp.trans (dvd_pow_self (u+2) (by decide : 2 ≠ 0))
    have d12 := (Nat.dvd_add_iff_right ds).mpr dl
    have := Nat.le_of_dvd (by decide : 0<12) d12
    interval_cases p <;> norm_num at *
  have fac : n+9 = (u+2)*(3*y) := by dsimp [y]; rw [uz] at hn ⊢; nlinarith
  apply two_primes (k:=9) (by decide) pp pq neq pbig qbig
  · rw [fac]; exact dvd_mul_of_dvd_left dp _
  · rw [fac]; exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right dq _) _

/-- The only solution immediately below an odd cube greater than one is 26. -/
theorem cube_classification {n u : ℕ} (hu : Odd u) (large : 1 < u) (hn : n+1=u^3) :
    v_l 1 n = 1 ↔ n=26 := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := cube_root_neighbor hu large hn h
    by_cases small : j < 4
    · interval_cases j
      · norm_num at hj
        omega
      · norm_num at hj
        omega
      · have u3 : u=3 := by norm_num at hj; omega
        norm_num [u3] at hn
        omega
      · have u7 : u=7 := by norm_num at hj; omega
        have n342 : n=342 := by norm_num [u7] at hn; omega
        subst n
        exact False.elim (two_primes (n:=342) (k:=3) (p:=5) (q:=23)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) h)
    · have d8 : 8 ∣ 2^j := pow_dvd_pow (2 : ℕ) (by omega : 3 ≤ j)
      by_cases oj : Odd j
      · have j5 : 5≤j := by obtain ⟨w, hw⟩ := oj; omega
        exact False.elim (cube_offset_nine hn hj j5 oj h)
      · have j2 : j%2=0 := by rw [Nat.odd_iff] at oj; omega
        have m := pow_cycle (a:=2) (d:=2) (m:=3) (by decide) j
        change 2^j%3=2^(j%2)%3 at m
        rw [j2] at m
        norm_num at m
        have du : 3 ∣ u := by omega
        have nl : 0 < n := by have := Nat.one_lt_pow (by decide : 3 ≠ 0) large; omega
        have hp := prime_power_succ nl h
        rw [hn, isPrimePow_pow_iff (by decide : 3 ≠ 0)] at hp
        obtain ⟨p, e, pp, _, he⟩ := (isPrimePow_nat_iff _).mp hp
        have d : 3 ∣ p^e := he ▸ du
        have p3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp (Nat.prime_three.dvd_of_dvd_pow d)
        rw [← p3] at he
        have := three_pow_mod_eight e
        omega
  · rintro rfl
    apply small_solution <;> decide +kernel

/-- Apart from 26, a positive even solution must precede an odd prime
power whose exponent is not divisible by three. -/
theorem even_solution_shape {n : ℕ} (hn : 0 < n) (ev : Even n) (h26 : n ≠ 26)
    (h : v_l 1 n = 1) :
    ∃ p a : ℕ, p.Prime ∧ Odd p ∧ 0 < a ∧ ¬3 ∣ a ∧ n+1 = p^a := by
  obtain ⟨p, a, pp, ha, he⟩ := (isPrimePow_nat_iff _).mp (prime_power_succ hn h)
  have op : Odd p := pp.odd_of_ne_two (by
    rintro rfl
    have d := dvd_pow_self (2 : ℕ) ha.ne'
    rw [he] at d
    obtain ⟨w, hw⟩ := ev
    omega)
  refine ⟨p, a, pp, op, ha, ?_, he.symm⟩
  rintro ⟨b, rfl⟩
  have bpos : b ≠ 0 := by omega
  have cube : n+1=(p^b)^3 := by rw [← he, ← pow_mul, Nat.mul_comm]
  exact h26 ((cube_classification op.pow (Nat.one_lt_pow bpos pp.one_lt) cube).mp h)

/-- The cofactor of x+1 in an odd power plus one is odd and grows
faster than the exponent for every odd x greater than one. -/
lemma odd_cofactor {x r : ℕ} (ox : Odd x) (hx : 1 < x) (orr : Odd r) (hr : 1 < r) :
    ∃ c : ℕ, Odd c ∧ r < c ∧ x^r+1 = (x+1)*c := by
  obtain ⟨w, hw⟩ := ox
  obtain ⟨j, rfl⟩ := orr
  have wp : 0 < w := by omega
  have hx3 : 3 ≤ x := by omega
  have aux (i : ℕ) : ∃ z : ℕ, 2*i ≤ z ∧ x^(2*i+1)+1 = (x+1)*(2*z+1) := by
    induction i with
    | zero => exact ⟨0, by decide, by simp⟩
    | succ i ih =>
      obtain ⟨z, hz, he⟩ := ih
      refine ⟨x^2*z+w*x, ?_, ?_⟩
      · have mulz : z ≤ x^2*z := by
          simpa using Nat.mul_le_mul_right z (show 1 ≤ x^2 by exact Nat.one_le_pow _ _ (by omega))
        have mulw : 3 ≤ w*x := by simpa using Nat.mul_le_mul wp hx3
        omega
      · rw [show 2*(i+1)+1 = (2*i+1)+2 by omega, pow_add]
        have scaled := congrArg (fun m : ℕ => m*x^2) he
        rw [hw] at scaled ⊢
        nlinarith only [scaled]
  obtain ⟨z, hz, he⟩ := aux j
  exact ⟨2*z+1, ⟨z,rfl⟩, by omega, he⟩

/-- When an even solution precedes a nontrivial odd power, the base
of that power is one less than a power of two. -/
theorem odd_power_root_neighbor {n x r : ℕ} (ox : Odd x) (hx : 1 < x)
    (orr : Odd r) (hr : 1 < r) (hn : n+1=x^r) (h : v_l 1 n=1) :
    ∃ b : ℕ, x+1=2^b := by
  obtain ⟨c, oc, hc, fac⟩ := odd_cofactor ox hx orr hr
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
  intro p pp dp
  by_contra p2
  have pbig := lt_of_le_of_ne pp.two_le (Ne.symm p2)
  have fac' : n+2=(x+1)*c := by omega
  have pure : c=p^c.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
    intro q pq dq
    by_contra different
    have qbig : 2 < q := by
      have := pq.two_le
      obtain ⟨w, hw⟩ := oc
      by_contra! z
      have q2 : q=2 := by omega
      rw [q2] at dq
      omega
    apply two_primes (k:=2) (by decide) pq pp different qbig pbig _ _ h
    · rw [fac']; exact dvd_mul_of_dvd_right dq _
    · rw [fac']; exact dvd_mul_of_dvd_left dp _)
  let _ : Fact p.Prime := ⟨pp⟩
  have nd : ¬p ∣ x := by
    intro d
    have d1 := (Nat.dvd_add_iff_right d).mpr dp
    have := Nat.le_of_dvd Nat.one_pos d1
    omega
  have v := padicValNat.pow_add_pow (x:=x) (y:=1) (pp.odd_of_ne_two p2) dp nd orr
  rw [one_pow, fac, padicValNat.mul (by omega) (by omega)] at v
  have eq : padicValNat p c = padicValNat p r := by omega
  have power : p^(padicValNat p c) = c := by
    conv_lhs => arg 2; rw [pure, padicValNat.prime_pow]
    exact pure.symm
  have cd : c ∣ r := by rw [← power, eq]; exact pow_padicValNat_dvd
  exact (Nat.not_le_of_gt hc) (Nat.le_of_dvd (by omega) cd)

lemma mersenne_power_exponent {p s b : ℕ} (op : Odd p) (hp : 1 < p)
    (hs : 0 < s) (eq : p^s+1=2^b) : s=1 := by
  by_contra bad
  rcases Nat.even_or_odd s with ⟨j, hj⟩|os
  · have hjp : j ≠ 0 := by omega
    have ob : Odd (p^j) := op.pow
    obtain ⟨w, hw⟩ := ob
    have large := Nat.one_lt_pow hjp hp
    have q : p^s = (2*w+1)^2 := by rw [hj, pow_add, hw, pow_two]
    have b2 : 2 ≤ b := by
      by_contra! z
      interval_cases b <;> norm_num at eq <;> have := Nat.one_lt_pow hs.ne' hp <;> omega
    have d4 : 4 ∣ 2^b := pow_dvd_pow (2 : ℕ) b2
    have sq : (2*w+1)^2+1 = 4*(w^2+w)+2 := by ring
    omega
  · obtain ⟨c, oc, hc, f⟩ := odd_cofactor op hp os (by omega)
    have dc : c ∣ 2^b := (f.symm.trans eq) ▸ dvd_mul_left c (p+1)
    obtain ⟨t, _, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp dc
    have tpos : t ≠ 0 := by rintro rfl; simp at ht; omega
    have d := dvd_pow_self (2 : ℕ) tpos
    rw [← ht] at d
    obtain ⟨w, hw⟩ := oc
    omega

/-- Every odd prime divisor of the successor exponent must be the entire
exponent. In that case the prime base is a Mersenne prime. -/
theorem successor_exponent {n p a : ℕ} (pp : p.Prime) (op : Odd p) (ha : 0<a)
    (hn : n+1=p^a) (h : v_l 1 n=1) :
    (∃ t : ℕ, a=2^t) ∨ (a.Prime ∧ Odd a ∧ ∃ b : ℕ, p+1=2^b) := by
  by_cases ex : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ a
  · obtain ⟨r, pr, r2, s, hs⟩ := ex
    have spos : 0 < s := by
      by_contra! z
      have s0 : s=0 := by omega
      rw [s0, Nat.mul_zero] at hs
      omega
    have hx : n+1 = (p^s)^r := by rw [hn, hs, ← pow_mul, Nat.mul_comm]
    obtain ⟨b, hb⟩ := odd_power_root_neighbor op.pow (Nat.one_lt_pow spos.ne' pp.one_lt)
      (pr.odd_of_ne_two r2) pr.one_lt hx h
    have one := mersenne_power_exponent op pp.one_lt spos hb
    rw [one, mul_one] at hs
    exact Or.inr ⟨hs ▸ pr, hs ▸ pr.odd_of_ne_two r2, b, by simpa [one] using hb⟩
  · left
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd ha.ne' ?_⟩
    intro r pr dr
    by_contra nr
    exact ex ⟨r, pr, nr, dr⟩

/-- At every sufficiently large odd prime, find a later or equal integer
with two distinct prime factors larger than the offset from its predecessor. -/
def H1 : Prop := ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B < p →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p+d ∧ s ∣ p+d

/-- The same witness question for proper powers with dyadic exponent. -/
def H2 : Prop := ∃ B : ℕ, ∀ p t : ℕ, p.Prime → Odd p → 0 < t → B < p^(2^t) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^(2^t)+d ∧ s ∣ p^(2^t)+d

/-- The remaining odd exponents are primes at least five, and the only
bases that need be considered are Mersenne primes. -/
def H3 : Prop := ∃ B : ℕ, ∀ p r : ℕ, p.Prime → Odd p → (∃ b : ℕ, p+1=2^b) →
    r.Prime → 5 ≤ r → B < p^r →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^r+d ∧ s ∣ p^r+d

theorem main : H1 → H2 → H3 → type_of% @Erdos889.erdos_889.variants.v1_eq_1_finite := by
  rintro ⟨A, primeCase⟩ ⟨B, dyadicCase⟩ ⟨C, mersenneCase⟩
  refine (Set.finite_le_nat (A+B+C+26)).subset ?_
  intro n hn
  change v_l 1 n = 1 at hn
  change n ≤ A+B+C+26
  by_contra! big
  rcases Nat.even_or_odd n with ev|od
  · obtain ⟨p, a, pp, op, apos, no3, he⟩ := even_solution_shape (by omega) ev (by omega) hn
    have witness : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
        q ∣ p^a+d ∧ s ∣ p^a+d := by
      rcases successor_exponent pp op apos he hn with ⟨t, ht⟩ | ⟨pr, oa, base⟩
      · subst a
        cases t with
        | zero =>
          simp only [pow_zero, pow_one] at he ⊢
          exact primeCase p pp op (by omega)
        | succ t => exact dyadicCase p (t+1) pp op (by omega) (by omega)
      · have a5 : 5 ≤ a := by
          obtain ⟨w, hw⟩ := oa
          have := pr.two_le
          omega
        exact mersenneCase p a pp op base pr a5 (by omega)
    obtain ⟨d,q,s,pq,ps,ne,hq,hs,dq,ds⟩ := witness
    have equal : n+(d+1)=p^a+d := by omega
    exact two_primes (k:=d+1) (by omega) pq ps ne hq hs (equal ▸ dq) (equal ▸ ds) hn
  · rcases (odd_classification od).mp hn with h|h|h|h <;> omega

end OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

