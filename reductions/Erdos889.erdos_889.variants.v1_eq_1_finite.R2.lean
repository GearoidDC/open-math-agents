import FormalConjectures.ErdosProblems.«889»

/-!
A reduction of the lowercase Erdős 889 finiteness problem. The odd case has
also been settled in the earlier R1 reduction. Here the new restriction on
even solutions comes from factoring an odd power plus one at offset two
and applying the lifting-the-exponent lemma to its odd cofactor. Fourth powers
and prime squares admit additional restrictions by elementary Pell descents
and quadratic reciprocity. The final steps also use factorizations in the
Eisenstein integers, modular certificates, and classifications of higher powers.
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

lemma pell_divisibility {x y : ℕ} (he : x^2+1=5*y^2) (hd : 5 ∣ y) : 61 ∣ y := by
  let states : List (ℕ × ℕ) := [(2,1),(38,17),(72,0),(38,288),(2,304),
    (303,304),(267,288),(233,0),(267,17),(303,1)]
  have closed : ∀ z ∈ states, ((9*z.1+20*z.2)%305,(4*z.1+9*z.2)%305) ∈ states := by
    decide +kernel
  have sieve : ∀ z ∈ states, 5 ∣ z.2 → 61 ∣ z.2 := by decide +kernel
  have orbit (b a : ℕ) (eqn : a^2+1=5*b^2) : (a%305,b%305) ∈ states := by
    induction b using Nat.strong_induction_on generalizing a with
    | h b ih =>
      by_cases small : b < 5
      · have ab : a ≤ 8 := by nlinarith [Nat.mul_self_le_mul_self (show b ≤ 4 by omega)]
        interval_cases b <;> interval_cases a <;> norm_num at eqn
        all_goals decide +kernel
      · have lb : 5 ≤ b := by omega
        have low : 20*b ≤ 9*a := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad.le, Nat.mul_self_le_mul_self lb]
        have high : 4*a ≤ 9*b := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad.le, Nat.zero_le (b*b)]
        have strict : 2*b < a := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad, Nat.mul_self_le_mul_self lb]
        let u := 9*a-20*b
        let v := 9*b-4*a
        have eu : u+20*b=9*a := Nat.sub_add_cancel low
        have ev : v+4*a=9*b := Nat.sub_add_cancel high
        have evsmall : v<b := by omega
        have norm : u^2+1=5*v^2 := by
          have az : (a:ℤ)^2+1=5*(b:ℤ)^2 := by exact_mod_cast eqn
          have uz : (u:ℤ)=9*(a:ℤ)-20*(b:ℤ) := by dsimp [u]; push_cast [Nat.cast_sub low]; ring
          have vz : (v:ℤ)=9*(b:ℤ)-4*(a:ℤ) := by dsimp [v]; push_cast [Nat.cast_sub high]; ring
          have nz : (u:ℤ)^2+1=5*(v:ℤ)^2 := by rw [uz,vz]; linear_combination az
          exact_mod_cast nz
        have prev := closed _ (ih v evsmall u norm)
        have m := (Nat.mod_modEq u 305).symm
        have n := (Nat.mod_modEq v 305).symm
        have ax := (m.mul_left 9).add (n.mul_left 20)
        have by' := (m.mul_left 4).add (n.mul_left 9)
        change (9*u+20*v)%305=_ at ax
        change (4*u+9*v)%305=_ at by'
        rwa [show a=9*u+20*v by omega, show b=4*u+9*v by omega, ax, by']
  have d5 : 5 ∣ y%305 := by omega
  have d61 := sieve (x%305,y%305) (orbit y x he) d5
  change 61 ∣ y%305 at d61
  omega

/-- The only possible positive square root of a power of five minus one is two. -/
theorem square_plus_one_five {z e : ℕ} (h : z^2+1=5^e) : z ≤ 2 := by
  rcases Nat.even_or_odd e with ⟨b, rfl⟩|⟨b, rfl⟩
  · have eq : z^2+1=(5^b)^2 := by simpa [pow_add,pow_two] using h
    by_contra! big
    by_cases le : 5^b ≤ z
    · nlinarith [Nat.mul_self_le_mul_self le]
    · have l : z+1 ≤ 5^b := by omega
      nlinarith [Nat.mul_self_le_mul_self l]
  · have eq : z^2+1=5*(5^b)^2 := by
      rw [h, pow_succ, mul_comm 2 b, pow_mul, mul_comm]
    by_cases b0 : b=0
    · simp [b0] at eq
      nlinarith
    · have d := pell_divisibility eq (dvd_pow_self (5:ℕ) b0)
      have pr : Nat.Prime 61 := by decide
      have bad := pr.dvd_of_dvd_pow d
      omega

lemma large_prime_of_square {u : ℕ} (ev : Even u) (hu : 2<u) :
    ∃ p : ℕ, p.Prime ∧ 5<p ∧ p ∣ u^2+1 := by
  by_contra! none
  have no3 : ¬3 ∣ u^2+1 := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow_two, Nat.mul_mod]
    have bound := Nat.mod_lt u (by decide : 0<3)
    interval_cases r : u%3 <;> decide
  obtain ⟨w, hw⟩ := ev
  have no2 : ¬2 ∣ u^2+1 := by
    have form : u^2+1 = 2*(2*w^2)+1 := by rw [hw]; ring
    omega
  have pure : u^2+1 = 5^(u^2+1).primeFactorsList.length := by
    apply Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
    intro p pp dp
    have le : p≤5 := by by_contra! big; exact none p pp big dp
    have choices : p=2 ∨ p=3 ∨ p=5 := by interval_cases p <;> norm_num at *
    rcases choices with rfl|rfl|rfl
    · exact False.elim (no2 dp)
    · exact False.elim (no3 dp)
    · rfl
  exact (Nat.not_le_of_gt hu) (square_plus_one_five pure)

/-- At offset five, the two Sophie Germain factors each supply a prime
above five, for every odd fourth root greater than three. -/
theorem fourth_power_witness {x : ℕ} (ox : Odd x) (hx : 3<x) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ 5<p ∧ 5<q ∧ p ∣ x^4+4 ∧ q ∣ x^4+4 := by
  obtain ⟨w, hw⟩ := ox
  let L := (2*w)^2+1
  let R := (2*w+2)^2+1
  obtain ⟨p, pp, pbig, dp⟩ := large_prime_of_square (u:=2*w) ⟨w,by omega⟩ (by omega)
  obtain ⟨q, pq, qbig, dq⟩ := large_prime_of_square (u:=2*w+2) ⟨w+1,by omega⟩ (by omega)
  change p ∣ L at dp
  change q ∣ R at dq
  have fac : x^4+4=L*R := by dsimp [L,R]; rw [hw]; ring
  refine ⟨p,q,pp,pq,?_,pbig,qbig,fac ▸ dvd_mul_of_dvd_left dp _,fac ▸ dvd_mul_of_dvd_right dq _⟩
  rintro rfl
  have diff : R=L+4*x := by dsimp [L,R]; rw [hw]; ring
  rw [diff] at dq
  have d4x := (Nat.dvd_add_iff_right dp).mpr dq
  have dx : p ∣ x := pp.dvd_mul.mp d4x |>.resolve_left (by
    intro d
    have := Nat.le_of_dvd (by decide : 0<4) d
    omega)
  have eq : L+2*x=x^2+2 := by dsimp [L]; rw [hw]; ring
  have dl := dvd_add dp (dvd_mul_of_dvd_right dx 2)
  rw [eq] at dl
  have ds : p ∣ x^2 := dx.trans (dvd_pow_self x (by decide : 2≠0))
  have bad := (Nat.dvd_add_iff_right ds).mpr dl
  have := Nat.le_of_dvd (by decide : 0<2) bad
  omega

/-- A uniform witness for successors that are prime squares suffices for
all proper powers of odd primes with power-of-two exponent. -/
theorem dyadic_of_prime_squares
    (squares : ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B < p^2 →
      ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
        q ∣ p^2+d ∧ s ∣ p^2+d) :
    ∃ B : ℕ, ∀ p t : ℕ, p.Prime → Odd p → 0<t → B < p^(2^t) →
      ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
        q ∣ p^(2^t)+d ∧ s ∣ p^(2^t)+d := by
  obtain ⟨B, hB⟩ := squares
  refine ⟨B+81, ?_⟩
  intro p t pp op ht big
  cases t with
  | zero => omega
  | succ j =>
    cases j with
    | zero =>
      change B+81 < p^2 at big
      exact hB p pp op (by omega)
    | succ j =>
      let x := p^(2^j)
      have eq : p^(2^(j+1+1))=x^4 := by
        dsimp [x]
        rw [← pow_mul, show j+1+1=j+2 by omega, pow_add]
        rfl
      rw [eq] at big ⊢
      have xbig : 3<x := by
        by_contra! small
        have bound := Nat.pow_le_pow_left small 4
        norm_num at bound
        omega
      obtain ⟨q,s,pq,ps,ne,hq,hs,dq,ds⟩ := fourth_power_witness (x:=x) op.pow xbig
      exact ⟨4,q,s,pq,ps,ne,hq,hs,dq,ds⟩

private theorem cofactor_power {N d m : ℕ} (hm : 2 ≤ m) (dm : m ∣ N+d)
    (eligible : ∀ q : ℕ, q.Prime → q ∣ m → d+1<q)
    (nohit : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ N+d ∧ s ∣ N+d) : IsPrimePow m := by
  by_contra bad
  obtain ⟨q, hq, s, hs, ne⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hm).mp bad
  obtain ⟨pq,dq,_⟩ := Nat.mem_primeFactors.mp hq
  obtain ⟨ps,ds,_⟩ := Nat.mem_primeFactors.mp hs
  exact nohit ⟨d,q,s,pq,ps,ne,eligible q pq dq,eligible s ps ds,dq.trans dm,ds.trans dm⟩

private theorem square_mod_three {x : ℕ} (h : ¬3 ∣ x) : x^2%3=1 := by
  have b := Nat.mod_lt x (by decide : 0<3)
  rw [pow_two, Nat.mul_mod]
  interval_cases e : x%3 <;> first | decide | omega

private theorem odd_power_mod_three {x b : ℕ} (ob : Odd b) (h : ¬3 ∣ x) :
    x^b%3 = x%3 := by
  obtain ⟨j,hj⟩ := ob
  have one : Nat.ModEq 3 (x^2) 1 := square_mod_three h
  have m := (one.pow j).mul_right x
  change Nat.ModEq 3 (x^b) x
  rw [hj, pow_succ, pow_mul]
  simpa only [one_pow, one_mul] using m

/-- Offsets 2 and 4 force simultaneous prime powers. Offset 10 removes
every multiple of four from the exponent of the first cofactor. -/
theorem square_survivor {p : ℕ} (pp : p.Prime) (op : Odd p) (hp : 3<p)
    (nohit : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^2+d ∧ s ∣ p^2+d) :
    ∃ q r a b : ℕ, q.Prime ∧ r.Prime ∧ q≠r ∧ q%4=1 ∧ r%3=1 ∧
      0<a ∧ ¬4 ∣ a ∧ 0<b ∧ Odd b ∧ p^2+1=2*q^a ∧ p^2+3=4*r^b := by
  obtain ⟨w,hw⟩ := op
  let A := 2*w*(w+1)+1
  let B := w*(w+1)+1
  have hA : p^2+1=2*A := by dsimp [A]; rw [hw]; ring
  have hB : p^2+3=4*B := by dsimp [B]; rw [hw]; ring
  have abig : 2≤A := by nlinarith [Nat.mul_self_le_mul_self hp.le]
  have bbig : 2≤B := by nlinarith [Nat.mul_self_le_mul_self hp.le]
  have aodd : ¬2 ∣ A := by
    have e : A=2*(w*(w+1))+1 := by dsimp [A]; ring
    omega
  have bodd : ¬2 ∣ B := by
    rcases Nat.even_or_odd w with ⟨i,hi⟩|⟨i,hi⟩
    · have e : B=2*(i*(w+1))+1 := by dsimp [B]; rw [hi]; ring
      omega
    · have e : B=2*(w*(i+1))+1 := by dsimp [B]; rw [hi]; ring
      omega
  have p3 : ¬3 ∣ p := by
    intro d
    have e := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp d
    omega
  have pmod := square_mod_three p3
  have modB : B%3=1 := by omega
  have pureA : IsPrimePow A := cofactor_power (d:=1) abig (hA ▸ dvd_mul_left A 2) (by
    intro q pq dq
    have := pq.two_le
    by_contra! bad
    have eq : q=2 := by omega
    exact aodd (eq ▸ dq)) nohit
  have pureB : IsPrimePow B := cofactor_power (d:=3) bbig (hB ▸ dvd_mul_left B 4) (by
    intro q pq dq
    by_contra! bad
    have e : q=2 ∨ q=3 := by interval_cases q <;> norm_num at *
    rcases e with rfl|rfl
    · exact bodd dq
    · omega) nohit
  obtain ⟨q,a,pq,apos,eqA⟩ := (isPrimePow_nat_iff _).mp pureA
  obtain ⟨r,b,pr,bpos,eqB⟩ := (isPrimePow_nat_iff _).mp pureB
  have dq : q ∣ A := eqA ▸ dvd_pow_self q apos.ne'
  have dr : r ∣ B := eqB ▸ dvd_pow_self r bpos.ne'
  have q2 : q ≠ 2 := by rintro rfl; exact aodd dq
  have qs : q ∣ p^2+1 := hA ▸ dvd_mul_of_dvd_right dq 2
  obtain ⟨j,hj⟩ := Nat.pow_pow_add_primeFactors_one_lt (a:=p) (n:=1) pq q2 (by simpa using qs)
  norm_num at hj
  have q4 : q%4=1 := by omega
  have qbig : 3<q := by have := pq.two_le; omega
  have ne : q ≠ r := by
    rintro rfl
    have d := hB ▸ (dvd_mul_of_dvd_right dr 4 : q ∣ 4*B)
    have dd := Nat.dvd_sub d qs
    have e : p^2+3-(p^2+1)=2 := by omega
    rw [e] at dd
    have := Nat.le_of_dvd (by decide) dd
    omega
  have ob : Odd b := by
    apply Nat.not_even_iff_odd.mp
    rintro ⟨i,hi⟩
    have sq : p^2+3=(2*r^i)^2 := by rw [hB, ← eqB, hi, pow_add]; ring
    by_cases le : 2*r^i ≤ p
    · nlinarith [Nat.mul_self_le_mul_self le]
    · nlinarith [Nat.mul_self_le_mul_self (show p+1 ≤ 2*r^i by omega)]
  have r3 : ¬3 ∣ r := by intro d; have dB := d.trans dr; omega
  have rmod := odd_power_mod_three ob r3
  have no4 : ¬4 ∣ a := by
    rintro ⟨i,hi⟩
    have ip : 0 < i := by omega
    let x := q^i
    have xb : 3<x := (lt_of_lt_of_le qbig (Nat.le_self_pow ip.ne' q))
    have ox : Odd x := (pq.odd_of_ne_two q2).pow
    have f : p^2+9=2*(x^4+4) := by
      have aa : A=x^4 := by dsimp [x]; rw [←eqA, hi, ←pow_mul, Nat.mul_comm]
      omega
    obtain ⟨l,s,pl,ps,nls,hl,hs,dl,ds⟩ := fourth_power_witness ox xb
    have no7 : ¬7 ∣ x^4+4 := by
      have mx := (Nat.mod_modEq x 7).symm
      have red := (mx.pow 4).add_right 4
      change (x^4+4)%7=((x%7)^4+4)%7 at red
      rw [Nat.dvd_iff_mod_eq_zero, red]
      have bound := Nat.mod_lt x (by decide : 0<7)
      interval_cases e : x%7 <;> decide
    have big (t : ℕ) (pt : t.Prime) (dt : t ∣ x^4+4) (ht : 5<t) : 10<t := by
      by_contra! small
      have et : t=7 := by interval_cases t <;> norm_num at *
      exact no7 (et ▸ dt)
    exact nohit ⟨9,l,s,pl,ps,nls,big l pl dl hl,big s ps ds hs,
      f ▸ dvd_mul_of_dvd_right dl 2,f ▸ dvd_mul_of_dvd_right ds 2⟩
  exact ⟨q,r,a,b,pq,pr,ne,q4,by omega,apos,no4,bpos,ob,by omega,by omega⟩

private theorem pell_three_divisibility {x y : ℕ} (he : x^2+2=3*y^2) (hd : 9 ∣ y) :
    17 ∣ y := by
  let states : List (ℕ × ℕ) := [(1,1),(5,3),(19,11),(71,41),(112,0),(71,112),
    (19,142),(5,150),(1,152),(152,152),(148,150),(134,142),(82,112),(41,0),
    (82,41),(134,11),(148,3),(152,1)]
  have closed : ∀ z ∈ states, ((2*z.1+3*z.2)%153,(z.1+2*z.2)%153) ∈ states := by
    decide +kernel
  have sieve : ∀ z ∈ states, 9 ∣ z.2 → 17 ∣ z.2 := by decide +kernel
  have orbit (b a : ℕ) (eqn : a^2+2=3*b^2) : (a%153,b%153) ∈ states := by
    induction b using Nat.strong_induction_on generalizing a with
    | h b ih =>
      by_cases small : b < 2
      · have ab : a ≤ 1 := by nlinarith [Nat.mul_self_le_mul_self (show b ≤ 1 by omega)]
        interval_cases b <;> interval_cases a <;> norm_num at eqn
        all_goals decide +kernel
      · have lb : 2 ≤ b := by omega
        have low : 3*b ≤ 2*a := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad.le, Nat.mul_self_le_mul_self lb]
        have high : a ≤ 2*b := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad.le, Nat.zero_le (b*b)]
        have strict : b < a := by
          by_contra! bad
          nlinarith only [eqn, Nat.mul_self_le_mul_self bad, Nat.mul_self_le_mul_self lb]
        let u := 2*a-3*b
        let v := 2*b-a
        have eu : u+3*b=2*a := Nat.sub_add_cancel low
        have ev : v+a=2*b := Nat.sub_add_cancel high
        have evsmall : v<b := by omega
        have norm : u^2+2=3*v^2 := by
          have az : (a:ℤ)^2+2=3*(b:ℤ)^2 := by exact_mod_cast eqn
          have uz : (u:ℤ)=2*(a:ℤ)-3*(b:ℤ) := by dsimp [u]; push_cast [Nat.cast_sub low]; ring
          have vz : (v:ℤ)=2*(b:ℤ)-(a:ℤ) := by dsimp [v]; push_cast [Nat.cast_sub high]; ring
          have nz : (u:ℤ)^2+2=3*(v:ℤ)^2 := by rw [uz,vz]; linear_combination az
          exact_mod_cast nz
        have prev := closed _ (ih v evsmall u norm)
        have m := (Nat.mod_modEq u 153).symm
        have n := (Nat.mod_modEq v 153).symm
        have ax := (m.mul_left 2).add (n.mul_left 3)
        have by' := m.add (n.mul_left 2)
        change (2*u+3*v)%153=_ at ax
        change (u+2*v)%153=_ at by'
        rwa [show a=2*u+3*v by omega, show b=u+2*v by omega, ax, by']
  have d9 : 9 ∣ y%153 := by omega
  have d17 := sieve (x%153,y%153) (orbit y x he) d9
  change 17 ∣ y%153 at d17
  omega

/-- The only possible natural roots of a power of three minus two are at most five. -/
theorem square_plus_two_three {z e : ℕ} (h : z^2+2=3^e) : z ≤ 5 := by
  rcases Nat.even_or_odd e with ⟨b, rfl⟩|⟨b, rfl⟩
  · have eq : z^2+2=(3^b)^2 := by simpa [pow_add,pow_two] using h
    by_contra! big
    by_cases le : 3^b ≤ z
    · nlinarith [Nat.mul_self_le_mul_self le]
    · nlinarith [Nat.mul_self_le_mul_self (show z+1 ≤ 3^b by omega)]
  · have eq : z^2+2=3*(3^b)^2 := by
      rw [h, pow_succ, mul_comm 2 b, pow_mul, mul_comm]
    by_cases lb : 2 ≤ b
    · have d9 : 9 ∣ 3^b := pow_dvd_pow (3 : ℕ) lb
      have d17 := pell_three_divisibility eq d9
      have pr : Nat.Prime 17 := by decide
      have bad := pr.dvd_of_dvd_pow d17
      omega
    · have ub : b ≤ 1 := by omega
      interval_cases b <;> norm_num at eq <;> nlinarith

/-- Offset three forces exactly one prime other than three to divide the middle term. -/
theorem square_middle {p : ℕ} (pp : p.Prime) (op : Odd p) (hp : 5 < p)
    (nohit : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^2+d ∧ s ∣ p^2+d) :
    ∃ t c e : ℕ, t.Prime ∧ 3 < t ∧ (t%8=1 ∨ t%8=3) ∧
      0 < c ∧ 0 < e ∧ p^2+2=3^c*t^e := by
  let n := p^2+2
  let c := n.factorization 3
  let m := n / 3^c
  have nz : n ≠ 0 := by dsimp [n]; omega
  have form : 3^c*m=n := Nat.ordProj_mul_ordCompl_eq_self n 3
  have dm : m ∣ n := Nat.ordCompl_dvd n 3
  have pos : 0 < m := Nat.ordCompl_pos 3 nz
  have no3 : ¬3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three nz
  have oddn : Odd n := (op.pow (n:=2)).add_even (by decide : Even 2)
  have no2 : ¬2 ∣ m := by intro div; exact (Nat.not_even_iff_odd.mpr oddn) (even_iff_two_dvd.mpr (div.trans dm))
  have div3 : 3 ∣ n := by
    have p3 : ¬3 ∣ p := by
      intro h
      have eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp h
      omega
    have residue := square_mod_three p3
    dsimp [n]; omega
  have cp : 0 < c := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three nz).mp div3
  have big : 2 ≤ m := by
    by_contra! small
    have m1 : m=1 := by omega
    have eq : p^2+2=3^c := by simpa [m1,n] using form.symm
    have bound := square_plus_two_three eq
    omega
  have pure : IsPrimePow m := cofactor_power (d:=2) big dm (by
    intro t pt dt
    have lb := pt.two_le
    by_contra! small
    rcases (show t=2 ∨ t=3 by omega) with rfl|rfl
    · exact no2 dt
    · exact no3 dt) nohit
  obtain ⟨t,e,pt,ep,eq⟩ := (isPrimePow_nat_iff _).mp pure
  have dt : t ∣ m := eq ▸ dvd_pow_self t ep.ne'
  have tb : 3 < t := by
    have lb := pt.two_le
    by_contra! small
    rcases (show t=2 ∨ t=3 by omega) with rfl|rfl
    · exact no2 dt
    · exact no3 dt
  have residue : t%8=1 ∨ t%8=3 := by
    let _ : Fact t.Prime := ⟨pt⟩
    apply (ZMod.exists_sq_eq_neg_two_iff (p:=t) (by omega)).mp
    refine ⟨(p : ZMod t), ?_⟩
    have zero := (ZMod.natCast_eq_zero_iff (p^2+2) t).mpr (dt.trans dm)
    push_cast at zero
    linear_combination -zero
  exact ⟨t,c,e,pt,tb,residue,cp,ep,by rw [eq]; exact form.symm⟩

/-- Each of the four surviving prime-square examples attains supremum one. -/
theorem square_examples {n : ℕ} (cases : n=8 ∨ n=24 ∨ n=48 ∨ n=120) : v_l 1 n = 1 := by
  have size : n ≤ 120 := by omega
  have lo : 1 ≤ v n 1 := by rcases cases with rfl|rfl|rfl|rfl <;> decide +kernel
  have vals : ∀ k : Fin 12, 0 < k.val → v n k.val ≤ 1 := by
    rcases cases with rfl|rfl|rfl|rfl <;> decide +kernel
  apply le_antisymm
  · apply iSup_le; intro k; apply iSup_le; intro hk
    have hv : v n k ≤ 1 := by
      by_cases small : k < 12
      · exact vals ⟨k, small⟩ hk
      · by_contra! hh
        have bound := square_bound hk hh
        have large : 12 ≤ k := by omega
        nlinarith [Nat.mul_le_mul_right k large]
    exact_mod_cast hv
  · exact (by exact_mod_cast lo : (1 : ℕ∞) ≤ (v n 1 : ℕ∞)).trans (offset_le (by decide))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
/-- Exact classification of positive solutions through the largest survivor in the finite search. -/
theorem solutions_through_330 {n : ℕ} (hn : 0 < n) (size : n ≤ 330) :
    v_l 1 n = 1 ↔ n ∈ [1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330] := by
  let xs : List ℕ := [1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
      48,60,70,78,80,96,120,190,222,330]
  change v_l 1 n = 1 ↔ n ∈ xs
  constructor
  · intro sol
    by_contra missing
    have excluded : ∀ m : Fin 331, 0 < m.val → m.val ∉ xs → ∃ k : Fin 12,
        0 < k.val ∧ 1 < ((m.val+k.val).primeFactors.filter (k.val < ·)).card := by
      decide +kernel
    obtain ⟨k,hk,hh⟩ := excluded ⟨n, by omega⟩ hn missing
    have bound := offset_le_one (k:=k.val) sol hk
    rw [v_as_card] at bound
    exact (Nat.not_lt_of_ge bound) hh
  · intro member
    have vals : ∀ m ∈ xs, ∀ k : Fin 20, 0 < k.val →
        ((m+k.val).primeFactors.filter (k.val < ·)).card ≤ 1 := by decide +kernel
    have first : ∀ m ∈ xs, 1 ≤ ((m+1).primeFactors.filter (1 < ·)).card := by decide +kernel
    have lo : 1 ≤ v n 1 := by rw [v_as_card]; exact first n member
    apply le_antisymm
    · apply iSup_le; intro k; apply iSup_le; intro hk
      have hv : v n k ≤ 1 := by
        by_cases small : k < 20
        · rw [v_as_card]; exact vals n member ⟨k,small⟩ hk
        · by_contra! hh
          have b := square_bound hk hh
          have large : 20 ≤ k := by omega
          nlinarith [Nat.mul_le_mul_right k large]
      exact_mod_cast hv
    · exact (by exact_mod_cast lo : (1 : ℕ∞) ≤ (v n 1 : ℕ∞)).trans (offset_le (by decide))

private theorem fifth_order {b q : ℕ} (pb : b.Prime) (ob : Odd b) (pq : q.Prime)
    (dq : q ∣ 2^b+1) (small : q < b) : q=3 := by
  -- The order of -2 divides both the prime b and q-1. It must be one.
  let _ : Fact q.Prime := ⟨pq⟩
  have zero := (ZMod.natCast_eq_zero_iff (2^b+1) q).mpr dq
  push_cast at zero
  have eq : (-2 : ZMod q)^b=1 := by rw [ob.neg_pow]; linear_combination -zero
  have ne : (-2 : ZMod q) ≠ 0 := by
    intro h
    rw [h,zero_pow pb.ne_zero] at eq
    exact zero_ne_one eq
  have cases := (Nat.dvd_prime pb).mp (orderOf_dvd_of_pow_eq_one eq)
  have one : orderOf (-2 : ZMod q)=1 := cases.resolve_right (by
    intro same
    have dd := ZMod.orderOf_dvd_card_sub_one ne
    rw [same] at dd
    have := Nat.le_of_dvd (show 0 < q-1 by have := pq.two_le; omega) dd
    omega)
  have nz := orderOf_eq_one_iff.mp one
  have z : ((3 : ℕ) : ZMod q)=0 := by push_cast; linear_combination -nz
  exact (Nat.prime_dvd_prime_iff_eq pq Nat.prime_three).mp ((ZMod.natCast_eq_zero_iff _ _).mp z)

private theorem mersenne_left_factor {b L : ℕ} (pb : b.Prime) (lb : L < b) (hb : 3 < b) :
    ∃ q : ℕ, q.Prime ∧ L < q ∧ q ∣ 2^b+1 := by
  have ob := pb.odd_of_ne_two (by omega)
  have no9 : ¬9 ∣ 2^b+1 := by
    have b3 : ¬3 ∣ b := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pb).mp h
      omega
    obtain ⟨w,hw⟩ := ob
    have rem : b%6=1 ∨ b%6=5 := by omega
    have pow : Nat.ModEq 9 (2^b) (2^(b%6)) := by
      have h : Nat.ModEq 9 (2^6) 1 := by decide
      calc
        2^b = 2^(b%6)*(2^6)^(b/6) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
        _ ≡ 2^(b%6)*1^(b/6) [MOD 9] := (h.pow _).mul_left _
        _ = _ := by simp
    change 2^b%9=2^(b%6)%9 at pow
    rcases rem with h|h <;> rw [h] at pow <;> norm_num at pow <;> omega
  by_contra! none
  have big := Nat.pow_le_pow_right (by decide : 0<2) (show 3 ≤ b by omega)
  norm_num at big
  have eq : 2^b+1=3^(2^b+1).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
      intro q pq dq
      have upper : q ≤ L := by by_contra! high; exact none q pq high dq
      exact fifth_order pb ob pq dq (by omega))
  generalize (2^b+1).primeFactorsList.length = e at eq
  have e2 : 2 ≤ e := by
    by_contra! bad
    interval_cases e <;> norm_num at eq
    all_goals omega
  exact no9 (eq ▸ (pow_dvd_pow (3 : ℕ) e2))

private theorem fifth_power_residue (a e : ℕ) (sq : a^2%8=1) :
    a^e%8=1 ∨ a^e%8=a%8 := by
  have m : Nat.ModEq 8 (a^2) 1 := sq
  rcases Nat.even_or_odd e with ⟨j,hj⟩|⟨j,hj⟩
  · left
    change Nat.ModEq 8 (a^e) 1
    rw [hj, ←two_mul, pow_mul]
    simpa only [one_pow] using m.pow j
  · right
    change Nat.ModEq 8 (a^e) a
    rw [hj, pow_succ, pow_mul]
    simpa only [one_pow,one_mul] using (m.pow j).mul_right a

/-- Every fifth power of a Mersenne prime provides a two-prime witness. -/
theorem mersenne_fifth_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
    q ∣ p^5+d ∧ s ∣ p^5+d := by
  have ep : p=2^b-1 := by omega
  have b1 : b ≠ 1 := by rintro rfl; norm_num at base; have := pp.two_le; omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime b1 (ep ▸ pp)).2
  by_cases small : b ≤ 33
  · have primes : b ∈ [2,3,5,7,11,13,17,19,23,29,31] := by
      have tab : ∀ k : Fin 34, k.val.Prime → k.val ∈ [2,3,5,7,11,13,17,19,23,29,31] := by decide +kernel
      exact tab ⟨b,by omega⟩ pb
    subst p
    simp only [List.mem_cons,List.not_mem_nil,or_false] at primes
    rcases primes with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨2,5,7,by decide +kernel⟩
    · exact ⟨1,11,191,by decide +kernel⟩
    · exact ⟨6,37,47,by decide +kernel⟩
    · exact ⟨1,11,41,by decide +kernel⟩
    · exact ⟨0,23,89,by decide +kernel⟩
    · exact ⟨1,11,181,by decide +kernel⟩
    · exact ⟨2,7,23,by decide +kernel⟩
    · exact ⟨1,31,421,by decide +kernel⟩
    · exact ⟨1,11,281,by decide +kernel⟩
    · exact ⟨0,233,1103,by decide +kernel⟩
    · exact ⟨3,5,23,by decide +kernel⟩
  by_contra missing
  have d8 : 8 ∣ 2^b := pow_dvd_pow (2 : ℕ) (show 3 ≤ b by omega)
  let x := p-2
  have xp : p=x+2 := by dsimp [x]; have := pp.two_le; omega
  have xm : Nat.ModEq 8 x 5 := by change x%8=5; omega
  let F (y : ℕ) := (((y+6)*y+16)*y+16)*y+16
  let C (y : ℕ) := (((y+7)*y+19)*y+23)*y+11
  have fc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (F i) (F j) :=
    ((((((h.add_right 6).mul h).add_right 16).mul h).add_right 16).mul h).add_right 16
  have cc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (C i) (C j) :=
    ((((((h.add_right 7).mul h).add_right 19).mul h).add_right 23).mul h).add_right 11
  have f8 : F x%8=7 := (fc xm).trans (by decide +kernel : Nat.ModEq 8 (F 5) 7)
  have c8 : C x%8=5 := (cc xm).trans (by decide +kernel : Nat.ModEq 8 (C 5) 5)
  have fac : p^5+32=(p+2)*F x := by rw [xp]; dsimp [F]; ring
  have first : p^5+1=(p+1)*C x := by rw [xp]; dsimp [C]; ring
  -- The two shifted powers differ by 31. A divisor 31 at offset 33
  -- gives a divisor at offset two, where C cannot be a power of 31.
  have no31 : ¬31 ∣ F x := by
    intro d
    have d32 : 31 ∣ p^5+32 := fac ▸ dvd_mul_of_dvd_right d _
    have d1 : 31 ∣ p^5+1 := by omega
    have pr : Nat.Prime 31 := by decide
    have eq : C x = 31^(C x).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
        intro q pq dq
        by_contra neq
        have lq : 2 < q := by
          have := pq.two_le
          by_contra! low
          have q2 : q=2 := by omega
          rw [q2] at dq
          omega
        exact missing ⟨1,q,31,pq,pr,neq,lq,by decide,first ▸ dvd_mul_of_dvd_right dq _,d1⟩)
    have res := fifth_power_residue 31 (C x).primeFactorsList.length (by decide)
    rw [←eq] at res
    norm_num at res
    omega
  obtain ⟨q,pq,hq,dq⟩ := mersenne_left_factor pb (show 33 < b by omega) (by omega)
  have dl : q ∣ p+2 := by convert dq using 1; omega
  obtain ⟨s,ps,hs,ds⟩ : ∃ s : ℕ, s.Prime ∧ 33 < s ∧ s ∣ F x := by
    by_contra! none
    have eq : F x = 11^(F x).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
        intro s ps ds
        have le : s ≤ 33 := by by_contra! big; exact none s ps big ds
        have tab : ∀ i : Fin 34, i.val.Prime → ∀ j : Fin i.val, F j.val%i.val=0 →
            i.val=2 ∨ (i.val=5 ∧ (j.val+4)%5=0) ∨ i.val=11 ∨ i.val=31 := by decide +kernel
        have cong := fc (Nat.mod_modEq x s).symm
        change F x%s=F (x%s)%s at cong
        have opts := tab ⟨s,by omega⟩ ps ⟨x%s,Nat.mod_lt _ ps.pos⟩ (cong ▸ Nat.mod_eq_zero_of_dvd ds)
        change s=2 ∨ (s=5 ∧ (x%s+4)%5=0) ∨ s=11 ∨ s=31 at opts
        rcases opts with rfl|⟨rfl,h⟩|ok|rfl
        · omega
        · have d5 : 5 ∣ 2^b+1 := by omega
          have bad := fifth_order pb (pb.odd_of_ne_two (by omega)) (by decide : Nat.Prime 5) d5 (by omega)
          contradiction
        · exact ok
        · exact False.elim (no31 ds))
    have res := fifth_power_residue 11 (F x).primeFactorsList.length (by decide)
    rw [←eq] at res
    norm_num at res
    omega
  have ne : q≠s := by
    rintro rfl
    have ident : F x+16*(p+2)=80+(p+2)*(x^3+2*x^2+8*x) := by rw [xp]; dsimp [F]; ring
    have dd := dvd_add ds (dvd_mul_of_dvd_right dl 16)
    rw [ident] at dd
    have d80 := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left dl _)).mpr dd
    have mem := pq.mem_primeFactors d80 (by decide)
    have list : (80:ℕ).primeFactors={2,5} := by decide +kernel
    rw [list] at mem
    simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    omega
  exact missing ⟨32,q,s,pq,ps,ne,hq,hs,fac ▸ dvd_mul_of_dvd_left dl _,fac ▸ dvd_mul_of_dvd_right ds _⟩


private theorem seventh_residue_product {v : ℕ} (hv : v ≠ 0)
    (h : ∀ q : ℕ, q.Prime → q ∣ v → q%24 ∈ [1,5,19,23]) : v%24 ∈ [1,5,19,23] := by
  let G : List ℕ := [1,5,19,23]
  -- These four residues form a subgroup of the units modulo 24.
  have closed : ∀ a ∈ G, ∀ b ∈ G, a*b%24 ∈ G := by decide +kernel
  have aux (l : List ℕ) (hl : ∀ q ∈ l, q%24 ∈ G) : l.prod%24 ∈ G := by
    induction l with
    | nil => decide +kernel
    | cons a t ih =>
      rw [List.prod_cons,Nat.mul_mod]
      exact closed _ (hl a (List.mem_cons_self ..)) _ (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)))
  have res := aux v.primeFactorsList (fun q hq => h q (Nat.prime_of_mem_primeFactorsList hq)
    (Nat.dvd_of_mem_primeFactorsList hq))
  rwa [Nat.prod_primeFactorsList hv] at res

set_option maxRecDepth 16384 in
private theorem seventh_small {b : ℕ} (small : b≤129) (pb : b.Prime) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ (2^b-1)^7+d ∧ s ∣ (2^b-1)^7+d := by
  let certs : List (ℕ × ℕ × ℕ × ℕ) := [(2,2,11,199),(3,1,113,911),(5,4,7,397),(7,1,673,757),(11,0,23,89),(13,1,29,71),(17,3,11,23),(19,1,71,281),(23,2,5,17),(29,0,233,1103),(31,1,71,113),(37,1,673,3067),(41,1,29,127),(43,3,13,31),(47,0,2351,4513),(53,4,7,73),(59,1,113,701),(61,3,23,157),(67,2,5,353),(71,2,5,17),(73,5,11,1487),(79,2,5,17),(83,1,71,127),(89,1,71,281),(97,1,29,127),(101,2,179,199),(103,1,239,673),(107,4,7,73),(109,3,349,557),(113,2,419,3583),(127,2,5,17)]
  have covers : ∀ k : Fin 130, k.val.Prime → ∃ z ∈ certs, z.1=k.val := by decide +kernel
  have valid : ∀ z ∈ certs, z.2.2.1.Prime ∧ z.2.2.2.Prime ∧ z.2.2.1≠z.2.2.2 ∧
      z.2.1+1<z.2.2.1 ∧ z.2.1+1<z.2.2.2 ∧ z.2.2.1 ∣ (2^z.1-1)^7+z.2.1 ∧
        z.2.2.2 ∣ (2^z.1-1)^7+z.2.1 := by decide +kernel
  obtain ⟨⟨j,d,q,s⟩,mem,eq⟩ := covers ⟨b,by omega⟩ pb
  change j=b at eq
  subst j
  exact ⟨d,q,s,valid _ mem⟩

set_option maxRecDepth 16384 in
set_option synthInstance.maxSize 512 in
set_option maxHeartbeats 2000000 in
/-- Every seventh power of a Mersenne prime provides a two-prime witness. -/
theorem mersenne_seventh_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
    q ∣ p^7+d ∧ s ∣ p^7+d := by
  have ep : p=2^b-1 := by omega
  have b1 : b ≠ 1 := by rintro rfl; norm_num at base; have := pp.two_le; omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime b1 (ep ▸ pp)).2
  by_cases small : b ≤ 129
  · exact ep ▸ seventh_small small pb
  by_contra missing
  have ob := pb.odd_of_ne_two (by omega)
  have d16 : 16 ∣ 2^b := pow_dvd_pow (2 : ℕ) (show 4 ≤ b by omega)
  let x := p-2
  have xp : p=x+2 := by dsimp [x]; have := pp.two_le; omega
  have p3 : Nat.ModEq 3 (2^b) 2 := by
    obtain ⟨j,hj⟩ := ob
    rw [hj,pow_succ,pow_mul]
    have h : Nat.ModEq 3 (2^2) 1 := by decide
    simpa only [one_pow,one_mul] using (h.pow j).mul_right 2
  change 2^b%3=2 at p3
  have xm : Nat.ModEq 24 x 5 := by change x%24=5; omega
  have xn : Nat.ModEq 16 x 13 := by change x%16=13; omega
  let F (y : ℕ) := (((((y+10)*y+44)*y+104)*y+144)*y+96)*y+64
  let C (y : ℕ) := (((((y+11)*y+51)*y+127)*y+179)*y+135)*y+43
  have fc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (F i) (F j) :=
    ((((((((((h.add_right 10).mul h).add_right 44).mul h).add_right 104).mul h).add_right 144).mul h).add_right 96).mul h).add_right 64
  have cc {m i j : ℕ} (h : Nat.ModEq m i j) : Nat.ModEq m (C i) (C j) :=
    ((((((((((h.add_right 11).mul h).add_right 51).mul h).add_right 127).mul h).add_right 179).mul h).add_right 135).mul h).add_right 43
  have f24 : F x%24=7 := (fc xm).trans (by decide +kernel : Nat.ModEq 24 (F 5) 7)
  have c16 : C x%16=7 := (cc xn).trans (by decide +kernel : Nat.ModEq 16 (C 13) 7)
  have fac : p^7+128=(p+2)*F x := by rw [xp]; dsimp [F]; ring
  have first : p^7+1=(p+1)*C x := by rw [xp]; dsimp [C]; ring
  have no127 : ¬127 ∣ F x := by
    intro d
    have d128 : 127 ∣ p^7+128 := fac ▸ dvd_mul_of_dvd_right d _
    have d1 : 127 ∣ p^7+1 := by omega
    have pr : Nat.Prime 127 := by decide
    have eq : C x = 127^(C x).primeFactorsList.length :=
      Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
        intro q pq dq
        by_contra neq
        have lq : 2 < q := by
          have := pq.two_le
          by_contra! low
          have q2 : q=2 := by omega
          rw [q2] at dq
          omega
        exact missing ⟨1,q,127,pq,pr,neq,lq,by decide,first ▸ dvd_mul_of_dvd_right dq _,d1⟩)
    have res (e : ℕ) : 127^e%16=1 ∨ 127^e%16=15 := by
      induction e with
      | zero => decide
      | succ e ih =>
        rw [pow_succ,Nat.mul_mod]
        rcases ih with h|h <;> rw [h] <;> decide
    have rr := res (C x).primeFactorsList.length
    rw [←eq] at rr
    omega
  have no113 : ¬113 ∣ F x := by
    -- The period of 2 modulo 113 is 28. The prime exponent b is coprime to 28.
    have period : Nat.ModEq 113 (2^28) 1 := by decide
    have red : Nat.ModEq 113 (2^b) (2^(b%28)) := by
      calc
        2^b = 2^(b%28)*(2^28)^(b/28) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
        _ ≡ 2^(b%28)*1^(b/28) [MOD 113] := (period.pow _).mul_left _
        _ = _ := by simp
    have b7 : ¬7 ∣ b := by
      intro h
      have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) pb).mp h
      omega
    have trans := (Nat.mod_modEq x 113).add_right 3
    change (x%113+3)%113=(x+3)%113 at trans
    change 2^b%113=2^(b%28)%113 at red
    have g := fc (Nat.mod_modEq x 113).symm
    change F x%113=F (x%113)%113 at g
    have tab : ∀ k : Fin 28, k.val%2=1 → k.val%7≠0 → ∀ z : Fin 113,
        (z.val+3)%113=2^k.val%113 → F z.val%113≠0 := by decide +kernel
    obtain ⟨w,ow⟩ := ob
    have rr := tab ⟨b%28,Nat.mod_lt _ (by decide)⟩ (by dsimp; omega) (by dsimp; omega)
      ⟨x%113,Nat.mod_lt _ (by decide)⟩ (by dsimp; omega)
    rw [Nat.dvd_iff_mod_eq_zero,g]
    exact rr
  obtain ⟨q,pq,hq,dq⟩ := mersenne_left_factor pb (show 129 < b by omega) (by omega)
  have dl : q ∣ p+2 := by convert dq using 1; omega
  obtain ⟨s,ps,hs,ds⟩ : ∃ s : ℕ, s.Prime ∧ 129 < s ∧ s ∣ F x := by
    by_contra! none
    have res := seventh_residue_product (v:=F x) (by omega) (by
      intro s ps ds
      have le : s ≤ 129 := by by_contra! big; exact none s ps big ds
      have tab : ∀ i : Fin 130, i.val.Prime → ∀ j : Fin i.val, F j.val%i.val=0 →
          i.val=2 ∨ (i.val=7 ∧ (j.val+4)%7=0) ∨ i.val=113 ∨ i.val=127 ∨
            i.val%24 ∈ [1,5,19,23] := by decide +kernel
      have cong := fc (Nat.mod_modEq x s).symm
      change F x%s=F (x%s)%s at cong
      have opts := tab ⟨s,by omega⟩ ps ⟨x%s,Nat.mod_lt _ ps.pos⟩ (cong ▸ Nat.mod_eq_zero_of_dvd ds)
      change s=2 ∨ (s=7 ∧ (x%s+4)%7=0) ∨ s=113 ∨ s=127 ∨ s%24 ∈ [1,5,19,23] at opts
      rcases opts with rfl|⟨rfl,h⟩|rfl|rfl|ok
      · omega
      · have d7 : 7 ∣ 2^b+1 := by omega
        have bad := fifth_order pb ob (by decide : Nat.Prime 7) d7 (by omega)
        contradiction
      · exact False.elim (no113 ds)
      · exact False.elim (no127 ds)
      · exact ok)
    rw [f24] at res
    norm_num at res
  have ne : q≠s := by
    rintro rfl
    have ident : F x+96*(p+2)=448+(p+2)*(x^5+6*x^4+20*x^3+24*x^2+48*x) := by rw [xp]; dsimp [F]; ring
    have dd := dvd_add ds (dvd_mul_of_dvd_right dl 96)
    rw [ident] at dd
    have d448 := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left dl _)).mpr dd
    have mem := pq.mem_primeFactors d448 (by decide)
    have list : (448:ℕ).primeFactors={2,7} := by decide +kernel
    rw [list] at mem
    simp only [Finset.mem_insert,Finset.mem_singleton] at mem
    omega
  exact missing ⟨128,q,s,pq,ps,ne,hq,hs,fac ▸ dvd_mul_of_dvd_left dl _,fac ▸ dvd_mul_of_dvd_right ds _⟩


/-- A solution cannot immediately precede any nontrivial fifth or seventh power. -/
theorem fifth_seventh_exclusion {n x r : ℕ} (hx : 1 < x) (hr : r=5 ∨ r=7)
    (eq : n+1=x^r) : v_l 1 n ≠ 1 := by
  intro sol
  have rp : 1 < r := by omega
  have ro : Odd r := by rcases hr with rfl|rfl <;> decide
  have bound : 32 ≤ x^r := by
    have a := Nat.pow_le_pow_left (show 2 ≤ x by omega) r
    rcases hr with rfl|rfl <;> norm_num at a <;> omega
  have ox : Odd x := by
    apply Nat.not_even_iff_odd.mp
    intro ex
    have dd : 2 ∣ x^r := (even_iff_two_dvd.mp ex).trans (dvd_pow_self x (by omega))
    have on : Odd n := by rw [Nat.odd_iff]; omega
    rcases (odd_classification on).mp sol with h|h|h|h <;> omega
  obtain ⟨b,base⟩ := odd_power_root_neighbor ox hx ro rp eq sol
  have pure := prime_power_succ (n:=n) (by omega) sol
  rw [eq,isPrimePow_pow_iff (by omega : r≠0)] at pure
  obtain ⟨p,e,pp,pe,he⟩ := (isPrimePow_nat_iff _).mp pure
  have op := pp.odd_of_ne_two (by
    rintro rfl
    have div := dvd_pow_self (2:ℕ) pe.ne'
    rw [he] at div
    exact (Nat.not_even_iff_odd.mpr ox) (even_iff_two_dvd.mpr div))
  have one := mersenne_power_exponent op pp.one_lt pe (he.symm ▸ base)
  rw [one,pow_one] at he
  subst x
  have hit : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p^r+d ∧ s ∣ p^r+d := by
    rcases hr with rfl|rfl
    · exact mersenne_fifth_witness pp base
    · exact mersenne_seventh_witness pp base
  obtain ⟨d,q,s,pq,ps,ne,hq,hs,dq,ds⟩ := hit
  have rearr : n+(d+1)=p^r+d := by omega
  exact two_primes (k:=d+1) (by omega) pq ps ne hq hs (rearr ▸ dq) (rearr ▸ ds) sol

private theorem odd_power_cannot_precede_prime_power {x r : ℕ} (hx : 3 ≤ x)
    (ex : Even x) (ro : Odd r) (hr : 3 ≤ r) : ¬IsPrimePow (x^r+1) := by
  intro pure
  have grow (j : ℕ) : (j+2)*(x+1) ≤ x^(j+2) := by
    induction j with
    | zero =>
      change 2*(x+1) ≤ x^2
      nlinarith [Nat.mul_le_mul_right x hx]
    | succ j ih =>
      have le : j+3 ≤ (j+2)*x := by
        have hb := Nat.mul_le_mul_left (j+2) hx
        omega
      have a := Nat.mul_le_mul_right (x+1) le
      have b := Nat.mul_le_mul_right x ih
      rw [show j+1+2=(j+2)+1 by omega,pow_succ]
      nlinarith only [a,b]
  have g := grow (r-2)
  rw [show r-2+2=r by omega] at g
  have d : x+1 ∣ x^r+1 := by simpa using (ro.nat_add_dvd_pow_add_pow (x:=x) (y:=1))
  obtain ⟨c,fac⟩ := d
  have hc : r < c := by
    by_contra! small
    have h := Nat.mul_le_mul_left (x+1) small
    nlinarith only [h,g,fac]
  obtain ⟨q,e,pq,_,eq⟩ := (isPrimePow_nat_iff _).mp pure
  have facq : (x+1)*c=q^e := fac.symm.trans eq.symm
  obtain ⟨a,_,ea⟩ := (Nat.dvd_prime_pow pq).mp (facq ▸ dvd_mul_right (x+1) c)
  obtain ⟨b,_,eb⟩ := (Nat.dvd_prime_pow pq).mp (facq ▸ dvd_mul_left c (x+1))
  have ap : a ≠ 0 := by rintro rfl; simp at ea; omega
  have dq : q ∣ x+1 := ea ▸ dvd_pow_self q ap
  have oq := pq.odd_of_ne_two (by
    rintro rfl
    obtain ⟨t,ht⟩ := ex
    omega)
  have nx : ¬q ∣ x := by
    intro dx
    have d1 := (Nat.dvd_add_iff_right dx).mpr dq
    have := Nat.le_of_dvd Nat.one_pos d1
    have := pq.two_le
    omega
  let _ : Fact q.Prime := ⟨pq⟩
  have v := padicValNat.pow_add_pow (x:=x) (y:=1) oq dq nx ro
  rw [one_pow,fac,padicValNat.mul (by omega) (by omega)] at v
  have val : padicValNat q c=padicValNat q r := by omega
  have power : q^(padicValNat q c)=c := by
    conv_lhs => arg 2; rw [eb,padicValNat.prime_pow]
    exact eb.symm
  have cd : c ∣ r := by rw [←power,val]; exact pow_padicValNat_dvd
  exact (Nat.not_le_of_gt hc) (Nat.le_of_dvd (by omega) cd)

private theorem even_fourth_power_excluded {x : ℕ} (hx : 2 < x) (ex : Even x) :
    v_l 1 (x^4) ≠ 1 := by
  obtain ⟨u,hu⟩ := ex
  let z := u-1
  have xz : x=2*(z+1) := by dsimp [z]; omega
  let L := 2*z^2+2*z+1
  let R := 2*z^2+6*z+5
  have zl : 1 ≤ z := by omega
  have f : x^4+4=4*L*R := by rw [xz]; dsimp [L,R]; ring
  have lb : 2 ≤ L := by dsimp [L]; omega
  have rb : 2 ≤ R := by dsimp [R]; omega
  obtain ⟨p,pp,dp⟩ := Nat.exists_prime_and_dvd (show L ≠ 1 by omega)
  obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd (show R ≠ 1 by omega)
  have no3 : ¬3 ∣ L ∧ ¬3 ∣ R := by
    have m := (Nat.mod_modEq z 3).symm
    have ml := (((m.pow 2).mul_left 2).add (m.mul_left 2)).add_right 1
    have mr := (((m.pow 2).mul_left 2).add (m.mul_left 6)).add_right 5
    change L%3=_ at ml
    change R%3=_ at mr
    have h := Nat.mod_lt z (by decide : 0<3)
    simp only [Nat.dvd_iff_mod_eq_zero,ml,mr]
    interval_cases e : z%3 <;> decide
  have high (t : ℕ) (pt : t.Prime) (dv : t ∣ L ∨ t ∣ R) : 4<t := by
    by_contra! small
    have choices : t=2 ∨ t=3 := by interval_cases t <;> norm_num at *
    rcases choices with rfl|rfl
    · rcases dv with h|h <;> dsimp [L,R] at h <;> omega
    · tauto
  have ph := high p pp (Or.inl dp)
  have qh := high q pq (Or.inr dq)
  have diff : R=L+4*(z+1) := by dsimp [R,L]; ring
  have ne : p≠q := by
    rintro rfl
    rw [diff] at dq
    have dd := (Nat.dvd_add_iff_right dp).mpr dq
    have dz := pp.dvd_mul.mp dd |>.resolve_left (by
      intro bad
      have := Nat.le_of_dvd (by decide : 0<4) bad
      omega)
    have ll : L=2*z*(z+1)+1 := by dsimp [L]; ring
    rw [ll] at dp
    have d1 := (Nat.dvd_add_iff_right (dvd_mul_of_dvd_right dz (2*z))).mpr dp
    have := Nat.le_of_dvd Nat.one_pos d1
    omega
  exact two_primes (k:=4) (by decide) pp pq ne ph qh
    (f ▸ dvd_mul_of_dvd_left (dvd_mul_of_dvd_right dp 4) _) (f ▸ dvd_mul_of_dvd_right dq _)

private theorem odd_actual_power {x r : ℕ} (hx : 1<x) (hr : 3≤r) (ro : Odd r)
    (sol : v_l 1 (x^r)=1) : x^r=8 := by
  have pos : 0 < x^r := Nat.pow_pos (by omega)
  have pure := prime_power_succ pos sol
  rcases Nat.even_or_odd x with ex|ox
  · by_cases eq : x=2
    · subst x
      rcases prime_power_neighbor (by omega) pure with h|⟨t,ht⟩
      · simp [h]
      · have t0 : t≠0 := by rintro rfl; norm_num at ht; omega
        have d2 := dvd_pow_self (2:ℕ) t0
        obtain ⟨w,hw⟩ := ro
        omega
    · exact False.elim (odd_power_cannot_precede_prime_power (by omega) ex ro hr pure)
  · have high : 27 ≤ x^r := by
      have three : 3 ≤ x := by obtain ⟨t,ht⟩ := ox; omega
      exact (Nat.pow_le_pow_left three 3).trans (Nat.pow_le_pow_right (by omega) hr)
    rcases (odd_classification ox.pow).mp sol with h|h|h|h <;> omega

/-- The only positive solutions that are perfect powers of exponent at least three are 8 and 16. -/
theorem higher_perfect_power {x r : ℕ} (hx : 1<x) (hr : 3≤r) :
    v_l 1 (x^r)=1 ↔ x^r=8 ∨ x^r=16 := by
  constructor
  · intro sol
    by_cases four : 4 ∣ r
    · obtain ⟨j,hj⟩ := four
      let y := x^j
      have eq : x^r=y^4 := by dsimp [y]; rw [hj,←pow_mul,Nat.mul_comm]
      rw [eq] at sol ⊢
      have hy : 1<y := Nat.one_lt_pow (by omega : j ≠ 0) hx
      rcases Nat.even_or_odd y with ev|od
      · have small : y≤2 := by by_contra! large; exact even_fourth_power_excluded large ev sol
        right
        rw [show y=2 by omega]
        decide
      · have large : 81 ≤ y^4 := Nat.pow_le_pow_left (show 3≤y by obtain ⟨t,ht⟩ := od; omega) 4
        rcases (odd_classification od.pow).mp sol with h|h|h|h <;> omega
    · left
      rcases Nat.even_or_odd r with ⟨j,hj⟩|ro
      · have oj : Odd j := by rw [Nat.odd_iff]; omega
        have eq : x^r=(x^2)^j := by rw [hj,←pow_mul,two_mul]
        rw [eq] at sol ⊢
        exact odd_actual_power (Nat.one_lt_pow (by decide : 2≠0) hx) (by omega) oj sol
      · exact odd_actual_power hx hr ro sol
  · rintro (h|h) <;> rw [h] <;> apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide +kernel


private theorem solution_prime_power_factor {n k c : ℕ} (sol : v_l 1 n = 1)
    (hk : 0 < k) (hc : 2 ≤ c) (div : c ∣ n+k)
    (eligible : ∀ p : ℕ, p.Prime → p ∣ c → k < p) : IsPrimePow c := by
  by_contra bad
  obtain ⟨p, hp, q, hq, different⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hc).mp bad
  obtain ⟨pp, dp, _⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨pq, dq, _⟩ := Nat.mem_primeFactors.mp hq
  exact two_primes hk pp pq different (eligible p pp dp) (eligible q pq dq)
    (dp.trans div) (dq.trans div) sol

/-- All powers of two which attain the lowercase supremum one. -/
theorem power_two_solution {n b : ℕ} (hn : n=2^b) :
    v_l 1 n = 1 ↔ n=1 ∨ n=2 ∨ n=4 ∨ n=8 ∨ n=16 := by
  constructor
  · intro sol
    have bound : b ≤ 4 := by
      by_contra! eb
      have pp := prime_power_succ (n:=n) (by rw [hn]; positivity) sol
      rw [hn] at pp
      obtain ⟨t,ht⟩ := (prime_power_neighbor (by omega) pp).resolve_left (by omega)
      have tp : t≠0 := by rintro rfl; simp at ht; omega
      have evenb : 2 ∣ b := ht ▸ dvd_pow_self 2 tp
      let a := b-1
      have ha : b=a+1 := by dsimp [a]; omega
      have ea : 2 ∣ 2^a := dvd_pow_self _ (by omega)
      have mid : n+2=2*(2^a+1) := by rw [hn,ha,pow_succ]; ring
      have pp2 : IsPrimePow (2^a+1) :=
        solution_prime_power_factor sol (k:=2) (by decide) (by have := @Nat.one_le_two_pow a; omega)
          (mid ▸ dvd_mul_left _ _) (by
            intro q pq dq
            have := pq.two_le
            by_contra! low
            have eq : q=2 := by omega
            rw [eq] at dq
            omega)
      obtain ⟨u,hu⟩ := (prime_power_neighbor (by omega) pp2).resolve_left (by omega)
      have up : u≠0 := by rintro rfl; simp at hu; omega
      have evena : 2 ∣ a := hu ▸ dvd_pow_self 2 up
      omega
    interval_cases b <;> norm_num at hn <;> omega
  · rintro (rfl|rfl|rfl|rfl|rfl) <;> apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide

private theorem shifted_double_orbit {n t s k p q r : ℕ} (hn : n+2=2*2^(2^t))
    (j : ℕ) (ht : t=s+12*j) (hk : 0<k)
    (pp : p.Prime) (pq : q.Prime) (ne : p≠q) (hp : k<p) (hq : k<q)
    (base : Nat.ModEq (p*q) (2^(2^s)) r) (period : Nat.ModEq (p*q) (r^4096) r)
    (hit : Nat.ModEq (p*q) (2*r+k) 2) : v_l 1 n ≠ 1 := by
  have orbit (i : ℕ) : Nat.ModEq (p*q) (2^(2^(s+12*i))) r := by
    induction i with
    | zero => simpa using base
    | succ i ih =>
      rw [show s+12*(i+1)=(s+12*i)+12 by omega,pow_add,pow_mul]
      calc
        _ ≡ r^(2^12) [MOD p*q] := ih.pow (2^12)
        _ ≡ r [MOD p*q] := by rw [show (2:ℕ)^12=4096 by decide]; exact period
  have cover := (((orbit j).mul_left 2).add_right k).trans hit
  rw [←ht,←hn,show n+2+k=(n+k)+2 by omega] at cover
  have d := Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' 2 (b:=0) cover)
  exact two_primes hk pp pq ne hp hq ((dvd_mul_right p q).trans d) ((dvd_mul_left q p).trans d)

set_option maxRecDepth 16384 in
private theorem shifted_double_exclusion {n t : ℕ} (hn : n+2=2*2^(2^t)) (ht : 3≤t) :
    v_l 1 n ≠ 1 := by
  let j := (t-3)/12
  have classes : t=3+12*j ∨ t=4+12*j ∨ t=5+12*j ∨ t=6+12*j ∨ t=7+12*j ∨ t=8+12*j ∨ t=9+12*j ∨ t=10+12*j ∨ t=11+12*j ∨ t=12+12*j ∨ t=13+12*j ∨ t=14+12*j := by
    dsimp [j]; omega
  rcases classes with h|h|h|h|h|h|h|h|h|h|h|h
  · apply shifted_double_orbit (k:=1) (p:=7) (q:=73) (r:=256) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=10) (p:=29) (q:=113) (r:=3273) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=10) (p:=13) (q:=41) (r:=529) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=6) (p:=19) (q:=43) (r:=815) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=10) (p:=13) (q:=29) (r:=373) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=9) (p:=13) (q:=79) (r:=510) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=1) (p:=7) (q:=73) (r:=256) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=11) (p:=19) (q:=41) (r:=385) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=7) (p:=11) (q:=53) (r:=289) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=6) (p:=11) (q:=19) (r:=207) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=10) (p:=13) (q:=29) (r:=373) hn j h <;> decide +kernel
  · apply shifted_double_orbit (k:=34) (p:=241) (q:=433) (r:=104337) hn j h <;> decide +kernel

private theorem shifted_even_exclusion {n j : ℕ} (hn : n+2=2^(j+j)) (hj : 2 ≤ j) :
    v_l 1 n ≠ 1 := by
  let x := 2^j
  have large : 4≤x := Nat.pow_le_pow_right (by decide : 0 < 2) hj
  have evenx : 2 ∣ x := dvd_pow_self 2 (by omega)
  have sq : n+2=x*x := by simpa [x,pow_add] using hn
  have fac : n+1=(x-1)*(x+1) := by
    have u : x-1+1=x := by omega
    nlinarith
  let p := (x-1).minFac
  let q := (x+1).minFac
  have pp : p.Prime := Nat.minFac_prime (by omega)
  have pq : q.Prime := Nat.minFac_prime (by omega)
  have dp : p ∣ x-1 := Nat.minFac_dvd _
  have dq : q ∣ x+1 := Nat.minFac_dvd _
  have ne : p≠q := by
    intro e
    rw [←e] at dq
    have diff := Nat.dvd_sub dq dp
    rw [show x+1-(x-1)=2 by omega] at diff
    have := Nat.le_of_dvd (by decide) diff
    have := pp.two_le
    have eq : p=2 := by omega
    rw [eq] at dq
    omega
  exact two_primes (k:=1) (by decide) pp pq ne pp.one_lt pq.one_lt
    (fac ▸ dvd_mul_of_dvd_left dp _) (fac ▸ dvd_mul_of_dvd_right dq _)

/-- All positive solutions two below a power of two. -/
theorem two_below_power_two_solution {n b : ℕ} (pos : 0<n) (hn : n+2=2^b) :
    v_l 1 n=1 ↔ n=2 ∨ n=6 ∨ n=30 := by
  constructor
  · intro sol
    have b2 : 2≤b := by by_contra! low; interval_cases b <;> norm_num at hn <;> omega
    rcases Nat.even_or_odd b with ⟨j,hj⟩ | ⟨j,hj⟩
    · by_cases large : 2 ≤ j
      · exact False.elim (shifted_even_exclusion (hj ▸ hn) large sol)
      · have j1 : j=1 := by omega
        rw [hj,j1] at hn
        norm_num at hn
        omega
    · let a := 2*j
      have ha : b=a+1 := hj
      have ea : 2 ∣ 2^a := dvd_pow_self _ (by omega)
      have m3 : 2^a%3=1 := by
        change Nat.ModEq 3 (2^a) 1
        have c : Nat.ModEq 3 (2^2) 1 := by decide
        have u := c.pow j
        simpa only [a,pow_mul,one_pow] using u
      have adj : n+4=2*(2^a+1) := by rw [ha,pow_succ] at hn; omega
      have pp : IsPrimePow (2^a+1) :=
        solution_prime_power_factor sol (k:=4) (by decide) (by have := @Nat.one_le_two_pow a; omega)
          (adj ▸ dvd_mul_left _ _) (by
            intro q pq dq
            by_contra! lq
            have choices : q=2 ∨ q=3 := by interval_cases q <;> norm_num at *
            rcases choices with rfl|rfl <;> omega)
      obtain ⟨t,ht⟩ := (prime_power_neighbor (by omega) pp).resolve_left (by dsimp [a]; omega)
      have expr : n+2=2*2^(2^t) := by rw [ha,pow_succ,ht] at hn; simpa [Nat.mul_comm] using hn
      have small : t≤2 := by by_contra! large; exact shifted_double_exclusion expr large sol
      interval_cases t <;> norm_num at expr <;> omega
  · rintro (rfl|rfl|rfl) <;> apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide

private theorem shifted_prime_above_three {m : ℕ} (hm : 1 < m) (oddm : ¬2 ∣ m)
    (ex : ∀ e : ℕ, m≠3^e) : ∃ p : ℕ, p.Prime ∧ 3<p ∧ p ∣ m := by
  by_contra! none
  exact ex _ (Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
    intro p pp dp
    have low : p ≤ 3 := by by_contra! big; exact none p pp big dp
    have := pp.two_le
    by_contra different
    have e : p=2 := by omega
    exact oddm (e ▸ dp)))

private theorem shifted_plus_not_three {j e : ℕ} (hj : 4≤j) : 2^j+1≠3^e := by
  intro eq
  have ep : e≠0 := by
    rintro rfl
    have := @Nat.one_le_two_pow j
    simp at eq
  have primepower : IsPrimePow (2^j+1) := (isPrimePow_nat_iff _).mpr
    ⟨3,e,Nat.prime_three,Nat.pos_of_ne_zero ep,eq.symm⟩
  obtain ⟨t,ht⟩ := (prime_power_neighbor (by omega) primepower).resolve_left (by omega)
  have tn : t≠0 := by rintro rfl; simp at ht; omega
  obtain ⟨u,hu⟩ : 2 ∣ j := ht ▸ dvd_pow_self 2 tn
  have red : Nat.ModEq 3 (2^j) 1 := by
    rw [hu,pow_mul]
    have m : Nat.ModEq 3 (2^2) 1 := by decide
    simpa only [one_pow] using m.pow u
  change 2^j%3=1 at red
  have d : 3 ∣ 2^j+1 := eq ▸ dvd_pow_self _ ep
  omega

/-- All positive solutions four below a power of two. -/
theorem four_below_power_two_solution {n b : ℕ} (pos : 0<n) (hn : n+4=2^b) :
    v_l 1 n=1 ↔ n=4 ∨ n=12 ∨ n=60 := by
  constructor
  · intro sol
    have bound : b≤6 := by
      by_contra! large
      let j := b/2
      let x := 2^j
      have j3 : 3≤j := by dsimp [j]; omega
      have xl : 8≤x := Nat.pow_le_pow_right (by decide : 0 < 2) j3
      have xe : 8 ∣ x := pow_dvd_pow (2:ℕ) j3
      have e0 : ¬2 ∣ x-1 := by omega
      have e1 : ¬2 ∣ x+1 := by omega
      have disjoint {p q : ℕ} (hp : 2<p) (dp : p ∣ x-1) (dq : q ∣ x+1) : p≠q := by
        rintro rfl
        have d := Nat.dvd_sub dq dp
        rw [show x+1-(x-1)=2 by omega] at d
        have := Nat.le_of_dvd (by decide) d
        omega
      have fac : x*x=(x-1)*(x+1)+1 := by
        have h : x-1+1=x := by omega
        nlinarith
      by_cases evenb : b=2*j
      · have j4 : 4≤j := by omega
        have shifted : n+3=(x-1)*(x+1) := by
          rw [evenb,Nat.mul_comm 2 j,pow_mul,pow_two] at hn
          change n+4=x*x at hn
          omega
        obtain ⟨p,pp,hp,dp⟩ := shifted_prime_above_three (m:=x-1) (by omega) e0 (by
          intro e eq
          have rr : 3^e%8=1 ∨ 3^e%8=3 := three_pow_mod_eight e
          omega)
        obtain ⟨q,pq,hq,dq⟩ := shifted_prime_above_three (m:=x+1) (by omega) e1
          (fun _ => shifted_plus_not_three j4)
        exact two_primes (k:=3) (by decide) pp pq (disjoint (by omega) dp dq) hp hq
          (shifted ▸ dvd_mul_of_dvd_left dp _) (shifted ▸ dvd_mul_of_dvd_right dq _) sol
      · have oddb : b=2*j+1 := by dsimp [j] at *; omega
        have shifted : n+2=2*((x-1)*(x+1)) := by
          rw [oddb,pow_succ,Nat.mul_comm 2 j,pow_mul,pow_two] at hn
          change n+4=x*x*2 at hn
          omega
        let p := (x-1).minFac
        let q := (x+1).minFac
        have pp : p.Prime := Nat.minFac_prime (by omega)
        have pq : q.Prime := Nat.minFac_prime (by omega)
        have dp : p ∣ x-1 := Nat.minFac_dvd _
        have dq : q ∣ x+1 := Nat.minFac_dvd _
        have hp : 2<p := by
          have := pp.two_le
          by_contra! low
          have eq : p=2 := by omega
          exact e0 (eq ▸ dp)
        have hq : 2<q := by
          have := pq.two_le
          by_contra! low
          have eq : q=2 := by omega
          exact e1 (eq ▸ dq)
        exact two_primes (k:=2) (by decide) pp pq (disjoint hp dp dq) hp hq
          (shifted ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dp _) _)
          (shifted ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right dq _) _) sol
    have bad : n≠28 := by
      rintro rfl
      have m := (solutions_through_330 (n:=28) (by decide) (by decide)).mp sol
      exact (by decide : 28 ∉ ([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,
        48,60,70,78,80,96,120,190,222,330] : List ℕ)) m
    interval_cases b <;> norm_num at hn <;> omega
  · rintro (rfl|rfl|rfl) <;> apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide

private theorem binary_cofactor_at {n k : ℕ} (hk : 0<k) (ev : 2 ∣ n+k)
    (notpure : ∀ e : ℕ, n+k≠2^e) (sol : v_l 1 n=1)
    (eligible : ∀ q : ℕ, q.Prime → q≠2 → q ∣ n+k → k<q) :
    ∃ q a b : ℕ, q.Prime ∧ k<q ∧ 0<a ∧ 0<b ∧ n+k=2^a*q^b := by
  let N := n+k
  let a := N.factorization 2
  let m := N/2^a
  have nz : N≠0 := by dsimp [N]; omega
  have fac : 2^a*m=N := Nat.ordProj_mul_ordCompl_eq_self N 2
  have dm : m ∣ n+k := Nat.ordCompl_dvd N 2
  have pos : 0 < m := Nat.ordCompl_pos 2 nz
  have oddm : ¬2 ∣ m := Nat.not_dvd_ordCompl Nat.prime_two nz
  have ap : 0<a := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two nz).mp ev
  have m2 : 2 ≤ m := by
    by_contra! small
    have one : m=1 := by omega
    exact notpure a (by simpa only [one,mul_one] using fac.symm)
  have ok (q : ℕ) (pq : q.Prime) (dq : q ∣ m) : k<q :=
    eligible q pq (by rintro rfl; exact oddm dq) (dq.trans dm)
  have pure := solution_prime_power_factor sol hk m2 dm ok
  obtain ⟨q,b,pq,bp,rep⟩ := (isPrimePow_nat_iff _).mp pure
  have dq : q ∣ m := rep ▸ dvd_pow_self q bp.ne'
  exact ⟨q,a,b,pq,ok q pq dq,ap,bp,by rw [rep]; exact fac.symm⟩

/-- The odd parts of both even neighbors p+1 and p+3 are nontrivial prime powers. -/
theorem prime_successor_survivor {n p : ℕ} (pp : p.Prime) (eq : n+1=p)
    (large : 60<n) (sol : v_l 1 n=1) :
    (∀ e : ℕ, p ≠ 2^e+1) ∧ ∃ q r a b c d : ℕ,
      q.Prime ∧ r.Prime ∧ 2<q ∧ 3<r ∧ q≠r ∧ 0<a ∧ 0<b ∧ 0<c ∧ 0<d ∧
      (a=1 ∨ c=1) ∧ p+1=2^a*q^b ∧ p+3=2^c*r^d := by
  have oddp := pp.odd_of_ne_two (by omega)
  obtain ⟨u,hu⟩ := oddp
  constructor
  · intro e he
    have claim := (power_two_solution (n:=n) (b:=e) (by omega)).mp sol
    omega
  · have no2 (e : ℕ) : n+2≠2^e := by
      intro he
      have small := (two_below_power_two_solution (by omega) he).mp sol
      omega
    have no4 (e : ℕ) : n+4≠2^e := by
      intro he
      have small := (four_below_power_two_solution (by omega) he).mp sol
      omega
    obtain ⟨q,a,b,pq,qbig,ap,bp,fa⟩ := binary_cofactor_at (by decide : 0<2)
      (by omega) no2 sol (by intro z pz nz _; have := pz.two_le; omega)
    obtain ⟨r,c,d,pr,rbig,cp,dp,fc⟩ := binary_cofactor_at (by decide : 0<4)
      (by omega) no4 sol (by
        intro z pz nz dz
        by_contra! small
        have z3 : z=3 := by interval_cases z <;> norm_num at *
        rw [z3] at dz
        have d3 : 3 ∣ p := by omega
        have bad := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp d3
        omega)
    have neq : q≠r := by
      rintro rfl
      have d2 : q ∣ n+2 := fa ▸ dvd_mul_of_dvd_right (dvd_pow_self q bp.ne') _
      have d4 : q ∣ n+4 := fc ▸ dvd_mul_of_dvd_right (dvd_pow_self q dp.ne') _
      have diff := Nat.dvd_sub d4 d2
      rw [show n+4-(n+2)=2 by omega] at diff
      have := Nat.le_of_dvd (by decide) diff
      omega
    have one : a=1 ∨ c=1 := by
      by_contra! bad
      have da : 4 ∣ n+2 := fa ▸ dvd_mul_of_dvd_left (pow_dvd_pow (2:ℕ) (show 2≤a by omega)) _
      have dc : 4 ∣ n+4 := fc ▸ dvd_mul_of_dvd_left (pow_dvd_pow (2:ℕ) (show 2≤c by omega)) _
      omega
    exact ⟨q,r,a,b,c,d,pq,pr,qbig,by omega,neq,ap,bp,cp,dp,one,by omega,by omega⟩


open NumberField


private theorem eisenstein_model : Nonempty ((QuadraticAlgebra ℤ (-1) (-1)) ≃ₐ[ℤ] 𝓞 (CyclotomicField 3 ℚ)) := by
  let _ : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) := CyclotomicField.isCyclotomicExtension 3 ℚ
  let z := IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)
  have hz : IsPrimitiveRoot z 3 := IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)
  let w := hz.toInteger
  have sq : w*w=(-1:ℤ) • (1:𝓞 (CyclotomicField 3 ℚ))+(-1:ℤ) • w := by
    have h := IsCyclotomicExtension.Rat.Three.eta_sq hz
    change w^2 = -w-1 at h
    simp only [neg_smul,one_smul]
    linear_combination h
  let f : (QuadraticAlgebra ℤ (-1) (-1)) →ₐ[ℤ] 𝓞 (CyclotomicField 3 ℚ) := QuadraticAlgebra.lift ⟨w,sq⟩
  have inj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).2
    intro x hx
    have e := congrArg f (QuadraticAlgebra.algebraMap_norm_eq_mul_star x)
    rw [AlgHom.commutes,map_mul,hx,zero_mul] at e
    have en : x.norm=0 := by
      change (x.norm : 𝓞 (CyclotomicField 3 ℚ))=0 at e
      exact_mod_cast e
    change x.re*x.re+(-1)*x.re*x.im-(-1)*x.im*x.im=0 at en
    ext
    · change x.re=0
      nlinarith [sq_nonneg (x.re-2*x.im),sq_nonneg x.re, sq_nonneg x.im]
    · change x.im=0
      nlinarith [sq_nonneg (2*x.re-x.im),sq_nonneg x.re,sq_nonneg x.im]
  have surj : Function.Surjective f := by
    let _ : IsCyclotomicExtension {3^1} ℚ (CyclotomicField 3 ℚ) := by norm_num; infer_instance
    let B := (show IsPrimitiveRoot z (3^1) from hz).integralPowerBasisOfPrimePow
    have hg : B.gen=w := IsPrimitiveRoot.integralPowerBasisOfPrimePow_gen _
    have incl : Algebra.adjoin ℤ ({B.gen} : Set (𝓞 (CyclotomicField 3 ℚ))) ≤ f.range := by
      apply Algebra.adjoin_le
      intro v hv
      obtain rfl := Set.mem_singleton_iff.mp hv
      exact ⟨QuadraticAlgebra.omega,by simp [f,QuadraticAlgebra.lift,hg]⟩
    rw [B.adjoin_gen_eq_top] at incl
    exact fun t => incl (show t ∈ (⊤ : Subalgebra ℤ (𝓞 (CyclotomicField 3 ℚ))) by trivial)
  exact ⟨AlgEquiv.ofBijective f ⟨inj,surj⟩⟩

private theorem eisenstein_unit_six (u : (𝓞 (CyclotomicField 3 ℚ))ˣ) : (u : 𝓞 (CyclotomicField 3 ℚ))^6=1 := by
  let _ : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) := CyclotomicField.isCyclotomicExtension 3 ℚ
  let z := IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)
  have hz : IsPrimitiveRoot z 3 := IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)
  have mem := IsCyclotomicExtension.Rat.Three.Units.mem hz u
  let w := hz.toInteger
  have h3 : w^3=1 := hz.toInteger_cube_eq_one
  have h6 : w^6=1 := by rw [show 6=3*2 by decide,pow_mul,h3,one_pow]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp only [Units.val_one,Units.val_neg,Units.val_pow_eq_pow_val,IsUnit.unit_spec,one_pow,Even.neg_pow (by decide : Even 6)]
  all_goals first | exact h6 | change (w^2)^6=1; rw [←pow_mul, Nat.mul_comm, pow_mul,h6,one_pow]

private theorem eisenstein_extract {x y z : (QuadraticAlgebra ℤ (-1) (-1))} {d : ℕ} (pd : d.Prime) (hd : 3 < d)
    (cop : IsCoprime x y) (prod : x*y=z^d) : ∃ a : (QuadraticAlgebra ℤ (-1) (-1)), a^d=x := by
  obtain ⟨f⟩ := eisenstein_model
  let _ : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) := CyclotomicField.isCyclotomicExtension 3 ℚ
  let _ : IsPrincipalIdealRing (𝓞 (CyclotomicField 3 ℚ)) := IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
  obtain ⟨a,u,hu⟩ := exists_associated_pow_of_mul_eq_pow' (cop.map f.toRingHom)
    (show f x*f y=(f z)^d by rw [←map_mul,prod,map_pow])
  have h6 := eisenstein_unit_six u
  have od := pd.odd_of_ne_two (by omega)
  have nd3 : ¬3 ∣ d := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pd).mp h
    omega
  obtain ⟨j,hj⟩ := od
  have key (e : ℕ) (he : e%6=1) : (u : 𝓞 (CyclotomicField 3 ℚ))^e=u := by
    have rep : e=e%6+6*(e/6) := (Nat.mod_add_div _ _).symm
    conv_lhs => rw [rep,pow_add,pow_mul,he,h6,one_pow,mul_one,pow_one]
  have root : ∃ v : 𝓞 (CyclotomicField 3 ℚ), v^d=u := by
    rcases (show d%6=1 ∨ d%6=5 by omega) with h|h
    · exact ⟨u,key d h⟩
    · exact ⟨(u : 𝓞 (CyclotomicField 3 ℚ))^5,by rw [←pow_mul]; exact key _ (by omega)⟩
  obtain ⟨v,hv⟩ := root
  refine ⟨f.symm (a*v),f.injective ?_⟩
  rw [map_pow,AlgEquiv.apply_symm_apply,mul_pow,hv,hu]
  rfl

private theorem eisenstein_im_dvd (v : (QuadraticAlgebra ℤ (-1) (-1))) (n : ℕ) : v.im ∣ (v^n).im := by
  induction n with
  | zero => simp [QuadraticAlgebra.im_one]
  | succ n ih =>
    rw [pow_succ,QuadraticAlgebra.im_mul]
    exact dvd_add (dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)) (dvd_mul_left _ _)

/-- A prime square plus three cannot be four times a nontrivial power
with prime exponent larger than three. -/
theorem square_plus_three_exclusion {p y d : ℕ} (pp : p.Prime) (hp : 3 < p)
    (pd : d.Prime) (hd : 3 < d) (hy : 1 < y) (eq : p^2+3=4*y^d) : False := by
  obtain ⟨w,hw⟩ := pp.odd_of_ne_two (by omega)
  let α : (QuadraticAlgebra ℤ (-1) (-1)) := ⟨(w:ℤ)+1,1⟩
  have pw : (p:ℤ)=2*(w:ℤ)+1 := by exact_mod_cast hw
  have ppow : (p:ℤ)^2+3=4*(y:ℤ)^d := by exact_mod_cast eq
  have tr : α+star α=(p:(QuadraticAlgebra ℤ (-1) (-1))) := by
    ext <;> simp [α]
    omega
  have diff : (α-star α)^2=(-3:(QuadraticAlgebra ℤ (-1) (-1))) := by
    ext <;> simp [α,pow_two,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]
  have normα : α.norm=(y:ℤ)^d := by
    simp [α,QuadraticAlgebra.norm_def]
    rw [pw] at ppow
    nlinarith
  have copZ : IsCoprime (p:ℤ) 3 := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    change p.Coprime 3
    exact pp.coprime_iff_not_dvd.mpr (by intro h; have := Nat.le_of_dvd (by decide : 0<3) h; omega)
  obtain ⟨u,v,uv⟩ := copZ
  have cop : IsCoprime α (star α) := by
    refine ⟨(u:(QuadraticAlgebra ℤ (-1) (-1)))-v*(α-star α),(u:(QuadraticAlgebra ℤ (-1) (-1)))+v*(α-star α),?_⟩
    calc
      _ = (u:(QuadraticAlgebra ℤ (-1) (-1)))*(α+star α)-v*(α-star α)^2 := by ring
      _ = 1 := by rw [tr,diff]; simpa using (show (u:(QuadraticAlgebra ℤ (-1) (-1)))*(p:(QuadraticAlgebra ℤ (-1) (-1)))+(v:(QuadraticAlgebra ℤ (-1) (-1)))*3=1 by exact_mod_cast uv)
  have prod : α*star α=(y:(QuadraticAlgebra ℤ (-1) (-1)))^d := by
    rw [← QuadraticAlgebra.algebraMap_norm_eq_mul_star,normα,map_pow]
    rfl
  obtain ⟨a,ha⟩ := eisenstein_extract pd hd cop prod
  have idiv := eisenstein_im_dvd a d
  rw [ha] at idiv
  change a.im ∣ 1 at idiv
  have absim : a.im.natAbs=1 := by
    obtain ⟨k,hk⟩ := idiv
    apply Nat.dvd_one.mp
    exact ⟨k.natAbs,by simpa [Int.natAbs_mul] using congrArg Int.natAbs hk⟩
  have ims : a.im^2=1 := by
    have hh := congrArg (fun t : ℕ => (t:ℤ)^2) absim
    simpa [Int.natCast_natAbs,sq_abs] using hh
  let S : ℤ := 2*a.re-a.im
  have ts : a+star a=(S:(QuadraticAlgebra ℤ (-1) (-1))) := by
    ext
    · change a.re+(a.re+(-1)*a.im)=2*a.re-a.im
      ring
    · change a.im+ -a.im=0
      omega
  have ad := (pd.odd_of_ne_two (by omega)).add_dvd_pow_add_pow a (star a)
  rw [ts,←star_pow,ha,tr] at ad
  obtain ⟨k,hk⟩ := ad
  have div : S ∣ (p:ℤ) := ⟨k.re,by simpa using congrArg QuadraticAlgebra.re hk⟩
  have absdiv : S.natAbs ∣ p := by
    obtain ⟨b,hb⟩ := div
    exact ⟨b.natAbs,by simpa [Int.natAbs_mul] using congrArg Int.natAbs hb⟩
  have nform : 4*a.norm=S^2+3 := by
    simp only [QuadraticAlgebra.norm_def,S]
    linear_combination 3*ims
  have hn : a.norm^d=(y:ℤ)^d := by rw [←map_pow,ha,normα]
  have ybig : (1:ℤ)<(y:ℤ)^d := one_lt_pow₀ (by exact_mod_cast hy) pd.ne_zero
  have big : 1 < a.norm := by
    by_contra! le
    have pos : 0 < a.norm := by nlinarith [sq_nonneg S]
    have one : a.norm=1 := by omega
    rw [one,one_pow] at hn
    omega
  have gt : a.norm < a.norm^d := by simpa using pow_lt_pow_right₀ big (show 1 < d by omega)
  have hs : (S.natAbs:ℤ)^2=S^2 := by rw [Int.natCast_natAbs,sq_abs]
  rcases (Nat.dvd_prime pp).mp absdiv with one|same
  · rw [one] at hs
    norm_num at hs
    omega
  · rw [same] at hs
    nlinarith

/-- For a surviving prime square, the third cofactor's odd exponent must be a power of three. -/
theorem square_third_exponent {p r b : ℕ} (pp : p.Prime) (hp : 3 < p)
    (hr : 1 < r) (ob : Odd b) (eq : p^2+3=4*r^b) :
    ∃ k : ℕ, b=3^k := by
  obtain ⟨w,hw⟩ := ob
  refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
  intro d pd dd
  by_contra ne
  have d2 : d≠2 := by rintro rfl; omega
  have big : 3 < d := by have := pd.two_le; omega
  obtain ⟨j,hj⟩ := dd
  have jp : j ≠ 0 := by rintro rfl; simp at hj; omega
  apply square_plus_three_exclusion pp hp pd big (Nat.one_lt_pow jp hr)
  rw [←pow_mul,Nat.mul_comm j d,←hj,eq]


private theorem gaussian_unit_four (u : GaussianIntˣ) : (u:GaussianInt)^4=1 := by
  have un := (Zsqrtd.norm_eq_one_iff' (by decide : (-1:ℤ)≤0) (u:GaussianInt)).mpr u.isUnit
  generalize (u:GaussianInt)=v at un ⊢
  obtain ⟨a,b⟩ := v
  change a*a-(-1)*b*b=1 at un
  have a₁ : -1 ≤ a := by nlinarith [sq_nonneg b]
  have a₂ : a ≤ 1 := by nlinarith [sq_nonneg b]
  have b₁ : -1 ≤ b := by nlinarith [sq_nonneg a]
  have b₂ : b ≤ 1 := by nlinarith [sq_nonneg a]
  interval_cases a <;> interval_cases b <;> norm_num at un
  all_goals decide +kernel

private theorem gaussian_odd_root {u : GaussianInt} (hu : u^4=1) {d : ℕ} (od : Odd d) :
    ∃ v : GaussianInt, v^d=u := by
  obtain ⟨w,hw⟩ := od
  have key (e : ℕ) (he : e%4=1) : u^e=u := by
    have rep : e=e%4+4*(e/4) := (Nat.mod_add_div _ _).symm
    conv_lhs => rw [rep,pow_add,pow_mul,he,hu,one_pow,mul_one,pow_one]
  rcases (show d%4=1 ∨ d%4=3 by omega) with h|h
  · exact ⟨u,key _ h⟩
  · exact ⟨u^3,by rw [←pow_mul]; exact key _ (by omega)⟩

private theorem gaussian_primitive_divisor {t : ℤ} {p k : ℕ} (ht : ¬2 ∣ t)
    (div : t ∣ (2:ℤ)^k*p) : t.natAbs ∣ p := by
  obtain ⟨h,hh⟩ := div
  have dn : t.natAbs ∣ 2^k*p := ⟨h.natAbs,by simpa [Int.natAbs_mul,Int.natAbs_pow] using congrArg Int.natAbs hh⟩
  have odd : Odd t.natAbs := by rw [Nat.odd_iff]; omega
  exact ((Nat.coprime_two_right.mpr odd).pow_right k).dvd_of_dvd_mul_left dn

private theorem gaussian_im_dvd (v : GaussianInt) (n : ℕ) : v.im ∣ (v^n).im := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

/-- A prime square plus one cannot be twice a nontrivial odd power of an odd number. -/
theorem square_plus_one_odd_exclusion {p y d : ℕ} (pp : p.Prime) (hp : 2 < p)
    (hy : 1 < y) (oy : Odd y) (hd : 1 < d) (od : Odd d) (eq : p^2+1=2*y^d) : False := by
  obtain ⟨w,hw⟩ := pp.odd_of_ne_two (by omega)
  obtain ⟨k,hk⟩ := od
  let I : GaussianInt := ⟨0,1⟩
  let A : GaussianInt := ⟨(w:ℤ)+1,-(w:ℤ)⟩
  have I2 : I^2=-1 := by decide +kernel
  have pair : A+I*star A=1+I := by ext <;> simp [I,A]
  have pcast : (p:ℤ)=2*(w:ℤ)+1 := by exact_mod_cast hw
  have eqZ : (p:ℤ)^2+1=2*(y:ℤ)^d := by exact_mod_cast eq
  have An : A.norm=(y:ℤ)^d := by
    rw [pcast] at eqZ
    simp [A,Zsqrtd.norm_def]
    nlinarith
  have prod : A*star A=(y:GaussianInt)^d := by rw [←Zsqrtd.norm_eq_mul_conj,An]; push_cast; rfl
  have Iprod : (1+I)*(1-I)=2 := by linear_combination -I2
  have cop : IsCoprime A (star A) := by
    obtain ⟨l,hl⟩ : Odd (y^d) := oy.pow
    have oddZ : (y:GaussianInt)^d = 2*(l:GaussianInt)+1 := by exact_mod_cast hl
    refine ⟨star A-(l:GaussianInt)*(1-I),-(l:GaussianInt)*(1-I)*I,?_⟩
    calc
      _ = A*star A-(l:GaussianInt)*((A+I*star A)*(1-I)) := by ring
      _ = 1 := by rw [prod,oddZ,pair,Iprod]; ring
  obtain ⟨z,u,hu⟩ := exists_associated_pow_of_mul_eq_pow' cop prod
  have ii : (-I)^4=1 := by decide +kernel
  have ui : ((u:GaussianInt)*(-I)^k)^4=1 := by
    rw [mul_pow,gaussian_unit_four,one_mul,←pow_mul,Nat.mul_comm,pow_mul,ii,one_pow]
  obtain ⟨v,hv⟩ := gaussian_odd_root ui (show Odd d from ⟨k,hk⟩)
  let h := z*v
  have hpow : h^d=(-I)^k*A := by dsimp [h]; rw [mul_pow,hv,←hu]; ring
  let θ := (1+I)*h
  have prodA : (1+I)*A=(p:GaussianInt)+I := by ext <;> simp [I,A] <;> omega
  have scale : ((1+I)^2)*(-I)=2 := by decide +kernel
  have θpow : θ^d=(((2:ℤ)^k : ℤ):GaussianInt)*((p:GaussianInt)+I) := by
    dsimp [θ]
    rw [mul_pow,hpow,hk,pow_succ,pow_mul]
    push_cast
    calc
      _ = (((1+I)^2)*(-I))^k*((1+I)*A) := by rw [mul_pow]; ring
      _ = _ := by rw [scale,prodA]
  have hnorm : h.norm=(y:ℤ) := by
    apply (show Odd d from ⟨k,hk⟩).pow_injective
    change Zsqrtd.normMonoidHom h ^ d = _
    rw [←map_pow,hpow,map_mul,map_pow]
    change (-I).norm^k*A.norm=_
    rw [show (-I).norm=1 by decide +kernel,one_pow,one_mul,An]
  have θnorm : θ.norm=2*(y:ℤ) := by
    dsimp [θ]
    rw [Zsqrtd.norm_mul,hnorm,show (1+I).norm=2 by decide +kernel]
  have sumsq : θ.re^2+θ.im^2=2*(y:ℤ) := by
    rw [←θnorm,Zsqrtd.norm_def]; ring
  have par : θ.re=h.re-h.im ∧ θ.im=h.re+h.im := by
    constructor
    · simp [θ,I,sub_eq_add_neg]
    · simp [θ,I,add_comm]
  have notboth : ¬(2 ∣ θ.re ∧ 2 ∣ θ.im) := by
    rintro ⟨⟨a,ha⟩,b,hb⟩
    have div : (4:ℤ) ∣ 2*(y:ℤ) := ⟨a^2+b^2,by rw [←sumsq,ha,hb]; ring⟩
    obtain ⟨m,hm⟩ := oy
    omega
  have oi : ¬2 ∣ θ.im := by omega
  have or' : ¬2 ∣ θ.re := by omega
  have imag := gaussian_im_dvd θ d
  have rpow : (θ^d).re=(2:ℤ)^k*p := by
    rw [θpow,Zsqrtd.re_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast]
    simp [I]
  have ipow : (θ^d).im=(2:ℤ)^k := by
    rw [θpow,Zsqrtd.im_mul,Zsqrtd.re_intCast,Zsqrtd.im_intCast]
    simp [I]
  rw [ipow] at imag
  have imag' : θ.im ∣ (2:ℤ)^k*1 := by simpa using imag
  have absI : θ.im.natAbs=1 := Nat.dvd_one.mp (gaussian_primitive_divisor (p:=1) oi imag')
  have real : θ.re ∣ (2:ℤ)^k*p := by
    have dv := (show Odd d from ⟨k,hk⟩).add_dvd_pow_add_pow θ (star θ)
    obtain ⟨s,hs⟩ := dv
    rw [←star_pow] at hs
    refine ⟨s.re,?_⟩
    have cc := congrArg Zsqrtd.re hs
    simp only [Zsqrtd.re_mul,Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_star,Zsqrtd.im_star,rpow] at cc
    nlinarith only [cc]
  have absR := gaussian_primitive_divisor or' real
  have isq : θ.im^2=1 := by
    have he := congrArg (fun t:ℕ => (t:ℤ)^2) absI
    simpa [Int.natCast_natAbs,sq_abs] using he
  have hs : (θ.re.natAbs:ℤ)^2=θ.re^2 := by rw [Int.natCast_natAbs,sq_abs]
  rcases (Nat.dvd_prime pp).mp absR with one|same
  · rw [one] at hs
    norm_num at hs
    omega
  · rw [same] at hs
    have gt : (y:ℤ) < (y:ℤ)^d := by simpa using pow_lt_pow_right₀ (show (1:ℤ)<y by exact_mod_cast hy) hd
    nlinarith

/-- In the surviving square branch the first prime cofactor has exponent one or two. -/
theorem square_first_exponent {p q a : ℕ} (pp : p.Prime) (hp : 2 < p) (oq : Odd q)
    (hq : 1 < q) (ap : 0 < a) (no4 : ¬4 ∣ a) (eq : p^2+1=2*q^a) : a=1 ∨ a=2 := by
  have pure : a=2^a.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd ap.ne' (by
    intro d pd dd
    by_contra ne
    obtain ⟨j,hj⟩ := dd
    have jpos : j ≠ 0 := by rintro rfl; simp at hj; omega
    apply square_plus_one_odd_exclusion pp hp (Nat.one_lt_pow jpos hq) oq.pow pd.one_lt (pd.odd_of_ne_two ne)
    rw [←pow_mul,Nat.mul_comm j d,←hj,eq])
  generalize a.primeFactorsList.length=e at pure
  have low : e < 2 := by
    by_contra! he
    exact no4 (pure ▸ pow_dvd_pow (2:ℕ) he)
  interval_cases e <;> simp_all


/-- At every sufficiently large odd prime, find a later or equal integer
with two distinct prime factors larger than the offset from its predecessor. -/
def H1 : Prop := ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B < p →
    (∀ x : ℕ, 1<x → p≠x^4+1) →
    ((∀ e : ℕ, p ≠ 2^e+1) ∧ ∃ q r a b c d : ℕ, q.Prime ∧ r.Prime ∧ 2<q ∧ 3<r ∧
      q≠r ∧ 0<a ∧ 0<b ∧ 0<c ∧ 0<d ∧ (a=1 ∨ c=1) ∧ p+1=2^a*q^b ∧ p+3=2^c*r^d) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p+d ∧ s ∣ p+d

/-- A prime square needs a witness only if three successive values have the prescribed factorizations
with the specified residues and exponents. -/
def H2 : Prop := ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B < p^2 →
    (∃ q r b : ℕ, q.Prime ∧ r.Prime ∧ q≠r ∧ q%4=1 ∧ r%3=1 ∧
      (∃ k : ℕ, b=3^k) ∧ p^2+3=4*r^b ∧
      (p^2+1=2*q ∨ (b=1 ∧ p^2+1=2*q^2))) →
    (∃ t c e : ℕ, t.Prime ∧ 3 < t ∧ (t%8=1 ∨ t%8=3) ∧
      0 < c ∧ 0 < e ∧ p^2+2=3^c*t^e) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^2+d ∧ s ∣ p^2+d

/-- The remaining odd exponents are primes at least eleven, and the only
bases that need be considered are Mersenne primes. -/
def H3 : Prop := ∃ B : ℕ, ∀ p r : ℕ, p.Prime → Odd p → (∃ b : ℕ, p+1=2^b) →
    r.Prime → 11 ≤ r → B < p^r →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^r+d ∧ s ∣ p^r+d

theorem main : H1 → H2 → H3 → type_of% @Erdos889.erdos_889.variants.v1_eq_1_finite := by
  rintro ⟨A, primeCase⟩ ⟨B0, narrowSquares⟩ ⟨C, mersenneCase⟩
  have squares : ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B < p^2 →
      ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
        q ∣ p^2+d ∧ s ∣ p^2+d := by
    refine ⟨B0+25, ?_⟩
    intro p pp op large
    by_contra missing
    have greater : 5 < p := by
      by_contra! small
      have lim := Nat.pow_le_pow_left small 2
      norm_num at lim
      omega
    obtain ⟨q,r,a,b,pq,pr,ne,rq,rr,ap,no4,bp,ob,f1,f3⟩ :=
      square_survivor pp op (by omega) missing
    have cb := square_third_exponent pp (by omega) pr.one_lt ob f3
    have qlarge : 3 < q := by have := pq.two_le; omega
    have qo := pq.odd_of_ne_two (by omega)
    have rOdd := pr.odd_of_ne_two (by omega)
    have first : p^2+1=2*q ∨ (b=1 ∧ p^2+1=2*q^2) := by
      rcases square_first_exponent pp (by omega) qo pq.one_lt ap no4 f1 with one|two
      · left; simpa [one] using f1
      · rw [two] at f1
        have next : q^2+1=2*r^b := by omega
        have b1 : b=1 := by
          by_contra bad
          exact square_plus_one_odd_exclusion pq (by omega) pr.one_lt rOdd (by omega) ob next
        exact Or.inr ⟨b1,f1⟩
    exact missing (narrowSquares p pp op (by omega)
      ⟨q,r,b,pq,pr,ne,rq,rr,cb,f3,first⟩ (square_middle pp op greater missing))
  obtain ⟨B, dyadicCase⟩ := dyadic_of_prime_squares squares
  refine (Set.finite_le_nat (A+B+C+60)).subset ?_
  intro n hn
  change v_l 1 n = 1 at hn
  change n ≤ A+B+C+60
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
          apply primeCase p pp op (by omega)
          · intro x hx eq
            have nx : n=x^4 := by omega
            have sol : v_l 1 (x^4)=1 := nx ▸ hn
            rcases (higher_perfect_power hx (by decide : 3≤4)).mp sol with h|h <;> omega
          · exact prime_successor_survivor pp he (by omega) hn
        | succ t => exact dyadicCase p (t+1) pp op (by omega) (by omega)
      · have exc : ¬(a=5 ∨ a=7) := fun h => fifth_seventh_exclusion pp.one_lt h he hn
        have a11 : 11 ≤ a := by
          obtain ⟨w, hw⟩ := oa
          have := pr.two_le
          omega
        exact mersenneCase p a pp op base pr a11 (by omega)
    obtain ⟨d,q,s,pq,ps,ne,hq,hs,dq,ds⟩ := witness
    have equal : n+(d+1)=p^a+d := by omega
    exact two_primes (k:=d+1) (by omega) pq ps ne hq hs (equal ▸ dq) (equal ▸ ds) hn
  · rcases (odd_classification od).mp hn with h|h|h|h <;> omega

end OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

