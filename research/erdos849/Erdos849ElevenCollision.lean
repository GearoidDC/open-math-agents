import Erdos849PowerCollision
import Mathlib.Tactic.IntervalCases

/-! Arithmetic exclusions for a value above a googol represented in columns
7 ≤ j < d ≤ 10, given a suitable prime-power divisor of the value. -/

namespace Erdos849ElevenCollision

open Erdos849NearPrimeCongruence

private structure Bounds where
  threshold : ℕ
  cofactor : ℕ
  scale : ℕ
  upperWeight : ℕ
  lowerWeight : ℕ
  otherWeight : ℕ
  ratio : ℕ

private def bounds (d : ℕ) : Bounds :=
  if d = 8 then ⟨10^12, 200, 300, 280, 8, 140, 18⟩
  else if d = 9 then ⟨5*10^11, 602, 650, 630, 72, 280, 4⟩
  else ⟨4*10^10, 43, 1300, 1260, 90, 630, 7⟩

/-- For columns 8, 9, and 10 the cofactor limits are 200, 602, and 43. -/
def cofactorLimit (d : ℕ) := (bounds d).cofactor

private def scaleFactor (d : ℕ) : ℕ := ((bounds d).cofactor+1)^2 * (bounds d).scale

set_option maxRecDepth 10000 in
private theorem constants :
    ∀ d ∈ Finset.Icc 8 10, ∀ j ∈ Finset.Ico 7 d,
      (bounds d).threshold^d ≤ d.factorial * 10^100 ∧
      (scaleFactor d)^j * j.factorial < (bounds d).threshold^(2*j-d) * d.factorial ∧
      (bounds d).otherWeight ≤ (bounds d).lowerWeight * (bounds d).ratio ∧
      0 < (bounds d).lowerWeight ∧
      ∀ s ∈ Finset.range d, (d=8 ∨ (1≤s ∧ s+1<d)) →
        (bounds d).lowerWeight ≤ weight d s ∧ weight d s ≤ (bounds d).upperWeight ∧
          ∀ r ∈ Finset.range j, weight j r ≤ (bounds d).otherWeight := by decide

private theorem threshold_le {n d j : ℕ} (hd : d ∈ Finset.Icc 8 10)
    (hj : j ∈ Finset.Ico 7 d) (ha : 10^100 < n.choose d) : (bounds d).threshold ≤ n := by
  by_contra! h
  have hpos : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
  have lo := Nat.mul_lt_mul_of_pos_left ha (Nat.factorial_pos d)
  have hi := n.descFactorial_le_pow d
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hi
  have hp := Nat.pow_lt_pow_left h (by omega : d≠0)
  exact (lt_of_lt_of_le (lt_trans (lo.trans_le hi) hp) (constants d hd j hj).1).false

/-- If the square of the higher-column row is bounded by K times the
    lower-column row, the equality forces an upper bound on n^(2j−d). -/
theorem square_cutoff {n m d j K : ℕ} (hn : 0 < n) (hdj : d ≤ 2*j)
    (hscale : n^2 ≤ K*(m+1-j)) (he : m.choose j = n.choose d) :
    n^(2*j-d)*d.factorial ≤ K^j*j.factorial := by
  have low := m.pow_sub_le_descFactorial j
  rw [Nat.descFactorial_eq_factorial_mul_choose, he] at low
  have high := n.descFactorial_le_pow d
  rw [Nat.descFactorial_eq_factorial_mul_choose] at high
  have hx : (n^(2*j-d)*d.factorial)*n^d ≤ (K^j*j.factorial)*n^d := calc
    _ = (n^2)^j*d.factorial := by
      rw [← pow_mul, mul_right_comm, ← pow_add, Nat.sub_add_cancel hdj]
    _ ≤ (K*(m+1-j))^j*d.factorial := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hscale _)
    _ = (K^j*d.factorial)*(m+1-j)^j := by rw [mul_pow]; ring
    _ ≤ (K^j*d.factorial)*(j.factorial*n.choose d) := Nat.mul_le_mul_left _ low
    _ = (K^j*j.factorial)*(d.factorial*n.choose d) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ high
  exact Nat.le_of_mul_le_mul_right hx (pow_pos hn _)

private theorem above_scale {d b P s : ℕ} (hd : d ∈ Finset.Icc 8 10)
    (hb : b ≤ cofactorLimit d) (hs : s < d)
    (hn : (bounds d).threshold ≤ b*P+s) : 10^8 ≤ P := by
  have hmul := Nat.mul_le_mul_right P hb
  obtain ⟨hd₁, hd₂⟩ := Finset.mem_Icc.mp hd
  interval_cases d <;> norm_num [cofactorLimit, bounds] at hmul hn <;> omega

private theorem no_wrap {d j b q s r P : ℕ}
    (hd : d ∈ Finset.Icc 8 10) (hj : j ∈ Finset.Ico 7 d)
    (hb : b ≤ cofactorLimit d) (hs : s < d) (hint : d=8 ∨ (1≤s ∧ s+1<d)) (hr : r < j)
    (hn : (bounds d).threshold ≤ b*P+s) (hP : 10^8 ≤ P)
    (he : (q*P+r).choose j = (b*P+s).choose d) :
    weight d s*q + weight j r*b < P := by
  obtain ⟨hd₁, hd₂⟩ := Finset.mem_Icc.mp hd
  obtain ⟨hj₁, hj₂⟩ := Finset.mem_Ico.mp hj
  have cert := constants d hd j hj
  have hw := cert.2.2.2.2 s (Finset.mem_range.mpr hs) hint
  by_contra! hwrap
  have hrough : P ≤ (bounds d).upperWeight*q + (bounds d).otherWeight*(bounds d).cofactor :=
    hwrap.trans (Nat.add_le_add (Nat.mul_le_mul_right _ hw.2.1)
      (Nat.mul_le_mul (hw.2.2 r (Finset.mem_range.mpr hr)) hb))
  have hq : P ≤ (bounds d).scale*(q-1) := by
    interval_cases d <;> norm_num [bounds] at hrough ⊢ <;> omega
  have hnP : b*P+s ≤ ((bounds d).cofactor+1)*P := by
    have hmul := Nat.mul_le_mul_right P hb
    unfold cofactorLimit at hmul
    rw [Nat.succ_mul]; omega
  have hqpos : 1 ≤ q := by
    by_contra! hz
    rw [show q-1=0 by omega, mul_zero] at hq
    omega
  have hmq : (q-1)*P+P=q*P := by rw [← Nat.succ_mul]; congr 1; omega
  have hscale : (b*P+s)^2 ≤ scaleFactor d*(q*P+r+1-j) := calc
    _ ≤ (((bounds d).cofactor+1)*P)^2 := Nat.pow_le_pow_left hnP _
    _ = ((bounds d).cofactor+1)^2*(P*P) := by ring
    _ ≤ ((bounds d).cofactor+1)^2*(((bounds d).scale*(q-1))*P) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hq)
    _ = scaleFactor d*((q-1)*P) := by unfold scaleFactor; ring
    _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have hnpos : 0<b*P+s := by
    by_contra! hnz
    interval_cases d <;> norm_num [bounds] at hn <;> omega
  have hcontra := square_cutoff hnpos (by omega : d≤2*j) hscale he
  exact cert.2.1.not_ge ((Nat.mul_le_mul_right d.factorial
    (Nat.pow_le_pow_left hn (2*j-d))).trans hcontra)

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) : n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Exclude all six close-column pairs with the cofactor selected from a row
    having at most ten distinct prime divisors in its binomial value. -/
theorem no_collision {p e b s d m j : ℕ}
    (hd₁ : 8 ≤ d) (hd₂ : d ≤ 10) (hj₁ : 7 ≤ j) (hj₂ : j < d)
    (hp : p.Prime) (hpp : 11 ≤ p) (hbpos : 0 < b) (hb : b ≤ cofactorLimit d)
    (hs : s < d) (hint : d=8 ∨ (1≤s ∧ s+1<d)) (ha : 10^100 < (b*p^e+s).choose d)
    (hm : 2*j ≤ m) (hdvd : p^e ∣ m.choose j) :
    m.choose j ≠ (b*p^e+s).choose d := by
  intro he
  have hd := Finset.mem_Icc.mpr (And.intro hd₁ hd₂)
  have hj := Finset.mem_Ico.mpr (And.intro hj₁ hj₂)
  let P := p^e
  let n := b*P+s
  let q := m/P
  let r := m%P
  have hn : (bounds d).threshold ≤ n := threshold_le hd hj ha
  have hP : 10^8 ≤ P := above_scale hd hb hs hn
  have hmq : q*P+r=m := Nat.div_add_mod' m P
  have hr : r < j := Erdos849PrimeHosts.residue_lt_column hp (by omega) (by omega) hdvd
  have hqpos : 1 ≤ q := by
    by_cases hz : q=0
    · rw [hz, zero_mul, zero_add] at hmq
      omega
    · exact Nat.one_le_iff_ne_zero.mpr hz
  have hqp : P ≤ q*P := by simpa using Nat.mul_le_mul_right P hqpos
  have hbp : P ≤ b*P := by simpa using Nat.mul_le_mul_right P (show 1≤b by omega)
  have hev : (q*P+r).choose j = (b*P+s).choose d := hmq ▸ he
  have hlt := no_wrap hd hj hb hs hint hr hn hP hev
  have hepos : 0 < e := by
    by_contra! h
    have hz : e=0 := Nat.eq_zero_of_le_zero h
    simp [P,hz] at hP
  have hu (t : ℕ) (ht : 1 ≤ t) (ht' : t < max d j) : IsUnit (t : ZMod P) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hepos).mpr (Nat.not_dvd_of_pos_of_lt ht (by omega))
  have hwp : 0 < weight j r*b := Nat.mul_pos (Nat.mul_pos (by omega) (Nat.choose_pos (by omega))) hbpos
  have heq : weight d s*q = weight j r*b := by
    rcases Erdos849PowerCollision.signed_collision (by omega : 0<P) hs hr
        (by omega) (by omega) hu hev.symm with h | h
    · exact h.eq_of_lt_of_lt (by omega) (by omega)
    · have := Nat.le_of_dvd (by omega) h
      omega
  have cert := (constants d hd j hj).2.2
  have hw := cert.2.2 s (Finset.mem_range.mpr hs) hint
  have hq : q ≤ (bounds d).ratio*b := by
    apply Nat.le_of_mul_le_mul_left _ cert.2.1
    calc
      _ ≤ weight d s*q := Nat.mul_le_mul_right _ hw.1
      _ = weight j r*b := heq
      _ ≤ (bounds d).otherWeight*b := Nat.mul_le_mul_right _ (hw.2.2 r (Finset.mem_range.mpr hr))
      _ ≤ ((bounds d).lowerWeight*(bounds d).ratio)*b := Nat.mul_le_mul_right _ cert.1
      _ = _ := Nat.mul_assoc _ _ _
  have hnear : m ≤ (bounds d).ratio*n+d := by
    have hmul := Nat.mul_le_mul_right P hq
    rw [Nat.mul_assoc] at hmul
    have hscale := Nat.mul_le_mul_left (bounds d).ratio (Nat.le_add_right (b*P) s)
    dsimp only [n]
    omega
  have hentry : n.choose d ≤ m.choose (d-1) := he.ge.trans (half_mono (by omega) (by omega))
  have hd' : d-1+1=d := by omega
  have hbound : d*((bounds d).ratio+1)^(d-1) < n-(d-1) := by
    interval_cases d <;> norm_num [bounds] at hn ⊢ <;> omega
  have hfar := Erdos849PowerCollision.next_row_bound (k := d-1) (c := (bounds d).ratio+1)
    (by rw [hd']; exact hbound) (by rw [hd']; exact hentry)
  interval_cases d <;> norm_num [bounds] at hn hnear hfar <;> omega

end Erdos849ElevenCollision
