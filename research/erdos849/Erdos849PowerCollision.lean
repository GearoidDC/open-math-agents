import Erdos849NearPrimeCongruence
import Erdos849PrimeHosts

namespace Erdos849PowerCollision
open Erdos849NearPrimeCongruence

private theorem above {P b k : ℕ}
    (units : ∀ t, 1 ≤ t → t ≤ k → IsUnit (t : ZMod P)) :
    (((b*P+k).choose k : ℕ) : ZMod P) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hu := units (k+1) (by omega) (by omega)
    have h := congrArg (fun z : ℕ => (z : ZMod P)) (Nat.add_one_mul_choose_eq (b*P+k) k)
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_self,
      mul_zero, zero_add, ih (fun t ht htk => units t ht (by omega)), mul_one] at h
    apply hu.mul_left_inj.mp
    simpa [Nat.cast_add, Nat.cast_one, Nat.add_assoc] using h.symm

private theorem below {P b k : ℕ} (hb : 1 ≤ b*P) (hbig : k < b*P)
    (units : ∀ t, 1 ≤ t → t ≤ k → IsUnit (t : ZMod P)) :
    (((b*P-1).choose k : ℕ) : ZMod P) = (-1)^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hu := units (k+1) (by omega) (by omega)
    have h := congrArg (fun z : ℕ => (z : ZMod P)) (Nat.choose_succ_right_eq (b*P-1) k)
    push_cast [Nat.cast_sub (by omega : k ≤ b*P-1), Nat.cast_sub hb] at h
    rw [ih (by omega) (fun t ht htk => units t ht (by omega))] at h
    simp only [ZMod.natCast_self, mul_zero, zero_sub] at h
    apply hu.mul_left_inj.mp
    push_cast
    rw [h, pow_succ]
    ring

private theorem product_mod {P b d s : ℕ} (hs : s < d) (hd : d ≤ b*P)
    (units : ∀ t, 1 ≤ t → t < d → IsUnit (t : ZMod P)) :
    (residueProduct (b*P) d s : ZMod P) = (-1)^(d-1-s) := by
  rw [residueProduct, Nat.cast_mul, above (fun t ht htk => units t ht (by omega)),
    below (by omega) (by omega) (fun t ht htk => units t ht (by omega)), one_mul]

/-- For a modulus whose small factorials are units, two rows sitting just beyond
    multiples bP and qP give a signed congruence of their binomial weights. -/
theorem signed_collision {P d j s r b q : ℕ} (hP : 0 < P) (hs : s < d) (hr : r < j)
    (hd : d ≤ b*P) (hj : j ≤ q*P)
    (units : ∀ t, 1 ≤ t → t < max d j → IsUnit (t : ZMod P))
    (he : (b*P+s).choose d = (q*P+r).choose j) :
    weight d s*q ≡ weight j r*b [MOD P] ∨ P ∣ weight d s*q + weight j r*b := by
  have h₁ := isolate (b*P) d s (by omega) hs
  have h₂ := isolate (q*P) j r (by omega) hr
  have hcross : P * ((weight d s*q) * residueProduct (q*P) j r) =
      P * ((weight j r*b) * residueProduct (b*P) d s) := by
    calc
      _ = weight d s * (q*P * residueProduct (q*P) j r) := by ring
      _ = weight j r * (weight d s * (b*P+s).choose d) := by rw [← h₂, ← he]; ring
      _ = _ := by rw [h₁]; ring
  have hz := congrArg (fun x : ℕ => (x : ZMod P)) (Nat.eq_of_mul_eq_mul_left hP hcross)
  have h₃ := product_mod hs hd (fun t ht htd => units t ht (by omega))
  have h₄ := product_mod hr hj (fun t ht htj => units t ht (by omega))
  simp only [Nat.cast_mul, h₃, h₄] at hz
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_zero_iff]
  push_cast
  rcases neg_one_pow_eq_or (ZMod P) (d-1-s) with h₅ | h₅ <;>
    rcases neg_one_pow_eq_or (ZMod P) (j-1-r) with h₆ | h₆ <;>
    simp only [h₅,h₆,mul_one,mul_neg] at hz <;> first
    | exact Or.inl hz
    | exact Or.inl (neg_inj.mp hz)
    | exact Or.inr (by linear_combination hz)
    | exact Or.inr (by linear_combination -hz)

private theorem no_wrap {P d j s r b q : ℕ} (hP : 10^9 ≤ P) (hb : b ≤ 315)
    (hj : 7 ≤ j) (hjd : j < d) (hd : d ≤ 9) (hs : s < d) (hr : r < j)
    (he : (q*P+r).choose j = (b*P+s).choose d) :
    weight d s*q + weight j r*b < P := by
  have nums : ∀ D ∈ Finset.range 10, ∀ J ∈ Finset.range D, 7 ≤ J →
      ∀ S ∈ Finset.range D, ∀ R ∈ Finset.range J,
      weight D S ≤ 630 ∧ weight J R ≤ 280 := by decide
  have ⟨hD,hJ⟩ := nums d (Finset.mem_range.mpr (by omega)) j (Finset.mem_range.mpr hjd)
    hj s (Finset.mem_range.mpr hs) r (Finset.mem_range.mpr hr)
  by_contra! hn
  have hrough : P ≤ 630*q+280*315 :=
    hn.trans (Nat.add_le_add (Nat.mul_le_mul_right q hD) (Nat.mul_le_mul hJ hb))
  let x := q-1
  have hx : 10^6 ≤ x := by dsimp [x]; omega
  have hpq : P ≤ 1000*x := by dsimp [x]; omega
  have hxq : x*P+P=q*P := by rw [← Nat.succ_mul]; congr 1; dsimp [x]; omega
  have hleft := (q*P+r).pow_sub_le_descFactorial j
  have hright := (b*P+s).descFactorial_le_pow d
  rw [Nat.descFactorial_eq_factorial_mul_choose, he] at hleft
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hright
  have hscale : b*P+s ≤ 316*P := by
    have := Nat.mul_le_mul_right P hb
    omega
  have hxj : (x*P)^j ≤ (316*P)^d := calc
    _ ≤ (q*P+r+1-j)^j := Nat.pow_le_pow_left (by omega) j
    _ ≤ j.factorial*(b*P+s).choose d := hleft
    _ ≤ d.factorial*(b*P+s).choose d := Nat.mul_le_mul_right _ (Nat.factorial_le hjd.le)
    _ ≤ (b*P+s)^d := hright
    _ ≤ _ := Nat.pow_le_pow_left hscale d
  rw [mul_pow,mul_pow] at hxj
  have hpow : P^d = P^(d-j)*P^j := by rw [← pow_add, Nat.sub_add_cancel hjd.le]
  rw [hpow, ← mul_assoc] at hxj
  have hxj' := Nat.le_of_mul_le_mul_right hxj (pow_pos (by omega : 0<P) j)
  have h₇ : x^7 ≤ 316^9*(1000*x)^2 := calc
    _ ≤ x^j := Nat.pow_le_pow_right (by omega) hj
    _ ≤ 316^d*P^(d-j) := hxj'
    _ ≤ 316^9*P^2 := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hd)
      (Nat.pow_le_pow_right (by omega) (by omega))
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpq 2)
  have hcompact : x^5*x^2 ≤ (316^9*1000^2)*x^2 := by
    calc
      _ = x^7 := by ring
      _ ≤ _ := h₇
      _ = _ := by ring
  have hu := Nat.le_of_mul_le_mul_right hcompact (pow_pos (by omega : 0<x) 2)
  have hl := Nat.pow_le_pow_left hx 5
  omega

/-- Every admissible collision in these columns forces an *integer* identity
    of the small weights when the host prime power exceeds a billion. -/
theorem exact_weights {p e b s d m j : ℕ} (hp : p.Prime) (hpp : 11 ≤ p)
    (hP : 10^9 ≤ p^e) (hbpos : 0 < b) (hb : b ≤ 315)
    (hj : 7 ≤ j) (hjd : j < d) (hd : d ≤ 9) (hs : s < d) (hm : 2*j ≤ m)
    (hdvd : p^e ∣ m.choose j) (he : m.choose j = (b*p^e+s).choose d) :
    ∃ q r : ℕ, r < j ∧ q*p^e+r=m ∧ weight d s*q = weight j r*b := by
  let P := p^e
  have hpow : 10^9 ≤ P := hP
  let q := m/P
  let r := m%P
  have hr : r < j := Erdos849PrimeHosts.residue_lt_column hp (by omega) (by omega) hdvd
  have hmq : q*P+r=m := Nat.div_add_mod' m P
  have hqpos : 0 < q := by
    by_contra! hn
    rw [Nat.eq_zero_of_le_zero hn, zero_mul, zero_add] at hmq
    omega
  have hbp : P ≤ b*P := by simpa using Nat.mul_le_mul_right P (show 1 ≤ b by omega)
  have hqp : P ≤ q*P := by simpa using Nat.mul_le_mul_right P (show 1 ≤ q by omega)
  have he' : (q*P+r).choose j = (b*P+s).choose d := hmq ▸ he
  have hlt := no_wrap hpow hb hj hjd hd hs hr he'
  have hepos : 0 < e := by
    cases e with
    | zero => norm_num at hP
    | succ => omega
  have hu (t : ℕ) (ht : 1 ≤ t) (ht' : t < max d j) : IsUnit (t : ZMod P) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp hepos).mpr (Nat.not_dvd_of_pos_of_lt ht (by omega))
  have hwp : 0 < weight j r*b := Nat.mul_pos (Nat.mul_pos (by omega) (Nat.choose_pos (by omega))) hbpos
  refine ⟨q, r, hr, hmq, ?_⟩
  rcases signed_collision (by omega : 0<P) hs hr (by omega) (by omega) hu he'.symm with h | h
  · exact h.eq_of_lt_of_lt (by omega) (by omega)
  · have := Nat.le_of_dvd (by omega) h
    omega

theorem next_row_bound {n m k c : ℕ} (hlarge : (k+1)*c^k < n-k)
    (he : n.choose (k+1) ≤ m.choose k) : c*(n-k) < m := by
  by_contra! hm
  have hleft := n.pow_sub_le_descFactorial (k+1)
  have hright := m.descFactorial_le_pow k
  rw [Nat.descFactorial_eq_factorial_mul_choose, show n+1-(k+1)=n-k by omega] at hleft
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hright
  have hh : (n-k)*(n-k)^k ≤ ((k+1)*c^k)*(n-k)^k := calc
    _ = (n-k)^(k+1) := by ring
    _ ≤ (k+1).factorial*n.choose (k+1) := hleft
    _ ≤ (k+1).factorial*m.choose k := Nat.mul_le_mul_left _ he
    _ = (k+1)*(k.factorial*m.choose k) := by rw [Nat.factorial_succ]; ring
    _ ≤ (k+1)*m^k := Nat.mul_le_mul_left _ hright
    _ ≤ (k+1)*(c*(n-k))^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
    _ = _ := by rw [mul_pow]; ring
  have := Nat.le_of_mul_le_mul_right hh (pow_pos (by omega : 0<n-k) k)
  omega

/-- The eighth-column parity obstruction works for any odd cofactor up to 315. -/
theorem no_eight_odd {p e b s m : ℕ} (hp : p.Prime) (hpp : 11 ≤ p)
    (hbpos : 0 < b) (hb : b ≤ 315) (ho : ¬2 ∣ b)
    (hs : s < 8) (hn : 10^12 ≤ b*p^e+s) (hm : 14 ≤ m) (hdvd : p^e ∣ m.choose 7) :
    m.choose 7 ≠ (b*p^e+s).choose 8 := by
  intro he
  have hscale := Nat.mul_le_mul_right (p^e) hb
  have hP : 10^9 ≤ p^e := by omega
  obtain ⟨q,r,hr,_,hw⟩ := exact_weights hp hpp hP hbpos hb (by decide)
    (by decide) (by decide) hs hm hdvd he
  have hdiv : 8 ∣ weight 7 r*b := ⟨(7 : ℕ).choose s*q, by simpa [weight, Nat.mul_assoc] using hw.symm⟩
  have hcop : Nat.Coprime 8 b := (Nat.prime_two.coprime_iff_not_dvd.mpr ho).pow_left 3
  have h := hcop.dvd_of_dvd_mul_right hdiv
  have hbad : ¬8 ∣ weight 7 r := by interval_cases r <;> decide
  exact hbad h

/-- Exclude a column-7 occurrence for an eighth-column host with b at most 34. -/
theorem no_eight {p e b s m : ℕ} (hp : p.Prime) (hpp : 11 ≤ p)
    (hbpos : 0 < b) (hb : b ≤ 34) (hs : s < 8) (hn : 10^12 ≤ b*p^e+s)
    (hm : 14 ≤ m) (hdvd : p^e ∣ m.choose 7) :
    m.choose 7 ≠ (b*p^e+s).choose 8 := by
  intro he
  have hscale := Nat.mul_le_mul_right (p^e) hb
  have hP : 10^9 ≤ p^e := by omega
  obtain ⟨q,r,hr,hqm,hw⟩ := exact_weights hp hpp hP hbpos (by omega) (by decide)
    (by decide) (by decide) hs hm hdvd he
  have wb : 8 ≤ weight 8 s := by unfold weight; interval_cases s <;> decide
  have wr : weight 7 r ≤ 140 := by unfold weight; interval_cases r <;> decide
  have h₁ := Nat.mul_le_mul_right q wb
  have h₂ := Nat.mul_le_mul_right b wr
  have hq : q ≤ 18*b := by omega
  have hmul := Nat.mul_le_mul_right (p^e) hq
  rw [Nat.mul_assoc] at hmul
  have lb := next_row_bound (c := 19) (k := 7) (by omega : 8*19^7 < b*p^e+s-7) he.ge
  omega

/-- Exclude seventh- and eighth-column occurrences for an interior ninth-column
    host with b at most 71. -/
theorem no_nine {p e b s m j : ℕ} (hp : p.Prime) (hpp : 11 ≤ p)
    (hbpos : 0 < b) (hb : b ≤ 71) (hs₁ : 1 ≤ s) (hs : s < 8)
    (hn : 10^11 ≤ b*p^e+s) (hj : 7 ≤ j) (hj' : j < 9) (hm : 2*j ≤ m)
    (hdvd : p^e ∣ m.choose j) : m.choose j ≠ (b*p^e+s).choose 9 := by
  intro he
  have hscale := Nat.mul_le_mul_right (p^e) hb
  have hP : 10^9 ≤ p^e := by omega
  obtain ⟨q,r,hr,hqm,hw⟩ := exact_weights hp hpp hP hbpos (by omega) hj hj'
    (by decide) (by omega) hm hdvd he
  have wb : 72 ≤ weight 9 s := by unfold weight; interval_cases s <;> decide
  have wr : weight j r ≤ 280 := by interval_cases j <;> interval_cases r <;> decide
  have h₁ := Nat.mul_le_mul_right q wb
  have h₂ := Nat.mul_le_mul_right b wr
  have hq : q ≤ 4*b := by omega
  have hmul := Nat.mul_le_mul_right (p^e) hq
  rw [Nat.mul_assoc] at hmul
  have hqpos : 1 ≤ q := by
    by_contra! h
    rw [show q=0 by omega, zero_mul, zero_add] at hqm
    omega
  have hmin : p^e ≤ q*p^e := by simpa using Nat.mul_le_mul_right (p^e) hqpos
  have hentry : m.choose j ≤ m.choose 8 := by
    rcases (show j=7 ∨ j=8 by omega) with rfl | rfl
    · exact Nat.choose_le_succ_of_lt_half_left (by omega)
    · rfl
  have lb := next_row_bound (c := 5) (k := 8) (by omega : 9*5^8 < b*p^e+s-8) (he.ge.trans hentry)
  omega

end Erdos849PowerCollision
