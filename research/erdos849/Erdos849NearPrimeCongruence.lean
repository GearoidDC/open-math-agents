import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! A congruence between two binomial representations in rows just above
positive multiples of the same prime. -/

namespace Erdos849NearPrimeCongruence

def weight (d s : ℕ) := d * (d-1).choose s

def residueProduct (Q d s : ℕ) :=
  (Q+s).choose s * (Q-1).choose (d-1-s)

/-- Isolate the multiple Q in the numerator, before reducing modulo a prime. -/
theorem isolate (Q d s : ℕ) (hQ : 0 < Q) (hs : s < d) :
    weight d s * (Q+s).choose d = Q * residueProduct Q d s := by
  have h₁ := Nat.choose_mul_succ_eq (d-1) s
  rw [show d-1+1 = d by omega] at h₁
  have h₂ := Nat.choose_mul (n := Q+s) hs.le
  rw [Nat.add_sub_cancel] at h₂
  have h₃ := Nat.add_one_mul_choose_eq (Q-1) (d-1-s)
  rw [show Q-1+1 = Q by omega, show d-1-s+1 = d-s by omega] at h₃
  unfold weight residueProduct
  calc
    _ = ((Q+s).choose d * d.choose s) * (d-s) := by
      rw [mul_comm d, h₁]
      ring
    _ = (Q+s).choose s * (Q.choose (d-s) * (d-s)) := by rw [h₂]; ring
    _ = _ := by rw [← h₃]; ring

private theorem above_multiple {p q s : ℕ} [Fact p.Prime] (hs : s < p) :
    (((q*p+s).choose s : ℕ) : ZMod p) = 1 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := q*p+s) (k := s)
  have he := (ZMod.natCast_eq_natCast_iff _ _ _).2 h
  simpa [Nat.add_mod, Nat.mod_eq_of_lt hs, Nat.div_eq_of_lt hs] using he

private theorem below_multiple {p q t : ℕ} [hp : Fact p.Prime] (hq : 1 ≤ q) (ht : t < p) :
    (((q*p-1).choose t : ℕ) : ZMod p) = (-1)^t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hqp : p ≤ q*p := by simpa using Nat.mul_le_mul_right p hq
    have hnz : (t+1 : ZMod p) ≠ 0 := by
      intro he
      exact (Nat.not_dvd_of_pos_of_lt (by omega) ht)
        ((ZMod.natCast_eq_zero_iff (t+1) p).mp (by simpa using he))
    have h := Nat.choose_succ_right_eq (q*p-1) t
    have hz := congrArg (fun x : ℕ => (x : ZMod p)) h
    push_cast [Nat.cast_sub (by omega : t ≤ q*p-1), Nat.cast_sub (by omega : 1 ≤ q*p)] at hz
    rw [ih (by omega)] at hz
    simp only [ZMod.natCast_self, mul_zero, zero_sub] at hz
    apply mul_right_cancel₀ hnz
    rw [hz,pow_succ]
    ring

private theorem residue_mod {p q d s : ℕ} [Fact p.Prime] (hq : 1 ≤ q) (hs : s < d) (hd : d < p) :
    (residueProduct (q*p) d s : ZMod p) = (-1)^(d-1-s) := by
  rw [residueProduct, Nat.cast_mul, above_multiple (hs.trans hd), below_multiple hq (by omega), one_mul]

/-- A collision between columns d and j in rows p+s and qp+r forces a
signed congruence of the small binomial weights. -/
theorem collision {p d j s r q : ℕ} (hp : p.Prime) (hd : d < p) (hj : j < p)
    (hs : s < d) (hr : r < j) (hq : 1 ≤ q)
    (he : (p+s).choose d = (q*p+r).choose j) :
    d * (d-1).choose s * q ≡ j * (j-1).choose r [MOD p] ∨
    p ∣ d * (d-1).choose s * q + j * (j-1).choose r := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h₁ := isolate p d s hp.pos hs
  have h₂ := isolate (q*p) j r (Nat.mul_pos hq hp.pos) hr
  have hcross : p * ((weight d s*q) * residueProduct (q*p) j r) =
      p * (weight j r * residueProduct p d s) := by
    calc
      _ = weight d s * (q*p * residueProduct (q*p) j r) := by ring
      _ = weight j r * (weight d s * (p+s).choose d) := by rw [← h₂, ← he]; ring
      _ = _ := by rw [h₁]; ring
  have h := Nat.eq_of_mul_eq_mul_left hp.pos hcross
  have hz := congrArg (fun x : ℕ => (x : ZMod p)) h
  have hm₁ : (residueProduct p d s : ZMod p) = (-1)^(d-1-s) := by
    simpa using residue_mod (p := p) (q := 1) (by decide) hs hd
  have hm₂ := residue_mod hq hr hj
  simp only [Nat.cast_mul, hm₁, hm₂] at hz
  change weight d s*q ≡ weight j r [MOD p] ∨ p ∣ weight d s*q + weight j r
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_zero_iff]
  push_cast
  rcases neg_one_pow_eq_or (ZMod p) (d-1-s) with hsg₁ | hsg₁ <;>
    rcases neg_one_pow_eq_or (ZMod p) (j-1-r) with hsg₂ | hsg₂ <;>
    simp only [hsg₁,hsg₂,mul_one,mul_neg] at hz <;> first
    | exact Or.inl hz
    | exact Or.inl (neg_inj.mp hz)
    | exact Or.inr (by linear_combination hz)
    | exact Or.inr (by linear_combination -hz)

end Erdos849NearPrimeCongruence
