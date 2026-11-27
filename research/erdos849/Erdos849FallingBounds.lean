import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Bounds from pairing the endpoints of a consecutive product. -/
namespace Erdos849FallingBounds

open Finset

/-- The geometric mean of a consecutive block is between the geometric
mean of its endpoints and their arithmetic mean, with denominators cleared. -/
theorem paired_product (x : ℝ) (hx : 0 ≤ x) (t : ℕ) :
    (4*x*(x+t))^(t+1) ≤ 4^(t+1) * (∏ i ∈ range (t+1), (x+i))^2 ∧
    4^(t+1) * (∏ i ∈ range (t+1), (x+i))^2 ≤ ((2*x+t)^2)^(t+1) := by
  have href : (∏ i ∈ range (t+1), (x+(t-i : ℕ))) =
      ∏ i ∈ range (t+1), (x+i) := by
    simpa using prod_range_reflect (fun i : ℕ ↦ x+i) (t+1)
  have hfactor : ∀ i ∈ range (t+1),
      4*x*(x+t) ≤ 4*(x+i)*(x+(t-i : ℕ)) ∧
      4*(x+i)*(x+(t-i : ℕ)) ≤ (2*x+t)^2 := by
    intro i hi
    have hit : i ≤ t := Nat.le_of_lt_succ (mem_range.mp hi)
    have hreal : (i : ℝ) ≤ t := by exact_mod_cast hit
    rw [Nat.cast_sub hit]
    constructor
    · nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) i) (sub_nonneg.mpr hreal)]
    · nlinarith [sq_nonneg ((t:ℝ)-2*i)]
  have hlo := prod_le_prod (s := range (t+1))
    (f := fun _ : ℕ ↦ 4*x*(x+t)) (g := fun i : ℕ ↦ 4*(x+i)*(x+(t-i : ℕ)))
    (fun _ _ ↦ by positivity) (fun i hi ↦ (hfactor i hi).1)
  have hhi := prod_le_prod (s := range (t+1))
    (f := fun i : ℕ ↦ 4*(x+i)*(x+(t-i : ℕ))) (g := fun _ : ℕ ↦ (2*x+t)^2)
    (fun _ _ ↦ by positivity) (fun i hi ↦ (hfactor i hi).2)
  simp only [prod_mul_distrib, prod_const, card_range, href] at hlo hhi
  constructor
  · simpa only [mul_pow, pow_two, mul_assoc] using hlo
  · simpa only [pow_two, mul_assoc] using hhi

/-- Integer candidates in a column must lie in this real interval, where
the column is t+1, its bottom numerator term is x, and the row is x+t. -/
theorem row_interval (x R : ℝ) (hx : 0 ≤ x) (hR : 0 < R) (t : ℕ)
    (hprod : ∏ i ∈ range (t+1), (x+i) = R^(t+1)) :
    R+t/2 ≤ x+t ∧ x+t ≤ R+t/2+(t:ℝ)^2/(8*R) := by
  obtain ⟨hl, hu⟩ := paired_product x hx t
  have heq : 4^(t+1) * (∏ i ∈ range (t+1), (x+i))^2 = (4*R^2)^(t+1) := by
    rw [hprod, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (t+1) 2]
  rw [heq] at hl hu
  have hl' := le_of_pow_le_pow_left₀ (by omega : t+1 ≠ 0)
    (by positivity : 0 ≤ 4*R^2) hl
  have hu' := le_of_pow_le_pow_left₀ (by omega : t+1 ≠ 0)
    (sq_nonneg (2*x+t)) hu
  have hr : 2*R ≤ 2*x+t := le_of_pow_le_pow_left₀ two_ne_zero
    (by positivity) (by nlinarith : (2*R)^2 ≤ (2*x+t)^2)
  constructor
  · linarith
  · have h : x+t-(R+t/2) ≤ (t:ℝ)^2/(8*R) := by
      apply (le_div_iff₀ (by positivity : 0 < 8*R)).mpr
      nlinarith [sq_nonneg (2*x+t-2*R)]
    linarith

#print axioms row_interval

end Erdos849FallingBounds
