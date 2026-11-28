import Mathlib

/-! Distinct occurrences of one coefficient have separated extreme descendants
at every admissible common depth in Pascal's triangle. -/

namespace Erdos849PascalDescent

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) :
    n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem column_lt {k n m : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) (hnm : n < m) :
    n.choose k < m.choose k := by
  have hpos := Nat.choose_pos (show k-1 ≤ n by omega)
  calc
    n.choose k < (n+1).choose k := by rw [Nat.choose_succ_left n k hk]; omega
    _ ≤ m.choose k := Nat.choose_le_choose k hnm

private theorem ratio_lt {i j p q : ℕ} (hij : i < j) (hp : 0 < p) (hpq : p < q) :
    (i:ℚ)/q < j/p := by
  have hq : (0:ℚ) < q := by exact_mod_cast hp.trans hpq
  calc
    (i:ℚ)/q < j/q := (div_lt_div_iff_of_pos_right hq).2 (by exact_mod_cast hij)
    _ ≤ j/p := div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hp)
      (by exact_mod_cast hpq.le)

private theorem down_right {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ((n-1).choose k : ℚ) = (n.choose k : ℚ)*(1-(k:ℚ)/n) := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.add_one_sub_one]
  have h := Nat.choose_mul_succ_eq v k
  have he : ((v.choose k : ℚ)*((v:ℚ)+1)) =
      ((v+1).choose k : ℚ)*((v:ℚ)+1-k) := by
    exact_mod_cast (by simpa using h : v.choose k*(v+1) = (v+1).choose k*(v+1-k))
  push_cast
  field_simp
  linarith

private theorem extreme_middle {n k h : ℕ} (hh : h ≤ k) (hk : 2*k ≤ n) :
    (n-h).choose (k-h) ≤ (n-h).choose k := by
  have hsym : (n-h).choose ((n-k)-h) = (n-h).choose k := by
    rw [show n-k-h = (n-h)-k by omega, Nat.choose_symm (by omega)]
  have hleft := Nat.choose_mul (n := n) hh
  have hright := Nat.choose_mul (n := n) (show h ≤ n-k by omega)
  rw [Nat.choose_symm (by omega), hsym] at hright
  have hcomp := Nat.mul_le_mul_left (n.choose k) (Nat.choose_le_choose h (show k ≤ n-k by omega))
  rw [hleft, hright] at hcomp
  exact Nat.le_of_mul_le_mul_left hcomp (Nat.choose_pos (by omega))

/-- The two endpoints for each witness enclose those for every earlier witness,
strictly on both sides. In particular no extreme Pascal descendant at a fixed
positive depth can have the same value for two distinct witness rows. -/
theorem nested_extremes {n m k l h : ℕ} (hnm : n < m) (hk : 1 ≤ k)
    (hn : 2*k ≤ n) (hm : 2*l ≤ m) (he : n.choose k = m.choose l)
    (hh : 1 ≤ h) (hl : h ≤ l) :
    (m-h).choose (l-h) < (n-h).choose (k-h) ∧
    (n-h).choose (k-h) ≤ (n-h).choose k ∧
    (n-h).choose k < (m-h).choose l := by
  have hlk : l < k := by
    by_contra! hle
    have := (column_lt hk (show k ≤ n by omega) hnm).trans_le (half_mono hle hm)
    omega
  refine ⟨?_,extreme_middle (by omega) hn,?_⟩
  · have hmpos := Nat.choose_pos (show h ≤ m by omega)
    have hnpos := Nat.choose_pos (show h ≤ n by omega)
    have ha := Nat.choose_pos (show k ≤ n by omega)
    have h1 := Nat.choose_mul (n := n) (show h ≤ k by omega)
    have h2 := Nat.choose_mul (n := m) hl
    rw [← he] at h2
    have hac := Nat.mul_lt_mul_of_pos_left (column_lt hh hl hlk) ha
    rw [h1,h2] at hac
    by_contra! hf
    have := Nat.mul_le_mul (Nat.choose_le_choose h hnm.le) hf
    omega
  · have aux : ∀ t ≤ h, ((n-t).choose k : ℚ) ≤ (m-t).choose l ∧
        (0 < t → ((n-t).choose k : ℚ) < (m-t).choose l) := by
      intro t
      induction t with
      | zero => simp [he]
      | succ t ih =>
        intro hth
        have hi := (ih (by omega)).1
        have hr := ratio_lt (i := l) (j := k) (p := n-t) (q := m-t) hlk
          (by omega) (by omega)
        have left : (0:ℚ) ≤ 1-(k:ℚ)/(n-t:ℕ) := by
          have hpos : (0:ℚ) < (n-t:ℕ) := by exact_mod_cast (show 0<n-t by omega)
          linarith [(div_le_one hpos).2 (show (k:ℚ) ≤ (n-t:ℕ) by exact_mod_cast (show k≤n-t by omega))]
        have hpos : (0:ℚ) < (m-t).choose l := by
          exact_mod_cast Nat.choose_pos (show l ≤ m-t by omega)
        have hh' : ((n-(t+1)).choose k : ℚ) < (m-(t+1)).choose l := by
          rw [show n-(t+1) = n-t-1 by omega, show m-(t+1) = m-t-1 by omega,
            down_right (by omega) (by omega), down_right (by omega) (by omega)]
          exact (mul_le_mul_of_nonneg_right hi left).trans_lt
            (mul_lt_mul_of_pos_left (by linarith) hpos)
        exact ⟨hh'.le,fun _ => hh'⟩
    exact_mod_cast (aux h le_rfl).2 hh

#print axioms nested_extremes

end Erdos849PascalDescent
