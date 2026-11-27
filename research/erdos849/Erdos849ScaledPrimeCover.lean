import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace Erdos849ScaledPrimeCover

/-- A multiple of a prime larger than the column forces that prime into
the coefficient whenever the multiple lies in its numerator block. -/
theorem prime_divides_of_multiple {m j p h : ℕ} (hp : p.Prime) (hjp : j < p)
    (hlo : m < h*p+j) (hhi : h*p ≤ m) :
    p ∣ m.choose j := by
  have hs : m - h*p < j := by omega
  have hterm : p ∣ m - (m - h*p) := by
    rw [Nat.sub_sub_self hhi]
    exact dvd_mul_left p h
  have hd : p ∣ m.descFactorial j := by
    rw [Nat.descFactorial_eq_prod_range]
    exact hterm.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hs))
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hd
  exact (hp.dvd_mul.mp hd).resolve_left (fun h => (hp.dvd_factorial.mp h).not_gt hjp)

/-- A gap bound around the scaled row excludes any coefficient from a
reference row below the witnessing prime. -/
theorem exclude_scaled_row {N K m j h g : ℕ} (hK : K ≤ N) (hh : 0 < h)
    (hwidth : h*g ≤ j)
    (hgap : ∃ p : ℕ, p.Prime ∧ N < p ∧ j < p ∧ p ≤ m/h ∧ m/h < p+g) :
    m.choose j ≠ N.choose K := by
  rintro he
  obtain ⟨p,hp,hNp,hjp,hpx,hx⟩ := hgap
  have hup : h*p ≤ m := by
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hh).mp hpx
  have hlt : m < (p+g)*h := (Nat.div_lt_iff_lt_mul hh).mp hx
  have hlo : m < h*p+j := by
    calc
      m < (p+g)*h := hlt
      _ = h*p+h*g := by ring
      _ ≤ h*p+j := by omega
  have hd := prime_divides_of_multiple hp hjp hlo hup
  rw [he] at hd
  have hg := Nat.dvd_gcd (dvd_refl p) hd
  rw [show p.gcd (N.choose K) = 1 from hp.coprime_choose_of_lt hNp hK] at hg
  exact hp.ne_one (Nat.dvd_one.mp hg)

/-- A prime-gap table for the interval [E/2,E] excludes repeated rows
all the way from E through E * floor(j/g). -/
theorem exclude_through_scaled_endpoint {N K m j E g : ℕ} (hK : K ≤ N)
    (hE : 0 < E) (hem : E ≤ m) (hcap : m ≤ E*(j/g))
    (table : ∀ x : ℕ, E/2 ≤ x → x ≤ E →
      ∃ p : ℕ, p.Prime ∧ N < p ∧ j < p ∧ p ≤ x ∧ x < p+g) :
    m.choose j ≠ N.choose K := by
  let b := (m-1)/E
  let h := b+1
  have hpos : 0 < h := Nat.zero_lt_succ b
  have hlo : b*E ≤ m-1 := Nat.div_mul_le_self _ _
  have hrem := Nat.mod_lt (m-1) hE
  have heq : (m-1)%E+b*E = m-1 := by
    simpa only [b, Nat.mul_comm] using Nat.mod_add_div (m-1) E
  have hmul : h*E = b*E+E := by dsimp [h]; ring
  have hceil : m ≤ h*E := by omega
  have htwice : h*E ≤ 2*m := by omega
  have hlt : b < j/g := (Nat.div_lt_iff_lt_mul hE).mpr (by
    rw [Nat.mul_comm]; omega)
  have hw : h*g ≤ j := (Nat.mul_le_mul_right g (show h ≤ j/g from hlt)).trans
    (Nat.div_mul_le_self _ _)
  apply exclude_scaled_row hK hpos hw
  apply table
  · apply (Nat.le_div_iff_mul_le hpos).mpr
    have ht := Nat.mul_le_mul_left h (Nat.div_mul_le_self E 2)
    nlinarith only [ht, htwice]
  · have hp : m < (E+1)*h := by
      rw [Nat.add_mul, one_mul, Nat.mul_comm E h]
      omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpos).mpr hp)

end Erdos849ScaledPrimeCover
