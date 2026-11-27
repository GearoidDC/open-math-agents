import Erdos849PrimeHosts
import Erdos849LindDiagonal
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-! Prime-containing numerator blocks of equal binomial coefficients. -/

namespace Erdos849PrimeWindow

def hasPrime (n k : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ n-k<p ∧ p≤n

theorem contains_iff {n k P Q : ℕ} (hk : 1≤k) (hh : 2*k≤n) (hp : P.Prime)
    (hd : P ∣ n.choose k) (hmax : ∀ r, r.Prime → r ∣ n.choose k → r≤P)
    (hq : Q.Prime) (hpq : P<Q) (hnext : ∀ r, r.Prime → P<r → Q≤r) :
    hasPrime n k ↔ P≤n ∧ n<Q := by
  have hres : n%P < k := by
    simpa only [pow_one] using
      Erdos849PrimeHosts.residue_lt_column (e:=1) hp hk (by omega : k≤n) (by simpa using hd)
  have hpn : P≤n := by
    by_contra! h
    rw [Nat.mod_eq_of_lt h] at hres
    omega
  constructor
  · rintro ⟨r,hr,hl,hu⟩
    have hrp := hmax r hr (hr.dvd_choose (by omega) hl hu)
    refine ⟨hpn,?_⟩
    by_contra! hqn
    have hqp := hmax Q hq (hq.dvd_choose (by omega) (by omega) hqn)
    omega
  · rintro ⟨_,hnq⟩
    obtain ⟨r,hr,hpr,hr₂⟩ := Nat.exists_prime_lt_and_le_two_mul P hp.ne_zero
    have hq₂ := hnext r hr hpr
    have h := Nat.mod_eq_sub_mod hpn
    rw [Nat.mod_eq_of_lt (by omega : n-P<P)] at h
    exact ⟨P,hp,by omega,hpn⟩

/-- A prime in the upper half of the row cannot occur squared. -/
theorem not_square {n k p : ℕ} (hp : p.Prime) (hk : 1≤k) (hkn : k≤n)
    (hn : n<2*p) : ¬p^2 ∣ n.choose k := by
  intro hd
  have h := Erdos849PrimeHosts.residue_lt_column hp hk hkn hd
  have hp2 := hp.two_le
  have hpow : n<p^2 := by nlinarith
  rw [Nat.mod_eq_of_lt hpow] at h
  omega

/-- Compare the left endpoints of two overlapping numerator blocks. -/
theorem lower_gap {n k m j r : ℕ} (hk : 1≤k) (hkn : 2*k≤n) (hj : 1≤j)
    (hjm : 2*j≤m) (he : n.choose k=m.choose j) (hover : m-j≤n)
    (hr : r.Prime) (hu : r≤m-j) : r≤n-k ∨ 2*r≤m := by
  by_contra! h
  have hd : r ∣ m.choose j := he ▸ hr.dvd_choose (by omega) h.1 (by omega)
  have hres : m%r < j := by
    simpa only [pow_one] using
      Erdos849PrimeHosts.residue_lt_column (e:=1) hr hj (by omega : j≤m) (by simpa using hd)
  have hmod := Nat.mod_eq_sub_mod (by omega : r≤m)
  rw [Nat.mod_eq_of_lt (by omega : m-r<r)] at hmod
  omega

/-- A prime no farther than G below the later left endpoint bounds the column drop. -/
theorem column_span {n k m j r G : ℕ} (hk : 1≤k) (hkn : 2*k≤n) (hj : 1≤j)
    (hjm : 2*j≤m) (hnm : n≤m) (he : n.choose k=m.choose j) (hover : m-j≤n)
    (hr : r.Prime) (hu : r≤m-j) (hg : m-j≤r+G) : k≤j+G := by
  rcases lower_gap hk hkn hj hjm he hover hr hu with h | h <;> omega

/-- A prime at or before the first row which does not divide the common
value must be at least a square-root distance below the second row. -/
theorem absent_prime_distance {r n H k j : ℕ} (hr : r.Prime) (hrn : r≤n)
    (hmiss : ¬r ∣ n.choose k) (hj : 1≤j) (hjk : j<k) (hhalf : 2*k≤n)
    (he : n.choose k=(n+H).choose j) : 4*r ≤ (n+H-r)^2 := by
  have hleft : r≤n-k := by
    by_contra! h
    exact hmiss (hr.dvd_choose (by omega) h hrn)
  let s := n-r
  have hks : k≤s := by dsimp [s]; omega
  have hpos : 1≤s := by omega
  have hspan := Erdos849LindDiagonal.earlier_column_bound hj hjk hhalf he
  have hup := Nat.mul_le_mul_left (H+2) hks
  have heq : n=r+s := by dsimp [s]; omega
  have hs : s-1+1=s := by omega
  have hprod : r≤(H+1)*(s-1) := by
    nlinarith only [hspan.trans hup,heq,congrArg (fun x : ℕ => H*x) hs,hs]
  have ham : 4*((H+1)*(s-1)) ≤ (H+1+(s-1))^2 := by
    simpa only [Nat.mul_assoc] using four_mul_le_sq_add (H+1) (s-1)
  have hsum : H+1+(s-1)=n+H-r := by dsimp [s]; omega
  rw [← hsum]
  exact (Nat.mul_le_mul_left 4 hprod).trans ham

/-- In a prime gap [r,q) above the largest prime factor of a repeated
coefficient, two row indices force the integer form of an Andrica violation. -/
theorem gap_size {r q n H k j : ℕ} (hr : r.Prime) (hrn : r≤n) (hnq : n+H<q)
    (hmiss : ¬r ∣ n.choose k) (hj : 1≤j) (hjk : j<k) (hhalf : 2*k≤n)
    (he : n.choose k=(n+H).choose j) : 4*r ≤ (q-r-1)^2 :=
  (absent_prime_distance hr hrn hmiss hj hjk hhalf he).trans
    (Nat.pow_le_pow_left (by omega) _)

private theorem increase_row {n k : ℕ} (hk : 0<k) (hkn : k≤n) (H : ℕ) :
    (n+H).choose k*(n-k)^H ≤ n.choose k*n^H := by
  induction H with
  | zero => simp
  | succ H ih =>
    obtain ⟨c,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    have ha := Nat.choose_succ_right_eq (n+H) c
    have hb := Nat.mul_le_mul_left ((n+H).choose c) (show n-(c+1)≤n+H-c by omega)
    have hstep : (n+H+1).choose (c+1)*(n-(c+1)) ≤ (n+H).choose (c+1)*n := by
      rw [Nat.choose_succ_succ,Nat.add_mul]
      calc
        _ ≤ ((n+H).choose (c+1))*(c+1)+((n+H).choose (c+1))*(n-(c+1)) :=
          Nat.add_le_add_right (hb.trans ha.ge) _
        _ = _ := by rw [← Nat.mul_add, Nat.add_sub_of_le hkn]
    calc
      _ = ((n+H+1).choose (c+1)*(n-(c+1)))*(n-(c+1))^H := by
        simp only [Nat.succ_eq_add_one, Nat.add_assoc, pow_succ]; ring
      _ ≤ (((n+H).choose (c+1))*n)*(n-(c+1))^H := Nat.mul_le_mul_right _ hstep
      _ = ((n+H).choose (c+1)*(n-(c+1))^H)*n := by ring
      _ ≤ _ := by simpa [pow_succ,Nat.mul_assoc] using Nat.mul_le_mul_right n ih

private theorem decrease_col {m n k j : ℕ} (hnm : n≤m) (hk : k≤n)
    (v : ℕ) (h : j+v≤k) :
    m.choose j*(n-k+1)^v ≤ m.choose (j+v)*k^v := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hc := Nat.choose_succ_right_eq m (j+v)
    have hstep : m.choose (j+v)*(n-k+1) ≤ m.choose (j+v+1)*k := calc
      _ ≤ m.choose (j+v)*(m-(j+v)) := Nat.mul_le_mul_left _ (by omega)
      _ = m.choose (j+v+1)*(j+v+1) := hc.symm
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    calc
      _ = (m.choose j*(n-k+1)^v)*(n-k+1) := by rw [pow_succ]; ring
      _ ≤ (m.choose (j+v)*k^v)*(n-k+1) := Nat.mul_le_mul_right _ (ih (by omega))
      _ = (m.choose (j+v)*(n-k+1))*k^v := by ring
      _ ≤ (m.choose (j+v+1)*k)*k^v := Nat.mul_le_mul_right _ hstep
      _ = _ := by simp only [Nat.add_assoc,pow_succ]; ring

/-- Integer version of the entropy-slope bound for any two occurrences. -/
theorem slope_power {n H k j v : ℕ} (hk : 0<k) (hkn : k≤n) (hjk : j+v=k)
    (he : n.choose k=(n+H).choose j) :
    (n-k+1)^v*(n-k)^H ≤ k^v*n^H := by
  have hrow := increase_row hk hkn H
  have hcol := decrease_col (by omega : n≤n+H) hkn v hjk.le
  rw [hjk,← he] at hcol
  apply Nat.le_of_mul_le_mul_left _ (Nat.choose_pos hkn)
  calc
    _ = (n.choose k*(n-k+1)^v)*(n-k)^H := by ring
    _ ≤ ((n+H).choose k*k^v)*(n-k)^H := Nat.mul_le_mul_right _ hcol
    _ = ((n+H).choose k*(n-k)^H)*k^v := by ring
    _ ≤ (n.choose k*n^H)*k^v := Nat.mul_le_mul_right _ hrow
    _ = _ := by ring

end Erdos849PrimeWindow
