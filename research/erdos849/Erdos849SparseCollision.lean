import Erdos849PrimeHosts
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic.Ring

/-! An effective elementary bound on fixed-column collisions with few
distinct prime factors. The modulus may have prime divisors smaller than
either column; the integer product congruence never divides by a factorial. -/

namespace Erdos849SparseCollision

def omitted (k s x : ℕ) : ℤ :=
  ∏ i ∈ (Finset.range k).erase s, ((x : ℤ) - i)

private theorem extract {k s n P b : ℕ} (hk : k ≤ n) (hs : s < k) (hn : n=b*P+s) :
    (k.factorial : ℤ)*(n.choose k : ℕ) = (P : ℤ)*b*omitted k s n := by
  have hprod : n.descFactorial k = (n-s) * ∏ t ∈ (Finset.range k).erase s, (n-t) := by
    rw [Nat.descFactorial_eq_prod_range]
    exact (Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hs)).symm
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hprod
  have he := congrArg (fun x : ℕ => (x : ℤ)) hprod
  simp only [Nat.cast_mul, Nat.cast_prod] at he
  have hm : n-s=b*P := by omega
  rw [hm, Nat.cast_mul, mul_comm (b : ℤ)] at he
  rw [he, omitted]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact Nat.cast_sub (by have := Finset.mem_range.mp (Finset.mem_of_mem_erase hi); omega)

private theorem omitted_mod {k s n b P : ℕ} (hn : n=b*P+s) :
    omitted k s n ≡ omitted k s s [ZMOD P] := by
  have h : (n : ℤ) ≡ (s : ℤ) [ZMOD P] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(b : ℤ), ?_⟩
    rw [hn]; push_cast; ring
  exact Int.ModEq.prod (fun i _ => h.sub_right i)

/-- Omit one numerator factor in each representation and cancel their common
    modulus before reducing the remaining factors. -/
theorem raw_congruence {d j n m s r b q P : ℕ} (hP : 0<P)
    (hs : s<d) (hr : r<j) (hd : d≤n) (hj : j≤m)
    (hn : n=b*P+s) (hm : m=q*P+r) (he : n.choose d=m.choose j) :
    (j.factorial : ℤ)*b*omitted d s s ≡ (d.factorial : ℤ)*q*omitted j r r [ZMOD P] := by
  have h₁ := extract hd hs hn
  have h₂ := extract hj hr hm
  have hcross : (P : ℤ)*((j.factorial : ℤ)*b*omitted d s n) =
      P*((d.factorial : ℤ)*q*omitted j r m) := by
    calc
      _ = j.factorial * ((P : ℤ)*b*omitted d s n) := by ring
      _ = (d.factorial : ℤ)*(j.factorial*(m.choose j : ℕ)) := by rw [← h₁, he]; ring
      _ = _ := by rw [h₂]; ring
  have hc := mul_left_cancel₀ (show (P:ℤ)≠0 by omega) hcross
  calc
    _ ≡ (j.factorial : ℤ)*b*omitted d s n [ZMOD P] :=
      (omitted_mod hn).symm.mul_left _
    _ = (d.factorial : ℤ)*q*omitted j r m := hc
    _ ≡ _ [ZMOD P] := (omitted_mod hm).mul_left _

private theorem omitted_ne_zero {k s : ℕ} : omitted k s s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have := (Finset.mem_erase.mp hi).1
  omega

private theorem omitted_bound {d k s : ℕ} (hkd : k ≤ d) (hs : s < k) :
    (omitted k s s).natAbs ≤ (d+1)^d := by
  unfold omitted
  rw [show (∏ i ∈ (Finset.range k).erase s, ((s:ℤ)-i)).natAbs =
      ∏ i ∈ (Finset.range k).erase s, ((s:ℤ)-i).natAbs from
    map_prod Int.natAbsHom _ _]
  have hcard : ((Finset.range k).erase s).card ≤ d :=
    (Finset.card_le_card (Finset.erase_subset _ _)).trans (by simpa using hkd)
  apply (Finset.prod_le_pow_card _ _ (d+1) ?_).trans
    (Nat.pow_le_pow_right (by omega) hcard)
  intro i hi
  have := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
  rcases le_total s i with hh | hh
  · rw [Int.natAbs_natCast_sub_natCast_of_le hh]; omega
  · rw [Int.natAbs_natCast_sub_natCast_of_ge hh]; omega

def coefficientBound (d : ℕ) := d.factorial*(d+1)^d

private theorem coeff_le {d k l s : ℕ} (hk : k≤d) (hl : l≤d) (hs : s<k) :
    ((l.factorial : ℤ)*omitted k s s).natAbs ≤ coefficientBound d := by
  simpa [coefficientBound, Int.natAbs_mul] using
    Nat.mul_le_mul (Nat.factorial_le hl) (omitted_bound hk hs)

private theorem half_mono {n i j : ℕ} (h : i ≤ j) (hj : 2*j ≤ n) : n.choose i ≤ n.choose j := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem row_power {n k A : ℕ} (hn : 2*k≤n) (hv : n.choose k ≤ A) :
    n^k ≤ (2^k*k.factorial)*A := calc
  _ ≤ (2*(n+1-k))^k := Nat.pow_le_pow_left (by omega) k
  _ = 2^k*(n+1-k)^k := mul_pow _ _ _
  _ ≤ 2^k*(k.factorial*n.choose k) := Nat.mul_le_mul_left _ (by
    simpa [Nat.descFactorial_eq_factorial_mul_choose] using n.pow_sub_le_descFactorial k)
  _ ≤ 2^k*(k.factorial*A) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hv)
  _ = _ := (mul_assoc _ _ _).symm

private theorem strip_powers {x a b C : ℕ} (hx : 0<x) (hba : b<a)
    (h : x^a ≤ C*x^b) : x ≤ C := by
  rw [show a=(a-b)+b by omega, pow_add] at h
  exact (Nat.le_self_pow (by omega : a-b≠0) x).trans
    (Nat.le_of_mul_le_mul_right h (pow_pos hx _))

/-- An explicit height for the value, with geometric and modular branches. -/
def heightBound (j d w : ℕ) : ℕ :=
  max ((2^d*d.factorial*(coefficientBound d+1)^j)^d)
    (((4*coefficientBound d)^j*j.factorial)^w)

/-- With fewer than twice the smaller column in distinct prime factors, a
    collision in two fixed proper columns has effectively bounded value. -/
theorem height_bound {a n m j d w : ℕ} (hj : 2 ≤ j) (hjd : j < d)
    (hn : 2*d ≤ n) (hm : 2*j ≤ m) (hdval : n.choose d = a) (hjval : m.choose j = a)
    (hf : a.primeFactors.card ≤ w) (hw : w < 2*j) : a ≤ heightBound j d w := by
  have ha : 1 < a := by
    have h := half_mono (by omega : 1≤j) hm
    rw [Nat.choose_one_right,hjval] at h
    omega
  obtain ⟨p, hp, hmax⟩ := a.primeFactors.exists_max_image
    (fun t : ℕ => t^a.factorization t) (Nat.nonempty_primeFactors.mpr ha)
  have hp' := Nat.prime_of_mem_primeFactors hp
  let P := p^a.factorization p
  have hP : 0<P := pow_pos hp'.pos _
  have hdiv : P ∣ a := (hp'.pow_dvd_iff_le_factorization (by omega : a≠0)).mpr le_rfl
  have hA : a ≤ P^w := calc
    a = ∏ t ∈ a.primeFactors, t^a.factorization t := Nat.prod_primeFactors_pow_factorization (by omega)
    _ ≤ P^a.primeFactors.card := Finset.prod_le_pow_card _ _ _ hmax
    _ ≤ _ := Nat.pow_le_pow_right hP hf
  let s := n%P
  let r := m%P
  let b := n/P
  let q := m/P
  have hddiv : p^a.factorization p ∣ n.choose d := by rw [hdval]; exact hdiv
  have hjdiv : p^a.factorization p ∣ m.choose j := by rw [hjval]; exact hdiv
  have hs : s<d := Erdos849PrimeHosts.residue_lt_column hp' (by omega) (by omega) hddiv
  have hr : r<j := Erdos849PrimeHosts.residue_lt_column hp' (by omega) (by omega) hjdiv
  have hbn : b*P+s=n := Nat.div_add_mod' n P
  have hqm : q*P+r=m := Nat.div_add_mod' m P
  let U : ℤ := j.factorial * omitted d s s
  let V : ℤ := d.factorial * omitted j r r
  let H := coefficientBound d
  have hu : U.natAbs ≤ H := coeff_le le_rfl hjd.le hs
  have hv : V.natAbs ≤ H := coeff_le hjd.le le_rfl hr
  have hvpos : 0 < V.natAbs := by
    apply Int.natAbs_pos.mpr
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero d) omitted_ne_zero
  have hc : (b:ℤ)*U ≡ (q:ℤ)*V [ZMOD P] := by
    simpa only [U,V,mul_assoc,mul_left_comm,mul_comm] using
      raw_congruence hP hs hr (by omega) (by omega) hbn.symm hqm.symm (hdval.trans hjval.symm)
  by_cases heq : (b:ℤ)*U = (q:ℤ)*V
  · have hq : q ≤ H*b := calc
      q ≤ q*V.natAbs := Nat.le_mul_of_pos_right _ hvpos
      _ = b*U.natAbs := by simpa only [Int.natAbs_mul,Int.natAbs_natCast] using congrArg Int.natAbs heq.symm
      _ ≤ b*H := Nat.mul_le_mul_left _ hu
      _ = _ := Nat.mul_comm _ _
    have hmul := Nat.mul_le_mul_right P hq
    rw [Nat.mul_assoc] at hmul
    have hmn : m ≤ (H+1)*n := by
      have hbn' : b*P ≤ n := by omega
      have := Nat.mul_le_mul_left H hbn'
      rw [Nat.succ_mul]; omega
    have hgeom : n^d ≤ (2^d*d.factorial*(H+1)^j)*n^j := calc
      _ ≤ (2^d*d.factorial)*a := row_power hn hdval.le
      _ ≤ (2^d*d.factorial)*m^j := Nat.mul_le_mul_left _ (hjval ▸ Nat.choose_le_pow m j)
      _ ≤ (2^d*d.factorial)*((H+1)*n)^j := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hmn _)
      _ = _ := by rw [mul_pow]; ring
    have hn' := strip_powers (by omega : 0<n) hjd hgeom
    exact ((hdval ▸ Nat.choose_le_pow n d).trans (Nat.pow_le_pow_left hn' d)).trans
      (le_max_left _ _)
  · let M := max n m
    have hdiff := Int.natAbs_le_of_dvd_ne_zero hc.dvd (sub_ne_zero.mpr (Ne.symm heq))
    have hsum := Int.natAbs_sub_le ((q:ℤ)*V) ((b:ℤ)*U)
    simp only [Int.natAbs_mul,Int.natAbs_natCast] at hsum hdiff
    have hsmall : P ≤ q*H+b*H := hdiff.trans (hsum.trans
      (Nat.add_le_add (Nat.mul_le_mul_left _ hv) (Nat.mul_le_mul_left _ hu)))
    have hM : P^2 ≤ (2*H)*M := calc
      _ ≤ (q*H+b*H)*P := by simpa [pow_two] using Nat.mul_le_mul_right P hsmall
      _ = H*(q*P)+H*(b*P) := by ring
      _ ≤ H*M+H*M := Nat.add_le_add (Nat.mul_le_mul_left _ (show q*P≤M from
        (by omega : q*P≤m).trans (le_max_right _ _))) (Nat.mul_le_mul_left _ (show b*P≤M from
        (by omega : b*P≤n).trans (le_max_left _ _)))
      _ = _ := by ring
    have hcol : n.choose j ≤ a := (half_mono hjd.le hn).trans hdval.le
    have hmj : M^j ≤ (2^j*j.factorial)*a := by
      rcases le_total n m with h | h
      · simpa only [M,max_eq_right h] using row_power hm hjval.le
      · simpa only [M,max_eq_left h] using row_power (by omega : 2*j≤n) hcol
    have hpow : P^(2*j) ≤ ((4*H)^j*j.factorial)*P^w := calc
      _ = (P^2)^j := pow_mul _ _ _
      _ ≤ ((2*H)*M)^j := Nat.pow_le_pow_left hM _
      _ = (2*H)^j*M^j := mul_pow _ _ _
      _ ≤ (2*H)^j*((2^j*j.factorial)*a) := Nat.mul_le_mul_left _ hmj
      _ = ((4*H)^j*j.factorial)*a := by
        rw [show 4*H=2*H*2 by ring, mul_pow (2*H) 2 j]; ring
      _ ≤ _ := Nat.mul_le_mul_left _ hA
    exact (hA.trans (Nat.pow_le_pow_left (strip_powers hP hw hpow) w)).trans (le_max_right _ _)

end Erdos849SparseCollision
