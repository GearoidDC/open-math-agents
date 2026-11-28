import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
import Mathlib.NumberTheory.Fermat
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Pell
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.ZMod.Basic

/-! Smooth quadratic values and necessary divisibility of large exceptions to Erdős 889. -/

namespace Erdos889.QuadraticSmooth

private theorem split_factor_exponent (e : ℕ) :
    ∃ i j : ℕ, e=i+j*2 ∧ i≤3 ∧ (0 < j → 2 ≤ i) := by
  by_cases small : e≤3
  · exact ⟨e,0,by omega,small,by omega⟩
  · exact ⟨2+e%2,(e-2)/2,by omega,by omega,by omega⟩

private theorem smooth_square_decomposition (T n : ℕ) (hn : 0 < n)
    (smooth : ∀ q : ℕ, q.Prime → q∣n → q ≤ T) :
    ∃ D y : ℕ, D≤(T+1).factorial^3 ∧ 0 < D ∧ 0 < y ∧ n=D*y^2 ∧
      ∀ q : ℕ, q.Prime → q∣y → q^2∣D := by
  induction T generalizing n with
  | zero =>
    have unit : n=1 := by
      by_contra ne
      obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd ne
      have := smooth q pq dq
      have := pq.two_le
      omega
    refine ⟨1,1,by decide,by decide,by decide,by simpa only [one_pow,mul_one] using unit,?_⟩
    intro q pq div
    have := Nat.le_of_dvd (by decide : 0<1) div
    have := pq.two_le
    omega
  | succ t ih =>
    let p := t+1
    let e := n.factorization p
    let m := n/p^e
    have fac : p^e*m=n := Nat.ordProj_mul_ordCompl_eq_self n p
    have dm : m∣n := Nat.ordCompl_dvd n p
    have pos : 0 < m := Nat.ordCompl_pos p hn.ne'
    have smaller (q : ℕ) (pq : q.Prime) (dq : q∣m) : q ≤ t := by
      have upper := smooth q pq (dq.trans dm)
      by_contra! high
      have equal : q=p := by dsimp [p]; omega
      rw [equal] at pq dq
      exact (Nat.not_dvd_ordCompl pq hn.ne') dq
    obtain ⟨D,y,cap,hD,hy,form,divisors⟩ := ih m pos smaller
    obtain ⟨i,j,ei,i3,ji⟩ := split_factor_exponent e
    have small : p^i ≤ (t+2)^3 :=
      (Nat.pow_le_pow_right (show 0 < p by dsimp [p]; omega) i3).trans
        (Nat.pow_le_pow_left (show p ≤ t+2 by dsimp [p]; omega) 3)
    have total : D*p^i ≤ (t+1+1).factorial^3 := by
      have bound := Nat.mul_le_mul cap small
      rw [Nat.factorial_succ (t+1),mul_pow,Nat.mul_comm ((t+1+1)^3)]
      exact bound
    refine ⟨D*p^i,y*p^j,total,Nat.mul_pos hD (pow_pos (by dsimp [p]; omega) _),
      Nat.mul_pos hy (pow_pos (by dsimp [p]; omega) _),?_,?_⟩
    · calc
        n = p^e*m := fac.symm
        _ = _ := by rw [form,ei,pow_add,pow_mul,mul_pow]; ring
    · intro q pq dq
      rcases pq.dvd_mul.mp dq with fromY|fromP
      · exact dvd_mul_of_dvd_left (divisors q pq fromY) _
      · have jp : 0 < j := by
          by_contra! low
          have zero : j=0 := by omega
          rw [zero,pow_zero] at fromP
          have := Nat.le_of_dvd (by decide : 0<1) fromP
          have := pq.two_le
          omega
        have pp : p.Prime := by
          by_contra np
          have zero : e=0 := Nat.factorization_eq_zero_of_not_prime n np
          omega
        have same := (Nat.prime_dvd_prime_iff_eq pq pp).mp (pq.dvd_of_dvd_pow fromP)
        rw [same]
        exact dvd_mul_of_dvd_right (pow_dvd_pow p (ji jp)) _

/-- Every square-plus-one supported on primes at most T gives a negative Pell
equation with D in an explicit finite interval. Each prime dividing its
positive y-coordinate has its square dividing D. -/
theorem quadratic_smooth_decomposition (T x : ℕ)
    (smooth : ∀ q : ℕ, q.Prime → q∣x^2+1 → q ≤ T) :
    ∃ D ∈ Finset.Icc 1 ((T+1).factorial^3), ∃ y : ℕ, 0 < D ∧ 0 < y ∧
      x^2+1=D*y^2 ∧ ∀ q : ℕ, q.Prime → q∣y → q^2∣D := by
  obtain ⟨D,y,cap,hD,hy,form,divisors⟩ := smooth_square_decomposition T (x^2+1) (by omega) smooth
  exact ⟨D,Finset.mem_Icc.mpr ⟨hD,cap⟩,y,hD,hy,form,divisors⟩

end Erdos889.QuadraticSmooth

namespace Erdos889.PellValuation

-- BEGIN PELL VALUATION
private theorem pell_expansion_remainder {d : ℤ} (z : Pell.Solution₁ d) (n : ℕ) :
    ∃ L K : ℤ, (z^(n+1)).x=z.x^(n+1)+d*L ∧
      (z^(n+1)).y=z.y*((n+1 : ℕ)*(z.x^n)+d*K) := by
  induction n with
  | zero => exact ⟨0,0,by simp,by simp⟩
  | succ n ih =>
    obtain ⟨L,K,hx,hy⟩ := ih
    refine ⟨L*z.x+(z^(n+1)).y*z.y,L+K*z.x,?_,?_⟩
    · change (z^(n+1)*z).x=z.x^(n+1+1)+d*(L*z.x+(z^(n+1)).y*z.y)
      rw [Pell.Solution₁.x_mul,hx,pow_succ z.x (n+1)]
      ring
    · change (z^(n+1)*z).y=z.y*((n+1+1:ℕ)*z.x^(n+1)+d*(L+K*z.x))
      rw [Pell.Solution₁.y_mul,hx,hy,pow_succ z.x n]
      push_cast
      ring

private theorem pell_prime_multiplier {D l q : ℕ} (z : Pell.Solution₁ (D:ℤ))
    (pl : l.Prime) (pq : q.Prime) (dq : q^2∣D) :
    ∃ k : ℕ, (z^l).y.natAbs=z.y.natAbs*k ∧ k≠0 ∧ k.factorization q=l.factorization q := by
  let _ : Fact q.Prime := ⟨pq⟩
  obtain ⟨_,K,_,hy⟩ := pell_expansion_remainder z (l-1)
  rw [Nat.sub_add_cancel pl.one_le] at hy
  obtain ⟨h,dh⟩ := dq
  have dint : (D:ℤ)=(q:ℤ)^2*h := by exact_mod_cast dh
  have zd : (D:ZMod q)=0 := (ZMod.natCast_eq_zero_iff _ _).mpr (dh ▸ dvd_mul_of_dvd_left (dvd_pow_self q (by decide : (2:ℕ)≠0)) h)
  have xz : (z.x:ZMod q)≠0 := by
    intro zero
    have f := congrArg (fun v:ℤ => (v:ZMod q)) z.prop
    push_cast at f
    rw [zd,zero,zero_pow two_ne_zero,zero_mul,sub_zero] at f
    exact zero_ne_one f
  let a := z.x^(l-1)
  have an : (a:ZMod q)≠0 := by dsimp [a]; push_cast; exact pow_ne_zero _ xz
  have no {c : ℤ} (hc : (c:ZMod q)≠0) : ¬q∣c.natAbs :=
    fun dd => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (Int.natCast_dvd.mpr dd))
  by_cases same : l=q
  · subst l
    let c := a+(q:ℤ)*h*K
    have cn : ¬q∣c.natAbs := no (by simpa [c] using an)
    have nc : c.natAbs≠0 := fun e => cn (e ▸ dvd_zero q)
    have yq : (z^q).y=z.y*((q:ℤ)*c) := by
      rw [hy]
      dsimp only [a,c]
      linear_combination z.y*K*dint
    refine ⟨q*c.natAbs,?_,mul_ne_zero pq.ne_zero nc,?_⟩
    · rw [yq]; simp only [Int.natAbs_mul,Int.natAbs_natCast]
    · rw [Nat.factorization_mul pq.ne_zero nc,Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd cn,add_zero]
  · have nl : ¬q∣l := fun h => same ((Nat.prime_dvd_prime_iff_eq pq pl).mp h).symm
    have lv : (l:ZMod q)≠0 := fun h => nl ((ZMod.natCast_eq_zero_iff _ _).mp h)
    let c := (l:ℤ)*a+(D:ℤ)*K
    have cn : ¬q∣c.natAbs := no (by
      dsimp only [c]
      push_cast
      rw [zd,zero_mul,add_zero]
      exact mul_ne_zero lv an)
    have nc : c.natAbs≠0 := fun e => cn (e ▸ dvd_zero q)
    refine ⟨c.natAbs,?_,nc,?_⟩
    · rw [hy,Int.natAbs_mul]
    · rw [Nat.factorization_eq_zero_of_not_dvd cn,Nat.factorization_eq_zero_of_not_dvd nl]

/-- At a prime whose square divides D, the imaginary coordinate of a Pell power gains exactly the exponent's valuation. -/
theorem pell_factorization_y_pow {D q n : ℕ} (eps : Pell.Solution₁ (D : ℤ))
    (pq : q.Prime) (dq : q^2∣D) (hn : 0 < n) :
    (eps^n).y.natAbs.factorization q = (n*eps.y.natAbs).factorization q := by
  by_cases hzero : eps.y=0
  · obtain ⟨_,_,_,hy⟩ := pell_expansion_remainder eps (n-1)
    rw [Nat.sub_add_cancel hn,hzero,zero_mul] at hy
    simp [hy,hzero]
  have base : eps.y.natAbs≠0 := fun h => hzero (Int.natAbs_eq_zero.mp h)
  have all : ∀ j : ℕ, j≠0 → (eps^j).y.natAbs≠0 ∧
      (eps^j).y.natAbs.factorization q=(j*eps.y.natAbs).factorization q := by
    apply induction_on_primes
    · simp
    · simp [base]
    · intro l a pl ih nz
      have ap : a≠0 := fun e => nz (by rw [e,mul_zero])
      obtain ⟨nonzero,ihv⟩ := ih ap
      obtain ⟨k,mult,kpos,kv⟩ := pell_prime_multiplier (eps^a) pl pq dq
      have e : eps^(l*a)=(eps^a)^l := by rw [←pow_mul,Nat.mul_comm]
      rw [e,mult]
      refine ⟨mul_ne_zero nonzero kpos,?_⟩
      rw [Nat.factorization_mul nonzero kpos,Finsupp.add_apply,kv,ihv,Nat.mul_assoc,
        Nat.factorization_mul pl.ne_zero (mul_ne_zero ap base),Finsupp.add_apply,Nat.add_comm]
  exact (all n hn.ne').2
-- END PELL VALUATION
end Erdos889.PellValuation

namespace Erdos889.QuadraticSmooth

private theorem cube_le_two_pow {m : ℕ} (hm : 10 ≤ m) : m^3≤2^m := by
  induction m,hm using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [pow_succ 2 k]
    have step : (k+1)^3≤2*k^3 := by
      have k2 : 5*k ≤ k^2 := by nlinarith [Nat.mul_le_mul_right k (show 5 ≤ k by omega)]
      nlinarith [Nat.mul_le_mul_right (k^2) (show 5 ≤ k by omega)]
    omega

private theorem pell_growth {D : ℤ} (eps : Pell.Solution₁ D) (hx : 1 < eps.x)
    (hy : 0 < eps.y) (n : ℕ) : (2:ℤ)^n*eps.y ≤ (eps^(n+1)).y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have sx := Pell.Solution₁.x_pow_pos (show 0 < eps.x by omega) (n+1)
    have sy := Pell.Solution₁.y_pow_succ_pos (show 0 < eps.x by omega) hy n
    have grow := mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ eps.x by omega) sy.le
    rw [pow_succ, show n+1+1=(n+1)+1 by rfl, pow_succ eps (n+1),Pell.Solution₁.y_mul]
    nlinarith [mul_pos sx hy]

private theorem quadratic_twist_bound (D : ℕ)
    (valuation : ∀ (eps : Pell.Solution₁ (D:ℤ)) (q n : ℕ), q.Prime → q^2∣D →
      0 < n → 1 < eps.x → 0 < eps.y →
      ((eps^n).y.natAbs).factorization q=(n*eps.y.natAbs).factorization q) :
    ∃ B : ℕ, ∀ x y : ℕ, 0 < y → x^2+1=D*y^2 →
      (∀ q : ℕ, q.Prime → q∣y → q^2∣D) → x ≤ B := by
  classical
  by_cases has : ∃ e : Pell.Solution₁ (D:ℤ), Pell.IsFundamental e
  · obtain ⟨eps,he⟩ := has
    let Y := eps.y.natAbs
    refine ⟨D*(10+4*D*Y)*Y,?_⟩
    intro x y hy eq support
    by_cases hx : x=0
    · omega
    have castEq : (x:ℤ)^2+1=(D:ℤ)*(y:ℤ)^2 := by exact_mod_cast eq
    have id : ((2:ℤ)*x^2+1)^2-D*(2*(x:ℤ)*y)^2=1 := by
      linear_combination -4*(x:ℤ)^2*(castEq.symm)
    let sol : Pell.Solution₁ (D:ℤ) := Pell.Solution₁.mk _ _ id
    have sx : sol.x=2*(x:ℤ)^2+1 := rfl
    have sy : sol.y=2*(x:ℤ)*y := rfl
    obtain ⟨n,hn⟩ := he.eq_pow_of_nonneg (a:=sol) (by rw [sx]; positivity) (by rw [sy]; positivity)
    have nz : 0 < n := by
      by_contra! h
      have : n=0 := by omega
      rw [this,pow_zero] at hn
      have eqy := congrArg Pell.Solution₁.y hn
      rw [sy,Pell.Solution₁.y_one] at eqy
      have : 0<(x:ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hx
      have pos : 0<2*(x:ℤ)*y := by positivity
      omega
    have YY : 0 < Y := by dsimp [Y]; exact Int.natAbs_pos.mpr he.2.1.ne'
    have imag : (eps^n).y.natAbs=2*x*y := by
      rw [←hn,sy,Int.natAbs_mul,Int.natAbs_mul]
      rfl
    have ydiv : y∣n*Y := by
      apply (Nat.factorization_le_iff_dvd hy.ne' (Nat.mul_pos nz YY).ne').mp
      intro q
      by_cases pq : q.Prime
      · by_cases dy : q∣y
        · have div : y∣2*x*y := dvd_mul_left _ _
          have nonz : 2*x*y≠0 := by positivity
          have le := (Nat.factorization_le_iff_dvd hy.ne' nonz).mpr div q
          rw [←imag,valuation eps q n pq (support q pq dy) nz he.1 he.2.1] at le
          exact le
        · simp [Nat.factorization_eq_zero_of_not_dvd dy]
      · simp [Nat.factorization_eq_zero_of_not_prime _ pq]
    have ybound := Nat.le_of_dvd (Nat.mul_pos nz YY) ydiv
    have Dx : x ≤ D*y := by
      have hD : 0 < D := by exact_mod_cast he.d_pos
      by_contra! large
      have h := Nat.mul_le_mul (show 1 ≤ D by omega) (Nat.le_refl (D*y^2))
      nlinarith [Nat.mul_self_lt_mul_self large]
    have expBound : 2^n*Y ≤ 4*x*y := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero nz.ne'
      have low := pell_growth eps he.1 he.2.1 j
      have eqy := congrArg Pell.Solution₁.y hn
      rw [←eqy,sy] at low
      have castY : (Y:ℤ)=eps.y := Int.natAbs_of_nonneg he.2.1.le
      change (2:ℕ)^(j+1)*Y ≤ 4*x*y
      zify
      rw [castY,pow_succ]
      linarith
    have nbound : n≤10+4*D*Y := by
      by_cases big : 10 ≤ n
      · have cube := cube_le_two_pow big
        have upper := Nat.mul_le_mul Dx ybound
        have upper' := Nat.mul_le_mul (Nat.mul_le_mul_left D ybound) (Nat.le_refl (n*Y))
        have all : n^3*Y≤(4*D*Y)*(n^2*Y) := by
          nlinarith [Nat.mul_le_mul_right Y cube]
        have eqN : n^3*Y=n*(n^2*Y) := by ring
        rw [eqN] at all
        have := Nat.le_of_mul_le_mul_right all (by positivity : 0 < n^2*Y)
        omega
      · omega
    exact Dx.trans (by calc
      D*y ≤ D*(n*Y) := Nat.mul_le_mul_left _ ybound
      _ ≤ D*((10+4*D*Y)*Y) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ nbound)
      _ = _ := by ring)
  · refine ⟨0,?_⟩
    intro x y hy eq _
    by_contra! xbig
    have castEq : (x:ℤ)^2+1=(D:ℤ)*(y:ℤ)^2 := by exact_mod_cast eq
    have id : ((2:ℤ)*x^2+1)^2-D*(2*(x:ℤ)*y)^2=1 := by
      linear_combination -4*(x:ℤ)^2*(castEq.symm)
    let sol : Pell.Solution₁ (D:ℤ) := Pell.Solution₁.mk _ _ id
    have sx : 1 < sol.x := by
      change 1<2*(x:ℤ)^2+1
      have hxZ : 0<(x:ℤ) := by exact_mod_cast xbig
      nlinarith [sq_pos_of_pos hxZ]
    exact has (Pell.IsFundamental.exists_of_not_isSquare
      (Pell.Solution₁.d_pos_of_one_lt_x sx) (Pell.Solution₁.d_nonsquare_of_one_lt_x sx))


/-- The greatest prime factor of x²+1 eventually exceeds each fixed bound. -/
theorem large_prime_of_square_add_one (T : ℕ) : ∃ B : ℕ, ∀ x : ℕ, B < x →
    ∃ q : ℕ, q.Prime ∧ T < q ∧ q∣x^2+1 := by
  classical
  have bounds (D : ℕ) := quadratic_twist_bound D (fun eps q n pr dv hn _ _ =>
    Erdos889.PellValuation.pell_factorization_y_pow eps pr dv hn)
  choose bound covers using bounds
  let ds := Finset.Icc 1 ((T+1).factorial^3)
  refine ⟨ds.sup bound,?_⟩
  intro x hx
  by_contra missing
  have smooth (q : ℕ) (pr : q.Prime) (dv : q∣x^2+1) : q ≤ T := by
    by_contra! big
    exact missing ⟨q,pr,big,dv⟩
  obtain ⟨D,hd,y,_,hy,eq,dv⟩ := quadratic_smooth_decomposition T x smooth
  exact (not_lt_of_ge ((covers D x y hy eq dv).trans (Finset.le_sup (f:=bound) hd))) hx

end Erdos889.QuadraticSmooth

namespace Erdos889.EventualPrimeDivisibility

open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem smooth_fourth_decomposition (T n : ℕ) (hn : 0 < n)
    (smooth : ∀ q : ℕ, q.Prime → q∣n → q ≤ T) :
    ∃ C z : ℕ, C ≤ T.factorial^3 ∧ 0 < C ∧ 0 < z ∧ n=C*z^4 := by
  induction T generalizing n with
  | zero =>
    have unit : n=1 := by
      by_contra ne
      obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd ne
      have := smooth q pq dq
      have := pq.two_le
      omega
    exact ⟨1,1,by decide,by decide,by decide,by simpa only [one_pow,mul_one] using unit⟩
  | succ t ih =>
    let p := t+1
    let e := n.factorization p
    let m := n/p^e
    have fac : p^e*m=n := Nat.ordProj_mul_ordCompl_eq_self n p
    have dm : m∣n := Nat.ordCompl_dvd n p
    have pos : 0 < m := Nat.ordCompl_pos p hn.ne'
    have smaller (q : ℕ) (pq : q.Prime) (dq : q∣m) : q ≤ t := by
      have upper := smooth q pq (dq.trans dm)
      by_contra! high
      have equal : q=p := by dsimp [p]; omega
      rw [equal] at pq dq
      exact (Nat.not_dvd_ordCompl pq hn.ne') dq
    obtain ⟨C,z,cap,hC,hz,form⟩ := ih m pos smaller
    have ppos : 0 < p := by dsimp [p]; omega
    have small : p^(e%4) ≤ p^3 := Nat.pow_le_pow_right ppos (by omega)
    have total : C*p^(e%4)≤(t+1).factorial^3 := by
      rw [Nat.factorial_succ,mul_pow,Nat.mul_comm ((t+1)^3)]
      exact Nat.mul_le_mul cap small
    refine ⟨C*p^(e%4),z*p^(e/4),total,Nat.mul_pos hC (pow_pos ppos _),
      Nat.mul_pos hz (pow_pos ppos _),?_⟩
    have ei : e=e%4+(e/4)*4 := by rw [Nat.mul_comm (e/4) 4,Nat.mod_add_div]
    calc
      n = p^e*m := fac.symm
      _ = p^(e%4+(e/4)*4)*(C*z^4) := by rw [←ei,form]
      _ = _ := by rw [pow_add,pow_mul,mul_pow]; ring

private theorem two_quadratic_factors {T u : ℕ} (hT : 4 ≤ T)
    (h₁ : ∃ q : ℕ, q.Prime ∧ T < q ∧ q∣u^2+1)
    (h₂ : ∃ q : ℕ, q.Prime ∧ T < q ∧ q∣(u+2)^2+1) :
    ∃ q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ T < q ∧ T < s ∧ q∣(u+1)^4+4 ∧ s∣(u+1)^4+4 := by
  obtain ⟨q,pq,hq,dq⟩ := h₁
  obtain ⟨s,ps,hs,ds⟩ := h₂
  let z := u+1
  let L := u^2+1
  let R := (u+2)^2+1
  change q∣L at dq
  change s∣R at ds
  have fac : (u+1)^4+4=L*R := by dsimp only [L,R]; ring
  refine ⟨q,s,pq,ps,?_,hq,hs,fac ▸ dvd_mul_of_dvd_left dq _,fac ▸ dvd_mul_of_dvd_right ds _⟩
  rintro rfl
  have diff : R=L+4*z := by dsimp only [R,L,z]; ring
  rw [diff] at ds
  have d4 := (Nat.dvd_add_iff_right dq).mpr ds
  have dz : q∣z := (pq.dvd_mul.mp d4).resolve_left (by
    intro dv; have := Nat.le_of_dvd (by decide : 0<4) dv; omega)
  have sum := dvd_add dq (dvd_mul_of_dvd_right dz 2)
  rw [show L+2*z=z^2+2 by dsimp only [L,z]; ring] at sum
  have sq : q∣z^2 := dz.trans (dvd_pow_self z (by decide : 2≠0))
  have bad := (Nat.dvd_add_iff_right sq).mpr sum
  have := Nat.le_of_dvd (by decide : 0<2) bad
  omega

/-- For any fixed prime q, if the largest prime factor of x²+1 tends to
infinity, all sufficiently large lowercase Erdős 889 solutions are divisible by q. -/
theorem eventual_prime_divisibility
    (quadratic : ∀ T : ℕ, ∃ B : ℕ, ∀ x : ℕ, B < x → ∃ q : ℕ, q.Prime ∧ T < q ∧ q∣x^2+1)
    (q : ℕ) (pq : q.Prime) :
    ∃ B : ℕ, ∀ n : ℕ, B < n → Erdos889.v_l 1 n=1 → q∣n := by
  let M := q.factorial^3
  let T := q+4*M
  have mp : 0 < M := pow_pos q.factorial_pos 3
  have hT : 4 ≤ T := by dsimp only [T]; omega
  obtain ⟨K,hK⟩ := quadratic T
  refine ⟨M*(K+2)^4,?_⟩
  intro n hn sol
  by_contra avoid
  let k := q-n%q
  have rem := Nat.mod_lt n pq.pos
  have nr : n%q≠0 := fun z => avoid (Nat.dvd_of_mod_eq_zero z)
  have kp : 0 < k := by dsimp only [k]; omega
  have kq : k < q := by dsimp only [k]; omega
  have qd : q∣n+k := by
    refine ⟨n/q+1,?_⟩
    have h := Nat.mod_add_div n q
    rw [Nat.mul_add,mul_one]
    dsimp only [k]
    omega
  have smooth (r : ℕ) (pr : r.Prime) (dr : r∣n+k) : r ≤ q := by
    by_contra! large
    exact two_primes kp pq pr (by omega) kq (by omega) qd dr sol
  obtain ⟨C,z,cap,_cp,_zp,form⟩ := smooth_fourth_decomposition q (n+k) (by omega) smooth
  change C ≤ M at cap
  have large : K+2 < z := by
    by_contra! low
    have cmp := Nat.mul_le_mul cap (Nat.pow_le_pow_left low 4)
    omega
  let u := z-1
  have zu : z=u+1 := by dsimp only [u]; omega
  have ku : K < u := by omega
  obtain ⟨a,b,pa,pb,ne,ha,hb,da,db⟩ := two_quadratic_factors hT (hK u ku) (hK (u+2) (by omega))
  have fac : n+(k+4*C)=C*((u+1)^4+4) := by
    rw [zu] at form
    calc
      _ = (n+k)+4*C := by omega
      _ = _ := by rw [form]; ring
  have ub : k+4*C ≤ T := by dsimp only [T]; omega
  exact two_primes (k:=k+4*C) (by omega) pa pb ne (by omega) (by omega)
    (fac ▸ dvd_mul_of_dvd_right da C) (fac ▸ dvd_mul_of_dvd_right db C) sol


/-- Each fixed prime divides every sufficiently large exceptional starting point. -/
theorem eventually_divides_bad (q : ℕ) (pq : q.Prime) :
    ∃ B : ℕ, ∀ n : ℕ, B < n → Erdos889.v_l 1 n=1 → q∣n :=
  eventual_prime_divisibility Erdos889.QuadraticSmooth.large_prime_of_square_add_one q pq

end Erdos889.EventualPrimeDivisibility

namespace Erdos889.UniformPowers
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

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


-- Reused when integrating into the reduction.
private theorem binary_plus_prime {s e : ℕ} (ps : s.Prime) (oe : Odd e) (dv : s∣2^e+1) :
    s%8=1 ∨ s%8=3 := by
  obtain ⟨j,hj⟩ := oe
  have epos : 0 < e := by omega
  have d2 := dvd_pow_self (2:ℕ) epos.ne'
  have ne : s≠2 := by rintro rfl; omega
  let _ : Fact s.Prime := ⟨ps⟩
  apply (ZMod.exists_sq_eq_neg_two_iff (p:=s) ne).mp
  refine ⟨(2:ZMod s)^(j+1),?_⟩
  have zero := (ZMod.natCast_eq_zero_iff (2^e+1) s).mpr dv
  push_cast at zero
  rw [←pow_add,show j+1+(j+1)=e+1 by omega,pow_succ]
  linear_combination -2*zero

private theorem nonsplit_prime {N : ℕ} (seven : N%8=7) :
    ∃ s : ℕ, s.Prime ∧ s∣N ∧ ¬(s%8=1 ∨ s%8=3) := by
  by_contra missing
  have ok (l : List ℕ) (h : ∀ s ∈ l, s%8=1 ∨ s%8=3) : l.prod%8=1 ∨ l.prod%8=3 := by
    induction l with
    | nil => decide
    | cons a t ih =>
      have ha := h a (by simp)
      have ht := ih (fun u hu => h u (by simp [hu]))
      rw [List.prod_cons,Nat.mul_mod]
      rcases ha with h|h <;> rcases ht with w|w <;> rw [h,w] <;> decide
  have result := ok N.primeFactorsList (by
    intro s hs
    by_contra bad
    exact missing ⟨s,Nat.prime_of_mem_primeFactorsList hs,Nat.dvd_of_mem_primeFactorsList hs,bad⟩)
  rw [Nat.prod_primeFactorsList (by omega)] at result
  omega

theorem finite_prime_threshold (L : ℕ) : ∃ B : ℕ, ∀ n : ℕ, B < n → Erdos889.v_l 1 n=1 →
    ∀ s : ℕ, s ≤ L → s.Prime → s∣n := by
  induction L with
  | zero =>
    refine ⟨0,?_⟩
    intro n hn sol s low ps
    have := ps.two_le
    omega
  | succ l ih =>
    obtain ⟨A,hA⟩ := ih
    by_cases prime : (l+1).Prime
    · obtain ⟨B,hB⟩ := Erdos889.EventualPrimeDivisibility.eventually_divides_bad _ prime
      refine ⟨max A B,?_⟩
      intro n hn sol s le ps
      by_cases same : s=l+1
      · exact same ▸ hB n (lt_of_le_of_lt (Nat.le_max_right _ _) hn) sol
      · exact hA n (lt_of_le_of_lt (Nat.le_max_left _ _) hn) sol s (by omega) ps
    · refine ⟨A,?_⟩
      intro n hn sol s le ps
      have ne : s≠l+1 := by rintro rfl; exact prime ps
      exact hA n hn sol s (by omega) ps

/-- A single bound suffices for all odd exponents from three through any prescribed R. -/
theorem bounded_odd_mersenne_exclusion (R : ℕ) : ∃ B : ℕ, ∀ n p b r : ℕ,
    B < n → p.Prime → p+1=2^b → 3 ≤ r → Odd r → r ≤ R → n+1=p^r → Erdos889.v_l 1 n≠1 := by
  let T := 2^R+1
  obtain ⟨B,allpr⟩ := finite_prime_threshold T
  refine ⟨max B ((2^(T+4))^R),?_⟩
  intro n p b r large pp base rlo odd upper eq sol
  have bigb : T+4 < b := by
    by_contra! small
    have hp := Nat.pow_le_pow_right (by decide : 0<2) small
    have a := Nat.pow_le_pow_left (show p≤2^(T+4) by omega) r
    have h := Nat.pow_le_pow_right (by positivity : 0<2^(T+4)) upper
    have m := Nat.le_max_right B ((2^(T+4))^R)
    omega
  have hb4 : 4 < b := lt_of_le_of_lt (Nat.le_add_left 4 T) bigb
  have ep : p=2^b-1 := by omega
  have pb := (Nat.prime_of_pow_sub_one_prime (by omega) (ep ▸ pp)).2
  have ob := pb.odd_of_ne_two (by omega)
  let k := 2^r+1
  have kT : k ≤ T := by dsimp [k,T]; exact Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) upper) 1
  have kp : 0 < k := by dsimp [k]; positivity
  have shift : n+k=p^r+2^r := by dsimp [k]; omega
  have db : 8∣2^b := pow_dvd_pow 2 (show 3 ≤ b by omega)
  have dr : 8∣2^r := pow_dvd_pow 2 rlo
  have pm : Nat.ModEq 8 p 7 := by change p%8=7%8; omega
  have prm : Nat.ModEq 8 (p^r) 7 := by
    obtain ⟨j,hj⟩ := odd
    calc
      p^r ≡ 7^r [MOD 8] := pm.pow _
      _ = (7^2)^j*7 := by rw [hj,pow_succ,pow_mul]
      _ ≡ 1^j*7 [MOD 8] := ((by decide : Nat.ModEq 8 (7^2) 1).pow j).mul_right 7
      _ = 7 := by simp
  have sev : (p^r+2^r)%8=7 := by change (p^r)%8=7%8 at prm; omega
  obtain ⟨s,ps,ds,wrong⟩ := nonsplit_prime sev
  have hs : k < s := by
    by_contra! small
    have dn := allpr n (lt_of_le_of_lt (Nat.le_max_left ..) large) sol s (small.trans kT) ps
    have ds2 : s∣n+k := shift.symm ▸ ds
    have dk : s∣k := (Nat.dvd_add_iff_right dn).mpr ds2
    exact wrong (binary_plus_prime ps odd dk)
  obtain ⟨q,pq,hq,dq⟩ := mersenne_left_factor pb (show k < b by omega) (by omega)
  have diff : q≠s := by rintro rfl; exact wrong (binary_plus_prime pq ob dq)
  have dbase : q∣p+2 := by convert dq using 1; omega
  have together := dbase.trans (odd.nat_add_dvd_pow_add_pow p 2)
  exact two_primes kp pq ps diff hq hs (shift ▸ together) (shift ▸ ds) sol

/-- Any fixed finite range of exponents at least three admits a single bound, for arbitrary bases. -/
theorem bounded_power_exclusion (R : ℕ) : ∃ B : ℕ, ∀ n x r : ℕ,
    B < n → 1 < x → 3 ≤ r → r ≤ R → n+1=x^r → Erdos889.v_l 1 n≠1 := by
  obtain ⟨B,hB⟩ := bounded_odd_mersenne_exclusion R
  refine ⟨max B 81,?_⟩
  intro n x r large hx hr upper eq sol
  have lb := Nat.le_max_right B 81
  have hB' := Nat.le_max_left B 81
  have odd_base {y j : ℕ} (hj : 0 < j) (e : n+1=y^j) : Odd y := by
    apply Nat.not_even_iff_odd.mp
    intro even
    have dd : 2∣n+1 := e ▸ (even_iff_two_dvd.mp even).trans (dvd_pow_self y hj.ne')
    have on : Odd n := by rw [Nat.odd_iff]; omega
    rcases (odd_classification on).mp sol with h|h|h|h <;> omega
  have rule {y j : ℕ} (hy : 1 < y) (lo : 3 ≤ j) (hi : j ≤ R)
      (oj : Odd j) (e : n+1=y^j) : False := by
    have oy := odd_base (by omega) e
    obtain ⟨b,base⟩ := odd_power_root_neighbor oy hy oj (by omega) e sol
    have pure := prime_power_succ (n:=n) (by omega) sol
    rw [e,isPrimePow_pow_iff (by omega : j≠0)] at pure
    obtain ⟨p,a,pp,pa,he⟩ := (isPrimePow_nat_iff _).mp pure
    have op := pp.odd_of_ne_two (by
      rintro rfl
      have div := dvd_pow_self (2:ℕ) pa.ne'
      rw [he] at div
      exact (Nat.not_even_iff_odd.mpr oy) (even_iff_two_dvd.mpr div))
    have one := mersenne_power_exponent op pp.one_lt pa (he.symm ▸ base)
    rw [one,pow_one] at he
    subst y
    exact hB n p b j (by omega) pp base lo oj hi e sol
  by_cases o : Odd r
  · exact rule hx hr upper o eq
  · have even : r%2=0 := by rw [Nat.odd_iff] at o; omega
    by_cases four : r%4=0
    · let y := x^(r/4)
      have ey : n+1=y^4 := by dsimp [y]; rw [←pow_mul,show r/4*4=r by omega,eq]
      have bigy : 3 < y := by
        by_contra! small
        have ly := Nat.pow_le_pow_left small 4
        norm_num at ly
        omega
      obtain ⟨p,q,pp,pq,ne,hp,hq,dp,dq⟩ := fourth_power_witness (odd_base (by decide) ey) bigy
      have rearr : n+5=y^4+4 := by omega
      exact two_primes (k:=5) (by decide) pp pq ne hp hq (rearr ▸ dp) (rearr ▸ dq) sol
    · have e : n+1=(x^2)^(r/2) := by rw [←pow_mul, show 2*(r/2)=r by omega,eq]
      exact rule (by nlinarith) (by omega) (by omega) (by rw [Nat.odd_iff]; omega) e

end Erdos889.UniformPowers

namespace Erdos889.PrimitivePowers
open Polynomial


private theorem power_cyclotomic_order {p n q : ℕ} (hn : 0 < n) (pq : q.Prime)
    (hd : q ∣ ((cyclotomic n ℤ).eval (p : ℤ)).natAbs) :
    orderOf (p : ZMod q) = n / q ^ n.factorization q ∧
      n / q ^ n.factorization q ∣ q - 1 := by
  let : Fact q.Prime := ⟨pq⟩
  have hr : IsRoot (cyclotomic n (ZMod q)) (Nat.castRingHom (ZMod q) p) := by
    have c : ((p : ℤ) : ZMod q) = ↑(Int.castRingHom (ZMod q) p) := by simp
    rw [IsRoot.def, ← map_cyclotomic_int n (ZMod q), eval_map, Nat.coe_castRingHom,
      ← Int.cast_natCast, c, eval₂_hom, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply Int.dvd_natAbs.1
    exact_mod_cast hd
  have hc : ¬q ∣ p := pq.coprime_iff_not_dvd.mp (coprime_of_root_cyclotomic hn hr).symm
  let m := n / q ^ n.factorization q
  let : NeZero (m : ZMod q) := NeZero.of_not_dvd _ (Nat.not_dvd_ordCompl pq hn.ne')
  have form : q ^ n.factorization q * m = n := Nat.ordProj_mul_ordCompl_eq_self n q
  have hr' : (cyclotomic (q ^ n.factorization q * m) (ZMod q)).IsRoot (p : ZMod q) := by
    rw [form]
    exact hr
  have eqn := (isRoot_cyclotomic_prime_pow_mul_iff_of_charP.mp hr').eq_orderOf
  refine ⟨eqn.symm, ?_⟩
  rw [show n / q ^ n.factorization q = orderOf (p : ZMod q) from eqn]
  exact ZMod.orderOf_dvd_card_sub_one (mt (CharP.cast_eq_zero_iff _ _ _).1 hc)

private theorem power_cyclotomic_div {p n d : ℕ} (hp : 1 ≤ p) (hd : d ∈ n.properDivisors) :
    (p ^ d - 1) * ((cyclotomic n ℤ).eval (p : ℤ)).natAbs ∣ p ^ n - 1 := by
  have h := eval_dvd (x := (p : ℤ))
    (X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ hd)
  simp only [eval_mul, eval_sub, eval_X_pow, eval_one] at h
  have castpow (k : ℕ) : (p : ℤ)^k - 1 = ((p^k-1 : ℕ) : ℤ) := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hp), Nat.cast_pow, Nat.cast_one]
  have h' := Int.natAbs_dvd_natAbs.mpr h
  simpa only [castpow, Int.natAbs_mul, Int.natAbs_natCast] using h'

private theorem power_cyclotomic_no_square {p n q : ℕ} (hp : 3 ≤ p) (oddp : Odd p)
    (hn : 2 < n) (pq : q.Prime) (dn : q ∣ n)
    (hF : q ∣ ((cyclotomic n ℤ).eval (p : ℤ)).natAbs) :
    ¬ q^2 ∣ ((cyclotomic n ℤ).eval (p : ℤ)).natAbs := by
  let : Fact q.Prime := ⟨pq⟩
  let d := n / q
  let a := p^d
  have form : d*q=n := Nat.div_mul_cancel dn
  have dpos : 0 < d := Nat.div_pos (Nat.le_of_dvd (by omega) dn) pq.pos
  have apos : 1 < a := Nat.one_lt_pow dpos.ne' (by omega : 1 < p)
  have dmem : d ∈ n.properDivisors := Nat.mem_properDivisors.mpr
    ⟨⟨q,form.symm⟩, Nat.div_lt_self (by omega) pq.one_lt⟩
  have divF := power_cyclotomic_div (p := p) (by omega) dmem
  have power : a^q=p^n := by rw [show a = p ^ d by rfl, ← pow_mul, form]
  rw [← power] at divF
  change (a-1) * _ ∣ a^q-1 at divF
  obtain ⟨ordp,orddiv⟩ := power_cyclotomic_order (by omega) pq hF
  have total : q ^ n.factorization q * (n / q ^ n.factorization q) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n q
  intro hs
  have div2 : (a-1)*q^2 ∣ a^q-1 := (Nat.mul_dvd_mul_left _ hs).trans divF
  by_cases qt : q=2
  · subst q
    have m1 : n / 2 ^ n.factorization 2 = 1 := Nat.dvd_one.mp orddiv
    rw [m1, mul_one] at total
    have ee : 2 ≤ n.factorization 2 := by
      by_contra! h
      interval_cases h' : n.factorization 2 <;> simp at total <;> omega
    obtain ⟨k,hk⟩ : ∃ k, n.factorization 2 = k+2 := ⟨_, (Nat.sub_add_cancel ee).symm⟩
    have dk : d = 2^k*2 := by rw [hk, pow_succ, pow_succ] at total; omega
    have ak : a = (p^(2^k))^2 := by change p^d = _; rw [dk,pow_mul]
    have neq : a^2-1=(a-1)*(a+1) := by
      have hh : a-1+1=a := by omega
      rw [← hh]
      simp only [Nat.add_sub_cancel]
      have e : (a-1+1)^2=(a-1)*(a-1+1+1)+1 := by ring
      omega
    rw [neq] at div2
    have ff := Nat.dvd_of_mul_dvd_mul_left (by omega : 0 < a-1) div2
    obtain ⟨j,hj⟩ := oddp.pow (n:=2^k)
    rw [ak,hj] at ff
    obtain ⟨z,hz⟩ := ff
    have eh : (2*j+1)^2+1 = 4*(j*j+j)+2 := by ring
    omega

  · have md : orderOf (p : ZMod q) ∣ n := ⟨q^n.factorization q, by
      rw [ordp,mul_comm,total]⟩
    have ax : (a : ZMod q)^q = 1 := by
      rw [show a = p^d from rfl, Nat.cast_pow, ← pow_mul, form]
      exact orderOf_dvd_iff_pow_eq_one.mp md
    rw [ZMod.pow_card] at ax
    have hdiv : q ∣ a-1 := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one, ax, sub_self]
    have na : ¬ q ∣ a := by
      intro h
      have := (ZMod.natCast_eq_zero_iff _ _).mpr h
      rw [ax] at this
      exact one_ne_zero this
    have vv := padicValNat.pow_sub_pow (p:=q) (x:=a) (y:=1)
      (pq.odd_of_ne_two qt) apos hdiv na pq.ne_zero
    simp only [one_pow,padicValNat_self] at vv
    obtain ⟨u,hu⟩ := div2
    have hpos := Nat.one_lt_pow pq.ne_zero apos
    have u0 : u ≠ 0 := by intro e; rw [e,mul_zero] at hu; omega
    rw [hu, padicValNat.mul (Nat.mul_ne_zero (by omega) (pow_ne_zero _ pq.ne_zero)) u0,
      padicValNat.mul (by omega) (pow_ne_zero _ pq.ne_zero), padicValNat.pow,
      padicValNat_self] at vv
    omega

private theorem power_primitive_prime {p n : ℕ} (hp : 3 ≤ p) (oddp : Odd p) (hn : 2 < n) :
    ∃ q : ℕ, q.Prime ∧ orderOf (p : ZMod q) = n := by
  let F := ((cyclotomic n ℤ).eval (p : ℤ)).natAbs
  have hF : 1 < F := lt_of_le_of_lt (by omega : 1 ≤ p-1)
    (sub_one_lt_natAbs_cyclotomic_eval (n:=n) (by omega) (by omega))
  by_contra miss
  have dividing {q : ℕ} (pq : q.Prime) (dv : q ∣ F) : q ∣ n := by
    by_contra nd
    have o := (power_cyclotomic_order (p:=p) (n:=n) (by omega) pq dv).1
    simp [Nat.factorization_eq_zero_of_not_dvd nd] at o
    exact miss ⟨q,pq,o⟩
  have lesser {q s : ℕ} (pq : q.Prime) (ps : s.Prime) (hq : q ∣ F)
      (hs : s ∣ F) (ne : s ≠ q) : s < q := by
    have hd := dividing ps hs
    have form := Nat.ordProj_mul_ordCompl_eq_self n q
    change q^n.factorization q * (n/q^n.factorization q)=n at form
    rw [← form] at hd
    rcases ps.dvd_mul.mp hd with h | h
    · exact (ne ((Nat.prime_dvd_prime_iff_eq ps pq).mp (ps.dvd_of_dvd_pow h))).elim
    · have hlt := Nat.le_of_dvd (by have := pq.one_lt; omega : 0 < q-1)
        (h.trans (power_cyclotomic_order (p:=p) (n:=n) (by omega) pq hq).2)
      omega
  obtain ⟨q,pq,hq⟩ := Nat.exists_prime_and_dvd (n:=F) (by omega)
  have fpow := Nat.eq_prime_pow_of_unique_prime_dvd (by omega : F ≠ 0) (p:=q) (by
    intro s ps hs
    by_contra ne
    have h := lesser pq ps hq hs ne
    have h' := lesser ps pq hs hq (Ne.symm ne)
    omega)
  have dn := dividing pq hq
  have tdiv := Nat.totient_dvd_of_dvd dn
  rw [Nat.totient_prime pq] at tdiv
  have tle := Nat.le_of_dvd (Nat.totient_pos.mpr (by omega : 0 < n)) tdiv
  have qF : q < F := calc
    q ≤ 2^(q-1) := by have h : q-1 < 2^(q-1) := Nat.lt_two_pow_self; omega
    _ ≤ (p-1)^n.totient := by gcongr <;> omega
    _ < F := sub_one_pow_totient_lt_natAbs_cyclotomic_eval (by omega) (by omega)
  have len : 2 ≤ F.primeFactorsList.length := by
    by_contra! h
    interval_cases he : F.primeFactorsList.length <;> simp at fpow <;> omega
  apply power_cyclotomic_no_square hp oddp hn pq dn hq
  change q^2 ∣ F
  conv_rhs => rw [fpow]
  exact pow_dvd_pow q len

private theorem power_primitive_plus {p k : ℕ} (hp : 3 ≤ p) (oddp : Odd p) (hk : 1 < k) :
    ∃ q : ℕ, q.Prime ∧ orderOf (p : ZMod q) = 2*k ∧ 2*k < q ∧ q ∣ p^k+1 := by
  obtain ⟨q,pq,eqo⟩ := power_primitive_prime hp oddp (n:=2*k) (by omega)
  let : Fact q.Prime := ⟨pq⟩
  have eq1 := pow_orderOf_eq_one (p : ZMod q)
  rw [eqo] at eq1
  have p0 : (p : ZMod q) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : 2*k ≠ 0)] at eq1
    exact zero_ne_one eq1
  have dl := ZMod.orderOf_dvd_card_sub_one p0
  rw [eqo] at dl
  have small := Nat.le_of_dvd (by have := pq.one_lt; omega : 0 < q-1) dl
  refine ⟨q,pq,eqo,by omega,?_⟩
  have sq1 : ((p : ZMod q)^k)^2 = 1 := by rw [← pow_mul,Nat.mul_comm k 2]; exact eq1
  rcases sq_eq_one_iff.mp sq1 with bad | good
  · have dk := orderOf_dvd_of_pow_eq_one bad
    rw [eqo] at dk
    have := Nat.le_of_dvd (by omega : 0 < k) dk
    omega
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_add,Nat.cast_one,Nat.cast_pow,good,neg_add_cancel]

private theorem power_exponent_odd_witness {p k u t : ℕ} (hp : 3 ≤ p) (oddp : Odd p)
    (ht : 1 < t) (oddt : Odd t) (hk : 1 < k) (gap : p^u < 2*k) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^(t*k+u)+d ∧ s ∣ p^(t*k+u)+d := by
  have ltprod : k < t*k := by nlinarith
  obtain ⟨q,pq,oq,hq,dq⟩ := power_primitive_plus hp oddp (k:=t*k) (by omega)
  obtain ⟨s,ps,os,hs,ds⟩ := power_primitive_plus hp oddp hk
  have differ : q ≠ s := by intro e; subst s; omega
  have d3 : p^k+1 ∣ p^(t*k)+1 := by
    rw [Nat.mul_comm t k, pow_mul]
    simpa only [one_pow] using oddt.nat_add_dvd_pow_add_pow (p^k) 1
  have factor : p^(t*k+u)+p^u=(p^(t*k)+1)*p^u := by rw [pow_add,add_mul,one_mul]
  refine ⟨p^u,q,s,pq,ps,differ,by omega,by omega,?_,?_⟩ <;> rw [factor]
  · exact dvd_mul_of_dvd_left dq _
  · exact dvd_mul_of_dvd_left (ds.trans d3) _

theorem power_missing_exponent_bound {p r : ℕ} (hp : 3 ≤ p) (oddp : Odd p)
    (pr : r.Prime) (hr : 5 ≤ r)
    (miss : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^r+d ∧ s ∣ p^r+d) :
    2*(r-2) ≤ 3*p^2 := by
  have nz : r%3 ≠ 0 := by
    intro eqn
    have dv := Nat.dvd_of_mod_eq_zero eqn
    have eqr := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) pr).mp dv
    omega
  by_contra! h
  have pp : p ≤ p^2 := by nlinarith
  let k := r/3
  have hk : 1 < k := by dsimp [k]; omega
  have eu := Nat.mod_add_div r 3
  change r%3+3*k=r at eu
  by_cases eqn : r%3=1
  · have ww := power_exponent_odd_witness hp oddp (u:=1) (by decide : 1 < 3)
      (by decide) hk (by simp; omega)
    apply miss
    rwa [show 3*k+1=r by omega] at ww
  · have ww := power_exponent_odd_witness hp oddp (u:=2) (by decide : 1 < 3)
      (by decide) hk (by omega)
    apply miss
    rwa [show 3*k+2=r by omega] at ww



theorem power_missing_exponent_linear {p r : ℕ} (hp : 3 ≤ p) (oddp : Odd p)
    (modr : r%3 = 1)
    (miss : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ p^r+d ∧ s ∣ p^r+d) :
    2*(r-1) ≤ 3*p := by
  by_contra! h
  let k := r/3
  have eu := Nat.mod_add_div r 3
  change r%3+3*k=r at eu
  have ww := power_exponent_odd_witness hp oddp (u:=1) (by decide : 1 < 3)
    (by decide) (k:=k) (by omega) (by simp; omega)
  apply miss
  rwa [show 3*k+1=r by omega] at ww



end Erdos889.PrimitivePowers
namespace Erdos889.Missing
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

-- BEGIN MISSING WITNESS
/-- Absence of a two-prime witness exactly bounds every count at the predecessor, and offset one attains the bound. -/
theorem predecessor_solution_of_missing {N : ℕ} (big : 1 < N)
    (none : ¬ ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q ≠ s ∧ d+1 < q ∧ d+1 < s ∧
      q ∣ N+d ∧ s ∣ N+d) : v_l 1 (N-1)=1 := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply iSup_le
    intro hk
    have bound : v (N-1) k ≤ 1 := by
      rw [v_as_card,Finset.card_le_one]
      intro q hq s hs
      obtain ⟨cq,bq⟩ := Finset.mem_filter.mp hq
      obtain ⟨cs,bs⟩ := Finset.mem_filter.mp hs
      have eq : N+(k-1)=(N-1)+k := by omega
      by_contra ne
      exact none ⟨k-1,q,s,Nat.prime_of_mem_primeFactors cq,Nat.prime_of_mem_primeFactors cs,ne,
        by omega,by omega,eq ▸ Nat.dvd_of_mem_primeFactors cq,eq ▸ Nat.dvd_of_mem_primeFactors cs⟩
    exact_mod_cast bound
  · obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd (show N≠1 by omega)
    have eq : N-1+1=N := by omega
    have first : 1 ≤ v (N-1) 1 := by
      rw [v_as_card,eq]
      exact Finset.card_pos.mpr ⟨q,Finset.mem_filter.mpr ⟨pq.mem_primeFactors dq (by omega),pq.one_lt⟩⟩
    exact (show (1 : ℕ∞) ≤ (v (N-1) 1 : ℕ∞) by exact_mod_cast first).trans
      (le_iSup_of_le 1 (le_iSup_of_le (by decide : 1≤1) le_rfl))
-- END MISSING WITNESS

end Erdos889.Missing

namespace OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H3_R1
open Erdos889
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2


open Finset
private theorem seventeen_smooth_cycle {x t m : ℕ} (h : Nat.ModEq m (x^t) 1) (b : ℕ) :
    Nat.ModEq m (x^b) (x^(b%t)) := by
  calc
    x^b = x^(b%t)*(x^t)^(b/t) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
    _ ≡ x^(b%t)*1^(b/t) [MOD m] := (h.pow _).mul_left _
    _ = _ := by simp

private theorem seventeen_smooth_legendre (m n : ℕ) [Fact m.Prime] (hm : 2 < m) :
    legendreSym m (n:ℤ) = if n%m=0 then 0 else if ((n%m)^(m/2))%m=1 then 1 else -1 := by
  have cast : ((n:ℤ):ZMod m)=(n:ZMod m) := by simp
  by_cases z : n%m=0
  · rw [if_pos z,legendreSym.eq_zero_iff,cast,ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero z
  rw [if_neg z]
  have nz : ((n:ℤ):ZMod m)≠0 := by
    intro h
    rw [cast] at h
    exact z (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff n m).mp h))
  have power : ((n%m)^(m/2))%m=1 ↔ (n:ZMod m)^(m/2)=1 := by
    have eq := ZMod.natCast_eq_natCast_iff' ((n%m)^(m/2)) 1 m
    rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at eq
    simpa only [Nat.cast_pow,ZMod.natCast_mod,Nat.cast_one] using eq.symm
  have sign := legendreSym.eq_pow m (n:ℤ)
  rw [cast] at sign
  rcases legendreSym.eq_one_or_neg_one m nz with h|h
  · rw [h,Int.cast_one] at sign
    rw [h,if_pos (power.mpr sign.symm)]
  · rw [h,Int.cast_neg,Int.cast_one] at sign
    rw [h,if_neg]
    intro bad
    have eq : (-1:ZMod m)=1 := sign.trans (power.mp bad)
    have zero : ((2:ℕ):ZMod m)=0 := by push_cast; linear_combination -eq
    have dd := (ZMod.natCast_eq_zero_iff _ _).mp zero
    have le := Nat.le_of_dvd (by decide) dd
    omega

private theorem seventeen_smooth_character_mul (m : ℕ) (ok : m=4 ∨ m=8 ∨ (m.Prime ∧ 2 < m)) :
    let char (n : ℕ) : ℤ := if m=4 then (if n%2=0 then 0 else if n%4=1 then 1 else -1)
    else if m=8 then (if n%2=0 then 0 else if n%8=1 ∨ n%8=7 then 1 else -1)
    else if n%m=0 then 0 else if ((n%m)^(m/2))%m=1 then 1 else -1
    ∀ u v, char (u*v)=char u*char v := by
  dsimp only
  rcases ok with rfl|rfl|⟨pm,hm⟩
  · intro u v
    simp only [if_true]
    simpa only [ZMod.χ₄_nat_eq_if_mod_four] using
      (show ZMod.χ₄ ((u*v:ℕ):ZMod 4)=ZMod.χ₄ (u:ZMod 4)*ZMod.χ₄ (v:ZMod 4) by rw [Nat.cast_mul,map_mul])
  · intro u v
    simp only [show (8:ℕ)≠4 by decide,if_false,if_true]
    simpa only [ZMod.χ₈_nat_eq_if_mod_eight] using
      (show ZMod.χ₈ ((u*v:ℕ):ZMod 8)=ZMod.χ₈ (u:ZMod 8)*ZMod.χ₈ (v:ZMod 8) by rw [Nat.cast_mul,map_mul])
  · intro u v
    let _ : Fact m.Prime := ⟨pm⟩
    have n4 : m≠4 := by rintro rfl; norm_num at pm
    have n8 : m≠8 := by rintro rfl; norm_num at pm
    simp only [n4,n8,if_false,←seventeen_smooth_legendre m _ hm,Nat.cast_mul,legendreSym.mul]

-- BEGIN SEVENTEEN
private theorem seventeen_smooth_powMod_eq (a e m : ℕ) : (fun (a e m : ℕ) => Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%m) (fun _ f n => (f (n/2))^2 * a^(n%2) % m) (e.log2+1) e) a e m = a^e % m := by
  let f (k : ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%m)
    (fun _ g n => (g (n/2))^2 * a^(n%2) % m) k
  have aux (k n : ℕ) (bound : n<2^k) : f k n = a^n % m := by
    induction k generalizing n with
    | zero =>
      have h : n=0 := by simpa using bound
      subst n
      simp [f]
    | succ k ih =>
      have half : n/2 < 2^k := by rw [pow_succ] at bound; omega
      change (f k (n/2))^2 * a^(n%2) % m = a^n % m
      rw [ih _ half]
      calc
        _ = ((a^(n/2))^2 * a^(n%2))%m :=
          ((Nat.mod_modEq _ _).pow 2).mul_right _
        _ = a^n % m := by
          rw [← pow_mul,← pow_add,show n/2*2+n%2=n by omega]
  change f (e.log2+1) e = a^e % m
  apply aux (e.log2+1) e
  by_cases h : e=0
  · subst e
    decide
  · exact (Nat.log2_lt h).mp (Nat.lt_succ_self _)


private theorem seventeen_smooth_residue {p b T k m : ℕ} (base : p+1=2^b) (idx : b%T=k)
    (hm : 1 < m) (per : 2^T%m=1) :
    Nat.ModEq m p ((2^k%m+m-1)%m) := by
  have period : Nat.ModEq m (2^T) 1 := by change 2^T%m=1%m; rwa [Nat.mod_eq_of_lt hm]
  have c := seventeen_smooth_cycle period b
  rw [idx,←base] at c
  have h : Nat.ModEq m ((2^k%m+m-1)+1) (2^k) := by
    rw [show 2^k%m+m-1+1=2^k%m+m by omega]
    change (2^k%m+m)%m=2^k%m
    simp
  exact (Nat.ModEq.add_right_cancel' 1 (c.trans h.symm)).trans (Nat.mod_modEq _ _).symm

private theorem seventeen_smooth_primes : ∀ s ∈ [3,5,7,11,17,19,29,37,71,73,103,137,239,307,337,409,433,613,919,953,1321,2521,10711,14449,34511], Nat.Prime s := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num1

private theorem seventeen_smooth_row {p b T k : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%T=k)
    (d q : ℕ) (S ms : List ℕ) (pm : ℕ → ℕ → ℕ → ℕ)
    (hpm : ∀ a e m, pm a e m=a^e%m)
    {pool : List ℕ} (facts : ∀ s ∈ pool, s.Prime)
    (ok :
      let V (m : ℕ) := ((pm 2 k m+m-1)%m)^17+d
      let C (m n : ℕ) : ℤ := if n%m=0 then 0 else if pm (n%m) (m/2) m=1 then 1 else -1
      q∈pool ∧ d+1 < q ∧ q∈S ∧ pm 2 T q=1 ∧ V q%q=0 ∧
      (∀ s ∈ List.range (d+2), s.Prime → s∈S ∨ (pm 2 T s=1 ∧ V s%s≠0)) ∧
      (∀ m ∈ ms, m∈pool ∧ 2 < m ∧ m≠4 ∧ m≠8 ∧ pm 2 T m=1) ∧
      (∀ s ∈ S, (ms.map (fun m => C m s)).prod=1) ∧
      (ms.map (fun m => C m (V m))).prod= -1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d := by
  let V (m : ℕ) := ((pm 2 k m+m-1)%m)^17+d
  let C (m n : ℕ) : ℤ := if n%m=0 then 0 else if pm (n%m) (m/2) m=1 then 1 else -1
  obtain ⟨qm,large,qmem,qper,qzero,small,mods,good,bad⟩ := ok
  have pq := facts q qm
  have red {m : ℕ} (hm : 1 < m) (per : pm 2 T m=1) : Nat.ModEq m (p^17+d) (V m) := by
    dsimp only [V]; rw [hpm]
    exact ((seventeen_smooth_residue base idx hm ((hpm ..) ▸ per)).pow 17).add_right d
  have dq : q ∣ p^17+d := Nat.modEq_zero_iff_dvd.mp ((red pq.one_lt qper).trans qzero)
  by_contra missing
  have support (s : ℕ) (ps : s.Prime) (ds : s ∣ p^17+d) : s∈S := by
    by_cases h : s=q
    · exact h ▸ qmem
    by_cases high : d+1 < s
    · exact (missing ⟨d,q,s,pq,ps,Ne.symm h,large,high,dq,ds⟩).elim
    rcases small s (List.mem_range.mpr (by omega)) ps with mem|⟨per,nonzero⟩
    · exact mem
    exact (nonzero ((red ps.one_lt per).symm.trans (Nat.modEq_zero_iff_dvd.mpr ds))).elim
  let chi (n : ℕ) := (ms.map (fun m => C m n)).prod
  have mul (u v : ℕ) : chi (u*v)=chi u*chi v := by
    have gm (m) (hm : m∈ms) : C m (u*v)=C m u*C m v := by
      obtain ⟨known,lt,h4,h8,_⟩ := mods m hm
      have prim := facts m known
      simpa only [C,hpm,h4,h8,if_false] using
        (seventeen_smooth_character_mul m (Or.inr (Or.inr ⟨prim,lt⟩)) u v)
    have gen (l : List ℕ) (h : ∀ m ∈ l, C m (u*v)=C m u*C m v) :
        (l.map (fun m => C m (u*v))).prod=(l.map (fun m => C m u)).prod*(l.map (fun m => C m v)).prod := by
      induction l with
      | nil => simp
      | cons m tail ih =>
        simp only [List.map_cons,List.prod_cons]
        rw [h m (by simp),ih (fun j hj => h j (by simp [hj]))]
        ring
    exact gen ms gm
  have neg : chi (p^17+d)= -1 := by
    apply Eq.trans (congrArg List.prod (List.map_congr_left (l:=ms) (f:=fun m => C m (p^17+d)) (g:=fun m => C m (V m)) ?_)) bad
    intro m hm
    obtain ⟨_,lt,_,_,per⟩ := mods m hm
    have eq : (p^17+d)%m=V m%m := red (by omega) per
    simp only [C,eq]
  have one : chi 1=1 := by
    have h := mul 1 (p^17+d)
    rw [one_mul,neg] at h
    omega
  have gen (l : List ℕ) (h : ∀ s ∈ l,s ∈ S) : chi l.prod=1 := by
    induction l with
    | nil => exact one
    | cons s tail ih =>
      rw [List.prod_cons,mul,show chi s=1 from good s (h s (by simp)),one_mul]
      exact ih (fun j hj => h j (by simp [hj]))
  have pos := gen (p^17+d).primeFactorsList (fun s h => support s (Nat.prime_of_mem_primeFactorsList h) (Nat.dvd_of_mem_primeFactorsList h))
  rw [Nat.prod_primeFactorsList (by positivity),neg] at pos
  contradiction


set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_361 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=361) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 14 29 [2,3,5,29] [71] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_673 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=673) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 2 37 [2,3,37] [73] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_841 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=841) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 8 37 [2,3,37] [433] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1201 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1201) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 8 37 [2,3,37] [337] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1321 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1321) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 2 37 [2,3,37] [73] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1513 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1513) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 5 11 [2,3,11] [1321] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1681 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1681) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 2 37 [2,3,37] [73] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1793 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1793) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 2 7 [2,3,7] [2521] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_1873 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=1873) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 5 11 [2,3,11] [1321] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_2520_2161 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%2520=2161) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 8 29 [2,3,29] [14449] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_2521 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=2521) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 1 34511 [2,34511] [953] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_5041 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=5041) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 10 239 [2,11,239] [10711] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_7561 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=7561) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 21 613 [2,11,613] [137] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_12601 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=12601) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 10 137 [2,11,137] [3,5,103] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_15121 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=15121) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 33 307 [2,17,23,307] [409] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_17641 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=17641) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 47 103 [2,3,23,47,103] [34511] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_20161 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=20161) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 1 103 [2,103] [137] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_22681 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=22681) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 7 409 [2,409] [103] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_25201 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=25201) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 1 103 [2,103] [409] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_27721 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=27721) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 1 613 [2,613] [103] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_30241 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=30241) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 38 239 [2,3,13,23,239] [7,11,17,19,137] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_32761 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=32761) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 53 307 [2,3,23,47,53,307] [7,11,17,19,137] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_35281 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=35281) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 17 307 [2,3,307] [409] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_37801 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=37801) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 46 103 [2,23,47,103] [919] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem case17_42840_40321 {p b : ℕ} (hp : 0 < p) (base : p+1=2^b) (idx : b%42840=40321) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d :=
  seventeen_smooth_row hp base idx 57 103 [2,23,29,47,53,103] [3,5,7,409] _ seventeen_smooth_powMod_eq seventeen_smooth_primes (by decide +kernel)

private theorem seventeen_compact_coset {G : Type*} [Monoid G] {v : G} {M b o : ℕ}
    (idx : b%M=1) (per : v^o=1) :
    (v^b)^(o/o.gcd M)=v^(o/o.gcd M) := by
  have form : b = 1+M*(b/M) := by have h := Nat.mod_add_div b M; rw [idx] at h; exact h.symm
  have dm : o∣M*(o/o.gcd M) := by
    rw [←Nat.mul_div_assoc M (Nat.gcd_dvd_left o M),Nat.mul_comm M o,←Nat.lcm_eq_mul_div]
    exact Nat.dvd_lcm_left o M
  obtain ⟨s,hs⟩ := dm
  let h := o/o.gcd M
  have exp : b*h=h+o*(s*(b/M)) := by
    calc
      b*h=(1+M*(b/M))*h := congrArg (·*h) form
      _ = h+(M*h)*(b/M) := by ring
      _ = h+o*(s*(b/M)) := by rw [show M*h=o*s from hs]; ring
  change (v^b)^h = v^h
  rw [←pow_mul,exp,pow_add,pow_mul,per,one_pow,mul_one]

private theorem seventeen_compact_root_exclusion {p b q o w : ℕ}
    (pq : q.Prime) (lo : 2 < q) (base : p+1=2^b) (idx : b%42840=1)
    (mult : q∣p^17+131072) (nd : ¬q∣p+2)
    (per : 2^o%q=1) (w19 : w^17%q=1) (wn : w%q≠1)
    (reject : ∀ i ∈ List.range 16,
      let y := (q+1-(2*w^(i+1))%q)%q
      y^(o/o.gcd 42840)%q≠2^(o/o.gcd 42840)%q) : False := by
  let _ : Fact q.Prime := ⟨pq⟩
  let _ : Fact (Nat.Prime 17) := ⟨by decide⟩
  have mod1 (v : ℕ) : (v:ZMod q)=1 ↔ v%q=1 := by
    simpa only [Nat.cast_one,Nat.mod_eq_of_lt pq.one_lt] using ZMod.natCast_eq_natCast_iff' v 1 q
  have two : (2:ZMod q)≠0 := by
    intro h
    have d := (ZMod.natCast_eq_zero_iff 2 q).mp h
    have := Nat.le_of_dvd (by decide : 0<2) d
    omega
  let z := -(p:ZMod q)/2
  have zero := (ZMod.natCast_eq_zero_iff _ _).mpr mult
  push_cast at zero
  have z19 : z^17=1 := by dsimp [z]; rw [div_pow,div_eq_iff (pow_ne_zero _ two)]; linear_combination -zero
  have primitive : IsPrimitiveRoot (w:ZMod q) 17 := IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime
    (by simpa only [Nat.cast_pow] using (mod1 _).mpr w19) (fun h => wn ((mod1 _).mp h)))
  obtain ⟨i,hi,iw⟩ := primitive.eq_pow_of_pow_eq_one z19
  have wv : (w:ZMod q)^i * 2 = -(p:ZMod q) := (eq_div_iff two).mp iw
  have i0 : i≠0 := by
    rintro rfl
    rw [pow_zero,one_mul] at wv
    apply nd
    apply (ZMod.natCast_eq_zero_iff (p+2) q).mp
    push_cast
    linear_combination wv
  let y := (q+1-(2*w^i)%q)%q
  have bound : (2*w^i)%q ≤ q+1 := by have := Nat.mod_lt (2*w^i) pq.pos; omega
  have cast : (y:ZMod q)=(2:ZMod q)^b := by
    dsimp [y]
    rw [ZMod.natCast_mod,Nat.cast_sub bound,Nat.cast_add,ZMod.natCast_self,Nat.cast_one,ZMod.natCast_mod,Nat.cast_mul,Nat.cast_pow]
    have bp := congrArg (fun n : ℕ => (n:ZMod q)) base
    push_cast at bp ⊢
    linear_combination bp - wv
  have cycle : (2:ZMod q)^o=1 := by simpa only [Nat.cast_pow,Nat.cast_ofNat] using (mod1 _).mpr per
  have projected := seventeen_compact_coset idx cycle
  rw [←cast] at projected
  have bad := reject (i-1) (List.mem_range.mpr (show i-1<16 by omega))
  rw [show i-1+1=i by omega] at bad
  apply bad
  apply (ZMod.natCast_eq_natCast_iff' _ _ q).mp
  push_cast
  exact projected

private theorem seventeen_compact_pow_eq (a e m : ℕ) : (fun (a e m : ℕ) => Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%m) (fun _ f n => (f (n/2))^2 * a^(n%2) % m) (e.log2+1) e) a e m = a^e % m := by
  let f (k : ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%m)
    (fun _ g n => (g (n/2))^2 * a^(n%2) % m) k
  have aux (k n : ℕ) (bound : n<2^k) : f k n = a^n % m := by
    induction k generalizing n with
    | zero =>
      have h : n=0 := by simpa using bound
      subst n
      simp [f]
    | succ k ih =>
      have half : n/2 < 2^k := by rw [pow_succ] at bound; omega
      change (f k (n/2))^2 * a^(n%2) % m = a^n % m
      rw [ih _ half]
      calc
        _ = ((a^(n/2))^2 * a^(n%2))%m :=
          ((Nat.mod_modEq _ _).pow 2).mul_right _
        _ = a^n % m := by
          rw [← pow_mul,← pow_add,show n/2*2+n%2=n by omega]
  change f (e.log2+1) e = a^e % m
  apply aux (e.log2+1) e
  by_cases h : e=0
  · subst e
    decide
  · exact (Nat.log2_lt h).mp (Nat.lt_succ_self _)

private theorem seventeen_compact_legendre (m n : ℕ) [Fact m.Prime] (hm : 2 < m) :
    legendreSym m (n:ℤ) = if n%m=0 then 0 else if ((n%m)^(m/2))%m=1 then 1 else -1 := by
  have cast : ((n:ℤ):ZMod m)=(n:ZMod m) := by simp
  by_cases z : n%m=0
  · rw [if_pos z,legendreSym.eq_zero_iff,cast,ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero z
  rw [if_neg z]
  have nz : ((n:ℤ):ZMod m)≠0 := by
    intro h
    rw [cast] at h
    exact z (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff n m).mp h))
  have power : ((n%m)^(m/2))%m=1 ↔ (n:ZMod m)^(m/2)=1 := by
    have eq := ZMod.natCast_eq_natCast_iff' ((n%m)^(m/2)) 1 m
    rw [Nat.mod_eq_of_lt (by omega : 1 < m)] at eq
    simpa only [Nat.cast_pow,ZMod.natCast_mod,Nat.cast_one] using eq.symm
  have sign := legendreSym.eq_pow m (n:ℤ)
  rw [cast] at sign
  rcases legendreSym.eq_one_or_neg_one m nz with h|h
  · rw [h,Int.cast_one] at sign
    rw [h,if_pos (power.mpr sign.symm)]
  · rw [h,Int.cast_neg,Int.cast_one] at sign
    rw [h,if_neg]
    intro bad
    have eq : (-1:ZMod m)=1 := sign.trans (power.mp bad)
    have zero : ((2:ℕ):ZMod m)=0 := by push_cast; linear_combination -eq
    have dd := (ZMod.natCast_eq_zero_iff _ _).mp zero
    have le := Nat.le_of_dvd (by decide) dd
    omega

set_option maxRecDepth 12000 in
private theorem seventeen_compact_interval {i start p b : ℕ} {N : ℤ} (cells : List ℕ)
    (pm : ℕ → ℕ → ℕ → ℕ) (eq : ∀ a e m, pm a e m=a^e%m)
    (checked : (cells.zipIdx start).all (fun entry =>
      let tok := entry.1
      let q := 34*entry.2+1
      if tok=0 then decide (q < 2)
      else if tok < 1024 then decide (1 < tok ∧ tok < q ∧ q%tok=0)
      else if tok=1024 then
        let a := (N%(q:ℤ)).toNat
        decide (a%q≠0 ∧ pm (a%q) (q/2) q=1)
      else
        let o := (tok-1025)/131072
        let w := (tok-1025)%131072
        decide (pm 2 o q=1 ∧ w^17%q=1 ∧ w%q≠1) &&
          (List.range 16).all (fun k =>
            let y := (q+1-(2*w^(k+1))%q)%q
            decide (pm y (o/o.gcd 42840) q≠pm 2 (o/o.gcd 42840) q)))=true)
    (low : start ≤ i) (high : i < start+cells.length)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym N (34*i+1)=1 := by
  let q := 34*i+1
  have qlo : 2 < q := by dsimp [q]; have := pq.two_le; omega
  have inside : i-start < cells.length := by omega
  let tok := cells[i-start]
  have mem : (tok,i) ∈ cells.zipIdx start := List.mk_mem_zipIdx_iff_le_and_getElem?_sub.mpr
    ⟨low, List.getElem?_eq_getElem inside⟩
  have h := List.all_eq_true.mp checked (tok,i) mem
  dsimp only at h
  by_cases z : tok=0
  · rw [if_pos z] at h
    have := of_decide_eq_true h
    omega
  rw [if_neg z] at h
  by_cases sm : tok<1024
  · rw [if_pos sm] at h
    obtain ⟨a,l,d⟩ := of_decide_eq_true h
    have := (Nat.dvd_prime pq).mp (Nat.dvd_iff_mod_eq_zero.mpr d)
    omega
  rw [if_neg sm] at h
  by_cases pos : tok=1024
  · rw [if_pos pos] at h
    obtain ⟨nz,pow1⟩ := of_decide_eq_true h
    let a := (N%(q:ℤ)).toNat
    have cast : (a:ℤ)=N%(q:ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg N (by exact_mod_cast (show q≠0 by omega)))
    let _ : Fact q.Prime := ⟨pq⟩
    change jacobiSym N q=1
    rw [jacobiSym.mod_left N q,←cast,←jacobiSym.legendreSym.to_jacobiSym,seventeen_compact_legendre q a qlo,
      if_neg nz,if_pos (by simpa only [←eq] using pow1)]
  rw [if_neg pos] at h
  obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨period,root,nontriv⟩ := of_decide_eq_true head
  exfalso
  rw [eq] at period
  apply seventeen_compact_root_exclusion (o:=(tok-1025)/131072) (w:=(tok-1025)%131072) pq qlo base idx mult nd period root nontriv
  intro k hk
  have reject := of_decide_eq_true (List.all_eq_true.mp tail k hk)
  simpa only [eq] using reject


set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_0 {i p b : ℕ} (ix : i/128=0) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=0) (cells:=[0,5,3,6685761,8914040,3,5,15598725,3,1024,11,3,26739749,1024,3,7,5,3,80217675,1024,3,5,7,3,19,23,3,20055457,8914723,3,1024,5,3,1024,13,3,5,1024,3,1024,89130301,3,11012367,7,3,1024,5,3,23,1024,3,5,29,3,11,122553354,3,7,1024,3,13,5,3,6687509,7,3,5,43,3,102500113,1024,3,31,13,3,167119914,5,3,7,1024,3,5,1024,3,1024,7,3,11,41,3,26740717,5,3,138153842,23,3,5,1024,3,7,19,3,454559816,31,3,467929912,5,3,1024,11,3,5,13,3,508037136,1024,3,23,1024,3,7,5,3,47,1024,3,5,7])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<128; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_1 {i p b : ℕ} (ix : i/128=1) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=128) (cells:=[3,41,44565988,3,67,34870458,3,1024,5,3,13,29,3,5,11,3,59,129240931,3,1024,7,3,222823791,5,3,11,1024,3,5,19,3,354290873,71304879,3,7,23,3,31,5,3,29,7,3,5,1024,3,61,11,3,13,1024,3,200543423,5,3,7,1024,3,5,416679046,3,1024,7,3,13375823,50596767,3,19,5,3,1024,67,3,5,900207641,3,7,1024,3,1024,11,3,37,5,3,949225349,19,3,5,47,3,11,245109333,3,989333279,1024,3,7,5,3,1024,13,3,5,7,3,73,61,3,1024,1060638123,3,1024,5,3,541464612,543688160,3,5,37,3,1024,1024,3,11,7,3,13])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<256; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_2 {i p b : ℕ} (ix : i/128=2) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=256) (cells:=[5,3,31,1024,3,5,59,3,47,1024,3,7,13,3,1203244513,5,3,1216619480,7,3,5,1234442290,3,53,1024,3,43,1024,3,11,5,3,7,31,3,5,38280336,3,13,7,3,1024,1024,3,101,5,3,225056183,1024,3,5,11,3,7,83,3,103,29,3,140380497,5,3,11,1024,3,5,1434982194,3,23,43,3,6688151,19,3,7,5,3,13,41,3,5,7,3,755373466,11,3,29,107,3,1024,5,3,1024,1024,3,5,392171157,3,92801583,1024,3,61,7,3,1024,5,3,1024,1024,3,5,1024,3,1024,23,3,7,11,3,41,5,3,187179916,7,3,5,31,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<384; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_3 {i p b : ℕ} (ix : i/128=3) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=384) (cells:=[11,13,3,1024,79,3,89,5,3,7,1755845330,3,5,104079248,3,1024,7,3,1024,71,3,47,5,3,1024,1822691321,3,5,1024,3,7,103,3,11,61,3,311959578,5,3,19,13,3,5,1024,3,29,1916287403,3,37,1024,3,7,5,3,53,11,3,5,7,3,31,1024,3,332008962,1024,3,11,5,3,73,43,3,5,41,3,1024,1024,3,23,7,3,97,5,3,347617118,37,3,5,11,3,71,31,3,7,1024,3,19,5,3,11,7,3,5,29,3,13,436743873,3,1024,1024,3,1024,5,3,7,19,3,5,13,3,280772866,7,3,1129712158,23,3,757607994,5])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<512; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_4 {i p b : ℕ} (ix : i/128=4) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=512) (cells:=[3,2286172062,1024,3,5,1024,3,7,231737113,3,1024,1165373841,3,2339641833,5,3,13,1024,3,5,1185426265,3,67,1192116603,3,19,11,3,7,5,3,37,53,3,5,7,3,11,1024,3,137,1024,3,113,5,3,2486699371,83,3,5,97,3,127,1024,3,13,7,3,508036830,5,3,2553554247,29,3,5,23,3,430060784,13,3,7,43,3,2607035237,5,3,1024,7,3,5,1024,3,19,15598721,3,53,1024,3,23,5,3,7,11,3,5,1352533098,3,904664707,7,3,1024,19,3,11,5,3,2754092032,13,3,5,163057287,3,7,79,3,1024,131,3,31,5,3,2820943362,1024,3,5,11,3,474620101])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<640; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_5 {i p b : ℕ} (ix : i/128=5) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=640) (cells:=[47,3,83,1432768942,3,7,5,3,11,2892246689,3,5,7,3,37,1024,3,89,13,3,245111397,5,3,1477325326,107,3,5,1024,3,23,11,3,73,7,3,59,5,3,3021490191,1024,3,5,1024,3,13,1024,3,7,149,3,29,5,3,1024,7,3,5,13,3,1024,389954768,3,1024,11,3,1024,5,3,7,3159628503,3,5,43,3,11,7,3,1024,3199737409,3,1024,5,3,13,103,3,5,19,3,7,3253219612,3,543689308,1024,3,67,5,3,23,1646672347,3,5,3306691027,3,41,73,3,11,29,3,7,5,3,3355721274,31,3,5,7,3,131,1024,3,13,1700143273,3,19,5,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<768; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_6 {i p b : ℕ} (ix : i/128=6) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=768) (cells:=[1024,11,3,5,1024,3,1024,13,3,29,7,3,11,5,3,79,19,3,5,1024,3,139,1024,3,7,59,3,354302420,5,3,43,7,3,5,11,3,1791502740,101,3,23,83,3,240663079,5,3,7,13,3,5,1024,3,1024,7,3,19,1024,3,1024,5,3,47,71,3,5,1853890537,3,7,11,3,149,1024,3,13,5,3,1024,1024,3,5,31,3,1261195916,757602939,3,59,13,3,7,5,3,3823658025,1024,3,5,7,3,29,1024,3,41,11,3,45625164,5,3,1024,3894940331,3,5,229922239,3,11,1960848324,3,3930595611,7,3,788795747,5,3,109,167,3,5,13,3,113,1024])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<896; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_7 {i p b : ℕ} (ix : i/128=7) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=896) (cells:=[3,7,19,3,71,5,3,2012111589,7,3,5,1024,3,31,4055383989,3,11,37,3,53,5,3,7,1024,3,5,23,3,89,7,3,43,139,3,103,5,3,1385968746,11,3,5,1024,3,7,31,3,1024,1024,3,11,5,3,1056204190,41,3,5,2121294970,3,163,19,3,13,4269297944,3,7,5,3,137,73,3,5,7,3,47,13,3,1024,4336151995,3,724202169,5,3,11,1024,3,5,173,3,2192601555,107,3,37,7,3,41,5,3,19,260579971,3,5,109,3,1024,11,3,7,67,3,4478735991,5,3,132123814,7,3,5,19,3,23,77993457,3,151,1024,3,79,5,3,7])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1024; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_8 {i p b : ℕ} (ix : i/128=8) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1024) (cells:=[37,3,5,1024,3,59,7,3,1149785893,11,3,13,5,3,29,1024,3,5,71,3,7,931427378,3,97,13,3,19,5,3,521414526,1024,3,5,83,3,2359698738,23,3,4732760842,47,3,7,5,3,1024,19,3,5,7,3,13,1024,3,11,1024,3,1024,5,3,23,1207700594,3,5,13,3,61,1024,3,107,7,3,31,5,3,37,11,3,5,89,3,1024,4924383575,3,7,101,3,11,5,3,13,7,3,5,163,3,1024,113,3,1024,1024,3,29,5,3,7,23,3,5,11,3,5053632181,7,3,67,5071449094,3,83,5,3,11,97,3,5,59,3,7,61,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1152; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_9 {i p b : ℕ} (ix : i/128=9) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1152) (cells:=[13,197,3,173,5,3,1024,157,3,5,1024,3,19,11,3,2600342848,151,3,7,5,3,1742509994,179,3,5,7,3,1024,53,3,5267528785,19,3,43,5,3,31,1024,3,5,1328036347,3,1024,41,3,1024,7,3,1024,5,3,893537701,13,3,5,1024,3,11,5392321551,3,7,1024,3,109,5,3,1024,7,3,5,418944236,3,1024,5459166085,3,1024,43,3,13,5,3,7,1024,3,5,137,3,103,7,3,11,13,3,1024,5,3,1390446204,1024,3,5,164114653,3,7,71,3,79,329799908,3,62430215,5,3,2814268961,11,3,5,23,3,13,29,3,61,1024,3,7,5,3,19,1024])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1280; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_10 {i p b : ℕ} (ix : i/128=10) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1280) (cells:=[3,5,7,3,149,1024,3,1024,717520930,3,23,5,3,338977312,5766675647,3,5,11,3,29,289675662,3,1024,7,3,5815675899,5,3,11,1024,3,5,31,3,43,1024,3,7,41,3,37,5,3,1024,7,3,5,2956876228,3,73,11,3,1024,61,3,19,5,3,7,53,3,5,103,3,187203319,7,3,13,1024,3,197,5,3,179,19,3,5,29,3,7,13,3,6069728189,11,3,2027720120,5,3,193,89,3,5,1024,3,11,1024,3,6136566840,6140993444,3,7,5,3,59,1024,3,5,7,3,83,167,3,19,6207858281,3,3108375870,5,3,1024,13,3,5,73,3,1024,23,3,11])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1408; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_11 {i p b : ℕ} (ix : i/128=11) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1408) (cells:=[7,3,191,5,3,107,131,3,5,1024,3,3161898714,1024,3,7,3170804667,3,13,5,3,23,7,3,5,181,3,6390586812,97,3,6403924511,13,3,11,5,3,7,29,3,5,1024,3,19,7,3,808867821,127,3,61,5,3,89,113,3,5,11,3,7,1024,3,31,19,3,151,5,3,11,23,3,5,13,3,1024,824470129,3,41,3304491296,3,7,5,3,552607033,1024,3,5,7,3,79,11,3,23,31,3,1024,5,3,13,418942393,3,5,1024,3,1024,6729282279,3,101,7,3,1024,5,3,1024,1024,3,5,6782763496,3,3395848503,19,3,7,11,3,6818402524,5,3,47,7,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1536; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_12 {i p b : ℕ} (ix : i/128=12) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1536) (cells:=[5,1024,3,11,1024,3,13,23,3,131,5,3,7,1024,3,5,1024,3,6925364854,7,3,167,6943189259,3,29,5,3,19,41,3,5,1024,3,7,1024,3,11,79,3,3509503749,5,3,7032322583,37,3,5,19,3,1024,1024,3,3536201138,1024,3,7,5,3,1024,11,3,5,7,3,1024,891334142,3,1024,3571861119,3,11,5,3,1194341934,227,3,5,23,3,7192756703,43,3,2402062164,7,3,13,5,3,139,1024,3,5,11,3,97,157,3,7,13,3,23,5,3,11,7,3,5,1024,3,3663233647,1024,3,29,137,3,294160313,5,3,7,1024,3,5,53,3,13,7,3,1024,3705580983])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1664; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_13 {i p b : ℕ} (ix : i/128=13) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1664) (cells:=[3,824453941,5,3,929223750,7437821289,3,5,13,3,7,3732300797,3,19,59,3,239,5,3,1024,31,3,5,41,3,1024,37,3,1024,11,3,7,5,3,13,61,3,5,7,3,11,29,3,127,951500042,3,53,5,3,1024,101,3,5,1024,3,211,3832569001,3,7674021770,7,3,89,5,3,41,7705201675,3,5,1024,3,19,1024,3,7,1024,3,67,5,3,3883815785,7,3,5,1024,3,7794340224,13,3,71,19,3,3910584982,5,3,7,11,3,5,139,3,37,7,3,73,47,3,11,5,3,23,7905768229,3,5,31,3,7,1024,3,1024,1024,3,137,5,3,3984065846,13,3,5])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1792; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_14 {i p b : ℕ} (ix : i/128=14) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1792) (cells:=[11,3,181,3999717266,3,1024,113,3,7,5,3,11,83,3,5,7,3,8061725723,19,3,1009398324,1024,3,13,5,3,8101883376,23,3,5,8119693457,3,4064300161,11,3,1357025992,7,3,43,5,3,8168680599,127,3,5,481600333,3,31,73,3,7,223,3,1024,5,3,19,7,3,5,1024,3,13,59,3,103,11,3,345414558,5,3,7,4153445781,3,5,13,3,11,7,3,1390434304,43,3,37,5,3,1024,29,3,5,61,3,7,1024,3,83,23,3,179,5,3,13,71,3,5,8453937572,3,1024,1024,3,11,89,3,7,5,3,29,47,3,5,7,3,59,4267089940,3,1024,1024,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<1920; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_15 {i p b : ℕ} (ix : i/128=15) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=1920) (cells:=[97,5,3,151,11,3,5,1024,3,1024,211,3,13,7,3,11,5,3,131,1024,3,5,8654438623,3,157,13,3,7,107,3,1024,5,3,1024,7,3,5,11,3,43,103,3,19,31,3,71,5,3,7,1024,3,5,1098538282,3,41,7,3,1024,109,3,23,5,3,191,13,3,5,260452186,3,7,11,3,89,1024,3,29,5,3,8904009945,1024,3,5,43,3,61,8935236587,3,4472113313,67,3,7,5,3,527762754,1024,3,5,7,3,19,173,3,1024,11,3,31,5,3,53,149,3,5,59,3,11,1024,3,9077815136,7,3,139,5,3,4552273286,325358328,3,5,79])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2048; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_16 {i p b : ℕ} (ix : i/128=16) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2048) (cells:=[3,13,47,3,7,29,3,107,5,3,167,7,3,5,13,3,1024,61,3,11,1024,3,401099184,5,3,7,151,3,5,9256079940,3,1024,7,3,29,1024,3,1024,5,3,13,11,3,5,1024,3,7,19,3,37,1024,3,11,5,3,4685988815,1024,3,5,71,3,1024,1024,3,1024,1024,3,7,5,3,23,4721610941,3,5,7,3,257,75789045,3,13,4741673334,3,3164121597,5,3,11,37,3,5,113,3,1588796710,13,3,67,7,3,3186374819,5,3,199,31,3,5,19,3,1024,11,3,7,239,3,271,5,3,251,7,3,5,1024,3,29,89,3,1613308224,1024,3,4846406085])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2176; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_17 {i p b : ℕ} (ix : i/128=17) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2176) (cells:=[5,3,7,13,3,5,1024,3,1024,7,3,23,11,3,19,5,3,173,1024,3,5,9790889824,3,7,131,3,1024,1024,3,13,5,3,37,19,3,5,2464462777,3,9866591588,127,3,43,13,3,7,5,3,1024,1024,3,5,7,3,1024,9937928573,3,11,23,3,332039874,5,3,47,269,3,5,31,3,13,37,3,19,7,3,113,5,3,1024,11,3,5,13,3,89,43,3,7,1024,3,11,5,3,59,7,3,5,1024,3,1024,1024,3,10147371355,73,3,5080382614,5,3,7,79,3,5,11,3,223,7,3,1024,53,3,1024,5,3,11,5122728626,3,5,23,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2304; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_18 {i p b : ℕ} (ix : i/128=18) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2304) (cells:=[7,109,3,1024,97,3,1024,5,3,3435991995,29,3,5,1024,3,37,11,3,13,19,3,7,5,3,1024,75772614,3,5,7,3,1024,13,3,181,1488497563,3,1738091529,5,3,29,1024,3,5,199,3,1024,10472725673,3,211,7,3,5247544734,5,3,1024,1024,3,5,10526179622,3,11,191,3,7,1024,3,61,5,3,3525052407,7,3,5,1024,3,47,19,3,10615262098,1024,3,83,5,3,7,43,3,5,167,3,23,7,3,11,971565832,3,13,5,3,1024,5356670017,3,5,1024,3,7,67,3,1024,13,3,157,5,3,19,11,3,5,1024,3,73,41,3,179,31,3,7,5])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2432; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_19 {i p b : ℕ} (ix : i/128=19) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2432) (cells:=[3,10842605163,10847042703,3,5,7,3,13,23,3,79,5443597427,3,59,5,3,454581988,1024,3,5,11,3,10936195953,1024,3,139,7,3,1827167075,5,3,11,1024,3,5,37,3,127,137,3,7,47,3,19,5,3,13,7,3,5,1024,3,1024,11,3,1024,29,3,31,5,3,7,19,3,5,73,3,1024,7,3,97,1024,3,53,5,3,269,23,3,5,223,3,7,233,3,13,11,3,47,5,3,109,5624043167,3,5,151,3,11,13,3,19,71,3,7,5,3,1024,173,3,5,7,3,67,11341683545,3,1024,41,3,277,5,3,61,1024,3,5,1024,3,167])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2560; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_20 {i p b : ℕ} (ix : i/128=20) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2560) (cells:=[1024,3,11,7,3,1024,5,3,1024,13,3,5,157,3,1024,29,3,7,23,3,1916283649,5,3,31,7,3,5,1024,3,19,107,3,320884125,131,3,11,5,3,7,97,3,5,1024,3,29,7,3,137,13,3,11631335504,5,3,11644753233,31,3,5,11,3,7,229,3,59,101,3,149,5,3,11,1024,3,5,109,3,13,1024,3,1024,257,3,7,5,3,73,1024,3,5,7,3,1024,11,3,37,1024,3,5915983586,5,3,3948428856,1024,3,5,29,3,53,19,3,5942716391,7,3,23,5,3,13,1024,3,5,1024,3,79,746519061,3,7,11,3,11965618278,5,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2688; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_21 {i p b : ℕ} (ix : i/128=21) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2688) (cells:=[1024,7,3,5,1024,3,11,6005104598,3,107,1024,3,1203297895,5,3,7,89,3,5,31,3,1024,7,3,13,1024,3,2016604328,5,3,12112698733,193,3,5,19,3,7,13,3,11,1024,3,1024,5,3,43,1024,3,5,12197299312,3,23,59,3,4073255286,1024,3,7,5,3,233,11,3,5,7,3,4091042358,47,3,1024,79,3,11,5,3,37,13,3,5,1024,3,31,53,3,307,7,3,6183365994,5,3,29,19,3,5,11,3,103,23,3,7,3106152768,3,13,5,3,11,7,3,5,61,3,59,31,3,47,13,3,283,5,3,7,1024,3,5,67,3,241,7])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2816; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_22 {i p b : ℕ} (ix : i/128=22) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2816) (cells:=[3,19,1024,3,1024,5,3,53,1024,3,5,277,3,7,12611762574,3,1024,12625166238,3,41,5,3,1024,6325949309,3,5,13,3,6337108211,1024,3,6343846863,11,3,7,5,3,1412766340,23,3,5,7,3,11,1024,3,31,311,3,29,5,3,13,12785626943,3,5,1024,3,19,239,3,23,7,3,181,5,3,83,3213114380,3,5,103,3,120361567,97,3,7,19,3,257,5,3,12914883792,7,3,5,12932693951,3,6470801904,43,3,13,1024,3,163,5,3,7,11,3,5,41,3,61,7,3,4340663222,23,3,11,5,3,113,53,3,5,1024,3,7,73,3,1024,191,3,1024,5,3,47])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<2944; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_23 {i p b : ℕ} (ix : i/128=23) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=2944) (cells:=[199,3,5,11,3,4380709542,19,3,29,13159929502,3,7,5,3,11,13,3,5,7,3,179,1024,3,281,1024,3,1024,5,3,271,13253531993,3,5,127,3,1024,11,3,53,7,3,13,5,3,19,1024,3,5,23,3,1024,79,3,7,13,3,1114116055,5,3,6691421146,7,3,5,19,3,263,29,3,3355782968,11,3,23,5,3,7,6727096110,3,5,37,3,11,7,3,101,1024,3,71,5,3,4505564371,43,3,5,13,3,7,41,3,293,157,3,19,5,3,31,83,3,5,3400306074,3,1024,241,3,11,173,3,7,5,3,13,19,3,5,7,3,1024,13681387952,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3072; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_24 {i p b : ℕ} (ix : i/128=24) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3072) (cells:=[149,163,3,1024,5,3,229,11,3,5,1024,3,23,1024,3,1024,7,3,11,5,3,103,59,3,5,29,3,1024,3453765437,3,7,1024,3,193,5,3,1731356610,7,3,5,11,3,239,13,3,131,1024,3,43,5,3,7,1740301373,3,5,6967734555,3,191,7,3,83,37,3,33467767,5,3,13984349892,1024,3,5,317,3,7,11,3,67,1024,3,668522822,5,3,23,13,3,5,1024,3,19,880211547,3,4697197837,41,3,7,5,3,1024,1024,3,5,7,3,311,7074680995,3,109,11,3,13,5,3,1024,29,3,5,1024,3,11,14216090501,3,1024,7,3,7119242479,5,3,227,23])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3200; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_25 {i p b : ℕ} (ix : i/128=25) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3200) (cells:=[3,5,1024,3,41,1024,3,7,420543727,3,1024,5,3,29,7,3,5,1024,3,13,256299583,3,11,1024,3,47,5,3,7,101,3,5,13,3,31,7,3,1024,89,3,1024,5,3,71,11,3,5,53,3,7,1024,3,603947239,1024,3,11,5,3,13,1024,3,5,1024,3,1024,31,3,113,23,3,7,5,3,19,1024,3,5,7,3,143347736,3654304152,3,151,7315354636,3,61,5,3,11,14657351854,3,5,19,3,14679644289,1024,3,13,7,3,29,5,3,7359841892,1024,3,5,229,3,14746488812,11,3,7,1024,3,269,5,3,37,7,3,5,179,3,3703412018,423399573,3,31])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3328; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_26 {i p b : ℕ} (ix : i/128=26) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3328) (cells:=[7415559713,3,19,5,3,7,14857846397,3,5,23,3,107,7,3,199,11,3,4969012185,5,3,67,13,3,5,7469023530,3,7,37,3,157,29,3,23,5,3,1024,220548034,3,5,7502469920,3,1024,149,3,1024,73,3,7,5,3,43,131,3,5,7,3,7540377090,71,3,11,13,3,79,5,3,5040318015,167,3,5,15138611863,3,163,7575980884,3,103,7,3,15174210317,5,3,949285105,11,3,5,1024,3,13,67,3,7,251,3,11,5,3,181,7,3,5,13,3,23,139,3,2549121311,151,3,1024,5,3,7,1024,3,5,11,3,19,7,3,233,59,3,41,5,3,11,15392610458,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3456; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_27 {i p b : ℕ} (ix : i/128=27) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3456) (cells:=[5,15405942290,3,7,47,3,1024,19,3,1024,5,3,61,79,3,5,97,3,29,11,3,1024,1024,3,7,5,3,1024,1024,3,5,7,3,313,15553028519,3,13,113,3,1557566185,5,3,23,1024,3,5,918093535,3,109,13,3,43,7,3,131,5,3,31,157,3,5,197,3,11,19,3,7,1024,3,209488404,5,3,280839619,7,3,5,29,3,15749145560,263,3,241,15766919082,3,37,5,3,7,13,3,5,83,3,67,7,3,11,107,3,7921374773,5,3,19,1024,3,5,163,3,7,53,3,23,3975197009,3,13,5,3,41,11,3,5,19,3,1024,1024,3,313079226,13])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3584; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_28 {i p b : ℕ} (ix : i/128=28) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3584) (cells:=[3,7,5,3,1998793128,1024,3,5,7,3,89,1024,3,1024,71,3,1024,5,3,1024,181,3,5,11,3,13,16087843153,3,127,7,3,19,5,3,11,29,3,5,13,3,1024,59,3,7,293,3,83,5,3,101,7,3,5,31,3,1024,11,3,1024,1024,3,40127123,5,3,7,1024,3,5,227,3,283,7,3,1024,277,3,107,5,3,2720714789,1024,3,5,8171022001,3,7,3271117649,3,19,11,3,8188746704,5,3,1024,43,3,5,23,3,11,349,3,13,37,3,7,5,3,307,1024,3,5,7,3,31,13,3,191,137,3,23,5,3,139,1024,3,5])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3712; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_29 {i p b : ℕ} (ix : i/128=29) (_lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3712) (cells:=[61,3,197,1655628850,3,11,7,3,1024,5,3,8295776420,53,3,5,1024,3,19,31,3,7,1024,3,29,5,3,73,7,3,5,47,3,695221092,1024,3,8349251932,19,3,11,5,3,7,1024,3,5,16742963048,3,1024,7,3,37,97,3,13,5,3,8396070146,16796444127,3,5,11,3,7,1024,3,53,13,3,842285233,5,3,11,1024,3,5,331,3,47,1024,3,31,29,3,7,5,3,263,37,3,5,7,3,13,11,3,8482863651,43,3,281,5,3,16992460848,103,3,5,13,3,41,23,3,29,7,3,5682088558,5,3,157,211,3,5,113,3,61,101,3,7,11,3])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3840; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12000 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_chunk_30 {i p b : ℕ} (ix : i/128=30) (lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  apply seventeen_compact_interval (start:=3840) (cells:=[137,5,3,13,7,3,5,139,3,11,223,3,1024,269,3,2229761])
    _ seventeen_compact_pow_eq
  · decide +kernel
  · omega
  · change i<3856; omega
  · exact pq
  · exact base
  · exact idx
  · exact mult
  · exact nd

set_option maxRecDepth 12288 in
set_option maxHeartbeats 10000000 in
private theorem seventeen_compact_catalog {i p b : ℕ} (lim : i<3856)
    (pq : (34*i+1).Prime) (base : p+1=2^b) (idx : b%42840=1)
    (mult : 34*i+1∣p^17+131072) (nd : ¬34*i+1∣p+2) : jacobiSym (-331523021797516948245918293902945476068223575069568126905840687324892679298721515514419537318572697943073425149822945198110 : ℤ) (34*i+1)=1 := by
  have range : i/128<31 := by omega
  interval_cases h : i/128
  · exact seventeen_compact_chunk_0 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_1 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_2 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_3 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_4 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_5 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_6 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_7 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_8 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_9 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_10 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_11 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_12 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_13 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_14 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_15 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_16 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_17 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_18 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_19 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_20 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_21 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_22 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_23 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_24 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_25 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_26 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_27 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_28 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_29 h lim pq base idx mult nd
  · exact seventeen_compact_chunk_30 h lim pq base idx mult nd

private theorem seventeen_compact_last_fifth {b q : ℕ} (pb : b.Prime) (ob : Odd b) (pq : q.Prime)
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

private theorem seventeen_compact_last_left {b L : ℕ} (pb : b.Prime) (lb : L < b) (hb : 3 < b) :
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
      exact seventeen_compact_last_fifth pb ob pq dq (by omega))
  generalize (2^b+1).primeFactorsList.length = e at eq
  have e2 : 2 ≤ e := by
    by_contra! bad
    interval_cases e <;> norm_num at eq
    all_goals omega
  exact no9 (eq ▸ (pow_dvd_pow (3 : ℕ) e2))


-- Reused when integrating into the reduction.
private theorem seventeen_compact_last_cycle {b m o : ℕ} (hm : Nat.ModEq m (2^o) 1) :
    Nat.ModEq m (2^b) (2^(b%o)) := by
  calc
    2^b = 2^(b%o)*(2^o)^(b/o) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
    _ ≡ 2^(b%o)*1^(b/o) [MOD m] := (hm.pow _).mul_left _
    _ = _ := by simp


private theorem seventeen_compact_last_order {q p : ℕ} (pq : q.Prime) (q2 : q≠2)
    (d : q ∣ p^17+131072) (nd : ¬q ∣ p+2) : 17 ∣ q-1 := by
  let _ : Fact q.Prime := ⟨pq⟩
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have eq := (Nat.prime_dvd_prime_iff_eq pq Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 q).mp h)
    exact q2 eq
  let t : ZMod q := -(p:ZMod q)/2
  have zero := (ZMod.natCast_eq_zero_iff _ _).mpr d
  push_cast at zero
  have eq : t^17=1 := by
    dsimp [t]
    rw [div_pow,div_eq_iff (pow_ne_zero _ h2)]
    linear_combination -zero
  have t1 : t≠1 := by
    intro h
    dsimp [t] at h
    rw [div_eq_iff h2] at h
    apply nd
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    linear_combination -h
  have t0 : t≠0 := by rintro h; rw [h] at eq; simp at eq
  have ord : orderOf t = 17 := ((Nat.dvd_prime (by decide : Nat.Prime 17)).mp
    (orderOf_dvd_of_pow_eq_one eq)).resolve_left (fun h => t1 (orderOf_eq_one_iff.mp h))
  exact ord ▸ ZMod.orderOf_dvd_card_sub_one t0


private theorem seventeen_compact_scaled {p F m k : ℕ} (fac : p^17+131072=(p+2)*F)
    (h : Nat.ModEq m p k) : Nat.ModEq m ((k+2)*F) (k^17+131072) := by
  calc
    (k+2)*F ≡ (p+2)*F [MOD m] := ((h.add_right 2).mul_right F).symm
    _ = p^17+131072 := fac.symm
    _ ≡ k^17+131072 [MOD m] := (h.pow 17).add_right _



private theorem seventeen_compact_common_prime {p F q : ℕ} (fac : p^17+131072=(p+2)*F) (fpos : F≠0)
    (qp : q.Prime) (qlo : 2 < q) (left : q∣p+2) (right : q∣F) : q=17 := by
  let _ : Fact q.Prime := ⟨qp⟩
  have qnp : ¬q∣p := by intro dp; have := Nat.le_of_dvd (by decide : 0<2) ((Nat.dvd_add_iff_right dp).mpr left); omega
  have val := padicValNat.pow_add_pow (x:=p) (y:=2) (qp.odd_of_ne_two (by omega)) left qnp (by decide : Odd 17)
  change padicValNat q (p^17+131072)=_ at val
  rw [fac,padicValNat.mul (by omega) fpos] at val
  have nz := (dvd_iff_padicValNat_ne_zero fpos).mp right
  have l : q∣17 := (dvd_iff_padicValNat_ne_zero (by decide : (17:ℕ)≠0)).mpr (by omega)
  exact (Nat.prime_dvd_prime_iff_eq qp (by decide)).mp l

private theorem seventeen_compact_cofactor_negative {p b F D : ℕ}
    (base : p+1=2^b) (hb : 131073 < b) (idx : b%42840=1) (fac : p^17+131072=(p+2)*F)
    (per : Nat.ModEq (3*D) (2^42840) 1) (cop : Nat.Coprime 8 D) (big : 43691 < D)
    (a8 : Nat.ModEq 8 7 (4*D+43691)) (ad : Nat.ModEq D 43691 (4*D+43691))
    (jac : jacobiSym (-(2*(D:ℤ))) (4*D+43691) = -1) :
    jacobiSym (-(2*(D:ℤ))) F = -1 := by
  have div8 : 8∣2^b := pow_dvd_pow 2 (show 3 ≤ b by omega)
  have p8 : Nat.ModEq 8 p 7 := by change p%8=7; omega
  have f8 : Nat.ModEq 8 F 7 := by
    calc
      F = 1*F := (one_mul _).symm
      _ ≡ (7+2)*F [MOD 8] := (show Nat.ModEq 8 1 (7+2) by decide).mul_right _
      _ ≡ 7^17+131072 [MOD 8] := seventeen_compact_scaled fac p8
      _ ≡ 7 [MOD 8] := by decide
  have fv : F%8=7 := f8
  have fo : Odd F := Nat.odd_iff.mpr (by omega)
  have pred : Nat.ModEq (3*D) p 1 := by
    have z := seventeen_compact_last_cycle (b:=b) per
    rw [idx,pow_one,←base] at z
    exact Nat.ModEq.add_right_cancel' 1 z
  have fd : Nat.ModEq D F 43691 := Nat.ModEq.mul_left_cancel' (by decide : (3:ℕ)≠0) (seventeen_compact_scaled fac pred)
  have total : Nat.ModEq (8*D) F (4*D+43691) := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp ⟨f8.trans a8,fd.trans ad⟩
  rw [jacobiSym.mod_right _ fo]
  have abs : 4*(-(2*(D:ℤ))).natAbs=8*D := by simp; omega
  rw [abs]
  have rem : F%(8*D)=4*D+43691 := Eq.trans total (Nat.mod_eq_of_lt (by omega))
  rwa [rem]


private theorem seventeen_compact_last_abstract {p b F : ℕ} {A : ℤ}
    (pp : p.Prime) (base : p+1=2^b) (hb : 131073 < b) (idx : b%42840=1)
    (fac : p^17+131072=(p+2)*F) (minus : jacobiSym A F = -1)
    (catalog : ∀ {i : ℕ}, i<3856 → (34*i+1).Prime → 34*i+1∣p^17+131072 → ¬34*i+1∣p+2 →
      jacobiSym A (34*i+1)=1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q∣p^17+d ∧ s∣p^17+d := by
  have ep : p=2^b-1 := by omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) (ep ▸ pp)).2
  have eight : 8∣2^b := pow_dvd_pow 2 (show 3 ≤ b by omega)
  have p8 : Nat.ModEq 8 p 7 := by change p%8=7; omega
  have z := seventeen_compact_scaled fac p8
  change (9*F)%8=7 at z
  have fo : Odd F := Nat.odd_iff.mpr (by omega)
  have fpos : F≠0 := by omega
  obtain ⟨s,ps,ds,minusS⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one minus
  have slo : 2 < s := lt_of_le_of_ne ps.two_le (Ne.symm (fo.ne_two_of_dvd_nat ds))
  obtain ⟨q,pq,qhi,qleft⟩ := seventeen_compact_last_left pb hb (show 3 < b by omega)
  have dx : q∣p+2 := by convert qleft using 1; omega
  have mult : s∣p^17+131072 := fac ▸ dvd_mul_of_dvd_right ds _
  have nd : ¬s∣p+2 := by
    intro h
    have es := seventeen_compact_common_prime fac fpos ps slo h ds
    have dL : s∣2^b+1 := by convert h using 1; omega
    have eq3 := seventeen_compact_last_fifth pb (pb.odd_of_ne_two (by omega)) ps dL (by omega)
    omega
  by_cases large : 131073 < s
  · have ne : q≠s := by rintro rfl; have := seventeen_compact_common_prime fac fpos pq (by omega) dx ds; omega
    exact ⟨131072,q,s,pq,ps,ne,qhi,large,fac ▸ dvd_mul_of_dvd_left dx _,mult⟩
  exfalso
  obtain ⟨j,hj⟩ := seventeen_compact_last_order ps (by omega) mult nd
  obtain ⟨u,hu⟩ := ps.odd_of_ne_two (by omega)
  let i := (s-1)/34
  have es : 34*i+1=s := by dsimp [i]; omega
  have bd : i<3856 := by dsimp [i]; omega
  have posS : jacobiSym A s=1 := by
    rw [←es]
    exact catalog bd (es ▸ ps) (es ▸ mult) (es ▸ nd)
  omega

set_option maxRecDepth 32768 in
private theorem seventeen_compact_discriminant_period : Nat.ModEq (3*165761510898758474122959146951472738034111787534784063452920343662446339649360757757209768659286348971536712574911472599055) (2^42840) 1 := by
  change 2^42840%(3*165761510898758474122959146951472738034111787534784063452920343662446339649360757757209768659286348971536712574911472599055)=1%(3*165761510898758474122959146951472738034111787534784063452920343662446339649360757757209768659286348971536712574911472599055)
  rw [←seventeen_compact_pow_eq]
  decide +kernel

set_option maxRecDepth 32768 in
private theorem seventeen_compact_discriminant_value : jacobiSym (-(2*(165761510898758474122959146951472738034111787534784063452920343662446339649360757757209768659286348971536712574911472599055:ℤ))) (4*165761510898758474122959146951472738034111787534784063452920343662446339649360757757209768659286348971536712574911472599055+43691) = -1 := by norm_num1


set_option maxRecDepth 32768 in
/-- The projected seventeenth roots exclude the final Mersenne-index congruence class. -/
theorem seventeen_last_compact_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b)
    (hb : 131073 < b) (idx : b%42840=1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧
      q∣p^17+d ∧ s∣p^17+d := by
  obtain ⟨F,fac⟩ : p+2∣p^17+131072 := (by decide : Odd 17).nat_add_dvd_pow_add_pow p 2
  have bad := seventeen_compact_cofactor_negative base hb idx fac seventeen_compact_discriminant_period
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) seventeen_compact_discriminant_value
  apply seventeen_compact_last_abstract pp base hb idx fac bad
  intro i lim ps mult nd
  exact seventeen_compact_catalog lim ps base idx mult nd


/-- Every seventeenth power with Mersenne index greater than 131073 has a two-prime witness. -/
theorem mersenne_seventeen_large_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b)
    (hb : 131073 < b)
    (coarseRule : (¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d) →
      b%2520 ∈ ([1,361,673,841,1201,1321,1513,1681,1793,1873,2161] : List ℕ)) : ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧
    q ∣ p^17+d ∧ s ∣ p^17+d := by
  by_contra missing
  have rems := coarseRule missing
  have reduced0 : b%2520=1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at rems
    rcases rems with h|h|h|h|h|h|h|h|h|h|h
    · exact h
    · exact (missing (case17_2520_361 pp.pos base h)).elim
    · exact (missing (case17_2520_673 pp.pos base h)).elim
    · exact (missing (case17_2520_841 pp.pos base h)).elim
    · exact (missing (case17_2520_1201 pp.pos base h)).elim
    · exact (missing (case17_2520_1321 pp.pos base h)).elim
    · exact (missing (case17_2520_1513 pp.pos base h)).elim
    · exact (missing (case17_2520_1681 pp.pos base h)).elim
    · exact (missing (case17_2520_1793 pp.pos base h)).elim
    · exact (missing (case17_2520_1873 pp.pos base h)).elim
    · exact (missing (case17_2520_2161 pp.pos base h)).elim
  have ep : p=2^b-1 := by omega
  have pb : b.Prime := (Nat.prime_of_pow_sub_one_prime (by omega) (ep ▸ pp)).2
  have form : b%42840=1+2520*((b/2520)%17) := by omega
  have indiv : b%17≠0 := by
    intro z
    have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 17) pb).mp (Nat.dvd_of_mod_eq_zero z)
    omega
  have rems2 : b%42840 ∈ [1,2521,5041,7561,12601,15121,17641,20161,22681,25201,27721,30241,32761,35281,37801,40321] := by
    have tab : ∀ t ∈ List.range 17, (1+2520*t)%17≠0 → 1+2520*t ∈ [1,2521,5041,7561,12601,15121,17641,20161,22681,25201,27721,30241,32761,35281,37801,40321] := by decide +kernel
    have z : b%42840%17≠0 := by rwa [Nat.mod_mod_of_dvd _ (by decide : 17∣42840)]
    rw [form] at z ⊢
    exact tab _ (List.mem_range.mpr (Nat.mod_lt _ (by decide))) z
  have reduced1 : b%42840=1 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at rems2
    rcases rems2 with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · exact h
    · exact (missing (case17_42840_2521 pp.pos base h)).elim
    · exact (missing (case17_42840_5041 pp.pos base h)).elim
    · exact (missing (case17_42840_7561 pp.pos base h)).elim
    · exact (missing (case17_42840_12601 pp.pos base h)).elim
    · exact (missing (case17_42840_15121 pp.pos base h)).elim
    · exact (missing (case17_42840_17641 pp.pos base h)).elim
    · exact (missing (case17_42840_20161 pp.pos base h)).elim
    · exact (missing (case17_42840_22681 pp.pos base h)).elim
    · exact (missing (case17_42840_25201 pp.pos base h)).elim
    · exact (missing (case17_42840_27721 pp.pos base h)).elim
    · exact (missing (case17_42840_30241 pp.pos base h)).elim
    · exact (missing (case17_42840_32761 pp.pos base h)).elim
    · exact (missing (case17_42840_35281 pp.pos base h)).elim
    · exact (missing (case17_42840_37801 pp.pos base h)).elim
    · exact (missing (case17_42840_40321 pp.pos base h)).elim
  exact missing (seventeen_last_compact_witness pp base hb reduced1)

theorem mersenne_seventeenth_witness {p b : ℕ} (pp : p.Prime) (base : p+1=2^b) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q ∣ p^17+d ∧ s ∣ p^17+d := by
  have ep : p=2^b-1 := by omega
  have b1 : b≠1 := by rintro rfl; norm_num at base; have := pp.two_le; omega
  have pb := (Nat.prime_of_pow_sub_one_prime b1 (ep ▸ pp)).2
  by_cases small : b≤131073
  · exact ep ▸ seventeen_bounded_witness pb small
  · have hi : 131073 < b := by omega
    exact mersenne_seventeen_large_witness pp base hi (seventeen_coarse pb pp base hi)

/-- No solution immediately precedes a nontrivial seventeenth power. -/
theorem seventeenth_power_exclusion {n x : ℕ} (hx : 1 < x)
    (eq : n+1=x^17) : v_l 1 n ≠ 1 := by
  intro sol
  have bound : 32 ≤ x^17 := by
    have a := Nat.pow_le_pow_left (show 2 ≤ x by omega) 17
    norm_num at a
    omega
  have ox : Odd x := by
    apply Nat.not_even_iff_odd.mp
    intro ex
    have dd : 2 ∣ x^17 := (even_iff_two_dvd.mp ex).trans (dvd_pow_self x (by omega))
    have on : Odd n := by rw [Nat.odd_iff]; omega
    rcases (odd_classification on).mp sol with h|h|h|h <;> omega
  obtain ⟨b,base⟩ := odd_power_root_neighbor ox hx (by decide : Odd 17) (by decide) eq sol
  have pure := prime_power_succ (n:=n) (by omega) sol
  rw [eq,isPrimePow_pow_iff (by omega : (17:ℕ)≠0)] at pure
  obtain ⟨p,e,pp,pe,he⟩ := (isPrimePow_nat_iff _).mp pure
  have op := pp.odd_of_ne_two (by
    rintro rfl
    have div := dvd_pow_self (2:ℕ) pe.ne'
    rw [he] at div
    exact (Nat.not_even_iff_odd.mpr ox) (even_iff_two_dvd.mpr div))
  have one := mersenne_power_exponent op pp.one_lt pe (he.symm ▸ base)
  rw [one,pow_one] at he
  subst x
  obtain ⟨d,q,s,pq,ps,ne,hq,hs,dq,ds⟩ := mersenne_seventeenth_witness pp base
  have rearr : n+(d+1)=p^17+d := by omega
  exact two_primes (k:=d+1) (by omega) pq ps ne hq hs (rearr ▸ dq) (rearr ▸ ds) sol


/-- The remaining prime exponents congruent to 1 modulo three, beyond any chosen cutoff. -/
def H1 : Prop := ∃ P R B : ℕ, ∀ p r : ℕ, p.Prime → Odd p → 31 < p → P < p →
    r.Prime → 23 ≤ r → R < r → r%3=1 → 2*(r-1) ≤ 3*p →
    (∃ b : ℕ, p+1=2^b ∧ (2^(b-1) ∣ r-1 → ∃ t : ℕ, r-1=2^t)) →
    B < p^r → ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q∣p^r+d ∧ s∣p^r+d

/-- The remaining prime exponents congruent to 2 modulo three, beyond any chosen cutoff. -/
def H2 : Prop := ∃ P R B : ℕ, ∀ p r : ℕ, p.Prime → Odd p → 31 < p → P < p →
    r.Prime → 23 ≤ r → R < r → r%3=2 → 2*(r-2) ≤ 3*p^2 →
    (∃ b : ℕ, p+1=2^b ∧ (2^(b-1) ∣ r-1 → ∃ t : ℕ, r-1=2^t)) →
    B < p^r → ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1 < q ∧ d+1 < s ∧ q∣p^r+d ∧ s∣p^r+d

theorem main : H1 → H2 → OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.H3 := by
  rintro ⟨P,R,A,left⟩ ⟨Q,S,B,right⟩
  let X := max (max P Q) 31
  let Y := max (max R S) 23
  obtain ⟨C,hC⟩ := Erdos889.UniformPowers.finite_prime_threshold X
  obtain ⟨D,hD⟩ := Erdos889.UniformPowers.bounded_power_exclusion Y
  refine ⟨max (max A B) (max C D)+1,?_⟩
  rintro p r pp op hp pr low ⟨b,base,align,_⟩ _ large
  by_contra missing
  have hAB := Nat.le_max_left (max A B) (max C D)
  have hCD := Nat.le_max_right (max A B) (max C D)
  have hA := Nat.le_max_left A B
  have hB := Nat.le_max_right A B
  have h1 := Nat.le_max_left C D
  have h2 := Nat.le_max_right C D
  have eq : p^r-1+1=p^r := by omega
  have sol := Erdos889.Missing.predecessor_solution_of_missing (by omega : 1 < p^r) missing
  have bigp : X < p := by
    by_contra! small
    have dp := hC (p^r-1) (by omega) sol p small pp
    have dr := dvd_pow_self p (by omega : r≠0)
    have dn : p∣(p^r-1)+1 := eq.symm ▸ dr
    have d1 := (Nat.dvd_add_iff_right dp).mpr dn
    exact pp.not_dvd_one d1
  have bigr : Y < r := by
    by_contra! small
    exact hD (p^r-1) p r (by omega) pp.one_lt (by omega) small eq sol
  have x1 := Nat.le_max_left P Q
  have x2 := Nat.le_max_right P Q
  have x3 := Nat.le_max_left (max P Q) 31
  have x4 := Nat.le_max_right (max P Q) 31
  have y1 := Nat.le_max_left R S
  have y2 := Nat.le_max_right R S
  have y3 := Nat.le_max_left (max R S) 23
  have y4 := Nat.le_max_right (max R S) 23
  dsimp only [X] at bigp
  dsimp only [Y] at bigr
  by_cases hm : r%3=1
  · exact missing (left p r pp op (by omega) (by omega) pr (by omega) (by omega) hm
      (Erdos889.PrimitivePowers.power_missing_exponent_linear (by omega) op hm missing)
      ⟨b,base,align⟩ (by omega))
  · have nz : r%3≠0 := by
      intro z
      have h := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pr).mp (Nat.dvd_of_mod_eq_zero z)
      omega
    exact missing (right p r pp op (by omega) (by omega) pr (by omega) (by omega) (by omega)
      (Erdos889.PrimitivePowers.power_missing_exponent_bound (by omega) op pr (by omega) missing)
      ⟨b,base,align⟩ (by omega))

end OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H3_R1
