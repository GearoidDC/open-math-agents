import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
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


namespace OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H1_R1

open Finset
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem minus_root_binary {x d : ℕ} (ox : Odd x) (hx : 1 < x) (od : Odd d) (hd : 1 < d)
    (unique : ∀ q s : ℕ, q.Prime → s.Prime → 2<q → 2<s →
      q ∣ x^d-1 → s ∣ x^d-1 → q=s) : ∃ a : ℕ, x-1=2^a := by
  let S := ∑ i ∈ range d, x^i
  have os : Odd S := by
    dsimp [S]
    rw [Finset.odd_sum_iff_odd_card_odd]
    simpa [ox.pow] using od
  have big : d<S := by
    have h : (∑ _i ∈ range d, (1:ℕ)) < ∑ i ∈ range d, x^i := by
      apply Finset.sum_lt_sum
      · intro i _
        exact Nat.one_le_pow _ _ (by omega)
      · exact ⟨1,mem_range.mpr hd,by simpa using hx⟩
    simpa [S] using h
  have fac : S*(x-1)=x^d-1 := geom_sum_mul_of_one_le hx.le d
  refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
  intro q pq dq
  by_contra q2
  have lq : 2<q := by have := pq.two_le; omega
  have pure : S=q^S.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
    intro z pz dz
    have z2 : 2<z := by
      have := pz.two_le
      by_contra! low
      have ez : z=2 := by omega
      rw [ez] at dz
      obtain ⟨k,hk⟩ := os
      omega
    exact unique z q pz pq z2 lq (fac ▸ dvd_mul_of_dvd_left dz _)
      (fac ▸ dvd_mul_of_dvd_right dq _))
  let _ : Fact q.Prime := ⟨pq⟩
  have nd : ¬ q ∣ x := by
    intro div
    have h := Nat.dvd_sub div dq
    rw [show x-(x-1)=1 by omega] at h
    have := Nat.le_of_dvd Nat.one_pos h
    omega
  have val := padicValNat.pow_sub_pow (x:=x) (y:=1) (pq.odd_of_ne_two q2) hx dq nd (by omega : d≠0)
  rw [one_pow,←fac,padicValNat.mul (by omega) (by omega)] at val
  have eq : padicValNat q S=padicValNat q d := by omega
  have power : q^(padicValNat q S)=S := by
    conv_lhs => arg 2; rw [pure,padicValNat.prime_pow]
    exact pure.symm
  have div : S ∣ d := by rw [←power,eq]; exact pow_padicValNat_dvd
  exact (Nat.not_le_of_gt big) (Nat.le_of_dvd (by omega) div)

private theorem missing_left {p : ℕ} (missing : ¬∃ d q s : ℕ,
    q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) :
    ∀ q s : ℕ, q.Prime → s.Prime → 2<q → 2<s → q ∣ p+1 → s ∣ p+1 → q=s := by
  intro q s pq ps hq hs dq ds
  by_contra ne
  exact missing ⟨1,q,s,pq,ps,ne,hq,hs,dq,ds⟩

/-- Between p+1 and p+3, the only possible nontrivial odd-power root is three. -/
theorem odd_middle_root {p x d : ℕ} (pp : p.Prime) (hp : 3<p) (ox : Odd x) (hx : 1<x)
    (od : Odd d) (hd : 1<d) (eq : p+2=x^d)
    (missing : ¬∃ k q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ k+1<q ∧ k+1<s ∧
      q ∣ p+k ∧ s ∣ p+k) : x=3 := by
  have elig (q : ℕ) (pq : q.Prime) (hq : 2<q) (dq : q ∣ p+3) : 4<q := by
    by_contra! small
    have e : q=3 := by interval_cases q <;> norm_num at *
    rw [e] at dq
    have d3 : 3 ∣ p := by omega
    have bad := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp d3
    omega
  obtain ⟨a,minus⟩ := minus_root_binary ox hx od hd (by
    rw [←eq,show p+2-1=p+1 by omega]
    exact missing_left missing)
  obtain ⟨b,plus⟩ := odd_root_with_unique_odd_prime ox hx od hd (by
    intro q s pq ps hq hs dq ds
    rw [←eq,show p+2+1=p+3 by omega] at dq ds
    by_contra ne
    exact missing ⟨3,q,s,pq,ps,ne,elig q pq hq dq,elig s ps hs ds,dq,ds⟩)
  obtain ⟨u,hu⟩ := ox
  by_contra bad
  have a2 : 2≤a := by by_contra! low; interval_cases a <;> norm_num at minus <;> omega
  have b2 : 2≤b := by by_contra! low; interval_cases b <;> norm_num at plus <;> omega
  have m4 : 4 ∣ x-1 := minus ▸ pow_dvd_pow (2:ℕ) a2
  have p4 : 4 ∣ x+1 := plus ▸ pow_dvd_pow (2:ℕ) b2
  omega

private theorem shifted_square_binary {p x : ℕ} (hx : 3<x) (eq : p+2=x^2)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : (∃ a : ℕ, x-1=2^a) ∨ (∃ a : ℕ, x+1=2^a) := by
  have fac : p+1=(x-1)*(x+1) := by
    have h : x-1+1=x := by omega
    nlinarith
  have oddprime (y : ℕ) (hy : 1<y) (nopow : ¬∃ a : ℕ, y=2^a) :
      ∃ q : ℕ, q.Prime ∧ 2<q ∧ q ∣ y := by
    by_contra! none
    exact nopow ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
      intro q pq dq
      have := pq.two_le
      by_contra ne
      exact none q pq (by omega) dq)⟩
  by_contra! neither
  obtain ⟨q,pq,hq,dq⟩ := oddprime (x-1) (by omega) (by simpa using neither.1)
  obtain ⟨s,ps,hs,ds⟩ := oddprime (x+1) (by omega) (by simpa using neither.2)
  have ne : q≠s := by
    rintro rfl
    have diff := Nat.dvd_sub ds dq
    rw [show x+1-(x-1)=2 by omega] at diff
    have := Nat.le_of_dvd (by decide) diff
    omega
  exact missing ⟨1,q,s,pq,ps,ne,hq,hs,fac ▸ dvd_mul_of_dvd_left dq _,fac ▸ dvd_mul_of_dvd_right ds _⟩

private theorem odd_factor_pure {p m : ℕ} (hm : 2 ≤ m) (om : ¬2 ∣ m) (dm : m ∣ p+1)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : IsPrimePow m := by
  by_contra bad
  obtain ⟨q,hq,s,hs,ne⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hm).mp bad
  obtain ⟨pq,dq,_⟩ := Nat.mem_primeFactors.mp hq
  obtain ⟨ps,ds,_⟩ := Nat.mem_primeFactors.mp hs
  apply ne (missing_left missing q s pq ps _ _ (dq.trans dm) (ds.trans dm))
  · have := pq.two_le
    by_contra! low
    have id : q=2 := by omega
    exact om (id ▸ dq)
  · have := ps.two_le
    by_contra! low
    have id : s=2 := by omega
    exact om (id ▸ ds)

private theorem dyadic_minus_bound {p j : ℕ} (hj : 2≤j) (div : 2^(j+j)-1 ∣ p+1)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : False := by
  let y := 2^j
  have big : 4≤y := Nat.pow_le_pow_right (by decide : 0<2) hj
  have even : 2 ∣ y := dvd_pow_self _ (by omega)
  have fac : 2^(j+j)-1=(y-1)*(y+1) := by
    rw [pow_add]
    change y*y-1=(y-1)*(y+1)
    have h : y-1+1=y := by omega
    have pos : 1 ≤ y*y := Nat.mul_pos (by omega) (by omega)
    have h2 : y*y-1+1=y*y := by omega
    nlinarith
  let q := (y-1).minFac
  let s := (y+1).minFac
  have pq : q.Prime := Nat.minFac_prime (by omega)
  have ps : s.Prime := Nat.minFac_prime (by omega)
  have dq : q ∣ y-1 := Nat.minFac_dvd _
  have ds : s ∣ y+1 := Nat.minFac_dvd _
  have hq : 2<q := by
    have := pq.two_le
    by_contra! low
    have e : q=2 := by omega
    rw [e] at dq
    omega
  have hs : 2<s := by
    have := ps.two_le
    by_contra! low
    have e : s=2 := by omega
    rw [e] at ds
    omega
  have ne : q≠s := by
    intro same
    rw [←same] at ds
    have df := Nat.dvd_sub ds dq
    rw [show y+1-(y-1)=2 by omega] at df
    have := Nat.le_of_dvd (by decide) df
    omega
  rw [fac] at div
  exact missing ⟨1,q,s,pq,ps,ne,hq,hs,(dvd_mul_of_dvd_left dq _).trans div,
    (dvd_mul_of_dvd_right ds _).trans div⟩

private theorem prime_above_three {m : ℕ} (hm : 1 < m) (om : ¬2 ∣ m)
    (ex : ∀ e : ℕ, m≠3^e) : ∃ q : ℕ, q.Prime ∧ 3<q ∧ q ∣ m := by
  by_contra! none
  exact ex _ (Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
    intro q pq dq
    have low : q ≤ 3 := by by_contra! high; exact none q pq high dq
    have := pq.two_le
    by_contra ne
    have e : q=2 := by omega
    exact om (e ▸ dq)))

private theorem power_plus_one_not_three {j e : ℕ} (hj : 4≤j) : 2^j+1≠3^e := by
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

private theorem square_mersenne_bound {p x b : ℕ} (hb : x+1=2^b) (eq : p+2=x^2)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : x≤63 := by
  by_contra! high
  have b7 : 7≤b := by
    by_contra! low
    have := Nat.pow_le_pow_right (by decide : 0<2) (show b≤6 by omega)
    omega
  let j := b/2
  let y := 2^j
  have j3 : 3≤j := by dsimp [j]; omega
  have big : 8≤y := Nat.pow_le_pow_right (by decide : 0<2) j3
  have even : 8 ∣ y := pow_dvd_pow (2:ℕ) j3
  have fac : y*y=(y-1)*(y+1)+1 := by
    have h : y-1+1=y := by omega
    nlinarith
  by_cases bj : b=2*j
  · have j4 : 4≤j := by omega
    have mid : x=(y-1)*(y+1) := by
      rw [bj,Nat.mul_comm 2 j,pow_mul,pow_two] at hb
      change x+1=y*y at hb
      omega
    obtain ⟨q,pq,hq,dq⟩ := prime_above_three (m:=y-1) (by omega) (by omega) (by
      intro e h
      have := three_pow_mod_eight e
      omega)
    obtain ⟨s,ps,hs,ds⟩ := prime_above_three (m:=y+1) (by omega) (by omega)
      (fun _ => power_plus_one_not_three j4)
    have ne : q≠s := by
      rintro rfl
      have df := Nat.dvd_sub ds dq
      rw [show y+1-(y-1)=2 by omega] at df
      have := Nat.le_of_dvd (by decide) df
      omega
    have xd : x ∣ p+2 := eq ▸ dvd_pow_self x (by decide : 2≠0)
    exact missing ⟨2,q,s,pq,ps,ne,hq,hs,(mid ▸ dvd_mul_of_dvd_left dq _).trans xd,
      (mid ▸ dvd_mul_of_dvd_right ds _).trans xd⟩
  · have bform : b=(j+j)+1 := by dsimp [j] at *; omega
    have xx : x-1=2*(2^(j+j)-1) := by
      rw [bform,pow_succ] at hb
      have := @Nat.one_le_two_pow (j+j)
      omega
    have dm : x-1 ∣ p+1 := by
      have h : x-1+1=x := by omega
      have f : p+1=(x-1)*(x+1) := by nlinarith
      rw [f]; exact dvd_mul_right _ _
    apply dyadic_minus_bound (by omega : 2≤j) _ missing
    rw [xx] at dm
    exact (dvd_mul_left _ 2).trans dm

private theorem middle_fifth_witness {p t : ℕ} (ht : 2≤t)
    (eq : p+2=(2*(2^(2^t))+1)^2)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : False := by
  have orbit (i : ℕ) : 2^(2^(i+2))%91=16 ∨ 2^(2^(i+2))%91=74 := by
    induction i with
    | zero => decide
    | succ i ih =>
      have step : 2^(2^(i+1+2))=(2^(2^(i+2)))^2 := by
        rw [show i+1+2=i+2+1 by omega,pow_succ (2:ℕ) (i+2),pow_mul]
      rw [step,Nat.pow_mod]
      rcases ih with h|h <;> rw [h] <;> decide
  let z := 2^(2^t)
  have res : z%91=16 ∨ z%91=74 := by
    have := orbit (t-2)
    simpa [z,Nat.sub_add_cancel ht] using this
  have div : 91 ∣ (2*z+1)^2+3 := by
    have co := ((((Nat.mod_modEq z 91).mul_left 2).add_right 1).pow 2).add_right 3
    apply Nat.modEq_zero_iff_dvd.mp
    apply co.symm.trans
    rcases res with h|h <;> rw [h] <;> decide
  have expr : p+5=(2*z+1)^2+3 := by dsimp [z]; omega
  rw [←expr] at div
  exact missing ⟨5,7,13,by decide,by decide,by decide,by decide,by decide,
    (show 7∣91 by decide).trans div,(show 13∣91 by decide).trans div⟩

set_option maxHeartbeats 600000 in
/-- Beyond the last small example, a multiple of three two above the successor
cannot be a square. -/
theorem middle_not_square {p x : ℕ} (pp : p.Prime) (hp : 223<p) (pm : p%3=1)
    (eq : p+2=x^2) (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) : False := by
  have xbig : 3<x := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    norm_num at this
    omega
  have bound : x≤63 := by
    rcases shifted_square_binary xbig eq missing with ⟨a,ha⟩|⟨a,ha⟩
    · have ax : x=2^a+1 := by omega
      have ap : a≠0 := by rintro rfl; norm_num at ax; omega
      let c := a-1
      have ac : a=c+1 := by dsimp only [c]; omega
      by_cases cz : c=0
      · rw [ac,cz] at ax; norm_num at ax; omega
      have plus : x+1=2*(2^c+1) := by rw [ax,ac,pow_succ]; ring
      have odd : ¬2 ∣ 2^c+1 := by have := dvd_pow_self (2:ℕ) cz; omega
      have fac : p+1=(x-1)*(x+1) := by
        have h : x-1+1=x := by omega
        nlinarith
      have div : 2^c+1 ∣ p+1 := by
        rw [fac,plus]
        exact (dvd_mul_left (2^c+1) 2).trans (dvd_mul_left _ _)
      have pure := odd_factor_pure (by have := @Nat.one_le_two_pow c; omega) odd div missing
      rcases prime_power_neighbor cz pure with c3|⟨t,ht⟩
      · rw [ac,c3] at ax; norm_num at ax; omega
      · by_cases small : t<2
        · interval_cases t <;> norm_num at ht <;> rw [ac,ht] at ax <;> norm_num at ax <;> omega
        · apply False.elim (middle_fifth_witness (by omega : 2≤t) _ missing)
          rw [eq,ax,ac,ht,pow_succ (2:ℕ) (2^t),Nat.mul_comm (2^(2^t)) 2]
    · exact square_mersenne_bound ha eq missing
  have oddm : Odd (p+2) := (pp.odd_of_ne_two (by omega)).add_even (by decide : Even 2)
  rw [eq,Nat.odd_pow_iff (by decide : 2≠0)] at oddm
  obtain ⟨u,hu⟩ := oddm
  have div3 : 3∣x := Nat.prime_three.dvd_of_dvd_pow (by rw [←eq]; omega)
  have xmin : 15<x := by
    by_contra! low
    have z := Nat.pow_le_pow_left low 2
    norm_num at z
    omega
  have alternatives : x=21 ∨ x=27 ∨ x=33 ∨ x=39 ∨ x=45 ∨ x=51 ∨ x=57 ∨ x=63 := by omega
  rcases alternatives with h|h|h|h|h|h|h|h <;> rw [h] at eq <;> norm_num at eq
  · have ep : p=439 := by omega
    rw [ep] at missing; exact missing ⟨1,5,11,by decide +kernel⟩
  · have ep : p=727 := by omega
    rw [ep] at missing; exact missing ⟨1,7,13,by decide +kernel⟩
  · have ep : p=1087 := by omega
    rw [ep] at missing; exact missing ⟨3,5,109,by decide +kernel⟩
  · have ep : p=1519 := by omega
    exact Nat.not_prime_of_dvd_of_lt (by norm_num : 7∣1519) (by decide) (by decide) (ep ▸ pp)
  · have ep : p=2023 := by omega
    exact Nat.not_prime_of_dvd_of_lt (by norm_num : 7∣2023) (by decide) (by decide) (ep ▸ pp)
  · have ep : p=2599 := by omega
    exact Nat.not_prime_of_dvd_of_lt (by norm_num : 23∣2599) (by decide) (by decide) (ep ▸ pp)
  · have ep : p=3247 := by omega
    exact Nat.not_prime_of_dvd_of_lt (by norm_num : 17∣3247) (by decide) (by decide) (ep ▸ pp)
  · have ep : p=3967 := by omega
    rw [ep] at missing; exact missing ⟨3,5,397,by decide +kernel⟩

/-- A power of three two above p produces a witness. The odd-prime exponent
case reduces to Fermat exponents, which give the primes seven and eleven. -/
theorem pure_three_exclusion {p r : ℕ} (pp : p.Prime) (hp : 223<p) (pr : r.Prime)
    (od : Odd r) (eq : p+2=3^r) (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) : False := by
  have ro := od
  obtain ⟨j,hj⟩ := ro
  have rr : r%4=1 := by
    by_contra b
    have e : r%4=3 := by omega
    have h := pow_cycle (a:=3) (d:=4) (m:=5) (by decide) r
    change 3^r%5=3^(r%4)%5 at h
    rw [e] at h
    norm_num at h
    have bad := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) pp).mp (by omega)
    omega
  let a := r-1
  have rp := pr.one_lt
  have ap : 0<a := by dsimp [a]; omega
  have ra : r=a+1 := by dsimp [a]; omega
  have a4 : a%4=0 := by omega
  have m5 := pow_cycle (a:=3) (d:=4) (m:=5) (by decide) a
  change 3^a%5=3^(a%4)%5 at m5
  rw [a4] at m5
  norm_num at m5
  have m3 := dvd_pow_self (3:ℕ) ap.ne'
  have eligible (q : ℕ) (pq : q.Prime) (lo : 2<q) (div : q ∣ 3^a+1) : 6<q := by
    by_contra! small
    have choice : q=3 ∨ q=5 := by interval_cases q <;> norm_num at *
    rcases choice with rfl|rfl <;> omega
  have dyadic : ∃ t : ℕ, a=2^t := by
    refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd ap.ne' ?_⟩
    intro l pl dl
    by_contra l2
    obtain ⟨s,hs⟩ := dl
    have sp : 0<s := by
      by_contra! bad
      have zz : s=0 := by omega
      simp [zz] at hs
      omega
    have form : (3^s)^l=3^a := by rw [←pow_mul,hs,Nat.mul_comm s l]
    have raised : p+5=3*(3^a+1) := by
      rw [ra,pow_succ] at eq
      omega
    obtain ⟨e,binary⟩ := odd_root_with_unique_odd_prime ((by decide : Odd 3).pow (n:=s))
      (Nat.one_lt_pow sp.ne' (by decide : 1<3)) (pl.odd_of_ne_two l2) pl.one_lt (by
        intro q z pq pz hq hz dq dz
        rw [form] at dq dz
        by_contra ne
        exact missing ⟨5,q,z,pq,pz,ne,eligible q pq hq dq,eligible z pz hz dz,
          raised ▸ dvd_mul_of_dvd_right dq 3,raised ▸ dvd_mul_of_dvd_right dz 3⟩)
    have one := mersenne_power_exponent (by decide : Odd 3) (by decide : 1<3) sp binary
    rw [one,mul_one] at hs
    obtain ⟨v,hv⟩ := pl.odd_of_ne_two l2
    omega
  obtain ⟨t,ht⟩ := dyadic
  have re : r=2^t+1 := by omega
  have tn : t≠0 := by rintro rfl; norm_num at re; omega
  have primepower : IsPrimePow (2^t+1) := re ▸ (isPrimePow_nat_iff _).mpr ⟨r,1,pr,by decide,by simp⟩
  rcases prime_power_neighbor tn primepower with three|⟨u,hu⟩
  · rw [three] at re
    norm_num at re
    rw [re] at pr
    norm_num at pr
  · by_cases small : u≤1
    · interval_cases u
      · norm_num at hu; rw [hu] at re; norm_num at re; omega
      · norm_num at hu; rw [hu] at re; norm_num at re
        rw [re] at eq
        have pe : p=241 := by norm_num at eq; omega
        rw [pe] at missing
        exact missing ⟨6,13,19,by decide +kernel⟩
    have t4 : 4 ∣ t := hu ▸ pow_dvd_pow (2:ℕ) (by omega : 2≤u)
    have t_mod : t%4=0 := by omega
    have t_even : t%2=0 := by omega
    have m := pow_cycle (a:=2) (d:=2) (m:=3) (by decide) t
    have n := pow_cycle (a:=2) (d:=4) (m:=5) (by decide) t
    change 2^t%3=2^(t%2)%3 at m
    change 2^t%5=2^(t%4)%5 at n
    rw [t_even] at m
    rw [t_mod] at n
    norm_num at m n
    have c6 : r%6=5 := by omega
    have c5 : r%5=2 := by omega
    have seven := pow_cycle (a:=3) (d:=6) (m:=7) (by decide) r
    have eleven := pow_cycle (a:=3) (d:=5) (m:=11) (by decide) r
    change 3^r%7=3^(r%6)%7 at seven
    change 3^r%11=3^(r%5)%11 at eleven
    rw [c6] at seven
    rw [c5] at eleven
    norm_num at seven eleven
    exact missing ⟨4,7,11,by decide,by decide,by decide,by decide,by decide,by omega,by omega⟩

private theorem three_exponent_prime {p c : ℕ} (pp : p.Prime) (hp : 223<p) (pm : p%3=1)
    (eq : p+2=3^c) (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) : c.Prime ∧ Odd c := by
  have large : 1<c := by
    by_contra! small
    interval_cases c <;> norm_num at eq <;> omega
  have oc : Odd c := by
    rcases Nat.even_or_odd c with ⟨k,hk⟩|od
    · exact (middle_not_square pp hp pm (x:=3^k) (by rw [eq,hk,pow_add,pow_two]) missing).elim
    · exact od
  refine ⟨?_,oc⟩
  by_contra notprime
  obtain ⟨d,pd,k,hk⟩ := Nat.exists_prime_and_dvd (by omega : c≠1)
  have kd : k≠1 := by
    rintro rfl
    simp only [mul_one] at hk
    exact notprime (hk ▸ pd)
  have k2 : 2≤k := by
    by_cases zero : k=0
    · simp [zero] at hk; omega
    · omega
  have oddd := pd.odd_of_ne_two (by
    rintro rfl
    obtain ⟨a,ha⟩ := oc
    omega)
  have xlarge : 9≤3^k := Nat.pow_le_pow_right (by decide : 0<3) k2
  have three := odd_middle_root pp (by omega) ((by decide : Odd 3).pow (n:=k)) (by omega)
    oddd pd.one_lt (by rw [eq,hk,Nat.mul_comm d k,pow_mul]) missing
  omega

private theorem mixed_coprime {p t a b : ℕ} (pp : p.Prime) (hp : 223<p) (pm : p%3=1)
    (pt : t.Prime) (ht : 3<t) (bp : 0<b) (eq : p+2=3^a*t^b)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) : a.Coprime b := by
  by_contra bad
  obtain ⟨d,pd,dc,de⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  obtain ⟨u,hu⟩ := dc
  obtain ⟨v,hv⟩ := de
  have vp : v≠0 := by rintro rfl; simp at hv; omega
  have lb := Nat.le_self_pow vp t
  have yb : 3 < 3^u*t^v := by
    have pos : 0<3^u := pow_pos (by decide) _
    have := Nat.mul_le_mul_right (t^v) pos
    omega
  have power : p+2=(3^u*t^v)^d := by
    rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm u d,Nat.mul_comm v d,←hu,←hv,eq]
  by_cases ev : d=2
  · rw [ev] at power
    exact middle_not_square pp hp pm power missing
  · have oy := ((by decide : Odd 3).pow (n:=u)).mul ((pt.odd_of_ne_two (by omega)).pow (n:=v))
    have three := odd_middle_root pp (by omega) oy (by omega) (pd.odd_of_ne_two ev)
      pd.one_lt power missing
    omega

private theorem middle_classification {p : ℕ} (pp : p.Prime) (hp : 223<p) (pm : p%3=1)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) :
    (∃ c : ℕ, c.Prime ∧ Odd c ∧ p+2=3^c) ∨
    (∃ t a b : ℕ, t.Prime ∧ 3<t ∧ 0<a ∧ 0<b ∧ a.Coprime b ∧ p+2=3^a*t^b) := by
  let n := p+2
  let a := n.factorization 3
  let m := n/3^a
  have nz : n≠0 := by dsimp [n]; omega
  have fac : 3^a*m=n := Nat.ordProj_mul_ordCompl_eq_self n 3
  have dm : m ∣ n := Nat.ordCompl_dvd n 3
  have pos : 0 < m := Nat.ordCompl_pos 3 nz
  have no3 : ¬3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three nz
  have op := pp.odd_of_ne_two (by omega)
  have no2 : ¬2 ∣ m := by
    intro h
    have bad := h.trans dm
    change 2 ∣ p+2 at bad
    obtain ⟨i,hi⟩ := op
    omega
  have ap : 0<a := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three nz).mp
    (by change 3 ∣ p+2; omega)
  by_cases one : m=1
  · have eq : p+2=3^a := by simpa only [one,mul_one,n] using fac.symm
    have h := three_exponent_prime pp hp pm eq missing
    exact Or.inl ⟨a,h.1,h.2,eq⟩
  have eligible (q : ℕ) (pq : q.Prime) (dq : q ∣ m) : 3<q := by
    have := pq.two_le
    by_contra! small
    rcases (show q=2 ∨ q=3 by omega) with rfl|rfl
    · exact no2 dq
    · exact no3 dq
  have pure : IsPrimePow m := by
    by_contra bad
    obtain ⟨q,hq,s,hs,ne⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le
      (by omega : 2 ≤ m)).mp bad
    obtain ⟨pq,dq,_⟩ := Nat.mem_primeFactors.mp hq
    obtain ⟨ps,ds,_⟩ := Nat.mem_primeFactors.mp hs
    exact missing ⟨2,q,s,pq,ps,ne,eligible q pq dq,eligible s ps ds,dq.trans dm,ds.trans dm⟩
  obtain ⟨t,b,pt,bp,rep⟩ := (isPrimePow_nat_iff _).mp pure
  have dt : t ∣ m := rep ▸ dvd_pow_self _ bp.ne'
  have ht := eligible t pt dt
  have eq : p+2=3^a*t^b := by rw [rep]; exact fac.symm
  exact Or.inr ⟨t,a,b,pt,ht,ap,bp,mixed_coprime pp hp pm pt ht bp eq missing,eq⟩

private theorem missing_prime_solution {p : ℕ} (pp : p.Prime)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q∣p+d ∧ s∣p+d) : Erdos889.v_l 1 (p-1)=1 := by
  have low := pp.two_le
  apply le_antisymm
  · apply iSup_le; intro k; apply iSup_le; intro hk
    have upper : Erdos889.v (p-1) k≤1 := by
      by_contra! high
      rw [v_as_card,Finset.one_lt_card_iff_nontrivial] at high
      obtain ⟨q,hq,s,hs,ne⟩ := high
      obtain ⟨qm,qb⟩ := Finset.mem_filter.mp hq
      obtain ⟨sm,sb⟩ := Finset.mem_filter.mp hs
      obtain ⟨pq,dq,_⟩ := Nat.mem_primeFactors.mp qm
      obtain ⟨ps,ds,_⟩ := Nat.mem_primeFactors.mp sm
      have shift : p-1+k=p+(k-1) := by omega
      exact missing ⟨k-1,q,s,pq,ps,ne,by omega,by omega,shift ▸ dq,shift ▸ ds⟩
    exact_mod_cast upper
  · have lo : 1≤Erdos889.v (p-1) 1 := by
      rw [v_as_card,Finset.one_le_card,show p-1+1=p by omega]
      exact ⟨p,Finset.mem_filter.mpr ⟨pp.mem_primeFactors (dvd_refl p) pp.ne_zero,pp.one_lt⟩⟩
    exact (by exact_mod_cast lo : (1:ℕ∞)≤(Erdos889.v (p-1) 1:ℕ∞)).trans (offset_le (by decide))

private theorem bounded_shift_no_fourths
    (quadratic : ∀ T : ℕ, ∃ B : ℕ, ∀ x : ℕ, B<x → ∃ q : ℕ, q.Prime ∧ T<q ∧ q∣x^2+1) :
    ∃ B : ℕ, ∀ p d x y a b : ℕ, B<p → d≤3 → x≤3 → p+d=x^a*y^b →
      (¬∃ k q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ k+1<q ∧ k+1<s ∧ q∣p+k ∧ s∣p+k) →
      ¬4∣b := by
  obtain ⟨A,hA⟩ := quadratic 112
  refine ⟨27*(A+2)^4,?_⟩
  rintro p d x y a b big hd hx eq missing ⟨j,hj⟩
  let C := x^(a%4)
  let z := x^(a/4)*y^j
  have cap : C≤27 := (Nat.pow_le_pow_left hx (a%4)).trans
    (Nat.pow_le_pow_right (by decide : 0<3) (by omega : a%4≤3))
  have split : a=a%4+(a/4)*4 := by rw [Nat.mul_comm (a/4) 4,Nat.mod_add_div]
  have form : p+d=C*z^4 := by
    calc
      _ = x^(a%4+(a/4)*4)*y^(j*4) := by rw [←split,Nat.mul_comm j 4,←hj,eq]
      _ = _ := by dsimp only [C,z]; rw [pow_add,pow_mul,pow_mul,mul_pow]; ring
  have zbig : A+2<z := by
    by_contra! small
    have := Nat.mul_le_mul cap (Nat.pow_le_pow_left small 4)
    omega
  let u := z-1
  have zu : z=u+1 := by dsimp only [u]; omega
  obtain ⟨q,pq,hq,dq⟩ := hA u (by omega)
  obtain ⟨s,ps,hs,ds⟩ := hA (u+2) (by omega)
  let L := u^2+1
  let R := (u+2)^2+1
  change q∣L at dq
  change s∣R at ds
  have fac : p+(d+4*C)=C*(L*R) := by
    rw [zu] at form
    calc
      _ = (p+d)+4*C := by omega
      _ = _ := by rw [form]; dsimp only [L,R]; ring
  have ne : q≠s := by
    rintro rfl
    have diff : R=L+4*z := by rw [zu]; dsimp only [R,L]; ring
    rw [diff] at ds
    have d4 := (Nat.dvd_add_iff_right dq).mpr ds
    have dz : q∣z := (pq.dvd_mul.mp d4).resolve_left (by
      intro dv; have := Nat.le_of_dvd (by decide : 0<4) dv; omega)
    have sum := dvd_add dq (dvd_mul_of_dvd_right dz 2)
    rw [show L+2*z=z^2+2 by rw [zu]; dsimp only [L]; ring] at sum
    have sq : q∣z^2 := dz.trans (dvd_pow_self z (by decide : 2≠0))
    have bad := (Nat.dvd_add_iff_right sq).mpr sum
    have := Nat.le_of_dvd (by decide : 0<2) bad
    omega
  exact missing ⟨d+4*C,q,s,pq,ps,ne,by omega,by omega,
    fac ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dq _) _,
    fac ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right ds _) _⟩

private theorem cubic_alignment {x a y b j n : ℕ} (base : x=2 ∨ x=3) (index : j=1 ∨ j=2)
    (dn : 7∣n) (eq : n+x^j=x^a*y^b) (div : 3∣b) : a%3=j%3 := by
  obtain ⟨k,hk⟩ := div
  have cyc : Nat.ModEq 7 (x^6) 1 := by rcases base with rfl|rfl <;> decide
  have co := (pow_cycle cyc a).mul ((Nat.mod_modEq (y^k) 7).symm.pow 3)
  rw [hk,Nat.mul_comm 3 k,pow_mul] at eq
  change (x^a*(y^k)^3)%7=(x^(a%6)*((y^k)%7)^3)%7 at co
  rw [←eq] at co
  have ne : (n+x^j)%7=(x^j)%7 := by rw [Nat.add_mod,Nat.mod_eq_zero_of_dvd dn,zero_add,Nat.mod_mod]
  have table : ∀ w ∈ [2,3], ∀ l ∈ [1,2], ∀ i : Fin 6, ∀ z : Fin 7,
      (w^i.val*z.val^3)%7=w^l%7 → i.val%3=l%3 := by decide +kernel
  have h := table x (by simpa using base) j (by simpa using index)
    ⟨a%6,by omega⟩ ⟨(y^k)%7,by omega⟩ (co.symm.trans ne)
  simpa only [Nat.mod_mod_of_dvd a (by decide : 3∣6)] using h

private theorem large_factor_of_short_valuations {m : ℕ} (hm : 12 < m) (h8 : ¬8∣m)
    (h9 : ¬9∣m) : ∃ q : ℕ, q.Prime ∧ 3<q ∧ q∣m := by
  by_contra! bad
  let a := m.factorization 2
  let u := m/2^a
  have form : 2^a*u=m := Nat.ordProj_mul_ordCompl_eq_self m 2
  have du : u∣m := Nat.ordCompl_dvd m 2
  have hu : 0<u := Nat.ordCompl_pos 2 (by omega)
  have odd : ¬2∣u := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have pure : u=3^u.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
    intro q pq dq
    have := pq.two_le
    have low : q≤3 := by by_contra! high; exact bad q pq high (dq.trans du)
    by_contra ne
    have e : q=2 := by omega
    exact odd (e ▸ dq))
  have a2 : a≤2 := by
    by_contra! high
    exact h8 ((pow_dvd_pow (2:ℕ) high).trans (form ▸ dvd_mul_right _ _))
  have b1 : u.primeFactorsList.length≤1 := by
    by_contra! high
    exact h9 ((show 9∣u from pure ▸ pow_dvd_pow (3:ℕ) high).trans du)
  have bound := Nat.mul_le_mul (Nat.pow_le_pow_right (by decide : 0<2) a2)
    (Nat.pow_le_pow_right (by decide : 0<3) b1)
  rw [←pure,form] at bound
  omega

private theorem cubic_quadratic_primes (w : ℕ) (hw : 2<w) :
    (∃ q : ℕ, q.Prime ∧ 3<q ∧ q∣w^2+7*w+13) ∧
    (∃ q : ℕ, q.Prime ∧ 3<q ∧ q∣w^2+6*w+12) := by
  have avoid (m : ℕ) (hm : m=8 ∨ m=9) :
      ¬m∣w^2+7*w+13 ∧ ¬m∣w^2+6*w+12 := by
    have table : ∀ x : Fin m, (x.val^2+7*x.val+13)%m≠0 ∧ (x.val^2+6*x.val+12)%m≠0 := by
      rcases hm with rfl|rfl <;> decide +kernel
    have mpos : 0 < m := by omega
    have atw := table ⟨w%m,Nat.mod_lt _ mpos⟩
    have co := Nat.mod_modEq w m
    have c1 := ((co.pow 2).add (co.mul_left 7)).add_right 13
    have c2 := ((co.pow 2).add (co.mul_left 6)).add_right 12
    exact ⟨fun d => atw.1 (c1.trans (Nat.modEq_zero_iff_dvd.mpr d)),
      fun d => atw.2 (c2.trans (Nat.modEq_zero_iff_dvd.mpr d))⟩
  have h8 := avoid 8 (Or.inl rfl)
  have h9 := avoid 9 (Or.inr rfl)
  exact ⟨large_factor_of_short_valuations (by nlinarith) h8.1 h9.1,
    large_factor_of_short_valuations (by nlinarith) h8.2 h9.2⟩

private theorem consecutive_small_support {m : ℕ} (hm : 16 < m)
    (first : ∀ q : ℕ, q.Prime → q∣m → q≤3)
    (second : ∀ q : ℕ, q.Prime → q∣m+1 → q≤3) : False := by
  have pure (n p q : ℕ) (hn : 0<n) (opts : (p=2 ∧ q=3) ∨ (p=3 ∧ q=2))
      (small : ∀ r : ℕ, r.Prime → r∣n → r≤3) (noq : ¬q∣n) : ∃ a : ℕ, n=p^a := by
    refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd hn.ne' ?_⟩
    intro r pr dr
    have := small r pr dr
    have := pr.two_le
    by_contra ne
    have eq : r=q := by rcases opts with ⟨hp,hq⟩|⟨hp,hq⟩ <;> omega
    exact noq (eq ▸ dr)
  by_cases ev : 2∣m
  · obtain ⟨b,hb⟩ := pure (m+1) 3 2 (by omega) (by decide) second (by omega)
    have bn : b≠0 := by rintro rfl; norm_num at hb; omega
    have d3 : 3∣m+1 := hb ▸ dvd_pow_self _ bn
    obtain ⟨a,ha⟩ := pure m 2 3 (by omega) (by decide) first (by omega)
    have a4 : 4≤a := by
      by_contra! low
      have := Nat.pow_le_pow_right (by decide : 0<2) (by omega : a≤3)
      omega
    exact power_plus_one_not_three a4 (ha ▸ hb)
  · obtain ⟨b,hb⟩ := pure m 3 2 (by omega) (by decide) first ev
    have bn : b≠0 := by rintro rfl; norm_num at hb; omega
    have d3 : 3∣m := hb ▸ dvd_pow_self _ bn
    obtain ⟨a,ha⟩ := pure (m+1) 2 3 (by omega) (by decide) second (by omega)
    have a3 : 3≤a := by
      by_contra! low
      have := Nat.pow_le_pow_right (by decide : 0<2) (by omega : a≤2)
      omega
    have d8 : 8∣m+1 := ha ▸ pow_dvd_pow (2:ℕ) a3
    have := three_pow_mod_eight b
    omega

/-- At offsets two, three and four, an integer multiple of the corresponding
offset by a cube forces witnesses at twice or nine times that offset. -/
private theorem no_scaled_cubes {n k z : ℕ} (large : 32000<n) (hk : k=2 ∨ k=3 ∨ k=4)
    (eq : n+k=k*z^3) (small : ∀ r : ℕ, r.Prime → r≤36 → r∣n)
    (sol : Erdos889.v_l 1 n=1) : False := by
  have k4 : k≤4 := by omega
  have zbig : 20<z := by
    by_contra! low
    have := Nat.mul_le_mul k4 (Nat.pow_le_pow_left low 3)
    norm_num at this
    omega
  let w := z-4
  have wz : z=w+4 := by dsimp only [w]; omega
  have wb : 16 < w+5 := by omega
  obtain ⟨first,second⟩ := cubic_quadratic_primes w (by omega)
  have force (K L F G : ℕ) (shift : K ∈ [4,6,8,18,27,36]) (fac : n+K=k*(L*F))
      (congr : F=G*L+3 ∨ F=G*L+12) (outside : ∃ q : ℕ, q.Prime ∧ 3<q ∧ q∣F) :
      ∀ q : ℕ, q.Prime → q∣L → q≤3 := by
    obtain ⟨s,ps,hs,ds⟩ := outside
    have cap : K≤36 ∧ 0<K := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at shift
      omega
    have eligible (q : ℕ) (pq : q.Prime) (hq : 3<q) (dq : q∣n+K) : K<q := by
      by_contra! low
      have dn := small q pq (by omega)
      have dk := (Nat.dvd_add_iff_right dn).mpr dq
      have table : ∀ k ∈ [4,6,8,18,27,36], ∀ p : Fin 37,
          p.val.Prime → 3<p.val → ¬p.val∣k := by decide +kernel
      exact table K shift ⟨q,by omega⟩ pq hq dk
    intro q pq dq
    by_contra! high
    have ne : q≠s := by
      rintro rfl
      have mul := dvd_mul_of_dvd_right dq G
      rcases congr with e|e
      · rw [e] at ds
        have d := (Nat.dvd_add_iff_right mul).mpr ds
        have := Nat.le_of_dvd (by decide : 0<3) d
        omega
      · rw [e] at ds
        have d := (Nat.dvd_add_iff_right mul).mpr ds
        rcases pq.dvd_mul.mp (show q∣4*3 from d) with df|dt
        · have dd := pq.dvd_of_dvd_pow (show q∣(2:ℕ)^2 from df)
          have := Nat.le_of_dvd (by decide : 0<2) dd; omega
        · have := Nat.le_of_dvd (by decide : 0<3) dt; omega
    have d1 : q∣n+K := fac ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dq _) _
    have d2 : s∣n+K := fac ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right ds _) _
    exact two_primes cap.2 pq ps ne (eligible q pq high d1) (eligible s ps hs d2) d1 d2 sol
  have f1 : n+2*k=k*((w+5)*(w^2+7*w+13)) := by
    calc
      _ = (n+k)+k := by omega
      _ = _ := by rw [eq,wz]; ring
  have f2 : n+9*k=k*((w+6)*(w^2+6*w+12)) := by
    calc
      _ = (n+k)+8*k := by omega
      _ = _ := by rw [eq,wz]; ring
  have s1 := force (2*k) (w+5) (w^2+7*w+13) (w+2)
    (by rcases hk with rfl|rfl|rfl <;> decide) f1 (Or.inl (by ring)) first
  have s2 := force (9*k) (w+6) (w^2+6*w+12) w
    (by rcases hk with rfl|rfl|rfl <;> decide) f2 (Or.inr (by ring)) second
  exact consecutive_small_support wb s1 s2


private theorem cubic_exponent_impossible {n x a y b j : ℕ} (large : 32000<n)
    (base : x=2 ∨ x=3) (index : j=1 ∨ j=2) (allowed : x^j=2 ∨ x^j=3 ∨ x^j=4)
    (eq : n+x^j=x^a*y^b) (small : ∀ r : ℕ, r.Prime → r≤36 → r∣n)
    (sol : Erdos889.v_l 1 n=1) : ¬3∣b := by
  intro div
  have aligned := cubic_alignment base index (small 7 (by decide) (by decide)) eq div
  have jj : j%3=j := Nat.mod_eq_of_lt (by omega)
  rw [jj] at aligned
  have ae : a=j+(a/3)*3 := by omega
  obtain ⟨m,hm⟩ := div
  have raised : n+x^j=x^j*(x^(a/3)*y^m)^3 := by
    calc
      _ = x^(j+(a/3)*3)*y^(m*3) := by rw [←ae,Nat.mul_comm m 3,←hm,eq]
      _ = _ := by rw [pow_add,pow_mul,pow_mul,mul_pow]; ring
  exact no_scaled_cubes large allowed raised small sol

private theorem eventually_divides_through
    (eventual : ∀ q : ℕ, q.Prime → ∃ B : ℕ, ∀ n : ℕ, B<n → Erdos889.v_l 1 n=1 → q∣n)
    (T : ℕ) :
    ∃ B : ℕ, ∀ n : ℕ, B<n → Erdos889.v_l 1 n=1 →
      ∀ q : ℕ, q.Prime → q≤T → q∣n := by
  induction T with
  | zero =>
    refine ⟨0,?_⟩
    intro n hn sol q pq low
    have := pq.two_le
    omega
  | succ t ih =>
    obtain ⟨A,hA⟩ := ih
    by_cases pt : (t+1).Prime
    · obtain ⟨B,hB⟩ := eventual _ pt
      refine ⟨max A B,?_⟩
      intro n hn sol q pq low
      by_cases e : q=t+1
      · exact e ▸ hB n (lt_of_le_of_lt (Nat.le_max_right _ _) hn) sol
      · exact hA n (lt_of_le_of_lt (Nat.le_max_left _ _) hn) sol q pq (by omega)
    · refine ⟨A,?_⟩
      intro n hn sol q pq low
      have ne : q≠t+1 := by rintro rfl; exact pt pq
      exact hA n hn sol q pq (by omega)

/-- The prime above three in p+2 occurs with exponent one. The cutoff T
may be chosen to impose any fixed initial set of prime divisors on p−1. -/
def H1 : Prop := ∃ T B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B<p →
    (∀ x : ℕ, 1<x → p≠x^4+1) → (∀ e : ℕ, p≠2^e+1) →
    p%3=1 → (∀ l : ℕ, l.Prime → l≤T → l∣p-1) →
    (∃ t u : ℕ, t.Prime ∧ 3<t ∧ T<t ∧ 0<u ∧ p+2=3^u*t) →
    (∃ q r a b c d : ℕ, q.Prime ∧ r.Prime ∧ 2<q ∧ 3<r ∧ T<q ∧ T<r ∧ q≠r ∧
      0<a ∧ 0<b ∧ 0<c ∧ 0<d ∧ (a=1 ∨ c=1) ∧ ¬4∣b ∧ ¬4∣d ∧ ¬3∣b ∧ ¬3∣d ∧ p+1=2^a*q^b ∧ p+3=2^c*r^d) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p+d ∧ s∣p+d

/-- The prime above three in p+2 occurs at least twice. Its exponent is
coprime to that of three and cannot be a multiple of three or four. -/
def H2 : Prop := ∃ T B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B<p →
    (∀ x : ℕ, 1<x → p≠x^4+1) → (∀ e : ℕ, p≠2^e+1) →
    p%3=1 → (∀ l : ℕ, l.Prime → l≤T → l∣p-1) →
    (∃ t u v : ℕ, t.Prime ∧ 3<t ∧ T<t ∧ 0<u ∧ 2≤v ∧ u.Coprime v ∧
      ¬4∣v ∧ ¬3∣v ∧ p+2=3^u*t^v) →
    (∃ q r a b c d : ℕ, q.Prime ∧ r.Prime ∧ 2<q ∧ 3<r ∧ T<q ∧ T<r ∧ q≠r ∧
      0<a ∧ 0<b ∧ 0<c ∧ 0<d ∧ (a=1 ∨ c=1) ∧ ¬4∣b ∧ ¬4∣d ∧ ¬3∣b ∧ ¬3∣d ∧ p+1=2^a*q^b ∧ p+3=2^c*r^d) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p+d ∧ s∣p+d

theorem main : H1 → H2 → OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.H1 := by
  have eventual := Erdos889.EventualPrimeDivisibility.eventually_divides_bad
  have quadratic := Erdos889.QuadraticSmooth.large_prime_of_square_add_one
  rintro ⟨X,A,h₁⟩ ⟨Y,B,h₂⟩
  let T := max X Y+36
  obtain ⟨F,hF⟩ := eventually_divides_through eventual T
  obtain ⟨G,hG⟩ := bounded_shift_no_fourths quadratic
  refine ⟨max (max A B) (max F G)+32002,?_⟩
  intro p pp op bound fourth outer
  have mA := Nat.le_max_left A B
  have mB := Nat.le_max_right A B
  have mF := Nat.le_max_left F G
  have mG := Nat.le_max_right F G
  have mAB := Nat.le_max_left (max A B) (max F G)
  have mFG := Nat.le_max_right (max A B) (max F G)
  have lo : 223<p := by omega
  have xx : X≤T := by dsimp only [T]; have := Nat.le_max_left X Y; omega
  have yy : Y≤T := by dsimp only [T]; have := Nat.le_max_right X Y; omega
  obtain ⟨fermat,q,r,a,b,c,d,pq,pr,hq,hr,qr,ap,bp,cp,dp,one,left,right⟩ := outer
  by_contra missing
  have sol := missing_prime_solution pp missing
  have small := hF (p-1) (by omega) sol
  have d3 := small 3 Nat.prime_three (by dsimp only [T]; omega)
  have through36 (r : ℕ) (pr : r.Prime) (le : r≤36) : r∣p-1 := small r pr (by dsimp only [T]; omega)
  have pm : p%3=1 := by omega
  obtain ⟨t,u,v,pt,ht,up,vp,cop,mid⟩ := (middle_classification pp lo pm missing).resolve_left (by
    rintro ⟨k,pk,ok,eq⟩
    exact pure_three_exclusion pp lo pk ok eq missing)
  have outside (l k : ℕ) (pl : l.Prime) (lk : ¬l∣k) (div : l∣(p-1)+k) : T<l := by
    by_contra! low
    exact lk ((Nat.dvd_add_iff_right (small l pl low)).mpr div)
  have qT : T<q := outside q 2 pq (by intro dv; have := Nat.le_of_dvd (by decide : 0<2) dv; omega)
    (by rw [show p-1+2=p+1 by omega,left]; exact dvd_mul_of_dvd_right (dvd_pow_self _ bp.ne') _)
  have rT : T<r := outside r 4 pr (by
      intro dv
      have e := pr.dvd_of_dvd_pow (show r∣(2:ℕ)^2 from dv)
      have := Nat.le_of_dvd (by decide : 0<2) e
      omega)
    (by rw [show p-1+4=p+3 by omega,right]; exact dvd_mul_of_dvd_right (dvd_pow_self _ dp.ne') _)
  have tT : T<t := outside t 3 pt (by intro dv; have := Nat.le_of_dvd (by decide : 0<3) dv; omega)
    (by rw [show p-1+3=p+2 by omega,mid]; exact dvd_mul_of_dvd_right (dvd_pow_self _ vp.ne') _)
  have noFourB := hG p 1 2 q a b (by omega) (by decide) (by decide) left missing
  have noFourD := hG p 3 2 r c d (by omega) (by decide) (by decide) right missing
  have noFourV := hG p 2 3 t u v (by omega) (by decide) (by decide) mid missing
  have noCubeB := cubic_exponent_impossible (x:=2) (j:=1) (by omega : 32000<p-1)
    (Or.inl rfl) (Or.inl rfl) (by decide)
    (show p-1+2^1=2^a*q^b by rw [←left]; omega) through36 sol
  have noCubeD := cubic_exponent_impossible (x:=2) (j:=2) (by omega : 32000<p-1)
    (Or.inl rfl) (Or.inr rfl) (by decide)
    (show p-1+2^2=2^c*r^d by rw [←right]; omega) through36 sol
  have noCubeV := cubic_exponent_impossible (x:=3) (j:=1) (by omega : 32000<p-1)
    (Or.inr rfl) (Or.inl rfl) (by decide)
    (show p-1+3^1=3^u*t^v by rw [←mid]; omega) through36 sol
  by_cases vOne : v=1
  · exact missing (h₁ p pp op (by omega) fourth fermat pm (fun l pl low => small l pl (low.trans xx))
      ⟨t,u,pt,ht,by omega,up,by simpa only [vOne,pow_one] using mid⟩
      ⟨q,r,a,b,c,d,pq,pr,hq,hr,by omega,by omega,qr,ap,bp,cp,dp,one,noFourB,noFourD,
        noCubeB,noCubeD,left,right⟩)
  · exact missing (h₂ p pp op (by omega) fourth fermat pm (fun l pl low => small l pl (low.trans yy))
      ⟨t,u,v,pt,ht,by omega,up,by omega,cop,noFourV,noCubeV,mid⟩
      ⟨q,r,a,b,c,d,pq,pr,hq,hr,by omega,by omega,qr,ap,bp,cp,dp,one,noFourB,noFourD,
        noCubeB,noCubeD,left,right⟩)

end OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H1_R1
