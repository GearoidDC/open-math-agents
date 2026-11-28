import Erdos889PrimeNineteenFull
import E889PrimeTwentyThreeD103

/-! Obstruction from the two cyclotomic factors at twice the initial offset. -/

namespace Erdos889.PrimeTwentyThree
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem supported_three (m x y q : ℕ) (pos : 0 < m)
    (sup : ∀ p : ℕ, p.Prime → p∣m → p=x ∨ p=y ∨ p=q) :
    ∃ a b c : ℕ, m=x^a*y^b*q^c := by
  induction m using induction_on_primes with
  | zero => omega
  | one => exact ⟨0,0,0,by simp⟩
  | prime_mul p t pp ih =>
    obtain ⟨a,b,c,eq⟩ := ih (Nat.pos_of_mul_pos_left pos) (fun r pr dr =>
      sup r pr (dvd_mul_of_dvd_right dr _))
    rcases sup p pp (dvd_mul_right p t) with rfl|rfl|rfl
    · exact ⟨a+1,b,c,by rw [eq,pow_succ]; ring⟩
    · exact ⟨a,b+1,c,by rw [eq,pow_succ]; ring⟩
    · exact ⟨a,b,c+1,by rw [eq,pow_succ]; ring⟩

theorem supported_offset {n j x y q : ℕ} (pq : q.Prime) (jq : j<q) (hj : 0<j) (jl : j<23) (div : 9699690∣n)
    (hit : q∣n+j) (xy : x*y∣n+j) (cop : (x*y).Coprime q)
    (small : ∀ p : Fin 23, p.val.Prime → p.val∣j → p.val=x ∨ p.val=y)
    (sol : v_l 1 n=1) : ∃ a b c : ℕ, n+j=x^a*y^b*q^c ∧ 0<a ∧ 0<b ∧ 0<c := by
  have whole := cop.mul_dvd_of_dvd_of_dvd xy hit
  obtain ⟨t,ht⟩ := whole
  have pos : 0<t := by by_contra! h; rw [show t=0 by omega,mul_zero] at ht; omega
  obtain ⟨a,b,c,eq⟩ := supported_three t x y q pos (by
    intro p pp dp
    have dn : p∣n+j := ht ▸ dvd_mul_of_dvd_right dp _
    by_cases low : p≤j
    · have tab : ∀ r : Fin 23, r.val.Prime → r.val∣9699690 := by decide
      have dj := (Nat.dvd_add_iff_right ((tab ⟨p,by omega⟩ pp).trans div)).mpr dn
      rcases small ⟨p,by omega⟩ pp dj with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · by_contra! neq
      exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.two_primes hj pp
        pq neq.2.2 (by omega) jq dn hit sol)
  refine ⟨a+1,b+1,c+1,?_,by omega,by omega,by omega⟩
  rw [ht,eq,pow_succ,pow_succ,pow_succ]
  ring

theorem no_forty_one_at_three {n : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 41∣n+3) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D103.exponents (by omega) div pp sol eq ha hc
  let z := 3^(a/12)*41^(c/12)
  have regroup (p i r : ℕ) (e : i%12=r) : p^i=p^r*(p^(i/12))^12 := by
    rw [←pow_mul,←pow_add,show r+i/12*12=i by omega]
  have shape : n+3=3*z^12 := by
    rw [eq,regroup 3 a 1 ra,regroup 41 c 0 rc]
    dsimp only [z]
    rw [mul_pow,pow_one,pow_zero,one_mul,mul_assoc]
  have hi : 1<z := by
    by_contra! low
    have := Nat.pow_le_pow_left low 12
    omega
  exact PrimeNineteen.no_nineteenth_twelfth (by decide) (by decide) big
    ((by decide : 510510∣9699690).trans div) hi shape sol

set_option maxHeartbeats 3000000 in
theorem no_twenty_third_twelfth {n j z : ℕ} (hj : 0<j) (small : j≤22) (large : 1000000000000000000<n) (div : 9699690∣n) (primeSucc : (n+1).Prime) (big : 1<z)
    (shape : n+j=j*z^12) (sol : v_l 1 n=1) : False := by
  let t := z^4
  let B := (t-1)^2+(t-1)+1
  have tlarge : 15<t := Nat.pow_le_pow_left big 4
  have Bpos : 1<B := by dsimp only [B]; omega
  have identity : B+t = t^2+1 := by
    have tz : t-1+1=t := by omega
    dsimp only [B]; nlinarith [congrArg (fun i : ℕ => i*(t-1)) tz,congrArg (fun i : ℕ => i*t) tz]
  have mul : (t+1)*B=z^12+1 := by
    have te : t^3=z^12 := by dsimp only [t]; rw [←pow_mul]
    rw [←te]; nlinarith [congrArg (fun w : ℕ => w*t) identity]
  have classifyA (p : ℕ) (pp : p.Prime) (low : p≤j+j) (dp : p∣t+1) : p=2 ∨ p=17 := by
    have tab : ∀ q : Fin 45, q.val.Prime → ∀ u : Fin q.val, (u.val^4+1)%q.val=0 → q.val=2 ∨ q.val=17 ∨ q.val=41 := by decide +kernel
    have m := ((Nat.mod_modEq z p).pow 4).add_right 1
    rcases tab ⟨p,by omega⟩ pp ⟨z%p,Nat.mod_lt _ pp.pos⟩ (m.trans (Nat.modEq_zero_iff_dvd.mpr dp)) with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · change p=41 at h
      subst p
      have near : n+(j+j)=j*((t+1)*B) := by rw [mul,Nat.mul_add,mul_one]; omega
      have d : 41∣n+(j+j) := near ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dp _) _
      rcases (show j=21 ∨ j=22 by clear * - small low; omega) with rfl|rfl
      · have d1 : 41∣n+1 := by clear * - d; omega
        have e := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 41) primeSucc).mp d1
        omega
      · exact False.elim (no_forty_one_at_three large div primeSucc sol (by clear * - d; omega))
  have largeZ : 239<z^2 := by
    by_contra! low
    have lim : z≤15 := by nlinarith
    have zz := Nat.pow_le_pow_left lim 12
    have nj := Nat.mul_le_mul small zz
    omega
  obtain ⟨p,pp,hp,dp⟩ : ∃ p : ℕ, p.Prime ∧ j+j<p ∧ p∣t+1 := by
    by_contra missing
    have classify (p : ℕ) (pp : p.Prime) (dp : p∣t+1) : p=2 ∨ p=17 :=
      classifyA p pp (by by_contra! hi; exact missing ⟨p,pp,hi,dp⟩) dp
    by_cases parity : 2∣t+1
    · let u := (t+1)/2
      have eu : 2*u=t+1 := by dsimp only [u]; omega
      have no4 : ¬ 4∣t+1 := by
        intro dv
        have m := ((Nat.mod_modEq z 4).pow 4).add_right 1
        have tab : ∀ r : Fin 4, (r.val^4+1)%4≠0 := by decide
        exact tab ⟨z%4,by omega⟩ (m.trans (Nat.modEq_zero_iff_dvd.mpr dv))
      have pu : u=17^u.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
        intro p pp dv
        rcases classify p pp (eu ▸ dvd_mul_of_dvd_right dv _) with h|h
        · subst p; omega
        · exact h)
      have eq : (z^2)^2+1=2*5^0*13^0*17^u.primeFactorsList.length := by
        simp only [pow_zero,mul_one,←pow_mul,←pu]
        exact eu.symm
      exact (Nat.not_lt_of_ge (Erdos889.QuadraticTwenty.square_add_one_smooth_twenty eq)) largeZ
    · obtain ⟨p,pp,dp⟩ := Nat.exists_prime_and_dvd (show t+1≠1 by omega)
      have e : p=17 := (classify p pp dp).resolve_left (by rintro rfl; exact parity dp)
      subst p
      have near : n+(j+j)=j*((t+1)*B) := by rw [mul,Nat.mul_add,mul_one]; omega
      have d2 : 17∣n+(j+j) := near ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dp _) _
      have dj := (Nat.dvd_add_iff_right ((by decide : 17∣9699690).trans div)).mpr d2
      have j17 : j=17 := by omega
      subst j
      have nz : ¬2∣z := by
        intro dz
        have even : 2∣17*z^12 := dvd_mul_of_dvd_right (dz.trans (dvd_pow_self _ (by decide : 12≠0))) _
        rw [←shape] at even; omega
      have zm : z%2=1 := by omega
      have tm : t%2=1 := by dsimp only [t]; rw [Nat.pow_mod,zm]
      exact parity (by omega)
  obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd (show B≠1 by omega)
  have hq : 44<q := by
    by_contra! low
    have tab : ∀ q : Fin 45, q.val.Prime → ∀ u : Fin q.val, ¬Nat.ModEq q.val (u.val^4) (u.val^8+1) := by decide +kernel
    have m := (Nat.modEq_zero_iff_dvd.mpr dq).add_right t
    rw [identity,zero_add] at m
    have zt : t^2=z^8 := by dsimp only [t]; rw [←pow_mul]
    rw [zt] at m
    have du := Nat.mod_modEq z q
    exact tab ⟨q,by omega⟩ pq ⟨z%q,Nat.mod_lt _ pq.pos⟩ ((du.pow 4).trans (m.symm.trans ((du.pow 8).add_right 1).symm))
  have ne : p≠q := by
    rintro rfl
    have e : B+3*(t+1)=(t+1)^2+3 := by nlinarith
    have left := dvd_add dq (dvd_mul_of_dvd_right dp 3)
    rw [e] at left
    have dd := (Nat.dvd_add_iff_right (dp.trans (dvd_pow_self _ (by decide : 2≠0)))).mpr left
    have := Nat.le_of_dvd (by decide : 0<3) dd; omega
  have h : n+(j+j)=j*((t+1)*B) := by rw [mul,Nat.mul_add,mul_one]; omega
  exact two_primes (by omega : 0<j+j) pp pq ne (by omega) (by omega)
    (h ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dp _) _) (h ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right dq _) _) sol


end Erdos889.PrimeTwentyThree
#print axioms Erdos889.PrimeTwentyThree.no_twenty_third_twelfth
