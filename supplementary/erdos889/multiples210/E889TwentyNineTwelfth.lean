import E889PrimeTwentyThreeTwelfth
import E889FortyOneD5
import E889FortyOneD7
import E889FortyOneD9
import E889FortyOneD11
import E889FortyOneD13
import E889FortyOneD15
import E889FortyOneD17
import E889FortyOneD19

/-! The exceptional small divisor 41 in a cyclotomic factor forces an earlier
odd offset. The certificates exclude all these offsets through 19. -/
namespace Erdos889.PrimeTwentyNine
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

theorem close_forty_one_exponents {n j x y a b c u v : ℕ} (hj : 0<j) (small : j≤22)
    (big : 1000000000000000000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1)
    (jval : j=x^u*y^v) (shape : n+j=x^a*y^b*41^c)
    (ha : a%12=u) (hb : b%12=v) (hc : c%12=0) : False := by
  let z := x^(a/12)*y^(b/12)*41^(c/12)
  have regroup (p i r : ℕ) (eq : i%12=r) : p^i=p^r*(p^(i/12))^12 := by
    rw [←pow_mul,←pow_add,show r+i/12*12=i by omega]
  have twelfth : n+j=j*z^12 := by
    calc
      n+j=x^a*y^b*41^c := shape
      _=j*z^12 := by
        rw [regroup x a u ha,regroup y b v hb,regroup 41 c 0 hc,jval]
        dsimp only [z]
        rw [mul_pow,mul_pow,pow_zero]
        ring
  have hi : 1<z := by
    by_contra! low
    have zz := Nat.pow_le_pow_left low 12
    have nj := Nat.mul_le_mul_left j zz
    omega
  exact PrimeTwentyThree.no_twenty_third_twelfth hj small big div pp hi twelfth sol

private theorem reject1 {n : ℕ} (big : 1000000000000000000<n) (pp : (n+1).Prime) (hit : 41∣n+1) : False := by
  have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 41) pp).mp hit
  omega

private theorem reject5 {n : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 41∣n+5) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=5) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := PrimeTwentyThree.FortyOneD5.exponents (by omega) div pp sol eq ha hc
  exact close_forty_one_exponents (j:=5) (x:=5) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0)
    (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem reject7 {n : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 41∣n+7) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=7) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := PrimeTwentyThree.FortyOneD7.exponents (by omega) div pp sol eq ha hc
  exact close_forty_one_exponents (j:=7) (x:=7) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0)
    (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem reject9 {n : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 41∣n+9) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=3) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := PrimeTwentyThree.FortyOneD9.exponents (by omega) div pp sol eq ha hc
  exact close_forty_one_exponents (j:=9) (x:=3) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0)
    (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem reject11 {n : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 41∣n+11) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=11) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := PrimeTwentyThree.FortyOneD11.exponents (by omega) div pp sol eq ha hc
  exact close_forty_one_exponents (j:=11) (x:=11) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0)
    (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem reject13 {n : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 41∣n+13) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=13) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := PrimeTwentyThree.FortyOneD13.exponents (by omega) div pp sol eq ha hc
  exact close_forty_one_exponents (j:=13) (x:=13) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0)
    (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem reject15 {n : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 41∣n+15) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=3) (y:=5) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
  obtain ⟨ra,rb,rc⟩ := PrimeTwentyThree.FortyOneD15.exponents (by omega) div pp sol eq ha hb hc
  exact close_forty_one_exponents (j:=15) (x:=3) (y:=5) (u:=1) (v:=1) (by decide) (by decide)
    big div pp sol (by decide) eq ra rb rc

private theorem reject17 {n : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 41∣n+17) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=17) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := PrimeTwentyThree.FortyOneD17.exponents (by omega) div pp sol eq ha hc
  exact close_forty_one_exponents (j:=17) (x:=17) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0)
    (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem reject19 {n : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 41∣n+19) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=19) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := PrimeTwentyThree.FortyOneD19.exponents (by omega) div pp sol eq ha hc
  exact close_forty_one_exponents (j:=19) (x:=19) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0)
    (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

/-- For any large prime-successor solution, 41 has no odd first offset through 19. -/
theorem no_forty_one_up_to_nineteen {n k : ℕ} (big : 1000000000000000000<n)
    (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1)
    (bound : k≤19) (odd : k%2=1) (hit : 41∣n+k) : False := by
  rcases (show k=1 ∨ k=3 ∨ k=5 ∨ k=7 ∨ k=9 ∨ k=11 ∨ k=13 ∨ k=15 ∨ k=17 ∨ k=19 by clear * - bound odd; omega)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact reject1 big pp hit
  · exact PrimeTwentyThree.no_forty_one_at_three big div pp sol hit
  · exact reject5 big div pp sol hit
  · exact reject7 big div pp sol hit
  · exact reject9 big div pp sol hit
  · exact reject11 big div pp sol hit
  · exact reject13 big div pp sol hit
  · exact reject15 big div pp sol hit
  · exact reject17 big div pp sol hit
  · exact reject19 big div pp sol hit

set_option maxHeartbeats 3000000 in
theorem no_twelfth_through_thirty {n j z : ℕ} (hj : 0<j) (small : j≤30) (large : 1000000000000000000<n) (div : 9699690∣n) (primeSucc : (n+1).Prime) (big : 1<z)
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
    have tab : ∀ q : Fin 61, q.val.Prime → ∀ u : Fin q.val, (u.val^4+1)%q.val=0 → q.val=2 ∨ q.val=17 ∨ q.val=41 := by decide +kernel
    have m := ((Nat.mod_modEq z p).pow 4).add_right 1
    rcases tab ⟨p,by clear * - low small; omega⟩ pp ⟨z%p,Nat.mod_lt _ pp.pos⟩ (m.trans (Nat.modEq_zero_iff_dvd.mpr dp)) with h|h|h
    · exact Or.inl h
    · exact Or.inr h
    · change p=41 at h
      subst p
      have near : n+(j+j)=j*((t+1)*B) := by rw [mul,Nat.mul_add,mul_one]; omega
      have d : 41∣n+(j+j) := near ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dp _) _
      have hjrange : 21 ≤ j := by clear * - low; omega
      have hit : 41 ∣ n+(2*j-41) := by clear * - d hjrange; omega
      have odd : (2*j-41)%2=1 := by clear * - hjrange; omega
      exact False.elim (no_forty_one_up_to_nineteen large div primeSucc sol
        (by clear * - small; omega) odd hit)
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
  have hq : 60<q := by
    by_contra! low
    have tab : ∀ q : Fin 61, q.val.Prime → ∀ u : Fin q.val, ¬Nat.ModEq q.val (u.val^4) (u.val^8+1) := by decide +kernel
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




/-- A first offset below 29 cannot yield a shifted twelfth power. -/
theorem no_twenty_ninth_twelfth {n j z : ℕ} (hj : 0<j) (small : j≤28)
    (large : 1000000000000000000<n) (div : 223092870∣n) (pp : (n+1).Prime)
    (big : 1<z) (shape : n+j=j*z^12) (sol : v_l 1 n=1) : False :=
  no_twelfth_through_thirty hj (by omega) large ((by decide : 9699690∣223092870).trans div)
    pp big shape sol
end Erdos889.PrimeTwentyNine

#print axioms Erdos889.PrimeTwentyNine.no_forty_one_up_to_nineteen
#print axioms Erdos889.PrimeTwentyNine.no_twelfth_through_thirty
