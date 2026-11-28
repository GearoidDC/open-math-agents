import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1

/-! A shifted twelfth power under the sole-missing-prime hypothesis. -/
namespace Erdos889.SoleMissing
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

theorem no_twelfth {n j z Q : ℕ} (hj : 0<j) (small : j≤30) (pQ : Q.Prime) (jQ : j<Q)
    (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠Q → r∣n) (dQ : Q∣n+j) (big : 1<z)
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
  have near : n+(j+j)=j*((t+1)*B) := by rw [mul,Nat.mul_add,mul_one]; omega
  have classifyA (p : ℕ) (pp : p.Prime) (low : p≤60) (dp : p∣t+1) : p=2 ∨ (p=17 ∧ j=17) := by
    have tab : ∀ q : Fin 61, q.val.Prime → ∀ u : Fin q.val,
        (u.val^4+1)%q.val=0 → q.val=2 ∨ q.val=17 ∨ q.val=41 := by decide +kernel
    have m := ((Nat.mod_modEq z p).pow 4).add_right 1
    have opts := tab ⟨p,by omega⟩ pp ⟨z%p,Nat.mod_lt _ pp.pos⟩ (m.trans (Nat.modEq_zero_iff_dvd.mpr dp))
    have d2 : p∣n+(j+j) := near ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dp _) _
    have diff : p≠Q := by
      rintro rfl
      have dj : p∣j := (Nat.dvd_add_iff_right dQ).mpr (by simpa only [Nat.add_assoc] using d2)
      exact (Nat.not_dvd_of_pos_of_lt hj jQ) dj
    have low53 : p≤53 := by rcases opts with h|h|h <;> simp only at h <;> omega
    have dd := (Nat.dvd_add_iff_right (sole p pp low53 diff)).mpr d2
    rcases opts with h|h|h
    · exact Or.inl h
    · right; simp only at h; subst p; exact ⟨rfl,by omega⟩
    · simp only at h; subst p; omega
  obtain ⟨p,pp,hp,dp⟩ : ∃ p : ℕ, p.Prime ∧ 60<p ∧ p∣t+1 := by
    by_contra miss
    have all (r : ℕ) (pr : r.Prime) (dr : r∣t+1) := classifyA r pr (by by_contra! hi; exact miss ⟨r,pr,hi,dr⟩) dr
    by_cases ex : j=17
    · subst j
      have two := sole 2 (by decide) (by decide) (by omega)
      have nz : ¬2∣z := by
        intro dv
        have d : 2∣17*z^12 := dvd_mul_of_dvd_right (dv.trans (dvd_pow_self _ (by decide : 12≠0))) _
        rw [←shape] at d; omega
      have dmod : (t+1)%4=2 := by
        have tab : ∀ u : Fin 4, u.val%2≠0 → (u.val^4+1)%4=2 := by decide
        have m := ((Nat.mod_modEq z 4).pow 4).add_right 1
        change ((z%4)^4+1)%4 = (t+1)%4 at m
        exact m.symm.trans (tab ⟨z%4,by omega⟩ (by change z%4%2≠0; omega))
      let C := (t+1)/2
      have form : 2*C=t+1 := by dsimp [C]; omega
      have no2 : ¬2∣C := by omega
      have pow17 : C=17^C.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
        intro r pr dr
        have dA : r∣t+1 := form ▸ dvd_mul_of_dvd_right dr _
        rcases all r pr dA with h|h
        · subst r; exact False.elim (no2 dr)
        · exact h.1)
      have limit := Erdos889.QuadraticTwenty.square_add_one_smooth_twenty (x:=z^2) (i:=0) (j:=0)
        (k:=C.primeFactorsList.length) (by simp only [pow_zero,mul_one,←pow_mul]; exact form.symm.trans (congrArg (2*·) pow17))
      have droot := pQ.dvd_mul.mp (shape ▸ dQ)
      have dz := pQ.dvd_of_dvd_pow (droot.resolve_left (Nat.not_dvd_of_pos_of_lt (by decide) jQ))
      have lower := Nat.le_of_dvd (by omega : 0<z) dz
      nlinarith
    have pow2 := Nat.eq_prime_pow_of_unique_prime_dvd (show t+1≠0 by omega) (fun {p} pp dp =>
      (all p pp dp).resolve_right (fun h => ex h.2))
    let e := (t+1).primeFactorsList.length
    change t+1=2^e at pow2
    have ee : 2≤e := by by_contra! low; have := Nat.pow_le_pow_right (by decide : 0<2) (show e≤1 by omega); omega
    have dv : 4∣t+1 := pow2 ▸ pow_dvd_pow 2 ee
    have m := ((Nat.mod_modEq z 4).pow 4).add_right 1
    have bad := m.trans (Nat.modEq_zero_iff_dvd.mpr dv)
    have tab : ∀ i : Fin 4, (i.val^4+1)%4≠0 := by decide
    exact tab ⟨z%4,by omega⟩ bad
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
  exact two_primes (by omega : 0<j+j) pp pq ne (by omega) (by omega)
    (near ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dp _) _) (near ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right dq _) _) sol

end Erdos889.SoleMissing
#print axioms Erdos889.SoleMissing.no_twelfth


/- Finite modular certificates for shifted powers under a unique missing prime. -/
namespace Erdos889.SoleMissing.Ranks
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem three_factors (A B Q m : ℕ) (hm : 0 < m)
    (pool : ∀ p : ℕ, p.Prime → p∣m → p=A ∨ p=B ∨ p=Q) :
    ∃ a b c : ℕ, m=A^a*B^b*Q^c := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases one : m=1
    · exact ⟨0,0,0,by simp [one]⟩
    let p := m.minFac
    have pp : p.Prime := Nat.minFac_prime one
    have dp : p∣m := Nat.minFac_dvd _
    have form : m/p*p=m := Nat.div_mul_cancel dp
    have lower : m/p < m := Nat.div_lt_self hm pp.one_lt
    have pos : 0 < m/p := Nat.div_pos (Nat.le_of_dvd hm dp) pp.pos
    obtain ⟨a,b,c,e⟩ := ih (m/p) lower pos (fun r pr dr =>
      pool r pr (dr.trans (Nat.div_dvd_of_dvd dp)))
    rcases pool p pp dp with h|h|h
    · exact ⟨a+1,b,c,by rw [←form,e,pow_succ,h]; ring⟩
    · exact ⟨a,b+1,c,by rw [←form,e,pow_succ,h]; ring⟩
    · exact ⟨a,b,c+1,by rw [←form,e,pow_succ,h]; ring⟩

theorem supported {n k q A B : ℕ} (hk : 0<k) (kq : k<q) (bound : k≤53)
    (pq : q.Prime) (dq : q∣n+k) (sole : ∀ p : ℕ, p.Prime → p≤53 → p≠q → p∣n)
    (small : ∀ p : Fin (k+1), p.val.Prime → p.val∣k → p.val=A ∨ p.val=B) (sol : v_l 1 n=1) :
    ∃ a b c : ℕ, n+k=A^a*B^b*q^c := by
  apply three_factors _ _ _ _ (by omega)
  intro p pp dp
  by_cases eq : p=q
  · exact Or.inr (Or.inr eq)
  by_cases high : k<p
  · exact False.elim (two_primes hk pp pq eq high kq dp dq sol)
  rcases small ⟨p,by omega⟩ pp ((Nat.dvd_add_iff_right (sole p pp (by omega) eq)).mpr dp) with h|h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem row {n k A B Q a b c r d G e x y z w : ℕ}
    (shape : n+k=A^a*B^b*Q^c) (rn : r∣n) (hd : 0<d)
    (hA : Nat.ModEq r (A^e) (G^x)) (hB : Nat.ModEq r (B^e) (G^y))
    (hQ : Nat.ModEq r (Q^e) (G^z)) (hk : Nat.ModEq r (k^e) (G^w))
    (hG : Nat.ModEq r (G^d) 1)
    (inj : ∀ u : Fin d, Nat.ModEq r (G^u.val) (G^w) → u.val=w) :
    (x*a+y*b+z*c)%d=w := by
  let f := x*a+y*b+z*c
  have mult : Nat.ModEq r ((A^a*B^b*Q^c)^e) (G^f) := by
    dsimp only [f]
    rw [mul_pow,mul_pow,pow_add,pow_add,pow_mul,pow_mul,pow_mul]
    rw [←pow_mul,←pow_mul,←pow_mul, Nat.mul_comm a e,Nat.mul_comm b e,Nat.mul_comm c e,
      pow_mul,pow_mul,pow_mul]
    exact ((hA.pow _).mul (hB.pow _)).mul (hQ.pow _)
  have shift := (Nat.modEq_zero_iff_dvd.mpr rn).add_right k
  rw [zero_add,shape] at shift
  have eq := mult.symm.trans ((shift.pow e).trans hk)
  have cyclic : Nat.ModEq r (G^f) (G^(f%d)) := by
    calc
      G^f=G^(f%d)*(G^d)^(f/d) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
      _ ≡ G^(f%d)*1^(f/d) [MOD r] := (hG.pow _).mul_left _
      _ = _ := by simp
  exact inj ⟨f%d,Nat.mod_lt _ hd⟩ (cyclic.symm.trans eq)

theorem assemble {n k A B Q a b c i j : ℕ}
    (shape : n+k=A^a*B^b*Q^c) (small : k=A^i*B^j)
    (ra : A^(a%12)=A^i) (rb : B^(b%12)=B^j) (rc : c%12=0) :
    ∃ z : ℕ, n+k=k*z^12 := by
  refine ⟨A^(a/12)*B^(b/12)*Q^(c/12),?_⟩
  have split (x s : ℕ) : x^s=x^(s%12)*(x^(s/12))^12 := by
    rw [←pow_mul,←pow_add,Nat.mul_comm (s/12),Nat.mod_add_div]
  rw [shape,small,split A a,split B b,split Q c,ra,rb,rc,pow_zero,one_mul,mul_pow,mul_pow]
  ring


set_option maxHeartbeats 3000000

private theorem combine {u v : ℕ} {s t : ℤ} (hv : v<12)
    (h4 : (u:ℤ)-v=4*s) (h3 : (u:ℤ)-v=3*t) : u%12=v := by omega

private theorem shape_2_1 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠2 → r∣n)
    (dq : 2∣n+1) (sol : v_l 1 n=1) : ∃ z : ℕ, n+1=1*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=1) (B:=1) (by decide : 0<1)
    (by decide : 1<2) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*c)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=0) (y:=0) (z:=2) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0]
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=0) (j:=0) shape (by decide)
    (by simp) (by simp) rem2

theorem shape_2 {n k : ℕ} (hk : 0<k) (kq : k<2) (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠2 → r∣n)
    (dq : 2∣n+k) (sol : v_l 1 n=1) : ∃ z : ℕ, n+k=k*z^12 := by
  have cases : k=1 := by omega
  subst k
  exact shape_2_1 sole dq sol

private theorem shape_3_1 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠3 → r∣n)
    (dq : 3∣n+1) (sol : v_l 1 n=1) : ∃ z : ℕ, n+1=1*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=1) (B:=1) (by decide : 0<1)
    (by decide : 1<3) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=0) (y:=0) (z:=3) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((3*c)/4 : ℕ):ℤ)-0))) - ((2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*c)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_0]
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=0) (j:=0) shape (by decide)
    (by simp) (by simp) rem2

private theorem shape_3_2 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠3 → r∣n)
    (dq : 3∣n+2) (sol : v_l 1 n=1) : ∃ z : ℕ, n+2=2*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<2)
    (by decide : 2<3) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=3) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=0) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) : ℤ) = 4*((((1*a)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((1)*(((((1*a)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (1)*(((((1*a)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

theorem shape_3 {n k : ℕ} (hk : 0<k) (kq : k<3) (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠3 → r∣n)
    (dq : 3∣n+k) (sol : v_l 1 n=1) : ∃ z : ℕ, n+k=k*z^12 := by
  have cases : k=1 ∨ k=2 := by omega
  rcases cases with rfl|rfl
  · exact shape_3_1 sole dq sol
  · exact shape_3_2 sole dq sol

private theorem shape_5_1 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠5 → r∣n)
    (dq : 5∣n+1) (sol : v_l 1 n=1) : ∃ z : ℕ, n+1=1*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=1) (B:=1) (by decide : 0<1)
    (by decide : 1<5) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*c)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=0) (y:=0) (z:=2) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0]
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=0) (j:=0) shape (by decide)
    (by simp) (by simp) rem2

private theorem shape_5_2 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠5 → r∣n)
    (dq : 5∣n+2) (sol : v_l 1 n=1) : ∃ z : ℕ, n+2=2*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<2)
    (by decide : 2<5) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=0) (z:=5) (w:=14)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 5*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 5*c)/16 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (12)*(((((14*a + 5*c)/16 : ℕ):ℤ)-0))) - ((11)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=2) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=0) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) : ℤ) = 3*((((1*a)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((1*a)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_5_3 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠5 → r∣n)
    (dq : 5∣n+3) (sol : v_l 1 n=1) : ∃ z : ℕ, n+3=3*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=1) (by decide : 0<3)
    (by decide : 3<5) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=1) (y:=0) (z:=5) (w:=1)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)) : ℤ) = 16*((((1*a + 5*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((1*a + 5*c)/16 : ℕ):ℤ)-0))) - ((2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*c)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=0) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) : ℤ) = 3*((((1*a)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((1*a)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (1)*(((((1*a)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_5_4 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠5 → r∣n)
    (dq : 5∣n+4) (sol : v_l 1 n=1) : ∃ z : ℕ, n+4=4*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<4)
    (by decide : 4<5) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=1) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=0) (z:=5) (w:=12)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-2)) + (5)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 5*c)/16 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-2) = 4*(((3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 5*c)/16 : ℕ):ℤ)-1))) - ((4)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (12)*(((((14*a + 5*c)/16 : ℕ):ℤ)-1))) - ((11)*(((a:ℤ)-2)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=2) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=0) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) : ℤ) = 3*((((1*a)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-2) = 3*(((1)*(((((1*a)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

theorem shape_5 {n k : ℕ} (hk : 0<k) (kq : k<5) (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠5 → r∣n)
    (dq : 5∣n+k) (sol : v_l 1 n=1) : ∃ z : ℕ, n+k=k*z^12 := by
  have cases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 := by omega
  rcases cases with rfl|rfl|rfl|rfl
  · exact shape_5_1 sole dq sol
  · exact shape_5_2 sole dq sol
  · exact shape_5_3 sole dq sol
  · exact shape_5_4 sole dq sol

private theorem shape_7_1 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠7 → r∣n)
    (dq : 7∣n+1) (sol : v_l 1 n=1) : ∃ z : ℕ, n+1=1*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=1) (B:=1) (by decide : 0<1)
    (by decide : 1<7) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*c)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=0) (y:=0) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0]
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=0) (j:=0) shape (by decide)
    (by simp) (by simp) rem2

private theorem shape_7_2 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠7 → r∣n)
    (dq : 7∣n+2) (sol : v_l 1 n=1) : ∃ z : ℕ, n+2=2*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<2)
    (by decide : 2<7) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=0) (z:=11) (w:=14)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-1)) + (11)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 11*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (12)*(((((14*a + 11*c)/16 : ℕ):ℤ)-0))) - ((11)*(((a:ℤ)-1)) + (9)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 11*c)/16 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=0) (z:=6) (w:=1)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (6)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 6*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((3)*(((((1*a + 6*c)/9 : ℕ):ℤ)-0))) - ((2)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (3)*(((((1*a + 6*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_7_3 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠7 → r∣n)
    (dq : 7∣n+3) (sol : v_l 1 n=1) : ∃ z : ℕ, n+3=3*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=1) (by decide : 0<3)
    (by decide : 3<7) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=1) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=0) (z:=3) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((3*a + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((3*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((3*c)/4 : ℕ):ℤ)-0))) - ((2)*(((c:ℤ)-0)))) := by
    linarith only [h2_1]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=4) (y:=0) (z:=6) (w:=4)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((4)*(((a:ℤ)-1)) + (6)*(((c:ℤ)-0)) : ℤ) = 9*((((4*a + 6*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((3)*(((((4*a + 6*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (3)*(((((4*a + 6*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_7_4 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠7 → r∣n)
    (dq : 7∣n+4) (sol : v_l 1 n=1) : ∃ z : ℕ, n+4=4*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<4)
    (by decide : 4<7) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=1) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=0) (z:=11) (w:=12)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-2)) + (11)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 11*c)/16 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-2) = 4*(((3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (12)*(((((14*a + 11*c)/16 : ℕ):ℤ)-1))) - ((11)*(((a:ℤ)-2)) + (9)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 11*c)/16 : ℕ):ℤ)-1))) - ((4)*(((a:ℤ)-2)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=0) (z:=6) (w:=2)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) + (6)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 6*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-2) = 3*(((3)*(((((1*a + 6*c)/9 : ℕ):ℤ)-0))) - ((2)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (3)*(((((1*a + 6*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_7_5 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠7 → r∣n)
    (dq : 7∣n+5) (sol : v_l 1 n=1) : ∃ z : ℕ, n+5=5*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=5) (B:=1) (by decide : 0<5)
    (by decide : 5<7) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=3) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=31) (e:=9) (x:=3) (y:=0) (z:=0) (w:=3)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((3)*(((a:ℤ)-1)) : ℤ) = 4*((((3*a)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((3*a)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)))) := by
    linarith only [h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (3)*(((((3*a)/4 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=0) (y:=0) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=7) (y:=0) (z:=6) (w:=7)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((7)*(((a:ℤ)-1)) + (6)*(((c:ℤ)-0)) : ℤ) = 9*((((7*a + 6*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((3)*(((((7*a + 6*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_7_6 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠7 → r∣n)
    (dq : 7∣n+6) (sol : v_l 1 n=1) : ∃ z : ℕ, n+6=6*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=3) (by decide : 0<6)
    (by decide : 6<7) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=3) (z:=1) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=3) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=1) (z:=11) (w:=15)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((14)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (11)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 1*b + 11*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1)) + (12)*(((((14*a + 1*b + 11*c)/16 : ℕ):ℤ)-0))) - ((11)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (9)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((1)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1)) + (3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (8)*(((((14*a + 1*b + 11*c)/16 : ℕ):ℤ)-0))) - ((8)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (8)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1)) + (3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (12)*(((((14*a + 1*b + 11*c)/16 : ℕ):ℤ)-0))) - ((12)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (11)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=1) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=4) (z:=6) (w:=5)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (6)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 4*b + 6*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=3) (G:=25) (e:=10) (x:=0) (y:=1) (z:=1) (w:=1)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*b + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 4*b + 6*c)/9 : ℕ):ℤ)-0)) + (2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (6)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((1)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 4*b + 6*c)/9 : ℕ):ℤ)-0)) + (1)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (5)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0)) + (3)*(((((1*a + 4*b + 6*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

theorem shape_7 {n k : ℕ} (hk : 0<k) (kq : k<7) (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠7 → r∣n)
    (dq : 7∣n+k) (sol : v_l 1 n=1) : ∃ z : ℕ, n+k=k*z^12 := by
  have cases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · exact shape_7_1 sole dq sol
  · exact shape_7_2 sole dq sol
  · exact shape_7_3 sole dq sol
  · exact shape_7_4 sole dq sol
  · exact shape_7_5 sole dq sol
  · exact shape_7_6 sole dq sol

private theorem shape_11_1 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+1) (sol : v_l 1 n=1) : ∃ z : ℕ, n+1=1*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=1) (B:=1) (by decide : 0<1)
    (by decide : 1<11) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=0) (z:=3) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((3*c)/4 : ℕ):ℤ)-0))) - ((2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*c)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_0]
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=0) (j:=0) shape (by decide)
    (by simp) (by simp) rem2

private theorem shape_11_2 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+2) (sol : v_l 1 n=1) : ∃ z : ℕ, n+2=2*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<2)
    (by decide : 2<11) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=0) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) : ℤ) = 4*((((1*a)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=3) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((1)*(((((1*a)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_11_3 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+3) (sol : v_l 1 n=1) : ∃ z : ℕ, n+3=3*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=1) (by decide : 0<3)
    (by decide : 3<11) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=0) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-1)) : ℤ) = 4*((((3*a)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=0) (z:=3) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((3*a)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)))) := by
    linarith only [h2_0]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((3*c)/4 : ℕ):ℤ)-0))) - ((2)*(((c:ℤ)-0)))) := by
    linarith only [h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=4) (y:=0) (z:=3) (w:=4)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((4)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 9*((((4*a + 3*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((3)*(((((4*a + 3*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0)) + (6)*(((((4*a + 3*c)/9 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_11_4 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+4) (sol : v_l 1 n=1) : ∃ z : ℕ, n+4=4*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<4)
    (by decide : 4<11) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=0) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-2)) : ℤ) = 4*((((1*a)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=3) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-2)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-2) = 4*(((1)*(((((1*a)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=1) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=1) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-2) = 3*(((1)*(((((2*a + 1*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_11_5 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+5) (sol : v_l 1 n=1) : ∃ z : ℕ, n+5=5*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=5) (B:=1) (by decide : 0<5)
    (by decide : 5<11) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=3) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=12) (e:=7) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((2*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (3)*(((((2*a + 1*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (3)*(((((2*a + 1*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0)) + (1)*(((((1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*c)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_11_6 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+6) (sol : v_l 1 n=1) : ∃ z : ℕ, n+6=6*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=3) (by decide : 0<6)
    (by decide : 6<11) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=3) (z:=0) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) : ℤ) = 4*((((1*a + 3*b)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=3) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=12) (e:=7) (x:=1) (y:=1) (z:=1) (w:=2)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 3*b)/4 : ℕ):ℤ)-1)) + (3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((2)*(((((1*a + 3*b)/4 : ℕ):ℤ)-1)) + (3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 3*b)/4 : ℕ):ℤ)-1)) + (2)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=1) (z:=1) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*b + 1*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=1) (z:=1) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*b + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=4) (z:=3) (w:=5)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 4*b + 3*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 1*b + 1*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w31 : ((b:ℤ)-1) = 3*(((2)*(((((2*a + 1*b + 1*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*a + 1*b + 1*c)/3 : ℕ):ℤ)-0)) + (3)*(((((1*a + 4*b + 3*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a + 1*b + 1*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 4*b + 3*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_1, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_11_7 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+7) (sol : v_l 1 n=1) : ∃ z : ℕ, n+7=7*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=7) (B:=1) (by decide : 0<7)
    (by decide : 7<11) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=0) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) : ℤ) = 4*((((1*a)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=3) (y:=0) (z:=3) (w:=3)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((3)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((1)*(((((1*a)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a)/4 : ℕ):ℤ)-0)) + (3)*(((((3*a + 3*c)/4 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=16) (e:=4) (x:=5) (y:=0) (z:=3) (w:=5)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((5)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 9*((((5*a + 3*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((6)*(((((5*a + 3*c)/9 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0)) + (6)*(((((5*a + 3*c)/9 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_11_8 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+8) (sol : v_l 1 n=1) : ∃ z : ℕ, n+8=8*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<8)
    (by decide : 8<11) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=0) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-3)) : ℤ) = 4*((((1*a)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=3) (w:=3)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-3)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-3) = 4*(((1)*(((((1*a)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-3)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=1) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-2) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=1) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-3) = 3*(((1)*(((((2*a + 1*c)/3 : ℕ):ℤ)-2)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-2)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=3 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=3) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_11_9 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+9) (sol : v_l 1 n=1) : ∃ z : ℕ, n+9=9*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=1) (by decide : 0<9)
    (by decide : 9<11) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=0) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-2)) : ℤ) = 4*((((3*a)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=0) (z:=3) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-2) = 4*(((3)*(((((3*a)/4 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-2)))) := by
    linarith only [h2_0]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((3*c)/4 : ℕ):ℤ)-0))) - ((2)*(((c:ℤ)-0)))) := by
    linarith only [h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=1) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=4) (y:=0) (z:=3) (w:=8)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((4)*(((a:ℤ)-2)) + (3)*(((c:ℤ)-0)) : ℤ) = 9*((((4*a + 3*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-2) = 3*(((3)*(((((4*a + 3*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0)) + (6)*(((((4*a + 3*c)/9 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_11_10 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+10) (sol : v_l 1 n=1) : ∃ z : ℕ, n+10=10*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=5) (by decide : 0<10)
    (by decide : 10<11) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=1) (z:=3) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*b + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=5) (z:=7) (w:=3)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (7)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 5*b + 7*c)/16 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=12) (e:=7) (x:=1) (y:=2) (z:=1) (w:=3)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*b + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 1*b + 3*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 5*b + 7*c)/16 : ℕ):ℤ)-1))) - ((4)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w41 : ((b:ℤ)-1) = 4*(((1)*(((((1*a + 1*b + 3*c)/4 : ℕ):ℤ)-0)) + (8)*(((((14*a + 5*b + 7*c)/16 : ℕ):ℤ)-1)) + (3)*(((((1*a + 2*b + 1*c)/4 : ℕ):ℤ)-0))) - ((8)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (5)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 1*b + 3*c)/4 : ℕ):ℤ)-0)) + (12)*(((((14*a + 5*b + 7*c)/16 : ℕ):ℤ)-1)) + (3)*(((((1*a + 2*b + 1*c)/4 : ℕ):ℤ)-0))) - ((12)*(((a:ℤ)-1)) + (6)*(((b:ℤ)-1)) + (8)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=2) (z:=1) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*b + 1*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=7) (z:=3) (w:=8)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((a:ℤ)-1)) + (7)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 7*b + 3*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((2*a + 2*b + 1*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 7*b + 3*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (6)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((1)*(((((2*a + 2*b + 1*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 7*b + 3*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((2*a + 2*b + 1*c)/3 : ℕ):ℤ)-1)) + (3)*(((((1*a + 7*b + 3*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

theorem shape_11 {n k : ℕ} (hk : 0<k) (kq : k<11) (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠11 → r∣n)
    (dq : 11∣n+k) (sol : v_l 1 n=1) : ∃ z : ℕ, n+k=k*z^12 := by
  have cases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact shape_11_1 sole dq sol
  · exact shape_11_2 sole dq sol
  · exact shape_11_3 sole dq sol
  · exact shape_11_4 sole dq sol
  · exact shape_11_5 sole dq sol
  · exact shape_11_6 sole dq sol
  · exact shape_11_7 sole dq sol
  · exact shape_11_8 sole dq sol
  · exact shape_11_9 sole dq sol
  · exact shape_11_10 sole dq sol

private theorem shape_13_1 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+1) (sol : v_l 1 n=1) : ∃ z : ℕ, n+1=1*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=1) (B:=1) (by decide : 0<1)
    (by decide : 1<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=0) (y:=0) (z:=3) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((3*c)/4 : ℕ):ℤ)-0))) - ((2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0]
  have row3_0 := row (d:=9) (G:=4) (e:=2) (x:=0) (y:=0) (z:=5) (w:=0)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((5)*(((c:ℤ)-0)) : ℤ) = 9*((((5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have w32 : ((c:ℤ)-0) = 3*(((6)*(((((5*c)/9 : ℕ):ℤ)-0))) - ((3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0]
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=0) (j:=0) shape (by decide)
    (by simp) (by simp) rem2

private theorem shape_13_2 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+2) (sol : v_l 1 n=1) : ∃ z : ℕ, n+2=2*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<2)
    (by decide : 2<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=3) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=0) (z:=4) (w:=14)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 4*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((2)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (2)*(((((14*a + 4*c)/16 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (2)*(((((14*a + 4*c)/16 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=0) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) : ℤ) = 3*((((2*a)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=0) (z:=5) (w:=1)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((2*a)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)))) := by
    linarith only [h3_0]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 5*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_13_3 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+3) (sol : v_l 1 n=1) : ∃ z : ℕ, n+3=3*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=1) (by decide : 0<3)
    (by decide : 3<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=3) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=1) (y:=0) (z:=4) (w:=1)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((1*a + 4*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((4)*(((((1*a + 4*c)/16 : ℕ):ℤ)-0))) - ((1)*(((c:ℤ)-0)))) := by
    linarith only [h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((3*a + 3*c)/4 : ℕ):ℤ)-0)) + (12)*(((((1*a + 4*c)/16 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=0) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) : ℤ) = 3*((((1*a)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=4) (y:=0) (z:=5) (w:=4)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((4)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((4*a + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((1*a)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_0]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a)/3 : ℕ):ℤ)-0)) + (6)*(((((4*a + 5*c)/9 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_13_4 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+4) (sol : v_l 1 n=1) : ∃ z : ℕ, n+4=4*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<4)
    (by decide : 4<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=3) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-2)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=0) (z:=4) (w:=12)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-2)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 4*c)/16 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-2) = 4*(((2)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (2)*(((((14*a + 4*c)/16 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (2)*(((((14*a + 4*c)/16 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=0) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-2)) : ℤ) = 3*((((2*a)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=0) (z:=5) (w:=2)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-2) = 3*(((2)*(((((2*a)/3 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-2)))) := by
    linarith only [h3_0]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 5*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-2)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_13_5 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+5) (sol : v_l 1 n=1) : ∃ z : ℕ, n+5=5*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=5) (B:=1) (by decide : 0<5)
    (by decide : 5<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=16) (G:=3) (e:=1) (x:=5) (y:=0) (z:=4) (w:=5)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((5)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((5*a + 4*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=31) (e:=9) (x:=3) (y:=0) (z:=3) (w:=3)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((3)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((4)*(((((5*a + 4*c)/16 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0]
  have w42 : ((c:ℤ)-0) = 4*(((12)*(((((5*a + 4*c)/16 : ℕ):ℤ)-0)) + (3)*(((((3*a + 3*c)/4 : ℕ):ℤ)-0))) - ((6)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=0) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) : ℤ) = 3*((((2*a)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=7) (y:=0) (z:=5) (w:=7)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((7)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((7*a + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((2*a)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)))) := by
    linarith only [h3_0]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a)/3 : ℕ):ℤ)-0)) + (6)*(((((7*a + 5*c)/9 : ℕ):ℤ)-0))) - ((6)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_13_6 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+6) (sol : v_l 1 n=1) : ∃ z : ℕ, n+6=6*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=3) (by decide : 0<6)
    (by decide : 6<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=3) (z:=3) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=1) (z:=4) (w:=15)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 1*b + 4*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=12) (e:=7) (x:=1) (y:=1) (z:=2) (w:=2)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((2)*(((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1)) + (4)*(((((14*a + 1*b + 4*c)/16 : ℕ):ℤ)-0)) + (1)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((12)*(((((14*a + 1*b + 4*c)/16 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0))) - ((11)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1)) + (8)*(((((14*a + 1*b + 4*c)/16 : ℕ):ℤ)-0)) + (3)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0))) - ((8)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=1) (z:=0) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) : ℤ) = 3*((((2*a + 1*b)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=4) (z:=5) (w:=5)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 4*b + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=3) (G:=25) (e:=10) (x:=0) (y:=1) (z:=2) (w:=1)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*b + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((3)*(((((1*a + 4*b + 5*c)/9 : ℕ):ℤ)-0)) + (2)*(((((1*b + 2*c)/3 : ℕ):ℤ)-0))) - ((2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_1, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((1)*(((((2*a + 1*b)/3 : ℕ):ℤ)-1)) + (3)*(((((1*a + 4*b + 5*c)/9 : ℕ):ℤ)-0)) + (2)*(((((1*b + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((2*a + 1*b)/3 : ℕ):ℤ)-1)) + (3)*(((((1*a + 4*b + 5*c)/9 : ℕ):ℤ)-0)) + (1)*(((((1*b + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_13_7 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+7) (sol : v_l 1 n=1) : ∃ z : ℕ, n+7=7*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=7) (B:=1) (by decide : 0<7)
    (by decide : 7<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=3) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=11) (y:=0) (z:=4) (w:=11)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((11)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((11*a + 4*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((12)*(((((11*a + 4*c)/16 : ℕ):ℤ)-0))) - ((8)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (12)*(((((11*a + 4*c)/16 : ℕ):ℤ)-0))) - ((9)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=9) (G:=4) (e:=2) (x:=6) (y:=0) (z:=5) (w:=6)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((6)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((6*a + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=25) (e:=10) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((6)*(((((6*a + 5*c)/9 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((6)*(((((6*a + 5*c)/9 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_13_8 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+8) (sol : v_l 1 n=1) : ∃ z : ℕ, n+8=8*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<8)
    (by decide : 8<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=3) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-3)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=0) (z:=4) (w:=10)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-3)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 4*c)/16 : ℕ):ℤ)-2) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-3) = 4*(((2)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (2)*(((((14*a + 4*c)/16 : ℕ):ℤ)-2))) - ((2)*(((a:ℤ)-3)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 3*c)/4 : ℕ):ℤ)-0)) + (2)*(((((14*a + 4*c)/16 : ℕ):ℤ)-2))) - ((2)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=0) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-3)) : ℤ) = 3*((((2*a)/3 : ℕ):ℤ)-2) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=0) (z:=5) (w:=3)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-3)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-3) = 3*(((2)*(((((2*a)/3 : ℕ):ℤ)-2))) - ((1)*(((a:ℤ)-3)))) := by
    linarith only [h3_0]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a)/3 : ℕ):ℤ)-2)) + (6)*(((((1*a + 5*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-3)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=3 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=3) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_13_9 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+9) (sol : v_l 1 n=1) : ∃ z : ℕ, n+9=9*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=1) (by decide : 0<9)
    (by decide : 9<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=3) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-2)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 3*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=1) (y:=0) (z:=4) (w:=2)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-2)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((1*a + 4*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-2) = 4*(((4)*(((((1*a + 4*c)/16 : ℕ):ℤ)-0))) - ((1)*(((c:ℤ)-0)))) := by
    linarith only [h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((3*a + 3*c)/4 : ℕ):ℤ)-1)) + (12)*(((((1*a + 4*c)/16 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-2)) + (5)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=0) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-2)) : ℤ) = 3*((((1*a)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=4) (y:=0) (z:=5) (w:=8)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((4)*(((a:ℤ)-2)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((4*a + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-2) = 3*(((1)*(((((1*a)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_0]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a)/3 : ℕ):ℤ)-0)) + (6)*(((((4*a + 5*c)/9 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-2)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_13_10 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+10) (sol : v_l 1 n=1) : ∃ z : ℕ, n+10=10*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=5) (by decide : 0<10)
    (by decide : 10<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=5) (z:=4) (w:=3)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((14)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 5*b + 4*c)/16 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=12) (e:=7) (x:=1) (y:=2) (z:=2) (w:=3)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*b + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=31) (e:=9) (x:=1) (y:=3) (z:=3) (w:=0)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 2*b + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((4)*(((((14*a + 5*b + 4*c)/16 : ℕ):ℤ)-1)) + (2)*(((((1*a + 2*b + 2*c)/4 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((12)*(((((14*a + 5*b + 4*c)/16 : ℕ):ℤ)-1)) + (1)*(((((1*a + 2*b + 2*c)/4 : ℕ):ℤ)-0)) + (1)*(((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1))) - ((11)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=2) (z:=0) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) : ℤ) = 3*((((2*a + 2*b)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=7) (z:=5) (w:=8)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (7)*(((b:ℤ)-1)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 7*b + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=3) (G:=25) (e:=10) (x:=0) (y:=2) (z:=2) (w:=2)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*b + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 2*b)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 7*b + 5*c)/9 : ℕ):ℤ)-0)) + (1)*(((((2*b + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (6)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((1)*(((((2*a + 2*b)/3 : ℕ):ℤ)-1)) + (3)*(((((1*a + 7*b + 5*c)/9 : ℕ):ℤ)-0)) + (2)*(((((2*b + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 2*b)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 7*b + 5*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (6)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_13_11 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+11) (sol : v_l 1 n=1) : ∃ z : ℕ, n+11=11*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=11) (B:=1) (by decide : 0<11)
    (by decide : 11<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=0) (y:=0) (z:=3) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((c:ℤ)-0)) : ℤ) = 4*((((3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=7) (y:=0) (z:=4) (w:=7)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((7)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((7*a + 4*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((12)*(((((7*a + 4*c)/16 : ℕ):ℤ)-0))) - ((5)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((3*c)/4 : ℕ):ℤ)-0))) - ((2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=0) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) : ℤ) = 3*((((1*a)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=3) (y:=0) (z:=5) (w:=3)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((3)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((3*a + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((1*a)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_0]
  have w32 : ((c:ℤ)-0) = 3*(((6)*(((((3*a + 5*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_13_12 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+12) (sol : v_l 1 n=1) : ∃ z : ℕ, n+12=12*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=3) (by decide : 0<12)
    (by decide : 12<13) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=3) (z:=3) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-2)) + (3)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=1) (z:=4) (w:=13)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 1*b + 4*c)/16 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=12) (e:=7) (x:=1) (y:=1) (z:=2) (w:=3)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((1)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-2) = 4*(((2)*(((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1)) + (4)*(((((14*a + 1*b + 4*c)/16 : ℕ):ℤ)-1)) + (1)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-2)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((12)*(((((14*a + 1*b + 4*c)/16 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0))) - ((11)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1)) + (8)*(((((14*a + 1*b + 4*c)/16 : ℕ):ℤ)-1)) + (3)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0))) - ((8)*(((a:ℤ)-2)) + (2)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=1) (z:=0) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) : ℤ) = 3*((((2*a + 1*b)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=4) (z:=5) (w:=6)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) + (4)*(((b:ℤ)-1)) + (5)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 4*b + 5*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=3) (G:=25) (e:=10) (x:=0) (y:=1) (z:=2) (w:=1)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*b + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-2) = 3*(((3)*(((((1*a + 4*b + 5*c)/9 : ℕ):ℤ)-0)) + (2)*(((((1*b + 2*c)/3 : ℕ):ℤ)-0))) - ((2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_1, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((1)*(((((2*a + 1*b)/3 : ℕ):ℤ)-1)) + (3)*(((((1*a + 4*b + 5*c)/9 : ℕ):ℤ)-0)) + (2)*(((((1*b + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((2*a + 1*b)/3 : ℕ):ℤ)-1)) + (3)*(((((1*a + 4*b + 5*c)/9 : ℕ):ℤ)-0)) + (1)*(((((1*b + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

theorem shape_13 {n k : ℕ} (hk : 0<k) (kq : k<13) (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠13 → r∣n)
    (dq : 13∣n+k) (sol : v_l 1 n=1) : ∃ z : ℕ, n+k=k*z^12 := by
  have cases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact shape_13_1 sole dq sol
  · exact shape_13_2 sole dq sol
  · exact shape_13_3 sole dq sol
  · exact shape_13_4 sole dq sol
  · exact shape_13_5 sole dq sol
  · exact shape_13_6 sole dq sol
  · exact shape_13_7 sole dq sol
  · exact shape_13_8 sole dq sol
  · exact shape_13_9 sole dq sol
  · exact shape_13_10 sole dq sol
  · exact shape_13_11 sole dq sol
  · exact shape_13_12 sole dq sol

private theorem shape_17_1 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+1) (sol : v_l 1 n=1) : ∃ z : ℕ, n+1=1*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=1) (B:=1) (by decide : 0<1)
    (by decide : 1<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*c)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*c)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_0]
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=0) (j:=0) shape (by decide)
    (by simp) (by simp) rem2

private theorem shape_17_2 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+2) (sol : v_l 1 n=1) : ∃ z : ℕ, n+2=2*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<2)
    (by decide : 2<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 1*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 1*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 1*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_17_3 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+3) (sol : v_l 1 n=1) : ∃ z : ℕ, n+3=3*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=1) (by decide : 0<3)
    (by decide : 3<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=1) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=31) (e:=9) (x:=2) (y:=0) (z:=3) (w:=2)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((2)*(((a:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((2*a + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((1)*(((((3*a + 1*c)/4 : ℕ):ℤ)-0)) + (1)*(((((2*a + 3*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((3*a + 1*c)/4 : ℕ):ℤ)-0)) + (1)*(((((2*a + 3*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_17_4 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+4) (sol : v_l 1 n=1) : ∃ z : ℕ, n+4=4*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<4)
    (by decide : 4<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=1) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-2) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=1) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=0) (z:=1) (w:=2)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 1*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-2) = 3*(((1)*(((((2*a + 1*c)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 1*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 1*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_17_5 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+5) (sol : v_l 1 n=1) : ∃ z : ℕ, n+5=5*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=5) (B:=1) (by decide : 0<5)
    (by decide : 5<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=12) (e:=7) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((2*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((1)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((2*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (1)*(((((2*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=0) (y:=0) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0)) + (2)*(((((2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_17_6 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+6) (sol : v_l 1 n=1) : ∃ z : ℕ, n+6=6*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=3) (by decide : 0<6)
    (by decide : 6<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=3) (z:=1) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=31) (e:=9) (x:=1) (y:=2) (z:=3) (w:=3)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*b + 3*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((1*a + 2*b + 3*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((1)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1)) + (2)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*b + 3*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1)) + (3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 2*b + 3*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=1) (z:=1) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*b + 1*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=1) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=4) (z:=1) (w:=5)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 4*b + 1*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 1*b + 1*c)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 4*b + 1*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((2)*(((((2*a + 1*b + 1*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 4*b + 1*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_1, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_17_7 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+7) (sol : v_l 1 n=1) : ∃ z : ℕ, n+7=7*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=7) (B:=1) (by decide : 0<7)
    (by decide : 7<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=3) (y:=0) (z:=2) (w:=3)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((3)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (1)*(((((3*a + 2*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((3*a + 2*c)/4 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=2) (y:=0) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=6) (y:=0) (z:=1) (w:=6)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((6)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((6*a + 1*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((2*a + 2*c)/3 : ℕ):ℤ)-0)) + (6)*(((((6*a + 1*c)/9 : ℕ):ℤ)-0))) - ((5)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((3)*(((((6*a + 1*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)))) := by
    linarith only [h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_17_8 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+8) (sol : v_l 1 n=1) : ∃ z : ℕ, n+8=8*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<8)
    (by decide : 8<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=1) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=2) (w:=3)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-3)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-3) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-3)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=1) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-2) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=0) (z:=1) (w:=3)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 1*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-3) = 3*(((1)*(((((2*a + 1*c)/3 : ℕ):ℤ)-2)) + (6)*(((((1*a + 1*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-2)) + (6)*(((((1*a + 1*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=3 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=3) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_17_9 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+9) (sol : v_l 1 n=1) : ∃ z : ℕ, n+9=9*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=1) (by decide : 0<9)
    (by decide : 9<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=1) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 1*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=31) (e:=9) (x:=2) (y:=0) (z:=3) (w:=0)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((2)*(((a:ℤ)-2)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((2*a + 3*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-2) = 4*(((1)*(((((3*a + 1*c)/4 : ℕ):ℤ)-1)) + (1)*(((((2*a + 3*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((3*a + 1*c)/4 : ℕ):ℤ)-1)) + (1)*(((((2*a + 3*c)/4 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=1) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-2) = 3*(((2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_17_10 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+10) (sol : v_l 1 n=1) : ∃ z : ℕ, n+10=10*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=5) (by decide : 0<10)
    (by decide : 10<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=1) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=12) (e:=7) (x:=1) (y:=2) (z:=1) (w:=3)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*b + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=31) (e:=9) (x:=1) (y:=3) (z:=3) (w:=0)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((1)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*b + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((2)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 2*b + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((1*a + 2*b + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 3*b + 3*c)/4 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=2) (z:=1) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*b + 1*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=7) (z:=1) (w:=8)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((a:ℤ)-1)) + (7)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 7*b + 1*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((2*a + 2*b + 1*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 7*b + 1*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (6)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((2)*(((((2*a + 2*b + 1*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 2*b + 1*c)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 7*b + 1*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (6)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_17_11 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+11) (sol : v_l 1 n=1) : ∃ z : ℕ, n+11=11*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=11) (B:=1) (by decide : 0<11)
    (by decide : 11<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=3) (y:=0) (z:=2) (w:=3)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((3)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((2)*(((((1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((3*a + 2*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*c)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_17_12 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+12) (sol : v_l 1 n=1) : ∃ z : ℕ, n+12=12*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=3) (by decide : 0<12)
    (by decide : 12<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=3) (z:=1) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-2)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=31) (e:=9) (x:=1) (y:=2) (z:=3) (w:=0)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((1)*(((a:ℤ)-2)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*b + 3*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-2) = 4*(((3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((1*a + 2*b + 3*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((1)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1)) + (2)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*b + 3*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1)) + (3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 2*b + 3*c)/4 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-2)) + (3)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=1) (z:=1) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*b + 1*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=1) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=4) (z:=1) (w:=6)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((a:ℤ)-2)) + (4)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 4*b + 1*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-2) = 3*(((1)*(((((2*a + 1*b + 1*c)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 4*b + 1*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((2)*(((((2*a + 1*b + 1*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 4*b + 1*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_1, h3_2]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_17_13 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+13) (sol : v_l 1 n=1) : ∃ z : ℕ, n+13=13*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=13) (B:=1) (by decide : 0<13)
    (by decide : 13<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=1) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=12) (e:=7) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((2*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((1)*(((((3*a + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((2*a + 1*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((3*a + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((2*a + 1*c)/4 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=5) (y:=0) (z:=1) (w:=5)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((5)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((5*a + 1*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((1*c)/3 : ℕ):ℤ)-0)) + (6)*(((((5*a + 1*c)/9 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*c)/3 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h3_0]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_17_14 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+14) (sol : v_l 1 n=1) : ∃ z : ℕ, n+14=14*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=7) (by decide : 0<14)
    (by decide : 14<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=1) (z:=1) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=3) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=12) (e:=7) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1)) + (3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((1)*(((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0)) + (1)*(((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=2) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*b + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=6) (z:=1) (w:=7)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (6)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 6*b + 1*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=3) (G:=25) (e:=10) (x:=0) (y:=1) (z:=1) (w:=1)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*b + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((1*a + 2*b + 2*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((1)*(((((1*a + 2*b + 2*c)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 6*b + 1*c)/9 : ℕ):ℤ)-0)) + (2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((1*a + 2*b + 2*c)/3 : ℕ):ℤ)-1)) + (3)*(((((1*a + 6*b + 1*c)/9 : ℕ):ℤ)-0)) + (2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_17_15 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+15) (sol : v_l 1 n=1) : ∃ z : ℕ, n+15=15*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=5) (by decide : 0<15)
    (by decide : 15<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=1) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*b + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=12) (e:=7) (x:=1) (y:=2) (z:=1) (w:=3)
    shape (sole 29 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*b + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=31) (e:=9) (x:=2) (y:=3) (z:=3) (w:=1)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((2)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)) : ℤ) = 4*((((2*a + 3*b + 3*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*b + 2*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 2*b + 1*c)/4 : ℕ):ℤ)-0)) + (1)*(((((2*a + 3*b + 3*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((3)*(((((1*b + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((2*a + 3*b + 3*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*b + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((1*a + 2*b + 1*c)/4 : ℕ):ℤ)-0)) + (3)*(((((2*a + 3*b + 3*c)/4 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=2) (z:=1) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*b + 1*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=9) (G:=4) (e:=2) (x:=4) (y:=7) (z:=1) (w:=2)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((4)*(((a:ℤ)-1)) + (7)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((4*a + 7*b + 1*c)/9 : ℕ):ℤ)-1) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((1*a + 2*b + 1*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (3)*(((((4*a + 7*b + 1*c)/9 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((1)*(((((1*a + 2*b + 1*c)/3 : ℕ):ℤ)-1)) + (6)*(((((4*a + 7*b + 1*c)/9 : ℕ):ℤ)-1))) - ((3)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a + 2*b + 1*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (3)*(((((4*a + 7*b + 1*c)/9 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_17_16 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+16) (sol : v_l 1 n=1) : ∃ z : ℕ, n+16=16*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<16)
    (by decide : 16<17) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=1) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-4)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-4)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-4) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-1)) + (3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-4)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-1)) + (1)*(((((1*a + 2*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-4)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-4)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-2) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=4) (e:=2) (x:=1) (y:=0) (z:=1) (w:=4)
    shape (sole 19 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-4)) + (1)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 1*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-4) = 3*(((1)*(((((2*a + 1*c)/3 : ℕ):ℤ)-2)) + (6)*(((((1*a + 1*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-4)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-2)) + (6)*(((((1*a + 1*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-4)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=4 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=4) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

theorem shape_17 {n k : ℕ} (hk : 0<k) (kq : k<17) (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠17 → r∣n)
    (dq : 17∣n+k) (sol : v_l 1 n=1) : ∃ z : ℕ, n+k=k*z^12 := by
  have cases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 ∨ k=16 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact shape_17_1 sole dq sol
  · exact shape_17_2 sole dq sol
  · exact shape_17_3 sole dq sol
  · exact shape_17_4 sole dq sol
  · exact shape_17_5 sole dq sol
  · exact shape_17_6 sole dq sol
  · exact shape_17_7 sole dq sol
  · exact shape_17_8 sole dq sol
  · exact shape_17_9 sole dq sol
  · exact shape_17_10 sole dq sol
  · exact shape_17_11 sole dq sol
  · exact shape_17_12 sole dq sol
  · exact shape_17_13 sole dq sol
  · exact shape_17_14 sole dq sol
  · exact shape_17_15 sole dq sol
  · exact shape_17_16 sole dq sol

private theorem shape_19_1 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+1) (sol : v_l 1 n=1) : ∃ z : ℕ, n+1=1*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=1) (B:=1) (by decide : 0<1)
    (by decide : 1<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*c)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_0]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=0) (y:=0) (z:=2) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0]
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=0) (j:=0) shape (by decide)
    (by simp) (by simp) rem2

private theorem shape_19_2 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+2) (sol : v_l 1 n=1) : ∃ z : ℕ, n+2=2*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<2)
    (by decide : 2<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=2) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-0)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_3 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+3) (sol : v_l 1 n=1) : ∃ z : ℕ, n+3=3*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=1) (by decide : 0<3)
    (by decide : 3<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=2) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((3*a + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((1*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*c)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=25) (e:=10) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_4 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+4) (sol : v_l 1 n=1) : ∃ z : ℕ, n+4=4*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<4)
    (by decide : 4<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=2) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=1) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-2) = 4*(((3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=2) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-2) = 3*(((1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_5 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+5) (sol : v_l 1 n=1) : ∃ z : ℕ, n+5=5*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=5) (B:=1) (by decide : 0<5)
    (by decide : 5<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=5) (y:=0) (z:=14) (w:=5)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((5)*(((a:ℤ)-1)) + (14)*(((c:ℤ)-0)) : ℤ) = 16*((((5*a + 14*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (12)*(((((5*a + 14*c)/16 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (11)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((5*a + 14*c)/16 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=2) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=0) (y:=0) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((2*a + 2*c)/3 : ℕ):ℤ)-0)) + (1)*(((((2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_6 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+6) (sol : v_l 1 n=1) : ∃ z : ℕ, n+6=6*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=3) (by decide : 0<6)
    (by decide : 6<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=3) (z:=2) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=1) (z:=14) (w:=15)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((14)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (14)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1)) + (12)*(((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-0))) - ((11)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (12)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1)) + (1)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=1) (z:=2) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=1) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=3) (G:=25) (e:=10) (x:=0) (y:=1) (z:=1) (w:=1)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*b + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w31 : ((b:ℤ)-1) = 3*(((1)*(((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_19_7 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+7) (sol : v_l 1 n=1) : ∃ z : ℕ, n+7=7*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=7) (B:=1) (by decide : 0<7)
    (by decide : 7<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=3) (y:=0) (z:=1) (w:=3)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((3)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((3*a + 1*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (3)*(((((3*a + 1*c)/4 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=2) (y:=0) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=36) (e:=14) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 43 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-0)) + (1)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_8 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+8) (sol : v_l 1 n=1) : ∃ z : ℕ, n+8=8*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<8)
    (by decide : 8<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=2) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-3)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=1) (w:=3)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-3) = 4*(((3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-3)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=2) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-3)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*c)/3 : ℕ):ℤ)-2) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-3)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-3) = 3*(((1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-2)) + (2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-3)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-2)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-3)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=3 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=3) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_9 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+9) (sol : v_l 1 n=1) : ∃ z : ℕ, n+9=9*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=1) (by decide : 0<9)
    (by decide : 9<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=2) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 2*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=0) (z:=1) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-2) = 4*(((3)*(((((3*a + 2*c)/4 : ℕ):ℤ)-1)) + (2)*(((((1*c)/4 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*c)/4 : ℕ):ℤ)-0))) - (0)) := by
    linarith only [h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=2) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=25) (e:=10) (x:=1) (y:=0) (z:=1) (w:=2)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-2) = 3*(((2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_10 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+10) (sol : v_l 1 n=1) : ∃ z : ℕ, n+10=10*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=5) (by decide : 0<10)
    (by decide : 10<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=1) (z:=1) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=5) (z:=14) (w:=3)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((14)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (14)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 5*b + 14*c)/16 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=8) (G:=27) (e:=5) (x:=2) (y:=6) (z:=1) (w:=0)
    shape (sole 41 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((2)*(((a:ℤ)-1)) + (6)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 8*((((2*a + 6*b + 1*c)/8 : ℕ):ℤ)-1) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((1)*(((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 5*b + 14*c)/16 : ℕ):ℤ)-1)) + (2)*(((((2*a + 6*b + 1*c)/8 : ℕ):ℤ)-1))) - ((4)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((2)*(((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0)) + (12)*(((((14*a + 5*b + 14*c)/16 : ℕ):ℤ)-1))) - ((11)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (11)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*a + 1*b + 1*c)/4 : ℕ):ℤ)-0)) + (6)*(((((2*a + 6*b + 1*c)/8 : ℕ):ℤ)-1))) - ((2)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=2) (z:=2) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*b + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=9) (G:=16) (e:=4) (x:=1) (y:=5) (z:=8) (w:=6)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (8)*(((c:ℤ)-0)) : ℤ) = 9*((((1*a + 5*b + 8*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 2*b + 2*c)/3 : ℕ):ℤ)-1)) + (6)*(((((1*a + 5*b + 8*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (6)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 5*b + 8*c)/9 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (6)*(((c:ℤ)-0)))) := by
    linarith only [h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((2*a + 2*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (6)*(((((1*a + 5*b + 8*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (7)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_19_11 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+11) (sol : v_l 1 n=1) : ∃ z : ℕ, n+11=11*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=11) (B:=1) (by decide : 0<11)
    (by decide : 11<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=3) (y:=0) (z:=1) (w:=3)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=7) (y:=0) (z:=14) (w:=7)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((7)*(((a:ℤ)-1)) + (14)*(((c:ℤ)-0)) : ℤ) = 16*((((7*a + 14*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((2)*(((((3*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((7*a + 14*c)/16 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((3)*(((((3*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((7*a + 14*c)/16 : ℕ):ℤ)-0))) - ((4)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=9) (G:=16) (e:=4) (x:=3) (y:=0) (z:=8) (w:=3)
    shape (sole 37 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((3)*(((a:ℤ)-1)) + (8)*(((c:ℤ)-0)) : ℤ) = 9*((((3*a + 8*c)/9 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (6)*(((((3*a + 8*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (6)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((6)*(((((3*a + 8*c)/9 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)))) := by
    linarith only [h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_12 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+12) (sol : v_l 1 n=1) : ∃ z : ℕ, n+12=12*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=3) (by decide : 0<12)
    (by decide : 12<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=3) (z:=2) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-2)) + (3)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=1) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=1) (z:=14) (w:=13)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((14)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (14)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-1) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-2) = 4*(((3)*(((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1)) + (12)*(((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-1))) - ((11)*(((a:ℤ)-2)) + (3)*(((b:ℤ)-1)) + (12)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-1))) - ((4)*(((a:ℤ)-2)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1)) + (1)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-1))) - ((4)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=1) (z:=2) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=1) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=3) (G:=25) (e:=10) (x:=0) (y:=1) (z:=1) (w:=1)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*b + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-2) = 3*(((1)*(((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w31 : ((b:ℤ)-1) = 3*(((1)*(((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-2)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-2)) + (2)*(((b:ℤ)-1)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have rem0 : a%12=2 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=2) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_19_13 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+13) (sol : v_l 1 n=1) : ∃ z : ℕ, n+13=13*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=13) (B:=1) (by decide : 0<13)
    (by decide : 13<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=3) (y:=0) (z:=2) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((3)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((3*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=4) (y:=0) (z:=14) (w:=4)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((4)*(((a:ℤ)-1)) + (14)*(((c:ℤ)-0)) : ℤ) = 16*((((4*a + 14*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((3*a + 2*c)/4 : ℕ):ℤ)-0)) + (4)*(((((4*a + 14*c)/16 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (5)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((3*a + 2*c)/4 : ℕ):ℤ)-0)) + (6)*(((((4*a + 14*c)/16 : ℕ):ℤ)-0))) - ((3)*(((a:ℤ)-1)) + (6)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=0) (y:=0) (z:=2) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=25) (e:=10) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((2*a + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_14 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+14) (sol : v_l 1 n=1) : ∃ z : ℕ, n+14=14*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=7) (by decide : 0<14)
    (by decide : 14<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=1) (z:=2) (w:=2)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=3) (z:=1) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=11) (z:=14) (w:=9)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((14)*(((a:ℤ)-1)) + (11)*(((b:ℤ)-1)) + (14)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 11*b + 14*c)/16 : ℕ):ℤ)-1) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0)) + (12)*(((((14*a + 11*b + 14*c)/16 : ℕ):ℤ)-1))) - ((11)*(((a:ℤ)-1)) + (9)*(((b:ℤ)-1)) + (12)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((2)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1)) + (4)*(((((14*a + 11*b + 14*c)/16 : ℕ):ℤ)-1))) - ((4)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 1*b + 2*c)/4 : ℕ):ℤ)-0)) + (3)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1)) + (8)*(((((14*a + 11*b + 14*c)/16 : ℕ):ℤ)-1))) - ((8)*(((a:ℤ)-1)) + (8)*(((b:ℤ)-1)) + (8)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=2) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*b + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=25) (e:=10) (x:=0) (y:=1) (z:=1) (w:=1)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*b + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=3) (G:=36) (e:=14) (x:=0) (y:=2) (z:=1) (w:=2)
    shape (sole 43 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((2)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((2*b + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((1*a + 2*b + 2*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w31 : ((b:ℤ)-1) = 3*(((2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0)) + (1)*(((((2*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0)) + (2)*(((((2*b + 1*c)/3 : ℕ):ℤ)-0))) - ((2)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_1, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_19_15 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+15) (sol : v_l 1 n=1) : ∃ z : ℕ, n+15=15*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=3) (B:=5) (by decide : 0<15)
    (by decide : 15<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=8) (e:=3) (x:=0) (y:=1) (z:=1) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*b + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=16) (G:=3) (e:=1) (x:=1) (y:=5) (z:=14) (w:=6)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (14)*(((c:ℤ)-0)) : ℤ) = 16*((((1*a + 5*b + 14*c)/16 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=4) (G:=30) (e:=13) (x:=1) (y:=3) (z:=1) (w:=0)
    shape (sole 53 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((1)*(((((1*b + 1*c)/4 : ℕ):ℤ)-0)) + (8)*(((((1*a + 5*b + 14*c)/16 : ℕ):ℤ)-0)) + (3)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (8)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w41 : ((b:ℤ)-1) = 4*(((3)*(((((1*b + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((1*a + 5*b + 14*c)/16 : ℕ):ℤ)-0)) + (3)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-1)) + (4)*(((b:ℤ)-1)) + (5)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*b + 1*c)/4 : ℕ):ℤ)-0)) + (12)*(((((1*a + 5*b + 14*c)/16 : ℕ):ℤ)-0)) + (1)*(((((1*a + 3*b + 1*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-1)) + (5)*(((b:ℤ)-1)) + (11)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=2) (z:=2) (w:=0)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*b + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=3) (G:=25) (e:=10) (x:=1) (y:=2) (z:=1) (w:=0)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*b + 1*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((1*a + 2*b + 2*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (2)*(((((1*a + 2*b + 1*c)/3 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w31 : ((b:ℤ)-1) = 3*(((2)*(((((1*a + 2*b + 2*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a + 2*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 2*b + 1*c)/3 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=1 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=1) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

private theorem shape_19_16 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+16) (sol : v_l 1 n=1) : ∃ z : ℕ, n+16=16*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=1) (by decide : 0<16)
    (by decide : 16<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=2) (w:=0)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-4)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=1) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-4)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-4) = 4*(((3)*(((((1*a + 2*c)/4 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-4)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 2*c)/4 : ℕ):ℤ)-1)) + (3)*(((((1*a + 1*c)/4 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-4)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=0) (z:=2) (w:=2)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-4)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*c)/3 : ℕ):ℤ)-2) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-4)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-4) = 3*(((1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-2)) + (2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-4)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-2)) + (1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-4)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=4 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=4) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_17 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+17) (sol : v_l 1 n=1) : ∃ z : ℕ, n+17=17*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=17) (B:=1) (by decide : 0<17)
    (by decide : 17<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 2*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=2) (y:=0) (z:=1) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((2)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((2*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have w40 : ((a:ℤ)-1) = 4*(((1)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (2)*(((((2*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have w42 : ((c:ℤ)-0) = 4*(((2)*(((((1*a + 2*c)/4 : ℕ):ℤ)-0)) + (1)*(((((2*a + 1*c)/4 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=1) (y:=0) (z:=2) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=2) (y:=0) (z:=2) (w:=2)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((2)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 2*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_1
    omega
  have w30 : ((a:ℤ)-1) = 3*(((2)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w32 : ((c:ℤ)-0) = 3*(((1)*(((((1*a + 2*c)/3 : ℕ):ℤ)-0)) + (1)*(((((2*a + 2*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=0) shape (by decide)
    (by rw [rem0]) (by simp) rem2

private theorem shape_19_18 {n : ℕ} (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+18) (sol : v_l 1 n=1) : ∃ z : ℕ, n+18=18*z^12 := by
  obtain ⟨a,b,c,shape⟩ := supported (A:=2) (B:=3) (by decide : 0<18)
    (by decide : 18<19) (by decide) (by decide) dq sole (by decide) sol
  have row2_0 := row (d:=4) (G:=2) (e:=1) (x:=1) (y:=3) (z:=2) (w:=3)
    shape (sole 5 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_0 : ((1)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1) := by
    clear * - row2_0
    omega
  have row2_1 := row (d:=4) (G:=8) (e:=3) (x:=1) (y:=0) (z:=1) (w:=1)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_1 : ((1)*(((a:ℤ)-1)) + (1)*(((c:ℤ)-0)) : ℤ) = 4*((((1*a + 1*c)/4 : ℕ):ℤ)-0) := by
    clear * - row2_1
    omega
  have row2_2 := row (d:=16) (G:=3) (e:=1) (x:=14) (y:=1) (z:=14) (w:=0)
    shape (sole 17 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h2_2 : ((14)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-2)) + (14)*(((c:ℤ)-0)) : ℤ) = 16*((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-1) := by
    clear * - row2_2
    omega
  have w40 : ((a:ℤ)-1) = 4*(((3)*(((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1)) + (12)*(((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-1))) - ((11)*(((a:ℤ)-1)) + (3)*(((b:ℤ)-2)) + (12)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_2]
  have w41 : ((b:ℤ)-2) = 4*(((2)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-1))) - ((4)*(((a:ℤ)-1)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_1, h2_2]
  have w42 : ((c:ℤ)-0) = 4*(((1)*(((((1*a + 3*b + 2*c)/4 : ℕ):ℤ)-1)) + (1)*(((((1*a + 1*c)/4 : ℕ):ℤ)-0)) + (4)*(((((14*a + 1*b + 14*c)/16 : ℕ):ℤ)-1))) - ((4)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-2)) + (4)*(((c:ℤ)-0)))) := by
    linarith only [h2_0, h2_1, h2_2]
  have row3_0 := row (d:=3) (G:=2) (e:=2) (x:=2) (y:=1) (z:=2) (w:=1)
    shape (sole 7 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_0 : ((2)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_0
    omega
  have row3_1 := row (d:=3) (G:=3) (e:=4) (x:=1) (y:=1) (z:=2) (w:=0)
    shape (sole 13 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_1 : ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-2)) + (2)*(((c:ℤ)-0)) : ℤ) = 3*((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1) := by
    clear * - row3_1
    omega
  have row3_2 := row (d:=3) (G:=25) (e:=10) (x:=0) (y:=1) (z:=1) (w:=2)
    shape (sole 31 (by decide) (by decide) (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel)
  have h3_2 : ((1)*(((b:ℤ)-2)) + (1)*(((c:ℤ)-0)) : ℤ) = 3*((((1*b + 1*c)/3 : ℕ):ℤ)-0) := by
    clear * - row3_2
    omega
  have w30 : ((a:ℤ)-1) = 3*(((1)*(((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1))) - ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1]
  have w31 : ((b:ℤ)-2) = 3*(((1)*(((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (1)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((1)*(((a:ℤ)-1)) + (1)*(((b:ℤ)-2)) + (2)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have w32 : ((c:ℤ)-0) = 3*(((2)*(((((2*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*a + 1*b + 2*c)/3 : ℕ):ℤ)-1)) + (2)*(((((1*b + 1*c)/3 : ℕ):ℤ)-0))) - ((2)*(((a:ℤ)-1)) + (2)*(((b:ℤ)-2)) + (3)*(((c:ℤ)-0)))) := by
    linarith only [h3_0, h3_1, h3_2]
  have rem0 : a%12=1 := combine (by decide) w40 w30
  have rem1 : b%12=2 := combine (by decide) w41 w31
  have rem2 : c%12=0 := combine (by decide) w42 w32
  exact assemble (i:=1) (j:=2) shape (by decide)
    (by rw [rem0]) (by rw [rem1]) rem2

theorem shape_19 {n k : ℕ} (hk : 0<k) (kq : k<19) (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠19 → r∣n)
    (dq : 19∣n+k) (sol : v_l 1 n=1) : ∃ z : ℕ, n+k=k*z^12 := by
  have cases : k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 ∨ k=12 ∨ k=13 ∨ k=14 ∨ k=15 ∨ k=16 ∨ k=17 ∨ k=18 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact shape_19_1 sole dq sol
  · exact shape_19_2 sole dq sol
  · exact shape_19_3 sole dq sol
  · exact shape_19_4 sole dq sol
  · exact shape_19_5 sole dq sol
  · exact shape_19_6 sole dq sol
  · exact shape_19_7 sole dq sol
  · exact shape_19_8 sole dq sol
  · exact shape_19_9 sole dq sol
  · exact shape_19_10 sole dq sol
  · exact shape_19_11 sole dq sol
  · exact shape_19_12 sole dq sol
  · exact shape_19_13 sole dq sol
  · exact shape_19_14 sole dq sol
  · exact shape_19_15 sole dq sol
  · exact shape_19_16 sole dq sol
  · exact shape_19_17 sole dq sol
  · exact shape_19_18 sole dq sol


theorem exclude_nineteen {n k q : ℕ} (pos : 0<n) (hk : 0<k) (kq : k<q) (pq : q.Prime) (bound : q≤19)
    (sole : ∀ r : ℕ, r.Prime → r≤53 → r≠q → r∣n)
    (dq : q∣n+k) (sol : v_l 1 n=1) : False := by
  have table : ∀ p : Fin 20, p.val.Prime →
      p.val=2 ∨ p.val=3 ∨ p.val=5 ∨ p.val=7 ∨ p.val=11 ∨ p.val=13 ∨ p.val=17 ∨ p.val=19 := by decide
  have choices := table ⟨q,by omega⟩ pq
  change q=2 ∨ q=3 ∨ q=5 ∨ q=7 ∨ q=11 ∨ q=13 ∨ q=17 ∨ q=19 at choices
  obtain ⟨z,shape⟩ : ∃ z : ℕ, n+k=k*z^12 := by
    rcases choices with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact shape_2 hk kq sole dq sol
    · exact shape_3 hk kq sole dq sol
    · exact shape_5 hk kq sole dq sol
    · exact shape_7 hk kq sole dq sol
    · exact shape_11 hk kq sole dq sol
    · exact shape_13 hk kq sole dq sol
    · exact shape_17 hk kq sole dq sol
    · exact shape_19 hk kq sole dq sol
  have big : 1<z := by
    by_contra! low
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp low with h|h
    · simp [h] at shape; omega
    · simp [h] at shape; omega
  exact Erdos889.SoleMissing.no_twelfth hk (by omega) pq kq sole dq big shape sol

end Erdos889.SoleMissing.Ranks


/- Two missing small primes force a pair of nearby smooth numbers. -/

namespace Erdos889.SmoothGap
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem first_missing_offset {n p : ℕ} (pp : p.Prime) (miss : ¬p∣n)
    (sol : v_l 1 n=1) :
    ∃ k : ℕ, 0<k ∧ k<p ∧ p∣n+k ∧ ∀ r : ℕ, r.Prime → r∣n+k → r≤p := by
  let k := p-n%p
  have rem := Nat.mod_lt n pp.pos
  have nz : n%p≠0 := fun h => miss (Nat.dvd_of_mod_eq_zero h)
  have hk : 0<k := by dsimp only [k]; omega
  have small : k<p := by dsimp only [k]; omega
  have step : n%p+k=p := by dsimp only [k]; omega
  have dv : p∣n+k := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, Nat.mod_eq_of_lt small, step, Nat.mod_self]
  refine ⟨k,hk,small,dv,?_⟩
  intro r pr rd
  by_contra! high
  exact two_primes hk pp pr (by omega) small (by omega) dv rd sol

/-- A bound on pairs of 53-smooth numbers at distance at most 51 implies
that at most one prime up to 53 can be missing from a large solution. -/
theorem missing_prime_unique
    (smooth_pair : ∀ x y : ℕ, 0<x → x<y → y≤x+51 →
      (∀ r : ℕ, r.Prime → r∣x → r≤53) →
      (∀ r : ℕ, r.Prime → r∣y → r≤53) → x≤87697857812500)
    {n : ℕ} (big : 1000000000000000000<n) (sol : v_l 1 n=1)
    {p q : ℕ} (pp : p.Prime) (pq : q.Prime) (hp : p≤53) (hq : q≤53)
    (pm : ¬p∣n) (qm : ¬q∣n) : p=q := by
  obtain ⟨a,ap,al,da,sa⟩ := first_missing_offset pp pm sol
  obtain ⟨b,bp,bl,db,sb⟩ := first_missing_offset pq qm sol
  have sA (r : ℕ) (pr : r.Prime) (d : r∣n+a) := (sa r pr d).trans hp
  have sB (r : ℕ) (pr : r.Prime) (d : r∣n+b) := (sb r pr d).trans hq
  by_contra ne
  rcases lt_trichotomy a b with h|rfl|h
  · have := smooth_pair (n+a) (n+b) (by omega) (by omega) (by omega) sA sB
    omega
  · exact two_primes ap pp pq ne al bl da db sol
  · have := smooth_pair (n+b) (n+a) (by omega) (by omega) (by omega) sB sA
    omega

end Erdos889.SmoothGap

#print axioms Erdos889.SmoothGap.missing_prime_unique


namespace Erdos889.SmoothGap

/-- Conditional on the stated 53-smooth gap bound, every large exceptional integer
is divisible by the product of the primes through 19. -/
theorem primorial_nineteen
    (smooth_pair : ∀ x y : ℕ, 0<x → x<y → y≤x+51 →
      (∀ r : ℕ, r.Prime → r∣x → r≤53) →
      (∀ r : ℕ, r.Prime → r∣y → r≤53) → x≤87697857812500)
    {n : ℕ} (big : 1000000000000000000<n) (sol : v_l 1 n=1) : 9699690∣n := by
  have all (q : ℕ) (pq : q.Prime) (bound : q≤19) : q∣n := by
    by_contra missing
    have sole (r : ℕ) (pr : r.Prime) (small : r≤53) (ne : r≠q) : r∣n := by
      by_contra missing'
      exact ne (missing_prime_unique smooth_pair big sol pr pq small (by omega) missing' missing)
    obtain ⟨k,hk,hq,dq,_⟩ := first_missing_offset pq missing sol
    exact Erdos889.SoleMissing.Ranks.exclude_nineteen (by omega) hk hq pq bound sole dq sol
  have d2 := all 2 (by decide) (by decide)
  have d6 : 6∣n := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd d2 (all 3 (by decide) (by decide))
  have d30 : 30∣n := (by decide : Nat.Coprime 6 5).mul_dvd_of_dvd_of_dvd d6 (all 5 (by decide) (by decide))
  have d210 : 210∣n := (by decide : Nat.Coprime 30 7).mul_dvd_of_dvd_of_dvd d30 (all 7 (by decide) (by decide))
  have d2310 : 2310∣n := (by decide : Nat.Coprime 210 11).mul_dvd_of_dvd_of_dvd d210 (all 11 (by decide) (by decide))
  have d30030 : 30030∣n := (by decide : Nat.Coprime 2310 13).mul_dvd_of_dvd_of_dvd d2310 (all 13 (by decide) (by decide))
  have d510510 : 510510∣n := (by decide : Nat.Coprime 30030 17).mul_dvd_of_dvd_of_dvd d30030 (all 17 (by decide) (by decide))
  have d9699690 : 9699690∣n := (by decide : Nat.Coprime 510510 19).mul_dvd_of_dvd_of_dvd d510510 (all 19 (by decide) (by decide))
  exact d9699690

end Erdos889.SmoothGap
#print axioms Erdos889.SmoothGap.primorial_nineteen
