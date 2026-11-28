import E889SquareThirtySevenPell

/-! Determine the squarefree coefficient for each possible first offset at 37
and apply the corresponding Pell bound. -/

namespace Erdos889.SquareThirtySeven
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem extract {n j R : ℕ} (div : 802241960520∣n) (hj : 0<j) (lj : j≤36)
    (rad : ∀ p : Fin 37, p.val.Prime → p.val∣j → p.val∣R) (large : 37∣R)
    (pos : R≠0) (hit : 37∣n+j) (sol : v_l 1 n=1) :
    ∃ D y : ℕ, D∣R ∧ D*y^2=n+j ∧ (∀ p : ℕ, p.Prime → p∣y → p∣R) := by
  have sup (p : ℕ) (pp : p.Prime) (hd : p∣n+j) : p∣R := by
    by_cases small : p≤j
    · have t : ∀ t : Fin 37, t.val.Prime → t.val∣802241960520 := by decide
      have dp := (t ⟨p,by omega⟩ pp).trans div
      exact rad ⟨p,by omega⟩ pp ((Nat.dvd_add_iff_right dp).mpr hd)
    · by_cases same : p=37
      · exact same ▸ large
      exact False.elim (two_primes hj pp (by decide : Nat.Prime 37) same (by omega) (by omega) hd hit sol)
  obtain ⟨D,y,_,_,fac,free⟩ := Nat.sq_mul_squarefree_of_pos (show 0<n+j by omega)
  have dD : D∣n+j := fac ▸ dvd_mul_left _ _
  have dy : y∣n+j := fac ▸ dvd_mul_of_dvd_left (dvd_pow_self y (by decide : 2≠0)) _
  refine ⟨D,y,?_,by rwa [Nat.mul_comm],fun p pp h => sup p pp (h.trans dy)⟩
  rw [←Nat.prod_primeFactors_of_squarefree free,Nat.prod_primeFactors_dvd_iff pos]
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  exact pp.mem_primeFactors (sup p pp ((Nat.dvd_of_mem_primeFactors hp).trans dD)) pos

private theorem coefficient {D y n j m R wanted : ℕ} (fac : D*y^2=n+j) (dr : D∣R)
    (hr : 0 < R) (hm : 0 < m) (dv : m∣n)
    (check : ∀ d : Fin (R+1), d.val∣R → ∀ t : Fin m,
      (d.val*t.val^2)%m=j%m → d.val=wanted) : D=wanted := by
  have mod := ((Nat.mod_modEq y m).pow 2).mul_left D
  have eq : (D*(y%m)^2)%m=j%m := by
    calc
      _=(D*y^2)%m := mod
      _=(n+j)%m := congrArg (·%m) fac
      _=_ := by simp [Nat.add_mod,Nat.mod_eq_zero_of_dvd dv]
  exact check ⟨D,Nat.lt_succ_of_le (Nat.le_of_dvd hr dr)⟩ dr ⟨y%m,Nat.mod_lt _ hm⟩ eq

private theorem coord_bound {n p y D j : ℕ} (sol : v_l 1 n=1) (fac : D*y^2=n+j)
    (shape : n+1=p^2) (one : 2≤D) (small : j≤36) (big : 100<p) :
    y<2^2097152 := by
  have pbig : 10000<p^2 := by nlinarith
  have yp : y≤p := by
    by_contra! hi
    have yp := Nat.pow_le_pow_left hi.le 2
    have := Nat.mul_le_mul_right (y^2) one
    omega
  have high := Erdos889.effective_binary_cutoff sol
  rw [show (2:ℕ)^21=2097152 by decide] at high
  have cap : p^2≤2^2097152 := by rw [←shape]; exact Nat.succ_le_of_lt high
  exact lt_of_lt_of_le (show y<p^2 by nlinarith) cap

set_option maxRecDepth 8192 in
private theorem table2 : ∀ d : Fin (74+1), d.val∣74 → ∀ t : Fin 15,
    (d.val*t.val^2)%15=2%15 → d.val=2 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject2 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+2) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=2) (R:=74) div (by decide : 0<2) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=2 := coefficient (n:=n) (D:=D) (y:=y) (j:=2) (m:=15) (R:=74) (wanted:=2) fac dr (by decide) (by decide)
    ((show 15∣802241960520 from ⟨53482797368,rfl⟩).trans div) table2
  subst D
  have eqn : p^2+1=2*y^2 := by omega
  have h := smooth2 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=2) (j:=2) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table4 : ∀ d : Fin (74+1), d.val∣74 → ∀ t : Fin 15,
    (d.val*t.val^2)%15=4%15 → d.val=1 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject4 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+4) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=4) (R:=74) div (by decide : 0<4) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (n:=n) (D:=D) (y:=y) (j:=4) (m:=15) (R:=74) (wanted:=1) fac dr (by decide) (by decide)
    ((show 15∣802241960520 from ⟨53482797368,rfl⟩).trans div) table4
  subst D
  have eqn : y^2=p^2+3 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

set_option maxRecDepth 8192 in
private theorem table5 : ∀ d : Fin (185+1), d.val∣185 → ∀ t : Fin 24,
    (d.val*t.val^2)%24=5%24 → d.val=5 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject5 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+5) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=5) (R:=185) div (by decide : 0<5) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=5 := coefficient (n:=n) (D:=D) (y:=y) (j:=5) (m:=24) (R:=185) (wanted:=5) fac dr (by decide) (by decide)
    ((show 24∣802241960520 from ⟨33426748355,rfl⟩).trans div) table5
  subst D
  have eqn : p^2+4=5*y^2 := by omega
  have h := smooth5 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=5) (j:=5) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table8 : ∀ d : Fin (74+1), d.val∣74 → ∀ t : Fin 15,
    (d.val*t.val^2)%15=8%15 → d.val=2 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject8 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+8) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=8) (R:=74) div (by decide : 0<8) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=2 := coefficient (n:=n) (D:=D) (y:=y) (j:=8) (m:=15) (R:=74) (wanted:=2) fac dr (by decide) (by decide)
    ((show 15∣802241960520 from ⟨53482797368,rfl⟩).trans div) table8
  subst D
  have eqn : p^2+7=2*y^2 := by omega
  have h := smooth8 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=2) (j:=8) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table10 : ∀ d : Fin (370+1), d.val∣370 → ∀ t : Fin 156,
    (d.val*t.val^2)%156=10%156 → d.val=10 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject10 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+10) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=10) (R:=370) div (by decide : 0<10) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=10 := coefficient (n:=n) (D:=D) (y:=y) (j:=10) (m:=156) (R:=370) (wanted:=10) fac dr (by decide) (by decide)
    ((show 156∣802241960520 from ⟨5142576670,rfl⟩).trans div) table10
  subst D
  have eqn : p^2+9=10*y^2 := by omega
  have h := smooth10 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=10) (j:=10) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table11 : ∀ d : Fin (407+1), d.val∣407 → ∀ t : Fin 8,
    (d.val*t.val^2)%8=11%8 → d.val=11 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject11 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+11) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=11) (R:=407) div (by decide : 0<11) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=11 := coefficient (n:=n) (D:=D) (y:=y) (j:=11) (m:=8) (R:=407) (wanted:=11) fac dr (by decide) (by decide)
    ((show 8∣802241960520 from ⟨100280245065,rfl⟩).trans div) table11
  subst D
  have eqn : p^2+10=11*y^2 := by omega
  have h := smooth11 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=11) (j:=11) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table12 : ∀ d : Fin (222+1), d.val∣222 → ∀ t : Fin 280,
    (d.val*t.val^2)%280=12%280 → d.val=3 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject12 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+12) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=12) (R:=222) div (by decide : 0<12) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=3 := coefficient (n:=n) (D:=D) (y:=y) (j:=12) (m:=280) (R:=222) (wanted:=3) fac dr (by decide) (by decide)
    ((show 280∣802241960520 from ⟨2865149859,rfl⟩).trans div) table12
  subst D
  have eqn : p^2+11=3*y^2 := by omega
  have h := smooth12 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=3) (j:=12) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table13 : ∀ d : Fin (481+1), d.val∣481 → ∀ t : Fin 35,
    (d.val*t.val^2)%35=13%35 → d.val=13 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject13 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+13) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=13) (R:=481) div (by decide : 0<13) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=13 := coefficient (n:=n) (D:=D) (y:=y) (j:=13) (m:=35) (R:=481) (wanted:=13) fac dr (by decide) (by decide)
    ((show 35∣802241960520 from ⟨22921198872,rfl⟩).trans div) table13
  subst D
  have eqn : p^2+12=13*y^2 := by omega
  have h := smooth13 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=13) (j:=13) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table17 : ∀ d : Fin (629+1), d.val∣629 → ∀ t : Fin 15,
    (d.val*t.val^2)%15=17%15 → d.val=17 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject17 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+17) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=17) (R:=629) div (by decide : 0<17) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=17 := coefficient (n:=n) (D:=D) (y:=y) (j:=17) (m:=15) (R:=629) (wanted:=17) fac dr (by decide) (by decide)
    ((show 15∣802241960520 from ⟨53482797368,rfl⟩).trans div) table17
  subst D
  have eqn : p^2+16=17*y^2 := by omega
  have h := smooth17 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=17) (j:=17) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table22 : ∀ d : Fin (814+1), d.val∣814 → ∀ t : Fin 40,
    (d.val*t.val^2)%40=22%40 → d.val=22 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject22 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+22) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=22) (R:=814) div (by decide : 0<22) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=22 := coefficient (n:=n) (D:=D) (y:=y) (j:=22) (m:=40) (R:=814) (wanted:=22) fac dr (by decide) (by decide)
    ((show 40∣802241960520 from ⟨20056049013,rfl⟩).trans div) table22
  subst D
  have eqn : p^2+21=22*y^2 := by omega
  have h := smooth22 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=22) (j:=22) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table26 : ∀ d : Fin (962+1), d.val∣962 → ∀ t : Fin 105,
    (d.val*t.val^2)%105=26%105 → d.val=26 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject26 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+26) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=26) (R:=962) div (by decide : 0<26) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=26 := coefficient (n:=n) (D:=D) (y:=y) (j:=26) (m:=105) (R:=962) (wanted:=26) fac dr (by decide) (by decide)
    ((show 105∣802241960520 from ⟨7640399624,rfl⟩).trans div) table26
  subst D
  have eqn : p^2+25=26*y^2 := by omega
  have h := smooth26 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=26) (j:=26) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table27 : ∀ d : Fin (111+1), d.val∣111 → ∀ t : Fin 8,
    (d.val*t.val^2)%8=27%8 → d.val=3 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject27 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+27) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=27) (R:=111) div (by decide : 0<27) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=3 := coefficient (n:=n) (D:=D) (y:=y) (j:=27) (m:=8) (R:=111) (wanted:=3) fac dr (by decide) (by decide)
    ((show 8∣802241960520 from ⟨100280245065,rfl⟩).trans div) table27
  subst D
  have eqn : p^2+26=3*y^2 := by omega
  have h := smooth27 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=3) (j:=27) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table28 : ∀ d : Fin (518+1), d.val∣518 → ∀ t : Fin 165,
    (d.val*t.val^2)%165=28%165 → d.val=7 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject28 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+28) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=28) (R:=518) div (by decide : 0<28) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=7 := coefficient (n:=n) (D:=D) (y:=y) (j:=28) (m:=165) (R:=518) (wanted:=7) fac dr (by decide) (by decide)
    ((show 165∣802241960520 from ⟨4862072488,rfl⟩).trans div) table28
  subst D
  have eqn : p^2+27=7*y^2 := by omega
  have h := smooth28 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=7) (j:=28) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table29 : ∀ d : Fin (1073+1), d.val∣1073 → ∀ t : Fin 15,
    (d.val*t.val^2)%15=29%15 → d.val=29 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject29 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+29) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=29) (R:=1073) div (by decide : 0<29) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=29 := coefficient (n:=n) (D:=D) (y:=y) (j:=29) (m:=15) (R:=1073) (wanted:=29) fac dr (by decide) (by decide)
    ((show 15∣802241960520 from ⟨53482797368,rfl⟩).trans div) table29
  subst D
  have eqn : p^2+28=29*y^2 := by omega
  have h := smooth29 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=29) (j:=29) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table31 : ∀ d : Fin (1147+1), d.val∣1147 → ∀ t : Fin 8,
    (d.val*t.val^2)%8=31%8 → d.val=31 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject31 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+31) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=31) (R:=1147) div (by decide : 0<31) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=31 := coefficient (n:=n) (D:=D) (y:=y) (j:=31) (m:=8) (R:=1147) (wanted:=31) fac dr (by decide) (by decide)
    ((show 8∣802241960520 from ⟨100280245065,rfl⟩).trans div) table31
  subst D
  have eqn : p^2+30=31*y^2 := by omega
  have h := smooth31 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=31) (j:=31) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table34 : ∀ d : Fin (1258+1), d.val∣1258 → ∀ t : Fin 60,
    (d.val*t.val^2)%60=34%60 → d.val=34 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject34 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+34) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=34) (R:=1258) div (by decide : 0<34) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=34 := coefficient (n:=n) (D:=D) (y:=y) (j:=34) (m:=60) (R:=1258) (wanted:=34) fac dr (by decide) (by decide)
    ((show 60∣802241960520 from ⟨13370699342,rfl⟩).trans div) table34
  subst D
  have eqn : p^2+33=34*y^2 := by omega
  have h := smooth34 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=34) (j:=34) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxRecDepth 8192 in
private theorem table35 : ∀ d : Fin (1295+1), d.val∣1295 → ∀ t : Fin 24,
    (d.val*t.val^2)%24=35%24 → d.val=35 := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
private theorem reject35 {n p : ℕ} (big : 10000000<p) (div : 802241960520∣n) (shape : n+1=p^2)
    (hit : 37∣n+35) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (n:=n) (j:=35) (R:=1295) div (by decide : 0<35) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=35 := coefficient (n:=n) (D:=D) (y:=y) (j:=35) (m:=24) (R:=1295) (wanted:=35) fac dr (by decide) (by decide)
    ((show 24∣802241960520 from ⟨33426748355,rfl⟩).trans div) table35
  subst D
  have eqn : p^2+34=35*y^2 := by omega
  have h := smooth35 eqn (coord_bound (n:=n) (p:=p) (y:=y) (D:=35) (j:=35) sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxHeartbeats 2000000 in
/-- Any further solution with a prime-square successor is divisible by every prime through 37. -/
theorem force_thirty_seven {n p : ℕ} (big : 330<n) (pp : p.Prime)
    (shape : n+1=p^2) (sol : v_l 1 n=1) (div : 802241960520∣n) : 29682952539240∣n := by
  have huge := (Erdos889.MissingPrimeSieve.further_solution_bounds_thirty big sol).1
  have large : 10000000<p := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have nz : ¬37∣p := by
    intro dvd
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 37) pp).mp dvd
    omega
  have thirtySeven : 37∣n := by
    by_contra miss
    have alts : 37∣n+2 ∨ 37∣n+4 ∨ 37∣n+5 ∨ 37∣n+8 ∨ 37∣n+10 ∨ 37∣n+11 ∨ 37∣n+12 ∨ 37∣n+13 ∨ 37∣n+17 ∨ 37∣n+22 ∨ 37∣n+26 ∨ 37∣n+27 ∨ 37∣n+28 ∨ 37∣n+29 ∨ 37∣n+31 ∨ 37∣n+34 ∨ 37∣n+35 := by
      have table : ∀ a b : Fin 37, (a.val+1)%37=(b.val^2)%37 →
          a.val≠0 → b.val≠0 → 37∣a.val+2 ∨ 37∣a.val+4 ∨ 37∣a.val+5 ∨ 37∣a.val+8 ∨ 37∣a.val+10 ∨ 37∣a.val+11 ∨ 37∣a.val+12 ∨ 37∣a.val+13 ∨ 37∣a.val+17 ∨ 37∣a.val+22 ∨ 37∣a.val+26 ∨ 37∣a.val+27 ∨ 37∣a.val+28 ∨ 37∣a.val+29 ∨ 37∣a.val+31 ∨ 37∣a.val+34 ∨ 37∣a.val+35 := by decide +kernel
      have localProof := table ⟨n%37,Nat.mod_lt _ (by decide)⟩ ⟨p%37,Nat.mod_lt _ (by decide)⟩
        (by dsimp; rw [Nat.mod_add_mod,shape,Nat.pow_mod p 2 37])
        (fun h => miss (Nat.dvd_of_mod_eq_zero h)) (fun h => nz (Nat.dvd_of_mod_eq_zero h))
      simpa only [Nat.dvd_iff_mod_eq_zero,Nat.mod_add_mod] using localProof
    rcases alts with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · exact reject2 large div shape h sol
    · exact reject4 large div shape h sol
    · exact reject5 large div shape h sol
    · exact reject8 large div shape h sol
    · exact reject10 large div shape h sol
    · exact reject11 large div shape h sol
    · exact reject12 large div shape h sol
    · exact reject13 large div shape h sol
    · exact reject17 large div shape h sol
    · exact reject22 large div shape h sol
    · exact reject26 large div shape h sol
    · exact reject27 large div shape h sol
    · exact reject28 large div shape h sol
    · exact reject29 large div shape h sol
    · exact reject31 large div shape h sol
    · exact reject34 large div shape h sol
    · exact reject35 large div shape h sol
  omega

end Erdos889.SquareThirtySeven

#print axioms Erdos889.SquareThirtySeven.force_thirty_seven
