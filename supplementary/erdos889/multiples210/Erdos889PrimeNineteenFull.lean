import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1
import Mathlib.Data.Nat.Factorization.Induction

/-! A modular certificate for the first multiple of nineteen. -/
namespace Erdos889.PrimeNineteen

private structure Config where
  d : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  ax : ℕ
  byy : ℕ
  cz : ℕ

private structure Row where
  q : ℕ
  k : ℕ
  pool : List ℕ
  other : List ℕ
  m : ℕ
  mask : ℕ
  deriving Inhabited

private abbrev Stable (g : Config) (L m : ℕ) :=
  0 < m ∧ g.x^(L+1)%m=g.x%m ∧ g.y^(L+1)%m=g.y%m ∧ g.z^(L+1)%m=g.z%m

private theorem cycle {L p m : ℕ} (hL : 0<L) (one : Nat.ModEq m (p^(L+1)) p) (e : ℕ)
    (he : 0<e) : Nat.ModEq m (p^e) (p^(L+e%L)) := by
  have step (v : ℕ) (hv : 0<v) : Nat.ModEq m (p^(v+L)) (p^v) := by
    have one' := one.mul_right (p^(v-1))
    rw [←pow_add,show L+1+(v-1)=v+L by omega] at one'
    simpa only [←pow_succ',Nat.sub_add_cancel hv] using one'
  have steps (v : ℕ) (hv : 0<v) (j : ℕ) : Nat.ModEq m (p^(v+L*j)) (p^v) := by
    induction j with
    | zero => simp only [Nat.mul_zero,Nat.add_zero]; rfl
    | succ j ih =>
      rw [Nat.mul_succ,←Nat.add_assoc]
      exact (step _ (by omega)).trans ih
  calc
    p^e ≡ p^(e+L) [MOD m] := (step e he).symm
    _ = p^((L+e%L)+L*(e/L)) := by rw [Nat.add_assoc,Nat.mod_add_div,Nat.add_comm]
    _ ≡ _ [MOD m] := steps _ (by omega) _

private def residue (g : Config) (L m k a b c : ℕ) :=
  (((g.x^(L+a)%m)*(g.y^(L+b)%m)%m)*(g.z^(L+c)%m)%m+k+g.d*m-g.d)%m

private structure H (g : Config) (n a b c : ℕ) : Prop where
  shape : n+g.d=g.x^a*g.y^b*g.z^c
  ha : 0<a
  hb : 0<b
  hc : 0<c ∨ g.z=1
  flat : g.z=1 → c=0
  big : 2000<n
  div : 510510∣n
  prime : (n+1).Prime
  sol : Erdos889.v_l 1 n=1

private theorem residue_eq {g : Config} {n a b c L m : ℕ} (h : H g n a b c) (hL : 0<L)
    (st : Stable g L m) (k : ℕ) : (n+k)%m=residue g L m k (a%L) (b%L) (c%L) := by
  obtain ⟨mp,c2,c3,c7⟩ := st
  let w := ((g.x^(L+a%L)%m)*(g.y^(L+b%L)%m)%m)*(g.z^(L+c%L)%m)%m+k
  have d : Nat.ModEq m (n+k+g.d) w := by
    rw [show n+k+g.d=(n+g.d)+k by omega,h.shape]
    apply Nat.ModEq.add_right k
    change _ % m = _ % m
    rw [Nat.mod_mod, ←Nat.mul_mod (g.x^(L+a%L)) (g.y^(L+b%L)), ←Nat.mul_mod]
    have cz : Nat.ModEq m (g.z^c) (g.z^(L+c%L)) := by
      rcases h.hc with pos|one
      · exact cycle hL c7 c pos
      · simp only [one,one_pow]; rfl
    exact ((cycle hL c2 a h.ha).mul (cycle hL c3 b h.hb)).mul cz
  have add : Nat.ModEq m w (w+g.d*m) := by
    change w%m=(w+g.d*m)%m
    rw [Nat.mul_comm g.d m,Nat.add_mul_mod_self_left]
  exact Nat.ModEq.add_right_cancel' g.d
    (show Nat.ModEq m (n+k+g.d) (w+g.d*m-g.d+g.d) by rw [Nat.sub_add_cancel (by have := Nat.le_mul_of_pos_right g.d mp; omega)]; exact d.trans add)

private abbrev RowOK (g : Config) (L : ℕ) (r : Row) :=
  r.q.Prime ∧ 0<r.k ∧ r.k<r.q ∧ r.q∈r.pool ∧ Stable g L r.q ∧ Stable g L r.m ∧
  r.mask.testBit (1%r.m)=true ∧
  (∀ i : Fin r.m, r.mask.testBit i.val=true → ∀ p∈r.pool, r.mask.testBit (i.val*p%r.m)=true) ∧
  (∀ p∈r.other, Stable g L p) ∧
  (∀ p : Fin (r.k+1), p.val.Prime → p.val∈r.pool ∨ p.val∈r.other)

private abbrev CellOK (g : Config) (L : ℕ) (r : Row) (i j k : ℕ) :=
  residue g L r.q r.k i j k=0 ∧ r.mask.testBit (residue g L r.m r.k i j k)=false ∧
  ∀ p∈r.other, residue g L p r.k i j k≠0

private theorem killRow {g : Config} {n a b c L : ℕ} (h : H g n a b c) (hL : 0<L)
    {r : Row} (valid : RowOK g L r) (cell : CellOK g L r (a%L) (b%L) (c%L)) : False := by
  obtain ⟨pq,kpos,klt,qin,sq,sm,one,closed,others,small⟩ := valid
  have qd := Nat.dvd_of_mod_eq_zero ((residue_eq h hL sq r.k).trans cell.1)
  have support (p : ℕ) (pp : p.Prime) (dp : p∣n+r.k) : p∈r.pool := by
    by_contra outside
    have ne : r.q≠p := by intro e; exact outside (e ▸ qin)
    by_cases early : p≤r.k
    · have po := (small ⟨p,by omega⟩ pp).resolve_left outside
      exact cell.2.2 p po ((residue_eq h hL (others p po) r.k).symm.trans (Nat.mod_eq_zero_of_dvd dp))
    · exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.two_primes kpos pq pp ne klt (by omega) qd dp h.sol
  have smooth (t : ℕ) : 0<t → (∀ p : ℕ, p.Prime → p∣t → p∈r.pool) → r.mask.testBit (t%r.m)=true := by
    induction t using induction_on_primes with
    | zero => omega
    | one => exact fun _ _ => one
    | prime_mul p t pp ih =>
      intro pos sup
      have tt : 0<t := Nat.pos_of_mul_pos_left pos
      have pt := sup p pp (dvd_mul_right p t)
      have good := ih tt (fun q pq d => sup q pq (dvd_mul_of_dvd_right d p))
      have final := closed ⟨t%r.m,Nat.mod_lt _ sm.1⟩ good p pt
      simpa only [Nat.mod_mul_mod,Nat.mul_comm t p] using final
  have final := smooth (n+r.k) (by omega) support
  rw [residue_eq h hL sm,cell.2.1] at final
  contradiction

private inductive Rule where
  | target | div (p : ℕ) | prime (q : ℕ) | pool (r : Row)
  deriving Inhabited

private def Valid (g : Config) (L : ℕ) : Rule → Prop
  | .target => 12∣L
  | .div p => p∣510510 ∧ Stable g L p
  | .prime q => q.Prime ∧ q≤2000 ∧ Stable g L q
  | .pool r => RowOK g L r

private instance (g : Config) (L : ℕ) (r : Rule) : Decidable (Valid g L r) := by
  cases r <;> unfold Valid <;> infer_instance

private abbrev Target (g : Config) (a b c : ℕ) := a%12=g.ax ∧ b%12=g.byy ∧ c%12=g.cz

private def Hit (g : Config) (L i j k : ℕ) : Rule → Prop
  | .target => Target g i j k
  | .div p => residue g L p 0 i j k≠0
  | .prime q => residue g L q 1 i j k=0
  | .pool r => CellOK g L r i j k

private instance (g : Config) (L i j k : ℕ) (r : Rule) : Decidable (Hit g L i j k r) := by
  cases r <;> unfold Hit <;> infer_instance

private theorem kill {g : Config} {n a b c L : ℕ} (h : H g n a b c) (hL : 0<L) (bad : ¬Target g a b c)
    (r : Rule) (v : Valid g L r) (hit : Hit g L (a%L) (b%L) (c%L) r) : False := by
  cases r with
  | target =>
    apply bad
    simpa only [Hit,Target,Nat.mod_mod_of_dvd _ v] using hit
  | div p =>
    apply hit
    rw [←residue_eq h hL v.2]
    exact Nat.mod_eq_zero_of_dvd (v.1.trans h.div)
  | prime q =>
    obtain ⟨pq,small,st⟩ := v
    have d := Nat.dvd_of_mod_eq_zero ((residue_eq h hL st 1).trans hit)
    have e := (Nat.prime_dvd_prime_iff_eq pq h.prime).mp d
    have := h.big
    omega
  | pool r => exact killRow h hL v hit

private structure Keys where
  count : ℕ
  bits : ℕ
  data : ℕ

private def coord (keys : Keys) (i d : ℕ) :=
  (keys.data >>> (keys.bits*(3*i+d))) % 2^keys.bits

private abbrev Match (t a b c : ℕ) (keys : Keys) :=
  ∃ i<keys.count, a%t=coord keys i 0 ∧ b%t=coord keys i 1 ∧ c%t=coord keys i 2

private structure Stage where
  cfg : Config
  t : ℕ
  s : ℕ
  old : Keys
  next : Keys
  rules : List Rule
  bits : ℕ
  codes : ℕ

private def pick (g : Stage) (i x y z : ℕ) :=
  (g.codes >>> (g.bits*(if g.cfg.z=1 then (i*g.s+x)*g.s+y else ((i*g.s+x)*g.s+y)*g.s+z))) % 2^g.bits

private abbrev Test (g : Stage) (i x y z : ℕ) : Prop :=
  if g.cfg.z=1 ∧ z≠0 then True else
  let u := coord g.old i 0 + g.t*x
  let v := coord g.old i 1 + g.t*y
  let w := coord g.old i 2 + g.t*z
  let code := pick g i x y z
  if code<g.rules.length then Hit g.cfg (g.t*g.s) u v w g.rules[code]!
  else let j := code-g.rules.length
       j<g.next.count ∧ u=coord g.next j 0 ∧ v=coord g.next j 1 ∧ w=coord g.next j 2

private theorem refine {n a b c : ℕ} (g : Stage) (h : H g.cfg n a b c) (bad : ¬Target g.cfg a b c)
    (ht : 0<g.t) (hs : 0<g.s) (valid : ∀r∈g.rules, Valid g.cfg (g.t*g.s) r)
    (tested : ∀ i<g.old.count, ∀ x y z : Fin g.s, Test g i x y z)
    (old : Match g.t a b c g.old) : Match (g.t*g.s) a b c g.next := by
  obtain ⟨i,hi,eA,eB,eC⟩ := old
  let L := g.t*g.s
  have hL : 0<L := Nat.mul_pos ht hs
  let digit (d : ℕ) : Fin g.s := ⟨d%L/g.t,(Nat.div_lt_iff_lt_mul ht).2 (by
    rw [Nat.mul_comm]; exact Nat.mod_lt d hL)⟩
  have split (d : ℕ) : d%g.t+g.t*(digit d).val=d%L := by
    change d%g.t+g.t*(d%L/g.t)=d%L
    have dv : g.t∣L := dvd_mul_right g.t g.s
    simpa only [Nat.mod_mod_of_dvd _ dv] using Nat.mod_add_div (d%L) g.t
  have cell := tested i hi (digit a) (digit b) (digit c)
  dsimp only [Test] at cell
  have nz : ¬(g.cfg.z=1 ∧ (digit c).val≠0) := by
    rintro ⟨one,ne⟩
    apply ne
    simp [digit,h.flat one]
  rw [if_neg nz] at cell
  rw [←eA,←eB,←eC,split a,split b,split c] at cell
  split at cell
  next hcode =>
    rw [getElem!_pos g.rules _ hcode] at cell
    exact False.elim (kill h hL bad _ (valid _ (List.getElem_mem hcode)) cell)
  next => exact ⟨_,cell⟩


open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
theorem no_nineteenth_twelfth {n j z : ℕ} (hj : 0<j) (small : j≤18) (large : 1000000000000000000<n) (div : 510510∣n) (big : 1<z)
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
  have classifyA (p : ℕ) (pp : p.Prime) (low : p≤36) (dp : p∣t+1) : p=2 ∨ p=17 := by
    have tab : ∀ q : Fin 37, q.val.Prime → ∀ u : Fin q.val, (u.val^4+1)%q.val=0 → q.val=2 ∨ q.val=17 := by decide +kernel
    have m := ((Nat.mod_modEq z p).pow 4).add_right 1
    exact tab ⟨p,by omega⟩ pp ⟨z%p,Nat.mod_lt _ pp.pos⟩ (m.trans (Nat.modEq_zero_iff_dvd.mpr dp))
  have largeZ : 239<z^2 := by
    by_contra! low
    have lim : z≤15 := by nlinarith
    have zz := Nat.pow_le_pow_left lim 12
    have nj := Nat.mul_le_mul small zz
    omega
  obtain ⟨p,pp,hp,dp⟩ : ∃ p : ℕ, p.Prime ∧ 36<p ∧ p∣t+1 := by
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
      have dj := (Nat.dvd_add_iff_right ((by decide : 17∣510510).trans div)).mpr d2
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
  have hq : 36<q := by
    by_contra! low
    have tab : ∀ q : Fin 37, q.val.Prime → ∀ u : Fin q.val, ¬Nat.ModEq q.val (u.val^4) (u.val^8+1) := by decide +kernel
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



namespace D2
private def cfg : Config := ⟨2,2,19,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨0,4,0x0⟩
private def rows12 : List Rule := [
  .div 3,
  .target,
  .div 5,
  .div 7,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x69a69a69a0000000005134d44d300000000069a69a69a0000000004d44d351300000000069a69a69a0000000004d35134d1000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+2=2^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  obtain ⟨i,hi,_⟩ := h12
  exact Nat.not_lt_zero i hi
end D2


namespace D3
private def cfg : Config := ⟨3,3,19,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x89045⟩
private def rows12 : List Rule := [
  .div 5,
  .target,
  .div 7,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x4104104100000000000850820c20000000004104104100000000000c20840820000000004104104100000000000820c2081000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨3,6,0x515020240a29⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩,
  .pool ⟨31,7,[31,7],[2,3,5],271,0x120d15b642339a3861580a1fc6dd5e913d437685449c07afe579e3a633bd92574fb6⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .pool ⟨31,4,[31,2],[3],271,0x120d15b642339a3861580a1fc6dd5e913d437685449c07afe579e3a633bd92574fb6⟩,
  .pool ⟨31,8,[31,2],[3,5,7],271,0x120d15b642339a3861580a1fc6dd5e913d437685449c07afe579e3a633bd92574fb6⟩,
  .pool ⟨61,25,[61,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0x6000600000000500090008000040007000300000000200010⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨2,7,0x50a200a15⟩
private def rows120 : List Rule := [
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],1464,0x8a20a08228028220008a08828000028808000a28228208a00800808220a28820220828a08a20000820800a08008808a08028820828820008000820220800020208828828008200200028a08800a28a00808008a00200a00208020000008020800a00800a20020200a28a00220a28000800820028228220808000208808200020008228208228020a20220020a00208200008a20a28208808228a08820200200a20828828a00020228000028220a20008828028820a08a2⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],1312,0xf599416313111545011581191b11991311114119418501411145910151416105211113011b53094110017113014151098131311151219d0511411331150101710541030505050191035511054141315101000101151905054111558113014141418105411d01015119910511417309151119190321150501911d0011052195b101911109410d0515011345110501430531051111913311b131035101455111918d05335e⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],160,0x1111010110a19901230a4501415100b18d05335e⟩,
  .pool ⟨41,6,[41,2,3],[5],244,0xf5915131119115111111d113111193b93111191171111115113111915135e⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0xadc291000⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 3 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨0,8,0x0⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨31,21,[31,3,7,19],[2,5,11,13,17],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0x30⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 2 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+3=3^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  obtain ⟨i,hi,_⟩ := h240
  exact Nat.not_lt_zero i hi
end D3


namespace D4
private def cfg : Config := ⟨4,2,19,1,2,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨0,4,0x0⟩
private def rows12 : List Rule := [
  .div 5,
  .div 7,
  .div 3,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x492492492101044041492492492208208208492492492044041101492492492208208208492492492041101043492492492208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+4=2^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=2 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  obtain ⟨i,hi,_⟩ := h12
  exact Nat.not_lt_zero i hi
end D4


namespace D5
private def cfg : Config := ⟨5,5,19,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x67⟩
private def rows12 : List Rule := [
  .div 3,
  .target,
  .div 7,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x4934924d20000000004d24934920000000004925124930000000004934924d20000000004d24934920000000004924d2491000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨3,6,0x4b701e7c0193⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],61,0x1ffffffffffffffe⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x28400004000018200⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨2,7,0x1eb600f1f⟩
private def rows120 : List Rule := [
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .prime 41]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,2,0x117644⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 3 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨0,8,0x0⟩
private def rows240 : List Rule := [
  .div 17]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 2 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+5=5^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  obtain ⟨i,hi,_⟩ := h240
  exact Nat.not_lt_zero i hi
end D5


namespace D6
private def cfg : Config := ⟨6,2,3,19,1,1,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨11,4,0x78a34ab0aab76772379a4564124891451⟩
private def rows12 : List Rule := [
  .div 7,
  .div 5,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x1010121010121111111111110101010101011111111111111012101012101111111111110101010101011111111111111210101210101111111111110101010101011111111111111111111111111010101010101111111111110101e101012111111111111110101010101011111111111101210101d101111111111111101010101010111111111111c101012101010101010101011111111111111010121010121111111111110101010101011111111111111012101012101111111111110101010101011111111111111210101210101111111111111111111111112101012101011111111111111010101010101111111111110101210101211111111111111010101010101111111111110121010121011111111111111010101010101b101012101011111111111101010101010111111111111110101a101012111111111111010101010101111111111111101210101910111111111111010101010101111111111111111111111111101010101010111111111111210101210101111111111111101010101010111111111111010121010121111111111111101010101010111111111111012101012101010101010101111111111111121010121010111111111111010101010101111111111111101012101012111111111111010101010101111111111111101210101210111111111111111111111111018101012101111111111111101010101010111111111111210101710101111111111111101010101010111111111111010121010161111111111111101010101010101210101210111111111111010101010101111111111111121010121010111111111111010101010101111111111111101012101012111111111111010101010101111111111111111111111111101010101010111111111111012101012101111111111111101010101010111111111111210101210101111111111111101010101010111111111111010121010121010101010101111111111111101510101210111111111111010101010101111111111111121010141010111111111111010101010101111111111111101012101013111111111111111111111111010121010121111111111111101010101010111111111111012101012101111111111111101010101010111111111111210101210101111111111111101010101010⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨147,6,0x7b2e4e0bb75221c88abe167e02ab50a3f4e9ba3a9dceb343a0c4eb3a2e0dcb8f42e0f488fa226dc8a7422cc489bd169e85834163c4583a0a3dc29b40aef0e8b93aeccbafc222d88a30225e45bb016be428b30a5c02aebf7297de25ebb8bad6edf28b7ca8d32bb1fa2c74b7ddeaf7a9fdf64f7187deadeb19fad24eb787ac6ddf79f7dedd3aab4f67d34874c6ac749f1e63f76b3ae69eb08face0eb0a77ce6df68f7cecd399b4f23d30834e6cc7ca71c26c76831d5eb486ed2d8b4e56d092b4b7aa39ba8262a155a884aa15b9c86272d59ce7a109b8456212d284176d11ab475ed351b416a71d49ca46729d8415e11148435ad0dca895aa010a8c6670169c94e43109067212598452dc60871b15c60e65b2d978865215954265e39648b59521654e4db2137854d20936ce41e2d060241d35c68171729968765d11968d5941165c159135350a4dd1d044441⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,10,[31,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨31,7,[31,7],[2,3,5],793,0x12d020a252081880644c112020006092460020080020180882a080f008c000022017044708b2850016000655a08040086844885840080416a98001a0028534438883a01100000c403c0415044060100040100189241800101220c8980460412914102d2⟩,
  .pool ⟨31,8,[31,2],[3,5,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,10,[31,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩,
  .pool ⟨31,4,[31,2],[3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,2,[31,2],[],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,5,[31,5],[2,3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,2,[31,2],[],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,3,[61,3],[2],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .prime 31,
  .pool ⟨61,2,[61,2],[],31,0x68818116⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .prime 61,
  .pool ⟨31,9,[31,3],[2,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],31,0x68818116⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],217,0x1a20200420400081200080104003000820040012040008108010116⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,4,[61,2],[3],31,0x68818116⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,3,[31,3],[2],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,8,[31,2],[3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,25,[61,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨61,10,[61,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨61,10,[61,2,5],[3,7],325,0x1b282210302018116d1430001a000809b68808802d0044045b6404001600030a2da206010302110536⟩,
  .pool ⟨61,20,[61,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],651,0x20a0522084922020090934c341b24221a2002d04810800d100a0412402c021300204a65a2000900c02986824db2000892936012982c905960a6502d26584102cb08221820301041060b28b0924422912832⟩,
  .pool ⟨31,4,[31,2],[3],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,9,[61,3],[2,5,7],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨61,9,[61,3],[2,5,7],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,5,[61,5],[2,3],25,0x210863⟩,
  .pool ⟨61,5,[61,5],[2,3],31,0x46000062⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,8,0x2a000000090000000800000000000000000700000029000a0000000000000000bd000000bc0000000b000000080000000000000b0000000800000007000000bb0000000000000000ba00b9000000280000000000000000270000000800000007000000000000260000000a000000b8000000b70000000900000000000000b6000000b5000000b4000000b30000000000000000b20025000000b10000000000000000b0000000af00000013000000000000ae000000ad000000ac000000ab000000aa000000000000a9000000a8000000110000000000000000a7000000a600130000000000000000a5000000a4000000a300000011000000a20000000000000000a10000000d000000240000000e000000000000230000000e00000022000000a000000000000000000d009f0000000d00000000000000009e0000000e0000009d0000000000000e0000009c000000210000000d0000009b0000000000000d0000009a0000000e0000000000000000990000009800000002000000970000002000000000000000009600000003000100000000000000001f0000001e0000009500000094000000000000930000001d00000001000000030000000000000000920003000000020000000000000000910000001d00000004000000000000900000000400000003000000020000008f000000000000008e0000008d0000008c0000008b00000000000000008a00890000001c0000000000000000880000008700000086000000000000850000001a000000840000001b0000001900000000000083000000820000008100000000000000001a00000080001800000000000000007f0000007e0000001900000018000000000000001700000005000000160000007d000000150000000000007c0000007b0000000600000000000000007a0000007900050000000000000000780000007700000076000000140000000000007500000014000000740000007300000000000000007200710000007000000000000000006f000000060000006e00000000006d0000006c0000006b0000006a0000000000000000690068000000670000000000000000660000006500000064000000000000130000006300000062000000610000001100000000000012000000120000001200000000000000001200000012006000000000000000005f0000005e000000110000005d000000000000005c0000005b0000005a0000000e000000590000000000000e000000100000001000000000000000000d00000010000d0000000000000000580000000e00000057000000560000000000000f0000000f0000000d0000000f00000000000000000e00550000000e000000000000000054000000530000000d000008000000000000000007000000520000000c000000090000000000005100000009000000500000000a00000000000000004f00070000004e00000000000000004d0000000b000000080000000000000b000000080000000a0000004c0000004b0000000000004a0000004900000009000000000000000008000000070000000000050000004800000047000000460000000600000000000045000000440000004300000000000000004200000041004000000000000000003f0000003e00000006000000050000000000003d000000050000003c0000003b00000000000000003a003900000038000000000000000006000000050000003700003600000000000000000400000003000000020000003500000000000002000000340000003300000032000000000000000003003100000003000000000000000002000000300000002f0000000000002e0000002d00000001000000030000000200000000000003000000020000002c00000000000000002b0000000100⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_8 : ∀ i ∈ List.range' 8 3, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 11 at hi
  by_cases h0 : i < 8
  · exact test60_0 i (by simp only [List.mem_range'_1]; omega)
  exact test60_8 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨540,7,0x87a3507d1aa1acd41d66a87a1707d0ba1ac5c1d62e9f73513b9aa7a0d44d06a9f71713b8ba7a05c4d02ee742f37297b9d044dca228712f07897a188bc1c45e8711107888a188441c4223f7235b4118fdc156d00acf4232ba11b3948caca46cf4052ba02b39414aca0a1fc3b4b69d87f0752da3aaf93b1b51dabe4746d43adf33b3321db7cc74cc83a07c2f3f69781f044fda223762f573978dd8455ce22df02f33097b7c044cc222c792927514b1e42c9d416970290f094a5c02c3c2167f923035119fe4140d40a37323572118dcc155c80a8f83b0bc1da3a4ec2d2768f81d0bc0ea3a4742d23aef2353b91abb8cd4ec66aef2173b90bbb8c5cec62ed7b2f2fd97b5b0bcbd85ed7b112fd88b5b044bd8221752f4731785d4451cc2276f29770149dbc2ddc0165f8236b49197e015ad20aa6f2317791a9808c5c046a6f0517782a980145c00ad5af9ae5fcf56b6eb97b7151edc6176c5473f1859f8d7e78a473e35f262919315de1c6770c5770f19d87ed1e1ba8f0fb0b86e85c3ed1c3ba8e1fb0b0ee85879dcf992e7ce737e649bf39dcdb92e6de7376e49bb73d9f9da57ccf676f695b7cd6f9aa3fcf35b6ea8fb7e53f9b69fcf913e6d89f3e53dbb69edf9136ed89b7cdcf3aae79f337cea9be7cdcd5aae6af33756a9bab856f386b79e11fce18fe7856d586b6ae11f5618fab9d3f392279e74f56489ab3d0f3da0f9cf4357683ab85ced866f6e1733e19b9f3d6edda3f6cf5b3f68f9fcd9e7aacf3f32b9ea95cfcd9c9aace4f32b26a9593e56e7b63f3f95b26d8f939d0e792873e7079e483cf9d0c992864e7072648393859e186570e1670e19587c52f9a61fcf14b6e987b7adbf39adf9eb33ce699e7adbd59adeaeb3356699abc58f3a6c79f127ce993e7c58d5a6c6af12756993ab7d2f3821f9df4b56087ab94ff38e7f9e503ce381e794fd58e7eae50356381ab058edbe4f6c1633ef939fad2ed9a976eb0fb6687dbad2cf9a967eb0f3e6879f95be78edf3e5339e399cf95bc98ede4e5332639993c55e7a6373f1572698d934dbe1e2670d36f0f899877d5e182af0df1b8608dc37d5c382ae1df1b0e08d8734fe1d6070cd3f0f581872bdb85175c0af66945d345b7b86945c16de69a5134131b84515c04c66914534ebab2395d93aea50e57288b7b20945922de5025128bb1b2211592ec65084528a3aac155d628ea385571c5b4ac692d616d239a4b1cebda0397503af608e5d04a37a01545028de085510483cb805e5c20b6e015b7083c9a05e4d20b66815b343b6b8593dc0eda6964f34839ac0555620e6381551ccb0ac298563286b0a4358cb08e29847328638a431c93bb20ddd924b2c83596493b940ddca24b2503592802fb23d05900be50f41287b5ac01ad61e9ab004d587b58e01ac71e9a3804d1c62fa66d05318be21b4110abba0196502aee0865904c38a025c5030a68095340c388225c4130a60895304a1a76945bb686962516b1d1476aca3b7415dab0aedd1458aca2c741562b0ab1b9d70a0eb86e39c281ce1b9d52a0ea96e394a81ca5e9770b84387a5d4ae10a589470882b862514a20aa5e9d6ab87357a7532e1c9989a6a88d35622daa216d589a4c88d26622d3221699a176a94bb56821aa510d5a174c94ba668213251099d1764acbb2742192b10c9d1746acba374211ab108de9464b8a327a1592e0ac9e9446b8a237a151ae0a8d89164888b2620992204c989146888a362091a2048de9a5eb8d2f7a2d7ae16bde9a40b8d207a2d02e16814115edc12f50450370481e1c76b46bb787162d1ab1c9076a883b7205daa02edc9058a882c720562a02b1b19709ccb86c29c2714e1b19529cca96c294a714a551670e43b854594b90ea5e1370b49b87811c2d08e1e1352b49a978114ad08a59936a909b56611aa408d59934c909a666113240899b106a9c0b56c41327029981c64846b260711a11a8d999649053266651a4148d0935ec022f424d0300881⟩
private def rows120 : List Rule := [
  .pool ⟨31,14,[31,2,7],[3,5,11,13],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨41,28,[41,2,7,17,19,23],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,25,[41,5,17,19,23],[2,3,7,11,13],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  .pool ⟨31,10,[31,2,5],[3,7],1281,0x1b28221060300800a0002800020000032000000522000000002100000000002930010010100000886020000000400000000020080000000000010000100022082800000800000c000800000000021200b4012100000000004000c00000400000504110002000020000000000004010000000000800000010184400002020020032500000000002100000000112800000130000010000500014004030182110536⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],1025,0x242031006008a0f6204002402122053040c00ab80c0da43222a12101880100c126b14000962101523902260815c0644c2193050909040208860835c80000b000089148303802ae0702614e982869402000c41041ec4084248000540a40898205f4391b0a6441434a410082008a4d72802024401220730c0e002fa0c09a43a22a⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],41,0x1b382b50736⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨41,13,[41,13],[2,3,5,7,11],183,0x4406824020400020424880000112420400020402416022⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],1025,0x1753739646c1ff0f7e0c33a51212a953045facbfc0d0da63b6bab2999cb6370ffa7b74409d6a90156b9862ede1de0ec4c319b5d596dce1b0b87dd35f8304ab44008b548307eb2ef874361ceda6aeb6630c8dc1ee1edd18675aa0255ae408bb797fc3b1b4e6653575b7196c2c0ff4d7e8832a5521229730c1fbc3fe0d89a73b2ba⟩,
  .pool ⟨41,13,[41,13],[2,3,5,7,11],61,0x1713e6940a59f23a⟩,
  .pool ⟨61,7,[61,7],[2,3,5],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨41,40,[41,2,5,17,19,23,29,37],[3,7,11,13,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,4,[31,2],[3],123,0x10000124014004012182110536⟩,
  .pool ⟨31,4,[31,2],[3],41,0x1b382b50736⟩,
  .pool ⟨61,3,[61,3],[2],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨61,31,[61,17,19,23,29],[2,3,5,7,11,13,31],1155,0x20840001a64308201141020004340228908009801a0034892502900424c001024108221808301028000220b0400000412400480000880802420510832180820080190026802520102034810980122420430886802000506100ca2806912086490492186d020021948228141220221a04109129008845004020000328060244a4080120182520c141168200800248b0012⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,17,[41,17],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,17,[41,17],[2,3,5,7,11,13],341,0x10005e2024580224044800c418080600000c000180000060000c000018040608c0048809100689011e8002⟩,
  .pool ⟨41,3,[41,3],[2],61,0x141002040810020a⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨31,9,[31,3],[2,5,7],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],341,0x10005e2024580224044800c418080600000c000180000060000c000018040608c0048809100689011e8002⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],451,0x100040000010010000400000000000000000010200104020000000004012000002100010116⟩,
  .pool ⟨31,3,[31,3],[2],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨61,4,[61,2],[3],451,0x100040000010010000400000000000000000010200104020000000004012000002100010116⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨41,12,[41,2,3],[5,7,11],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],915,0x20820000a6020080100022002020004090810c840040008001000021900200001029000000000000208000a00200041120840000008001000024340328000000840800209020000a6000886092502c021204100068220001000120008301200000060008120001000141100220a00108b0092⟩,
  .pool ⟨31,7,[31,7],[2,3,5],205,0x60111860280e10524000005100001520414841a008080011282⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],1435,0x5044c01003019034002042804000240810148042024241800000ca0610005012a18c800050000005000002010000080204420140430084024030006208122110002010000ca032c000800000921099083200053840700004208010420000e021ca0004c1099084900000100034c0530000804000884481046000c02402100c2028042204010000080400000a000000a00013185480a000860530000018242404201280810240002014204002c0980c00803220a⟩,
  .pool ⟨41,13,[41,13],[2,3,5,7,11],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨61,9,[61,3],[2,5,7],1435,0x5044c01003019034002042804000240810148042024241800000ca0610005012a18c800050000005000002010000080204420140430084024030006208122110002010000ca032c000800000921099083200053840700004208010420000e021ca0004c1099084900000100034c0530000804000884481046000c02402100c2028042204010000080400000a000000a00013185480a000860530000018242404201280810240002014204002c0980c00803220a⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,10,0x90a419023f8fa3d8f23b8ea398e2378da358d2338c80701e318c00701e2f8ba2d8b22b8aa298a2270980701c260980701c2601e268940701e2488c0788a218821f87a1d8721b04a1a8641204a1885c1285818062158501806213054150541505415054158481705e118401705e0f0581304c160581304c1604c160581304c160581309412048250941204825060250941806025094180620e834180620c82c180541505415054150541505e0a8241705e0881c170581304c160581304c16818110460581011046030581304c160581304c168081204a0180012049ff054150541505415054157f81705dfd7f01705dfb7e81705df97e01705df704c160581304c1605813049f67d412049f47cc12040090241004009024107c9f17c1ef7b9ed7b1eb7a9e97a1e7799e5791e3789e1781df779dd771db045da76411045d875c110400902410040090241004024090100402409010049d675412049d474c12049d274412049d073c1209010040240901004024739cd731cb729c9721c771801005c571001005c300c0300c0300c0300c0308c020082308c02008230880000022088000002200402008010040200801085c270421085c06fc216f801005bd6f001005bb001ba6e400001b86dc006d9b56d1b36c9b16c1af6b9ad6b1ab6a9a96a1a7075a66941d075a468c1d68820081a1680200819f6799d6719b669996619706c1b06c1b06c1b06c1b6599565193649916418f6398d6318b62989621876181d075856101d0758307d826041f07d805fc1f5f81d0757d5f01d0757b0797a5e41e079785dc1e06c1b06c1b06c1b06c1b5d9755d1735c9715c16f5b81d0756d5b01d0756b5a9695a16759965591635881c071615801c0715f06c1b06c1b06c1b06c1b5781a0695d5701a0695b56959561575595555153549515414f5394d5314b528060194952006019475194551143509415013f0053e4f4010053c4ec01010040100401004010044e9394e1374d9354d1334c9314c12f4b92d4b12b4a806019294a00601927004020080100402008010100401004010040100400526494010052448c0101004010040100401004489214811f4791d4711b0191a464060191845c0606516454190651444c190541505415054150541505d124441705d1043c170581304c160581304c160490e434120490c42c120581304c160581304c164281104509420110450741818061054101806103054150541505415054154081705d014001705cff3f81705cfd3f01705cfb04c160581304c1605813048fa3e412048f83dc123d81705cf53d01705cf30581304c160581304c163c811044f13c011044ef054150541505415054153b8ed3b0eb3a8e93a0e704c140501304c1405013048e639412048e438c120400902410040090241038811044e138011044df02410040090241004009378dd370db368d9360d703c110440f03c110440f0400902410040090241003c0f03c0f03c0f03c0f0240e038090240e03809358d5350d3348d1340cf0300d0340c0300d0340c02cce3340b02ccc32c0b0240a028090240a02809328c9320c7318c5310c302009024080200902408020c230408020c02fc082f80701cbd2f00701cbb2e8b92e0b72d8b52d0b32c802008b12c002008af010040100401004010042b8ad2b0ab2a8a92a0a7298a5290a3288a12809f01405014050140501405278060189d270060189b268010049926001004970100401004010040100425802008952500200893248912408f2388d2308b2288922087218852108301405014050140501405208812007f1f87d1f07b1e8791e0771d8751d0731c8711c06f1b86d1b06b010040100401004010041a8691a067198651906300462184010046017c01178000005d170000005b16859160571585515053148511404f1384d1304b0004a124000004811c001184511043108411003f00c0300c0300c0300c030f83d0f03b0e8390e0370d800000350d000000330c802008310c0020082f0b8000002d0b0000002b004020080100402008010002a0a4000002809c00⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_137 : ∀ i ∈ List.range' 137 10, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 147 at hi
  by_cases h0 : i < 137
  · exact test120_0 i (by simp only [List.mem_range'_1]; omega)
  exact test120_137 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨160,8,0xe0c9e568c9e5e0c96d68c96da451e52c51e5a4516d2c516de051a96851a9e05131685131a4c9a92cc9a9a4c9312cc931bcc9d944c9d9bcc96144c961bc519d44519dbc5125445125b039cd3839cdb03955383955b0b19138b191b0b11938b1198069cd0869cd80695508695580e19108e19180e11908e119c899cdc899558c21cd1421cd8c21551421555021915021198c99911499918c9919149919e021c1e02149a499c12c99c1a499492c994968998568990da421852c2185a4210d2c210db069b53869b5b0693d38693db0e17938e179b0e10138e101d481b55c81b5d4813d5c813dd409795c0979d409015c0901e8e9e5e8e96d7071a9707131a0b9e528b9e5a0b96d28b96da041a92841a9a04131284131d0a1d958a1d9d0a16158a1619429d91c29d99429611c2961d0299d58299dd0292558292594a19d1ca19d94a1251ca125a0d1d928d1d9a0d16128d161a0599d28599da05925285925e811d97011d9e81161701161e8899d70899de889257089258889cd1089cd888955108955881191101191881119101119d0b9cd58b9cdd0b95558b955d04191584191d041195841194071c1407149b8e985b8e90d88a1c110a1c188a14910a14988298510298588290d10290db889b54089b5b8893d40893db81179401179b81101401101⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨241,31,[241,19,23,29],[2,3,5,7,11,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨41,25,[41,5,19,23],[2,3,7,11,13,17],1525,0x1b78be523ff599206eaeb9cb4a092451a7a363b33b1fd6389661434c75d1d91a24bf7528f43b6d3c7f295feac8b03f574ce1a50c9038d7d0b99b9d0fca1c0b2021873aa8fc893257f8847e3db69c3f90aefd66589faaa632d20669142bf8d8edc6c7f50a259812d319557e4699afdd427f0e5b6f1f8847fa93244fc557386101340e14fc2e766742fac7024c2961ccbabf0344d5fea53f8f2db70bc52bbf491626e2eb8cb0a19a471afe373371b17962892414b4e75d5d81266bff129f47b6⟩,
  .pool ⟨41,20,[41,2,5,19],[3,7,11,13,17],1275,0x4016100122816500102580d94522d22110416410d368105a29361324949b6080812420124522c240304b20b2884520432880c821a6d060b4d24d260929b6c109005844248245940060960365948b40864101b0430db0c149a4d84c165265801204b08849040b0900812c86cb2116910ca20b60861b6182914934992ca6cb0424092110122916520182590596522922114416c10d36c105a6936932594db6⟩,
  .pool ⟨241,31,[241,19,23,29],[2,3,5,7,11,13,17,31],1155,0x20840001a64308201141020004340228908009801a0034892502900424c001024108221808301028000220b0400000412400480000880802420510832180820080190026802520102034810980122420430886802000506100ca2806912086490492186d020021948228141220221a04109129008845004020000328060244a4080120182520c141168200800248b0012⟩,
  .pool ⟨41,20,[41,2,5,19],[3,7,11,13,17],1525,0x1b78be523ff599206eaeb9cb4a092451a7a363b33b1fd6389661434c75d1d91a24bf7528f43b6d3c7f295feac8b03f574ce1a50c9038d7d0b99b9d0fca1c0b2021873aa8fc893257f8847e3db69c3f90aefd66589faaa632d20669142bf8d8edc6c7f50a259812d319557e4699afdd427f0e5b6f1f8847fa93244fc557386101340e14fc2e766742fac7024c2961ccbabf0344d5fea53f8f2db70bc52bbf491626e2eb8cb0a19a471afe373371b17962892414b4e75d5d81266bff129f47b6⟩,
  .pool ⟨61,38,[61,2,19,23,29,37],[3,5,7,11,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨241,31,[241,19,23,29],[2,3,5,7,11,13,17,31],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨241,7,[241,7],[2,3,5],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨241,5,[241,5],[2,3],25,0x210863⟩,
  .pool ⟨61,32,[61,2,19,23,29],[3,5,7,11,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨61,36,[61,2,3,19,23,29],[5,7,11,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,8,0xb0b00000b0b00000000000000000b0b00000b0b00000000000000000000abaa0000a9a800000000a7a60000a5a4000000000000000000000000000000000000a3a20000a1a09f9e00009d9c0000000000000000000000000000000000000000000000000000000000000000000000000303000003030a0a00000a0a000000000000000000000000000000000000030300000303000000000a0a00000a0a000000000000000000000a0a00000a0a00000000000000000a0a00000a0a00009b9a0000999800000000000000000000000097960000959400000000000000000000000000000000000093920000919000000000000000008f8e00008d8c0000080900000809000000008b8a000089880000000000000000000000000000000000000908000009088786000085840000000000000000000000000000000000000000000000000000000000000000000083070000820700000000818000007f7e000000000000000000000000000000000000077d0000077c7b7a000079780000000000000000000000000000000000000000770700007607757400007372000000000000000000000000000000000000077100000770000000006f6e00006d6c0606000006060000000006060000060600000000000000000000000000000000000006060000060606060000060600000000000000000000000000000000000000000000000000000000000000000000000003030000030306060000060600000000000000000000000000000000000003030000030300000000060600000606050500000505000000006b6a0000696800000000000000000000000000000000000005050000050567660000656400000000000000000000000000000000000000000000000000006362000061600000000000000000000000005f5e00005d5c5b0400005a04000000000000000000000000045900000458000000000000000000000202000002025756000055540000000000000000000000000000000000000202000002020000000053520000515000000000000000000000000000000000000000000000000000000000000000004f4e00004d4c000000004b4a0000494800000000000000000000000000000000000047460000454443420000414000003f3e00003d3c0000000000000000000000003b3a000039380000000000000000000000000000000000000000000000000000373600003534030300000303000000000000000000000000000000000000333200003130000000000303000003030000000000000000000000000000000000000202000002022f2e00002d2c000000000000000000000000000000000000020200000202000000002b2a0000292827260000252400000000000000000000000023220000212000000000000000000000011f0000011e00000000000000001d0100001c010000000000000000000000000000000000001b1a0000191800000000000000000000000017160000151400000000000000001312000011100000000000000000000000000f0e00000d0c⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_137 : ∀ i ∈ List.range' 137 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_274 : ∀ i ∈ List.range' 274 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_411 : ∀ i ∈ List.range' 411 129, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 540 at hi
  by_cases h0 : i < 137
  · exact test240_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h137 : i < 274
  · exact test240_137 i (by simp only [List.mem_range'_1]; omega)
  by_cases h274 : i < 411
  · exact test240_274 i (by simp only [List.mem_range'_1]; omega)
  exact test240_411 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨49,10,0x248aa6c51a0c975648aa55d1a0c91b5d08c689381412a4e0506117423148660566ad5c069334f8566ad02069335701a63598159514081a6353e1595157074581982c124408745813e2c124660b05f95c1d1064f8b05f9021d1066a89e6ad320996f5b8624cd6e1898d6a89e545320991563080671140216054044491501117e4500841968249a54b0564b50e249a5618564b52c159875a09252d86159874389252d2c2c15a618b05690e0e11e5a0385e12c2c100618b0401⟩
private def rows720 : List Rule := [
  .pool ⟨37,8,[37,2],[3,5,7],41,0x1b382b50736⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],481,0x1a60e406f08054a3a952005088d2202b63088820000098030303887034513228b038470303006400001044431b50112c4428012a5714a8043d809c196⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],1241,0x1b7cae9366e31868e5a3b0384e04f217f59f312e6c547a4097e41192f83119beb98a1fe82d0c63b4e2c0d9d1fa70810659aaa180080b4833bb11694c1e0a6aa32a5e13754aefe345228d1295a47b7896a522c5128b1fdd4abb21e953155941e0ca5a2377304b4040061556698204397e2e6c0d1cb718c2d05fe14675f662307d26209fa40978a8d9d233e6bfa13c81c87037169c58631d9b25d4fb6⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],665,0x1a3438806b524104a7389c70840c109270a82b130a90a9465080038008035820a8032244362c4939026319027248d1b089130054106b0040070004298a542543235054392420c08438e4739482092b580470b16⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],577,0x1eb63cf47e82bd94bbe610272e9e08926e2ab5f14c5431bc76a75be052064c25a6e07766799bb81d9690c981281f6b95b8f630a8ca3eb551d92441e5d390219f74a6f505f8bcf1b5e⟩,
  .pool ⟨31,10,[31,2,5],[3,7],399,0x100300044a0114106120c80006122102512d060904a0d14504102816490802410d32120db24069009344348905a6132536⟩,
  .pool ⟨31,24,[31,2,3,23],[5,7,11,13,17,19],37,0x1ffffffffe⟩,
  .pool ⟨31,24,[31,2,3,23],[5,7,11,13,17,19],577,0x1eb63cf47e82bd94bbe610272e9e08926e2ab5f14c5431bc76a75be052064c25a6e07766799bb81d9690c981281f6b95b8f630a8ca3eb551d92441e5d390219f74a6f505f8bcf1b5e⟩,
  .prime 37,
  .pool ⟨31,24,[31,2,3,23],[5,7,11,13,17,19],1463,0x425082205d50c081122a62200a1549443064c1d892c180805408c063661c231210a042825b053e6849618f1438541d01036744195a0112d4a687906a5180e42191201cc4024189048338f51261aac39d121832806d5bb56200f91323003f20502001e692a7124038226985102034da264d939c46e9705388d23428541a8244853d2425d1102f5e035441c300690d21024d01b0ad5aa73431839028dc8f50f87a6424c42c50f0d945038f3328a8b336c4d4015ab87135e⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨41,33,[41,3,11,23,29],[2,5,7,13,17,19,31],73,0x1fffffffffffffffffe⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],777,0x1a2124596090ca49a4020d029360921a60800060029904264868a44208205a60a01300141144a01001221a0c049121b48304b6122480c161120020148a20a00320141968104108945849908265001800041961241b2502c10096494c241a6892116⟩,
  .pool ⟨181,4,[181,2],[3],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨577,12,[577,2,3],[5,7,11],247,0x7ac8a0918840830680847404810a013c805081202e210160c102118905135e⟩,
  .pool ⟨41,20,[41,2,5],[3,7,11,13,17,19],209,0x1b392b592239de0830207a0b8ab5474178103041ee71126b52736⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],481,0x1fba6e34e2a13996a02730197b0f08f3604424ad7c451b0cba2c06a81652fd29a05580d174c36288fad490881b3c43c37a60339015a672151cb1d977e⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],949,0x175663565e83704f610d7e83069a2c1342e3a4641549fb43bb08c49a9967f79738894ed4187a1e4ea63621f400946bc59106a9b94f6ce050b1a218000611634281cdbca765582268f58a400be11b195c9e17860adca4473a7bf9a65648c43770b7e4aa098971d0b20d1658305fac21bc83b05e9ab19aba⟩,
  .pool ⟨181,23,[181,23],[2,3,5,7,11,13,17,19],111,0x14122102590d06410d329345b6⟩,
  .pool ⟨241,12,[241,2,3],[5,7,11],247,0x7ac8a0918840830680847404810a013c805081202e210160c102118905135e⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,7,0x1820988143058a10286081420588263040b144860818205441820608142058a102860b1420608862840b104860a182040b1448608182050c104c40a182c508143040a102c413182840b104860a182210c103040a102c508143058a103044114207881e3050c103c60818205081e2840a183c508182078f14206081e2050c103c60a18205081e3040a103c50f182040a183c508182078a103c40f18286081e3040c102840f143040a103c50f182078a103040f10286081e3050c102840f110060a1820508163040a102c512182058a103043f102860c104c40a182c508143040a102c412182058a263040c102858a103043e10286087a3050c102840b1820508162890c102058a263040c1028608262050c162840a1820508162090c18205081e2878c103c5081820788143040f1828608142078a18205081e2078c103c50f1820608143040f102860f142040f1828608142078c102840f143c6081e2840c103c40a183040f102860f142050c102840f103c6081e2878c103040a101c3070c203080e1840910243090c203861018407101c30610244090c243080e18406101c4070c203860e18406101c3861018407101c308121848610184090c203880e1838610203860e18406101c3080e203860e184090c2030812204860e18406101c4070c2048612184061024308122048612184080e1838610184070c20488121848610243080c204881218308122048612184070c203080e2038610243090c2030812243080c2048812184070c1c3080c2038610244090c24308101c3070c203080e18407101c3070c2048610184091024306101c4070c1c308121840610244090c203860e18406101c3861018407101c3080e1838610184070c2048812184861020486121840610243080e203860e184070c203080e2038610243090c203081218407101c3070c204861018409102430610244090c243080e18406101c4070c204861218406102448610184091024308121848610184090c203880e18386102048612184061024308122048612184070c203080e20386104483c2020808224041210448112020890104041110ec810104443a2044808244041010444112020890224041010e4890104041110e08082241b901040411202090822408901020890224041010d88082221a9022404122020808222089010448112020808244041110d081120219901040411104481010444112048808224041010c8411202189022404101045810104041110448082240890104041220208885e408901021710224041010448082220890244041120208085a20890583040c102840b142050c162840c10ac508162150c143040a102c4291828608503040c102840b142050c162840c109c78a103040f10286081e3050c102840f18205081e2878c102078a1e3040c10286081e2050c1e2840a18205081e2078c18205081e2878c103c5081820788143040f1828608142078a18205081e2078c103c50f1820608143040f102860f142130c103040a102c508143058a10304251420588483050c102840b108c60a182070c103040a102c508143058a1030422143040a103c40f182078a1e3040c10286081e2050c1e28408143078a103040f14207881e3050c103c60818205081e286081e2050c1e2840a18205081e2078c103c50f1820608143c60818205081e2840a183c508182078a103c40f1828608101c3070c203080e1840910243090c20486101840910243090c203081220486101c3070c203080e1840910243090c20308122048612184070c203080e20386101c3070c203080e1c3080c203880e184070c1c3080c2038610244090c2430810243090c203081218407101c3070c203861018407101c306101c4070c1c308121840610244090c203860e18406101c3080e203860e184070c203080e2038610243090c2030812203860e18406101c3080e203860e184090c20308122048610243090c20308121840910243090c203861018407101c30610244090c24308121840610244090c203860e18406101c3861018407101c308121848610184090c20488121848610203860e18406101c308122048612184090c203081220486108460a1820508163040a102c50d182058a1030420102860c107c40a182c508143040a102c40d182058a3c3040c102858a103041d1028608383050c102840b1820508162868c102058a363040c1028608342050c162840a1820508162068c102c50d18206081430419102860b142050c102840b103860a102c40d1828608303040c102840b142050c162840c105c50c102840b1058608162868c103040a1820a88143058a102050c162840c1038508162068c14304141820608142058a0c204881218486101c3080c203880e184090c243080c204890c203081220486101c3070c203080e1840910243090c204090c243080c2048610244090c243080e18406101c4070c1840910243090c20486101840910243080e183861018407101c3070c203080e18407101c3070c204861018409102430610244090c243080e18406101c4070c203860e18406101c3861018407101c308121848610184090c203880e183861020486121840610243080e203860e184070c203080e2038602000800204081040408002080800204101020408002000820204081000400102000800204081040408002080800204080020008102041010200082020008104040810200080020808102040010004080020008102041010200082020008108102040810204081020408102040810183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c204081020408102040810204081020408102040810204080c183060c183060c20408102040810203060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c18306102040810204081020408102040810203060c183060c183060c183060c18306102040810204081020408102040810203060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183061020408102040810183060c183060c18408102040810204060c183060c18306102040810204081020408102040810203060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183061020408102040810183060c183060c18408102040810204060c183060c183060c183060c183060c183060c183060c1840810204081020408102040810204080c183060c183060c183060c183060c1840810204081020408102040810204080c183060c183060c183060c183060c183060c183060c18308102040810204081020408102040810183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c20408102040810204081020408102040204001000410102000810204101000408202000810204000020408100041010200082020408100040820200080020408202000810204001020008002080810004081020808002040820200080020400102040800208081000410102040800200080020408104040800208080020410102040800200081020008002080810004081020808002041010004081020010102040800200081000400102040820204001040400102041010004081020008100040010404080020408104040010a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a1428508102040810204080c183060c183060c20408102040810203060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c18306102040810204081020408102040810203060c183060c183060c183060c18306102040810204081020408102040810203060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183060c183061020408102040810183060c183060c18408102040810204020400100041010200081020410100040820200081020400002040810004101020008202040810004082020008002040820200081020400102000800208081000408102080800204082020008002040010204080020808100041010204080020008002040810404080020808002041010204080020008102000800208081000408102080800204101000408102001010204080020008100040010204082020400104040010204101000408102000810004001040408002040810404001060c183060c183060c183060c183060c183060c183060c183060c183060c18308102040810204081020408102040810183060c183060c183060c183060c183060c183060c18306102040810204081020408102040810203060c183060c183000408102000820204001040408102000810404001000408100040010204082020400104040010208081020400100040810404001000408002040810004101020008202040810008081020400100040800200081020410102000820200081020400100041010200081020410100040820200081020400002040810004101020008202040810004082020008002040820200081020400102000800208081000408102080800204082020008002040010204080020808100041010204080000408102000820204001040408102000810404001000408100040010204082020400104040010208081020400100040810404001000408002040810004101020008202040810008081020400100040800200081020410102000820200081020400100041010200081020410100040820200081020400002040810004101020008202040810004082020008002040820200081020400102000800208081000408102080800204082020008002040010204080020808100041010204080⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_40 : ∀ i ∈ List.range' 40 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_80 : ∀ i ∈ List.range' 80 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_120 : ∀ i ∈ List.range' 120 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 160 at hi
  by_cases h0 : i < 40
  · exact test720_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : i < 80
  · exact test720_40 i (by simp only [List.mem_range'_1]; omega)
  by_cases h80 : i < 120
  · exact test720_80 i (by simp only [List.mem_range'_1]; omega)
  exact test720_120 i (by simp only [List.mem_range'_1]; omega)
private def keys5040 : Keys := ⟨0,13,0x0⟩
private def rows5040 : List Rule := [
  .pool ⟨37,30,[37,2,3,5,23],[7,11,13,17,19,29],1825,0x1fba6e74a3b1b893256f781e7a034c7d60d8e7a8aa154bf4aa354539d6c1af8cb0079e07b5ab32436371499d977efdd373253d8d84992b5bc8f3c01e63eb06c7394550aa5fa550aa69ce362d7c65903cf03dad49961b1b8a4cecbbf7ee9b9928ec6c24c97ade079e00d31f58363dca2a8752fd2b85514ef1b06be32c01e781ed7a4c90d8dc526765dfbf74dcc9476361a64ad6f03cf02698fad1b1ce59542a97e9542a8a738d835f19e00f3c4f6b526486c6f2933b2efdfba6e64a3b1b093356b781e78034c7d60dae728ab154bf4aa154579c6c1af8cb0179e07bda9324763714b9d977e⟩,
  .pool ⟨29,22,[29,2,11],[3,5,7,13,17,19],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨29,2,[29,2],[],31,0x68818116⟩,
  .pool ⟨29,7,[29,7],[2,3,5],49,0x81020408183⟩,
  .pool ⟨29,13,[29,13],[2,3,5,7,11],61,0x1005810120206802⟩,
  .pool ⟨29,26,[29,2,13,23],[3,5,7,11,17,19],31,0x7ffffffe⟩,
  .prime 29,
  .pool ⟨29,13,[29,13],[2,3,5,7,11],43,0x7fffffffffe⟩,
  .pool ⟨29,7,[29,7],[2,3,5],93,0x124c345b00221100368b0c92⟩,
  .pool ⟨29,22,[29,2,11],[3,5,7,13,17,19],127,0x7ffffffffffffffffffffffffffffffe⟩,
  .pool ⟨37,30,[37,2,3,5,23],[7,11,13,17,19,29],113,0x1fffffffffffffffffffffffffffe⟩,
  .prime 127,
  .prime 71,
  .pool ⟨29,26,[29,2,13,23],[3,5,7,11,17,19],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],551,0x14422061191d147946069217b607207ac6216d152cd709126a8f39153a48156bc9f06809576da247630ca1b72f14835748799c81fb0b9217361f8d61d1476739dbb5d7fe⟩,
  .prime 211,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],421,0x1756731e5683b44a660dfb81977f38db0e4ead3405d0eba5e252001291e975c2e80b2d5c9c36c73fba6077ec19948b705a9e339aba⟩,
  .pool ⟨29,22,[29,2,11],[3,5,7,13,17,19],703,0x16284d9071f687047b12ab2c803a01253a8e5358d88e4cb581011a9d01171c770a9cc4b9375f37d4a380d0f960b4de32d412041342dcc2a71147176f06a57f7e10cd86e4e4258e835b7b23fe4b2aa321dd1e9011f645eb96⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],631,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩]
private def step5040 : Stage := ⟨cfg,720,7,keys720,keys5040,rows5040,5,0x10628c8c5290628c8c6291028ca46291028c6462906214646290631464629c06290628c4062906214406290631440629088144062948814546314e3144081440629083145462948314406314831440031483146203148310a20314e8314831440031488146203148810a203148318a2a3148418a20314a718a2030a2a3148318a203148418a20314a440a20318a440a20018a418a31018a7188a418a20318a418a20018a418a31518a418851018a41a051018a43a051018b1018a440851018a440c51018a420c51018a520c51018c520c51028c538c51290624a8c62906288006291028c40629d0214406290631440629083144062c40629062144062906314406290e3145462948814406314881240031483144881464629483146463148314652314e3126323148310a323148340a323148031483145203148810a2a3148818a20314e418a20314a418a20318a418a2018a203148418a20314a418a20318a740a20018a440a31518a418849018a4198a418a20518a418a31018a418851018a718c49018a422051018a52205101851018a442051018a420c49018a538c51018c520c51500c520c51880c520c428a8c520c62880c521062880c529102880c62910288006290628c40629c6229062880c62906288006290628c54629062144062906814406290e8144062c4062910214406291031440629083144062948314406314831440a314e314483146462948314646314881465231488146323148310a323148318a32314e031483146203148310a203148318a203148440a20314a440a2a318a718a2040a203148418a2a314a418a20318a418a20018a418a31018a418851018a7418a418a20018a440a31018a440851018a418c51518a420c51018a538c5101862880c521062880c529062880c629d0288006291028c5462906212406290662906288146290628c406290621440629c6312406290881440629488144061440629108144062908312406294e3144063148314540314831462031483114831254631483144003148814620314e810a203148318a203148418a20316203148310a203148318a203148718a2a314a440a20318a440920018a418a2440a32314a418a32318a418a32918a718931918a418851918a41a051918a4018a418a29018a440851518a440c51018a720c51018a520c51018c520c51018a718a20018a418931018a440851018a440c51018a420c51518a520c5101851018a718c51518a420c51018a520c51018c522051000c522051480c520c453a051018c520c51000c520c51880c520c424a8c520c62880c521102880c58a8c538c42880c522102480c521062880c529062880c629062880062906289c624c8c5290628c8c6290628ca46291028c646291021464629063146462900629c628c406290621440629063144062908314406294881240631488145481440629c88144062948314546314831240031483146203148310a2031483880c520c42880c520c628a8c539102880c529102880c6290628800629062890628c8c5290628c8c629c628ca46290628c6462906214646291081464629006291028c546291021440629c6314406290831440629483144063148314403144062908314406294e814406314881440a31483146203148310a203148331483145403148314620314e310a203148340a203148440a20314a418a2030a203148818a203148718a20314a418a2a318a418a20018a418a31018a4408a418a20318a440a20018a740a31018a418851018a418c51018a420c51518a3144062908314406294e814406314881440a31483146203148310a203148331483145403148314620314e310a203148340a203148440a20314a418a2030a203148818a203148718a20314a418a2a318a418a20018a418a31018a4408a418a20318a440a20018a740a31018a418851018a418c51018a420c51518b1018a418851018a418c51518a722051018a522051018c520c51000c520c5120c51918a520c51918c538c51948c520c518c8c520c428c8c5221028c8c5200c5220518a8c522042880c538c62880c521062880c529062880c629062880e3126462948314646314831465231488146323148810a323148318a3231480314e3146203148310a203148318a203148418a20314a440920318a440a2a40a20314e440a20314a418a2a318a418920018a418a31018a418851018a4198a718a20018a418931018a440851018a440c51018a420c51518a520c5101851018a718c51518a420c51018a520c51018c522051000c522051480c520c453a051018c520c51000c520c51880c520c424a8c520c62880c521102880c58a8c538c42880c522102480c521062880c529062880c6290628800629062899a460830719a460821719a4609ef799ef63041719a423049719ad3b04171981719a418d81719a47bd8f799ed20d89718cd20d81838cd221810b8cd3a18d2204c718cf7bdec7b8cd20c4c638cd20c42638cd20c62638cd21c62638cd7b0cf7bde20b0cd20d020b0cd211020b0cd690620b0c6690620b18669c62490620b8cd690620b8c6690620c1c6690620a5c669102105c66910f7bde67bdc661102085c661062125c661063105c661083105c6631ef7bde6330e810603125c66b188105c66b588105c6335831060f33d8f7bc2e335831082e335830b0cd20c420b0cd38def7b0cf790620b0cd691020b0c6691020b18669062091020b8cd7bdef7bcc6690620b9c6690620860669062105c669068105c6691e663def7860661d02105c661103105c661083105c663083105c633083105c3105c66b183105c66b583105c633588105ce33588104303358313def33d8f3348c105ce334ec104303348c1082e3348c6082e3348f63def33da46082e3302e334884302e334e41b02e335a41b02e319ef7b1ef719a41b021819a41b1a41898e319a71898e719a44098c799ef7bc4c719a418c4c719a420c4c719a20c0cd231820b8cd211820b8cd7bd8f7bcc6691820b9c669182485c669d826906c0b8c66906c0b9e67bdec7a5c66906c6060669068605c6690e8605c66b1c6691027b1e67bde3131c669083131c66b483131c633483131ce334e3131ef7bd867b48310586334881058c334881042c334831082c334831892c334ee334831042e3348310830334831882e334844092e335a44082e319ef7bdef4082e330841882e331841892e319841882e719841882f7998f7bc4181987419ac1892e719ac40821719ac40841819ac1bdef799ec60c41719ad60c4171883105866b4e31058633def7bd8c334831042c334881082c334881882c3348e33488105ef33def7882e334831882e3348418830335a41882e319a44082e7bdef331e740830331844082e319841882e7198418821719841884171984199ac1882e719ac18821719ac18841719ac42041719ac60c41819af63def79841719a463041719a723041819ad23041718cd2304173ccf7b1ef0b8cd2304d22181718cd3a181738cd20d810b8cd20d8c7bccf7bc6c0b8cd2106c0c0cd638cd20c42638cd38d02638cd23def63ccf69062638c669062639c66906260c41719ac60c41719ad60c41718cd62041738cd620410c0cd60c4f7bccf63ccd23041738cd3b0410c0cd230420b8cd231820b8cd23d8f7bccf691820b8cc0b8cd2210c0b8cd3906c0b8cd6906c0b8c67bdec7bdc66906c086066906c69062638c669c62639c669102631e67bdef131c669063131c669083131c668586690621058669c6f7bd867bc83105866b48810586334881058c3348310488105c66bdef7bde633483105ce3348310430334831082e334834082e3348f331ef7bc30330e81082e330881882e330841882e331841882e319841882e20c41719ad20c41718cd20c41838cd20c414b8cd220420b8cd221ef7bccf7b8cc220410b8cc20c424b8cc20c620b8cc210620b8cc63def7bcc661d020c0624b8cd631020b8cd6b1020b8c66b0620c1e67b1ef785c66b062105c66b066691820c1c669182085c6691827bde67bd8c105c66908c125c66b4ec105c6605c669063605c6691ef63de67b483625c6334836060e334886042e334e863488131c633def7b1ee334831318e334831098e334831898e334871898e335ec33def7882c334834082c334844082c335a41882c319a41882c619a7189266b0620b9c66b062085c66b062105c66b108105c66b183106066bd8f7bde6105c66918c105c669c8c106066b48c105c63348c105cf33dec7bc2e3348c13488605c6334e8605ce334836042e33483631ef33def1b02e334841b0303358e334831098e334e34098e3348f7bd8f33da41898e319a41898e719a4189841882c335a71882c319ef7bdec619a418821619a440841619a440c41619a4719a44082f799ef7bc41719a418c41719a420c41819ad20c41718cd2204173def7998f3a0418198c22041718cc20c41738cc20c410b8cc20c420b8cc20dc669062085c6690621060669063105c669088125c66b488105c633def7bde8105c661083105c663083125c633083105ce33083105ef331ef78830330e833583125ce335881042e3358810830335837bdef33d8c1882e335ac1882e308303348c6082e334846082e335ef63def319a46082e719a460921719a7609a41b02e319a41b02e799ef7b1e9719a41b181819a41a181719a43a181719ac719a4409ec799ef78c4c719a420c4c719ad20c4c718cd20c4c738cd38c4c7bdef619ed20c41618cd22041630cd220410b0cd20c420b0cd20c624b0cd3b483605c633def63dee3348360430334836302e334884302e334e41b02e3358f33def7898e334831898e334841898e335a41898e319a71898e719a4409841882c335a44082c319a44082c619a418821619a418841619a71bdef619ef719a418821819a418841719a41a041719a422041719af7bdef798cd20c4170c417198420c417198c20c41718cc20c4173ccc7bdef0c0cc3a0420b8cc220cd62041738cd620410c0cd60c4f7bccf63c620b8cd630620b8cd6b0620b8c20b8cd231820b8cd23d8f7bccf691820b8c6691820b9c669d820860669182335831060f33d8f7bc2e335831082e335831892e3358c4082e335ac4082e33def33dec6082e334846092e335a76082e319a460830719a460821719a4609a41b12e319a41b030719a443021719a743181719a418d81719a47bd8f799ec719a41884c719a418c4c719a438c4c719ad2204c718cf7bdec7b8cd20c4c22041619ad20c41618cd20c41630cd38c497b0cf7bde20b0cd20d020b0cd238cd20c414b8cd220420b8cd221ef7bccf790620b8cd690620b8c6690620c0620b8cc210620b8cc63def7bcc661d020c1c661102085c661062125c661061719a41b18f799ef78d81719a420d81819ad22181718cd3a181738cd20d817bdec799ed20c4c718cd20c4c738cd20c4c638cd20c42638cd38d02638cd230cd20c410b0cd220420b0cd220620b0cd210620b0cd69c620b0c67bdef7b0620b8cd210620c0cd690620b8c6691020b9c6691020bde67bdef105c669066610620b9c661062085c661062105c66106f7bde663ce81060663088105c6105c66b108105c66b183106066bd8f7bde633583105ce335831042e335831348c105c63348c105cf33dec7bc2e3348c1082e3348c6082e334e46083033441819ac1bdef799ec60c41719ad60c41718cd60c49738cd620410b8cd6204f7b1ef798cd23041738cd230490b8cd3b0420c0cd231820b8cd211820b8cd4b8cd20d8c0c0cd20d0c0b8cd21d0c0b8cd6906c0b8c66906c0b9e67bdec79062638cd69062638c669062639c669c62631c6691027b1e67bde3131c66918669102085866906210586690631258669def7bd867b483105863348810583105c669088125c66b488105c633def7bdee334831042e33483108303348333083105ce33083105ef331ef78830330e84082e330841882e331841892e331c669062131c669063131c6690e3131c66b488131c633def7b1ee3348313088105866b48310586334831058c334e3125ec33def7882c334834082c3348e334831052e334881082e334887bdef33de41882e335a41882e319a4188301882e330841882e3318f7bdef31987408307198440821719841884971984199ac18830799ec7bde1719ac18841719ac18c49719ac62041719ad62041719ef799ef63041719a423049719ad3b041718cd23041838cd230410b8cd2304d20d89718cd20d81838cd221810b8cd3a18c0b8cd20c6c0b8cd23dec7bccf1882e330841882e331841882e319841882e7998f7bde1819874084171984419ac4082e719ac40821819ac189ef799ec78c41719ac60c41719ad60c4171841719a463041719a47b1ef799ed23041718cd23041738cd3b0410c0cd2304d20d81718cf7bd8f7b8cd20d810c0cd20d8c0b8cd2210c0b8cd3906c0b8cd63ccf7bde2638cd20c62638cd21062638cd69062638c669c62639c669102610620b0cd691020b0c6691020b1866906208586690621058669c6f7bd867bdc6690620860669062105c669068105c669088105c66bdef7bde633483105c41898e335a41898e319a41898e719a71898c719a4409ec799ef78c4c719a4619a440821619a418841619a418c49619a77bdef619ed20c41618cd2204160c41719a422049719ad22041718cf7bdef7b8cd20c410b8cd20c420c0cd20ccc20c41738cc20c417bccc7bde20c0cc3a1020b8cc210620b8cc610624b8c20c0cd60def7bccf630620b8cd6b0620b8c66b0624b9c66b102085c66b1027bd8f7bcc6691820b9c669182485c669d82106066918c105c66908c105c66a5c66906c6060669068605c6690e8605c66b483605c633483605cf33def63ccc20c41738cc20c410b8cc20c420b8cc20def7bccc79d020c0cc611020b8c20b8cd621020b8cd630620c0cd7b1ef7bcc66b0620b9c66b062085c66b062691820b8c6691820b9e67bd8f785c669182105c66918c105c669c8c10606685c66906c63de67bde3605c669083606066b488605c6334e8605ce33483605ef7b1e67b483131c633483131ce334831318e334831098e334e34098e3348c334831042c334881082c334881882c334841882c335a71882c319ef7bdec1882e3348418830335a41882e319a44082e719a44082f799ef7bc41719a41948c104063148c104003148c104203148c109203148c60820314e46082a314203148363020314831b12a314841b020314a443020318a743020018a41b02440980314a418980318a418980018a41898c018a41884c518a71a04c018a4618a418821618a440841618a440c41618a420c41618a538c49618c520c4160c41018a420c41018a520c41018c522049028c522041080c538c42080c520ccc20c41500cc20c49080cc20c42080cc20c62080cc21d02080cc61102080c2080c562102080c563062080c52b0620a8c62b062080062b0620a4062b0623316b5ad603308310420330e810820330881882a330841882033184188203082a31583188203158c18820314ac18820318ac408205996c5ad61018ac188a460820318a460820018a76082b5996b62c41018a463041018a423041018a1018a41b18b5996b5a181018a720d81018a520d81018c520d81028c520d8120c4c018a520c4c018c538c4c500c52204c600c522042600c520d6b62ccb5b0c520c410b0c520c420b0c538c620b0c522d6b5b0cb291020b0c6291020b102080c5211020a8c55ad6b5acc62906208006290620840629062104062906c314e31042c314831082c314834082c314844082c314a41882c318a41882c18820314e418820314a418820318a418820018a418821018a440841518a44198740820019844082151984188410198418c410198420c410198c20c4101841018ac18c41018ac62041018a562041018c560c41028c560c41080c560c453b041018c523041500c523041080c523042080c523182080c521182080c5080c53a18c080c520c6c080c52106c080c52906c0a8c62906c080062910c09c62628c529102600c6291026000629062630062906213006290631300629041018ac18c41018ac62041018a562041018c560c41028c560c41080c560c453b041018c523041500c523041080c523042080c523182080c521182080c5080c53a18c080c520c6c080c52106c080c52906c0a8c62906c080062910c09c62628c529102600c629102600062906263006290621300629063130062918629c6208586290621058629068105862908810586294831058631483105831040629c8310406294831040631483104003148310420314881082a31488330e810400330881042a330831082033083188203308418820331841882030c41018a420c41018a520c41018c522049028c522041080c538c42080c520ccc20c41500cc20c49080cc20c42080cc20c62080cc21d02080cc61102080c2080c562102080c563062080c52b0620a8c62b062080062b0620a4062b06229182080c62918208006291820840629182124062918c1040629c8c10546284062906c60406290636254629083604062948860406314e860400314836048813006294831300631483130003148313180314831098a314e3409803148c314831042c314881082c314881882c314841882c314a71892c318a41882c20c4c018a520c4c018c538c4c500c52204c600c522042600c520d6b62ccb5b0c520c410b0c520c420b0c538c620b0c522d6b5b0cb291020b0c6291020b102080c5211020a8c55ad6b5acc62906208006290620840629062104062906662d6b5ac06610620840661d0210406611031054661083104066308310406105462b063104062b183104062958310406315881040b32d8b5ac20315831148c104063148c10400314ec1056b32d6c588203148c60820314846082031420314836316b32d6b43020314e41b020314a41b020318a41b020518a41b02c314831056c32d6b5882c314884082c314841882c314a41882c318a71882c188203148418820314a418820318a418820018a440821518a44096b5996b599844082051984188210198418841019841ad6b5998b20c410198c3a04101841018ac1a041018ac62d6b5996560c41018c560c41500c560c41080c560c4b5b16b598c523041000c523041080c523042080c523182080c521d82080c5080c520d8c080c520c6c080c52106c0a8c52906c080c65ad6c5ac0629d0c09102600c529102600c629062601665ad6b630062906213006290631314629c2a314836302031483430203148743020314a41b020318a41b020018a41b02418980314a418980318a418980518a71898c018a44084c018a440c4c018a4618a440821618a418841618a418c41618a720c41618a520c41618c52204160c41018a422041018a522041518c538c41000c520c41080c520c42080c520ccc20c41000cc20c41080cc20c42080cc3a102080cc210620a8cc61062080c2080c560c620a8c563062080c52b062080c62b062080062b102084062b10229182080c62918208006291820840629d82105462918c104062908c104062882031583188203158c18920314ac40820318ac40820018ac18821518ac188a460920318a760820518a460821018a460841018a463041018a423041018a1018a443181018a740d81018a420d81018a520d81018c520d89500c520d8120c4c018a538c4c518c52204c000c52204c600c520c42600c520c62600c5230c520c414b0c538c420b0c520c620b0c5211020b0c5291020b0c6290620b1020a8c521c62080c529062080c629062080062906208406290621240629106610620800661d0208406611021054661063124066108310406630831040620c4c018a538c4c518c52204c000c52204c600c520c42600c520c62600c5230c520c414b0c538c420b0c520c620b0c5211020b0c5291020b0c6290620b1020a8c521c62080c529062080c629062080062906208406290621240629106610620800661d02084066110210546610631240661083104066308310406104062b063104062b1831240629588104063158810400315831042a315831148c12406314ec1040a3148c104203148c108203148c608203148460820314203148863020314e81b020314841b020314a41b020318a41b12a018a41b02661062080066106208406610621040661d081040661083105466308310406104062b063105462b18310406295831040631583104003158810420315881148c104063148c104003148c10420314ec1082a3148c6082031484608203142a314836302031483430203148743020314a41b020318a41b020018a41b02418980314a418980318a418980518a71898c018a44084c018a440c4c018a4618a440821618a418841618a418c41618a720c41618a520c41618c52204160c41018a422041018a522041518c538c41000c520c41080c520c42080c520c41018a418c41018a422041018a522041018cb5ad6b580c520c41080c520c4520c41018c520c4102ccb5ad6b080c520c42080c53a102080c521062080c55accb5ad62080c520c62080c521062080c529c62080c629062080062910209062080c529102080c62910208006290620840629c625ad665ad631040629006290620840629062104062906b5ad665ace81040629483104063148310403104062916b5ad6659483104063148310400314e3104203148810820314883148810400314881042031483108203148318820314e4188203156b5ad6b31062080c529062080c6290620800629102084062910212406290631040629c0629062084062906210406290631240629083104062948810406314e8104081040629088124062948310406314831040031483104203148310820314e331483104003148310420314881082031488188203148418820314a7189203082031483188203148418820314a418820318a440920018a440821018a7188a440820318a418820018a418921018a418841018a418c41018a43a041018a9018a418841018a442041018a420c41018a520c41018c520c41000c538c4129062080c629062080062910208546291025ad665ad631040629083104062840629062104062906b5ad665ac8310406294e810406314881040a314831056b5ad66594831040631483105403148310420314e31082031483408203148031483104203148810820314881882031487188203156b5ad6b318a41882018820314841882a314a4188203196b5ad6b018a740821018a418841018a4198a4188205996b5ad61018a418841018a418c41518a722041018a52204101841518a442041018a420c41018a520c41018c538c41000c520c415accb5ad61518a418841018a418c41018a422041018a522041018c520c49000c538c4120c41018a520c41018c520c41028c520c49080c520c42080c522102080c5380c522041480c522042080c520c62080c521062080c529062080c629c620a862080c521062080c5291020a8c629102080062906208406290621240629c6629062080062906208406290621040629068124062908810546294e3104061040629103105462908312406294831040631483104003148310420314e8114831240631488104003148810420314831082a31483188203148718820314c520c41000c520c41080c522042080c522062080c521062080c529c62480c2080c520c62080c521062080c529062080c62910248006291020840629c6229102080c62906208006290624840629062104062906310406290e8104062a40629062104062910810406290831040629483104063148310400314e3104831040629483104063148310400314881042031488109203148318820314e03148310420314831082031483189203148418820314a440820318a740820408203148440920314a418820318a418820018a418821018a418841018a7180c520c41080c520c42080c520d6b5accb59d02080c529062080c62906208062080c522d6b5accb29062080c6290620800629c6208406291021040629106291020800629102084062906210406290631040629c83104062ad6b5ad661040629063104062908810406294881040632d6b5ad603148310420314831148310406314831040b32d6b5ac203148310820314e84082031484188203156b32d6b5882031483188203148418820314a718820318a418820018a44082418820314a440820318a440820018a418821018a71896b5996b58c41018a4188203148418820314a44082a318a440820018a418821018a418849018a7198a418820018a418821018a418841018a41a049018a422041518a538c4101841018a440c41518a420c49018a520c41018c520c41000c520c41080c53a04520c49018c522041000c522041080c520c420a8c520c62080c521c62080c50a8c520c42080c520c62080c521102080c529102080c6290624800629c6209062080c529062080c6290620814629062484062906210406291081040629c06291020a4062910210406290631040629083104062948310406314e310543104062908310546294831040632d6b5ad60314e810420314831082031483314831040b32d6b5ac203148310820314831882a314e440820314a4408203082a31488408203148418820314a418820318a718820018a41882b5996b5aca418820318a418820018a440821518a44096b5996b58c41018a420c41018a1018a418841018a41ad6b5996b20c41018a53a041018c522041028c520c415ad6b5996520c41018c520c41500c520c41080c538c42080c520d02080c5200c520c41080c522042080c522062080c521c62080c55ad6b5acc62906208020314831082031483188203148740820314a440820318a41882a018a41892418820314a41882a318a418820018a718829018a418841018a442041018a4018a440821018a440849018a418c41018a720c41518a520c41018c520c4100c49518a420c41018a522041018c53a041000c520c41080c520c42080c520cc520c41000c520c41080c520c420a8c538d02080c521102480c529062080c2080c522062080c521062080c529c62480c6290620800629062085462910229062080c62910248146291020840629c621040629063104062908310406294831040631483104003148310420314e8108203148818820314841892031420314831082031483188203148718820314a418920318a440820018a44082440820314a440820318a418920018a718821018a418841018a418c41018a4018a418921018a418841018a442041018a720c41018a520c41018c520c4100c41018a420c41018a520c41018c538c41000c522041480c522042080c520cc522041000c520c41080c520c42480c538c62080c521062080c529102080c2080c520d02480c521102080c529c62080c62906208006290620840629062314e310400314831056b32d6b5882031488408203148418820314a41882032d6b32d6b188203148418820314a418820318a418820018a440821018a4408a740820318a440820018a418821018a418841018a41ad6b5996b20c41018a1018a718841018a41a041018a45ad6b5996520c41018c520c41000c520c4138c41018ab5ad6b598c520c41000c520c41080c522042080c522062080c5200c53a041080c520c42080c520c62080c521062080c529062080c65ad6b5ac62080c539102080c529102080c629062081665ad6b5840629062104062906538c41018c520c41000c5220415accb5ad62080c520c620a8c521062080c5080c538c4b5accb5ac62080c521062080c529102080c629102080062906209d02080c529062080c62906208006290620854629062104062906b5ad665ad4629c6208406291021040629103104062916b5ad66594831040631483104031040629c83104062ad6b5ad663148810540314881042031483108203148332d6b5ad603148310420314831082031483188203148440820314a44082a30820314e840820314841882a314a418820318a4188205996b5ad61018a4188c520c41000c520c41080c520c420a8c538d02080c521102480c529062080c2080c522062080c521062080c529c62480c6290620800629062085462910229062080c62910248146291020840629c6210406290631040629083104062840629062104062906310406290e8104062948810406314831054031483124831040629483105463148310400314e3105203148310820314884082031480314881042031488109203148318820314e41882a314a418820318a4188201892a3148418820314a440820318a740820018a418821018a418841018a418c41018a420c41018a520c41018c538c41000c522041480c522042080c520cc522041000c520c41080c520c42480c538c62080c521062080c529102080c2080c520d02480c521102080c529c62080c6290620800629062084062906229062080c62906208006290620840629d0210406291031040629083124062840629062104062906310406290e3104062948312406314881040031488104881040629488104063148312400314e3104203148310820314831882031480314831242031483108203148840820314e418820314a418820318a418820⟩
set_option maxHeartbeats 5000000 in
private theorem valid5040 : ∀ r ∈ rows5040, Valid cfg 5040 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_3 : ∀ i ∈ List.range' 3 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_6 : ∀ i ∈ List.range' 6 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_9 : ∀ i ∈ List.range' 9 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_12 : ∀ i ∈ List.range' 12 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_15 : ∀ i ∈ List.range' 15 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_18 : ∀ i ∈ List.range' 18 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_21 : ∀ i ∈ List.range' 21 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_24 : ∀ i ∈ List.range' 24 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_27 : ∀ i ∈ List.range' 27 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_30 : ∀ i ∈ List.range' 30 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_33 : ∀ i ∈ List.range' 33 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_36 : ∀ i ∈ List.range' 36 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_39 : ∀ i ∈ List.range' 39 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_42 : ∀ i ∈ List.range' 42 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_45 : ∀ i ∈ List.range' 45 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_48 : ∀ i ∈ List.range' 48 1, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
private theorem run5040 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 720 a b c keys720) : Match 5040 a b c keys5040 := by
  apply refine step5040 h bad (by decide) (by decide) valid5040 _ old
  intro i hi
  change i < 49 at hi
  by_cases h0 : i < 3
  · exact test5040_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h3 : i < 6
  · exact test5040_3 i (by simp only [List.mem_range'_1]; omega)
  by_cases h6 : i < 9
  · exact test5040_6 i (by simp only [List.mem_range'_1]; omega)
  by_cases h9 : i < 12
  · exact test5040_9 i (by simp only [List.mem_range'_1]; omega)
  by_cases h12 : i < 15
  · exact test5040_12 i (by simp only [List.mem_range'_1]; omega)
  by_cases h15 : i < 18
  · exact test5040_15 i (by simp only [List.mem_range'_1]; omega)
  by_cases h18 : i < 21
  · exact test5040_18 i (by simp only [List.mem_range'_1]; omega)
  by_cases h21 : i < 24
  · exact test5040_21 i (by simp only [List.mem_range'_1]; omega)
  by_cases h24 : i < 27
  · exact test5040_24 i (by simp only [List.mem_range'_1]; omega)
  by_cases h27 : i < 30
  · exact test5040_27 i (by simp only [List.mem_range'_1]; omega)
  by_cases h30 : i < 33
  · exact test5040_30 i (by simp only [List.mem_range'_1]; omega)
  by_cases h33 : i < 36
  · exact test5040_33 i (by simp only [List.mem_range'_1]; omega)
  by_cases h36 : i < 39
  · exact test5040_36 i (by simp only [List.mem_range'_1]; omega)
  by_cases h39 : i < 42
  · exact test5040_39 i (by simp only [List.mem_range'_1]; omega)
  by_cases h42 : i < 45
  · exact test5040_42 i (by simp only [List.mem_range'_1]; omega)
  by_cases h45 : i < 48
  · exact test5040_45 i (by simp only [List.mem_range'_1]; omega)
  exact test5040_48 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+6=2^a*3^b*19^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=1 ∧ b%12=1 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  have h720 := run720 h bad h240
  have h5040 := run5040 h bad h720
  obtain ⟨i,hi,_⟩ := h5040
  exact Nat.not_lt_zero i hi
end D6


namespace D7
private def cfg : Config := ⟨7,7,19,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x49085⟩
private def rows12 : List Rule := [
  .div 5,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x410410410000000000082084082000000000410410410000000000083082082000000000410410410000000000082082081000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨1,6,0x529⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,10,[31,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],133,0x161f2054da76220c210c111b96ca813e1a⟩,
  .pool ⟨31,19,[31,17],[2,3,5,7,11,13,19],8,0x82⟩,
  .pool ⟨31,24,[31,2,3,17,23],[5,7,11,13,19],45,0x55898f135e⟩,
  .pool ⟨61,38,[61,2,17,23,29,37],[3,5,7,11,13,19,31],880,0xd191cb195a6799e911d6b4bd4b79547109015b9c5590655990d71dc33192173108531033b14561581139e13a1e93116b7388f135a3535295958b591e239dad1192f0b90f3910350d451b9811942119d093198771d613354c135473b501211c553da57a5ad7112f33ccb531a71316⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x80001a000280006001000060000d0000200⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨2,7,0x14ca02829⟩
private def rows120 : List Rule := [
  .pool ⟨41,14,[41,2,7],[3,5,11,13],57,0x1a60a0132014196⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,2,0x24⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 1 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨0,8,0x0⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨181,33,[181,3,11,23,29],[2,5,7,13,17,19,31],760,0xa2a00a2a800280022a0a8208a0288080202822088080080888a20888220820288a080a00a08020028280aa000022000000880000aa02828008020a00a020a22808208822208a2220200202208828080202280a2082a0a880028002a8a00a8a⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0xc⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 2 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+7=7^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  obtain ⟨i,hi,_⟩ := h240
  exact Nat.not_lt_zero i hi
end D7


namespace D8
private def cfg : Config := ⟨8,2,19,1,3,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨0,4,0x0⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .div 7,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x30a28c28a00000000045145145100000000028c28a30a00000000045145145100000000028a30a28b000000000451451451000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+8=2^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=3 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  obtain ⟨i,hi,_⟩ := h12
  exact Nat.not_lt_zero i hi
end D8


namespace D9
private def cfg : Config := ⟨9,3,19,1,2,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x8a046⟩
private def rows12 : List Rule := [
  .div 5,
  .div 7,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x450410c10000000002082082080000000000c10440410000000002082082080000000000410c1042000000000208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨0,6,0x0⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],200,0xa88a00a20aa88800a22aa08800220aa88a00222aa08a00a22a⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨31,2,[31,2],[],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩,
  .prime 31,
  .pool ⟨61,14,[61,2,7],[3,5,11,13],271,0x120d15b642339a3861580a1fc6dd5e913d437685449c07afe579e3a633bd92574fb6⟩,
  .pool ⟨31,8,[31,2],[3,5,7],271,0x120d15b642339a3861580a1fc6dd5e913d437685449c07afe579e3a633bd92574fb6⟩,
  .pool ⟨31,7,[31,7],[2,3,5],793,0x12d020a252081880644c112020006092460020080020180882a080f008c000022017044708b2850016000655a08040086844885840080416a98001a0028534438883a01100000c403c0415044060100040100189241800101220c8980460412914102d2⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0x9000800000000700060005000040004000300000000200010⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+9=3^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=2 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  obtain ⟨i,hi,_⟩ := h60
  exact Nat.not_lt_zero i hi
end D9


namespace D10
private def cfg : Config := ⟨10,2,5,19,1,1,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨11,4,0x4bba5b899239077617ab5455293833671⟩
private def rows12 : List Rule := [
  .div 7,
  .div 13,
  .div 3,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x100000e00002222222222220000010000012222222222220001000001002222222222220d0000010000222222222222000001000001222222222222000100000100222222222222222222222222001000001000222222222222100000100000222222222222000010000010222222222222001000001000222222222222100000100000222222222222000010000010000001000001222222222222000c00000100222222222222010000010000222222222222000001000001222222222222000100000b0022222222222201000001000022222222222222222222222210000010000022222222222200001000001022222222222200100000100022222222222210000010000022222222222200001000001022222222222200100000100000010000010022222222222201000001000022222222222200000100000a222222222222000100000100222222222222010000010000222222222222000009000001222222222222222222222222000010000010222222222222001000001000222222222222100000100000222222222222000010000010222222222222001000001000222222222222100000100000080000010000222222222222000001000001222222222222000100000100222222222222010000070000222222222222000001000001222222222222000100000100222222222222222222222222001000001000222222222222100000100000222222222222000010000010222222222222001000001000222222222222100000100000222222222222000010000010000001000001222222222222000100000600222222222222010000010000222222222222000001000001222222222222000500000100222222222222010000010000222222222222222222222222100000100000222222222222000010000010222222222222001000001000222222222222100000100000222222222222000010000010222222222222001000001000000100000100222222222222010000010000222222222222000004000001222222222222000100000100222222222222010000010000222222222222000001000003222222222222222222222222000010000010222222222222001000001000222222222222100000100000222222222222000010000010222222222222001000001000222222222222100000100000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨154,6,0xa3bef48fb717ec4eefa2fbf45ef70bbe88e34178f42e372f5c48d740b5dc8cba0b2fad7b29ded617b5b5bfaa6f89dbca46fbb58d6a632858eea57e915e21572a92fa14b821e6c279b39b54b6de21b6056d239854555e09560b4922124e9f9083e42ced39bb723ed683b666e1cb355a9d508f2660c992bdcc7f7607dd8deb91facc4ebc07af0ddf62b7c07df9137ccdd3c2b4c04d332b1f07c76131c01c7da5dc6377a81deac6b4a5af666b181ac6c5f4997f635f7817dec53a994d2353db11de947a8d1d2047eafd628f5b8bd6eee9ea3a4a2e92bb7568dd8bb44abd159744a8c5b971562c5429d5c475105d68a6941da5c169a1d77415dd35444751a11450d45d29168145c95cda2730ad9e68670a16ce25b3b93da84f9b90da5430890d4cf3e27ce03e72039ec9db8036ec6cfe033f8cc38270c86c3ab7c52af1793c6aae5d9395e1e51ab66a7d9d87676dcd19f36a4cd487352dc179f0464c1⟩
private def rows60 : List Rule := [
  .div 11,
  .prime 31,
  .pool ⟨31,5,[31,5],[2,3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],31,0x68818116⟩,
  .pool ⟨61,3,[61,3],[2],279,0x4020108804020100804028900804060100804020100844020100a04020100804020a⟩,
  .pool ⟨61,8,[61,2],[3,5,7],31,0x68818116⟩,
  .pool ⟨61,2,[61,2],[],31,0x68818116⟩,
  .pool ⟨61,4,[61,2],[3],31,0x68818116⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],279,0x7ac8a194980782258684457bd44c0c26813c816430322bdea22161a441e0192985135e⟩,
  .pool ⟨31,21,[31,3,7,17,19],[2,5,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,8,0xa60000000000000200a5000000000000a40000000000000100000000a300a20000000000000100a1000000000000a000000000010000000000000c009f0000000000009e009d000000000c0000000000009c0000000000009b00010000000000009a000000000b000100000000000099000000000000020098000000970000000000000100000000000096000200000000000095000000009400930000000000009200000000000091000100000000900000000000008f00010000000000000c0000000000008e0000000001008d0000000000000c008c0000000000008b00000000020000000000008a000b000000000000010089000000000000000a000100000000000088000000000000020087000000008600000000000085008400000000000083000000000000010000000082000700000000000001000800000000000002000000000100000000000009000800000000000081008000000000020000000000007f0000000000007e0001000000000000070000020000000000007d000a000000000000010000000000007c000000007b00010000000000007a00790000000000007800000000080000000000000200770000000000000700010000000076000000000000750000000000000100090000000000000800000000010007000000000000020000000000007400730000000000000002007200000000000071000100000000000070000000006f00000000000001006e0000000000006d006c000000006b0000000000006a00000000000069006800000000000001000000006700660000000000000100000000000065000200000000010000000000006400630000000000006200000000000061000000010060000000000000020000000000005f005e000000005d0000000000005c005b000000000000010000000000005a000000005900010000000000005800570000000000005600000000550000000000000200540000000000005300010000000052000000000000510000000000000100500000000000004f0000000002004e0000000000004d00000000000001004c000000004b00000000000001004a000000000000020000000000004900000000480002000000000000470006000000000000010000000046000000000000450001000000000000440002000000000100000000000006000000000000430042000000000000410000010000000000004000020000000000003f0000000000003e0000000002003d0000000000003c00010000000000003b000000000600000000000001003a0000000000000200390000000038000000000000020000000000003700360000000000000100000000350034000000000000010000000000000600330000000000000001000400000000000002003200000000000031000000000400000000000030002f0000000000000100030000000005000000000000010000000000002e00020000000000002d000000002c00020000000000002b000000000000040001000000002a0000000000000300010000000000002900000000000028000000270026000000000000010000000000000400020000000001000000000000030004000000000000250000000000002400000000020023000000000000050001000000000000220000000004000000000000010021000000000000020020000000001f0000000000001e0000000000001d00030000000000000100001c0000000000001b00010000000000001a000000000000020000000001001900000000000002001800000000000017000000000200000000000016001500000000000001001400000000130000000000000100000000000012001100000000000010000000000f00020000000000000e0000000000000d0001000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_8 : ∀ i ∈ List.range' 8 3, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 11 at hi
  by_cases h0 : i < 8
  · exact test60_0 i (by simp only [List.mem_range'_1]; omega)
  exact test60_8 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨408,7,0x697fbb447dda5f76d11bb81df5c077ae0775f01dafc9af5a8d7af22fd6a17ebc9ad7a8d6bf22f5ea17afe14f5b4a7af817d6d0bebe14d7b4a6bf8175ed0baf994efcc2f7e6534730ba3b1ae99cd74ec2fa6717d3b1acb9cd65ec2f2e71797817e984bf4e023a6111d3817cb84be5e0232e11197b17e3d8471ec5f176118bc91e3a88f1f20b8ea05c7c91c5a88e2f20b16a058b45675a23bad1595e88eaf153758a23ac54d5e288af5d969ae534d7652eb9497ed369ba9b4fb11a6e88d3ed34bba9a5fb112ee8897bd069a2834ef05a6882d3bd04ba2825ef052e88297ed063f60b1fb4117d828b4177aa043d505d72810b989d6e88eb76239ba21cdd89d5088ea862394221ca1a146894a346815a250ad1a144a94a2568152a50a95e9168b88b47a09a2e04d1e914ab88a57a092ae0495b9a62dc5b16e691371689c55eea6af7711bba98dddc55d0a6ae8711b4298da1ddbe8ee674776f2bb9995ad8e8d64f46b632b59395a9cf398e79ea37ce61be7a9cd598e6aea375661babd90f3b0879f607cec03e7d90d5b086af60756c03ab61cedb06f6d8733ec1b9f016ed803f6c05b3e00f9fc13eda49f6f013b6909dbc13cfa49e7f0133e9099f19ce78c6f3c6732631b93919e18ccf0e42b86315c3919c38cce1e42b0e31587313e198270cc4f0e60987790e180870de0786003c3790c380861de070e003879d87392c39e725ce492e79d85592c2ae72556492abe5573b6ab9f919ced8ce7e5555b6aaaf91956d8cab0cf7386039c33d56180ab0db6d86636c36d3e1989f9d56dce336e7553f38c9f3cf6d9e036cf3d3e7809fe5b61b6db0f93186d98c3e5b43b6da1f9310ed9887b5861da4b0ed610f69287edaf8bad7c7b2fe2e97f1edadabad6d7b2f6ae97b5bd7f8a2bfc6f23e2891f1bd7daa2bed6f236a891b55d1f8ae17c57476ab85b55ddf2ae779577752b9da9ed7f2f64797b5f53d91a945de6a277351772289d9115ae68a5f3456b2229791b13789c9bc6c11e2708f1b135a9c9ad6c116a708b5810788483c6005e2102f18105a8482d60056a102b551972a8539546552a14a99967290b39661dca40ee59965490b2a661d5240ea9b1072d80b96c4153602a96906cb40b65a413ad029de1c66b4e3378359ad1acde1c48b4e24783522d1a918166684b33601d9a10ecd8164884b24601d2210e9151366a8233544d22a089169960b45305a650ad1485dd477ee2bbf75167b8ab3c5d5fe272ff1750789c83a1bf794dfbe833de519efa1bd994dece83366519b3d18ebe84f5f46337a139b895df88aefe21b7e20dbf895c188ae0e21b0620d833d3f69e27b4f4f62789b1e53f0f2278794f4bc89a5b50f0da0f86d434b683a5e5ce4b6e72793792d9bc9e5cc6b6e6379371ad9b8d0d6e4863f2435b1a18f8d9d0e492872670792483c99d0c69286367071a4838d9dcdece6ef67730339b81b56de9eb6f6d1f7a78fbdb56c09eb606d1f0278f810d3de8626f434f0218981⟩
private def rows120 : List Rule := [
  .pool ⟨41,2,[41,2],[],31,0x121d47b6⟩,
  .pool ⟨41,2,[41,2],[],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,5,[31,5],[2,3],123,0x10000124014004012182110536⟩,
  .pool ⟨31,5,[31,5],[2,3],41,0x1b382b50736⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .prime 41,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,8,[41,2],[3,5,7],915,0x102410820120480080002080020804014800400004c008041000800804020001221840100201040100061a0000080502002100000804500804424010800000002180802802400020010484012102400030010002c02884000010000800122110804100802004000414090002026100090116⟩,
  .pool ⟨41,8,[41,2],[3,5,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨41,5,[41,5],[2,3],31,0x121d47b6⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],279,0x4422106916120164a34170128b0c024920806926328904120909934327584b2493ea⟩,
  .pool ⟨41,5,[41,5],[2,3],61,0x1713e6940a59f23a⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨31,5,[31,5],[2,3],451,0x2000800000000000082000100001000000088000008000000000000000000000040008800000024000040000000000800000082000022⟩,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨41,11,[41,11],[2,3,5,7],61,0x1434026619900b0a⟩,
  .pool ⟨61,31,[61,17,19,23,29],[2,3,5,7,11,13,31],1155,0x20840001a64308201141020004340228908009801a0034892502900424c001024108221808301028000220b0400000412400480000880802420510832180820080190026802520102034810980122420430886802000506100ca2806912086490492186d020021948228141220221a04109129008845004020000328060244a4080120182520c141168200800248b0012⟩,
  .pool ⟨41,28,[41,2,7,17,19,23],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,14,[41,2,7],[3,5,11,13],31,0x121d47b6⟩,
  .pool ⟨41,6,[41,2,3],[5],279,0x5463346d1e1f256ce757f812ab1d2369f0e96b673abfc41719c99b47a7595b3dd7fe⟩,
  .pool ⟨41,14,[41,2,7],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨61,8,[61,2],[3,5,7],451,0x100040000010010000400000000000000000010200104020000000004012000002100010116⟩,
  .pool ⟨41,31,[41,17,19,23,29,31],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],41,0x1b382b50736⟩,
  .pool ⟨41,8,[41,2],[3,5,7],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨61,3,[61,3],[2],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨41,5,[41,5],[2,3],183,0x4406824020400020424880000112420400020402416022⟩,
  .pool ⟨61,2,[61,2],[],451,0x100040000010010000400000000000000000010200104020000000004012000002100010116⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],915,0x20820000a6020080100022002020004090810c840040008001000021900200001029000000000000208000a00200041120840000008001000024340328000000840800209020000a6000886092502c021204100068220001000120008301200000060008120001000141100220a00108b0092⟩,
  .pool ⟨41,2,[41,2],[],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],427,0x54419250004488602030c2014002001403c28008015210980224000244019084a80100143c02800400280430c04061122000a49822a⟩,
  .pool ⟨41,2,[41,2],[],915,0x102410820120480080002080020804014800400004c008041000800804020001221840100201040100061a0000080502002100000804500804424010800000002180802802400020010484012102400030010002c02884000010000800122110804100802004000414090002026100090116⟩,
  .pool ⟨41,2,[41,2],[],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,20,[41,2,5,17,19],[3,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,5,[31,5],[2,3],1281,0x1b28221060300800a0002800020000032000000522000000002100000000002930010010100000886020000000400000000020080000000000010000100022082800000800000c000800000000021200b4012100000000004000c00000400000504110002000020000000000004010000000000800000010184400002020020032500000000002100000000112800000130000010000500014004030182110536⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],1435,0x5044c01003019034002042804000240810148042024241800000ca0610005012a18c800050000005000002010000080204420140430084024030006208122110002010000ca032c000800000921099083200053840700004208010420000e021ca0004c1099084900000100034c0530000804000884481046000c02402100c2028042204010000080400000a000000a00013185480a000860530000018242404201280810240002014204002c0980c00803220a⟩,
  .pool ⟨41,18,[41,2,3,17],[5,7,11,13],61,0x1ffffffffffffffe⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,9,0x204c08130204c08130aef82bbd0aef02bbb098502614098502614dd04b7212dc04b6e12db6d769b3d96c761afd76b759abd56a751a7018080602018080602018080602018080602d303f4a0fd203f460f078401e10078401e10d1687419fcf677399bcd6673197cb6572993020100804020100804c90132204c80131e04c7637198bc5627118705828160a05828160a068281a0a068281a0a06034180d06034180d0201008040201008040180c06030180c06030ce1833850ce10338304e08138104e00137f0301c0c070301c0c07030140c05030140c05018180606018180606025f8097d025f0097bbd5e6f177bb5d6e973b95c6e16fb75b6d96b130844c21130844c21b5086d221b4086ce210959825650959025631209448251209448250201008040201008040100c04030100c04030803c200f0803c200f0803c200f0803c200fb1586c15faf576b95bad566b157ab556a953a9546a14fa7536994ba50569215a40568e150a04c28130a04c2813120644819120644819020100804020100804028180a06028180a06030140c05030140c050181806060181806060e8183a060e8183a06a35168943a1506813f9f0067a019e00676019d00272009c0026e000f8303e0c0f8303e0c0502c140b0502c140b078401e10078401e10078401e10078401e100201008040201008049b4d66933994c6612f02010080402010080401838060e01838060e974b6592b954a651270249809250249009230188c06230188c062311488452111480451f8f476391b8d46631170ac582b150ac502b130a04c28130a04c28130204c08130204c081389446210f87436190b0100c04030100c04030942825090942025078341609038140600ff030140c05030140c050301c0c070301c0c07028180a06028180a060180806020180806027f3f5f8fb7d3e5f0f77b3d5e8f3793c5e0ef023b808ed023b008eb003a800e9003a000e773085ca2172085c6210180c06030180c06031038840e11038040df0507c141f0507c141f068301a0c068301a0c05828160a05828160a6f375b8db6d365b0d76b021aa086a021a6080201008040201008040180c06030180c060369345a0cf6733598cb6532590c76331588c30230808c10230008bf002f800bd002f000bb5d00572015c0056e010e078381e0e078381e068281a0a068281a0a06034180d06034180d04ad812b504ad012b304ac812b104ac012af020100804020100804018180606018180606030740c1d030740c1d030140c05030140c05020100804020100804572b558ab552a550a75329548a351285409f0e278389d0e270389b4d26530974b2552893490112204480111e040204c08130204c08130aa382a8d0aa302a8b45225108743215088341205007f3f1f4f87b091e82479091e024770803c200f0803c200f079d81e75079d01e7301808060201808060239004e20138004de010880022000880022000686c1a1b0686c1a1b05034140d05034140d0201008040201008040d06434190d0643419030140c05030140c050c01830060c01830063705cda173605cd6170b0102c040b0102c04018080602018080602351a4d06733194c8630884422110884422110b0542c150b0542c150a04c28130a04c281331048c21230048be120904424110904424110201008040201008040803c200f0803c200f0201008040201008040700c1c030700c1c032f174b85b2d164b057068301a0c068301a0c05828160a05828160a05158145505150145302010080402010080429024a209280249e09270209a082602096080301c0c070301c0c07028180a06028180a06030140c05030140c0525124904723114884302108084102100083f0180806020180806021f0f4783b1d0e470371b0046a011a0046601190c4602f170b4582b000a80029000a00027⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_137 : ∀ i ∈ List.range' 137 17, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 154 at hi
  by_cases h0 : i < 137
  · exact test120_0 i (by simp only [List.mem_range'_1]; omega)
  exact test120_137 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨180,8,0x2259e322596b9ad1a79ad12fee11cb7611cbee1153761153b289cb3a89cbb289533a8953ee898f76898fee8917768917b2118f3a118fb211173a11179ab9cb22b9cb9ab95322b9539a418f22418f9a4117224117bcb1d544b1d5bcb15d44b15d8039d50839d580395d08395dbc3999443999bc392144392180b19908b19980b12108b121c851c95051c9c851515051518cc9c914c9c98cc95114c951c8c98d50c98dc8c91550c9158c518d14518d8c5115145115b081c93881c9b08151388151b0098d38098db00915380915c6d9df4ed9dfc6d9674ed9678a61df1261df8a6167126167c661a34e61a3c6612b4e612b8ad9a312d9a38ad92b12d92b0631d306315b7ea9977ea91f1e01d31e015b96799796791fd011e95811e9d011715811719489e91c89e99489711c8971d089ad5889add089355889359411ad1c11ad9411351c1135a029dda0296528a1a128a1298859dd1059dd88596510596588d1a110d1a188d12910d129acb9d1acb95934419534411de8e9c570e9c5e8e94d70e94dac71c53471c5ac714d34714de87189707189e87111707111ace98934e989ace91134e911b859c54059c5b8594d40594db8d18940d189b8d11140d111a089c52889c5a0894d28894da01189281189a01111281111ac29b93429b9ac2941342941aca17d34a17daca10534a105e6c9e76ec9e7e6c96f6ec96fe651ab6e51abe651336e5133dab1b762b1b7dab13f62b13fda397b62397bda3903623903⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨241,16,[241,2],[3,5,7,11,13],41,0x1b382b50736⟩,
  .pool ⟨241,4,[241,2],[3],41,0x1b382b50736⟩,
  .pool ⟨41,6,[41,2,3],[5],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨241,9,[241,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨241,11,[241,11],[2,3,5,7],403,0x1805010007580101234808802042804000024002220001200024200000002182012006884410008000251102001000000c42⟩,
  .pool ⟨41,20,[41,2,5,19],[3,7,11,13,17],31,0x121d47b6⟩,
  .pool ⟨61,2,[61,2],[],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨61,33,[61,3,11,19,23,29],[2,5,7,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨41,12,[41,2,3],[5,7,11],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨41,8,[41,2],[3,5,7],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨41,8,[41,2],[3,5,7],723,0x4004100110002010016006010002024000004800120104022c145029004240104048100924140140000020905001060840020020104809b0422122104986000130482000120520412480520010c24830122110536⟩,
  .pool ⟨61,41,[61,19,23,29,37],[2,3,5,7,11,13,17,31,41],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨41,18,[41,2,3],[5,7,11,13,17],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨31,23,[31,19,23],[2,3,5,7,11,13,17],1037,0x29c4012000802006083840220180b02088863006005ed0a9e1054a0809020011134414b0d80009a5321d130102208008003304200480431a00150ec038a0502030002470a0600114120082001180008460106812200008812c00191c880010800c91480802e0e812c000002032200440aa28a4140980c46808410429130a1892082⟩,
  .pool ⟨241,22,[241,2,11,19],[3,5,7,13,17],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨41,31,[41,19,23,29],[2,3,5,7,11,13,17,31],51,0x21a0022996832⟩,
  .pool ⟨241,8,[241,2],[3,5,7],41,0x1b382b50736⟩,
  .pool ⟨241,12,[241,2,3],[5,7,11],369,0x1fba6a74e325b887e13d348f2e4655fbf54c6e9c2c9712fd23a4d0e5d8cabf7ea989d3c4b2f21f8476931cb95977e⟩,
  .pool ⟨241,14,[241,2,7],[3,5,11,13],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,8,0x9c7000009c60000000000000000c5090000c40900000000000000000000000000000000000009090000090900000000000000000000000009090000090900000000000000000e0e00000e0e0000000000000000000000000e0e00000e0e000000000000000000000000000000000000c3c20000c1c0bfbe0000bdbc000000000000000000000000000000000000bbba0000b9b800000000b7b60000b5b40000101000001010b3b20000b1b000000000000000000000000000000000000010100000101000000000afae0000adac000000000000000000000000000000000e0e00000e0e0000000000000000000000000e0e00000e0e000000000000000000000000000000000e0e00000e0e0000000000000000000000000e0e00000e0e00000000000000000000000000000000abaa0000a9a800000000a7a60000a5a4000000000000000000000000000000000000a3a20000a1a09f9e00009d9c000000009b9a00009998979600009594000000000000000000000000000000000000939200009190000000008f8e00008d8c000000000000000000000000000000000000000000000000000000000000000000000606000006068b8a00008988000000000000000000000000000000000000060600000606000000008786000085841303000013030000000000000000000000000313000003130000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000838200008180000000007f7e00007d7c0000000000000000000000000000000000007b7a000079787776000075740000000000000000000000000000000000000000000000000000000000000000000011120000111200000000101000001010000000000000000000000000000000000000121100001211101000001010000000000000000000000e0e00000e0e0000000000000000000000000e0e00000e0e000000000000000000000f7300000f720000000000000000710f0000700f000000000000000000000e0e00000e0e0000000000000000000000000e0e00000e0e000000000000000000000d6f00000d6e00000000000000006d0d00006c0d0000000000000000000000000000000000000c0900000c09000000000a0b00000a0b000000000000000000000000000000000000090c0000090c0b0a00000b0a000009090000090900000000000000000000000009090000090900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006b6a00006968676600006564000000000000000000000000000000000000636200006160000000005f5e00005d5c00000808000008080808000008080000000000000000000000000000000000000808000008080000000008080000080800000000000000000000000000000000000000000000000000005b0700005a07000000000000000007590000075800000606000006060000000057560000555400000000000000000000000000000000000006060000060653520000515000000000000000000000000000000000000004050000040500000000000000000000000005040000050400000000000000004f0300004e03000000000000000000000000034d0000034c00000000000000004b4a00004948000000004746000045440000000000000000000000000000000000004342000041403f3e00003d3c00000000000000000000000000000000000000003b3a00003938010200000102000000000000000000000000000000000000373600003534000000000201000002010000000000000000000000000000000000000000000000003332000031300000000000000000000000002f2e00002d2c000000000000000000002b2a00002928000000000000000027260000252400002322000021200000000000000000000000001f1e00001d1c000000000000000000000000000000001b1a0000191800000000000000000000000017160000151400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_137 : ∀ i ∈ List.range' 137 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_274 : ∀ i ∈ List.range' 274 134, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 408 at hi
  by_cases h0 : i < 137
  · exact test240_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h137 : i < 274
  · exact test240_137 i (by simp only [List.mem_range'_1]; omega)
  exact test240_274 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨37,35,[37,5,7,23,29],[2,3,11,13,17,19,31],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨37,31,[37,23,29,31],[2,3,5,7,11,13,17,19],61,0x1ffffffffffffffe⟩,
  .prime 37,
  .pool ⟨37,31,[37,23,29,31],[2,3,5,7,11,13,17,19],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,18,[41,2,3],[5,7,11,13,17],1687,0x7ac8a0908840860080806000802800148000c101280000118000188404001220c0000040a0020042088000000040430281000001068090200420000502080800a0010104000474048800000c00402048008091000001000100102044200a00089006000010004102013c804082000800006009100050042204080080008000008901001204020030000011202e20002080800500101040a0000420040901608000008140c20200000001104200400502000003044800202118000188000014808300012800140100060101006102110905135e⟩,
  .pool ⟨41,18,[41,2,3],[5,7,11,13,17],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],171,0xd028b04804228948865020101844260308824028a⟩,
  .pool ⟨37,13,[37,13],[2,3,5,7,11],171,0x2080012080000000002002080090010482000012012⟩,
  .pool ⟨37,14,[37,2,7],[3,5,11,13],549,0x1a60a00261041120a0084490094824032014120184820800120982106094002924004c800925000a41821064120004104860120a01300904a4024884014122082190014196⟩,
  .pool ⟨37,3,[37,3],[2],27,0x8060b⟩,
  .pool ⟨37,3,[37,3],[2],61,0x1434026619900b0a⟩,
  .pool ⟨31,23,[31,23],[2,3,5,7,11,13,17,19],37,0x10ac804d42⟩,
  .pool ⟨31,23,[31,23],[2,3,5,7,11,13,17,19],41,0x12082850412⟩,
  .pool ⟨31,23,[31,23],[2,3,5,7,11,13,17,19],133,0x161f2054da76220c210c111b96ca813e1a⟩,
  .pool ⟨37,14,[37,2,7],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨37,14,[37,2,7],[3,5,11,13],1767,0x420080410910524524086424526182432182400812830496136182806c00c200a0d068009241141804208801b0134d368124a29169009904169b44100a41905048801a2102984500182582516532112d00424190584c004169a44125b21b61a2c80424d34990992022c82114196920024532c828b2424420104996402820032012590800516d84816414996902532010412c10c36d14c225328264a4d164208b6514020596402d201228125a0004134036c86996434124926da0d028b6806d80da0c101300961a25a6492c30182c30914190ca4910916522516c36996⟩,
  .pool ⟨37,3,[37,3],[2],171,0x4020100804020900804020100804020300804020a⟩,
  .pool ⟨37,9,[37,3],[2,5,7],95,0x102450d207310b30d453b5e⟩,
  .pool ⟨37,21,[37,3,7],[2,5,11,13,17,19],171,0x4020904804020908825020100804220300824028a⟩,
  .pool ⟨41,18,[41,2,3],[5,7,11,13,17],297,0x1eb238356f103c88b6ac1c457bd646062de227911ed18189af7a88e0d5b444f023dab07135e⟩,
  .pool ⟨37,9,[37,3],[2,5,7],27,0x8060b⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],37,0x1ffffffffe⟩,
  .pool ⟨61,39,[61,3,13,23,29],[2,5,7,11,17,19,31,37],779,0x23b064abd48b333108820e34b5f1c0a9aa6f2e76e607e0cd219800ad06fb602d2306d300a34715d34206f99002aa1e14a3ac785a8bff6209eb534561d3a5f349b3b4b39208f4afdc67b0cf81788908b098a62f87052538baeef71332c942ad1f23a⟩,
  .pool ⟨37,9,[37,3],[2,5,7],61,0x1434026619900b0a⟩,
  .pool ⟨41,31,[41,23,29,31],[2,3,5,7,11,13,17,19],1197,0x102800c148100300300820808200000900804800000020204940048b08b2002090c06412084880c200a61a00064800040005020a60304001909000009204009924201808060b44140008200104000a08b4180406010926400812400002426000830194102800080004980016194010c04484120980c241001344344800a48101000000048040240000104041040300300204a0c00502⟩,
  .pool ⟨41,20,[41,2,5],[3,7,11,13,17,19],209,0x1b392b592239de0830207a0b8ab5474178103041ee71126b52736⟩,
  .pool ⟨61,28,[61,2,7,23],[3,5,11,13,17,19],1095,0x400124410402192030424030410902920d000b00201825000a4524424092110d821900a2010010da0400090116900d26514014882032186534096104c20c061204a69008129205048849104301004300b2884530500104c20116432d860044b61928224224044320949109040b4c128169320a65008229065121a41940b0012d12584134c96996⟩,
  .pool ⟨37,31,[37,23,29,31],[2,3,5,7,11,13,17,19],1037,0x29c4012000802006083840220180b02088863006005ed0a9e1054a0809020011134414b0d80009a5321d130102208008003304200480431a00150ec038a0502030002470a0600114120082001180008460106812200008812c00191c880010800c91480802e0e812c000002032200440aa28a4140980c46808410429130a1892082⟩,
  .pool ⟨61,28,[61,2,7,23],[3,5,11,13,17,19],1387,0x6983811a8003439cc101140e354a86b4a0024042522004ec0e222188d4688a30cd40004824002008634d0d500130aca150e81c1c4816c094b320298585984e10a0f36400104074805c2011500c440190791a25a600a2264450065a4589e098022300a88043a012e02080026cf05087219a1a19404cd290368123838170a85350c800ab0b2c610040024120002b30c51162b118444703720044a420240052d6152ac7028808339c2c0015881c196⟩,
  .pool ⟨37,35,[37,5,7,23,29],[2,3,11,13,17,19,31],41,0x1fffffffffe⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,5,0x4b8ee3a8e971d2e4b8ee3a9c751d2e4b8ee3a8e9725c74b8ee3a8e971d2e4b8ee3a9c749d4e4b8e971dc749d4e3a9c971dc749d4e4b8ee3a5c749d4e4b8e971dc749d4e71d274b94e3a9c771d274b8e9729c771d2971dc749d4e3a9c971dc74b8e93a9c971ce9729c771d2e3a4e9729c7538ee3a4e9738e93a9c971d2e3b8e93a9c75392e3b8e94b8ee3a8e971d2e4b8ee3a9c751d2e4b8e74b94e3b8e971d274b94e3a9c771d274b9c751d2e4b8e971dc751d2e3a5c971dc7529c771d274b8e9729c771d2e3a4e9729c771d274b94e3a9c771d274b8e9729c771d2971dc749d4e3a9c971dc74b8e93a9c971ce9729c771d2e3a4e9729c7538ee3a4e9738e93a9c971d2e3b8e93a9c75392e3b8e971d474b92e3a5c771d474b8e9725c771d4a71dc749d2e3a5ca71dc74b8e93a5ca71ce9725c771d4e3a8e9725c74b8ee3a8e9738e93a5ca71d4e3b8e93a5c74b94e3b8e9318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c616c1b00802d805b16c1b00b601005b16c0016c5b06c02d804016c5b00b60d804016f601005b16c02d83601005b00b62d836010b60d804016c02d8b60d805b00802d8b6016fbbe8ba2df45b16fbbe8b7d1745b16fbd16c5beefa2df45d16c5be8b7ddf45d16f7d1745b16fa2df77d1745be8b62df77d10b7ddf45d16fa2d8b7ddf45be8ba2d8b7dd804016c5b00b60d804016c02d8b60d8042d83601005b00b62d836016c0200b62d8002d8b60d805b00802d8b6016c1b00802dec0200b62d805b06c0200b6016c5b06c0216fbbe8ba2df45b16fbbe8b7d1745b16fbd16c5beefa2df45d16c5be8b7ddf45d16f7d1745b16fa2df77d1745be8b62df77d10b7ddf45d16fa2d8b7ddf45be8ba2d8b7d16f5bd0b82df05b16f5bd0b7a1705b16f5a16c5bd6f82df05a16c5bd0b7adf05a16f7a1705b16f42deb7a1705be0b62deb7a10b7adf05a16f42d8b7adf05be0b42d8b7ac88621e47910f22c88621e443c8f22c8863c8b221887910f23c8b221e44310f23c8843c8f22c887910c43c8f221e45910c43ce44310f23c88791644310f221e4791644316f5bd0b82df05b16f5bd0b7a1705b16f5a16c5bd6f82df05a16c5bd0b7adf05a16f7a1705b16f42deb7a1705be0b62deb7a10b7adf05a16f42d8b7adf05be0b42d8b7a10f23c8b221e44310f23c88791644310f3910c43c8f221e45910c43c88791e45910c791644310f221e47916443c88621e479108791e45910f22188791e443c8b2218879308c2318c6118c2308c231846318c2308c6308c2308c6118c6308c231846118c630846318c2308c611846318c2318461184631846118c6308c611846118c2318c611846118c6308c231846118c6308c611846118c611846318c23184611846308c631846118c611846118c2318c611846308c2318c6108c631846118c2308c631846308c2308c6a625895e57c4af8a625895f12bcaf8a6252a62f896257c4af2a62f895f12c4af2a6312bcaf8a6254c4b12bcaf895f14c4b12bdf12c4af2a6254c5f12c4af895e54c5f12bda5695257b4af6bda56952d2a4af6bda52bda9695a57b4af2bda96952d2b4af2bdad2a4af6bda57b4ad2a4af695ed7b4ad2a52d2b4af2bda57b52d2b4af695e57b52d2c4af2be29895312c4af2be257c5312c4af7c4b12bca9895317c4b12be25795317c4a57c5312c4af895e57c5312a625895e57c625795317c4af89625795312a62f896257bda5695257b4af6bda56952d2a4af6bda52bda9695a57b4af2bda96952d2b4af2bdad2a4af6bda57b4ad2a4af695ed7b4ad2a52d2b4af2bda57b52d2b4af695e57b52d2354d5318c6a98d5354d531aa6318d5354d5318c6a9aa6354d5318c6a98d5354d531aa6318d5354c6a9aa6318d531aa6a9aa6318d5354d531aa6318d5354c6a9aa6318d59467124892a12549467124a24912549467124892a4a339467124892a12549467124a339125195092a12339125124a32a123391251950919ca339125195092a1233912513a90941d074a0e93a90941d283a0e93a9083a8e9425074a0e83a8e941d284a0e83a9283a0e93a907521283a0e941d275212839d284a0e83a90751d284a0e941d0751d2841d274a1483a90741d274a0e94290741d2941d0749d483a90941d074a0e93a90941ce94290741d283a4e942907520e83a4e9420e93a90941d283a0e93a907521283a0e93a90941d074a0e93a90941d283a0e93a9083a8e9425074a0e83a8e941d284a0e83a9283a0e93a907521283a0e941d275212839d284a0e83a90751d284a0e941d0751d283a50a41d074a0e93a50a41d483a0e93a5083a4ea425074a0e83a4ea41d484a0e83a5483a0e93a5074a1483a0e941d274a14839d484a0e83a50749d484a0e941d0749d4879e074bd2f3a5e779e074bce97a5e779e074bd2f3bcf079e074bd2f3a5e779e074be0f3bce93a5e74be0f3bce979d274be0f3bce93a5f079e0f3bce93a5e74be0f3bce9318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c64b8ee3a4ea71d4e4b8ee3a5c749d4e4b8ee3a4ea725c74b8ee3a4ea71d4e4b8ee3a52e3b8ea3a5c74b92e3b8ea71d474b92e3b8ea3a5c971d2e3b8ea3a5c74b92e3b8ea5b56d5ad6b6ad6d5b56d5adab5ad6d5b56b5b56d5b56b6ad6b5b56d5adab6ad6b5b5ab5ad6d5b56b6adab5ad6d5adab6adab5adab6ad6b5b56b6adab6ad6d5ad6b6adab5b16c5ad6b62d6c5b16c5ad8b5ad6c5b16b5b16c5b16b62d6b5b16c5ad8b62d6b5b18b5ad6c5b16b62d8b5ad6c5ad8b62d8b5ad8b62d6b5b16b62d8b62d6c5ad6b62d8b6ad6b5b56d5adab6ad6b5b56b6adab6ad6b6adab5ad6d5adab6adab5b56b5adab6ad6b6adab6ad6d5ad6b6adab5b56d5ad6b6b56b5adab6ad6d5b56b5adab5b56d5b56b5b16c5ad6b62d6c5b16c5ad8b5ad6c5b16b5b16c5b16b62d6b5b16c5ad8b62d6b5b18b5ad6c5b16b62d8b5ad6c5ad8b62d8b5ad8b62d6b5b16b62d8b62d6c5ad6b62d8b520e83a4e941d28520e83a50749d28520e7521283a0e941d27521283a50741d275210749d28520ea41d0749d283a50a41d074a50741d27520ea4250741d283a4ea42507520e83a4e941d28520e83a50749d28520e7521283a0e941d27521283a50741d275210749d28520ea41d0749d283a50a41d074a50741d27520ea4250741d283a4ea42507318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c6318c61944410c43208641944410c8218864194421946411043208621946410c8220862194821886419443288821886410c832888218c82208621944328c822086410c4328c82208621906510ca2208621904320ca220863208821886510ca3208821904310ca32084320ca22086410c4320ca21944410c432104310ca3208641104310ca21946411043008220802010402008220804100402008210080208820104010080208041104010084100402008201044100402080401044100041104010082010041104020802010041104010080208041104010082010041104001044100402080401044100820080401042010041104020802010041008220802010820080401040208820080410080208820⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_40 : ∀ i ∈ List.range' 40 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_80 : ∀ i ∈ List.range' 80 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_120 : ∀ i ∈ List.range' 120 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_160 : ∀ i ∈ List.range' 160 20, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 180 at hi
  by_cases h0 : i < 40
  · exact test720_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : i < 80
  · exact test720_40 i (by simp only [List.mem_range'_1]; omega)
  by_cases h80 : i < 120
  · exact test720_80 i (by simp only [List.mem_range'_1]; omega)
  by_cases h120 : i < 160
  · exact test720_120 i (by simp only [List.mem_range'_1]; omega)
  exact test720_160 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+10=2^a*5^b*19^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=1 ∧ b%12=1 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  have h720 := run720 h bad h240
  obtain ⟨i,hi,_⟩ := h720
  exact Nat.not_lt_zero i hi
end D10


namespace D11
private def cfg : Config := ⟨11,11,19,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨5,4,0xab089067045023⟩
private def rows12 : List Rule := [
  .div 3,
  .target,
  .div 5,
  .div 7,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x292323242323000000000000232823232423000000000000232327232324000000000000242323262323000000000000232423232523000000000000232324232321000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨27,6,0x8bb00aec05a302e5c059700a2c0239008b40e21014840515008240ab7006dc01ab0367c0d930361c0a87028a40a1d034140cb30269c099b0263c0c83⟩
private def rows60 : List Rule := [
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],133,0x420000400000e06012000900001920202⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],63,0x6880800180010116⟩,
  .pool ⟨61,9,[61,3],[2,5,7],9,0x9b⟩,
  .pool ⟨31,29,[31,17,23,29],[2,3,5,7,11,13,19],247,0x40a9631d5030001191249040ed0100a50080b70209248988000c0ab8c69502⟩,
  .pool ⟨31,20,[31,2,5,17],[3,7,11,13,19],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,4,[61,2],[3],57,0x1a60a0132014196⟩,
  .pool ⟨61,4,[61,2],[3],31,0x68818116⟩,
  .pool ⟨31,21,[31,3,7,17],[2,5,11,13,19],720,0x8002200000000208008000a00008820080028082a0000a82028002008220000a000200208000000008800200a28088220082a0020282808822008a20000a208000200008000208a00008a2008822028280800a82008822028a⟩,
  .prime 61,
  .pool ⟨61,41,[61,17,23,29,37,41],[2,3,5,7,11,13,19,31],285,0x1201b0c101105225a64104b21048021040140a0082100482134820996912822020c36012⟩,
  .pool ⟨61,37,[61,17,23,29,37],[2,3,5,7,11,13,19,31],285,0x1201b0c101105225a64104b21048021040140a0082100482134820996912822020c36012⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,19,[61,17],[2,3,5,7,11,13,19],4,0x2⟩,
  .pool ⟨61,22,[61,2,11,17],[3,5,7,13,19],76,0x351b197f99d13d75fb6⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨31,29,[31,17,23,29],[2,3,5,7,11,13,19],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,5,[61,5],[2,3],19,0x30af2⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨61,21,[61,3,7,17],[2,5,11,13,19],180,0xa2a088208020a82a2208800022088a82a080208220a8a⟩,
  .pool ⟨31,21,[31,3,7,17],[2,5,11,13,19],61,0x1ffffffffffffffe⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,6,0x140ef06e4c11070d31c3b410ec06b1c11070ea044443a520d10689c11264043c39410cf0449038ce3222c43438600cd2c47cb10c0de74330b10720a04370810705b2032470c80446812070d90421831180c50435c11000560830150c2040⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 5, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 5 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨34,7,0x5eee0113b005af80a48c06aa601717014a9802c5c0468e0050b0113a8010e4050a200a1500ab980ccdc006ce0212b00da780e44c0728601b07019328050a4028b20321d01c2080681406ede01933009ab80c46c062960130f⟩
private def rows120 : List Rule := [
  .pool ⟨31,21,[31,3,7,17],[2,5,11,13,19],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨31,20,[31,2,5,17],[3,7,11,13,19],416,0x121270985950be9699b6393aa4575631dc1c14fbd2dcb27c7ee1131371995850bf9798b7383ba5565730dd1d14fad3ddb37d7fe⟩,
  .pool ⟨41,22,[41,2,11,17],[3,5,7,13,19],665,0x1a3438806b524104a7389c70840c109270a82b130a90a9465080038008035820a8032244362c4939026319027248d1b089130054106b0040070004298a542543235054392420c08438e4739482092b580470b16⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],1197,0x2400000000410402002002002080010080400402400010010000000410000000000000000000010002002410410000000402000002400410012090002000002000080012010000080480000490000480010080402012002000410000000010412080002000492000400000000012000410082080400000002480002082000402002090480412080092012000012400080000002402⟩,
  .pool ⟨61,29,[61,17,23,29],[2,3,5,7,11,13,19],1240,0x2208202088222822080a22808a088a2020022a00802002008aa0a8280082a0008002880200a00000a0080228002000a8200282a0aa20080080200a8800808a220a20288a020882888220808208880a08a0802808088228080202022008288a8008a2288a82a000200022a0802a82a2800a0a80a2a8a02a0a0028a82a8020a880008000a82a2288a2002a2282008808080202882202028020a20a02⟩,
  .pool ⟨41,40,[41,2,5,17,23,29,37],[3,7,11,13,19,31],61,0x1ffffffffffffffe⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,6,0x9c20a61410450a59028c20a28410607c209e74209c0441010c20830000006c209a0000000996020000000975820000000955024c105200000044209004f38134208c2c208a0000000892021c1046000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 27, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 27 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨7,8,0x80b10008b100c85100505100a0a100e841007041⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨31,20,[31,2,5],[3,7,11,13,17,19],976,0x2513a92dcf430d515975398f0bf11323bb41b5992f69e9fda3e5dd2903af27056fc799a1659141c307ddb5eb55637ff14f0dd7b3dbdb8f6b0987c57fa63503b93ddf531d414965299f1be10333ab51a5893f79f9edb3f5cd3913bf27157fd789b1758151d317cda5fb45736fe15f1dc7a3cbcb9f7b1997d56fb6⟩,
  .pool ⟨61,43,[61,23,29,37,43],[2,3,5,7,11,13,17,19,31,41],1205,0x12d130e3139c1295e210d027a0c823504299a27956f389004b9c75a98f4242b62dcc6094d79d4423124505c138d2f3b86c51d02311250894e0006a0a5285804b590035390f38d2703445311223288b0392c73c272b0026b480685294158001ca4429223102e28d8773d2c720e828923108ae7aca418ced1b5090bc656b8e74802473daa791665082b104c17902c211ea520e7231c322d2⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,4,0x98000076000000000000000000000000000000000000000052001100000000430000000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 34, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 34 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨37,7,[37,7],[2,3,5],19,0x41982⟩,
  .pool ⟨37,18,[37,2,3],[5,7,11,13,17],36,0x11915135f⟩,
  .pool ⟨37,8,[37,2],[3,5,7],73,0x10080002100010116⟩,
  .pool ⟨37,8,[37,2],[3,5,7],95,0x102450d207310b30d453b5e⟩,
  .pool ⟨37,23,[37,23],[2,3,5,7,11,13,17,19],152,0x8220002a0a80008820a2888aa80a02aa2228a⟩,
  .pool ⟨37,27,[37,3,23],[2,5,7,11,13,17,19],36,0xa0a802a0a⟩,
  .pool ⟨37,20,[37,2,5],[3,7,11,13,17,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨37,20,[37,2,5],[3,7,11,13,17,19],1159,0x1002100018030000000280000e44000110000100088001000005f82120004000121600000000070000018081004002000001001023aa8008020c00010020100501020842284540504040410000002a014010001003c100804600003001010800010410000201004310080b8c8890000184041900a0041100124001094012040122500250481184210c0c852122310536⟩,
  .pool ⟨37,23,[37,23],[2,3,5,7,11,13,17,19],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨37,20,[37,2,5],[3,7,11,13,17,19],1088,0x101000300010000030500210101002022012005001300002501202302010222040104050003040000110201012500000021261121010402040520052023020406260011000100120111000102050030000100212301200401030001241120220301022205010414010304010101021000250011003126002011040305052004213302150736⟩,
  .pool ⟨37,23,[37,23],[2,3,5,7,11,13,17,19],61,0x1434026619900b0a⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,4,0x5a65a75a765a95a95a589549546758754654102102103102103102210310210⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 7, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 7 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+11=11^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  have h720 := run720 h bad h240
  obtain ⟨i,hi,_⟩ := h720
  exact Nat.not_lt_zero i hi
end D11


namespace D12
private def cfg : Config := ⟨12,2,3,19,2,1,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨11,4,0x78b34bb0bab86782389a5565125892452⟩
private def rows12 : List Rule := [
  .div 5,
  .div 7,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x101010101010000000000001010e010102000000000000001010101010100000000000010201010d010000000000000010101010101000000000000c010102010101010101010100000000000000101020101020000000000001010101010100000000000000102010102010000000000001010101010100000000000000201010201010000000000000000000000002010102010100000000000000101010101010000000000001010201010200000000000000101010101010000000000001020101020100000000000000101010101010b010102010100000000000010101010101000000000000001010a010102000000000000101010101010000000000000010201010901000000000000101010101010000000000000000000000000010101010101000000000000201010201010000000000000010101010101000000000000101020101020000000000000010101010101000000000000102010102010101010101010000000000000020101020101000000000000101010101010000000000000010102010102000000000000101010101010000000000000010201010201000000000000000000000000108010102010000000000000010101010101000000000000201010701010000000000000010101010101000000000000101020101060000000000000010101010101010201010201000000000000101010101010000000000000020101020101000000000000101010101010000000000000010102010102000000000000101010101010000000000000000000000000010101010101000000000000102010102010000000000000010101010101000000000000201010201010000000000000010101010101000000000000101020101020101010101010000000000000010501010201000000000000101010101010000000000000020101040101000000000000101010101010000000000000010102010103000000000000000000000000101020101020000000000000010101010101000000000000102010102010000000000000010101010101000000000000201010201010000000000000010101010101010102010102000000000000101010101010000000000000010201010201000000000000101010101010000000000000020101020101000000000000101010101010000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨140,6,0x1ecbd382f1c88ebe171e05dba3b9dcef343b0c4ee7d2fce8bcf42f6c4bc3d233e88db7239d08f37170d05cf117cf42c3a0b3dc2e710b2e4ee333b5f0be392fbf08fb9235cc8d79178d85ef317ec05e3c0bbe42e2ef8bafe0a5f85a3b225ecb8bb16ee08af80a2e05975222d42bb216bc8e8b21eaf8a9fe364f8187e2adec19fb124ec787b06de04ab81e7e0a938361e07b75367d41935121d41ab2127c83a7e263f8c83e1aceccb38029e039b81a3e03b35329c8683215eb586ed6d8b5e56d6dea9262a555a984aa49e9d56e76189de4a755291e7a149b8585616d285176d5d7b5d46d69aa9446a75d9d16a75179d75276919da5e445191372a656a9042a4169dc42465985342160872b15c88b5a5216ac25a82d3b854e2093ace42e2d094542d35c84a72711ca81724359a8d5a41169c15a135390a4ed1d084442⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .prime 31,
  .pool ⟨61,3,[61,3],[2],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,3,[61,3],[2],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],651,0x20a0522084922020090934c341b24221a2002d04810800d100a0412402c021300204a65a2000900c02986824db2000892936012982c905960a6502d26584102cb08221820301041060b28b0924422912832⟩,
  .pool ⟨31,8,[31,2],[3,5,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,4,[31,2],[3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,10,[31,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,4,[31,2],[3],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,10,[31,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨61,6,[61,2,3],[5],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .prime 61,
  .pool ⟨61,4,[61,2],[3],31,0x68818116⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,7,[31,7],[2,3,5],793,0x12d020a252081880644c112020006092460020080020180882a080f008c000022017044708b2850016000655a08040086844885840080416a98001a0028534438883a01100000c403c0415044060100040100189241800101220c8980460412914102d2⟩,
  .pool ⟨31,3,[31,3],[2],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,2,[31,2],[],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩,
  .pool ⟨61,2,[61,2],[],31,0x68818116⟩,
  .pool ⟨61,2,[61,2],[],217,0x1a20200420400081200080104003000820040012040008108010116⟩,
  .pool ⟨31,5,[31,5],[2,3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,21,[31,3,7,17,19],[2,5,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨61,9,[61,3],[2,5,7],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨61,8,[61,2],[3,5,7],31,0x68818116⟩,
  .pool ⟨61,8,[61,2],[3,5,7],217,0x1a20200420400081200080104003000820040012040008108010116⟩,
  .pool ⟨31,9,[31,3],[2,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,6,[31,2,3],[5],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,25,[61,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,28,[31,2,7,17,19,23],[3,5,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,2,[31,2],[],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,5,[61,5],[2,3],31,0x46000062⟩,
  .pool ⟨61,5,[61,5],[2,3],25,0x210863⟩,
  .pool ⟨31,8,[31,2],[3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,10,[31,2,5],[3,7],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,10,[61,2,5],[3,7],775,0x6ca08954c1832225a016805a4c0c18368910536d9411229830e044b442d00b6881831651220a6db2862453060c0897805a01e9103060ca24614db650448a68c18116d00b422d22070c19448829b6ca08916c1830325a016805a444c1832a910536⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,8,0x2e0000000b0000000a00000000000000002d0000000c000d0000000000000000ba000000b90000000e0000000a0000000000000e0000000a0000000d0000000c0000000000000000b800b70000002c0000000000000000b60000000a0000000f0000000000002b0000000d0000002a000000290000000b0000000000000017000000b5000000b4000000b30000000000000000b200b1000000b0000000000000000017000000af000000ae000000000000ad000000ac000000ab000000aa00000017000000000000280000001a000000a90000000000000000a8000000a700a60000000000000000a5000000a40000001a000000a3000000140000000000000000a200000015000000a100000016000000000000a00000009f0000001400000013000000000000000015009e0000009d0000000000000000270000009c00000014000000000000260000009b0000009a0000009900000098000000000000970000009600000016000000000000000014000000130000009500000094000000250000000000000000930000000300010000000000000000240000009200000091000000900000000000008f0000008e000000010000000300000000000000008d0003000000020000000000000000230000008c0000008b0000000000008a00000089000000030000000200000088000000000000002100000087000000860000008500000000000000008400830000002200000000000000008200000081000000800000000000007f0000007e0000007d0000007c0000007b0000000000007a000000210000007900000000000000007800000077001f00000000000000007600000075000000200000001f000000000000000600000074000000050000007300000072000000000000710000001e0000000600000000000000001e00000005007000000000000000006f0000006e0000006d000000060000000000006c000000060000001d0000000500000000000000001c00050000006b00000000000000001b000000060000006a00000000006900000068000000670000006600000000000000001a00650000001a000000000000000064000000630000006200000000000061000000600000005f000000170000005e0000000000001700000018000000190000000000000000180000005d005c00000000000000005b000000170000005a0000005900000000000000580000001500000057000000160000005600000000000016000000550000001300000000000000001500000054005300000000000000005200000051000000500000004f00000000000014000000130000004e0000001200000000000000004d001100000011000000000000000011000000110000001100000a00000000000000000f0000000c000000100000000b0000000000004c0000000b0000004b0000000d00000000000000004a000f0000000c0000000000000000490000000e0000000a0000000000000e0000000a0000000d0000000c000000480000000000000c000000470000000b00000000000000000a00000046000000000009000000050000004500000044000000060000000000000800000006000000080000000000000000050000000700050000000000000000430000004200000006000000410000000000000600000040000000050000003f00000000000000003e003d0000003c0000000000000000060000003b0000000500003a000000000000000039000000030000003800000037000000000000360000000400000004000000040000000000000000030035000000030000000000000000020000003400000033000000000000320000003100000001000000030000000200000000000003000000020000003000000000000000002f0000000100⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_8 : ∀ i ∈ List.range' 8 3, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 11 at hi
  by_cases h0 : i < 8
  · exact test60_0 i (by simp only [List.mem_range'_1]; omega)
  exact test60_8 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨540,7,0x87a3587d1ae1acd61d66b87a1787d0be1ac5e1d62f9f73593b9ae7a0d64d06b9f71793b8be7a05e4d02f8712f87897e188be1c45f8711187888e188461c423cfd29abe94f3b8a6adc53cfd0babe85f3b82eadc17af93b9bc9deba8ee6d477af91d9bc8eeba8766d43bc763ba7b1df19cee9ce77c761da7b0ef19c769ce3b6733bef21dd9cc77bc83b7f03b8309ddfc0760c23b67935ef51ad9e45fbd42f973358f99ae590d63c86b973178f98be5905e3c82faf0359b81aeb84d66c26baf0179b80beb845e6c22f7fc2f83e17dfb4be0da5f7fc1183e08dfb4460da239792f8fc97e5a8be3d45f979118fc88e5a8463d423af62f9bb17eb9cbe6ce5faf6119bb08eb9c466ce23c732fa7217f1cc469c823df629b3b14f79ca6cce53df60bb3b05f79c2ecce177f32983994df90a60c8537f30b83985df902e0c817970298f094e5c02e3c217dfc23b3e11f7b48ecda47dfc05b3e02f7b416cda0b1f623cb391c7d8172ce0bc7023a7811f1848e9c247c7005a7802f184169c20b8f83b8b49de3e0762d23bbf23ba319defc8768c63ba7b359761ae9ec5e5d82fd7b2faf617f5ec46bd8237782ff7497dde047dd22347529df314d1d42f7cc17d7229af194f5c82ebc61776f29f7014ddbc2fdc017bfb23a3611efec168d80b5f823eb491d7e017ad20b45dfa5e77d11777179db8154fa462fd05537118bb8a57f41647a295f58591ac5d1f46a17a174759a85ac151ee46177054741185a0bd1e8221742f472888594b59fa1ecfd2d2be8795f4b59dc1ecee2d2b70795b8e53fa369fd3913e8d89f4e53dc369ee391370d89b8cdcf42ae7a3337d0a9be8cdcd62ae6b333758a9bac9d3f4129fa2713d0489e89d3d6129eb271358489ac85cee066f721734019ba03d6ee5a3f70f5b4168fa0e56e836b74391fa0d8fd0e56ca36b65391f28d8f949d0e8128742707a0483d09d0ca1286527072848394859e20657121671019588958fa0ec7d2527e8393f4958dc0ec6e252770393b8dcffa3207d373f70c81b8ddbee32df73733b8c99dcddbd032de8373340c99a0ad2ee1a9772b0fb8687dcad2d01a9682b0f40687a0658e26e4f1196311b9388acfe21a7f12b0388681c4acfc41a7e22b031068188a3db895edc68bae255d71a3d9a95ecd68ba6a55d35bbab8a1d5c6eaee285771bba9aa1d4d6eae6a857355b7b8e945c56de6ba5135eb4b8b92dc7ad26ae4b35d3db2ad75974f652b5d298b7b289bd962a2ca251658b79489bca62a25225129a34b295a596896ca54b65a349495a4a68965254b298bdac89ed662bab225d598bd8e89ec762ba3a25d1d2baacd15d64aea3b4571d437acdd45650de3b7511deb1acb91567ac63ae451debda0b9ed07aba82e5d41ebd82b9ec17aba0ae5d058baa0895d062ea0a25705bb4a0a1a506e968284b41bb482a1a416e960a84b05d31a0ad8d0748a82b4541d3182ad8c1748a0ab45050bcb8c16dc42f26b05b353b6b8d93dc4eda6b64f359b0b2910d966c25244329e3cacb56d678f23ad5b1d839ac8555660e63a1551dcb0aca90d672c23aa431d93bb28ddd964b2ca3596593b948ddca64b252359297afb2817d95e82ca041657af94817ca5e8252041297b5ac81ad65e9ab204d597b58e81ac75e9a3a04d1ddafa6b17d376829ac414ddaf88b17c4768222c4111c38a0a5c5070a68295341c3882a5c4170a60a95305d14772ca3bb415dcb0aeed14592ca2cb41564b0ab2a176b14435a85d345109ad116b2c8b5b409acb04d6d114d2c8a6b40934b049a41a655c5b290691d7168e111654413284451d1048ee9a5f38d2fba2d7ce16bee9a4138d20ba2d04e1682a145f14a2fa8157c50abea144114a20a8150450a8269c77706bb9a7165c1ab28197704cbba029dc114ee8195904caca02964114b2393775823b8e4d65608b221c714c6b888714d31aa6c9c6b286b5b27134a1a9a219654c53288651d3148e8135f0422fa04d0410882⟩
private def rows120 : List Rule := [
  .prime 41,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,25,[41,5,17,19,23],[2,3,7,11,13],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],915,0x20820000a6020080100022002020004090810c840040008001000021900200001029000000000000208000a00200041120840000008001000024340328000000840800209020000a6000886092502c021204100068220001000120008301200000060008120001000141100220a00108b0092⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],1025,0x1753739646c1ff0f7e0c33a51212a953045facbfc0d0da63b6bab2999cb6370ffa7b74409d6a90156b9862ede1de0ec4c319b5d596dce1b0b87dd35f8304ab44008b548307eb2ef874361ceda6aeb6630c8dc1ee1edd18675aa0255ae408bb797fc3b1b4e6653575b7196c2c0ff4d7e8832a5521229730c1fbc3fe0d89a73b2ba⟩,
  .pool ⟨31,10,[31,2,5],[3,7],41,0x1b382b50736⟩,
  .pool ⟨31,8,[31,2],[3,5,7],123,0x10000124014004012182110536⟩,
  .pool ⟨31,8,[31,2],[3,5,7],41,0x1b382b50736⟩,
  .pool ⟨31,2,[31,2],[],123,0x10000124014004012182110536⟩,
  .pool ⟨31,2,[31,2],[],1025,0x1a20200070000000a800000000000002220000000000000000000000000000202020000000000000000000000000000000000000000000000000000000003000300030000000000000000000000000000000000000000000000000000000001010100000000000000000000000000001110000000000000054000000380010116⟩,
  .pool ⟨31,3,[31,3],[2],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨61,4,[61,2],[3],451,0x100040000010010000400000000000000000010200104020000000004012000002100010116⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨31,7,[31,7],[2,3,5],205,0x60111860280e10524000005100001520414841a008080011282⟩,
  .pool ⟨31,2,[31,2],[],1435,0x100000000042000100000000000000200c000000424400000400000014000010001000180040a10000001000002058202000100004002000100000000042200100000002000001021000000380000020408806000400001000020040000000080022800800180101010204001000300010080010000200400000041000400020080801000200000000010444081010100100020009020000040000004a81110400040008002054808000380010116⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨61,2,[61,2],[],451,0x100040000010010000400000000000000000010200104020000000004012000002100010116⟩,
  .pool ⟨41,38,[41,2,17,19,23,29,37],[3,5,7,11,13,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],1025,0x242031006008a0f6204002402122053040c00ab80c0da43222a12101880100c126b14000962101523902260815c0644c2193050909040208860835c80000b000089148303802ae0702614e982869402000c41041ec4084248000540a40898205f4391b0a6441434a410082008a4d72802024401220730c0e002fa0c09a43a22a⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],451,0x688580269400082c82200000008448a0800c0810005000001001903060c09800800000a00081030010512210000000441341000296401a116⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨41,9,[41,3],[2,5,7],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨61,8,[61,2],[3,5,7],451,0x100040000010010000400000000000000000010200104020000000004012000002100010116⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],41,0x1fffffffffe⟩,
  .pool ⟨41,5,[41,5],[2,3],25,0x210863⟩,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨31,9,[31,3],[2,5,7],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],427,0x54419250004488602030c2014002001403c28008015210980224000244019084a80100143c02800400280430c04061122000a49822a⟩,
  .pool ⟨41,24,[41,2,3,17,19,23],[5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,5,[41,5],[2,3],31,0x121d47b6⟩,
  .pool ⟨61,7,[61,7],[2,3,5],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨41,25,[41,5,17,19,23],[2,3,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,4,[31,2],[3],41,0x1b382b50736⟩,
  .pool ⟨31,4,[31,2],[3],123,0x10000124014004012182110536⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,10,0x906408fe3e8f63c8ee3a8e6388de368d6348ce328c6308be2e8b62c8ae2a8a62889e268962488e22090250942409025094248862087e1e8761c86e1a8661885e168561484e1205611840150560f838158341204a0c82c1204a0a0541505415054150541504a098201204a07818128160480e02806007fdfe7f5fc7edfa7e5f87ddf67d5f47cdf27c5f07bdee7b5ec7adea7a5e879de6795e478de2785e077dde77412049dc76c12049da765d875dd6755d474dd2745d073dce735cc72dca72415055c871c15055c6715c470dc2705c06fdbe05415054150541505415049bd6f012049bb6e8126e5b86ddb66d5b46cdb26c40e039b06bc0e039ae6b411045ac6ac11045aa6a411045a869c11045a602c0a0280b02c0a0280b6940e039a468c0e039a2031a16800c0319f6780c0280b02c0a0280b02c0a03c0f03c0f03c0f03c0f0399d6700e0399b6680e6640c0319865c0c03196045956501104593648116440c0319063c0c0318e0458d630110458b62811011896200401187618040040100401004010040100d856100300d836080360404011805fc040117e004010040100401004010017d5f0000017b5e8000040100401004010040100002008000000200800011795e004011775d804014000000501400000055d42308d745cc2308d720080000002008000000208822088220882208822004010040100401004015c5705bd6e5b56c5ad6a06c210841b06c210841b5a56859d665956458d620741f07c1d0741f07c1d5856057d5e5755c56d5a078000001e078000001e5655855d565555454d520701b06c1c0701b06c1c5440300d5053c0300d4e0701b06c1c0701b06c1c0814d530200814b528200741f07c1d0741f07c1d078000001e078000001e074180601d074180601d5254851d465154450d4206c1c0701b06c1c0701b505404fd3e4f53c4ed3a4e41a069384dc1a06936060190641806019064184d5344cd324c5304bd2e008000000200800000024b40300d2c4ac0300d2a008000000200800000024a52849d264952448d2205c1705c1705c1705c17000050140000005014004852047d1e4751c46d1a05816058160581605816001194600000117458004551444d124451043d0e4350c42d0a4250841d064150440d02405003fcfe054fd3f015054fb3e8153e412048f83dc12048f63d412048f43cc12048f23c4f03bcee3b4ec3acea3a4e839ce6394e438ce205415054150541505415384e037cde374dc36cda054d936015054d735815048d535012048d33481234414050d033c14050ce04c120481304c1204813334cc32cca324c831cc631412048c430c12048c2304c02fcbe2f4bc2ecba2e4b82dcb62d4b42ccb2038b12c00e038af2b80e044ad2b011044ab2a81103c0f03c0f03c0f03c0f03c0f03c0f03c0f03c0f2a411044a829c11044a62940c030a428c0c030a228411044a027c110449e0400a028100400a0281003c0f03c0f03c0f03c0f2740e0389c26c0e0389a0300d0340c0300d0340c0280b02c0a0280b02c0a2649825c962549424c92020090240802009024082449023c8e2348c22c8a2248821c862148420c82204801fc7e1f47c1ec7a1e4781dc761d4741cc7201c0701c0701c0701c07000020080000002008001c4701bc6e1b46c1ac6a014000000501400000051a40300c6819c0300c661946418c621846017c5e0185d170060185b168060140000005014000000500c591600300c5715803008000000200800000021545414c521445013c4e1344c12c4a1244811c4600045110000004310800104400fc3e0f43c0ec3a010390e004010370d80400401004010040100401010350d004010330c8040c40300c300bc0300c2e0040100401004010040100002008000000200800004010040100401004010002d0b0000002b0a800004010040100401004010a4000002809c0000026⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_137 : ∀ i ∈ List.range' 137 3, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 140 at hi
  by_cases h0 : i < 137
  · exact test120_0 i (by simp only [List.mem_range'_1]; omega)
  exact test120_137 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨120,8,0xe0c9e668c9e6e0c96e68c96ea451e62c51e6a4516e2c516ee051aa6851aae05132685132a4c9aa2cc9aaa4c9322cc9328c21ce1421ce8c21561421568c99921499928c991a14991ae009ce6809cee00956680956a481ce2c81cea481562c8156e08192688192e0811a68811aa409922c0992a4091a2c091a98e1c298e14a20698620690eece1b6ece13eb069b63869b6b0693e38693e74697a746902b0e17a38e17ab0e10238e102c8c9b6c8c93e8c51b61451b68c513e14513e50517a5051028cc97a14c97a8cc90214c902ac71e63471e6ac716e34716eace9aa34e9aaace93234e932b829e6b8296e7ca1e604a1e67ca16e04a16e40a1aa40a1327c29aa0429aa7c2932042932d089e65889e6d0896e58896ed011aa5811aad01132581132dc71ce6471cedc7156647156dce99264e992dce91a64e91ac429c24c29c2c4294a4c294ac4a1864ca186c4a10e4ca10e7c11b60411b67c113e04113e7c897a04897a7c8902048902⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],241,0x11a0115e923660112012414509d84703886e428a0920122019b125ea20162⟩,
  .pool ⟨241,24,[241,2,3,19,23],[5,7,11,13,17],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨241,10,[241,2,5],[3,7],41,0x1b382b50736⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,7,0xf9ec000f5e40000003c770003b7500000000000000000000000000000003a730003971e1bc000ddb4000000000000000000000000000000000000000000000000366b000356900000000000000d19c000cd94000000000000000000000000000000000032630003161c17c000bd740000000000000000000000000000000b96c000b5640000002c570002b55a810000a61000000000000000000000025200002510000000000000000000000000000000020400002040000000000000008100000810000a00c0009e0c000000274d000264b000000000000000000000000000000001ca00001c9911c0008d140000000000000000000000000000000880800086080000002141000203f0000000000000000000000000000000013e000013d78ec00074e400000000000000000000000000000000001c370001b350000000000000068cc00064c4000000000000000000000000000000000000000000000000180200017825cb400058ac000000000000000000000000000000004a800004a40000001427000132500000000000000488c000448400000000000000000000101f0000f1d000008100000810000000000000002040000204000000000000000000000e1b0000d1900000000000000305c0002c5400000000000000000000000000000000000a13000091100000000000000203c0001c3400000000000000000000060b000050900000000000000101c0000c14000⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_137 : ∀ i ∈ List.range' 137 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_274 : ∀ i ∈ List.range' 274 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_411 : ∀ i ∈ List.range' 411 129, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 540 at hi
  by_cases h0 : i < 137
  · exact test240_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h137 : i < 274
  · exact test240_137 i (by simp only [List.mem_range'_1]; omega)
  by_cases h274 : i < 411
  · exact test240_274 i (by simp only [List.mem_range'_1]; omega)
  exact test240_411 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨31,28,[31,2,7,23],[3,5,11,13,17,19],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨31,20,[31,2,5],[3,7,11,13,17,19],399,0x100300044a0114106120c80006122102512d060904a0d14504102816490802410d32120db24069009344348905a6132536⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],703,0x16284d9071f687047b12ab2c803a01253a8e5358d88e4cb581011a9d01171c770a9cc4b9375f37d4a380d0f960b4de32d412041342dcc2a71147176f06a57f7e10cd86e4e4258e835b7b23fe4b2aa321dd1e9011f645eb96⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],481,0x1a60e406f08054a3a952005088d2202b63088820000098030303887034513228b038470303006400001044431b50112c4428012a5714a8043d809c196⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],577,0x1eb63cf47e82bd94bbe610272e9e08926e2ab5f14c5431bc76a75be052064c25a6e07766799bb81d9690c981281f6b95b8f630a8ca3eb551d92441e5d390219f74a6f505f8bcf1b5e⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],703,0x4410302402041a100820000800241288020040840c1100010094010008200218c081104800002000806100a442024400000240008225010610000481480000090280a000800312402180010000014810100184412916⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],1235,0x22926184c43812821c85210af0210b22c8022c446388b420407b12a1b5452282170dae309646184e0284043c250382a398aa000000a0231910149589338037a0ac418255004220c2318089524836094269c6328da3539450a5cc0b0033a106604c673421398ea7bd622a4283a0c53018b5a9684a48512928009073a1a51004a3000f5b9826018c4892f489a0338e0235a0685ac23c2149861129a⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],949,0x175663565e83704f610d7e83069a2c1342e3a4641549fb43bb08c49a9967f79738894ed4187a1e4ea63621f400946bc59106a9b94f6ce050b1a218000611634281cdbca765582268f58a400be11b195c9e17860adca4473a7bf9a65648c43770b7e4aa098971d0b20d1658305fac21bc83b05e9ab19aba⟩,
  .prime 181,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,4,0x778778778787787787877877877877877877778778778787787787877877877778778778787787787787787787877877877778778778aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa787787787877877877778778778778778778787787787877877877778778778787787787877877877877877877778778778787787787aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa444444444444444444444444444666666666666666666444444444444444444666666666666666666444444444444444444444444444444444444555555555444444444444444444555555555444444444444444444444444444555555555444444444444444444555555555666666666444444444444444444666666666444444444444444444444444444666666666444444444444444444666666666444444444444444444444444444444444444555555555444444444555555555555555555555555555444444444444444444444444444444444444444444444444444444666666666666666666444444444444444444666666666666666666444444444444444444444444444444444444aaa999aaaaaaaaa999999aaaaaa999aaaaaaaaa999aaaaaaaaa999787787999999877877778999778778778999999787787877999877778999778787787999999877877877999877778778999999787787999aaaaaaaaa999aaaaaaaaa999aaaaaa999999aaaaaaaaa999aaa877877999999778778787999787787787999999877877778999778787999787877877999999778778778999778787787999999877877444444444444444444444444444666666666666666666444444444555555555444444444444444444555555555444444444444444444444444444555555555444444444444444444555555555444444444444444444444444444666666666666666666444444444444444444444444444444444444444444444444444444555555555555555555555555555444444444555555555444444444444444444444444444000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111233332323323233332332323233323233332332323233233332323332323233233332323323233332233332323323233332332323233332323233233332323323233332233332323323233332332323233323233332332323233233332323332323233233332323323233332111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_40 : ∀ i ∈ List.range' 40 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_80 : ∀ i ∈ List.range' 80 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 120 at hi
  by_cases h0 : i < 40
  · exact test720_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : i < 80
  · exact test720_40 i (by simp only [List.mem_range'_1]; omega)
  exact test720_80 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+12=2^a*3^b*19^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=2 ∧ b%12=1 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  have h720 := run720 h bad h240
  obtain ⟨i,hi,_⟩ := h720
  exact Nat.not_lt_zero i hi
end D12


namespace D13
private def cfg : Config := ⟨13,13,19,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨5,4,0x69009065005061⟩
private def rows12 : List Rule := [
  .div 5,
  .target,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x4104104100000000000821c20860000000004104104100000000000821420840000000004104104100000000000820c2081000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨6,6,0x6d40935000a404a5006340781⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,2,[31,2],[],16,0xd117⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],208,0x1131371995950bf9799b7393ba5575731dd1d14fbd3ddb37d7fe⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .prime 31,
  .pool ⟨31,7,[31,7],[2,3,5],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],336,0x109004901221869a0832504814094436582cb0d261109104901320869b0932514914084536582db0d36⟩,
  .pool ⟨31,7,[31,7],[2,3,5],80,0x82000202000080800082⟩,
  .pool ⟨31,10,[31,2,5],[3,7],48,0x1109b2514db6⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],488,0x15139115d75315515155119713d11313935195911751d1d593d5d5111397071557d79191559151d317d595d3555357d15715d793d3d397531197d55796⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],31,0x68818116⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],72,0x88a2200aaa208aaa⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],16,0xd397⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],80,0x129a543ce1139a553de⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],16,0x8002⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,5,0x1a0040000000002c007800e0000068000000006000b000000000a001200000005800400070000000004000c0000150000000014000a0010000000000c02000000001300020000000024004400⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 5, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 5 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨1,7,0x29⟩
private def rows120 : List Rule := [
  .div 17,
  .pool ⟨31,10,[31,2,5],[3,7],800,0x8110004001012000015000000980010517000210011100000181000041400020018011011708000005110002010101000140800001c001013700401001100800010500000340000101800181170840000130000011010108014004010182110537⟩,
  .prime 41,
  .pool ⟨31,27,[31,3,19,23],[2,5,7,11,13,17],328,0xa0a822aaa200888028a08a082a888a820002280a00a028800082a222a820a20a280222008aaa882a0a⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0x610044000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 6, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 6 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨0,8,0x0⟩
private def rows240 : List Rule := [
  .pool ⟨31,10,[31,2,5],[3,7],1575,0x40000020101100000008000205020200040000001140800004000800360008101801101160040100001000020220008000004040204040009000000a2800000080030002c10102030002026c100020000200004044020004000008040809005000800045000000300020005800200060044145821004000000008808804000000001009101000a40000008a0020002010c000b0004000c000829b0420000000800010510080000000120102020014800000134000010400180016004810182110536⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 1 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+13=13^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  obtain ⟨i,hi,_⟩ := h240
  exact Nat.not_lt_zero i hi
end D13


namespace D14
private def cfg : Config := ⟨14,2,7,19,1,1,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨17,4,0xbb47b83b0994598198b70774378950554154b3873033491851⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,5,0x8c2308c2308c3408421084210842118461184611846108421084210842108c2308c3308c2308421084210842118461184611846108421084210842108c3208c2308c2308421084210842118461184611846108421084210842100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018461184611846108421084210842108c2308c2308c3108421084210842118461184611846108421084210842108c2308c3008c2308421084210842118461184611846108421084210842108c2f08c2308c2308421084210842100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008c2e08c2308c2308421084210842118461184611846108421084210842108c2308c2308c2d08421084210842118461184611846108421084210842108c2308c2c08c2308421084210842118461184611846108421084210842100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018461184611846108421084210842108c2b08c2308c2308421084210842118461184611846108421084210842108c2308c2308c2a08421084210842118461184611846108421084210842108c2308c2908c2308421084210842100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008c2308c2808c2308421084210842118461184611846108421084210842108c2708c2308c2308421084210842118461184611846108421084210842108c2308c2308c2608421084210842118461184611846108421084210842100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018461184611846108421084210842108c2308c2508c2308421084210842118461184611846108421084210842108c2408c2308c2308421084210842118461184611846108421084210842108c2308c2308c22084210842108421000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨167,6,0x302efc175f4def71fbf47e372b5f41d7d2b2e87cb7132eccfb827ed46fbe03ec8cefb1bbe03ef8338ec9d781b5c80d7639e4cb79021e5886d315b4ce61609858b55321540e4961524c249a35e44479d05e44d6dd29b6876d735844761a05874d55a29550455105578c79b25e60679201e6c36d801b6cc61825878061e2556c65580d554ef7e23deceeb523af82ebe2f7ec8df50b7f8ec75171e4df7013dc0deb613ad8ddf32b7c07dfc137e41df92b4d87d302b1e44c7a27dd0ceb127ae83eb1334e86d34034d09c7a031e0e75221d6c27553977885db1576025db39460b51215460545c35d70a51d25d5c375731a74369a01a7465170147404542fcc48f3d17ce82f312f6f48dba176e8ecf1173f42cf13b0e88c37170ecdf382bcf81f38376c87dbe136ec1dbb2b3e07cfe1f0ec4c38070d83f3303cd8ce73279c06e761b6cc3db0036ccccf6033d89c331b0e8e71421c44571a21950265a09668b4d41534424d53597876551d678159e2936c74d505354a41e1106c141⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,7,[31,7],[2,3,5],793,0x12d020a252081880644c112020006092460020080020180882a080f008c000022017044708b2850016000655a08040086844885840080416a98001a0028534438883a01100000c403c0415044060100040100189241800101220c8980460412914102d2⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],819,0x40904001001020008009008044001040008244000000001000001000000000800005000049005104000004a00000040000008000100000020000005200000208a00920000a0000100000000080000080000000022410002080022010090010004080080020902⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .pool ⟨31,7,[31,7],[2,3,5],549,0x82080002000012080080490090000012010000080000000000082002090002000000480092400080082002412000410482012080010090480000080010002082090010092⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨61,9,[61,3],[2,5,7],45,0x108805020a⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],117,0x509d474f8985b8c7bb134b559f7e⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],651,0x20a0522084922020090934c341b24221a2002d04810800d100a0412402c021300204a65a2000900c02986824db2000892936012982c905960a6502d26584102cb08221820301041060b28b0924422912832⟩,
  .pool ⟨31,10,[31,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,6,[31,2,3],[5],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],45,0x55898f135e⟩,
  .pool ⟨31,10,[31,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨31,6,[31,2,3],[5],45,0x55898f135e⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,10,[61,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨61,10,[61,2,5],[3,7],775,0x6ca08954c1832225a016805a4c0c18368910536d9411229830e044b442d00b6881831651220a6db2862453060c0897805a01e9103060ca24614db650448a68c18116d00b422d22070c19448829b6ca08916c1830325a016805a444c1832a910536⟩,
  .pool ⟨31,10,[31,2,5],[3,7],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,9,[61,3],[2,5,7],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,9,[61,3],[2,5,7],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨31,9,[31,3],[2,5,7],45,0x108805020a⟩,
  .pool ⟨31,4,[31,2],[3],63,0x6880800180010116⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩,
  .pool ⟨31,27,[31,3,17,19,23],[2,5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨31,9,[31,3],[2,5,7],9,0x9b⟩,
  .pool ⟨31,5,[31,5],[2,3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,27,[61,3,17,19,23],[2,5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨31,9,[31,3],[2,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,4,[31,2],[3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,4,[31,2],[3],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],279,0x544120708c040285189240aab009070621008460e0900d55024918a14020310e04822a⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],225,0x108815020b088440ac10580622014182c031900a04560108a05822b⟩,
  .pool ⟨31,26,[31,2,13,17,19,23],[3,5,7,11],61,0x1ffffffffffffffe⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,8,0x1900000000001b1700000000001600000000001a0000001600000000001a000000000019000000000018c90000000000000000181700000000001600000000001a0000000000190000001a000000000019000000000018c80000000000160000001c00000000001600000000001a00000000001900000000001c0000170000000000160000000000150f00000000000f000000c70000000000180000000000c600000000001600000000001500000016000000000015c5000000000018000000000017000000180000000000c4000000000016000000000015c3000000000000000015c20000000000c10000000000c00000000000160000bf0000000000be0000000000bd000000000017bc0000000000000000bb1f0000000000ba0000000000b9000000000018000000b80000000000180000000000171e00000000001d0000001f0000000000b70000000000b60000000000180000000000b50000001b0000000000201e00000000001d00000000002100000000b40000000000b30000000000b20900000000000b0000000c00000000000b0000000000b10000000000b000000000000a000000af00000000000a0900000000000b0000000000ae0000000b0000000000ad0000000000ac00000000000a0c0000000000000000ab0900000000000b0000000000aa0000000000a90000a800000000000900000000000e0000000000a7a60000000000000000a5a40000000000a300000000000c00000000000e000000a200000000000e0000000000a1120000000000a00000009f00000000009e00000000000c00000000009d00000000009c000000140000000000131300000000000a00000000000900009b00000000009a00000000009900000000000d0000000000980000000d00000000000c0e0000000000970000000000960000009500000000009400000000000d0000000000099300000000000000000c9200000000009100000000009000000000000d0000000f00000000000d0000000000110e0000000000100000000000008f0000000000048e0000000000050000000000030000008d00000000000300000000008c0000000000048b0000000000000000018a000000000089000000000002000000000088000000030000000000060000000000040600000000000600000087000000000005000000000003000000000086000000000001008500000000000500000000000300000000008404000000000000000083040000000000220000000000820000000000030000008100000000008000000000007f7e00000000007d0000000400000000007c00000000007b00000000000300000000000f0000000300000000007a040000000000790000000000050000030000000000780000000000010000000000080000000000050000007700000000007602000000000075000000000004000000070000000000040000000000070000000000070300000000000000007403000000000073000000000004000000000072000000040000000000710000000000050200000000007000000000006f00000000001800000000006e1f00000000006d0000001e00000000001d00000000002100000000001b0000000000200000006c0000000000176b00000000006a000000000069000000680000000000670000000000180000000000661f0000000000000000171e00000000001d000000000065000000000018006400000000001600000000001a0000000000190000000000180000001900000000001c1c00000000001600000000001a0000001600000000001a00000000001900000000001b170000000000000000186300000000001600000000001a0000000000190000001a00000000001900000000001817000000000016000000000000001562000000000018000000000061000000000016000000600000000000160000000000155f00000000005e0000000f00000000000f000000000017000000000016000000000015000000160000000000155d00000000001800000000005c000000180000000000170000000000160000000000155b0000000000000c00000000005a000000000059580000000000570000001300000000000a0000000000090000000000140000000000130000000e000000000056550000000000540000000000090000005300000000000c00000000000e000000000052510000000000000000501200000000004f00000000004e00000000000e00004d00000000004c00000000000d00000000000c4b0000000000000000110e00000000001000000000000f00000000000d0000004a00000000000d000000000049480000000000470000000e00000000004600000000004500000000000d00000000000c0000000d000000000009440000000000430000000000420000000000000a0c00000000000b0000000000410000000000400000003f00000000003e00000000003d0900000000000b0000000900000000000b00000000003c00000000003b00000000003a0000003900000000000a0c00000000000b0000000000380000000b00000000003700000000003600000000000a09000000000035000000000004000000000034000000000033030000000000000000050200000000003200000000000400000000003100000001000000000008000000000005030000000000300000000200000000002f00000000000400000000002e00000000002d00000007000000000007030000000000070000000000040000060000000000060000000000030000000000060000000000040000002c0000000000012b0000000000050000000000030000000500000000000300000000002a00000000000429000000000000000004280000000000270000000000030000000000260000000200000000002500000000000124000000000023000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_8 : ∀ i ∈ List.range' 8 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_16 : ∀ i ∈ List.range' 16 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 17 at hi
  by_cases h0 : i < 8
  · exact test60_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h8 : i < 16
  · exact test60_8 i (by simp only [List.mem_range'_1]; omega)
  exact test60_16 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨448,7,0xd94e9b02f4f6532ec0b97696eff03f7da5b47c0fa3e10e9b40f4f8432ed0397393e3d8271ce4f176098bb98fba04fdee6376813bb41befdc677d06f47719a3b95e9a0374ee572e80d9710fe9c4074c43f2f1019731d7ad473d4c757351cb991a7a8c5bd646972316b97977a80bbd5e21ea010f57975c80bae5e2172010b919474c82ba46515b20aad19d6ec873746754321ca1a916e981376a4542604a179d6280eb15e398a01cc579d4480ea25e391201c89c9c7aa86bd727172a1ab98137a8423d604d72108b9e107ab40bd784172d02b9e1974b453a78655ad14adc9674a83ba72595aa0ead8166e843b760594210ea1c9968a853472652aa1495e9b7ab8dbd7a31eae18f5e9b5cb8dae7a3172e18b95987ae84bd566173a12b9b957aa033d6e557280cb940f74dc03a503d5b700ad59b6ee8637566d43a18a14186edc4b7506143712a170f6ef40375c3d43d00a1e9868b8c347a25a2e12d1e984ab8c257a252ae129529df9d077cca776f41db7e97f9b847cfa5f6ee11b7a17f394479e85f56511abd17edac476f45f3eb119fa14e1942f0e8530e50b87c1cf9a46fcf0736e91bb7793f98027cde4f6e009b779cf3806f9de735601baba9ced986f6ea733e61b9f796ed80b76de1fb600fdb796cf80b67de1f3e00f9f799e180570de670e01587c92f3a81f9f24b56a07ab09be7c0673c26f2701993515e7e4373d4572790d93c8fe1a8070f23f0ea0187b9d78a0ebc6e39e281cf1b9d5aa0ead6e396a81cb5897788843c625d6a210b559178e813c56456ba04b5b916ca08b66e09b2804d9b914ea08a76e093a8049db9a66a0d336e2d9a816cdb9a48a0d246e2d2281691b9460a02b06e510a80a85e1878b4c3c7825e2d12f1e185ab4c2d78256ad12b5b12789c1bc6c496a706b5b1b729c6396c6d52718a969272f01b95a4953c06a9c8f72a8039723d52a00a9e1566b4ab378199ad0ccde1548b4aa4781922d0c91e0f60b47b0780182d00c1e0f42b47a178010ad0085817f78447be05f66111b3514ebe42f5d4533790b9b094e5c02f2c2531f00b8fe11e5b4172f8471ed058f517dfe446fd45f079118359cf7e86fbd67367a1bb3710f7f40fbdc4367d03b3713ebf4275dc4f37d099bd19e5ac572f4671eb158fb96e5a03f2ee5b1e80f8f716dff43efdc5b07d0f83015f1bc378c0574ef0da778feb80075de3f360019b91be58c672e46f1e3198f30fe5d4072cc3f1f5018fc9d76a8ebb7239daa1cedc9d58a8eac723962a1cb1997769043b665d62410b18147684a3b6015da10aed8145884a2c60156210ab1c9770a8bb87221c2a10e1c9752a8ba972214aa10a599170908b86609c2404e199152908a966094a404a5c9a64a8d32722d92a16c9c9a46a8d23722d1aa168d99464902b266511a40a8d09164c013242451b0048da1c7094e386835c251ae1a1c5294e2968354a51aa5e9670b8b387a1dc2e0ee1e9652b8b297a1d4ae0ea52966ad03b54a593340e99e906ab80b57a4132e029971964f45325c651bd148dd1664ac3b274591ab0e8da106494832680592502c9a10469482368051a5028d2995ed052f4a650341481e935eb89af7a117ae08bde9340b89a07a1102e0881d105eac82f74057ab02bdd1040ac820740502b0281⟩
private def rows120 : List Rule := [
  .pool ⟨41,28,[41,2,7,17,19,23],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,8,[41,2],[3,5,7],31,0x121d47b6⟩,
  .pool ⟨41,36,[41,2,3,17,19,23,29],[5,7,11,13,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,8,[41,2],[3,5,7],819,0x100002000000000800014000000010000180100010022000000004000000020000000002900102000010020000080c040140100000000060001004101000000800000000104001000008861000020109100000001204000900045000108040b0102110536⟩,
  .pool ⟨41,8,[41,2],[3,5,7],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨41,7,[41,7],[2,3,5],117,0x1060024000161921261a0000900182⟩,
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨41,2,[41,2],[],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,17,[41,17],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .prime 41,
  .pool ⟨41,2,[41,2],[],31,0x121d47b6⟩,
  .pool ⟨41,3,[41,3],[2],63,0x50402a100854020a⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],1025,0x1753739646c1ff0f7e0c33a51212a953045facbfc0d0da63b6bab2999cb6370ffa7b74409d6a90156b9862ede1de0ec4c319b5d596dce1b0b87dd35f8304ab44008b548307eb2ef874361ceda6aeb6630c8dc1ee1edd18675aa0255ae408bb797fc3b1b4e6653575b7196c2c0ff4d7e8832a5521229730c1fbc3fe0d89a73b2ba⟩,
  .pool ⟨41,2,[41,2],[],819,0x100002000000000800014000000010000180100010022000000004000000020000000002900102000010020000080c040140100000000060001004101000000800000000104001000008861000020109100000001204000900045000108040b0102110536⟩,
  .pool ⟨31,10,[31,2,5],[3,7],41,0x1b382b50736⟩,
  .pool ⟨41,25,[41,5,17,19,23],[2,3,7,11,13],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  .pool ⟨31,10,[31,2,5],[3,7],123,0x10000124014004012182110536⟩,
  .pool ⟨31,10,[31,2,5],[3,7],1281,0x1b28221060300800a0002800020000032000000522000000002100000000002930010010100000886020000000400000000020080000000000010000100022082800000800000c000800000000021200b4012100000000004000c00000400000504110002000020000000000004010000000000800000010184400002020020032500000000002100000000112800000130000010000500014004030182110536⟩,
  .pool ⟨31,6,[31,2,3],[5],369,0x100844020590854130148e0c4615d890482c10089612e10280d0e5188a9f120901924032d01d0452131cb15977e⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],369,0x100844020590854130148e0c4615d890482c10089612e10280d0e5188a9f120901924032d01d0452131cb15977e⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨31,5,[31,5],[2,3],123,0x10000124014004012182110536⟩,
  .pool ⟨41,29,[41,17,19,23,29],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,9,[31,3],[2,5,7],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨31,4,[31,2],[3],1025,0x1a20200070000000a800000000000002220000000000000000000000000000202020000000000000000000000000000000000000000000000000000000003000300030000000000000000000000000000000000000000000000000000000001010100000000000000000000000000001110000000000000054000000380010116⟩,
  .pool ⟨31,4,[31,2],[3],41,0x1b382b50736⟩,
  .pool ⟨31,5,[31,5],[2,3],41,0x1b382b50736⟩,
  .pool ⟨31,26,[31,2,13,17,19,23],[3,5,7,11],41,0x1fffffffffe⟩,
  .pool ⟨41,2,[41,2],[],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨41,17,[41,17],[2,3,5,7,11,13],403,0x43b050100875c098b63481880a2639640480658422200016240246800044421a60120269c645011812c6d1903ae10080a0dc2⟩,
  .pool ⟨41,11,[41,11],[2,3,5,7],61,0x1434026619900b0a⟩,
  .pool ⟨41,3,[41,3],[2],61,0x141002040810020a⟩,
  .pool ⟨41,11,[41,11],[2,3,5,7],819,0x400104020020000800004410100000804000000000120000080000000080010d00000882110000000c200200800200000100100008120800a01001100220200820000000000000000100800800020008120204000264000000300800100048a0000100902⟩,
  .pool ⟨41,27,[41,3,17,19,23],[2,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨41,7,[41,7],[2,3,5],915,0x20820000a6020080100022002020004090810c840040008001000021900200001029000000000000208000a00200041120840000008001000024340328000000840800209020000a6000886092502c021204100068220001000120008301200000060008120001000141100220a00108b0092⟩,
  .pool ⟨41,7,[41,7],[2,3,5],279,0x40200201200004021005000820800000000200220800000000901020348020001a2⟩,
  .pool ⟨61,10,[61,2,5],[3,7],41,0x1b382b50736⟩,
  .pool ⟨41,11,[41,11],[2,3,5,7],403,0x43b050100875c098b63481880a2639640480658422200016240246800044421a60120269c645011812c6d1903ae10080a0dc2⟩,
  .pool ⟨41,3,[41,3],[2],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨31,7,[31,7],[2,3,5],205,0x60111860280e10524000005100001520414841a008080011282⟩,
  .pool ⟨31,7,[31,7],[2,3,5],41,0x1fffffffffe⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨41,7,[41,7],[2,3,5],31,0x121d47b6⟩,
  .pool ⟨41,17,[41,17],[2,3,5,7,11,13],671,0x460044628a420410000104100345880766002208c0000802842400800e001280024009004100002600081000640000820090024001480070010024214010000310440066e011a2c0082080000820425146220062⟩,
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],41,0x1fffffffffe⟩,
  .pool ⟨41,17,[41,17],[2,3,5,7,11,13],341,0x10005e2024580224044800c418080600000c000180000060000c000018040608c0048809100689011e8002⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],41,0x1fffffffffe⟩,
  .pool ⟨31,5,[31,5],[2,3],451,0x2000800000000000082000100001000000088000008000000000000000000000040008800000024000040000000000800000082000022⟩,
  .pool ⟨31,27,[31,3,17,19,23],[2,5,7,11,13],41,0x1fffffffffe⟩,
  .pool ⟨41,26,[41,2,13,17,19,23],[3,5,7,11],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,17,[41,17],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,9,0xb0c060160b0c06016fa02413f3f902413f11a09c4e341a09c4e340b0c060160b0c06016067c3de0c067bbda0c198783c33198783c33f60b059ebf50b059e9058c8640b058c8640b0e070381c0e070381c167a3ce2c1679bca2c16064322c16064322cf20a051e3f10a051e11887038311887038310d86c361b0d86c361b0b0c060160b0c0601605864320b05864320b138bc5e27138bc5e2706783be0c0677bba0c0509c4e0a0509c4e0aee0b059dbed0b059d904f63ae0904f5baa0904753a6080474ba208e801c0fcfe701c0fcde672f95c9e471f8dc504020100804020100817713862e1770b822e03f037e0703efb7a07de02011bbdd02011b90402010080402010080381c0e070381c0e07dc6df6db5da6cf65b10402010080402010080381c0e070381c0e07d805029afd705029add602011abd502011a9d401c0fa7d301c0fa5040201008040201008d20b85da3d10b85da1d0050299fcf050299d080402010080402010ce020119bcd02011990a05028140a05028140381c0e070381c0e07cc0000197cb00001950a8542a150a8542a15040201008040201008ca64f2591c863f1d8d0463316080462b1208c401c0f87c301c0f8508048241008048241004020100804020100817613062e1760b022e04602fe08045fafa0803df2f60703deaf20700de2ee0100ddaea01ba5cee571b85bedd6d0402010080402010080381c0e070381c0e0705db2d60b05daad20bb40b05967b30b05965100281420100281420b20844363b108443611182c16231182c1623088844211088844211b0030195faf030195d100b45a20100b45a200f0743a1e0f0743a1eae0180d5bad0180d59ac0b05957ab0b05955aa02c1753a902c1751a8084434fa7084434d05080400a05080400aa6030194ba50301949058ac560b058ac560ba451e8d45a250e8541148a85429148a854291404422281404422281387c3e271387c3e27128984c25128984c25a0090493f9f090493d0e8783c1d0e8783c1d058140a0b058140a0b1182c16231182c162305088440a05088440a9e084433b9d0844339034e26e06034da6a0607cd2660f07cca620f0f880401f0f880401f0e8783c1d0e8783c1d980180d2f970180d2d964ae55299449e4d25920582d23910582d210cc823e190cc7a3a190e070381c0e070381c0d06c361a0d06c361a0c86432190c86432198e46e35198c45e2d150c86432190c86432198a44e25118843e1d0d0b0582c160b0582c16860140b0b850140b090b06030160b06030160b0582c160b0582c168441e0d058240e0501800582cff7f0582cfd7e0582cfb7d0582cf900be1ee0100bd9ea017a05c2ef37905c2ef1783bddced763add4e90b0582c160b0582c167439dcce57238dc4e1088542a11088542a117002412df6f02412dd0382c16070382c16070a05028140a05028140402c16080402c16080382814070382814070a371b6140a369b2140a02c16140a02c161404361ae0804359aa086a02412d36902412d10402010080402010080a3419e140a3399a140904c26120904c261207b31960f07b29920f0382c16070382c160708b218e1108b198a1103828140703828140708040201008040201006311860c06309820c0402c16080402c16086002010bf5f02010bd5e03c1ebb5d03c1eb905ae16e0b05ad96a0b0402010080402010080301c0e060301c0e0607024120e07024120e0581c0e0b0581c0e0b0402010080402010080681c0e0d0681c0e0d062d1660c062c9620c0402c16080402c16080501c0e0a0501c0e0a580180caf570180cad5602412ab5502412a9042a14e08042994a080402010080402010080301c0e060301c0e065228d44a15027d3c9d4e000009b4d00000994c25d2c954a24d24914823d1c8d4622d14894421d0c854220d0481020140a04020140a04401fcfc7d3e1ecf4793c00402773b0040275001d0e600001c8e200381bcdc6d361acd4693419ccc653218cc46101980be0301978ba032e008045b2d008045900960ae0100958aa012a00000532900000512813c9c4d2612c9449001208e00001188a002210c8441200fc7c3d1e0ec74391c0dc6c35⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_137 : ∀ i ∈ List.range' 137 30, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 167 at hi
  by_cases h0 : i < 137
  · exact test120_0 i (by simp only [List.mem_range'_1]; omega)
  exact test120_137 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨264,8,0xb421ed3c21edb421753c21757899ed0099ed789975009975b499b13c99b1b499393c99397821b10021b1782139002139dc71ed6471eddc7175647175dce9b164e9b1dce93964e939ac29e13429e1ac2969342969aca1a534a1a5aca12d34a12da0a1c9a0a151a0298da02915ec31ed7431edec3175743175b0a9ed38a9edb0a97538a975eca9b174a9b1eca93974a939b031b13831b1b03139383139b061c93861c9b06151386151b0d98d38d98db0d91538d915d439e95c39e9d439715c397198b1e920b1e998b17120b171d4b1ad5cb1add4b1355cb1359839ad2039ad9839352039358021e90821e98021710821718099ad0899ad809935089935d4e1c55ce1c5d4e14d5ce14d9869c52069c598694d20694dd469895c6989d469115c691198e18920e18998e11120e111e861e97061e9e86171706171acd9e934d9e9acd97134d971e8d9ad70d9ade8d93570d935ac61ad3461adac6135346135d0c1e958c1e9d0c17158c171d049ad5849add049355849359431dd1c31dd9431651c316594a9a11ca9a194a9291ca929e819c57019c5e8194d70194dac91c53491c5ac914d34914de89189709189e89111709111ac1989341989ac1911341911e801b97001b9e80141700141ac79b93479b9ac7941347941e8797d70797de87905707905ac017d34017dac0105340105a021d92821d9a02161282161a0999d28999da09925289925c409d94c09d9c409614c09618881d91081d9888161108161c4819d4c819dc481254c812588099d10099d880925100925dc69c16469c1dc694964694928e1c128e149dce18564e185dce10d64e10d28698528690db881c14081c1b88149408149b80985400985b8090d40090dc871d95071d9c871615071618ce9d914e9d98ce96114e961c8e99d50e99dc8e92550e9258c719d14719d8c7125147125ec59d97459d9ec5961745961b0d1d938d1d9b0d16138d161ecd19d74d19decd12574d125b0599d38599db05925385925ec41cd7441cdec4155744155ecb99174b991ecb91974b919c841c1c841498cb9c114b9c18cb94914b949c8b985c8b90d8c41851441858c410d14410d5029b550293d50a17950a101⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨61,27,[61,3,19,23],[2,5,7,11,13,17],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨61,27,[61,3,19,23],[2,5,7,11,13,17],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .prime 241,
  .pool ⟨41,31,[41,19,23,29],[2,3,5,7,11,13,17,31],51,0x21a0022996832⟩,
  .pool ⟨241,28,[241,2,7,19,23],[3,5,11,13,17],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨241,36,[241,2,3,19,23,29],[5,7,11,13,17,31],549,0x158cb06c33d40e2d4297f8dc406f5679dd53359bbee478b959444a2f8c9e5ba5bdb99c929788e1f3a2fb7f5d5ab176a0c9b4dd591c27437ff17825bf58e7f70df2fcf3b5e⟩,
  .pool ⟨61,29,[61,19,23,29],[2,3,5,7,11,13,17],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨41,20,[41,2,5,19],[3,7,11,13,17],819,0x6ca0984082d020108008a2014900020490000180990814022086110004080020820000000102900182820090026000080c048168120301000064009004141800940800000004104001020008861044028109901800009204000928045100108040b4102190536⟩,
  .pool ⟨41,33,[41,3,11,19,23,29],[2,5,7,13,17,31],153,0x8f809aee7a1c98d4831debd3d33e922a9dfa3a⟩,
  .pool ⟨61,23,[61,19,23],[2,3,5,7,11,13,17],533,0x12dc64720a2e548beccb115b365df890457c39c4f1e77012920a502415a1e23f2833053f11e16a090294125203b9e3c8e70fa88247ee9b36a234cdf44a9d1413898ed2⟩,
  .pool ⟨61,23,[61,19,23],[2,3,5,7,11,13,17],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨31,5,[31,5],[2,3],1575,0x4000002010000000000800000402000000000000000080000000000022000010080110002004000000000002000000800000400000400000100000080000000000020000410000010002004400002000020000400000000400000000080100000080000000000020000000080000002004400082000000000000880000400000000000110000080000000000020000010000010000000400082010020000000800010400000000000100002000000800000020000010000100002004000082010022⟩,
  .pool ⟨41,20,[41,2,5,19],[3,7,11,13,17],31,0x121d47b6⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],723,0x25841a0da4532d10024c94802114d92da29308065809228b21a0c80c00492410422020d02832da01940b2d309321261020b44368021a2d069b2996590496d86c868320a2926c10da6122802404532da44849b6502114806834c12⟩,
  .pool ⟨31,9,[31,3],[2,5,7],1525,0x141000866080000008181a0321481a000000c04080c1008600802004800284c21001225020004100848004860008000000000000000900408109001812000d02005001048c021294000408c800302100000011880008b0182308801019400a001400a60200443106034400046200000021030004c408000a52100c48200280102c00120600242040802400000000000000040018480048402080010291200210c8500048010040184020c04080c000001604a130160604000000419840020a⟩,
  .pool ⟨31,29,[31,19,23,29],[2,3,5,7,11,13,17],819,0xa00000000000000800240000200200005020841200a48200000208028000804008100020000344000300000000008200004000020100000020024000000000800200020004000020008848044000808100000004000240200100001840100008000a0c80002⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],1037,0x29c4012000802006083840220180b02088863006005ed0a9e1054a0809020011134414b0d80009a5321d130102208008003304200480431a00150ec038a0502030002470a0600114120082001180008460106812200008812c00191c880010800c91480802e0e812c000002032200440aa28a4140980c46808410429130a1892082⟩,
  .pool ⟨241,31,[241,19,23,29],[2,3,5,7,11,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨61,36,[61,2,3,19,23,29],[5,7,11,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨31,29,[31,19,23,29],[2,3,5,7,11,13,17],1037,0x29c4012000802006083840220180b02088863006005ed0a9e1054a0809020011134414b0d80009a5321d130102208008003304200480431a00150ec038a0502030002470a0600114120082001180008460106812200008812c00191c880010800c91480802e0e812c000002032200440aa28a4140980c46808410429130a1892082⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,9,0x8844000008844000000000000000000000000000221100000221100000201000000201000000000000000000008040000008040000000000000000000000000000000000000000000000000000000000000002391b0000235198c45c00008b45400000000000000000000000000000000000000008a44c000089444000000002210f000021d0d08040000008040000000000000000000000000000201000000201000000000000000000000000000000000000000000201000000201000000000000000000008040000008040000000000000000000000000000221100000221100000000000000000008844000008844000000000000000000000000000000000000000005028000005028000000000140a00000140a00000000000000000000000000000000000000000140a00000140a05028000005028000000002190b0000215090000000000000000008441c00008341400000000000000000000000000000000000000000000022110000022110000000000000000000884400000884400000a05000000a0500000000000000000000000000002814000002814000000000000000000000000000000000000000020903000020501000000000000000000803fc00007f3f400000000026130000026130000000000000000000984c00000984c00000000000000000000000000022110000022110000000000000000000884400000884400000000000000000000000000000000000000007e04800007d848000000000000000000000000001f41200001f21200000000000000000000000000000000000000001f0f700001ecf57a3cc0000793c40000000000000000000000000000000000000000783bc0000773b4000000001d8eb00001d4e900000221100000221100000000000000000008844000008844000000000000000000000000000000000000000000000201000000201000000000000000000008040000008040000000000000000000000008040000008040000000000000000000000000000201000000201000000000000000000008844000008844000000000000000000000000000221100000221108040000008040000000000000000000000000000201000000201000000000000000000000000000000000000000000100800000100800000000000000000004020000004020000002010000002010000000001d0e700001cce50000000000000000000000000000000000000000008040000008047238c000071384000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c0df00001bcdd6e36c00006d36400000000000000000000000000000000000000006c35c00006b354000000001a8d300001a4d100000000000000000000001a0cf000019ccd0000000000000000006632c00006532400000000000000000000000783c00000783c0000000000000000000000000001e0f000001e0f00000000000000000000000000000000000000000080400000080405028000005028000000000000000000000000000000000000000002010000002010000000000140a00000140a6431c00006331400000000188c30000184c10000000000000000000000000000000000000000180bf000017cbd5e2ec00005d2e40000000000000000000000000000000000000000070380000070380000000000000000000000000001c0e000001c0e0000000000000000000000170b7000016cb55a2cc0000592c40000000000000000000000000000000000000000582bc0000572b400000000158ab0000154a90000000000000000000000000000000000005429c00005329400000000000000000000000000148a30000144a100000000000000000000000000000000000000001409f000013c9d0000000000000000004e26c00004d2640000068340000068340000000000000000000000000001a0d000001a0d00000000000000000000000000000000000006030000006030000000000000000000000000000180c00000180c000000000000000000000000000000000000000013097000012c954a24c00004924400000000000000000000000000000000000000004823c000047234000000001188b000011489000000000000000000000000000000000000000011087000010c854220c0000412040000000000000000000000000000000000000000401fc00003f1f4000000000f87b00000f47900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005028000005028000000000060a00000060a00000000000000000000000000000000000000000140a00000140a0182800000182800000000000000000000000582c00000582c000000000000000000000000000160b00000160b05028000005028000000000120900000120900000000000000000000000000000000000000000140a00000140a04824000004824000000000000000000000000000000000000000000000000000000000000000000000000000004824000004824000000000f07700000ec750000000000000000000000000000000000000000012090000012093a1cc0000391c4000000000000000000000000000000000000000000000e06f00000dc6d361ac0000351a400000000000000000000000000000000000000003419c000033194000000000c86300000c46100000c05f00000bc5d0317000000316c00000000000000000000000000000000000000002d16400002c15c0000000000c56000000c550000000000000000000000000000000000000402000000402000000000000000000000000000010080000010080000000000000000000000000000000000002a14c000029144000000000000000000000000000a04f000009c4d00000984b0000094492411c00002311400000000000000000000000000000000000000002210c000021104000000000803f000007c3d00000000000000000000000000000000000000000783b0000074391c0dc00001b0d400000000000000000000000000000000000000001a0cc0000190c4000000000602f000005c2d00000000000000000000000000000000000004020000004020000000000000000000000000000100800000100800000000000000000000000582b0000054290000000000000000001409c00001309400000000000000000000000000000000000000000000010080000010080000000000000000000402000000402000000381c00000381c0000000000000000000000000000e07000000e070000000000000000000000048060000046061108400001007c00000000000000000000000000000000000000000f01800000e818000000000381b000003419000000000000000000000000000000000000000000000000000000000000a18000000a17000000000000000000028580000028540000000000000000000000000000000000000000000000804000000804018080000018080000000000000000000000000000000000000000020100000020100000000000602000000602008040000008040000000000201000000201000000000000000000000000000000000000000000201000000201008040000008040000000000000000000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_137 : ∀ i ∈ List.range' 137 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_274 : ∀ i ∈ List.range' 274 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_411 : ∀ i ∈ List.range' 411 37, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 448 at hi
  by_cases h0 : i < 137
  · exact test240_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h137 : i < 274
  · exact test240_137 i (by simp only [List.mem_range'_1]; omega)
  by_cases h274 : i < 411
  · exact test240_274 i (by simp only [List.mem_range'_1]; omega)
  exact test240_411 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨61,27,[61,3,23],[2,5,7,11,13,17,19],133,0x1430126400024e0721381c90000992030a⟩,
  .pool ⟨37,20,[37,2,5],[3,7,11,13,17,19],1159,0x1002100018030000000280000e44000110000100088001000005f82120004000121600000000070000018081004002000001001023aa8008020c00010020100501020842284540504040410000002a014010001003c100804600003001010800010410000201004310080b8c8890000184041900a0041100124001094012040122500250481184210c0c852122310536⟩,
  .pool ⟨37,22,[37,2,11],[3,5,7,13,17,19],1159,0x6cb08e5484b9333084218a920a4e4e448130480390888249008825fd21b8206180121f1131d0100fc20081c081086082001081801c23aae209028fc0090028128555020842aa47425a42e255421040aaa14814009003f140904755c438018108004106108103810043f0080b8c88f8480186041d84bfa4110092411109c0120c8122727250495184210ccc9d212a710d36⟩,
  .pool ⟨61,27,[61,3,23],[2,5,7,11,13,17,19],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨37,20,[37,2,5],[3,7,11,13,17,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨37,22,[37,2,11],[3,5,7,13,17,19],793,0x1a342980230a1004202c12310c000490640032c0082068091290011044c20800e08100152822810012052404a240420808631840410809148092812002051052a002041c00410c8822002522405810400d300098248000c23120d010802143100650b16⟩,
  .pool ⟨41,31,[41,23,29,31],[2,3,5,7,11,13,17,19],1615,0x121806900539821404261bc6d01842301071192d038eb02ce3400690300c1a0413006a4202870da7015ec4a9ca1008a4b80a2044153882111a4110a153c81034020a10153c8d205c4519c12b54b7886a011236ace5319c92a48d13044194cc219a8511c85944243506225ac4844d53124298244242508803331ea18402400a74054941d8460047630eb591e7081462b564235296a14358da2720ca2bd484288c015612080e399ca0b9275b0687a1c619cc3081e2021e40256053d231a5a41806838dc5324213b4856396⟩,
  .pool ⟨37,20,[37,2,5],[3,7,11,13,17,19],41,0x1b382b50736⟩,
  .pool ⟨41,31,[41,23,29,31],[2,3,5,7,11,13,17,19],73,0x1fffffffffffffffffe⟩,
  .pool ⟨37,20,[37,2,5],[3,7,11,13,17,19],123,0x10000124014004012182110536⟩,
  .pool ⟨41,38,[41,2,23,29],[3,5,7,11,13,17,19,31,37],657,0x1b28325128308808220169020200160125205009a60800201121000008a0004830c860009800020b20b4134100006400184c304800144000021220100041964028129201a00101025a0110404430522930536⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],777,0x1a2124596090ca49a4020d029360921a60800060029904264868a44208205a60a01300141144a01001221a0c049121b48304b6122480c161120020148a20a00320141968104108945849908265001800041961241b2502c10096494c241a6892116⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],1615,0x121806900539821404261bc6d01842301071192d038eb02ce3400690300c1a0413006a4202870da7015ec4a9ca1008a4b80a2044153882111a4110a153c81034020a10153c8d205c4519c12b54b7886a011236ace5319c92a48d13044194cc219a8511c85944243506225ac4844d53124298244242508803331ea18402400a74054941d8460047630eb591e7081462b564235296a14358da2720ca2bd484288c015612080e399ca0b9275b0687a1c619cc3081e2021e40256053d231a5a41806838dc5324213b4856396⟩,
  .pool ⟨73,4,[73,2],[3],41,0x1b382b50736⟩,
  .pool ⟨73,7,[73,7],[2,3,5],19,0x30af2⟩,
  .pool ⟨41,33,[41,3,11,19,23,29],[2,5,7,13,17,31],459,0x23a026bb9683263520c77af4e4cfa088a77e0e91f00355cf43921a9023bd7a7a63d24553bf4748f809aee7a1c98d0831ceb53d33e922a99fa3a⟩,
  .pool ⟨73,31,[73,23,29,31],[2,3,5,7,11,13,17,19],1463,0x425082205d50c081122a62200a1549443064c1d892c180805408c063661c231210a042825b053e6849618f1438541d01036744195a0112d4a687906a5180e42191201cc4024189048338f51261aac39d121832806d5bb56200f91323003f20502001e692a7124038226985102034da264d939c46e9705388d23428541a8244853d2425d1102f5e035441c300690d21024d01b0ad5aa73431839028dc8f50f87a6424c42c50f0d945038f3328a8b336c4d4015ab87135e⟩,
  .pool ⟨73,4,[73,2],[3],117,0x1a2420812002010c20100120410916⟩,
  .pool ⟨31,20,[31,2,5],[3,7,11,13,17,19],1159,0x131f43ba305a8b894a10278cd59fd483219c1245092bd0a1a27787faa364d05a5816d6a00608217704c20d8ea710d9529c4c3b3e906fbb89cc4a7c20f74572d93781033de27cdd41557944c118432f7e1164b11c10f3c1accc6e0201f283234dc6a564b51a8e0fbcd71178ef9fda9493e5a564d92aa01c11ba3a74236f5cb7c65b3ad006544e1be7ad4c2ea5b3a2350736⟩,
  .pool ⟨31,20,[31,2,5],[3,7,11,13,17,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨31,20,[31,2,5],[3,7,11,13,17,19],37,0x1ffffffffe⟩,
  .pool ⟨41,38,[41,2,23,29],[3,5,7,11,13,17,19,31,37],935,0x1021409022104c3114808160530a00a024625854194062c45720e1198410188500d6579082785226002c334412808b120227a5c11b84613c685310610129580634000a339622bc254910c3bd03308096900500ce54a5a352447098015818e525c50190c2b8c72b10712cec5212c534ab12d85335e⟩,
  .pool ⟨41,31,[41,23,29,31],[2,3,5,7,11,13,17,19],1197,0x102800c148100300300820808200000900804800000020204940048b08b2002090c06412084880c200a61a00064800040005020a60304001909000009204009924201808060b44140008200104000a08b4180406010926400812400002426000830194102800080004980016194010c04484120980c241001344344800a48101000000048040240000104041040300300204a0c00502⟩,
  .pool ⟨61,34,[61,2,17,23,29],[3,5,7,11,13,19,31],1463,0x425082205d50c081122a62200a1549443064c1d892c180805408c063661c231210a042825b053e6849618f1438541d01036744195a0112d4a687906a5180e42191201cc4024189048338f51261aac39d121832806d5bb56200f91323003f20502001e692a7124038226985102034da264d939c46e9705388d23428541a8244853d2425d1102f5e035441c300690d21024d01b0ad5aa73431839028dc8f50f87a6424c42c50f0d945038f3328a8b336c4d4015ab87135e⟩,
  .pool ⟨31,27,[31,3,23],[2,5,7,11,13,17,19],1295,0x4402421401c201803210047b40c1102d1004b09021411246a8a2014e50302450da252101124cf5192400d422046070d207898d48d08105230b826000a150c207300e78909724c431102531c70a1aa33028218604110b6250d09106528006b10b30c452bd48380a330c4e304c44200720d0b11ca950d6c10500489463314b009452b1e1014a92a80c315873a4c21a5641b16461009734a13a56a41d85389cd1b5e⟩,
  .pool ⟨31,27,[31,3,23],[2,5,7,11,13,17,19],333,0x143c886dd28d40806330b9691742a95990d3a1188804462172c266a550ba25a743318040ac52ed844f0a⟩,
  .pool ⟨31,27,[31,3,23],[2,5,7,11,13,17,19],949,0x175663565e83704f610d7e83069a2c1342e3a4641549fb43bb08c49a9967f79738894ed4187a1e4ea63621f400946bc59106a9b94f6ce050b1a218000611634281cdbca765582268f58a400be11b195c9e17860adca4473a7bf9a65648c43770b7e4aa098971d0b20d1658305fac21bc83b05e9ab19aba⟩,
  .pool ⟨37,20,[37,2,5],[3,7,11,13,17,19],1209,0x1b2832512930d90c225929028a48069121209b49220804320221960045a6190c205960161b6982092024020404d129201160201a08b44040809a61b04a4d068024009a08a41008b04b28b20b4134534834402094416400900582c948361964040808b44160101a2012522c808100901241065b61a01a6810c261968801a61101308041124b6412122580494502526910c26c32522930536⟩,
  .pool ⟨31,27,[31,3,23],[2,5,7,11,13,17,19],369,0x161a2854c32120846124148b0e06516ac1442a182c0412852080d061508a0d5a2981c344a092188412130ca85161a⟩,
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],511,0x802100110042c00080000c20200000100000008108011140005800000010041400800240b4580030000a00a01480c200c0000048800190800812286840122⟩,
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],925,0x11a4805dc2a46c406a940a201340255908d8958ec804d628d26026e15236203d48051408a012ac046d4a8764824b1469201370a91b101aa40a880454095602362543b201258a349049b854ad880d5201440a2804af011b12a1d90192c51ac804dc6a46c426a900b201140a55808d8950ee804962⟩,
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],629,0x1390a3f9d2c151b124817ea6333196b7df18f9e705509a0b96c0d3a4770c13402156c1ed41911752ba2260ade0daa100b20c3b8972c0da741642a839e7c63efb5a6333195fa0492362a0d2e7f14272⟩,
  .pool ⟨37,22,[37,2,11],[3,5,7,13,17,19],465,0x1a25248921865208201a00b08825125060004a2010132c02020034884c30c844b0010100d32020114800182922904434016010412986124492916⟩,
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],1025,0x13002250400008002800a00a020004030100000400000010002008005000000860a0000100400020200800000020200000802100400080004802000000092200000112400000010048000400080210040000101000000040101000080200001418400000280040100020000000800002030080010140140050004000082910032⟩,
  .pool ⟨31,27,[31,3,23],[2,5,7,11,13,17,19],999,0x50f201b7423102008cc2e5a45d0aa166434e042220011085c9099a9502e896950cc60102314b96013c2a87910d3a11a8100466152d22e8150b32127023100008c40e484cd0a81744b4a866200815885cb089e1543c8069d28c40806330a9691740a9599093a1088004442072c2668550ba25a7433100408c42ed804f0a⟩,
  .pool ⟨31,27,[31,3,23],[2,5,7,11,13,17,19],135,0x116063c45780ab131626bc055898f135e⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],247,0x7ac8a0918840830680847404810a013c805081202e210160c102118905135e⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],135,0x116063c45780ab131626bc055898f135e⟩,
  .pool ⟨31,6,[31,2,3],[5],189,0x1eb22824620160c5b4605009e402818b68c1a0118905135e⟩,
  .pool ⟨31,6,[31,2,3],[5],247,0x7ac8a0918840830680847404810a013c805081202e210160c102118905135e⟩,
  .pool ⟨31,29,[31,23,29],[2,3,5,7,11,13,17,19],1025,0x1a20304178408108ea00800210080202a720000200001520080006004020043220a820001001012100000000088820000240104000e00000c00020001081392030127204200010000c00001c000820090000104440000000021202002000105411308010080180004012a0000100001395010040210004015c4204087a0830116⟩,
  .pool ⟨31,29,[31,23,29],[2,3,5,7,11,13,17,19],37,0x10ac804d42⟩,
  .pool ⟨31,6,[31,2,3],[5],135,0x116063c45780ab131626bc055898f135e⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,6,0xa28a2baeba28a2baeba28a28a28a28a28a28aebae8a28aebae8a28aebae8a28a28a28a28a28a2baeba28a28a28aebae8a28aebae8a28aebae8a28a28a28a28a28a2baeba28a2baeba28a2baeba28a28a28aebae8a28a28a28a28a28a2baeba28a2baeba28a2baeba28a28a28a28a28a28aebae8a28aebae8a28a28a2baeba28a2baeba28a28a28a28a28a28aebae8a28aebae8a28aebae8a28a28a28a28a28a2baeba28a28a28aebae8a28aebae8a28aebae8a28a28a28a28a28a2baeba28a2baeba28a2baeba28a28a28aebae8a28a28a28a28a28a2baeba28a2baeba28a2baeba28a28a28a28a28a28aebae8a28aebae8a28aebae8a28a28a28a28a28a2baeba28a2baeba28a2baeba28a28a28a28a28a28aebae8a28aebae8a28a28a2baeba28a2baeba28a28a28a28a28a28aebae8a28aebae8a28aebae8a28a28a28a28a28a2baeb9e79e79e7a28a279e7a28a279e7a28a279e79e79e79e79e79e8a289e79e8a289e79e8a289e79e79e7a28a279e79e79e79e79e79e8a289e79e8a289e79e8a289e79e79e79e79e79e7a28a279e7a28a279e7a28a279e79e79e79e79e79e8a289e79e8a289e79e8a289e79e79e79e79e79e7a28a279e7a28a279e79e79e8a289e79e8a289e79e79e79e79e79e7a28a279e7a28a279e7a28a279e79e79e79e79e79e8a28aaaa6aa6aa6aaa9aaaaaaa6aa6aaa9aa9aaaaaaa69aaaaaaa6aa6aaa9aa9aaaaaaa6aaa9aa9aa9aaaaa9aa9aaaaaaa6aaa9aa9aa9aaaa6aaaaaa9aa9aaaaa9aa9aa9aaaa6aaaaaa9aa9aaaa6aa6aaaaaa9aaaa6aa6aa6aaa9aaaaaaa6aa6aaa9aa9aaaaaaa69aaaaaaa6aa6aaa9aa9aaaaaaa6aaa9aa9aa9aaaaa9aa9aaaaaaa6aaa9aa9aa9aaaa6aaaaaa9aa9aaaaa9aa9aa9aaaa6aaaaaa9aa9aaaa6aa6aaaaaa99e79e8a289e79e8a289e79e79e79e79e79e7a28a279e79e79e8a289e79e8a289e79e8a289e79e79e79e79e8a289e79e8a289e79e79e79e79e79e7a28a279e79e79e8a289e79e8a289e79e8a289e79e79e79659659659a69a59659a69a59659a69a59659659659659659669a69659669a69659669a69659659659a69a59659659659659659669a69659669a69659669a69659659659659659659a69a59659a69a59659659669a69659669a69659659659659659659a69a59659a69a59659a69a59659659659659659669a69659659659a69a59659a69a59659a69a59659659659659659669a69659669a69659669a69659659659a69a59659659659659659669a69659669a69659669a69659659659659659659a69a59659a69a59659659669a69659669a69659659659659659659a69a59659a69a59659a69a59659659659659659669a69659669a69659669a69659659659659659659a69a59659a69a59659a69a59659659659659659669a69659659659a69a59659a69a59659a69a59659659659659659669a69659669a69659669a69659659659659669a69659669a69659659659659659659a69a59659a69a59659a69a59659659659659659669a69659659659a69a59659a69a59659a69a59659659659659659669a69659669a69659669a69659659659659659659a69a59659a69a59659a69a59659659659659659669a69659669a69659669a69659659659a69a59659659659659659669a69659669a69659669a69659659659659659659a69a59659a69a59656e36db1db9249076db9249236db92491b6e36db1db6e36db1e49246c76e49246e36e49248db6c76db92491b6e36db1db8db6c76e49241db6e49248db6e49248db6c76db6db8db6c792491b1db92491b8db25b6e49248db6e49246db8db6c96e36db25b92491b25b92491b8db9249236db25b6db6e36db2649246e36db25b9249096db9249236db92491b6e36db25b6e36db2649246c96e49246e36e49248db6c96db9249236db1db6db6e36db1e49246c76e49246e36e49246e36db1db8db6c76db92491b6c792491b6e36c76e49246e36e49248db6c76db6db8db6c792491b6c792491b6e392491b8db6c76e36db1db6e49246db2649246db8e49246e36db25b8db6c96db9249096db9249236db92491b6e36db25b8db6c96e49248db6c96db92491b6c992491b6e392491b8db6c96db8db6c96e492425b6e49248db6e49246db8db6c979e81e79f79e89e7de7a279e81e89e7a079e7de7a079e7de7a279e79e7de7a279e81e89e7a079e7de89e7a079e7de79e7a079e7de7a279f79e89e7a079e89e7a079e7de81e79f79e89e79e79f79e89e7a07a279e81e79f7a079e7de7a279e79e7de7a279e81e7a279e81e79f7a079e7de7a279f79e89e7a079e79e7de7a279e81e89e7a079e7de81e79f79e89e79f79e89e7a079e79e89e7a079e7de81e79f79e89e92491b8db6dc6e36db71b6e49246db7249246db8e49246db8db6dc6e36db71b92491c6db9249236db6db7249246db8e49246e36db71b8db6dc6db92491c6db9249236db92491b6e36db71b8db6dc6e492471b6e49248db6e49246db8db6dc6e36db71b92491b71b92491b8db9249236db71b6db6e36db7249246e36db71b92491c6db9249236db92491b6e36db71b6e36db7249246dc6e49246e36e49248db6dc6db9249236db71b6db6e36db7249246dc6e49246e36e49246e36db71b8db6dc6db92491b6dc92491b6e36dc6e49246e36e49248db6dc6db6db8db6dc92491b6dc92491b6e392491b8db6dc6e36db71b6e49246db8db6dc92491b71b92491b8db9249236db71b6e36db71b6e49246db7249246db8e49246e36db71b9249236db71b6db6e36db7249246dc6e49246e36e49246e36db71b8db6dc6db92491b6dc92491b6e369d75d75a75a75d69d69d75d75a75d69d69d69d75d69d69d75d75a75d69d69d69d75a75d75d69d69d75d69d69d69d75a75d75d69d69d75a75a75d75d69a75d75d69d69d75a75a75d75d69d75a75a75a75d75a75a75d75d69d75a75a75a75d69d75d75a75a75d75a75a75a75d69d75d75a75a75d69d69d75d75a69d75d75a75a75d69d69d75d75a75d69d69d69d75d69d69d75d75a75d69d69d69d75a75d75d69d69d69d75d75a75a75d69d69d75d75a75d69d69d69d75d69d69d75d75a75d69d69d69d75a75d75d69d69d75d69d69d69d75a75d75d69d69d75a75a75d75d69a75d75d69d69d75a75a75d75d69d75a75a75a75d69d75d75a75a75d69d69d75d75a75d69d69d69d75d69d69d75d75a75d69d69d69d75a75d75d69d69d75d69d69d69d75a75d75d69d69d75a75a75d75d69a75d75d69d69d75a75a75d75d69d75a75a75a75d7a281e81f79f8a07de7e27a281e89e7e07a27de8207a27de82279f7a07de7e27a281f89e8a07a07de89e7e07a27de81e8a07a07de7e281f79f89e8a079f89e8a07a07de81e89f7a089e7de81f79f89e8a08a07a07de7e279f7a089e7e07a279f89e8a07a07de8a07a07de7e281f79f89e8a07a279f81e89f7a079f89e8a07a07e281e81f79f89e7de82279f81e8a279f81e89f7a07a281e81f79f8a07de7e27a281e79f85e8607a07e181e81f79f85e7de82179f81e86179f81e85f7a07a181e81f79f8607de7e17a181e7de82179f81e85e7e17a181e81f8607a07de7e17a07de7e17a181e85e7e07a17de81e8607a07de7e181f79f85e8607a179f81e85f7a07a181e81f79f85e81f79f85e8607e17a181e81f7a07a17de82179f7a181e81f79f8607de7e17a181e85e7e07a17de8207a17de82179f7a07de7e17a181f85e8607a07de69d75d75a75a75d69d69d75d75a75d69d69d69d75d69d69d75d75a75d69d69d69d75a75d75d69d69d75d69d69d69d75a75d75d69d69d75a75a75d75d69a75d75d69d69d75a75a75d75d69d75a75a75a75d75a75a75d75d69d75a75a75a75d69d75d75a75a75d75a75a75a75d69d75d75a75a75d69d69d75d75a69d75d75a75a75d69d69d75d75a75d69d69d69d75d69d69d75d75a75d69d69d69d75a75d75d69d69d69d75d75a75a75d69d69d75d75a75d69d69d69d75d69d69d75d75a75d69d69d69d75a75d75d69d69d75d69d69d69d75a75d75d69d69d75a75a75d75d69a75d75d69d69d75a75a75d75d69d75a75a75a75d69d75d75a75a75d69d69d75d75a75d69d69d69d75d69d69d75d75a75d69d69d69d75a75d75d69d69d75d69d69d69d75a75d75d69d69d75a75a75d75d69a75d75d69d69d75a75a75d75d69d75a75a75a75d75a75a75d75d69d75a75a75a75d69d75d75a75a75d75a75a75a75d69d75d75a75a75d69d69d75d75a69d75d75a75a75d69d69d75d75a75d69d69d69d75d69d69d75d75a75d69d69d69d75a75d75d69d69d64469c69b6996da6dc65b6846996da65a6446dc69a6446dc69b69971a6da65b6446996da11a65a6dc6da65a6446dc69911a71a6da65b69b7196da11a6596da11a65a6dc69911b71a6da65c69b6996d911a75a75a75d75d69d75a75a75a75d69d75d75a75a75d75a75a75a75d69d75d75a75a75d69d69d75d75a69d75d75a75a75d69d69d75d75a75d69d69d69d75d69d69d75d75a75d69d69d69d75a75d75d69d69d11a65a6dc65b69b71a6da65a6446996d911a71a6d911a71a6da65b69b7196da11a65b69969911b71a6996d911a71a6c469969b7196da6dc69b69969911b69969911b71a64469c69b6996da6dc65b68469914960960560525814914960960525815814914961814914960960525815814914960525825815814925815814914960525825815814960524525825814525825815814960524525825814960560524525814960960560525814914960960525815814914961814914960960525815814914960525825815814925815814914960525825815814960524525825814525825815814960524525825814960560524525830d34d34c34c34d30d30d34d34c34d30d30d30d34d30d30d34d34c34d30d30d30d34c34d34d30d30d34d30d30d30d34c34d34d30d30d34c34c34d34d30c34d34d30d30d34c34c34d34d30d34c34c34c34d34c34c34d34d30d34c34c34c34d30d34d34c34c34d34c34c34c34d30d34d34c34c34d30d30d34d34c30d34d34c34c34d30d30d34d34c34d30d30d30d34d30d30d34d34c34d30d30d30d34c34d34d30d30d30d34d34c34c34d30d30d34d34c34d30d30d30d34d30d30d34d34c34d30d30d30d34c34d34d30d30d34d30d30d30d34c34d34d30d30d34c34c34d34d30c34d34d30d30d34c34c34d34d30d34c34c34c34d30d34d34c34c34d30d30d34d34c34d30d30d30d34d30d30d34d34c34d30d30d30d34c34d34d30d30d34d30d30d30d34c34d34d30d30d34c34c34d34d30c34d34d30d30d34c34c34d34d30d34c34c34c34d1d71571471475c51d71d71571475c51c51d71d71451d71d71571475c51c51d71d71475c55c51c51d75c51c51d71d71475c55c51c51d71475c75c55c51c75c55c51c51d71475c75c55c51d71471475c75c558524525624a14958528524525614928958558524524a25615614958524525624a1495852852452561d71571471475c51d71d71571475c51c51d71d71451d71d71571475c51c51d71d71475c55c51c51d75c51c51d71d71475c55c51c51d71475c75c55c51c75c55c51c51d71475c75c55c51d71471475c75c514958958528525614914928958524a1561491495892855852452561495895852852561491492895854d55154d44d35535154d54d55135534d44d55154d44d55154d54d35535134d54d55135535544d35155534d44d55154d35545535134d54d45535535544d35535544d35155135545535534d54d44d35535545544d35154d54d45535534d44d54d35535545535135545535134d54d45535535544d54d35135545534d35535545535155134d45535535154d54d35135554d35135545534d55154d44d35535154d54d55131493c94854452521491494493c525114f14914948f1491494894452521511491493c525124f15214925114f14914948524f25215114948524525124f14525124f1521493c524525225114948544524524f3851c51d01cf1474053c51c51ce1473c73854051c73854051c51cf1474073c53851cf1471473874051473c73854051ce1471474073c51d014f14714738f1471473874051ce1501471473c51d01cf14e1471494493c548524f1491494894452521511491493d11491493c948524f15214914944525225114f1492521511491493c525124f1521493c524525225114525225114f14944524524f2521493c54852452511473874053c51d01471473c73851cf14e14714740e1471474073c51d014f1471473851cf1ce1501471cf14e1471474051ce1d014f1474051c51cf1ce1451cf1ce1501473851c51d01cf1474053c51c51ce30d2cd34b34c2cd2cd30b34d2cc2cd30b30d2cd34b30d2cd34b34c34d2cd30b30d2cc2cd34b30d2cd2cd30b30d2cd34c34b34d2cd30b34b34c2cd34b30c2cd34b30d2cd2cc34b34d2cd30d34b34c2cc34b34b34c2cd34b30b34c2cc34b34d30d2cd34b34c2cd34b34c2cc34b30b34d2cc34b34b30d2cd34b34c30d2cd34b34c2cd2cd30b34d2cc2cd30b30d2cd34b30d2cd34b34c34d2cd30b30d2cc2cd34b30d2cd30b34d2cc34b34b30d2cd34b34c34d2cd30b30d2cd30b30d2cd34b34b30d2cd30b34b34d2cd30b30d34d2cd30b30d2cc2cd34b30d2cd2cc34b34d2cd30b34d2cd30b30d34c2cc34b34d2cd2cc34b34c2cd2cd34b34c2cc34d30b30d2cd34b34b30d2cd30b34d2cd30b34d2cc2cd30b30d2cd34c34b34d2cd30b34b30d2cd30b34b34d2cd30b30d34c2cc34b34d2cc34b34d2cd30b34b34c2cd34b30b34c2cc34b34d2cc34b34d2cd30d34b34c2cc34b30b34d2cc34b34d2cc34b34c2cd2cd34b34c2cc34d30b30d2cd34b30b34d2cc34b34b30d2cd34b34c34d2cd30b30d2cd30b30d2cd34b34b30d2cd30b34b34d2cd30b30d34c2cc34b34d2cd2cc34b34c2cd2cd34b34c2cc34b34c2cc34b34d30d2cd34b34c2cd2cd30b34d2cc2cd34b34c2cc34d30b30d2cd34b34b30d2cd30b34d2cd30b34d2cc2cd30b30d2cd34c34b34d2cd30b24a14a14914928524a24a14a14928524524a24a14a14914928928524a14a14914928524a24a14a1491471872051851c81471471871851c61461471472061471472071851c81461471471851c61c61481471c61461471472051c61c81461472051c51c61c61451c61c61481471851c51c81c61472051851c51c624a14a14914928524a24a14a14928524524a24a14a14914928928524a14a14914928524a24a14a1491c61481471471851c81c61461471851c51c61c81451c61c81461472051c51c61c61471851851c51c81851c51c61c81471852051c51c61472071851851c71851851c51c81471872051851c81471471871850c21020400400810020020421030810040c20020420401030800810c21020400400810020020421030020421030400840c20020420400810010020c21020400400830840020421030400840c2002042040⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_40 : ∀ i ∈ List.range' 40 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_80 : ∀ i ∈ List.range' 80 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_120 : ∀ i ∈ List.range' 120 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_160 : ∀ i ∈ List.range' 160 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_200 : ∀ i ∈ List.range' 200 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_240 : ∀ i ∈ List.range' 240 24, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 264 at hi
  by_cases h0 : i < 40
  · exact test720_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : i < 80
  · exact test720_40 i (by simp only [List.mem_range'_1]; omega)
  by_cases h80 : i < 120
  · exact test720_80 i (by simp only [List.mem_range'_1]; omega)
  by_cases h120 : i < 160
  · exact test720_120 i (by simp only [List.mem_range'_1]; omega)
  by_cases h160 : i < 200
  · exact test720_160 i (by simp only [List.mem_range'_1]; omega)
  by_cases h200 : i < 240
  · exact test720_200 i (by simp only [List.mem_range'_1]; omega)
  exact test720_240 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+14=2^a*7^b*19^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=1 ∧ b%12=1 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  have h720 := run720 h bad h240
  obtain ⟨i,hi,_⟩ := h720
  exact Nat.not_lt_zero i hi
end D14


namespace D15
private def cfg : Config := ⟨15,3,5,19,1,1,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨23,4,0x7aba7b14b41bba92795498193a76779470177a5a75145415ba32735438133a1671941⟩
private def rows12 : List Rule := [
  .div 13,
  .div 7,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,5,0x8421080210842008421c8421084010842008421080210840108421004210e02108420084210042108401084210842108021084200842100421086e1084200842108021084010842100421080210843608421004210840108421004210840108421084210802108420084210042108401084200842108021084010842100421080210842008421004210840108421084210802108420084210042108401084200842108021084010842100421080210842008421080210842008421a8421084010842108421080210842008421004210840108420084210d021084010842100421080210842008421004210866108421084210802108420084210042108401084320842108021084010842100421084010842100421080210842008421004210840108421084210802108420084210042108401084200842108021084010842100421080210842008421004210840108421084210802108420084210042108401084200842108021084200842108021084010842188421080210842008421004210840108421084210c02108420084210042108401084200842108021085e1084210042108021084200842100421084010842108421080210842e0842100421084010842100421084010842008421080210840108421004210802108420084210042108401084210842108021084200842100421084010842008421080210840108421004210802108420084210042108401084210842108021084200842108021084200842168421084010842008421080210840108421004210b0210842008421004210840108421084210802108420084210042108561084200842108021084010842100421080210842a0842100421084010842100421084010842108421080210842008421004210840108420084210802108401084210042108021084200842100421084010842108421080210842008421004210840108420084210802108401084210042108021084200842108021084200842148421084010842108421080210842008421004210840108420084210a02108401084210042108021084200842100421084e108421084210802108420084210042108401084260842108021084010842100421084010842100421080210842008421004210840108421084210802108420084210042108401084200842108021084010842100421080210842008421004210840108421084210802108420084210042108401084200842108021084200842108021084010842128421080210842008421004210840108421084210902108420084210042108401084200842108021084610842100421080210842008421004210840108421084210802108422084210042108401084210042108401084200842108021084010842100421080210842008421004210840108421084210802108420084210042108401084200842108021084010842100421080210842008421004210840108421084210802108420⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨121,6,0xadfb59feee7e3bb75e867bd01ed00634195c2df939fe4ededcabb424ed6b7842ae1c87866dd53ab5727d56935421d5cb725aac9819e6c079831b6c66d50db54961e19860361e3156095521956c355501554649e0d276df7487dc6debaabade1eb4b77f6adf79f7c6ad3a9f4f67c71871f0977619dc096b919acc36bc197d835f0017e43533014e49476011eedf5e9fd624f58aba4a7e9b93a561e92b776eadd59f7621dd5b7462dc5b9f17a1c5131d50675701d50c69d25a44369a01a4495da1975035dd01774651725144645401166df33abcdaae739f6c24cf6b70f21c3219cec373e0d9ec05b8313d4943e190c6af1a9fc524f1d9f9461e5db76467d9487646dcdaab3527cd787352dc1dab05e7c1⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,2,[61,2],[],31,0x68818116⟩,
  .pool ⟨31,9,[31,3],[2,5,7],80,0xa08800220a⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],112,0xf59161ab1d034ee58171ab0d135e⟩,
  .pool ⟨31,3,[31,3],[2],80,0xa08800220a⟩,
  .pool ⟨31,3,[31,3],[2],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,19,[61,17,19],[2,3,5,7,11,13],744,0x200020820a00820008800200228a20028208008020200000808020020828008a28800800220008200a08208000808828a08008028208a20228828800008a00820a00a08828a28220a00a08200a20000228228808a20828020020a2822⟩,
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,3,[61,3],[2],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,4,[31,2],[3],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,4,[31,2],[3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,2,[31,2],[],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,14,[61,2,7],[3,5,11,13],496,0x1953b315751d33b1bd9311d11dbd570b7fd1db9dbb39d1b133dbf77b313f9a5d17f751315977f1f9d7559559f9134f3b959fd9ff7d95b5779fb33f757bde⟩,
  .pool ⟨31,2,[31,2],[],488,0x15139115d75315515155119713d11313935195911751d1d593d5d5111397071557d79191559151d317d595d3555357d15715d793d3d397531197d55796⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],16,0x8002⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],48,0x190014116⟩,
  .pool ⟨61,2,[61,2],[],112,0x131050301332215211107152736⟩,
  .pool ⟨31,9,[31,3],[2,5,7],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,3,[31,3],[2],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨31,2,[31,2],[],16,0xd117⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],560,0xf5b1c723d8153c0d59d0a119ad5210d31141519254912b714e5331243910738d831b1ab1b183639c1138491994e51da91254931505119610956b310a17356079503789c71b5e⟩,
  .pool ⟨31,4,[31,2],[3],112,0xd111410311034005811181051116⟩,
  .pool ⟨61,6,[61,2,3],[5],112,0x1131950bd9b33a5571d14f9db77e⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],336,0x109004901221869a0832504814094436582cb0d261109104901320869b0932514914084536582db0d36⟩,
  .pool ⟨61,14,[61,2,7],[3,5,11,13],176,0xf79d59f91341d57b31379ab3d919bd5705913f3573de⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,8,0x9500190000000000009400170000000000001b00000000001b000b000000000000190000000000001c00170000000000170000000000001b009300000000000019001a00000000009200000000000017001b0000000000001c00000000000019190000000000001800000000000017001b0000000000001a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000170000000000001b009100000000000019009000000000001c00000000000017001b0000000000000b00000000000019190000000000001a00000000000017001b0000000000008f00000000001c00190000000000008e00170000000000001b00000000001b001a000000000000190000000000001800170000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008d00160000000000008c00090000000000001500000000008b008a000000000000070000000000008900080000000000880000000000008700140000000000001600860000000000850000000000008400830000000000008200000000000081800000000000007f0000000000000a0015000000000000140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000900150000000000007e00000000000016007d00000000007c00000000000008007b0000000000007a0007000000000016000000000000790078000000000000770000000000001476000000000000750000000000007400730000000000007200000000001500140000000000007100700000000000000a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006f000000000000120000000000001100030000000000006e00000000006d006c0000000000001200110000000000006b00000000006a00690000000000006800000000000012001100000000001100000000000067006600000000000013001200000000001200000000000011006500000000000003000000000000640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000030063000000000000620000000000001200110000000000110000000000006100600000000000005f001200000000001200000000000011005e0000000000005d0000000000005c130000000000001200000000000011005b0000000000005a000000000003005900000000000012001100000000000058000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000057000000000000100056000000000000550000000000000d0d0000000000005400000000000053005200000000000051000000000050004f0000000000004e000e0000000000004d00000000004c000b0000000000000d0000000000000f000e00000000004b0000000000000b004a0000000000000c00490000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000048000d0000000000004700100000000000004600000000004500440000000000000d00000000000043004200000000000e0000000000004100400000000000003f003e00000000000f0000000000000e003d0000000000000b0000000000000d0c0000000000003c0000000000003b000b0000000000003a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000039000000000000380005000000000000040000000000000606000000000000370000000000000a00050000000000000400000000000400060000000000003600090000000000000500000000000500040000000000000700000000000035000800000000003400000000000005000400000000000006003300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000060000000000003200310000000000000500000000000500040000000000000600300000000000000a00000000000900050000000000000400000000000006002f00000000002e0000000000000800050000000000000400070000000000060000000000002d002c000000000000050000000000000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000002b002a000000000000290002000000000002000000000000010028000000000000030000000000002726000000000000020000000000002500030000000000002400000000002300220000000000002100010000000000002000000000001f001e0000000000001d0000000000000200010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_8 : ∀ i ∈ List.range' 8 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_16 : ∀ i ∈ List.range' 16 7, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 23 at hi
  by_cases h0 : i < 8
  · exact test60_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h8 : i < 16
  · exact test60_8 i (by simp only [List.mem_range'_1]; omega)
  exact test60_16 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨200,7,0x15cfb8a6fde3737719bbba56fbd23fdcb5b7658fbbd56efea3f7d75b46b8fa3d5ce9aee74f537a6b9bd3d5ccbaee65f5372eb9b97adceed66f74d734269ba158f7aac03d743d73a00b92986e944b7686143412a141868dcc256255a222ad1886688833462552a22a958864a883257449a3a06d15924aac1a56801a2500956dcf9b66fcf9736fc9bb79c1f9920edf367ceab3e7ccaf3aa579f36756ab3abccad5aa56aed07ce783ab9dced92e76e737b649bdb9dccf92e67e7373e49b9f6d9edb6576f9673fc959fb56ed9eb76ed1fb678fdbb56cf9eb67ed1f3e78f9f6d6e1f2b61e143861a18778f6dbc036c03d3e0009f48961e04a1f573e3a9bf15dcdaae6ed5d5be3dadb5459f2a25796f6753795a9a56ecd23f64b5b3a58f9da4de6966e46655e242af1986789033c66556a42ab59865a9032d4e3de3600f1b0f5a9c02d6631ca418a9e1872b4c397825cad12e5e1854b4c2a782552d12a909272841b9604953006a9c8072a802a5455b2a0cd9c954ee4327783db3c00d968f4eb402778559ad0ccd69548f0324483d82400c198f42cc0217173de9b9efc4df7a66fbf173669b9b3c4dd9a66ece567df295ef1d9d98e56ce55bae3ad9b650dfb20eff74307b8383e56f0b6b694307c3083a56dceab66f5797333c9b999d0ea9286661739309bc90dcc6866e3556792a95c9cd9c6e65636d43927a18db56de9eb6f6d1f7a78fbdb56c09eb606d1f0278f81⟩
private def rows120 : List Rule := [
  .pool ⟨41,27,[41,3,17,19,23],[2,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨41,3,[41,3],[2],61,0x141002040810020a⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨61,20,[61,2,5,17,19],[3,7,11,13],1056,0xd949b0c345a0d92d90114c02d34904594120012192d02104532d324b01921b6132890da08301a48969845108068309101905245125869065000369260b45960b2526c949a0d345a0c92d80014c12c34914494130112182c02114432d224b01820b6122990db09301a49969944108169309000905344125968065101369360b45861b2536⟩,
  .pool ⟨41,8,[41,2],[3,5,7],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,8,[41,2],[3,5,7],32,0x2070317⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],123,0x10000124014004012182110536⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],41,0x1b382b50736⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,2,[41,2],[],732,0x510110110110110110114110110110110110110110110110110110114110014110110110114110110110110110130110110112110110510110110112502110512110110110110110130110130130110110510110110130110110116⟩,
  .pool ⟨41,2,[41,2],[],96,0x20500110002030100010116⟩,
  .pool ⟨41,2,[41,2],[],1364,0x120104400110101000103101103100012010000110050100211100150130001001040011100010201111001011000300000403112100020111101105102010010000111010104011112110324201007600031101010020111011411000100500005010101000150101141100000014000151010100011112110112043001000011125010003111010011000100300001114101040113101504100410012000551410100035110110116⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],96,0x800080020002⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨41,2,[41,2],[],244,0x7511513111111511111151131111133131111111711111151131111151356⟩,
  .pool ⟨41,4,[41,2],[3],32,0x2070317⟩,
  .pool ⟨41,4,[41,2],[3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨41,26,[41,2,13,17,19,23],[3,5,7,11],620,0x13350d199053114b711213b5a33192451d2b131cb11d6f39d6959501799e9039a97b9477398d3958d53123511c552dc1591ed399c3191031bd4973d471b8a75b565115e77b10b7b5af51d8f335e⟩,
  .pool ⟨61,2,[61,2],[],451,0x100040000010010000400000000000000000010200104020000000004012000002100010116⟩,
  .pool ⟨41,12,[41,2,3],[5,7,11],32,0xb4f1b5f⟩,
  .pool ⟨41,12,[41,2,3],[5,7,11],488,0x5511410111010501010141030111030901010901510101050101010141054f4905030109014101011d010101090b03110101070101014103110905135e⟩,
  .pool ⟨41,18,[41,2,3,17],[5,7,11,13],620,0x13350d199053114b711213b5a33192451d2b131cb11d6f39d6959501799e9039a97b9477398d3958d53123511c552dc1591ed399c3191031bd4973d471b8a75b565115e77b10b7b5af51d8f335e⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],1464,0x8a20a08228028220008a08828000028808000a28228208a00800808220a28820220828a08a20000820800a08008808a08028820828820008000820220800020208828828008200200028a08800a28a00808008a00200a00208020000008020800a00800a20020200a28a00220a28000800820028228220808000208808200020008228208228020a20220020a00208200008a20a28208808228a08820200200a20828828a00020228000028220a20008828028820a08a2⟩,
  .pool ⟨41,22,[41,2,11,17,19],[3,5,7,13],16,0x1b5f⟩,
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,8,[41,2],[3,5,7],31,0x121d47b6⟩,
  .pool ⟨31,22,[31,2,11,17,19],[3,5,7,13],41,0x1fffffffffe⟩,
  .pool ⟨41,2,[41,2],[],16,0x317⟩,
  .pool ⟨41,28,[41,2,7,17,19,23],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,4,[41,2],[3],16,0x317⟩,
  .pool ⟨41,12,[41,2,3],[5,7,11],80,0x10901430a111905135e⟩,
  .pool ⟨41,18,[41,2,3,17],[5,7,11,13],16,0x1b5f⟩,
  .pool ⟨61,19,[61,17,19],[2,3,5,7,11,13],492,0x8200a28808008a28a08220800820028028820a20808200000220220000a08020a00008808800000820208a08228028008200208820a28a20020228a0082⟩,
  .pool ⟨61,29,[61,17,19,23,29],[2,3,5,7,11,13],492,0x8200a28808008a28a08220800820028028820a20808200000220220000a08020a00008808800000820208a08228028008200208820a28a20020228a0082⟩,
  .pool ⟨41,9,[41,3],[2,5,7],427,0x5040001000400820000040010000001400020008000200800000000000001004000100040002800000080020000041002000800020a⟩,
  .pool ⟨41,32,[41,2,17,19,23,29],[3,5,7,11,13,31],1056,0x84910432100180d248128a20369a0592490c00126404484820d16cb64229b4186194900522100090c349028b21368b0482580d10136504594930c06cb65328b4096094910432000190d248128a20269a0592590c10126404584830d16cb65229a4186194800532100090d349128b21369b0492580d10036504594930d06ca65328b4196⟩,
  .pool ⟨61,3,[61,3],[2],164,0x8820a0220282088002aa88a282a02a0a288aaa⟩,
  .pool ⟨61,34,[61,2,17,19,23,29],[3,5,7,11,13,31],984,0xd305b2994d14db69b0d32190596516d16d925b25849341101361361101b4d121b4514994994514196030db0d329129109305349925b69b2112136db05929341b6d909109b2db49325941921129129961b6180d305145325325145b09165b0110d90d901105924349b4936d16d14d341309961b2db65165329b4196⟩,
  .prime 41,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨31,2,[31,2],[],41,0x1b382b50736⟩,
  .pool ⟨31,2,[31,2],[],32,0xd1010117⟩,
  .pool ⟨41,21,[41,3,7,17,19],[2,5,11,13],1240,0xa280a82800a2a0aa0082a200020002a0a88a228800a88a0802202020080a2088080a0082882808882080822088a08820288a02282228808008a802008008022a82a0a0020a8002000a200802800002802008a0008002a0800a0a82a880200200802a20020228882880a22808220a2208820208222028228200a0202208a0200808088020a22a002288a22a0a800080008a8200aa0a8a00282a028a⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],1056,0xd949b0c345a0d92d90114c02d34904594120012192d02104532d324b01921b6132890da08301a48969845108068309101905245125869065000369260b45960b2526c949a0d345a0c92d80014c12c34914494130112182c02114432d224b01820b6122990db09301a49969944108169309000905344125968065101369360b45861b2536⟩,
  .pool ⟨31,4,[31,2],[3],32,0xd1010117⟩,
  .pool ⟨31,4,[31,2],[3],656,0xd1010003000400050001001000004013000110010000010001000000100001050002000101008001000100020101000080014100001000000100010000010011000190040000100100014000400180010116⟩,
  .pool ⟨61,6,[61,2,3],[5],328,0x1119935b5335397599153fb99f793f13f1f399bba555dd71f17717d31dd513bfddb3d7b57b5b7ddffe⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],820,0xf79dc9735253bd2f3114913dc5511ed535a9319a43918759d091918931d4f139871bd651bd0151de1095433b5ab531635998f3b9e33358d195ab5b9855210f715017b14d7b1c3391e57192313121735c31384b3192b5956f1154779125119e97b94959d2773de⟩,
  .pool ⟨61,14,[61,2,7],[3,5,11,13],328,0x1119935b5335397599153fb99f793f13f1f399bba555dd71f17717d31dd513bfddb3d7b57b5b7ddffe⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,4,[41,2],[3],31,0x121d47b6⟩,
  .pool ⟨31,4,[31,2],[3],41,0x1b382b50736⟩,
  .pool ⟨31,4,[31,2],[3],123,0x10000124014004012182110536⟩,
  .pool ⟨31,2,[31,2],[],123,0x10000124014004012182110536⟩,
  .pool ⟨41,3,[41,3],[2],560,0x80000020008000000000000000800000000020008000200000000000000000000000000000208000000020200080002000000000208000000000a000800000a000800020a⟩,
  .pool ⟨41,8,[41,2],[3,5,7],160,0x102000001000600010000020100010116⟩,
  .pool ⟨41,28,[41,2,7,17,19,23],[3,5,11,13],528,0x94910432100190d248128a20369a0592590c10126404584830d16cb65229b4186194900532100090d349128b21369b0492580d10136504594930d06cb65328b4196⟩,
  .pool ⟨31,3,[31,3],[2],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],160,0x1111010110a19901230a4501415100b18d05335e⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],1312,0xf599416313111545011581191b11991311114119418501411145910151416105211113011b53094110017113014151098131311151219d0511411331150101710541030505050191035511054141315101000101151905054111558113014141418105411d01015119910511417309151119190321150501911d0011052195b101911109410d0515011345110501430531051111913311b131035101455111918d05335e⟩,
  .pool ⟨31,3,[31,3],[2],1312,0xa088002202000000000080080a00880200000008008000000000800000002000200002000a020800000020020000000880202000002088000000022000000020000002000000008002000000000020000000000000080000000000800200000000800000080000000880000000220800000808022000000080080000002080a00080000800080000000200000000020020000000802200a020020000000000808800220a⟩,
  .pool ⟨61,29,[61,17,19,23,29],[2,3,5,7,11,13],1364,0x8a20820220220800a0a002280a80a022208888280880a0008aa008022aa00820a0a0a80028a0028a000a8282820802aa200802a8800280880a088882220280a80a20028280082202202082288000000002aa2aaaa08822822a2282288a0282a820a802822202888820a88880aa8002a88a200220a2808280a2a0828a082a280a080a2822002288aa000aa80888a820888a02220a00a820aa0a0288a20a22a20a20882aaaa2aa⟩,
  .pool ⟨31,9,[31,3],[2,5,7],1312,0xa088002202000000000080080a00880200000008008000000000800000002000200002000a020800000020020000000880202000002088000000022000000020000002000000008002000000000020000000000000080000000000800200000000800000080000000880000000220800000808022000000080080000002080a00080000800080000000200000000020020000000802200a020020000000000808800220a⟩,
  .pool ⟨41,34,[41,2,17,19,23,29],[3,5,7,11,13,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,9,[31,3],[2,5,7],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨31,9,[31,3],[2,5,7],41,0x1fffffffffe⟩,
  .pool ⟨31,3,[31,3],[2],41,0x1fffffffffe⟩,
  .pool ⟨61,3,[61,3],[2],1435,0x5044c01003019034002042804000240810148042024241800000ca0610005012a18c800050000005000002010000080204420140430084024030006208122110002010000ca032c000800000921099083200053840700004208010420000e021ca0004c1099084900000100034c0530000804000884481046000c02402100c2028042204010000080400000a000000a00013185480a000860530000018242404201280810240002014204002c0980c00803220a⟩,
  .pool ⟨41,2,[41,2],[],31,0x121d47b6⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,9,0x134304d0b8509a12268409a0e26134184d058209e062713c084f01803fdfcfd7e3edf4f9188c46231188c462310f07c261f0f8783e131886c621b0d8c436310c85c32170b8642e19191007c40200c8803e088c822321904464111d8e8743b1d0ec763a20100804020100804022070881c0e11038447c061ee180c3d830f51d0ec763a1d8e8743b0d06434190c868321a0080002000000400010086002180c00430011d0ec863a1d8e874432010080402010080401c9087242210e484391c8e472391c8e472390a8502a130a0542615201008040201008040123d048f379091e2241108444211088842221d09c763a138e8743b201048041209008240103c040ef77081da200c06030180c06030181f8e8743b1d0fc763a1f0f8423d1f0f87a211cbb0723c758e47839753a5d0e773395c8e371061c2180c38030df1d0edbc3a1d8e874dd130e44c391c8987226128984a26130944c2513b704edb6d09db22701821b0080400c10d70402010080402010086b355a8d369345a0cf018099c020100c04cd6632d94c96431d8cc50431010c3610218208602fd7cbd5e2ed74b9010980426130084c02130204c08040981026012e004235b80846025b00c062301ad446030d8e036381c06c701b0d8e036381c06c701b0b8dc2e041b85c08170405c10170b8202e081b85c08170b8dc2e040100804020100804020000400010080002005a0d966361b2c86cb10b0082c020105804160407c101f0f8203e080e80c3ab0018755e1d08874221d0e8443a11570655a190cab032ab15aa8082b548ac5604188c46231188c4623100aa002a7530054a011a8a45235148d46a29000ac560115800022b000c40031188006200188c46231188c46231160d0662c1a0b058335204d461409a8828a115854282b0a8ac5614158c9402b190ac569f148a05029140a45228188286209050c41231050701c1c0e028380e180c46031188c062304f275389b4d265309715a592a2b4a0ac5693158c1242b180ac56914823d1c8d4622d148917a205e87430bd0a2f148a10829140a45283170985626130b84c2b132084c8140098fe26130b44c2c1689858263f098fa26131f04c7b3d0ac5679159e0ee2b150885422110a8442a148a05029140a45228139d84e753a09ce627391c4e06f371b4d86b35060d2180c1a03067128984a26130944c253309046241219448231088842221108444210c06030180c060301810190406331080c2200080002000000400010c00430010086002180987c3c1f0f84c3e1e08874221d0e8443a110d870361c0e06c381b0c868321a0d06434190b8602e180c05c30170b0082c020105804160a8202a080405410150905024130a0482612300441e110897c220f0800c1e5e01840ba0f051701c5b2d028b20e06034160c06830180b2c02806090515c12032b020aa08041501053021480a51280109e050301c0c07038180e062701406040293408030100804020100804020000400010080002002612c94492411c8c45⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 121, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 121 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨96,8,0xa65b9b2e5b9ba6d3232ed323a6ebcb2eebcba673532e7353e2af8f6aaf8fe237176a37178c25d58c9d5d98d9c99861518019c90819c98091510891515079c9500151de67df6667dfdedf6766df67a2dfdf2adfdfa267672a6767dea3a366a3a3de2b2b662b2ba22ba32a2ba3a2a32b2aa32bea6797726797eadf1f72df1fd25bd35a5bd3d2d35b5ad35b96d3d31ed3d3965b5b1e5b5bd297975a9797d21f1f5a1f1f961f971e1f9796971f1e971f8819e91019e9889171109171c4cdad4ccdadc455354c5535d079e95879e9d001715801718831a11031a188a92910a929e825dde89d65e861a1e8d929b8c1a1b84929a001a1a07929e8cdc570cdc5e8554d70554de81989701989e891117091118879b9880141c43d7d4c3d7dc4b5054cb505⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨31,22,[31,2,11,19],[3,5,7,13,17],240,0xd12124030410000500100180080912912020030010014000104180490916⟩,
  .pool ⟨31,29,[31,19,23,29],[2,3,5,7,11,13,17],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨31,25,[31,5,19,23],[2,3,7,11,13,17],964,0x200a8820880200a0a8a22aa808a80a2082822a8a080802aa0800280202222220200a00082aa0080828aa20a082280a880aaa228a828020088208a80222a808a288aa2a8280822000a880a8228a0a200828a8aa0028aaa0aa2a220222a2a82aa8a002a8a8a08022828a20a808a80022080a0aa2a88a2880aa2⟩,
  .pool ⟨41,29,[41,19,23,29],[2,3,5,7,11,13,17],248,0x808a2a88a880aa28200a880080208a82a208020022a00828aa022a22a8a202⟩,
  .pool ⟨31,2,[31,2],[],64,0x5101000180010117⟩,
  .pool ⟨61,18,[61,2,3],[5,7,11,13,17],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨61,6,[61,2,3],[5],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨41,37,[41,19,23,29,37],[2,3,5,7,11,13,17,31],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨61,20,[61,2,5,19],[3,7,11,13,17],544,0x253b0d6501d31f9189a9532dabf7c903e2616f493105875bc5cdfd1779eba38d57a6352b1d7511c30f8189b9433dbbe7d913f2717f592115974bd5cded0769fbb39d47b6⟩,
  .pool ⟨31,19,[31,19],[2,3,5,7,11,13,17],451,0x20008000000000000820001000010080000e8000008000000800048010002000040008820044025212040c00000008800000083080022⟩,
  .pool ⟨31,23,[31,19,23],[2,3,5,7,11,13,17],964,0x200a8820880200a0a8a22aa808a80a2082822a8a080802aa0800280202222220200a00082aa0080828aa20a082280a880aaa228a828020088208a80222a808a288aa2a8280822000a880a8228a0a200828a8aa0028aaa0aa2a220222a2a82aa8a002a8a8a08022828a20a808a80022080a0aa2a88a2880aa2⟩,
  .pool ⟨31,19,[31,19],[2,3,5,7,11,13,17],656,0x80a020022200080028a08a00220880820000200000a020800000a0022020000000020200022a802008200802a8800080800000000808800a000002080a00000800008202208800a20a280020008880080a02⟩,
  .pool ⟨31,23,[31,19,23],[2,3,5,7,11,13,17],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨41,21,[41,3,7,19],[2,5,11,13,17],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],320,0x101010100a18801230a4401414100a18c05224e1011000110a19901220a4501405100b18d05335e⟩,
  .pool ⟨31,22,[31,2,11,19],[3,5,7,13,17],656,0xd5b1755337155d557db59b117359d1931551751141f531d11555f1537175511511131315177b917518315d13bdd15191911151155d1d951f555117195f05115d15519317359d11b35b7d557551d9955d1b56⟩,
  .pool ⟨31,22,[31,2,11,19],[3,5,7,13,17],1312,0xd1316503351111050db58b111159919315514511414501811505b14171014105011111011533010118015d1325815181811111115d019105150115191b01011901010105018d0111011d15654181151103400581115103054d5171011101630141010101310101b1315101514113017511111103031503499175003101019951011111014105011d051b415103014505114515519313351111a35b6141111159814d1916⟩,
  .pool ⟨61,19,[61,19],[2,3,5,7,11,13,17],964,0x200a8820880200a0a8a22aa808a80a2082822a8a080802aa0800280202222220200a00082aa0080828aa20a082280a880aaa228a828020088208a80222a808a288aa2a8280822000a880a8228a0a200828a8aa0028aaa0aa2a220222a2a82aa8a002a8a8a08022828a20a808a80022080a0aa2a88a2880aa2⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,7,0x60c000000018300002040810000000000000000000000000000000000002040810000081000000002040000000000000000000000000000060c00000001830003971e1bc0000000000000000000004081020000ddb4000000366b00000000000000000000000000000000000000000000000000000000d5a40000003467000040810200000000000000000000000000000000000000000000000000000000000000008102040000000000000000000000000000000000008102040000000000000000000003312ca480002244000000089100000000000000c8480000003192000000000000000000000000000000000000000000204000000008100003161c17c00022440000000891000081020400000000000000000000000000000000000010204080000000000000000000000000000000000010204080001f7800000007dd000000000000001c38000000070e00000000000000000000000000001c38000000070e000000000000001a34000000068d0002e5bb564000b15c0000002b5500000000000000000000000000000000000000000000000000000000a94c0000002951000284f9d340001428000000050a00000000000000000060c18300001428000000050a000000000000000000000000000000000000000000000000000000001428000000050a000060c183000000000000000000162c000000058b000264b95240000000000000000000024478d14000890c00000021410000000000000000000000000000000000000000000000000000000080fc0000001f3d0001e3b74e4000000050a1428000000000000000000000489122400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000102000000004080001c376cd400068cc00000019310000408102000000000000000000000000000000000000000000000060bc000000172d102000000004080000000000000000000000000000000162b54a4000000000000000000000000000000000014034e0c0000e1c000000038700013034a0c0000e1c000000038700000000000000000000000000000000000000000000003060c18000481800000011860000000000000000000000000000000110542140000000000000000006100000000184000020408100000000000000000000000000000000000020408100000810000000020400000000000000407c0000000f1d00000000000000000000000000000000e1b346400000000000000000300c0000000b830000b15284c0000000000000000000000000000000000000000000000000081020400002040000000081000008102040000204000000008100000000000000000000000000000000102040800000000000000000000000000000000000102040800000000000000000020400000000810000000000000000000810204000020400000000810000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_137 : ∀ i ∈ List.range' 137 63, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 200 at hi
  by_cases h0 : i < 137
  · exact test240_0 i (by simp only [List.mem_range'_1]; omega)
  exact test240_137 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨32,10,0x28abfafd9237cdf82abfafc2a37cdf64a4791ca255d570aa4791e0a55d573799364dce28d9337a8328ebe28ca39199364c6628d9391a8328d5628ca3afa0b82cde46e0b73a0b0acde0ac2b55a0b82e4646e0b19a0b0ae460ac2ba0a0b64d920ad9328a0b28d9246ca364a8382ca228e0b649930ae8228c2b⟩
private def rows720 : List Rule := [
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .prime 181,
  .pool ⟨31,20,[31,2,5],[3,7,11,13,17,19],41,0x1b382b50736⟩,
  .pool ⟨31,20,[31,2,5],[3,7,11,13,17,19],37,0x1ffffffffe⟩,
  .pool ⟨31,2,[31,2],[],76,0xd115153311199515116⟩,
  .pool ⟨31,24,[31,2,3,23],[5,7,11,13,17,19],1295,0x4402421401c201803210047b40c1102d1004b09021411246a8a2014e50302450da252101124cf5192400d422046070d207898d48d08105230b826000a150c207300e78909724c431102531c70a1aa33028218604110b6250d09106528006b10b30c452bd48380a330c4e304c44200720d0b11ca950d6c10500489463314b009452b1e1014a92a80c315873a4c21a5641b16461009734a13a56a41d85389cd1b5e⟩,
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],456,0x220800820000a08220028208000000020828008820a00008200208808808028208a28020808a00800a28a28a00200a20208028a2082802022⟩,
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],296,0x200a800202228a2020808a288808002a0080a8aa02aa82888208a8a2a20822282aa80aa2a⟩,
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],328,0x88000a8200200088000880200080a20a200000200008000008a08a0200080220002200080082a00022⟩,
  .pool ⟨31,20,[31,2,5],[3,7,11,13,17,19],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,24,[31,2,3,23],[5,7,11,13,17,19],544,0x843300d2dab02f9a4d16645828ff56bce1953211c3dba13e8a5c07755939ee57ade0943310d2cab03f9a5d16745838ff46bce1952211d3dbb13e9a5c17754939fe57bde⟩,
  .pool ⟨37,13,[37,13],[2,3,5,7,11],80,0x2000002202⟩,
  .pool ⟨41,30,[41,2,3,5,23,29],[7,11,13,17,19],592,0x1315b911757339b317191db79dd1d517b11d0bdbb17bfd3dd971db9b7b319337d7bb91fb3a5751fd5531377df7531d59f3d9959153f5594f9ff53fb9799d359fdb3f75d77393ffd5bf7e⟩,
  .pool ⟨37,32,[37,2,23,29],[3,5,7,11,13,17,19,31],1216,0x8631407a1b9001dc60b6dc9aa81a17bf2378a4d365152e1ec4548834e299defd5a52fb762ce18730517b1a9110dd60b7cd9ba91b06be2279a5d264143f1fc5559934e398cffc5b53ea772de09631507a0b9011dc70b6cc9ab81a07bf3378a4d375153e1ed4549834f299cefd4a52eb763ce19730417b0a9100dd70b7dd9bb91b16be3279a5d274142f1fd5558934f398dffc4b53fa773de⟩,
  .pool ⟨41,30,[41,2,3,5,23,29],[7,11,13,17,19],181,0x1ffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨37,32,[37,2,23,29],[3,5,7,11,13,17,19,31],960,0x205201104800909029860a0826902430024414094094c02c825b4c328061205200104901809128861b0826912530024504084194d12d825a4c328160305201104800809029861a0836902430124404094094d02c825b4c329061305200104901909128860b0836912530124514084194c12d825a4c32916⟩,
  .pool ⟨37,32,[37,2,23,29],[3,5,7,11,13,17,19,31],1056,0x84910432100180d248128a20369a0592490c00126404484820d16cb64229b4186194900522100090c349028b21368b0482580d10136504594930c06cb65328b4096094910432000190d248128a20269a0592590c10126404584830d16cb65229a4186194800532100090d349128b21369b0492580d10036504594930d06ca65328b4196⟩,
  .pool ⟨181,11,[181,11],[2,3,5,7],133,0x161f2054da76220c210c111b96ca813e1a⟩,
  .pool ⟨73,20,[73,2,5],[3,7,11,13,17,19],16,0x2737⟩,
  .pool ⟨73,43,[73,23,29,43],[2,3,5,7,11,13,17,19,31,37,41],1360,0x802002080020808a008080a880028880202000080280000080000000008a00080008008008020002000080000202282800000080200000000000288800802200020080a0000800200800082008002000000000228002880000000008002008200020080020000a02008000880200222800000000000802000000282880800002000080008020020020002000a200000000020000028020000808022280022a020200a202080020800802⟩,
  .pool ⟨181,30,[181,2,3,5,23,29],[7,11,13,17,19],1232,0xfdd3d3ad51ad74711bb1ce511538b53983c5dd9952d49913091b3f60dd11b763581f5811d3514151931471b071c99b153249b9f525d53612d1733303c73d1e3d1150a35fb158192b512f93933ab99393e915a930351bf58a151178f179c781999d1690d957495f3b249951b3271c1b1c5193150515971035f0358ddb11760df9b1219132569533774783395a395114e71bb11c5d6b156b97977e⟩,
  .pool ⟨181,4,[181,2],[3],16,0x2737⟩,
  .pool ⟨73,10,[73,2,5],[3,7],48,0x10122110536⟩,
  .pool ⟨31,23,[31,23],[2,3,5,7,11,13,17,19],37,0x10ac804d42⟩,
  .pool ⟨31,23,[31,23],[2,3,5,7,11,13,17,19],48,0x20080800002⟩,
  .pool ⟨41,37,[41,23,29,37],[2,3,5,7,11,13,17,19,31],1205,0x12d130e3139c1295e210d027a0c823504299a27956f389004b9c75a98f4242b62dcc6094d79d4423124505c138d2f3b86c51d02311250894e0006a0a5285804b590035390f38d2703445311223288b0392c73c272b0026b480685294158001ca4429223102e28d8773d2c720e828923108ae7aca418ced1b5090bc656b8e74802473daa791665082b104c17902c211ea520e7231c322d2⟩,
  .pool ⟨73,10,[73,2,5],[3,7],41,0x1b382b50736⟩,
  .pool ⟨181,18,[181,2,3],[5,7,11,13,17],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨181,18,[181,2,3],[5,7,11,13,17],112,0x1131950bd9b33a5571d14f9db77e⟩,
  .prime 37,
  .pool ⟨31,12,[31,2,3],[5,7,11],247,0x7ac8a0918840830680847404810a013c805081202e210160c102118905135e⟩,
  .pool ⟨31,22,[31,2,11],[3,5,7,13,17,19],76,0xd33515331b199515996⟩,
  .pool ⟨31,3,[31,3],[2],76,0xa88280a20008a02822a⟩,
  .pool ⟨31,24,[31,2,3,23],[5,7,11,13,17,19],352,0x20ca85966e031cb94967e030da95867e130cb95977e020da85966e131ca94977e030da95867e131cb95977e⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,7,0xa142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a1428542850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a13e7ce9f3a7ce9f3e7ce9f3a7cf9f3e74e9f3e7cf9d3e74f9f3e74f9d3e74f9f3e74f9d3e7cf9f3a74f9f3e7ce9f3a7d0203a80ea03a810203a80ea0408101d3a81020407501d4080ea03a810204074ea0408101d4075020407501d40750203e7ce9f3a7ce9f3e7ce9f3a7cf9f3e74e9f3e7cf9d3e74f9d3e7cf9f3a7ce9f3e7ce9f3a7ce9f3e7ce9f3a7cf9f3e74f9f3a7ce9f3a7cf9f3a7ce9f3e7cf9d3a7cf9f3e74f9d3e74f9f3e7ce9f3a7cf9f3a7ce9f3a7cf9f3a7ce9f3e7cf9d3c74f1d3c78f1e3a74f1e3c78e9e3a78f1e3a78e9e3a78f1d3c78f1e3a78e9e3c78e9e3a78e9e3c78e9e3a78f1e3c74699166458d1634c99163458d3234c8b1634c8d322cc8b1a2c7991e64599163c799166458f163cc99163c58f323cc8b1a64599163458d326458d1634c8d322c58d3234c8b322c68b1e64799166458f1e64599163c58f326458f163cc8f322c58f823c98b242c78f242ce0b1e2c793262c78b1e487c016fc5901640990242c5902440e0b262c810262c90b202c83e1ef4593163c58f244858f163de0f262c58f263c90b382c78b20ec813164859020485ba1640590264c5901640910382c79b166c58f163cd1a163c58f723dc0b163db8f342db0b1e2c69b1a6c59a163469a16d458d1635a33163458d343590b622c78b1ec079a162c79a1e6c59b163c7af166858f163d70d5a2d60b1a2c69a342c68b1a6c69b162c6ab1a685aa163481a166c5901640da91640590344140b16413904c2cd0b202c7991e64599163c799166458f163cc99163c58f323cc8b209459a1640590486c5901640d90342c590344118b442c80b1e64799166458f1e64599163c58f326458f163cc8f322cc182e60b982e60c182e60b983060c172e60c18305cc17305cc183060b982e60c182e60b982e60c182e60b983060c173060b982e60b983060b982e60c18305cb983060c17305cc173060c182e60b983060b982e60b983060b982e60c18305c80c1630590164060e16405901c4070b1640610182c60b202c78c1e3058c163c78e163858f163c70c163c58f183c60b203058c164059018305901640610182c5901c4070b1c2c80b1e3078c163058f1e3058c163c58f183858f163c70f1c2c58d2a34a8b2c2c68d2c2ca0b1a2c694222c68b1a58691165458f163ca8f2c2c58f2c3ca0b282c78f222cb0b1e2c7911a44591163458d2c5858d1634a8d2a2c58d2834b0b282c68b1e44791165858f1e58595163c58f2a5058f163cb0f282c794164c58f163c912163c58f223c98b163c98f242ca8b1e2c814204c59216408121644590164099316405902440a8b2a2c78b1e4c792162c7921e50593163c793164858f163c8902a2c98b202c812242c80b2050813162c8132048591164078e163858f163c70c163c58f183c60b163c60f182c60b1e2c68e1a3858e163468c163058d163460c163458d183460b1e3058c163c58f183858f163c70f1c2c58f183c60b182c78b1a3068c163058d1a3858e163458d1c3058d163460d182c2850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a1450a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142810206081820608102060818204081030608102040c103040c102040818206081020608182060810206081820408103040c1030408102060c1020408182060810206081820608102040c103040c102040c1030408102060c1020408182060848906241890624489062418912244830624489120c483120c4891224189062448906241890624489062418912244831224189062418912241890624489120c1891224483120c483122448906241891224189062418912241890624489120c4080e203880e204080e2038810204070e20408101c4071020407101c4071020407101c408102038710204080e203880c183860e183860c183860e183060c1c3860c183070c1c3060c1c3070c1c3060c1c3070c183060e1c3060c183860e182850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850a142850810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081010206081820608102060818204081030608102040c103040c102040818206081020608182060810206081820408103040c1030408102060c1020408182060810206081820608102040c103040c102040c1030408102060c10204081820608103040c102040818304081020608182040818206081820408103040c1030408103040c102040818304081020608182040c1030408102060c1020408182060810206081820608102040c103040c102040c1030408102060c102040818206080000000000000000102040810204081000000000000000000000000000000000000000000000000102040810204081020408102040810200000000000000000000000000000000102040810204081000000000000000000000000000000000000000000000000102040810204081000000000000000000000000000000000810204081020408000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_40 : ∀ i ∈ List.range' 40 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_80 : ∀ i ∈ List.range' 80 16, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 96 at hi
  by_cases h0 : i < 40
  · exact test720_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : i < 80
  · exact test720_40 i (by simp only [List.mem_range'_1]; omega)
  exact test720_80 i (by simp only [List.mem_range'_1]; omega)
private def keys5040 : Keys := ⟨0,13,0x0⟩
private def rows5040 : List Rule := [
  .prime 43,
  .pool ⟨29,17,[29,17],[2,3,5,7,11,13],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨41,37,[41,23,37],[2,3,5,7,11,13,17,19,29,31],61,0x1434026619900b0a⟩,
  .pool ⟨29,26,[29,2,13,23],[3,5,7,11,17,19],176,0x3f5591315b891db3b9f7527b11d1751fcd59f7bdb316⟩,
  .pool ⟨29,5,[29,5],[2,3],71,0x1164729716b1d977e⟩,
  .pool ⟨29,3,[29,3],[2],152,0x8220002a0a80008820a2888aa80a02aa2228a⟩,
  .pool ⟨29,18,[29,2,3],[5,7,11,13,17],176,0xf79d59f91341d57b31379ab3d919bd5705913f3573de⟩,
  .pool ⟨29,3,[29,3],[2],71,0x1164729716b1d977e⟩,
  .pool ⟨29,7,[29,7],[2,3,5],281,0x1b78ba137e65193ceba0f1880b096ad7a23b7117ad5a4340463c175cf26299fb21747b6⟩,
  .pool ⟨29,7,[29,7],[2,3,5],284,0x8aa0028a2a0aa2a220888080280820aa8020802aa082028020222088a8aa0a8a2800aa2⟩,
  .pool ⟨29,18,[29,2,3],[5,7,11,13,17],71,0x1164729716b1d977e⟩,
  .pool ⟨29,7,[29,7],[2,3,5],49,0x81020408183⟩,
  .pool ⟨29,5,[29,5],[2,3],129,0x1b29221960201a08b44160101a6112536⟩,
  .pool ⟨29,5,[29,5],[2,3],219,0x21a40309b2d02820412400ca2122932886d905969a2d020261b4832⟩,
  .pool ⟨29,7,[29,7],[2,3,5],344,0x8aa080882a8882aa2a08a808a020028800288a8a008200a2a228002280080a202a20a8aa8222a822020aa2⟩,
  .pool ⟨29,5,[29,5],[2,3],211,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨29,7,[29,7],[2,3,5],421,0x10e90405130b7467a784a11602281c055d0480618a12840180cd806cc0600852146180482ea80e05101a214879798bb432280825c2⟩,
  .pool ⟨29,7,[29,7],[2,3,5],339,0x20b21020a4da25a2124d100321800220b4830d00882ca6d061a40b2996c321b65049328128048b2d320b2⟩,
  .pool ⟨29,5,[29,5],[2,3],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨29,5,[29,5],[2,3],181,0x200902024000000040000080104002a000022⟩,
  .pool ⟨29,17,[29,17],[2,3,5,7,11,13],152,0x220002202000000202200022002022222202⟩,
  .pool ⟨41,34,[41,2,17,19,23],[3,5,7,11,13,29,31],633,0x1a2134592d949a48229b48920a61821024260b6c865208205360a01b00345844209021a0126cb68305b4d920161024108868b00360141b2810412984db41909021061941244b65104964a6d268b2116⟩,
  .pool ⟨41,34,[41,2,17,19,23],[3,5,7,11,13,29,31],852,0xd121b6916db6d92194d34534534994914190db2d109905301b2590d369125109901b6980d14594d92112516190930db29b45b69341b0592db45b29b6192130d14910936534516032db0132114912d961349b01941321169b6130512532594594596530936db6d12db0916⟩,
  .pool ⟨41,34,[41,2,17,19,23],[3,5,7,11,13,29,31],688,0x133d1d51b3511b33f795319139fd9f155db553139d0bd93b3ff1ddfb59d593b9b3f975331bb731bfdbd33a57795915f7155f77b3d171d57db9db5119f11757d94f9d7f7bb599bf1d91d7fdb7bd31775ff375fb9f977e⟩,
  .pool ⟨41,34,[41,2,17,19,23],[3,5,7,11,13,29,31],1204,0xd951b3a1dd95541151d149939910b91b130359191841f39741593112555991c519151235995109d331501811d58d513512191171a791191c193131695b9158b18951811111149d93f3c119b31079f93725111110315231a3513b52d191930713113cb1d113091591563571030151997211533589151314713355491193505d39f043131358191b13a113393251715105553770b9b1536⟩,
  .pool ⟨43,41,[43,23],[2,3,5,7,11,13,17,19,29,31,37,41],7,0x16⟩,
  .pool ⟨29,7,[29,7],[2,3,5],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨29,26,[29,2,13,23],[3,5,7,11,17,19],113,0x1fffffffffffffffffffffffffffe⟩]
private def step5040 : Stage := ⟨cfg,720,7,keys720,keys5040,rows5040,5,0x2cf75a0140418b31e2630516a2acc7202f41d68b51c0601075a2eb4580e41a8a01d689ad16604c6598ef45828031c83a907802d47598a418280ad2063916a2cc7500c14598b351580ad177a2cc700c041d68b551002937720eb4018f45a8131d663ad1602814598eb41d40b31c8a39360a22b4818a401c03bd1660516a2cc65602b459a8b51403a9375a24c0480e41d683b5006290c720ea058eb4580b331663cd015025459ece4182893516a3901500eb4598ab30083bd180bd16a2e8c506eb41de885026039075a2eb4028e419483a8166a2cc720c00598e41d49b0510a3c0c5202b41de8b31c0a03475a2eb4580ad195a3ad00aad1260136720eb44828031483b107502cc75a8ad18280ad1662b14500eb458c14498e451c80ad175a2cc500c041de8b351602b47568f34018a9515bba8083ad1603814720eb41d40b3148639060a2ef45a8ac0141bad346a214068ee7202f459a8b51c03a9075a2cc0580e41d69bad00a2bcc568f004028b515a331c83ad01802d4720ca41828b352063901500eb44a8ab301e3ad077a2c056acc700ef41d68b5008029377a22b4018e4195a3a816aa2cc568c0c0568b516b4028b319663c0106a2d4598c0405e8b31d6a38075a0eb45980401c83ad163ad12a280c098eb45de8b0166339075a00c05a8e41e083051662c0c7202b498ea05a8ab3166305015a2d45618e01de8bad16a0106520ef44028031c83a8263ad16aa2c0598eb31d680515663907500c14428e431480ad237a2cc700d4598c145d68b3158028075a2d54498041d483ad120380c520ed41d40b31c8b01663ad079a00c59a8b31d4090512639067202b45aa8b31403a9077a2cc0a2d45602e01d69a3150a04c77a0eb4580e451c83ad01502cc520ce41828b3107502cc7428e418280ad226290c700ef45d68b501a32b475a2c14028ad1d4041d689351203907520ed4018ab31c83a8060a2d45698ac0568bad16a2806639060a26b45a8e401403ad166a2cc020eed1d68b014062b479a0ea04a8ad580e41d683ad00a390c520ea05828b31c832b017a2d54d18a01d5a3bd10a051663901700eb45a8eb30083ad075a2c07228af1d680c01062b46568c145aab4018e419c83c016aa2cc520c040569031d2a28075a0eb45980f015a3bd163bd1663814020eb45de880148339075a00c05a8ad1d5a3051662ad45602b431c8305177a2d45600a0dd69a3510a0347720eb4580e051c83ad07502cc522c0720eb4dd680515e62b478020145a8ad19c80bd166a2d4700ea41d68b3029031c80a8075a25455980f1d683bd1602b4c720eb40600b51c8329060a2cd5a00c720cad1d40b551662b460602b45a8ab31c03bd075a2d40200a4dde881de8b31c0a03475a2eb4580ad195a3ad00a02cc720ea4d828851e0629015a107502cc75a8ad18280ad1662b14500eb45d6893009b39075a2414018a41d8041de8b351602b47568f34018a9515bba8060a24c7228e40568bad1662806901c83ad076a00c5218e41d40b0516a2cc65602b459a8b51403a9375a24c0a2d47202a01d68b3156601077a0eb4580b331663cd015025459ece4182893568051c832907502cd4598e418180bd16a2e8c506eb41de885026039075a2c75a2d47018041d68bad160390659eeb40280831663c4c60a2d45598e405e841e00b51d6629060a02b4818e451403ad135a2cc098cb31de8b050063907501075a2d54400a4ddc83ad0063ad4598ea01828b3166a2b015a2ef4598e01a8e4d8288ad2062900700ef459a8b50263acc75a2c05028b31d683a816639014598e419580bd16aa68c500ead1de885016039075a0eb4028e431483a8163ad1603914578eb406008315a32b460a2d54598e405c03ad16a3acc020eb4202b4818e951403ad075a2cc0780ad1de8bad0063906720f005aa8b3148301c83ad00602d4568ead1828b3156a2b015a0ef4598e050083ad177a200520cc700ef45d68b501a32b475a2c14028ad1d483a81663a14720c14056913148b31c83a8060a2d45698ac0568bad16a2806020eb449a8901c83a9076a00c5a2cc020eed1d68b014062b479a0ea04a8ad31c8305135a2d47200a01d68b31075a2407018a41da83a81663914598c145d68b3158028075a2d54498041d4e40568b551662807520ef45980b01663ad079a00c59a8b31d409051263906a39075a02a0598a419c8305166a2d45602e01d69a3150a04c77a0eb4580e45a8e01d683ad1660100720eb45d680516632cc78020d45a8b318080bd1663816a3907820c14598b031c80ad075a2545018131d68bbd1602cc6720eb401ab45a80419483bd100a00c720eb31d40b515662cc60a02b45a8ac31c03bd1630510a390c5202b48de8b31c0304c75a2d54580b31d663ad00a2acc720ea003c75a2cd4580b21dc83ad0063ad4720f001828b3148639015a42b44a8a0198b21828bad16a2b00700ef459a8b50083a9077a2005018e41d683a816a2c9602c875a0eb4028b231c83a8160a214720ca405690351663807790eb45a814598ac05403ad16a2a4c020eb41d68901c8629076a02a0598e4196430516acd0062c86590ea04aa8931c8301015a2d47598a01d683bd1660100590eb458eb4d18a050243bd115a2c0720ce41d680501662907520c14598eb51580bd243c01062ad4590c1405e8b31c8a38075a2eb45980419c83ad160a014578ea40569031d2a28075a0eb45980f015a3bd175a00c720ce41e00b551662906039075a00c05a8ad1d5a3051662ad45602b41de8b31c0a01075a2ef4400a4198e01de8bad16a0346568eb458280515a3a907502cc7428e418280ad206291663907500c145a8ad31580ad175a2d4500c041d689351203907520ed4018b4598041dda3ad160280c568f341d409515a639060a26b45a8e401403ad1660516639065602f45aa9a31403ab477a2140580e41d683ad00a390c520ea058eb4580e4515e3ad018020c568cad1828b551663901700eb45a8eb30083ad2b4580e419c83ad00a02cc520ea41828b31d6a2b017a0eb4d18a050263bd100bd1663914700eb45d68b3008339075a2c14028b31d663c01062ad4598c1420eb4018eb51c83c0060a2cc5218e405690ad12a2806098eb459a8b01663b9c03bd166a2d4020ea41de880140639075a0ea05a8b33166305175a2d45600c720ea05828851c8329015a40d4598e01de63ad16a02c0598eb41d6805166930083ad075a2407218a41da80a81663906598c145aa8b31580a8075a2d45a24c720c040568b51d6628075a0ef45980401663ad179a00c598cb31d40952cc720c1405e8b5158628075a6af44281319c83ad160a014720ea41d40b3168b01c83acc75a0145418b31e0030516a2ccc7202f45d68b51c0301075a2cd5a40c7200a01d6895516604c7598ef4580a031c83ad07802d47218a41828b1d68031c8a2cc7502c14598b319580ad16aa2cc700ee41d68b5010029077a0077a2cc75a8131d683ad1602cd4598eb40540b31c8339060a2154818a4054e41d40b3516a2cc60602b4598ab51403ad075a24c0200e41d689b50062906601077a2eb4580b319663cd0060254598ea41828931d6a39015a0eb4598a0ad16603c6590ef45828031c83a907802d47598a418280ad2263914500eb448c14598b251580ad177a2cc700c041d68b551002907720eb4018eb51643a8243ad1602814590eb41d40b31c8a39060a22b4818a401c03bd166a2d4090ea5602b459a8b51403a9075a24c0480e41d683b5006290c720ea05828b5164331643cd0150254590ce4182893516a3901500eb4598ab30083bd075a2c05944c500eb41de885024039075a2eb4028e419483a8166a2cc720c0c05e8b5140831643c4860a2d45598e405e83ad16a380c020eb45d68b01c832bc75a015131c80ad075a25450180f1d68bbd1602b46720eb40180b51c83c1060a2cc5a00c720ead1d40b515662b460a02b45a8ac31c03bd175a2d4020ca41de8805e8b31c0303475a2d54580ad1d5a3ad00a2acc720ea01828851c8629015a407502cc7228ad1828bad1662b00500eb45aa8930083a9075a2407018a41da841de8b301602b475a0f34018ad515a3a8120a24c720ce40568b551662807539060a2cd45a8ac05c03ad2262a14068ef41d68b01c8a39075a02a0598a4180e41d68bad00a2bc6568f0041a8b515a301017a2cc75a8e01d683ad1660100720eb45d68051c832907502cd4598e418180bd16a2c4c500eb41de885026b31c80bd075a2d47018041d68bad1603906598eb40280831663c4c60a2d45a00c720ea41e00b51d6629060a02b4898e451403ad135a2cc098cb31de8b05e8b31c0301075a2d54400a41dc83ad0063ad4598ea01828b3166a2b015a2c7502cc7228e418288ad2062900700ef459a8b50263acc75a2c05028b31d6841d6893012039075a0ed4018a431c83a8160a2d4598cac0568b3516a2807539060a24d45a8e405403ad1662acc020ef41d68b016662cc79a02a04a8b318c14598e451580bd175a44c500c131de88551603907520eb4028eb31483a8083ad1603814598eb41e0083166a2cc60a2ef4598e401c03ad16aa2cc020ea7202b489a8951403acc75a2cc0580b31de83ad0063914720f005828b3148331c83ad01502d4598cb31828b3516a2b01500ef4598eb50083ad077a200522cc700ef41d68b502602cc75a2eb4028b319c83a8166a214720c04056903140b31c83acc60a2d45598ac05683ad16a280c020eb44d68901c8329076a00d7a2cc020cb31d68b050062cc7998ea04a8a931c8305015a2d47218a01d68b2b015a2d54598e01dc83ad16a0200520ef41d68031c8a2cc7502c14598b31a8b31d680a81663906720c1442a9031480a8077a2cc75a8131d683ad1602cd6a28075a0eb44980401c83ad136a00c520ce41d40b3516a2cc60602b4598a04a8b31d483051263ad47202b41d68b3140601077a2eb4580b319663cd006bd10a04c6720eb45828051c83a907502cc5598e418280bd16a2b0c500eb4d0c145a8b331c80bd175a2d4700c041d68b351603907598eb4028a831663c0263bd160280c720eb41e00b51c8629060a2eb4818e401403ad12aa2cc098ea3a816a2ccc598c145d68b5158038077a2cd45a8041d483bd100280c720eb498eb45a80b01663ad075a0145998e41d40b0510a39065202b481a8b31c03b96630516aa2cc5602a01d68b5152601075a0eb4480e431483b501502cc720c0598eb45e680316632cc7502554498e418080ad16a3acc500eb41de8b3008b51580bd075a68c5028131de88ad1603906720eb40280b31483a9060a2cc7a014598eb31e0083156a2cc60a02f4598e451c03ad175a2cc020ce41d68b056895140304c75a2cd4580b31dc83ad0063ad4720f001828b3148639015a407502545698e418289ad16a3900500eb459a8b30083bb475a2c05018ad1e68d1de885016039075a0eb4028e431483a8160a2cc720cac05e8b55346280752b460a2d54598e405c03ad16a3acc020eb41d68b01c8a2bc75a0300418ad180ad1de8bad0063906720f005aa8b3148301015a40c74a8a01d683ad16603d6a2b015a0ef4598e050083ad177a200520ce41d6803016a2b47568c14598b4028ad1d483a81663a14720c14056903148638077a2eb45a80d195a3ad160ad16a2806020eb449a8901c83a9076a00c5598e41d4030516a2b4c5602b45acc500eb41de8b300802c875a2f34018b219643a812aa24c720c040568b51c0b31483a9060a2cc75a8ac05e83ad3462814090ef44568b01c8339075a0155a2cc020ce41d68b0500a2bc7590f00418ab5164305017a2cc7228e01d68b1828b3148639015a42b44a8a0181e3ad166a2c0590ee41d68031d6a3907801077a2005018e41d683a816a2c8c590c145d68b5158038077a2cd45a8041d4a405690351663807790eb45a80b01643ad075a0145918e41d40b0510a3906629076a02a0598e4196430516aa2cc5602a01d68b5152601075a0eb4480e4a2d45602a01de8b31d6a01075a0ef4400a431c83ad01502d4598cb31828b35680516633907502cd4428e418080ad2062acc700ef41d68b502602cc75a2c75a2d45018041d689ad1203906520ed40180b31c83acc60a2d45598ac056931d4095152639060a02b45a8e431403ad177a2cc020cb31d68b050062cc7904c77a2154580e41d483ad00a3acc520ea01828b31c8a2b017a2eb4898a01a8b31828bbd1663900700eb45aa8b30083a9075a2c07028b31d683c01062cd602cc77a0eb4018e451c83c0160a2cc520ce4056913512a2807598eb45980b51663a8060a2cc59a8ac0568bbd1663806020eb45aa8801483b9075a00c7a2d4098eb31d68b0140a2cc75a0ea0598e451c8305115a40c5200e01de8b3028b516632b015a2cd45a8a01d483ad1260240720eb41da80314863907502c75a2c05998b31e680a812a2cc6720c1449a8b51c80a8075a2cc5598041de8c05e8b5162628075a0ef44281301c83ad175a014720ca41d40b35166390602cc75a0140418b31e2630516a2acc7202f41d68b51c0601075a2eb4580e41a8a01d689ad16604c6598ef45828031c83a907802d47598a418280ad2263914568ea04828931c8339015a2d54598a01d483bd16602c0568eb41e680315a8501a3bd075a2c07228e41d680a81662906720c1459a8b51580b8075a44c5a2d4568c0405e8b31d6a38075a0eb45980401c83ad175a014578cad1e00835e8b015a339075a00c05a8e41e083051662c4c7202b41d6895140603c75a2c15a2d45618e01de8bad16a0106520ef44028031c83ab47502d45598ad1828d1d680515663907500c14428e431480ad217a2cc700c0d1d68b551602b47528075a2d54498041d483ad120380c520ed41d40b31c8a2b460a2eb4598ac00075a2cc5598041de83ad1602c8c590f34054095164339060a24d45a8e4054a41d40b3516639060602f45a8b131403ad077a2140900e41d68bad00a3906601075a2eb4580e4195e3ad00a020c590f121828b5156639017a0eb45a8e0598a418280ad2263914500eb44d68b301e32c877a2c14018e41d483c016a3d1002907720eb4018eb51643a8060a2cc5928ac0568bbd1663806020eb45aab4818a401c03bd166a2d4090eb21d68b0140a2c875a0ea0598e451c8305103b5006290c720ea05828b516432b015a2cd45a8a01d483ad1260240720eb40ac0568c441882031d6a3906200c01598a431c80106020a54500c0f1882b3082b51580380620acc15a80418883105c0280c720c411880b515a62b4600ac6208145698e41880b0052a39065200414182b31c03134620ad40580ad188201882b515260106208c41400e4314831040202cc720cad1802b505662b0022b46202541498e4180801056a3acc500c411882b300802b4620ac41018ad1a80d18829105603906720c410280b31483110600acc75a8ac00823105062816a2b46008041598e451c03105620acc020ce41882b0040a2bc6268c40898a520c015983031c80100620a5455980f18823105602c8c720c410080b51c8301483105c2080c720cb21880b505662c860600415a8ab31c03104620ad40220c5200411882b31c0a048620ac41580b2196431040a02cc720c441802951c20314831106202cc75a8b218020105662b14500c415882930083390620a0020acc500c041882b305602c86290c41018a951643100600a4c7228e40082b1880b31486390600ac415a8ac01403105060a54090c441882b01c0a39062090620acc0580e4188231040a2bcc590c408802b51643390020acc15a8e0188620a540980e41882b1040a3906520c405982b31c83030020ad45418a0188331802b515663900208c415a8e030083105620ac0720cb318820502262cc622cc620ac01018e4188831016a3acc520c010083031c8a280620a441598131a8ac0082b105663806020c415a82e0148311062080c75a8b318803005662cc0a2cc6208c40598e451c83005220a0c5200e01882b3056a04c6298c41580a15a8a018883105260200720c4118820314863906202c015a8b319580105661012a2cc6720c014982b51c80100620acc55980418823105602ccc598c410082b51580280620a0c14a81318883105603814720c411880b31486390600ac6208145998b3188110056a2cc67200415982b51c03110620acc0580e418820188295156604c6208c41580b331c831040202d4720ca41802b30606390022cc6202d41598b3181801056a2acc700c411882b50080290620b841018e41a8131882b105602cc6598c410280b31c83110600a547418a400823105663816a2cc6008041598ac51403105620a4c020ce418828004062906220c40598e1580b318a63104062a54598c401802931c8a390020ac41598a01808310566598e0188231056a0100520c417082031c832cc6202d41598b3181801056a281663906220c014a8e831480104620acc7028131882b105602cc6598c41028414980419c8310500080c520c441880b31d6a2cc6008041598ac51403105630052639147200415882b31403010620acc1580b318a63104062a54598c4020c41580e051c831046202cc5218e41802b1056a2b00500c41418295026311c80105660ad4700c441882b301603906208c41028b331663102200ad4598cc720c410080b51c83290600acc1818e4008031052a2acc098c411882b016641882031d6a2cc6200c01598b351580105620acc700c041882b505c029062380620acc15a81318a63105602814598c411880b31c8a390600a441418a4018e41880b0056a2cc65600415982b51403110620a4c0400e41882310406291660106208c41580b331663104020254598ce4180293056a3900200c41598a1598e4181801056a2a0c500c411882950260390620ac41028e41948310166105603906598c41028113166314c600ad45598e4008231056a380c020c4158041818e451403105220acc098cb31882b004063906220c405a8eb3148300643104062a54590c401802931c8a390020ac41598a018083105660ac0590c4500c414182950243110620ac07028e41882310166290c720c015882b5158031643102200ad4590ce40082b3056a3806220c415980b01c8310462081457acc078c411882b0164639062080405a8e419483005660c0c720040188295142b31643030020ad45598e0188231056a0100520c417082031c832c86202d420ac0590cb218820501663906220c014a8e831480104620acc7028121882b0082b3158a280620ac414980419c8310500080c520c441880b31d6a2c86008c4159804015a310562080c568cad188095052639060200415a8eb3140310483005663ad4560041188283140a034620a441580e419c831040a02cc520c4720c4158020515e313462044c55a8ad18020105663914700c415882b3008331c80106020a54500c0f1882b305602b46220c41018eb51c83100600acc5200c720c411880b515a62b4600ac415a8ac01c03105660ad4020c441882e0142b31c03134620ad40580ad188231040a2b4c720c405802951c83290020a0c202cc720cad1802b505662b00200c415a8a930083104620a007218a418820⟩
set_option maxHeartbeats 5000000 in
private theorem valid5040 : ∀ r ∈ rows5040, Valid cfg 5040 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_3 : ∀ i ∈ List.range' 3 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_6 : ∀ i ∈ List.range' 6 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_9 : ∀ i ∈ List.range' 9 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_12 : ∀ i ∈ List.range' 12 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_15 : ∀ i ∈ List.range' 15 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_18 : ∀ i ∈ List.range' 18 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_21 : ∀ i ∈ List.range' 21 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_24 : ∀ i ∈ List.range' 24 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_27 : ∀ i ∈ List.range' 27 3, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_30 : ∀ i ∈ List.range' 30 2, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
private theorem run5040 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 720 a b c keys720) : Match 5040 a b c keys5040 := by
  apply refine step5040 h bad (by decide) (by decide) valid5040 _ old
  intro i hi
  change i < 32 at hi
  by_cases h0 : i < 3
  · exact test5040_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h3 : i < 6
  · exact test5040_3 i (by simp only [List.mem_range'_1]; omega)
  by_cases h6 : i < 9
  · exact test5040_6 i (by simp only [List.mem_range'_1]; omega)
  by_cases h9 : i < 12
  · exact test5040_9 i (by simp only [List.mem_range'_1]; omega)
  by_cases h12 : i < 15
  · exact test5040_12 i (by simp only [List.mem_range'_1]; omega)
  by_cases h15 : i < 18
  · exact test5040_15 i (by simp only [List.mem_range'_1]; omega)
  by_cases h18 : i < 21
  · exact test5040_18 i (by simp only [List.mem_range'_1]; omega)
  by_cases h21 : i < 24
  · exact test5040_21 i (by simp only [List.mem_range'_1]; omega)
  by_cases h24 : i < 27
  · exact test5040_24 i (by simp only [List.mem_range'_1]; omega)
  by_cases h27 : i < 30
  · exact test5040_27 i (by simp only [List.mem_range'_1]; omega)
  exact test5040_30 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+15=3^a*5^b*19^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=1 ∧ b%12=1 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  have h720 := run720 h bad h240
  have h5040 := run5040 h bad h720
  obtain ⟨i,hi,_⟩ := h5040
  exact Nat.not_lt_zero i hi
end D15


namespace D16
private def cfg : Config := ⟨16,2,19,1,4,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨0,4,0x0⟩
private def rows12 : List Rule := [
  .div 7,
  .div 5,
  .div 13,
  .div 3,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x6db6db6db0410410416db6db6db20a2082886db6db6db0410410416db6db6db20828820c6db6db6db0410410416db6db6db28820a208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+16=2^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=4 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  obtain ⟨i,hi,_⟩ := h12
  exact Nat.not_lt_zero i hi
end D16


namespace D17
private def cfg : Config := ⟨17,17,19,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨0,4,0x0⟩
private def rows12 : List Rule := [
  .div 3,
  .target,
  .div 5,
  .div 7,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x69a69a69a0000000004d44d351300000000069a69a69a0000000005134d44d300000000069a69a69a0000000004d35134d1000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+17=17^a*19^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  obtain ⟨i,hi,_⟩ := h12
  exact Nat.not_lt_zero i hi
end D17


namespace D18
private def cfg : Config := ⟨18,2,3,19,1,2,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨11,4,0x79a35ab1a687247a079b45741348a1461⟩
private def rows12 : List Rule := [
  .div 5,
  .div 7,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x1010101010100000000000000102010102010000000000001010101010100000000000000201010201010000000000001010101010100000000000000101020101020101010101010000000000001010e010102000000000000001010101010100000000000010201010d010000000000000010101010101000000000000c0101020101000000000000000000000000001010201010200000000000010101010101000000000000001020101020100000000000010101010101000000000000002010102010100000000000010101010101020101020101000000000000001010101010100000000000010102010102000000000000001010101010100000000000010201010201000000000000001010101010100000000000000000000000010101010101000000000000001010b010102000000000000101010101010000000000000010201010a01000000000000101010101010000000000000090101020101010101010101000000000000201010201010000000000000010101010101000000000000101020101020000000000000010101010101000000000000102010102010000000000000000000000000020101020101000000000000101010101010000000000000010102010102000000000000101010101010000000000000010201010201000000000000101010101010108010102010000000000000010101010101000000000000201010701010000000000000010101010101000000000000101020101060000000000000010101010101000000000000000000000000101010101010000000000000020101020101000000000000101010101010000000000000010102010102000000000000101010101010000000000000010201010201010101010101000000000000102010102010000000000000010101010101000000000000201010201010000000000000010101010101000000000000101020101020000000000000000000000000010501010201000000000000101010101010000000000000020101040101000000000000101010101010000000000000010102010103000000000000101010101010101020101020000000000000010101010101000000000000102010102010000000000000010101010101000000000000201010201010000000000000010101010101000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨139,6,0x1fe7ade1eb7e6eae1887262ded5878564d559f2564ed2b724a3f5ea777a0c5eb3a6e0ddb9b16e3e98a7462cc5883456cf528f74a6d12bbc7a2e5e9767a8cdeaf07a5f1ba396ebd9bbb36e2c1b8b6625cd8979568d95bb056be528b34a5c12aa837d94deae2b1a0ac6e1f4ac7de81fa947f621f7b84eab13da04c65134884f6e071ac1d28070b4de64370844fa937298dd6337880dcac2b5a4ae262bb8cafa02be987ca31feb04e2313b804d6c078a41ee6072801e1bf4e57d09edc86372d5dcb6f41d7f4a53d351f4a6ba357e8447a35ddc16b7117dc7537291dc47741dad0a5f4051d0a771057c445311d1c4667a256e8c4fa25cdc05b7190dc65b4259c4c5b1382b1216960599e1636ce81d36c44ab141ec5c4b1a06c50da5d129441a5a36674a9911e65c199136350a8d71e36848dd0635cd81a2a050181⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,11,[31,11],[2,3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,4,[31,2],[3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,4,[31,2],[3],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,10,[31,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨31,2,[31,2],[],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,10,[31,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,2,[31,2],[],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .prime 31,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,6,[31,2,3],[5],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,9,[61,3],[2,5,7],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,9,[61,3],[2,5,7],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨31,3,[31,3],[2],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,6,[61,2,3],[5],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,22,[31,2,11,17,19],[3,5,7,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,5,[61,5],[2,3],25,0x210863⟩,
  .pool ⟨31,5,[31,5],[2,3],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,5,[61,5],[2,3],31,0x46000062⟩,
  .pool ⟨61,3,[61,3],[2],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨31,7,[31,7],[2,3,5],793,0x12d020a252081880644c112020006092460020080020180882a080f008c000022017044708b2850016000655a08040086844885840080416a98001a0028534438883a01100000c403c0415044060100040100189241800101220c8980460412914102d2⟩,
  .pool ⟨61,3,[61,3],[2],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩,
  .pool ⟨61,2,[61,2],[],31,0x68818116⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,10,[61,2,5],[3,7],325,0x1b282210302018116d1430001a000809b68808802d0044045b6404001600030a2da206010302110536⟩,
  .prime 61,
  .pool ⟨61,8,[61,2],[3,5,7],31,0x68818116⟩,
  .pool ⟨31,8,[31,2],[3,5,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,20,[61,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,9,[31,3],[2,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,25,[61,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨61,4,[61,2],[3],31,0x68818116⟩,
  .pool ⟨61,4,[61,2],[3],217,0x1a20200420400081200080104003000820040012040008108010116⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,5,[31,5],[2,3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],61,0x1ffffffffffffffe⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,8,0xb70000000f000000b600000000000000002c0000000c00b500000000000000000c0000000d0000000f0000000e0000000000000f0000000e000000b40000000c0000000000000000b3000c000000b20000000000000000b1000000b0000000af0000000000000e000000ae0000000c0000000d000000ad00000000000000ac0000001c000000ab0000001a0000000000000000aa001a000000a90000000000000000a80000002b000000a70000000000002b000000a60000001a000000a5000000a40000000000002a000000290000001c0000000000000000a30000002900a200000000000000001a000000a1000000a00000001c0000009f00000000000000009e0000009d0000009c0000009b0000000000009a0000009900000098000000970000000000000000960027000000280000000000000000950000009400000027000000000000120000009300000092000000140000009100000000000014000000900000001200000000000000008f0000008e0000000026000000220000008d0000008c000000000000000026008b0000002500000000000000008a0000002200000024000000000000890000008800000087000000860000008500000000000084000000830000008200000000000000008100000080007f00000000000000007e0000007d0000002300000022000000000000007c0000000a000000040000007b0000000700000000000009000000070000000600000000000000000500000008002100000000000000000400000009000000070000000600000000000007000000060000000a0000000800000000000000007a0020000000200000000000000000200000002000000020000000020000007900000000000000007800000077000000760000000000007500000074000000730000007200000071000000000000010000001f0000007000000000000000006f00000002006e000000000000000002000000010000006d0000006c0000000000006b0000006a00000069000000020000000000000000680000001c000000670000001a0000006600000000000000001e001d0000001d00000000000000001c0000001d0000001a000000000000650000001a00000064000000630000001c00000000000019000000620000001b00000000000000001a00000019001600000000000000001800000016000000170000001600000000000000150000001400000061000000600000005f000000000000120000005e0000005d0000000000000000140000005c005b00000000000000005a00000059000000580000005700000000000056000000550000005400000013000000000000000053005200000012000000000000000051000000500000004f0000110000000000000000110000000c000000100000000f0000000000000d0000004e0000004d0000004c00000000000000000c004b0000000c00000000000000004a0000000f000000490000000000000f0000000e000000480000000c0000000d0000000000000c000000470000004600000000000000000b0000000b00000000000a0000000800000009000000070000004500000000000007000000060000000500000000000000004400000009000400000000000000000900000007000000430000000500000000000006000000050000000800000042000000000000000007004100000007000000000000000006000000050000000400004000000000000000003f0000003e0000003d0000003c0000000000003b00000002000000010000003a000000000000000039003800000037000000000000000036000000030000003500000000000034000000330000003200000031000000300000000000002f0000002e000000020000000000000000010000002d00⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_8 : ∀ i ∈ List.range' 8 3, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 11 at hi
  by_cases h0 : i < 8
  · exact test60_0 i (by simp only [List.mem_range'_1]; omega)
  exact test60_8 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨384,7,0xe777b3743db9dd74dd0ba9f469132b4a7d12c4ca963f1695b1348fc52d6c49627a634f5b189e9153d68ae716337131b9c514dc48ac767b27b3db19dec9cef6c765d27b2eb19d749ceba7f07b030bd9fc1740c2ba679756f53a99e55dbd4aeaf0751b83aab85d46c2eaaf0571b82bab855c6c2aedfc6333e31b7b58ccdac6dfc4533e22b7b514cda8a1f6634b3b187d9152ce8aefb7b3bdbdbbb1eced8f6efb5d3bdaebbb174ed8babf27b231bdafc9748c6baa7b751763aa9ed5c5d8aed75752fabab599d4bccead75572faabb5995cbccaea7869174b4a9e12c5d29676f69770349dbd2ddc0965f8636b4b197e115ad28a8f2630b931a38d8c2c6c68f2450b922a38d142c68ae5439b6a1cf914e6d8a73e541bb6a0df9146ed8a37cdd33aae99f338cea9c67cdd15aae8af33856a9c2b0d733c2419c35c570902b3d72dda416cf5c3f6901fe512db6896f908b6d845be510fb6887f9083ed841f55a27e6593d56827996139d12792893e7089e4844f9d10992884e708264841385a2186d10e12c861964385a0386d01e12c0e1960775839f649cdd606fd9237bcf39a279cef00e688073bcf1ba278def006e8803715b33c6619c56c571982ba583396c19e924ce59267a581596c0ae924565922bd5233ae199f54856b862b7552df6316dd543fd8c1f1522dc6196c5483f1861fedb27bad93fb309ee984fedb09bad84fb3026e9813d5521aea90f51886b8c43d5503aea81f5180eb8c078cf218a010e33c0e28007bbaf821d7c2eafe0857f0bbada21d6d2eaf68857b4eb4f8392fc3ad368e4bb48bdec09ef622bbb025dd88bdce09ee722bb3825d9c437ec5d47610df397519c3b6f8593fc0edb6964fb4e30f83587c3887e0d43f0e30da3586d388768d43b4cb9f229cf932abc8a55e4cb9d429cea32ab50a55a8e36f2353f938db50d4fa89b0f2110f926c350443a8839ec0557620e7381559cb33ec1d9f62c93b0749d8b33ce1d9e72c93387499c9bce611e7326b79845bcc9bcc811e6426b72045b90cbce0296f032f308a5b84836e005b70209f8014fc0836c205b61209f0814f849b3e01127026cf0844984ab8f2194f92ae350653a8c35f22537930d75094da8632f26d1f918cb51b47a8c3bec2567630ef389599c035ec3d37600d738f4d9c32fec550760cbf395419ce1cb6b46db787262d1b31b13b69c9db6c12da7096db13989c9cc6c12627093199cb090e586636c241b6199c9290e4966364a41b25090b0c00d842424b00325816aa84b55601eaa10f558168c84b46601e3210f19b10aa9c0d56c423270319999a49055266661a4150d513a4e4252544e1b9090de10a4b4852780692d0349e1086b484378061ad030d39c9ed86cf4e720361b01c999ea8ccf722a7aa153dc9980a8cc0722a02a1501⟩
private def rows120 : List Rule := [
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,17,[41,17],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨41,8,[41,2],[3,5,7],31,0x121d47b6⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],341,0x10005e2024580224044800c418080600000c000180000060000c000018040608c0048809100689011e8002⟩,
  .pool ⟨41,14,[41,2,7],[3,5,11,13],31,0x121d47b6⟩,
  .pool ⟨31,4,[31,2],[3],123,0x10000124014004012182110536⟩,
  .pool ⟨31,4,[31,2],[3],41,0x1b382b50736⟩,
  .pool ⟨41,28,[41,2,7,17,19,23],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],41,0x1fffffffffe⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨31,10,[31,2,5],[3,7],41,0x1b382b50736⟩,
  .pool ⟨31,10,[31,2,5],[3,7],123,0x10000124014004012182110536⟩,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],915,0x20820000a6020080100022002020004090810c840040008001000021900200001029000000000000208000a00200041120840000008001000024340328000000840800209020000a6000886092502c021204100068220001000120008301200000060008120001000141100220a00108b0092⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],1025,0x242031006008a0f6204002402122053040c00ab80c0da43222a12101880100c126b14000962101523902260815c0644c2193050909040208860835c80000b000089148303802ae0702614e982869402000c41041ec4084248000540a40898205f4391b0a6441434a410082008a4d72802024401220730c0e002fa0c09a43a22a⟩,
  .pool ⟨41,10,[41,2,5],[3,7],31,0x121d47b6⟩,
  .pool ⟨41,16,[41,2],[3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,27,[41,3,17,19,23],[2,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨31,3,[31,3],[2],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨41,16,[41,2],[3,5,7,11,13],31,0x121d47b6⟩,
  .pool ⟨41,9,[41,3],[2,5,7],427,0x5040001000400820000040010000001400020008000200800000000000001004000100040002800000080020000041002000800020a⟩,
  .pool ⟨41,13,[41,13],[2,3,5,7,11],61,0x1713e6940a59f23a⟩,
  .pool ⟨31,5,[31,5],[2,3],41,0x1b382b50736⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨61,7,[61,7],[2,3,5],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨61,10,[61,2,5],[3,7],41,0x1b382b50736⟩,
  .pool ⟨31,9,[31,3],[2,5,7],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨31,8,[31,2],[3,5,7],41,0x1b382b50736⟩,
  .pool ⟨31,8,[31,2],[3,5,7],1025,0x1a20200070000000a800000000000002220000000000000000000000000000202020000000000000000000000000000000000000000000000000000000003000300030000000000000000000000000000000000000000000000000000000001010100000000000000000000000000001110000000000000054000000380010116⟩,
  .pool ⟨41,14,[41,2,7],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,36,[41,2,3,17,19,23,29],[5,7,11,13,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,13,[41,13],[2,3,5,7,11],183,0x4406824020400020424880000112420400020402416022⟩,
  .pool ⟨61,14,[61,2,7],[3,5,11,13],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨61,4,[61,2],[3],41,0x1b382b50736⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],451,0x688580269400082c82200000008448a0800c0810005000001001903060c09800800000a00081030010512210000000441341000296401a116⟩,
  .pool ⟨61,31,[61,17,19,23,29],[2,3,5,7,11,13,31],1155,0x20840001a64308201141020004340228908009801a0034892502900424c001024108221808301028000220b0400000412400480000880802420510832180820080190026802520102034810980122420430886802000506100ca2806912086490492186d020021948228141220221a04109129008845004020000328060244a4080120182520c141168200800248b0012⟩,
  .pool ⟨41,16,[41,2],[3,5,7,11,13],915,0x102410820120480080002080020804014800400004c008041000800804020001221840100201040100061a0000080502002100000804500804424010800000002180802802400020010484012102400030010002c02884000010000800122110804100802004000414090002026100090116⟩,
  .pool ⟨41,27,[41,3,17,19,23],[2,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,9,0x88402011088402011d704c27add604c27ab09048241209048241209048241209048241217040202e17040202e080b85c10080b85c10168381c2d168381c2dd504c27a9d404c27a70969b4a120969346121668b422c166833e2ccf0381d9dce0381d9b0e8743a1d0e8743a1dcd6673197cb6572993c90381d91c80381d8f0763b1a0e07633160e0e8743a1d0e8743a1dc56271187c36170983158ac562b158ac562b158381c2b158381c2b0e8743a1d0e8743a1d148a85429148a85429c1607017fbf5f6f97b075eaf20e075e2ee0e0e8743a1d0e8743a1dbb5d6e973b95c6e16f0b0984c160b0984c160a8381c150a8381c15b705c2f6db605c2f6b0c86030190c8603019b505c2f69b405c2f670c86030190c8603019b3596c963b1586c15f0b06c36160b06c3616070542a0e070542a0e0b8a050170b8a050170c06432180c0643218af09c4f5dae09c4f5b130582c26130582c260bd6ab2170bd62ae170bd5aaa170bd52a617a9546a14fa7536994b0b06c36160b06c3616108844221108844221a55269147a35168943a1506813f9f4f6793b124ea7224124e26e241108c46221108c462210884422110884422112cda6a2512cd26625100804020100804020994c6612f974b6592b100804020100804020124aa5224124a24e241108c46221108c462210884422110884422193496492391486411f1088442211088442218f476391b8d46631171008040201008040200502c160a0502c160a0402412080402412080402412080402412080245a2a040245226040080000010080000010101c0e020101c0e0289446210f87436190b0142a1202014220e028341609038140600ff028180c05028180c057f01008fd7e01008fb008000001008000001013e9f202013e1ee020fbd9ea1f0fbd1e61f793c5e0ef773b5d8eb0180402030180402030f008041e0f008041e018040203018040203038080407038080407753a5d0e773395c8e37101008e17001008df6f375b8db6d365b0d76b0381cd56a0381cd369345a0cf6733598cb07329920e073218e0e0e8743a1d0e8743a1d0e070381c0e070381c0bb198a170bb1186170c06432180c06432186130580bf5f2f578bb5d2e570b75b2d568b3590582cb1580582caf5705c2ead5605c2eab070542a0e070542a0e5505c2ea95405c2ea70c86030190c86030195329548a351285409f0b06c36160b06c36164f275389b4d26530970b06c36160b06c36160a86834150a86834150c06432180c06432184b05c2e954a05c2e9349245208f47235188b450582c89440582c87070542a0e070542a0e430381c85420381c834104c26814004c267f0a1f8fa140a1f0f6143d04824793c0482477081d8ea10081d0e610099c8e213099c0de130904824120904824120804422100804422100703c1e0e0703c1e0e05828140b05828140b060341a0c060341a0c0502c160a0502c160a04024120804024120804024120804024120837010086d36010086b000040200000040200038080407038080407351a4d06733194c863030140a06030140a0631184c05f2f174b85b00004020000004020001168b20201160ae020180402030180402030380804070380804072b154a85329144a04f27010084d26010084b028180c05028180c052501008492401008470080c06010080c0601011188a0201110860221104803f1f0f4783b010e87202010e06e021b0d46833190c4602f000040200000040200⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_137 : ∀ i ∈ List.range' 137 2, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 139 at hi
  by_cases h0 : i < 137
  · exact test120_0 i (by simp only [List.mem_range'_1]; omega)
  exact test120_137 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨84,8,0x4cead94cea618872d91072d9887261107261c4729dc4722588ea9d10ea9d88ea2510ea2504bad904ba617c429d7c4225b85acd405acdb85a55405a557cd2cd04d2cd7cd25504d255b8d29140d291b8d21940d2197c5a91045a917c5a19045a19d0bacd58bacdd0ba5558ba55d04291584291d0421958421988a2c110a2c188a24910a249882a85102a85882a0d102a0ddc8ac1648ac1dc8a49648a49dc1285641285dc120d64120de842c17042c1e84249704249e8ba8570ba85e8ba0d70ba0d9472b51c72b594723d1c723d94ea791cea7994ea011cea01dca2b564a2b5dca23d64a23d282ab5282a3ddc2a79642a79dc2a01642a01a0a279a0a201⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨241,36,[241,2,3,19,23,29],[5,7,11,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨241,15,[241,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨31,21,[31,3,7,19],[2,5,11,13,17],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨241,15,[241,3,5],[2,7,11,13],217,0x1530503d00a30404202c9942104008210a64d01080831402f02832a⟩,
  .pool ⟨241,38,[241,2,19,23,29,37],[3,5,7,11,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨61,29,[61,19,23,29],[2,3,5,7,11,13,17],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,7,0xc180000c1800000000000000000000030600003060000000000000000000000000000000000000000000c180000c18000000030600003060000000000000000000000000000000030600003060c180000c180000b680000b640000002c570002b5500000000000000000000000000000002a050002985a544000a13c000000000000000000000000000000009380000934000000000000000000002604000258400000000000000000254900024478d14000890c0000000000000000000000000000000850400080fc0000001f3d0001e3b000000000000000000000000000074e400070dc000000000000000000001b350001a33000000000000000000000000000064c400060bc00000000000000000000172d000162b0000000000000054a4000509c00000000000000000000132500012230001121000101f040c000040c00000000000000000000000000000003c74000386c0000000182000018200000000000000000000000000000000d190000c17000000000000002c54000284c0000000000000000000000000000000000000000000002444000203c000000008e000008d0000000000000000000000000000000060b000050910040000e04000⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_137 : ∀ i ∈ List.range' 137 137, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_274 : ∀ i ∈ List.range' 274 110, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 384 at hi
  by_cases h0 : i < 137
  · exact test240_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h137 : i < 274
  · exact test240_137 i (by simp only [List.mem_range'_1]; omega)
  exact test240_274 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨14,10,0x9a072ae488589c940072ae6681c95140072545f058861222ca9f6687689d7c2ca9f5007689d9a1da81488b2915401da815f0b2915⟩
private def rows720 : List Rule := [
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨31,24,[31,2,3,23],[5,7,11,13,17,19],37,0x1ffffffffe⟩,
  .pool ⟨31,24,[31,2,3,23],[5,7,11,13,17,19],577,0x1eb63cf47e82bd94bbe610272e9e08926e2ab5f14c5431bc76a75be052064c25a6e07766799bb81d9690c981281f6b95b8f630a8ca3eb551d92441e5d390219f74a6f505f8bcf1b5e⟩,
  .pool ⟨37,26,[37,2,13,23],[3,5,7,11,17,19],61,0x1ffffffffffffffe⟩,
  .pool ⟨37,4,[37,2],[3],41,0x1b382b50736⟩,
  .pool ⟨37,26,[37,2,13,23],[3,5,7,11,17,19],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],37,0x10ac804d42⟩,
  .pool ⟨181,16,[181,2],[3,5,7,11,13],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨37,4,[37,2],[3],73,0x10080002100010116⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],949,0x175663565e83704f610d7e83069a2c1342e3a4641549fb43bb08c49a9967f79738894ed4187a1e4ea63621f400946bc59106a9b94f6ce050b1a218000611634281cdbca765582268f58a400be11b195c9e17860adca4473a7bf9a65648c43770b7e4aa098971d0b20d1658305fac21bc83b05e9ab19aba⟩,
  .pool ⟨37,24,[37,2,3,23],[5,7,11,13,17,19],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨37,26,[37,2,13,23],[3,5,7,11,17,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨577,36,[577,2,3,23,29],[5,7,11,13,17,19,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,5,0x84210842108421084210842108421084210842108421084210842108421084210856a6254bda92a5a549d298b4a14c5a9695316a5a549ca92a5b5495a98a4a14c5a9694a14c5a96952d4c4a9785254b4a92d5316a4a14c5a96962d4b4a9375254bb292b5302108421084210842108421084210842108421084210842108421084210842108421526aa62d4b4b16a5a5494292a5d1495a9935256a6254b5316a5a54942d2a4c94c5a92a5c5495a98a4c14c5a96962d4b4a92852d2a4bd4c5a9ca4ad4c4a96a62d4b4a92829846114453086318c4310c621886318c4310c4318c6218c4310c43188a62984611445314c2308a611445314c218c4310c4318c621886218c45314c2308a611445314c200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842139ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce739ce71886218c6310c621886218c45314c2308a5308c2288a610c631886218c4310c631884318c621886611445314c218c4310c4319845114c53086310c4310c6218c6310c43114c5308c228c4310c63188a611845114c611445314c218c4310c43188a629846114a611845114c2298a6118451886218c63108a629846114c2288a629843188621886300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018c4310c43188a42904411482288a42904218c6310c43208a2290a411482208a229082288a4290431886218863114852088229482208a22904318c6218864114452148218c4310c431886318c4310c82288a429042290a4110451886218c6310c621886218c621886318c4520882288a410c631886219482208a22904318c621886310c4318c62084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421000000000000000000000000000000000000000000000000000000000000000000002108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210840000000000000000000000000000000000000000000000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_40 : ∀ i ∈ List.range' 40 40, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_80 : ∀ i ∈ List.range' 80 4, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 84 at hi
  by_cases h0 : i < 40
  · exact test720_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : i < 80
  · exact test720_40 i (by simp only [List.mem_range'_1]; omega)
  exact test720_80 i (by simp only [List.mem_range'_1]; omega)
private def keys2160 : Keys := ⟨0,12,0x0⟩
private def rows2160 : List Rule := [
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],109,0x1752639f4e85b003685cbe7192ba⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],541,0x175267de4e15711a690ef22343f3a49f19f7ec4c529fce872a8146d19f2db506a0b00341582b6d3e62d8a055385cfe528c8dfbe63e4973f0b113dc259623aa1c9ef992ba⟩,
  .prime 109]
private def step2160 : Stage := ⟨cfg,720,3,keys720,keys2160,rows2160,2,0xa9556a555a95540015000540015a9556a555a9556a555a9556a555a9556a555a9554001500054001501500054001501556a555a9556a01500054001501556a555a9556a555a9556a555a80540015000540555a9556a555a80540015000540⟩
set_option maxHeartbeats 5000000 in
private theorem valid2160 : ∀ r ∈ rows2160, Valid cfg 2160 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test2160_0 : ∀ i ∈ List.range' 0 14, ∀ x y z : Fin 3, Test step2160 i x y z := by decide +kernel
private theorem run2160 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 720 a b c keys720) : Match 2160 a b c keys2160 := by
  apply refine step2160 h bad (by decide) (by decide) valid2160 _ old
  intro i hi
  change i < 14 at hi
  exact test2160_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 510510∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+18=2^a*3^b*19^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=1 ∧ b%12=2 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  have h720 := run720 h bad h240
  have h2160 := run2160 h bad h720
  obtain ⟨i,hi,_⟩ := h2160
  exact Nat.not_lt_zero i hi
end D18

private theorem supported_three (m x y : ℕ) (pos : 0 < m)
    (sup : ∀ p : ℕ, p.Prime → p∣m → p=x ∨ p=y ∨ p=19) :
    ∃ a b c : ℕ, m=x^a*y^b*19^c := by
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

private theorem supported_offset {n j x y : ℕ} (hj : 0<j) (jl : j<19) (div : 510510∣n)
    (hit : 19∣n+j) (xy : x*y∣n+j) (cop : (x*y).Coprime 19)
    (small : ∀ p : Fin 19, p.val.Prime → p.val∣j → p.val=x ∨ p.val=y)
    (sol : v_l 1 n=1) : ∃ a b c : ℕ, n+j=x^a*y^b*19^c ∧ 0<a ∧ 0<b ∧ 0<c := by
  have whole := cop.mul_dvd_of_dvd_of_dvd xy hit
  obtain ⟨t,ht⟩ := whole
  have pos : 0<t := by by_contra! h; rw [show t=0 by omega,mul_zero] at ht; omega
  obtain ⟨a,b,c,eq⟩ := supported_three t x y pos (by
    intro p pp dp
    have dn : p∣n+j := ht ▸ dvd_mul_of_dvd_right dp _
    by_cases low : p≤j
    · have tab : ∀ r : Fin 19, r.val.Prime → r.val∣510510 := by decide
      have dj := (Nat.dvd_add_iff_right ((tab ⟨p,by omega⟩ pp).trans div)).mpr dn
      rcases small ⟨p,by omega⟩ pp dj with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · by_contra! neq
      exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.two_primes hj pp
        (by decide : Nat.Prime 19) neq.2.2 (by omega) jl dn hit sol)
  refine ⟨a+1,b+1,c+1,?_,by omega,by omega,by omega⟩
  rw [ht,eq,pow_succ,pow_succ,pow_succ]
  ring

private theorem close_from_three {n j x y a b c u v : ℕ} (hj : 0<j) (small : j≤18)
    (big : 1000000000000000000<n) (div : 510510∣n) (sol : v_l 1 n=1)
    (jval : j=x^u*y^v) (shape : n+j=x^a*y^b*19^c)
    (ha : a%12=u) (hb : b%12=v) (hc : c%12=0) : False := by
  let z := x^(a/12)*y^(b/12)*19^(c/12)
  have regroup (p i r : ℕ) (eq : i%12=r) : p^i=p^r*(p^(i/12))^12 := by
    rw [←pow_mul,←pow_add,show r+i/12*12=i by omega]
  have twelfth : n+j=j*z^12 := by
    calc
      n+j=x^a*y^b*19^c := shape
      _=j*z^12 := by
        rw [regroup x a u ha,regroup y b v hb,regroup 19 c 0 hc,jval]
        dsimp only [z]
        rw [mul_pow,mul_pow,pow_zero]
        ring
  have hi : 1<z := by
    by_contra! low
    have zz := Nat.pow_le_pow_left low 12
    have nj := Nat.mul_le_mul_left j zz
    omega
  exact no_nineteenth_twelfth hj small big div hi twelfth sol


/-- A missing nineteen cannot have its first positive hit at a large prime-successor solution
divisible by every smaller prime. -/
theorem exclude_offset {n j : ℕ} (big : 1000000000000000000<n) (div : 510510∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (lo : 0<j) (hi : j<19) (hit : 19∣n+j) : False := by
  interval_cases j
  · have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 19) pp).mp hit
    omega
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D2.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=2) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D3.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=3) (x:=3) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D4.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=4) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=5) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D5.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=5) (x:=5) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=3) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D6.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=6) (x:=2) (y:=3) (u:=1) (v:=1) (by decide) (by decide) big div sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=7) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D7.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=7) (x:=7) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D8.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=8) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=3) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D9.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=9) (x:=3) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=5) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D10.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=10) (x:=2) (y:=5) (u:=1) (v:=1) (by decide) (by decide) big div sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=11) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D11.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=11) (x:=11) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=3) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D12.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=12) (x:=2) (y:=3) (u:=2) (v:=1) (by decide) (by decide) big div sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=13) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D13.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=13) (x:=13) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=7) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D14.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=14) (x:=2) (y:=7) (u:=1) (v:=1) (by decide) (by decide) big div sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=5) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D15.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=15) (x:=3) (y:=5) (u:=1) (v:=1) (by decide) (by decide) big div sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D16.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=16) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=4) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=17) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D17.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=17) (x:=17) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=3) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D18.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=18) (x:=2) (y:=3) (u:=1) (v:=2) (by decide) (by decide) big div sol (by decide) eq ra rb rc

/-- Every sufficiently large prime-successor solution divisible by the primes through
seventeen is also divisible by their product with nineteen. -/
theorem primorial_nineteen {n : ℕ} (big : 1000000000000000000<n) (div : 510510∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) : 9699690∣n := by
  have d : 19∣n := by
    by_contra missing
    let j := 19-n%19
    have nz : n%19≠0 := fun h => missing (Nat.dvd_of_mod_eq_zero h)
    have hj : 0<j := by dsimp only [j]; omega
    have lo : j<19 := by dsimp only [j]; omega
    have sum : n%19+j=19 := by dsimp only [j]; omega
    have hit : 19∣n+j := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod,Nat.mod_eq_of_lt lo,sum,Nat.mod_self]
    exact exclude_offset big div pp sol hj lo hit
  exact (by decide : Nat.Coprime 510510 19).mul_dvd_of_dvd_of_dvd div d

end Erdos889.PrimeNineteen
#print axioms Erdos889.PrimeNineteen.primorial_nineteen
