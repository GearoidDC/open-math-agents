import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
import Mathlib.Data.Nat.Factorization.Induction

/-! A modular certificate for the first multiple of seventeen. -/
namespace Erdos889.PrimeSeventeen

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
  div : 30030∣n
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
  | .div p => p∣30030 ∧ Stable g L p
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
theorem no_seventeenth_twelfth {n j z : ℕ} (hj : 0<j) (small : j≤16) (sev : 17∣z) (big : 1<z)
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
  have classifyA (p : ℕ) (pp : p.Prime) (low : p≤32) (dp : p∣t+1) : p=2 := by
    have tab : ∀ q : Fin 33, q.val.Prime → ∀ u : Fin q.val, (u.val^4+1)%q.val=0 → q.val=2 ∨ q.val=17 := by decide +kernel
    have m := ((Nat.mod_modEq z p).pow 4).add_right 1
    have d17 : 17∣t := sev.trans (dvd_pow_self z (by decide : 4≠0))
    exact (tab ⟨p,by omega⟩ pp ⟨z%p,Nat.mod_lt _ pp.pos⟩ (m.trans (Nat.modEq_zero_iff_dvd.mpr dp))).resolve_right
      (by intro eq; change p=17 at eq; subst p; omega)
  obtain ⟨p,pp,hp,dp⟩ : ∃ p : ℕ, p.Prime ∧ 32<p ∧ p∣t+1 := by
    by_contra miss
    have pow2 := Nat.eq_prime_pow_of_unique_prime_dvd (show t+1≠0 by omega) (fun {p} pp dp =>
      classifyA p pp (by by_contra! hi; exact miss ⟨p,pp,hi,dp⟩) dp)
    let e := (t+1).primeFactorsList.length
    change t+1=2^e at pow2
    have ee : 2≤e := by by_contra! low; have := Nat.pow_le_pow_right (by decide : 0<2) (show e≤1 by omega); omega
    have dv : 4∣t+1 := pow2 ▸ pow_dvd_pow 2 ee
    have m := ((Nat.mod_modEq z 4).pow 4).add_right 1
    have bad := m.trans (Nat.modEq_zero_iff_dvd.mpr dv)
    have tab : ∀ i : Fin 4, (i.val^4+1)%4≠0 := by decide
    exact tab ⟨z%4,by omega⟩ bad
  obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd (show B≠1 by omega)
  have hq : 32<q := by
    by_contra! low
    have tab : ∀ q : Fin 33, q.val.Prime → ∀ u : Fin q.val, ¬Nat.ModEq q.val (u.val^4) (u.val^8+1) := by decide +kernel
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
private def cfg : Config := ⟨2,2,17,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x89045⟩
private def rows12 : List Rule := [
  .div 3,
  .div 7,
  .div 5,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x102042042210210210086081081408408408042102042210210210081085081408408408042042102210210210081081083408408408⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨5,6,0xe3902cb4051501c740105⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,8,[31,2],[3,5,7],63,0x6880800180010116⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],549,0x1a60a00261041120a0084490094824032014120184820800120982106094002924004c800925000a41821064120004104860120a01300904a4024884014122082190014196⟩,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩,
  .pool ⟨31,24,[31,2,3,17,19,23],[5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨61,8,[61,2],[3,5,7],31,0x68818116⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0xa0000090000050000080000043000002000007000001000006⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨4,7,0x1d3a80e8e40048200205⟩
private def rows120 : List Rule := [
  .pool ⟨41,7,[41,7],[2,3,5],31,0x121d47b6⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨31,23,[31,19,23],[2,3,5,7,11,13,17],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨31,23,[31,19,23],[2,3,5,7,11,13,17],819,0xa00000000000000800240000200200005020841200a48200000208028000804008100020000344000300000000008200004000020100000020024000000000800200020004000020008848044000808100000004000240200100001840100008000a0c80002⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨41,11,[41,11],[2,3,5,7],51,0x21a0022996832⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,4,0x95854444323211110706⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 5, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 5 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨8,8,0x74ed00747500ecb100ec390004b9000441007c7d007c05⟩
private def rows240 : List Rule := [
  .pool ⟨241,20,[241,2,5,19],[3,7,11,13,17],75,0x116026c145829b0536⟩,
  .pool ⟨241,29,[241,19,23,29],[2,3,5,7,11,13,17],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,4,0x1918716105043020⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 4 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨19,13,[19,13],[2,3,5,7,11],17,0x1a316⟩,
  .pool ⟨19,3,[19,3],[2],9,0xb⟩,
  .pool ⟨19,9,[19,3],[2,5,7],45,0x10080c120a⟩,
  .pool ⟨19,9,[19,3],[2,5,7],27,0x8060b⟩,
  .pool ⟨19,8,[19,2],[3,5,7],17,0x1a316⟩,
  .pool ⟨19,6,[19,2,3],[5],45,0x55898f135e⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],51,0x21a0022996832⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,3,0xd659a6b35d659a6bacb359a6bac6410c22116410c32882190c3288⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 8 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+2=2^a*17^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D2

namespace D3
private def cfg : Config := ⟨3,3,17,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x67⟩
private def rows12 : List Rule := [
  .div 5,
  .div 7,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x40040080010008008001002001400200200040100040008008010002001001200200400080040040008010008001001003200400200⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨1,6,0xab7⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,10,[31,2,5],[3,7],48,0x1109b2514db6⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],16,0x8002⟩,
  .pool ⟨61,6,[61,2,3],[5],112,0x1131950bd9b33a5571d14f9db77e⟩,
  .pool ⟨61,2,[61,2],[],31,0x68818116⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0xa00000803010000008⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨0,7,0x0⟩
private def rows120 : List Rule := [
  .pool ⟨41,16,[41,2],[3,5,7,11,13],32,0x2070317⟩,
  .pool ⟨41,31,[41,17,19,23,29],[2,3,5,7,11,13,31],132,0x808000220000808208028a20228a0082⟩,
  .pool ⟨41,16,[41,2],[3,5,7,11,13],73,0x1a30280023100050316⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,2,0x94⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 1 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+3=3^a*17^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  obtain ⟨i,hi,_⟩ := h120
  exact Nat.not_lt_zero i hi
end D3

namespace D4
private def cfg : Config := ⟨4,2,17,1,2,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x8a046⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .div 7,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x44144144120e20a20a0510510512882c828844144144120a20d20a0510510512882882c844144144120a20a20c0510510512c8288288⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨5,6,0xe3a02cb80516028a80106⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],63,0x6880800180010116⟩,
  .pool ⟨31,7,[31,7],[2,3,5],549,0x82080002000012080080490090000012010000080000000000082002090002000000480092400080082002412000410482012080010090480000080010002082090010092⟩,
  .pool ⟨31,10,[31,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],819,0x40904001001020008009008044001040008244000000001000001000000000800005000049005104000004a00000040000008000100000020000005200000208a00920000a0000100000000080000080000000022410002080022010090010004080080020902⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],31,0x68818116⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0xa0000090000050000080000043000007000002000001000006⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨4,7,0xa330050a80048400206⟩
private def rows120 : List Rule := [
  .pool ⟨41,14,[41,2,7],[3,5,11,13],31,0x121d47b6⟩,
  .pool ⟨41,8,[41,2],[3,5,7],31,0x121d47b6⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],119,0x141324470b0970652b11cb15977e⟩,
  .pool ⟨61,29,[61,19,23,29],[2,3,5,7,11,13,17],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩,
  .pool ⟨31,25,[31,5,19,23],[2,3,7,11,13,17],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,27,[41,3,19,23],[2,5,7,11,13,17],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,4,0x54543333222219180706⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 5, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 5 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨16,8,0xa0de0028de00a06600286600a0a20028a200a02a00282a007cba0004ba007c42000442007c7e00047e007c06000406⟩
private def rows240 : List Rule := [
  ]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,4,0xfedcba9876543210⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 4 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨19,6,[19,2,3],[5],45,0x55898f135e⟩,
  .pool ⟨19,18,[19,2,3],[5,7,11,13,17],45,0x55898f135e⟩,
  .pool ⟨19,7,[19,7],[2,3,5],31,0x121d47b6⟩,
  .pool ⟨19,7,[19,7],[2,3,5],85,0x20200ca0300000829028a⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,2,0x3744d33744cdd344cdd1334dd133744d3374264492264489924489912249912264492264⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 16, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 16 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+4=2^a*17^b) (ha : 0<a) (hb : 0<b) : a%12=2 ∧ b%12=0 := by
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
end D4

namespace D5
private def cfg : Config := ⟨5,5,17,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x61⟩
private def rows12 : List Rule := [
  .div 3,
  .div 7,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x81042041210208408042041081208408210041081042408210208081042041210208408042041081208408210041101043408210208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨1,6,0x781⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨61,10,[61,2,5],[3,7],124,0x5151111111115113315113113111536⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],497,0x1a317819fb144a5fab285880d2258fba226c2250ca130502cc30308f16ba3a317175a3c43030cd0283214c2910d91177c6912c04685357e948a37e607a316⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,2,0x408000101030⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨0,7,0x0⟩
private def rows120 : List Rule := [
  .prime 41,
  .pool ⟨41,9,[41,3],[2,5,7],427,0x5040001000400820000040010000001400020008000200800000000000001004000100040002800000080020000041002000800020a⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,1,0xa⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 1 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+5=5^a*17^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  obtain ⟨i,hi,_⟩ := h120
  exact Nat.not_lt_zero i hi
end D5

namespace D6
private def cfg : Config := ⟨6,2,3,17,1,1,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨11,4,0x7ab14b2798193a7947a75415ba3543671⟩
private def rows12 : List Rule := [
  .div 7,
  .div 5,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x1110111011120111e11101111011101112111121110111011110111211102111011101111011121110111101110111d1111211101110011101112111121110111011110111211101110111011101111011101110011101110111101110111011110111011101111011101110011101110111101110111011110111011101111011101110011101110111101110111011121110111011110111211101111011101112011121110111101110111c11112111011101111011121110211101110111101112111011110111011121111b1110111001110111211101110111011110111011101111011101110111101110111001110111011110111011101111011101110111101110111001110111011110111011101111011101110111101110111011121110111001110111a111121110111011110111211101111011101112011121110111101110111211119111011101111011121110211101110111101112111011110111011121110111011101111011101110011101110111101110111011110111011101111011101110011101110111101110111011110111011101111011101110011101110111101110111011101112111011110111011121111211101110011101112111181110111011110111211101111011101112011121110111101110111211112111011101111011171110211101110111011101110111101110111011110111011101111011101110011101110111101110111011110111011101111011101110011101110111101110111011110111011101111011101110111011121110611101110111101112111011110111011121111211101110011101112111121110111011110111511101111011101112011121110111101110111211112111011101110111011101111011101110011101110111101110111011110111011101111011101110011101110111101110111011110111011101111011101110011101110111101110111011101110111211112111011101111011121110211101110111101114111011110111011121111211101110011101112111121110111011110111211101111011101113011121110111011101110111101110111011110111011101111011101110011101110111101110111011110111011101111011101110011101110111101110111011110111011101111011101110⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨55,6,0x1a7f99ab842dd53935661d5cb724eac9b25e78079e19b5496120d86cc55501560c49e252567f5b93d56de9893a7a1e92b7762addb8776e7d188744aac570dd74075d19a68069d3174435d125450051731150645a0d15edf1187c6aae5d87946dd97ab6767d949366a1d9db736a7cd19335e1cdab705e7c1d930521c1⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,3,[31,3],[2],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,4,[61,2],[3],31,0x68818116⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,8,[61,2],[3,5,7],217,0x1a20200420400081200080104003000820040012040008108010116⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,8,[61,2],[3,5,7],31,0x68818116⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨31,24,[31,2,3,17,19,23],[5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,10,[31,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,8,[31,2],[3,5,7],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,10,[31,2,5],[3,7],1281,0x1b28221060300800a0002800020000032000000522000000002100000000002930010010100000886020000000400000000020080000000000010000100022082800000800000c000800000000021200b4012100000000004000c00000400000504110002000020000000000004010000000000800000010184400002020020032500000000002100000000112800000130000010000500014004030182110536⟩,
  .pool ⟨31,7,[31,7],[2,3,5],793,0x12d020a252081880644c112020006092460020080020180882a080f008c000022017044708b2850016000655a08040086844885840080416a98001a0028534438883a01100000c403c0415044060100040100189241800101220c8980460412914102d2⟩,
  .pool ⟨31,8,[31,2],[3,5,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,8,[31,2],[3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,10,[31,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,7,0x26000000000000220004b000070000000000000a00000070000500000000000004c000220000000000000a00000220004a0000000000000e000068000480000000000000248000480002200000000000090000470000046000000000000450000680000000000009000044000000000e000220000000000000900002c00086000000000000004400012000420000000000001000009000000680000000000020800044000000000001000001c000007e0000000000001600010000078000000000001f000001e8000f00000000000002c0001c0000000000001a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001400004000000000000760003a00000000000006000003900003000000000000050000e00006e00000000000000d80006a00005000000000000060001a0000003000000000000050000cc000000000000140006400000040000000000006200006000050000000000000280000000800003000000000000050000c00005e0000000000000030000160002e0000000000000600016800001600000000000005000020000000000000ac00012000001200000000000054000060000400000000000014800001400001c0000000000009c0004c0000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000094000060000000000000a00002000000000000240000001000118000000000000200000c000440000000000000084000400001f0000000000001e0000e800000e0000000000000100006c0000000000006800032000003000000000000002000170000b0000000000000a80⟩
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
private def keys180 : Keys := ⟨21,8,0x2aa39d66679da22b9d66a361a267612a2b61a2a3252a6725662b25721f91ae1f55361f194e8b911213918a8b554e1355128b198a13195a43859643491e430d⟩
private def rows180 : List Rule := [
  .pool ⟨19,2,[19,2],[],31,0x121d47b6⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],31,0x121d47b6⟩,
  .pool ⟨31,20,[31,2,5,17],[3,7,11,13,19],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,3,[31,3],[2],481,0x143002244080080620201001400c080100040080244112002208002800108420005000411001220890040080020040c00a0020101180400408910030a⟩,
  .pool ⟨19,2,[19,2],[],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩,
  .pool ⟨37,14,[37,2,7],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨37,12,[37,2,3],[5,7,11],61,0x1ffffffffffffffe⟩,
  .pool ⟨37,29,[37,17,23,29],[2,3,5,7,11,13,19],1267,0x42a043140f048c0cc11080041f04401c48f524103e3ad0886044138b0abc4102401b1414e18080aa00036420499226098372004084a14114343410528884032484986020000600840024208e2c643402c263471042400210060000406192124c021114a082c2c2882852102004ec1906449920426c000550101872828d80240823d50d1c82206110b5c7c0824af12380220f820010883303120f028c20542⟩,
  .pool ⟨19,2,[19,2],[],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],259,0x30a92334e3d1b04a00d110ac04ae5a20abb2408dbc2e750bf2cf07010c31b2a72⟩,
  .pool ⟨37,29,[37,17,23,29],[2,3,5,7,11,13,19],1209,0x1b2832512930d90c225929028a48069121209b49220804320221960045a6190c205960161b6982092024020404d129201160201a08b44040809a61b04a4d068024009a08a41008b04b28b20b4134534834402094416400900582c948361964040808b44160101a2012522c808100901241065b61a01a6810c261968801a61101308041124b6412122580494502526910c26c32522930536⟩,
  .pool ⟨37,12,[37,2,3],[5,7,11],1705,0x1ef2a9672308b1ad61685242280e6288a01ca640d8319061720443a1e433564225004a8631a084529e01284a1810e50ce8200095952e301aa18168298ce4906420d81500873244f52c0e3052548188224ee0014d221086340a410c17a5894392a3146001401319ca08d837b06c414e63200a0018a315270a4697a0c20940b1842112ca001dc9104604a92831c0d2bc89338402a06c1098249cc6505a06156031d2a6a400105cc29c2061485201e5288416318548029109ab309e1708813a1826306c0994e0144519c05109285a1ad63443139a553de⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],275,0x688090048210002084080200010008108060108100080004010210400084120090116⟩,
  .pool ⟨37,12,[37,2,3],[5,7,11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨19,2,[19,2],[],275,0x688090048210002084080200010008108060108100080004010210400084120090116⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .prime 19,
  .pool ⟨19,9,[19,3],[2,5,7],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .prime 37,
  .pool ⟨19,8,[19,2],[3,5,7],31,0x121d47b6⟩,
  .pool ⟨19,9,[19,3],[2,5,7],427,0x54419250004488602030c2014002001403c28008015210980224000244019084a80100143c02800400280430c04061122000a49822a⟩,
  .pool ⟨19,9,[19,3],[2,5,7],775,0x100028c003000000020a4090000a0000240000100000000000402000200008221420018040000000900008200000000000000a010000000004100000420000000208000008001000000008800030000002000000000a0210020000000808020a⟩,
  .pool ⟨19,9,[19,3],[2,5,7],61,0x1713e6940a59f23a⟩,
  .pool ⟨19,8,[19,2],[3,5,7],275,0x688090048210002084080200010008108060108100080004010210400084120090116⟩,
  .pool ⟨19,9,[19,3],[2,5,7],1147,0x51c01f9420016dc9a481550046104224240d32a9cd9c88848613008404c750434608a0081503600044503102284e118a4683c020a9874ec0b08a1844980914a4d942c02801e803108c017801403429b252890192218510d0372e1950403c16251887214408c0a220006c0a810051062c20ae3202100c861211139b3954cb0242442086200aa812593b6800429f8038a⟩,
  .pool ⟨19,9,[19,3],[2,5,7],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨19,8,[19,2],[3,5,7],481,0x1a206404e0801082a00200100802002360000020000018000200002014503028a010000100006000001000001b10010040200100150420041c8098116⟩,
  .pool ⟨19,8,[19,2],[3,5,7],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,9,[19,3],[2,5,7],671,0x50401010000040600000c00000240000004014020012200004000000820090001800001000000202010000804040000008000018000900410000002000044800402802000000240000030000060200000808020a⟩,
  .pool ⟨19,8,[19,2],[3,5,7],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,18,[19,2,3,17],[5,7,11,13],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,14,[19,2,7],[3,5,11,13],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩,
  .pool ⟨19,5,[19,5],[2,3],25,0x1394a73⟩,
  .pool ⟨31,7,[31,7],[2,3,5],181,0x11e0049dc628b42426480880440499090b4518ee4801e2⟩,
  .pool ⟨19,14,[19,2,7],[3,5,11,13],31,0x121d47b6⟩,
  .pool ⟨19,5,[19,5],[2,3],259,0x800014419080000001000400040000038040842c020000128305010420a0062⟩,
  .pool ⟨31,8,[31,2],[3,5,7],247,0x12080090000082000000140481080114004000000621016080021180050316⟩,
  .pool ⟨19,5,[19,5],[2,3],181,0x11e0049dc628b42426480880440499090b4518ee4801e2⟩,
  .pool ⟨19,5,[19,5],[2,3],31,0x121d47b6⟩,
  .pool ⟨19,14,[19,2,7],[3,5,11,13],481,0x1a60e406f08054a3a952005088d2202b63088820000098030303887034513228b038470303006400001044431b50112c4428012a5714a8043d809c196⟩,
  .pool ⟨31,22,[31,2,11,17],[3,5,7,13,19],665,0x1a3438806b524104a7389c70840c109270a82b130a90a9465080038008035820a8032244362c4939026319027248d1b089130054106b0040070004298a542543235054392420c08438e4739482092b580470b16⟩,
  .pool ⟨19,5,[19,5],[2,3],175,0x441090c0280233100510c24308a008cc401403090822⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],481,0x1a60e406f08054a3a952005088d2202b63088820000098030303887034513228b038470303006400001044431b50112c4428012a5714a8043d809c196⟩,
  .pool ⟨31,10,[31,2,5],[3,7],481,0x1fba6e34e2a13996a02730197b0f08f3604424ad7c451b0cba2c06a81652fd29a05580d174c36288fad490881b3c43c37a60339015a672151cb1d977e⟩,
  .pool ⟨31,10,[31,2,5],[3,7],399,0x100300044a0114106120c80006122102512d060904a0d14504102816490802410d32120db24069009344348905a6132536⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],703,0x16284d9071f687047b12ab2c803a01253a8e5358d88e4cb581011a9d01171c770a9cc4b9375f37d4a380d0f960b4de32d412041342dcc2a71147176f06a57f7e10cd86e4e4258e835b7b23fe4b2aa321dd1e9011f645eb96⟩,
  .pool ⟨19,5,[19,5],[2,3],61,0x1713e6940a59f23a⟩]
private def step180 : Stage := ⟨cfg,60,3,keys60,keys180,rows180,7,0x2a46a519f54a552346a551f548d52352a5523548cfa352a97a33e8d4af52bd1a33ebd4af46bd1a93ebd1af46a51a95e9d62d50b539f4eb162d4eb53a84eb0fad4eb13a85ab0fa746a50a9428d0a33ea50a3428d4a33e850a3528d4a13e8519f428d0a3568d721428cfa35685721468cfa156851a146b90a3528d4a13e851a352854a1468519f52851a146a519f427d3a34e8d5a35c9d3a33e8d5a75c9d1a33e9d5a7469d1ae5a9d427507d61f4e9d42d507d39f4eb142d4e7d3a84eb0faa46a519f547d52346a551f548d5233ea5523548cfa33ea919f4ead3a34e8cf9f4e8d3a3568cfa74e8cfa3569cfa7468d2aa3ea91aa467d2aa46a919f467d52a469519f547d523467d21f488d223527d223488cfa352912233e8cfa452911a1467d19f42a50a3467d09f428d0a3527d0a3428cfa352853a844a0fa73e9d128449cfa7509d11f449d427507d11f4e8cfa63e911a44694fa6469119f4695226467d19f48952234485021407d01f4285022407d09f4281022427d0a04280f942e44b912844a172e44a11285ca172244a17285c8972250b912844a17285c891285ca17225c894285c89722508942e5c8942250b942e448942e50b912e44a142e44b912844a172250b942e44b912850b912e44a11285cb912844a17285c8942e44b912844a172e44a11285ca172244a17285c89722508942e50b912e44a142e44b912844a172e44a11285ca172250b912e44a11285cb912844a17285c891285ca17225c8942e44f113c5cf172244f173c5c8972278f17225c89e2278b91285ca17225c894285c89722508942e5c8942250b942e448942450e913a44a142444e912844a1d2444a112874a1d2244a17285c8972250a17225c8942250b9722508942e50b912250b1426449112650b112644a112648b112844a1326488932444a912844a1324449912854a132244992285489322509912844997285c891284c997225c894284c897224c8942e688932270d1b26448933470d112644d933444d113844d932250d142644d112650d112644a112668d112844a1326688972250894264cb912250b942644b912650b912644a11265c8932450c912644a132444c912844a1324449912864a13224cb912e44a11284cb912644a17284c891265ca17224c8942e44c11304c9972244c17304c897224cc17224c898224cb9322508932450b1122509932444b112850991244499128588942a5099124449942a4499128449922a44a11284c99222001810604001000c1810004003000c081000c003020c080123880620248091038809202430910408091c24310104049013104c32108809130484020248097ef88092025e89784020a0228084021050a02100841410501021050414045010804006002c0870200006022c080020038602000801600381122808a02240891428089022450914040891424501140448b02240891825d8102245891805d011224581180448112e44b820208092025bb620248091025a902025a091041990120c0800200180060408006001810604000060418100040031a3c30f103470d1e3c30d103478d1e3830d1e347881e386810008002020808000080820200080040808002001000404501120448a1228081122848a0228089122808a0224089140448c12c808b022448c02c4089022458c02240896024581122808a022408914280890224509140408914245011404484101438508142061014205081c2060a14208081c2860a101810004003000c081000c003020c080000c08302000800600101040400100081010004002000808100080020208080⟩
set_option maxHeartbeats 5000000 in
private theorem valid180 : ∀ r ∈ rows180, Valid cfg 180 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_40 : ∀ i ∈ List.range' 40 15, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
private theorem run180 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 180 a b c keys180 := by
  apply refine step180 h bad (by decide) (by decide) valid180 _ old
  intro i hi
  change i < 55 at hi
  by_cases h0 : i < 40
  · exact test180_0 i (by simp only [List.mem_range'_1]; omega)
  exact test180_40 i (by simp only [List.mem_range'_1]; omega)
private def keys360 : Keys := ⟨6,9,0x24c1fa2c983e91b134e12ae0fc26c4d32aab83e55⟩
private def rows360 : List Rule := [
  .pool ⟨37,14,[37,2,7],[3,5,11,13],1353,0x1a61a41a61805b20a04a45148a6d24022510926084994c825320a6d860800060348808021860b04301924a4882d34424c868240220a2da40a01300041145b01128921200061001340b05a4122c04d06d100b0924932492434022d82c80d120968340b20021800121245220368a2080032014096d14110090584c908b2d044949260308341861004044b0180004186d94132904ca6484192422910092d944a2894814136806196096196⟩,
  .pool ⟨31,25,[31,5,17,23],[2,3,7,11,13,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨37,12,[37,2,3],[5,7,11],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  .pool ⟨37,12,[37,2,3],[5,7,11],511,0x140004221001411244808020051022046020c60209000c1010950042213001808106528000d00a028040911c2050404b0030002158322410071090d135e⟩,
  .pool ⟨41,28,[41,2,7,17,23],[3,5,11,13,19],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,25,[41,5,17,23],[2,3,7,11,13,19],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  .pool ⟨37,12,[37,2,3],[5,7,11],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨31,25,[31,5,17,23],[2,3,7,11,13,19],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨73,22,[73,2,11,17],[3,5,7,13,19],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨41,23,[41,17,23],[2,3,5,7,11,13,19],543,0x5321a0d028800b64008849045049b2d20410184d12182502526112092da0db61941344300068024b2530912d10c32504c36596902024d14d24ca6d900b6ca2d06832116⟩,
  .pool ⟨37,29,[37,17,23,29],[2,3,5,7,11,13,19],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨37,29,[37,17,23,29],[2,3,5,7,11,13,19],803,0x268338a1b06726fc40ab8604a3c4501f87ae46053a967bcb31a01bc29cae8d012a0023118682a6d8b15338d611205d34a0a136af8d305d37694c33172648abc8e3733feab5f4a8a46a425fa33242096835b990a0e05f59c32de9e08f9c01b09f07aa3369a⟩,
  .pool ⟨41,23,[41,17,23],[2,3,5,7,11,13,19],185,0x1a3539c82a1e921022601ae31d6019102125e1504e72b16⟩]
private def step360 : Stage := ⟨cfg,180,2,keys180,keys360,rows360,5,0x1318213182000000000052d2a52d2a188431884300000000005256a5256a318c6318c600000000004a9494a9493a2473a22781cef71ced09ce109ce12908529085318c6318c6214a4214a42884528845214a4214a410c6210c62084210842100000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid360 : ∀ r ∈ rows360, Valid cfg 360 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test360_0 : ∀ i ∈ List.range' 0 21, ∀ x y z : Fin 2, Test step360 i x y z := by decide +kernel
private theorem run360 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 180 a b c keys180) : Match 360 a b c keys360 := by
  apply refine step360 h bad (by decide) (by decide) valid360 _ old
  intro i hi
  change i < 21 at hi
  exact test360_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],511,0x802100110042c00080000c20200000100000008108011140005800000010041400800240b4580030000a00a01480c200c0000048800190800812286840122⟩]
private def step720 : Stage := ⟨cfg,360,2,keys360,keys720,rows720,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 6, ∀ x y z : Fin 2, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 360 a b c keys360) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 6 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+6=2^a*3^b*17^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=1 ∧ b%12=1 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h180 := run180 h bad h60
  have h360 := run360 h bad h180
  have h720 := run720 h bad h360
  obtain ⟨i,hi,_⟩ := h720
  exact Nat.not_lt_zero i hi
end D6

namespace D7
private def cfg : Config := ⟨7,7,17,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x49085⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x2c82c82c820820820820b20d20b2082082082c82c82c820820820820c20b20b2082082082c82c82c820820820820b20b20a208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨3,6,0x121028540529⟩
private def rows60 : List Rule := [
  .pool ⟨31,10,[31,2,5],[3,7],100,0x119171991719d171193711d37⟩,
  .div 11,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],117,0x509d474f8985b8c7bb134b559f7e⟩,
  .pool ⟨31,24,[31,2,3,17,19,23],[5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],819,0x4000420002800004000000020000020000100000000400002000002000000000000000004080000000010000000082000400000000020004100000000800000000102000000000000000004000004000020000000080000400000400000002000014000420002⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0x21111110111111817111111511411111161311111121111110⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨4,7,0xa2880c854014ca02829⟩
private def rows120 : List Rule := [
  .pool ⟨41,14,[41,2,7],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,14,[41,2,7],[3,5,11,13],31,0x121d47b6⟩,
  .pool ⟨31,24,[31,2,3,17,19,23],[5,7,11,13],73,0x1fffffffffffffffffe⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0x2911a8118⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 3 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨8,8,0x8cdd0014dd008c6500146500c8a10050a100c829005029⟩
private def rows240 : List Rule := [
  .pool ⟨61,38,[61,2,19,23,29,37],[3,5,7,11,13,17,31],272,0x353b1d7511d31f9189b9533dbbf7d913f2717f593115975bd5cdfd1779fbb39d57b6⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,4,0x87654321⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 4 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨19,3,[19,3],[2],85,0x20200ca0300000829028a⟩,
  .pool ⟨19,17,[19],[2,3,5,7,11,13,17],3,0x2⟩,
  .prime 19,
  .pool ⟨19,3,[19,3],[2],27,0x8060b⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,2,0xe4925e4922792527924927a49277924a7924⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 8 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+7=7^a*17^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D7

namespace D8
private def cfg : Config := ⟨8,2,17,1,3,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x8b047⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .div 7,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x460420422102102100810c10814084084080420450422102102100810810c14084084080420420442102102100c1081081408408408⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨5,6,0xe3b02cbc08230145c0a2b⟩
private def rows60 : List Rule := [
  .pool ⟨31,11,[31,11],[2,3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .div 11,
  .prime 31,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],549,0x1a60a00261041120a0084490094824032014120184820800120982106094002924004c800925000a41821064120004104860120a01300904a4024884014122082190014196⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,3,[31,3],[2],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0xa1111191111181111171111154111116111113111112111110⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨6,7,0x68d60342f0142980a05c028ce0142b⟩
private def rows120 : List Rule := [
  .pool ⟨41,16,[41,2],[3,5,7,11,13],31,0x121d47b6⟩,
  .pool ⟨31,29,[31,19,23,29],[2,3,5,7,11,13,17],819,0xa00000000000000800240000200200005020841200a48200000208028000804008100020000344000300000000008200004000020100000020024000000000800200020004000020008848044000808100000004000240200100001840100008000a0c80002⟩,
  .pool ⟨31,29,[31,19,23,29],[2,3,5,7,11,13,17],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,29,[41,19,23,29],[2,3,5,7,11,13,17],51,0x21a0022996832⟩,
  .pool ⟨31,19,[31,19],[2,3,5,7,11,13,17],205,0x294000800401024204a020021084a42802420485014a1294002⟩,
  .pool ⟨31,19,[31,19],[2,3,5,7,11,13,17],451,0x20008000000000000820001000010080000e8000008000000800048010002000040008820044025212040c00000008800000083080022⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,4,0x5454b3a3212190800706⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 5, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 5 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨24,8,0xe0e30068e300e06b00686b00e0a70068a700e02f00682f00c8cb0050cb00c85300505300c88f00508f00c81700501700a0df0028df00a06700286700a0a30028a300a02b00282b⟩
private def rows240 : List Rule := [
  ]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,5,0xbdab49ca307b9ac5a928398a418820⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 6, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 6 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨19,12,[19,2,3],[5,7,11],45,0x55898f135e⟩,
  .pool ⟨19,17,[19],[2,3,5,7,11,13,17],3,0x2⟩,
  .pool ⟨19,14,[19,2,7],[3,5,11,13],481,0x1a60e406f08054a3a952005088d2202b63088820000098030303887034513228b038470303006400001044431b50112c4428012a5714a8043d809c196⟩,
  .pool ⟨19,5,[19,5],[2,3],31,0x121d47b6⟩,
  .pool ⟨19,6,[19,2,3],[5],45,0x55898f135e⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],17,0x1a316⟩,
  .pool ⟨19,5,[19,5],[2,3],25,0x1394a73⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,3,0xb34d759acb34d759669acd759669aeb2cd669aeb2cd35d66b2cd357658e3b1d7658e3aecb1d8e3aecb1c75d8ecb1c75d9638ec75d96308a20844208a208411442208411441082211441082288211082288⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 24, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 24 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+8=2^a*17^b) (ha : 0<a) (hb : 0<b) : a%12=3 ∧ b%12=0 := by
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
end D8

namespace D9
private def cfg : Config := ⟨9,3,17,1,2,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x68⟩
private def rows12 : List Rule := [
  .div 5,
  .div 13,
  .div 7,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x8010010002001002200400400080100080010010008001002002400400200040080080010008010002002003400200400080080040⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨1,6,0x488⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],560,0xf5b1c723d8153c0d59d0a119ad5210d31141519254912b714e5331243910738d831b1ab1b183639c1138491994e51da91254931505119610956b310a17356079503789c71b5e⟩,
  .pool ⟨61,6,[61,2,3],[5],112,0x1131950bd9b33a5571d14f9db77e⟩,
  .pool ⟨31,4,[31,2],[3],112,0xd111410311034005811181051116⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x800000602008000028⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨0,7,0x0⟩
private def rows120 : List Rule := [
  .pool ⟨31,30,[31,2,3,5,17,19,23,29],[7,11,13],41,0x1fffffffffe⟩,
  .pool ⟨41,29,[41,17,19,23,29],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,1,0x6⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 1 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+9=3^a*17^b) (ha : 0<a) (hb : 0<b) : a%12=2 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  obtain ⟨i,hi,_⟩ := h120
  exact Nat.not_lt_zero i hi
end D9

namespace D10
private def cfg : Config := ⟨10,2,5,17,1,1,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨11,4,0xa7b47b819219677077a15415873273611⟩
private def rows12 : List Rule := [
  .div 7,
  .div 3,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x1012101012100101210101211010121010122101012101011e10101d1010012101012101101210101210010121010121101012101012210101210101121010121010012101012101010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010101012101012210101210101121010121010012101012101101210101210010121010121101012101012210101210101121010121010012101012101101c10101b1001012101012101010101010110101010101001010101010110101010101001010101010110101010101001010101010110101010101001010101010110101010101001010101010110101010101012101012101001210101210110121010121001012101012110101a101019210101210101121010121010012101012101101210101210010121010121101012101012210101210101010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010101210101210010121010121101012101012210101210101121010121010012101012101101210101210010121010121101012101012210101210101181010171010012101012101010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010101012101012210101210101121010121010012101012101101610101510010121010121101012101012210101210101121010121010012101012101101210101210010121010121010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010121010121010012101012101101210101210010121010121101012101012210101210101121010121010012101012101101210101210010121010121101014101013210101210101010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010010101010101101010101010⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨126,6,0x293ee2aefe878d67d7bb72c4aef7078f47d74372c8c79819e6c379e31b4896d80db7896150d860061b25578655501554c49b192480499b1e4267938de5ac6d9a5b4236d6a587236108184e955699572055cb124e649aabdf67f7487dd2deba9fac61eb1b77d2adf79f7ea4dfdb74c6ad37934f6ac74931de1c732bdd87f7c07df0deb31fae41eb9377f0adf01f7cc4df6374e4ad30134cc1d362b1f04c70071d6075b99a62351ea5174075419a68c5d10d45c945e37cd47f3b07cecde75139e0ddbb2b6c84db82b3f84cf2073d4ac381f0f81c36b7cf27f3387ccede799f9f24e70b76ceadb9936c2acf6933e61cfcab0c27c36870dec71aa5c7667118dc52c657a59763654a566a359d8164694d49936a04dab104664148d05e041⟩
private def rows60 : List Rule := [
  .div 11,
  .prime 31,
  .pool ⟨31,5,[31,5],[2,3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,5,[31,5],[2,3],1281,0x1b28221060300800a0002800020000032000000522000000002100000000002930010010100000886020000000400000000020080000000000010000100022082800000800000c000800000000021200b4012100000000004000c00000400000504110002000020000000000004010000000000800000010184400002020020032500000000002100000000112800000130000010000500014004030182110536⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],63,0x6880800180010116⟩,
  .pool ⟨31,3,[31,3],[2],9,0x9b⟩,
  .pool ⟨31,27,[31,3,17,19,23],[2,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,6,[31,2,3],[5],45,0x55898f135e⟩,
  .pool ⟨31,8,[31,2],[3,5,7],63,0x6880800180010116⟩,
  .pool ⟨31,9,[31,3],[2,5,7],9,0x9b⟩,
  .pool ⟨31,2,[31,2],[],63,0x6880800180010116⟩,
  .pool ⟨61,27,[61,3,17,19,23],[2,5,7,11,13],45,0x55898f135e⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,8,0x8000000070000000a00000000000000008900000009000000000a000000880000000900000008000000000000000007000000000900000008000000070000000a00000087000000000700000000000000000a000000860000000900000008000000008500000009000000000000000008000000070000000a00000000000008000000070000000a0000000b00000009000000000a0000000000000000840000000900000008000000070000000009000000080000000000000000070000000a0000008300000000070000000a0000008200000000000000000900000008000000008100000009000000080000000700000000000000000a0000000080000000050000007f0000007e00000004000000007d00000000000000007c000000040000007b0000000500000000040000007a0000000000000000050000007900000078000000000500000077000000760000000000000000040000007500000000740000000400000073000000050000000000000000720071000000050000000000000000700000006f00000004000000006e0000006d0000000400000000000000006c0000000500000000040000006b000000050000006a00000000000000006900000000050000006800000067000000040000006600000000650000000000000000040000006400000005000000060000000000020000006300000062000000000000000001000000610000000060000000010000005f0000000200000000000000005e000000005d0000005c0000005b0000005a0000000100000000590000000000000000580000000100000057000000020000000001000000560000000000000000020000005500000054000000000000020000005300000052000000010000005100000000500000000000000000010000004f000000020000004e000000004d0000004c00000000000000004b0000004a0000000100000000490000004800000001000000000000000047000000460000000001000000450000000300000044000000000000000043000009000000080000000700000000000000000a0000004200000000070000000a0000004100000009000000000000000008000000000b0000000900000008000000070000000a00000000080000000000000000070000000a0000004000000009000000000a0000003f00000000000000000900000008000000070000000000000900000008000000070000000a0000003e000000000700000000000000000a0000003d0000000900000008000000003c00000009000000000000000008000000070000000a0000000008000000070000000a00000000000000003b00000009000000000a0000003a00000009000000080000000000000000073900000000000000000400000038000000050000003700000000360000000500000000000000000600000035000000040000000034000000330000000400000000000000003200000005000000000400000031000000050000003000000000000000002f00000000050000002e0000002d000000040000002c0000000000002b000000040000002a000000000000000005000000290000000028000000050000002700000026000000000000000004000000002500000024000000040000002300000005000000000400000000000000002200000005000000210000002000000000050000001f00000000000000001e000000040000001d000000001c0000001b0000001a0000000000000000190000000100000000180000001700000001000000160000000000000000030000000001000000150000000200000014000000130000000002000000000000000012000000110000000100000010000000000f0000000100000000000000000e0000000d0000000c0000⟩
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
private def keys180 : Keys := ⟨157,8,0x2aa3afa22baf66a3732a2b73a2a337662b373697af729773ae97371207af4e07738a07378a73a31273674e732b6697a3a297672a972b7e7fa34207a37e076706072b06739742735b7e731f9697975a97971e5b975a1f9796975b1e975b5a5b5b961f5b5a971f1e971f965b1f1e1f1f2a4f97664f5ba24f1f36738b72378b72734fae374fae73133637137e2b8b062b4f422b135a4f8b964f4f1e4f1312137f4e13438a130784a3af482baf0c2baf0ca373842b73482b7348a337842b370c2b37185baf545b73905b37a87faf6c07af307f73a807736c7f373007376c37a3a8376730372b485ba3845b670c5b2b247fa3607f679c7f2b6073979c37979c735b24375b24731f60371f3c979778975b00971f0c139748135b84131f18734f90371324a3133c4f4f00131390a37f542b7f18a343902b4354a307182b07304f7f6c137f6c4f43a81343a84f07301307007f7f3c7f43787f0796a9a97219a936916d0685a912a99d4e6d9d4ea9618a6d618aa925126d255a619d9661611e612536859d728561ae85258a61911261554e61196685912a8591a24991a285556685552a4955a285192a8519664919ae3d91363d55723d194225857e254906250da2a9792aa93d66a9017e197906193d4219015a3d79963d3d1e3d01⟩
private def rows180 : List Rule := [
  .pool ⟨19,14,[19,2,7],[3,5,11,13],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩,
  .pool ⟨37,20,[37,2,5,17],[3,7,11,13,19],61,0x1ffffffffffffffe⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],481,0x1a206404e0801082a00200100802002360000020000018000200002014503028a010000100006000001000001b10010040200100150420041c8098116⟩,
  .pool ⟨37,11,[37,11],[2,3,5,7],793,0x1034000001000000202012300c0000100400108000004008000000100002000040000011002080000001040000004000080000400008000000820000000410022000000800010000200000004008000004200080200000c031201010000002000000b02⟩,
  .pool ⟨31,5,[31,5],[2,3],703,0x54d100f940c4050089934adc310008f52318201106001009a08c8484e02e108861d0595202740c44a2824d0810b2414522302e404a9a0b86110874072121310590080060880418c4af10008c3b52c99100a023029f008b2a⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],31,0x121d47b6⟩,
  .pool ⟨31,5,[31,5],[2,3],181,0x11e0049dc628b42426480880440499090b4518ee4801e2⟩,
  .pool ⟨19,14,[19,2,7],[3,5,11,13],31,0x121d47b6⟩,
  .pool ⟨31,23,[31,17,23],[2,3,5,7,11,13,19],1443,0x25800a08a21225361245a4c32510910484824190430d00802194086934d92c82030d26d10820186882c00904da20029b20a44809320b0110c00c004924104a20a0502800d20404802d32012da41a00324a41128b25349b0800032136d260041020a25308901968340021a2102ca4d16906d82d028b2892590496d865861360b20264148b20029a2804d22d80ca0c360a6100906032c02404100ca4432d82d041964241a48965264121048109101029308a28b4c12⟩,
  .pool ⟨37,11,[37,11],[2,3,5,7],181,0x1717e2151bcfb266b4947840878a4b59937cf62a11fa3a⟩,
  .pool ⟨61,41,[61,17,23,29,41],[2,3,5,7,11,13,19,31,37],1147,0x349a3c32b10eb4b064dcbf02718e70b7d6df510a3410af97c4ec2f0194be3504499758548829e933f08be8ab361110800a9a060ea601cfa5399a3157b0982fdf8d2c39d49928989a6e6a366d4634b0e040ae6f01571a6634a087f9a8f17a6affee377932ac80ef033286aeed5651665de5382d63d0bc8dc100af7d3a765049402f10e719f02c0d9b2d28f5233c3a6d2⟩,
  .pool ⟨37,11,[37,11],[2,3,5,7],61,0x1434026619900b0a⟩,
  .pool ⟨37,20,[37,2,5,17],[3,7,11,13,19],1209,0x1b2832512930d90c225929028a48069121209b49220804320221960045a6190c205960161b6982092024020404d129201160201a08b44040809a61b04a4d068024009a08a41008b04b28b20b4134534834402094416400900582c948361964040808b44160101a2012522c808100901241065b61a01a6810c261968801a61101308041124b6412122580494502526910c26c32522930536⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,14,[19,2,7],[3,5,11,13],481,0x1a60e406f08054a3a952005088d2202b63088820000098030303887034513228b038470303006400001044431b50112c4428012a5714a8043d809c196⟩,
  .pool ⟨37,20,[37,2,5,17],[3,7,11,13,19],181,0x1ffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨61,27,[61,3,17,23],[2,5,7,11,13,19],135,0x116063c45780ab131626bc055898f135e⟩,
  .pool ⟨61,27,[61,3,17,23],[2,5,7,11,13,19],351,0x5040c31002809186240540030c082a8006188054048c31202a01186001541030c002a0246189014008c3020a⟩,
  .pool ⟨61,27,[61,3,17,23],[2,5,7,11,13,19],133,0x1430126400024e0721381c90000992030a⟩,
  .pool ⟨31,5,[31,5],[2,3],399,0x100300044a0114106120c80006122102512d060904a0d14504102816490802410d32120db24069009344348905a6132536⟩,
  .pool ⟨19,17,[19,17],[2,3,5,7,11,13],9,0x102⟩,
  .pool ⟨19,2,[19,2],[],31,0x121d47b6⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],93,0x124c345b00221100368b0c92⟩,
  .pool ⟨19,2,[19,2],[],793,0x1a207404ac8001c266c20040150e8421e4a6842400418010088d42e254d5201af08320f711c020904445844e10151804470303888062a021c886888824100e23bc13043d6012aca91d0ac440200608009085949e1085c2a008010d990e0004d480b8116⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],185,0x2900000480214212802020424280a00840429025294802⟩,
  .pool ⟨19,2,[19,2],[],481,0x1a206404e0801082a00200100802002360000020000018000200002014503028a010000100006000001000001b10010040200100150420041c8098116⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],217,0x102e4c05010003003610e1a232848531161c21b00300020280c9d02⟩,
  .pool ⟨19,2,[19,2],[],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,2,[19,2],[],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,2,[19,2],[],819,0x6880904082102000800802004800000090000080000800002084100004000000820000000100900000000080004000000804806012010000002000100000000090080000000410000002000082104000010000100000900000012004010010004084102090116⟩,
  .prime 37,
  .pool ⟨19,2,[19,2],[],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,7,[19,7],[2,3,5],31,0x121d47b6⟩,
  .pool ⟨19,8,[19,2],[3,5,7],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,15,[19,3,5],[2,7,11,13],481,0x1fba6e34e2a13996a02730197b0f08f3604424ad7c451b0cba2c06a81652fd29a05580d174c36288fad490881b3c43c37a60339015a672151cb1d977e⟩,
  .pool ⟨19,15,[19,3,5],[2,7,11,13],693,0x1018444a15858083605d8b11cb15065478a055cacf0728584bc7695d8904b0c990ab422504c99b866396b844a873018f15972ec0f8b30c9b9f124941832952964a0d137728c525749911c6835f0b3e55a1f16f1db77e⟩,
  .pool ⟨19,8,[19,2],[3,5,7],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩,
  .pool ⟨19,15,[19,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨19,8,[19,2],[3,5,7],819,0x6880904082102000800802004800000090000080000800002084100004000000820000000100900000000080004000000804806012010000002000100000000090080000000410000002000082104000010000100000900000012004010010004084102090116⟩,
  .pool ⟨19,8,[19,2],[3,5,7],481,0x1a206404e0801082a00200100802002360000020000018000200002014503028a010000100006000001000001b10010040200100150420041c8098116⟩,
  .pool ⟨19,15,[19,3,5],[2,7,11,13],427,0x54419250004488602030c2014002001403c28008015210980224000244019084a80100143c02800400280430c04061122000a49822a⟩,
  .pool ⟨19,8,[19,2],[3,5,7],793,0x1a207404ac8001c266c20040150e8421e4a6842400418010088d42e254d5201af08320f711c020904445844e10151804470303888062a021c886888824100e23bc13043d6012aca91d0ac440200608009085949e1085c2a008010d990e0004d480b8116⟩,
  .pool ⟨19,8,[19,2],[3,5,7],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨31,21,[31,3,7,17],[2,5,11,13,19],37,0x1ffffffffe⟩,
  .pool ⟨37,9,[37,3],[2,5,7],61,0x1434026619900b0a⟩,
  .pool ⟨37,9,[37,3],[2,5,7],27,0x8060b⟩,
  .pool ⟨31,5,[31,5],[2,3],259,0x30a92334e3d1b04a00d110ac04ae5a20abb2408dbc2e750bf2cf07010c31b2a72⟩,
  .pool ⟨37,9,[37,3],[2,5,7],181,0x1717e2151bcfb266b4947840878a4b59937cf62a11fa3a⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],793,0x1a207404ac8001c266c20040150e8421e4a6842400418010088d42e254d5201af08320f711c020904445844e10151804470303888062a021c886888824100e23bc13043d6012aca91d0ac440200608009085949e1085c2a008010d990e0004d480b8116⟩,
  .pool ⟨37,9,[37,3],[2,5,7],671,0x44000000000000000000000000000000800000000000000021000200000000001000000810010000000000004000000000200000800000020000040000200800020a⟩,
  .pool ⟨61,20,[61,2,5,17],[3,7,11,13,19],181,0x1ffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨37,9,[37,3],[2,5,7],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨37,36,[37,2,3,17,23,29],[5,7,11,13,19,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,36,[61,2,3,17,23,29],[5,7,11,13,19,31],1463,0x425082205d50c081122a62200a1549443064c1d892c180805408c063661c231210a042825b053e6849618f1438541d01036744195a0112d4a687906a5180e42191201cc4024189048338f51261aac39d121832806d5bb56200f91323003f20502001e692a7124038226985102034da264d939c46e9705388d23428541a8244853d2425d1102f5e035441c300690d21024d01b0ad5aa73431839028dc8f50f87a6424c42c50f0d945038f3328a8b336c4d4015ab87135e⟩,
  .pool ⟨181,27,[181,3,17,23],[2,5,7,11,13,19],135,0x116063c45780ab131626bc055898f135e⟩,
  .pool ⟨181,27,[181,3,17,23],[2,5,7,11,13,19],999,0x14123143590f46610f729755be24386d4604bb3e1c833e77268fec09745ac429e6753d1475cecf5ff802a1910a5ae87a3b0c7995baadb101d36a3427d9f06459d3a93c7f624ba256616f23a1eca1af76fabfc0150c8c52d74351d863dcadd16f890e9b11a13ec78722cf9dc9e3db125516b30b799d4f651d7bb7d7fe⟩]
private def step180 : Stage := ⟨cfg,60,3,keys60,keys180,rows180,8,0x2326242624232423252624232423262325242423262326242524232328272827232723282827232723282328272723282328272827232524232423262326242423252326242624232325242624232423262a232b232b2d2b2d23232b2a2b2d232d232b2b2a232d232b232b2d2d232623262a252d2323262d262a232d2325262d232a232623252d272328232827282723232827282723272328282723272328232827232827282723272328282723272328232827272328232827282723232829282a232a23282829232a232823282a29232823282a282a2325242324232623252424232523262425242323252426242324232517162121181718211616211718172121161821171617211816182117211e161e21211716211e171e21161716211e172121161e1621171f1621211e1f1e211616211f1e1f2121161e211f161f211e161e21171621211a171a21161621171a172121161a21171617211a161a21161a21211d161d211a1a21161d1621211a1d21161a16211d1a1d2116211718172121161821171617211816182117162121181718211616182121171617211818211617162121181721161816211718172121171617211a161a21171621211a171a21161621171a172121161a1a2116221621211a1b21161a1621221a1b21161a212122161b211a1a2116171621211a1721161a1621171a1721161a2121171617211a1a1b2121161a1621221b211a161a21212216211a1b1a21162216212116181621171817211618212117161721181821161716212118171f1621211a1f1a211616211f1a1f2121161a211f161f211a161a21172118161821211716211817182116171621181721211618162117161a2121171617211a1a2116171621211a1721161a1621171a17211618171817161716181817161716181618171716181618171817161e171617161e161e1717161e161e171e1716161e171e171617161e1e20161b161e161e2020161e161e1b1e2016161e201e1b1620161e1a171617161c161a1717161a161c171a1716161a171c171617161a1a191619161a161c1b19161a161a191c1b16161a191a19161b161c17161816181718171616181718171617161818171617161816181717161816181718171616181718171617161818171617161816181717161a161c171a1716161a171c171617161a1a171617161c161a17161a1f1a1f161f161c1a1f161f161a161c1f1f161a161a1f1c1f16161e171e171617161e1e171617161e161e1717161e161e171e1716161e1d1e1d161d161e1e1d161d161e161e1d1d161e161e1d1e1d16161817181716171618181716171618161817171618161817181716161e1f1e1f161f161e1e1f161f161e161e1f1f161e161e1f1e1f16181716171618161817171618161817181716161817181716171618000fd70f0c00d6000f0fd5000c000f000fd4d3000f000f0c0fd2000806d1060d080c080606d0080d080608060ccf080608060d060c080609080908060806ce09080608060906cd08080609060908cc0806060c08cb080608060d0c08060806ca060d0808060c06c9080d080606c808090806080609c708060806090609080806c6060908090806c5000f000f0c0fc400000f3a0f0c00c3000f0f39000c000f000fc20908060806c106090808060906c008090806060908bf0806080609071006100605060515100607060510051506060710051006150605bebd021002bc03bb10ba02b902b810b7100302b6b5b410021003b30a08060806b2060d0808060a06b1080d0806060a08b0080608060d0c000f000faf0fae00000f0c0fad00ac000f0f0c00ab000f000faa08060d060c08a90806060d080c08060806a80d080608060c06a70808060906a608090806060908a508060806090908060806a40609080806090609083708060609080908060806370908060806090637080e0c1037380e100ea30c100e380e370ea210100e0c0e3738a1100e060d080c08060806370d080608060c06370808060d060c08370806a0100f100f2f0f9f9e100f9d0f2f109c9b0f0f9a1030100f990f982e0806080697062f0808062e0696082f0806062e0895080608063094080608062f069308080692062f0891080606900830080608068f30080608062e068e0808062f062e088d0806062f082e080608068c08060b068b08300806060b088a080608062f0b0806080689062f08000e880e30000b000e0e87002f000e000e0b86000e000e2f0e0b00080636068508840806063008830806080682360806080681068008000607063100310006060700310006000631070006000631063100037f003500020033347e000300023533300000037d0235003400330632082e080608067c30080608062e067b08080632062e087a08060f2f1012140f100f132f100f140f790f1210100f300f131478100f0613082f080608062e12080608062f062e080806770630082e08062f080608061206130808062f067608120806063008130806080675071006100631060715100607063110071506060710311006150607740806080630067308080672062f087108060670082f080608066f30000f000f6e0f6d00000f2f0f6c006b000f0f2f006a000f000f690806680630082e08060667082f080608062e66080608062f062e082d232823282a282d2323282d282a232d2328282d232a232823282d242325232624262423232524262423242326252423242326232624282723272328232827272328232827282723232827282723272328282723272328232827272328232827282723232827282723272328232b2a2b2c232a232b2b2a232c232b232b2a2a232b232b2c2b2a23252a232a23252326292a232523252a26292323252a252a23292326262423242325232524242326232524252423232624252423242325232827282723272328282723272328232827272328232827282723232524262423242325252423242326232524242325232624252423161e21211d161d211e1e21161d1621211e1d21161e16211d1e1d212117161721181618211716212118171821161621171817212116181e172121161e16211717211e161e21211716211e171e211617162118211617162121181721161816211718172116182121171617211821161e16211f1e1f21161e21211f161f211e1e21161f1621211e1f21161e1621171e1721161e2121171617211e1e2116171621211e171b211e161e21212216211e1b1e21162216211e1b2121161e162122161821211716172118182116171621211817211618162117181721211817182116171621181721211618162117172118161821211716161a2121171617211a1a2116171621211a1721161a1621171a17211a1b2121161a1621221b211a161a21212216211a1b1a21162216211a172121161a16211717211a161a21211716211a171a2116171621211f161f211a161a211f1621211a1f1a211616211f1a1f2121161a18172121161816211717211816182121171621181718211617162120161a161a201c1b16161a201a20161b161c1a201620161a161c1b171618161817181716161817181716171618181716171618161817161c171a171617161a1c171617161a161a1717161c161a171a1716161817181716171618181716171618161817171618161817181716161a171c171617161a1a171617161c161a1717161a161c171a1716161a1f1a1f161f161c1a1f161f161a161c1f1f161a161a1f1c1f161e171617161e161e1717161e161e171e1716161e171e171617161e1e1f161f161e161e1f1f161e161e1f1e1f16161e1f1e1f161f161e18171617161816181717161816181718171616181718171617161817161816181718171616181718171617161818171617161816181717161a161a171c1716161a171a171617161c1a171617161a161c171d161c161a1d1a1d16161c1d1a1d161d161a1c1d161d161a161a1d17161c161a171a1716161c171a171617161a1c171617161a161a17161a191c1b1619161a1a19161b161c161a1919161a161c1b1a191616181718171617161818171617161816181717161816181718171665080608060906090808061306090809080606120809080608060905100615060706071010060506071507100606051007150610060712100f100f0c0f6414100f630f0c1013140f0f13100c100f140f120806620611080c080606130811080608060c120806080611060c08000f610f600004000f0f5f005e000f000f045d000f000f5c0f040008060a065b080d0806060a085a080608060d0a0806080659060d080806580609080908060657080908060806095608060806090609080609085508060806090908060806540609080806090653080908060f525150100f100f0a4f4e0f100f4d0f0a104c0f4b0f4a100a100f06040849080608060d040806080648060d080806040647080d08060c000e000e0b0e4600000e0c0e0b0045000e0e0c000b000e000e440d080608060c060b0808060d060c080b0806060d080c080608060b09080608060b060908080609060b080908060609080b0806080609430806080601060a080806420601080a080606410801080608060a08060906090840080606090809080608063f090806080609063e08000605060700050006060500070006000605050006000607060500000304023d000100020304003c000200020104000300023b020100⟩
set_option maxHeartbeats 5000000 in
private theorem valid180 : ∀ r ∈ rows180, Valid cfg 180 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_40 : ∀ i ∈ List.range' 40 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_80 : ∀ i ∈ List.range' 80 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_120 : ∀ i ∈ List.range' 120 6, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
private theorem run180 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 180 a b c keys180 := by
  apply refine step180 h bad (by decide) (by decide) valid180 _ old
  intro i hi
  change i < 126 at hi
  by_cases h0 : i < 40
  · exact test180_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : i < 80
  · exact test180_40 i (by simp only [List.mem_range'_1]; omega)
  by_cases h80 : i < 120
  · exact test180_80 i (by simp only [List.mem_range'_1]; omega)
  exact test180_120 i (by simp only [List.mem_range'_1]; omega)
private def keys360 : Keys := ⟨106,9,0x54df938a9be731b25ec6364babe4d4b93c9a96738101e4f02039ce9497a5d292e972d43e1e5a8796cb54b6996a961f6907da6d20f87e944f81d289e4f6304e66c6099fe7157b1ce147639c55d5f3851abdf8dfb192057637e37d5e4815abd815793b0147276055ce6c0519ce70df93ce1be732455dd64851bac91571b92146375401e4ea8039ce413375c80feeb904cc6f203f8dde097a5bc12e970052da600a587c3127818624e4f480dd8e901b84e40c799c818e7f9040def208190d50c77baa026f75431c86a80990d504f5daa09e071831d763009aec60c7038c0260763576a212aed458ca9a8b1aba9d095753ac654a749d21a893a429d815762a4e54c56055d3093952619f4862b3e36c567d2130cf8da619f575b28aaeb667ca96ca2952d99f5744a8aae8967ca912a295225814559b028a8655cf1a2ab87b45573c522ae1ea446cf1848d9e255933c59b2678864b4f1969687b2d2d3c4f25a1e9e6943d78d287a3d⟩
private def rows360 : List Rule := [
  .pool ⟨41,2,[41,2],[],73,0x1a30280023100050316⟩,
  .pool ⟨41,18,[41,2,3,17],[5,7,11,13],297,0x1eb238356f103c88b6ac1c457bd646062de227911ed18189af7a88e0d5b444f023dab07135e⟩,
  .pool ⟨73,32,[73,2,17,23,29],[3,5,7,11,13,19,31],111,0x14122102590d06410d329345b6⟩,
  .pool ⟨31,23,[31,17,23],[2,3,5,7,11,13,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨31,23,[31,17,23],[2,3,5,7,11,13,19],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,31,[41,17,23,29],[2,3,5,7,11,13,19,31],285,0x1201b0c101105225a64104b21048021040140a0082100482134820996912822020c36012⟩,
  .pool ⟨41,31,[41,17,23,29],[2,3,5,7,11,13,19,31],73,0x1fffffffffffffffffe⟩,
  .prime 41,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],365,0x29000821008c301e30a8411208159900000201906461100030000200070008108800982808004420a10010b2082⟩,
  .pool ⟨37,20,[37,2,5,17],[3,7,11,13,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],1443,0x25800a08a21225361245a4c32510910484824190430d00802194086934d92c82030d26d10820186882c00904da20029b20a44809320b0110c00c004924104a20a0502800d20404802d32012da41a00324a41128b25349b0800032136d260041020a25308901968340021a2102ca4d16906d82d028b2892590496d865861360b20264148b20029a2804d22d80ca0c360a6100906032c02404100ca4432d82d041964241a48965264121048109101029308a28b4c12⟩,
  .pool ⟨31,21,[31,3,7,17],[2,5,11,13,19],1845,0x145031044280770c400010210002294004112413401098210088109804100606202b604090208010429020ed414204008211908580406110800c0241820020440008448001230ce0302008c4a2a08460088580ae18100004400000528008320022802030c24134213108200c0c5016e00128410020852001da028c0c010423210b2090c30100510013040052800000880002061d4068440188415148c4010301cc3120004884000881001060900c004221808068426210400810a0adc10250820041024081b501181802080642044021064200b209220800a51000210200008c3b80508823028a⟩,
  .pool ⟨73,31,[73,17,23,29],[2,3,5,7,11,13,19,31],111,0x14122102590d06410d329345b6⟩,
  .pool ⟨41,5,[41,5],[2,3],333,0x1b29221820300a0034112c00022000012980080822d10404006520000110000d220b0014030106112536⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨19,14,[19,2,7],[3,5,11,13],1353,0x1a61a41a61805b20a04a45148a6d24022510926084994c825320a6d860800060348808021860b04301924a4882d34424c868240220a2da40a01300041145b01128921200061001340b05a4122c04d06d100b0924932492434022d82c80d120968340b20021800121245220368a2080032014096d14110090584c908b2d044949260308341861004044b0180004186d94132904ca6484192422910092d944a2894814136806196096196⟩,
  .pool ⟨19,14,[19,2,7],[3,5,11,13],1095,0x400124410402192030424030410902920d000b00201825000a4524424092110d821900a2010010da0400090116900d26514014882032186534096104c20c061204a69008129205048849104301004300b2884530500104c20116432d860044b61928224224044320949109040b4c128169320a65008229065121a41940b0012d12584134c96996⟩,
  .pool ⟨41,12,[41,2,3],[5,7,11],657,0x1eb22824221020802021180020024004200030080b04000024004120904004802004100028000204027900810000500020801004800824120800900000834040300010800900100062101004102110905135e⟩,
  .pool ⟨31,21,[31,3,7,17],[2,5,11,13,19],205,0x1653318642c0f70d6e0812a510022952041dac3bc0d09863329a⟩,
  .pool ⟨41,12,[41,2,3],[5,7,11],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨41,12,[41,2,3],[5,7,11],999,0x7eeda8f289c4aa09d0d6f02098880496a700a268ab54181493d580904560927c8c2e01508c4c38d49cdb672543844721d20fa6278100c64020373805830d7eb0c1a01cec0402630081e465f04b84e221c2a4e6db392b1c32310a8074313e4906a20901abc928182ad5164500e569201119040f6b0b905523914f15b77e⟩,
  .pool ⟨41,31,[41,17,23,29,31],[2,3,5,7,11,13,19],1443,0x25800a08a21225361245a4c32510910484824190430d00802194086934d92c82030d26d10820186882c00904da20029b20a44809320b0110c00c004924104a20a0502800d20404802d32012da41a00324a41128b25349b0800032136d260041020a25308901968340021a2102ca4d16906d82d028b2892590496d865861360b20264148b20029a2804d22d80ca0c360a6100906032c02404100ca4432d82d041964241a48965264121048109101029308a28b4c12⟩,
  .pool ⟨41,31,[41,17,23,29,31],[2,3,5,7,11,13,19],73,0x1fffffffffffffffffe⟩,
  .pool ⟨73,40,[73,2,5,17,23,29],[3,7,11,13,19,31,37],111,0x14122102590d06410d329345b6⟩,
  .pool ⟨41,8,[41,2],[3,5,7],73,0x1a30280023100050316⟩,
  .pool ⟨41,5,[41,5],[2,3],31,0x121d47b6⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],427,0x54419250004488602030c2014002001403c28008015210980224000244019084a80100143c02800400280430c04061122000a49822a⟩,
  .pool ⟨41,26,[41,2,13,17,23],[3,5,7,11,19],543,0x5321a0d028800b64008849045049b2d20410184d12182502526112092da0db61941344300068024b2530912d10c32504c36596902024d14d24ca6d900b6ca2d06832116⟩,
  .pool ⟨41,26,[41,2,13,17,23],[3,5,7,11,19],185,0x1a3539c82a1e921022601ae31d6019102125e1504e72b16⟩,
  .pool ⟨37,21,[37,3,7,17],[2,5,11,13,19],803,0x268338a1b06726fc40ab8604a3c4501f87ae46053a967bcb31a01bc29cae8d012a0023118682a6d8b15338d611205d34a0a136af8d305d37694c33172648abc8e3733feab5f4a8a46a425fa33242096835b990a0e05f59c32de9e08f9c01b09f07aa3369a⟩,
  .pool ⟨73,32,[73,2,17,23,29],[3,5,7,11,13,19,31],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨41,14,[41,2,7],[3,5,11,13],31,0x121d47b6⟩,
  .pool ⟨181,20,[181,2,5,17],[3,7,11,13,19],1271,0x1021508163300c5176c1a1b4445b123423e2ca4029903cf647175339b52495e600d4eec1cb1c934110dc3c2540fb0ae7d246b476f224b0bc38e2359659223e86c5400a275f9b9e552a1da12f4971f71070650b7a45ab518622051badf55c9e83aa65965398e342f29bb091921db418ae00fd5bc1c4e77d32c72c7480d4ff9842db526315151d9083f66afd2cb83bd23725ddd07a3c9171cff31976f57bf7e⟩,
  .pool ⟨41,28,[41,2,7,17,23],[3,5,11,13,19],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,20,[41,2,5,17],[3,7,11,13,19],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,11,[41,11],[2,3,5,7],61,0x1434026619900b0a⟩,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨61,41,[61,17,23,29],[2,3,5,7,11,13,19,31,37,41],13,0x161a⟩,
  .pool ⟨73,31,[73,17,23,29],[2,3,5,7,11,13,19,31],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,14,[19,2,7],[3,5,11,13],41,0x1fffffffffe⟩,
  .pool ⟨41,6,[41,2,3],[5],657,0x1eb22824221020802021180020024004200030080b04000024004120904004802004100028000204027900810000500020801004800824120800900000834040300010800900100062101004102110905135e⟩,
  .pool ⟨41,6,[41,2,3],[5],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨41,6,[41,2,3],[5],999,0x7eeda8f289c4aa09d0d6f02098880496a700a268ab54181493d580904560927c8c2e01508c4c38d49cdb672543844721d20fa6278100c64020373805830d7eb0c1a01cec0402630081e465f04b84e221c2a4e6db392b1c32310a8074313e4906a20901abc928182ad5164500e569201119040f6b0b905523914f15b77e⟩,
  .pool ⟨73,27,[73,3,17,23],[2,5,7,11,13,19],513,0x8a988a5e9788ba41ce050fdb8c7d32ee0685ace6ae9153114bd2f3164839c081fb798fa65dc0d0b5bcd5d22e62297ade22c91738103f6e31f4cbb81a1eb39aba⟩,
  .pool ⟨73,3,[73,3],[2],27,0x8060b⟩,
  .pool ⟨37,20,[37,2,5,17],[3,7,11,13,19],73,0x1fffffffffffffffffe⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],513,0x1510483402194080482490480482612584c9a1110800164121814820102c14020100a0d020104a061209a0004222164c869219048048249048040a6100b04822a⟩,
  .pool ⟨73,20,[73,2,5,17],[3,7,11,13,19],111,0x14122102590d06410d329345b6⟩,
  .pool ⟨41,8,[41,2],[3,5,7],185,0x1a3539c82a1e921022601ae31d6019102125e1504e72b16⟩,
  .pool ⟨37,11,[37,11],[2,3,5,7],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨37,11,[37,11],[2,3,5,7],219,0x21a40309b2d02820412400ca2122932886d905969a2d020261b4832⟩,
  .pool ⟨41,2,[41,2],[],333,0x1b29221820300a0034112c00022000012980080822d10404006520000110000d220b0014030106112536⟩,
  .pool ⟨41,2,[41,2],[],57,0x1a60a0132014196⟩,
  .pool ⟨41,2,[41,2],[],185,0x1a3539c82a1e921022601ae31d6019102125e1504e72b16⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨73,27,[73,3,17,23],[2,5,7,11,13,19],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨73,17,[73,17],[2,3,5,7,11,13],181,0x10401408204430019030203301030260030881040a0082⟩,
  .pool ⟨41,5,[41,5],[2,3],61,0x1713e6940a59f23a⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],703,0x54d100f940c4050089934adc310008f52318201106001009a08c8484e02e108861d0595202740c44a2824d0810b2414522302e404a9a0b86110874072121310590080060880418c4af10008c3b52c99100a023029f008b2a⟩]
private def step360 : Stage := ⟨cfg,180,2,keys180,keys360,rows360,8,0xa2f3a0a0a2f3a0a3a2f3a2f3a2f3a2f2f0a0a3a2f0a0a3a3aa53a303aa43a302e3b3a2e2e3b3a2e2f3a2f3a2f3a2f3a0c2c0ca30c2c0ca2a10c300ca00c300c0c2d0c390c2d0c39000303380003033830369f3630369e3603010003030100030c130c130c130c130c130c130c130c13130c130c130c130c0404040404040404040404040404040404040404040404042e0737072e07370707370737073707373707370737073707370737073707370705040504050405040403040504030405050403040504030430369d3630369c3635111110351111102c0a0a002c0a0a003233323332333233113510111135101101360100013601002e9b342e2e9a342e33323332333233320099362c0098362c1035100a1035100a010a0a34010a0a3433329732333296320708070807080708080708070807080707080708070807081915191419151914120a0a19120a0a1912311519123115190a14190a0a14190a19143112191431122e15312e2e15312e1313131313131313131313131313131313131313131313131a03032f1a03032f301a951a301a941a2f03031a2f03031a2e16932e2e16922e160a0a2d160a0a2d0a162c0a0a162c0a912a902a8f2a8e2a8d1e1e8c8b1e1e8a2810281128102811892b882a872b862a852a0229842a022911281028112810282a8329822a81298028102810281028101e1e1e1e1e1e1e1e1c131c131c131c13131c131c131c131c1c131c131c131c1304030403040304032704030427040304040d0403040d04030402047f0402047e7d047c047b047a04040304030403040313131313131313131313131313131313131313131313131322262226222622260303030303030303032226030322260325242524252425242425242524252425252425242524252404040404040404040404040404040404040404040404040404040404040404040404040404040404040404040404040402237923022378231e1e1e1e1e1e1e1e1e77231e1e76231e130c130c130c130c0c130c130c130c13130c130c130c130c2275220222742202221f2273221f2272210c1f0c210c1f0c200420042004200404200420042004200404040404040404040404040404040404040404040404040404040404040404040404040404040404040404040404041e1e1e1e1e1e1e1e711c1f1c701c1f1c6f1e1e1d6e1e1e1d1c6d1c6c1c6b1c6a1d021d691d021d681c671c661c651c641313131313131313131313131313131313131313131313131b1a1b1a1b1a1b1a14191519141915190a0a0a0a0a0a0a0a131313131313131363626117605f5e17165d1618165c16185b02025a590202585717561655175416535251504f4e4d4c0a0a0a0a0a0a0a0a15131513151315131314131513141315131413121314131208070307080703070708070807080708030703070307030703030303030303030003030d0003030d4b0002004a0002000f0e0f0e0f0e0f0e10101010101010100a0a0a0a0a0a0a0a0e0f0e0f0e0f0e0f10111110101111100e0f0e0f0e0f0e0f10111110101111100e0f0e0f0e0f0e0f0f0e0f0e0f0e0f0e0c490c480c470c460c450c0d0c440c0d430c020c420c020c070b0709070b07090a070a070a070a07090709070907090707080708070807080708070807080708080708070807080703040604030406040504050405040504040304030403040300410040003f003e02003d0002003c000100010001000100⟩
set_option maxHeartbeats 5000000 in
private theorem valid360 : ∀ r ∈ rows360, Valid cfg 360 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test360_0 : ∀ i ∈ List.range' 0 137, ∀ x y z : Fin 2, Test step360 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test360_137 : ∀ i ∈ List.range' 137 20, ∀ x y z : Fin 2, Test step360 i x y z := by decide +kernel
private theorem run360 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 180 a b c keys180) : Match 360 a b c keys360 := by
  apply refine step360 h bad (by decide) (by decide) valid360 _ old
  intro i hi
  change i < 157 at hi
  by_cases h0 : i < 137
  · exact test360_0 i (by simp only [List.mem_range'_1]; omega)
  exact test360_137 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨32,10,0xa222fa6e8831e9ba222f4ce8831d334822f79d2031de74822f1fd2031c7f8422f97e1031e5f8422f3de1031cf72a17b97ca804e5f2a17b3dca804cf72a22f6aca831dab2a22f10ca831c438417b6ae1004dab8417b10e1004c436622f88d9831e236622f2ed9831cbb0c22f5bc3031d6f0c22f01c3031c07⟩
private def rows720 : List Rule := [
  .pool ⟨41,18,[41,2,3],[5,7,11,13,17],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],1629,0x130482d060100a4426890c844169109804028340825328300a6c32194880522094080412010084c328b44804220b0480522830980402090082512034080d06030da24228b4082522810086c16990182c029305a0412194880426114486d06030980436010880402010080d061148804060140804361941a24020900824320148805228141a6406114882426110080d029304a25021b40a64020b0d80406830880d228141a04068101804020104805228309824128108804068b0ca4412010082406090d824261108a6c028a⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],949,0x175663565e83704f610d7e83069a2c1342e3a4641549fb43bb08c49a9967f79738894ed4187a1e4ea63621f400946bc59106a9b94f6ce050b1a218000611634281cdbca765582268f58a400be11b195c9e17860adca4473a7bf9a65648c43770b7e4aa098971d0b20d1658305fac21bc83b05e9ab19aba⟩,
  .pool ⟨31,23,[31,23],[2,3,5,7,11,13,17,19],37,0x10ac804d42⟩,
  .pool ⟨41,31,[41,23,29,31],[2,3,5,7,11,13,17,19],1281,0x1b2c22d16032c948a0402c22820986136404900526d021224021020b40b40869b09104921900049864a28901345820248101301840201228840368805240a24a2906180810834c245a48004101921b04b4836126020800496890cb04204061825149140928045b00845120100860320204901068b20245149864800261248224365840b40b4102100912102d928024809b2186410510d008144a4d301a2d10d36⟩,
  .pool ⟨61,45,[61,3,5,23,29,43],[2,7,11,13,17,19,31,37,41],779,0x23b064abd48b333108820e34b5f1c0a9aa6f2e76e607e0cd219800ad06fb602d2306d300a34715d34206f99002aa1e14a3ac785a8bff6209eb534561d3a5f349b3b4b39208f4afdc67b0cf81788908b098a62f87052538baeef71332c942ad1f23a⟩,
  .pool ⟨37,20,[37,2,5],[3,7,11,13,17,19],123,0x10000124014004012182110536⟩,
  .pool ⟨73,31,[73,23,29,31],[2,3,5,7,11,13,17,19],357,0x120c205940a6400534580c12532c921240040060a0122112014180080092124d32920c068b28009940a6810c12⟩,
  .pool ⟨241,26,[241,2,13,23],[3,5,7,11,17,19],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨37,21,[37,3,7],[2,5,11,13,17,19],85,0x165225ce0300301ce9129a⟩,
  .pool ⟨41,33,[41,3,11,23,29],[2,5,7,13,17,19,31],153,0x8f809aee7a1c98d4831debd3d33e922a9dfa3a⟩,
  .pool ⟨31,23,[31,23],[2,3,5,7,11,13,17,19],357,0x120c205940a6400534580c12532c921240040060a0122112014180080092124d32920c068b28009940a6810c12⟩,
  .pool ⟨41,14,[41,2,7],[3,5,11,13],255,0x4012100120816100102580594422902110406410c36810522926130494996⟩,
  .pool ⟨37,11,[37,11],[2,3,5,7],221,0x13d42232c79f91d869513040b74120bb408322a586e27e78d3110af2⟩,
  .pool ⟨41,18,[41,2,3],[5,7,11,13,17],1105,0x1eb228642210e08021201802a0020014211920000a0000226000402000001c8024080b0c200004000220110410047424a000400480406000101000000a86000020801205027902812004100001854000002020001808048008001490b880208220110000800010c340409004e00000100800191000014000126210a001001500601210041c2110985135e⟩,
  .pool ⟨41,18,[41,2,3],[5,7,11,13,17],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],119,0x141324470b0970652b11cb15977e⟩]
private def step720 : Stage := ⟨cfg,360,2,keys360,keys720,rows720,6,0x4104104104104104104104100410410410410410410410410410410410410410410410410c30c30c30c30c30c30c30c33ce3ce3ce3ce38f38f38f38f38f38f38f38f3ce3ce3ce3ce38f38f38f38f3ce3ce3ce3ce34d34d34d34d34d34d34d34d0c30c30c30c30c30c30c30c318618618618618618618618630c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c24924924924924924924924924924924924924924924924930c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c24924924924924924924924930c30c30c30c30c30c30c30c30c30c30c30c30c30c30c30c0c30c30c30c30c30c30c30c32cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb2cb24924924924924924924924924924924924924924924924924924924924924924924924928a28a28a28a28a28a28a28ac08bc8b88b4822c22b22a229249249249249249249249249a089c898894822422322222122021f21e21d7086c86886482492492492492492492492496085c85885481c71c71c71c72142132122111c71c71c71c71451451451451041041041041451451451451451451451451041041041041451451451451861861861861861861861861041041041041451451451451041041041041451451451451861861861861861861861861861861861861861861861861451451451451041041041041451451451451041041041041451451451451041041041041451451451451041041041040c30c30c30c30c30c30c30c3082082082082082082082082082082082082082082082082082082082082082082082082041041041041041041041041000000000000000000000000000000000000000000000000000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 106, ∀ x y z : Fin 2, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 360 a b c keys360) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 106 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
private def keys3600 : Keys := ⟨0,12,0x0⟩
private def rows3600 : List Rule := [
  .pool ⟨41,35,[41,5,7,23,29],[2,3,11,13,17,19,31],1111,0x120d54b222308e185c190f5581f9479037a412c210ba2327c502bf92346b92404a6e8870131cb14807118ac8490a1d6eb536505cdaead61d0f217d9ed31c2410318d3ded81d43e40424e53f1db472484413b07469488a0c56583508907a76cec8e731f6d624537b1e688adddb22953a600bb1c133aa2d7b8b75a03f41d2056540f47c1e70ee3b9b29547b6⟩,
  .pool ⟨61,45,[61,3,5,23,29,43],[2,7,11,13,17,19,31,37,41],101,0x1ffffffffffffffffffffffffe⟩,
  .pool ⟨101,25,[101,5,23],[2,3,7,11,13,17,19],241,0x11a0115e923660112012414509d84703886e428a0920122019b125ea20162⟩]
private def step3600 : Stage := ⟨cfg,720,5,keys720,keys3600,rows3600,2,0x2aa0015500000002aa0015555400002aa0000055400002aaaa800554000015500000aa8000015500000aaaaa0015500000002aa0015500000002aa001550015500000aaaaa0015500000002aa0015500000002aa0015555400002aa00000aa8005540000000aa8005555500000aa8000015500000aaaaa0015500000aa8005540000000aa8005540000000aa8005555500000aa8000015500000aa800002aa0015555400002aa0000055400002aaaa8005540000000aa8005540055400002aa0000055400002aaaa8005540000000aa8005540000000aa800556aa0015500000002aa0015500000002aa0015555400002aa0000055400002aa0015500000aaaaa0015500000002aa0015500000002aa0015555400002aa00000aa8005540000000aa8005555500000aa8000015500000aaaaa001550000000000aa8005555500000aa8000015500000aaaaa0015500000002aa001550000055400002aaaa8005540000000aa8005540000000aa8005555500000aa800aa8005540000000aa8005540000000aa8005555500000aa8000015500000aa800002aa0015555400002aa0000055400002aaaa8005540000000aa8005540055400002aa0000055400002aaaa8005540000000aa8005540000000aa800556aa0015500000002aa0015500000002aa0015555400002aa0000055400002aa55400002aa0000055400002aaaa8005540000000aa8005540000000aa800556aa0015500000002aa0015500000002aa0015555400002aa0000055400002aa002aa0015500000002aa0015555400002aa0000055400002aaaa800554000015500000aa8000015500000aaaaa0015500000002aa0015500000002aa001550015500000aaaaa0015500000002aa0015500000002aa0015555400002aa00000aa8005540000000aa8005555500000aa8000015500000aaaaa001550000000000aa8005555500000aa8000015500000aaaaa0015500000002aa001550000055400002aaaa8005540000000aa8005540000000aa8005555500000aa80000000aa8005555500000aa8000015500000aaaaa0015500000002aa001550000055400002aaaa8005540000000aa8005540000000aa8005555500000aa800aa8005540000000aa8005540000000aa8005555500000aa8000015500000aa800002aa0015555400002aa0000055400002aaaa8005540000000aa80055400002aa0015500000002aa0015555400002aa0000055400002aaaa800554000015500000aa8000015500000aaaaa0015500000002aa0015500000002aa001550015500000aaaaa0015500000002aa0015500000002aa0015555400002aa00000aa8005540000000aa8005555500000aa8000015500000aaaaa0015500000⟩
set_option maxHeartbeats 5000000 in
private theorem valid3600 : ∀ r ∈ rows3600, Valid cfg 3600 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test3600_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 5, Test step3600 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test3600_8 : ∀ i ∈ List.range' 8 8, ∀ x y z : Fin 5, Test step3600 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test3600_16 : ∀ i ∈ List.range' 16 8, ∀ x y z : Fin 5, Test step3600 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test3600_24 : ∀ i ∈ List.range' 24 8, ∀ x y z : Fin 5, Test step3600 i x y z := by decide +kernel
private theorem run3600 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 720 a b c keys720) : Match 3600 a b c keys3600 := by
  apply refine step3600 h bad (by decide) (by decide) valid3600 _ old
  intro i hi
  change i < 32 at hi
  by_cases h0 : i < 8
  · exact test3600_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h8 : i < 16
  · exact test3600_8 i (by simp only [List.mem_range'_1]; omega)
  by_cases h16 : i < 24
  · exact test3600_16 i (by simp only [List.mem_range'_1]; omega)
  exact test3600_24 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+10=2^a*5^b*17^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=1 ∧ b%12=1 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h180 := run180 h bad h60
  have h360 := run360 h bad h180
  have h720 := run720 h bad h360
  have h3600 := run3600 h bad h720
  obtain ⟨i,hi,_⟩ := h3600
  exact Nat.not_lt_zero i hi
end D10

namespace D11
private def cfg : Config := ⟨11,11,17,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨0,4,0x0⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .target,
  .div 7,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x44043043208208208043044043208208208043043044208208208044043043208208208043044043208208208043043042208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+11=11^a*17^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  obtain ⟨i,hi,_⟩ := h12
  exact Nat.not_lt_zero i hi
end D11

namespace D12
private def cfg : Config := ⟨12,2,3,17,2,1,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨11,4,0x27a81a3a8948a76416ba45446727a0140⟩
private def rows12 : List Rule := [
  .div 5,
  .div 7,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x1000100010000100010001100010001000010001000100001000100010000100010001100010001000010001000100001000100010000100010001100010001000010001000100020001000100001000200010000100010002100020001000010001000e00002000100010000100020001200010001000010002000100001000100020000d0001000110001000200010001000100001000100010000100010001000010001000110001000100001000100010000100010001000010001000110001000100001000100010000100010001000010001000100020001000110001000c00002000100010000100020001000010001000210002000100001000100020000b0001000100001000200012000100010000100020001000010001000200010001000100001000100011000100010000100010001000010001000100001000100011000100010000100010001000010001000100001000100011000100010000100010001000100020001000010001000200002000100011000100020000a0001000100001000200010000100010002100020001000010001000200002000100010000100090001200010001000100010001000010001000100001000100010000100010001100010001000010001000100001000100010000100010001100010001000010001000100001000100010000100010001000100020001800010001000010002000100001000100020000200010001100010002000020001000100001000700010000100010002100020001000010001000200002000100010001000100010000100010001100010001000010001000100001000100010000100010001100010001000010001000100001000100010000100010001100010001000010001000100010001000200002000100010000100020001200010001000010006000100001000100020000200010001100010002000020001000100001000200010000100010003100020001000100010001000010001000100001000100010000100010001100010001000010001000100001000100010000100010001100010001000010001000100001000100010000100010001000100010002100050001000010001000200002000100010000100020001200010001000010002000100001000100040000200010001100010002000020001000100001000200010⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨66,6,0xabe9a7fa387e9adeecabba6ae209f882dd63935a61d6cb728eacab25ea037ae19b9436e20d8a0062b315889565015a0c4ae2529464a59fdae4f65b7a8a7eae87aa2adeb87796ad28874aedc62ab1ba4c6431d9c376d01d84c6a725aa806a425784952d0d490646a0d19edf2dabcaa4f2187c92de6aab9b61e61b769eadad9f6924daa876b6dce4ab3864ce7873aadc279f0b64c2⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,9,[31,3],[2,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,8,[61,2],[3,5,7],31,0x68818116⟩,
  .pool ⟨61,8,[61,2],[3,5,7],217,0x1a20200420400081200080104003000820040012040008108010116⟩,
  .pool ⟨31,6,[31,2,3],[5],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .prime 31,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .pool ⟨61,31,[61,17,19,23,29],[2,3,5,7,11,13,31],1155,0x20840001a64308201141020004340228908009801a0034892502900424c001024108221808301028000220b0400000412400480000880802420510832180820080190026802520102034810980122420430886802000506100ca2806912086490492186d020021948228141220221a04109129008845004020000328060244a4080120182520c141168200800248b0012⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],31,0x68818116⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,7,0x680000000000027800138000040000000000009a00000980004b0000000000000d0000580000000000001000000580012800000000000124000120000c00000000000000900000c000058000000000002380011800001140000000000011000012000000000000180000b0000000002000086000000000000180004200003800000000000000b00004000104000000000001000001800000120000000000000e0000b0000000000003f0001f000001e8000000000001e00001c000140000000000007600000740003900000000000038000038000000000000480000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000030000000000001b8000d80000000000001400000d40000a0000000000006800006000198000000000000006000190000080000000000001400062000000a00000000000060000060000000000000200017800001700000000000016800014000580000000000000c0000000ac0000a000000000000100002a0001480000000000000280001380001c000000000000140004c000000a0000000000004a000060000000000000700004000000400000000000012000014000460000000000000c000000e00006000000000000220001080000000000002800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000f800000000000010000780000000000007400000700003600000000000008000030000d00000000000000190000c00005c000000000000580002a00000280000000000002600001000000000000120000880000080000000000000100003c0001c000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
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
private def keys180 : Keys := ⟨57,8,0x9673aa1e37aa1e736e5a376e5a73329637322a4faa664f6ea24f322aa39e66679e2a679ea22b9e66a362a267626667622a2b62a2a326a267262a6726662b2636079e720762ae0726ae979236975672971a4e8b92128b928a4f921213928a8b564e8b56124f564e13568a8b1a128b1a4e4f1a8a131a4e2b868a2b4a122b0e7e8b86064f86068b4a424f4a428b0e7e4f0e66af7aa2737aa2af3e2a733e2aaf026673025a977a96973e1e9702⟩
private def rows180 : List Rule := [
  .pool ⟨61,37,[61,17,23,29,31],[2,3,5,7,11,13,19,37],1463,0x425082205d50c081122a62200a1549443064c1d892c180805408c063661c231210a042825b053e6849618f1438541d01036744195a0112d4a687906a5180e42191201cc4024189048338f51261aac39d121832806d5bb56200f91323003f20502001e692a7124038226985102034da264d939c46e9705388d23428541a8244853d2425d1102f5e035441c300690d21024d01b0ad5aa73431839028dc8f50f87a6424c42c50f0d945038f3328a8b336c4d4015ab87135e⟩,
  .pool ⟨19,4,[19,2],[3],31,0x121d47b6⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],61,0x1713e6940a59f23a⟩,
  .pool ⟨37,28,[37,2,7,17,23],[3,5,11,13,19],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨19,4,[19,2],[3],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨37,24,[37,2,3,17,23],[5,7,11,13,19],61,0x1ffffffffffffffe⟩,
  .pool ⟨19,4,[19,2],[3],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨181,3,[181,3],[2],185,0x246010012904100600004000526288440350041c01020a⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],1267,0x348c2b12e204bd7201f2a78f041d44b5eab5459233003941b2cf990d1e9d71d40212241898c874e284b12aece0118ad821721c1120298e0c28542905c489081ef9b2b4a6828b787979330e0f904a11a372cf40b87234121602cba12c2922006ed6ad44f4b956acd8a63eb57873079e0a663d8882a70dab0c1cca666d9b3b7c45106064d6204a25d037e31b2554288125c45db060a903f3040dbb0a70b8e52⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],259,0x30a92334e3d1b04a00d110ac04ae5a20abb2408dbc2e750bf2cf07010c31b2a72⟩,
  .pool ⟨37,24,[37,2,3,17,23],[5,7,11,13,19],181,0x1ffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨61,8,[61,2],[3,5,7],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,4,[19,2],[3],275,0x688090048210002084080200010008108060108100080004010210400084120090116⟩,
  .pool ⟨61,8,[61,2],[3,5,7],481,0x1a60e406f08054a3a952005088d2202b63088820000098030303887034513228b038470303006400001044431b50112c4428012a5714a8043d809c196⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],259,0x30a92334e3d1b04a00d110ac04ae5a20abb2408dbc2e750bf2cf07010c31b2a72⟩,
  .pool ⟨61,8,[61,2],[3,5,7],247,0x12080090000082000000140481080114004000000621016080021180050316⟩,
  .pool ⟨37,28,[37,2,7,17,23],[3,5,11,13,19],1767,0x420080410910524524086424526182432182400812830496136182806c00c200a0d068009241141804208801b0134d368124a29169009904169b44100a41905048801a2102984500182582516532112d00424190584c004169a44125b21b61a2c80424d34990992022c82114196920024532c828b2424420104996402820032012590800516d84816414996902532010412c10c36d14c225328264a4d164208b6514020596402d201228125a0004134036c86996434124926da0d028b6806d80da0c101300961a25a6492c30182c30914190ca4910916522516c36996⟩,
  .pool ⟨61,37,[61,17,23,29],[2,3,5,7,11,13,19,31,37],13,0x161a⟩,
  .pool ⟨31,9,[31,3],[2,5,7],481,0x143002244080080620201001400c080100040080244112002208002800108420005000411001220890040080020040c00a0020101180400408910030a⟩,
  .pool ⟨31,9,[31,3],[2,5,7],1525,0x141000866080000008181a0321481a000000c04080c1008600802004800284c21001225020004100848004860008000000000000000900408109001812000d02005001048c021294000408c800302100000011880008b0182308801019400a001400a60200443106034400046200000021030004c408000a52100c48200280102c00120600242040802400000000000000040018480048402080010291200210c8500048010040184020c04080c000001604a130160604000000419840020a⟩,
  .pool ⟨19,2,[19,2],[],31,0x121d47b6⟩,
  .pool ⟨19,18,[19,2,3,17],[5,7,11,13],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],31,0x121d47b6⟩,
  .pool ⟨37,23,[37,17,23],[2,3,5,7,11,13,19],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨37,23,[37,17,23],[2,3,5,7,11,13,19],1267,0x42a043140f048c0cc11080041f04401c48f524103e3ad0886044138b0abc4102401b1414e18080aa00036420499226098372004084a14114343410528884032484986020000600840024208e2c643402c263471042400210060000406192124c021114a082c2c2882852102004ec1906449920426c000550101872828d80240823d50d1c82206110b5c7c0824af12380220f820010883303120f028c20542⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨31,22,[31,2,11,17],[3,5,7,13,19],665,0x1a3438806b524104a7389c70840c109270a82b130a90a9465080038008035820a8032244362c4939026319027248d1b089130054106b0040070004298a542543235054392420c08438e4739482092b580470b16⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],481,0x1a206404e0801082a00200100802002360000020000018000200002014503028a010000100006000001000001b10010040200100150420041c8098116⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨37,23,[37,17,23],[2,3,5,7,11,13,19],305,0x1200bc4011401120662218830001000006000303000180000200030461119812200a2008f4012⟩,
  .pool ⟨19,2,[19,2],[],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,2,[19,2],[],37,0x1ffffffffe⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],181,0x1ffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨19,2,[19,2],[],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],247,0x28021c0000000100009000810100050000360200248908000c0a80868102⟩,
  .prime 37,
  .pool ⟨37,13,[37,13],[2,3,5,7,11],1159,0x429748101c00a021b54228ae4680c0cd40c15025f74c461159042ace421e00114f140680c0ec06080100491908005021c00ce54f13224b100530a802412801848244a1ca12d208c14283104b48538522412180148240150ca008d244c8f2a73003840a00109892008010603703016028f2880078427354209a886232efa40a8302b3030162751442ad840500380812e942⟩,
  .pool ⟨37,13,[37,13],[2,3,5,7,11],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨37,13,[37,13],[2,3,5,7,11],181,0x1717e2151bcfb266b4947840878a4b59937cf62a11fa3a⟩,
  .pool ⟨19,9,[19,3],[2,5,7],61,0x1713e6940a59f23a⟩,
  .pool ⟨19,10,[19,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨19,17,[19,17],[2,3,5,7,11,13],93,0x124c345b00221100368b0c92⟩,
  .pool ⟨19,17,[19,17],[2,3,5,7,11,13],181,0x10401408204430019030203301030260030881040a0082⟩,
  .prime 181,
  .pool ⟨19,10,[19,2,5],[3,7],31,0x121d47b6⟩,
  .pool ⟨19,9,[19,3],[2,5,7],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨19,10,[19,2,5],[3,7],481,0x1fba6e34e2a13996a02730197b0f08f3604424ad7c451b0cba2c06a81652fd29a05580d174c36288fad490881b3c43c37a60339015a672151cb1d977e⟩,
  .pool ⟨19,9,[19,3],[2,5,7],671,0x50401010000040600000c00000240000004014020012200004000000820090001800001000000202010000804040000008000018000900410000002000044800402802000000240000030000060200000808020a⟩,
  .pool ⟨19,9,[19,3],[2,5,7],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,9,[19,3],[2,5,7],775,0x100028c003000000020a4090000a0000240000100000000000402000200008221420018040000000900008200000000000000a010000000004100000420000000208000008001000000008800030000002000000000a0210020000000808020a⟩,
  .pool ⟨19,9,[19,3],[2,5,7],37,0x1ffffffffe⟩,
  .pool ⟨19,10,[19,2,5],[3,7],1525,0x1b68a61224e418202086b0c04a012001250241b22802d0009620404c35001118208c1520941b6d30730110628810104348e02500901096802899040548080b00200712801888304648804a2cb6983900a83944180c00a432020449000950906d8242a4002488101309400c0608a7054027065b4d148044988304460052380100340404a8082645005a4202402901c4b082020451822033832db60a412a0c410622002b0c80811a4002d005136090292001201480c35841010609c9121945b6⟩,
  .pool ⟨19,9,[19,3],[2,5,7],427,0x54419250004488602030c2014002001403c28008015210980224000244019084a80100143c02800400280430c04061122000a49822a⟩,
  .pool ⟨19,17,[19,17],[2,3,5,7,11,13],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩]
private def step180 : Stage := ⟨cfg,60,3,keys60,keys180,rows180,7,0x15ad50b543666d96ad50ad4365ad96b350ad6b65aa16b36cd19aa5ca9a2a5eb99aa68a9a2e5eb952a68cda2e54b952f5ad553554b552d66d552d54b5aad66a952d6ab5aaa66a96ae54b552d66b572a54b572d66a972a5ab572a66a96aa5ab952d50b542a66a96ad50a942a5aa96b350a96aa5aa16b354d172a5ca97aa68cd72a68a97ae68cd52a68b97ae54cd53454b59ad50a942a5ab59aa50a96aa5aa19aa5aa96a85aa152d60a99aa5aa96b060a96aa5acd6b054a96b05acd53054b542a52a94b352a152a52a14b354a152952a153354a552950a96a85aa153354b56a854a152d54b59a854b552d50b59aa52a153354a552950a152954a59a950a952950a59aa50a94aa5ab96ae54cd52d5ab952e54b552d66b952d54b572d66a952d64b58aa64a96ad64a98aa5aa96b264a96aa5ac56b254ad6a85aa15a856b56a856a15ad56b542856b55ad50b542b5ca96aa5ab96ae54a96ae5ab952e54b56ae54b952d54b572d62a982a5aa96b062a96aa5ac16b054a96b15ac153054b572c5ea97ac58b952c5eb97ac54b952c5eb962c54bd52c5ca96ae5ab952e54b56ae54b952d54b572e54b552d5cb572a52b952e54a55295cb952954a57295ca95295ca572a5ca94aa5aa16a854a152d5aa152854b552d50a152d54b542d50a96ae56b95ad56b572e56b55ad5cb572b56b572d5cad72b5ab952f54bd72f5ca952f5cbd72a5ca97af5ca972a5ea97ae56b172d5cb162b5ab172b5cb16ab5ab172b58b16ae5ab15a854a552950a542a54a542950a942a52a542a50a94aa52a0ba42a58aa4485d3242a5caa42c5d3242a5d2242c553242e952172a5d2242c552174a5d2152c552174a912152e552164a90b952e912162a90ba52e90a962a90ba54890a972a90b242a68aa42c68da42a692242c54da434692152c55224346d2162a992172a5d2162a912174c5d2152a90b174c912152e90b154c90b952e90b154890ba62e90a954858ba64890a972c55224346cd242a55216346d2242a692162a6d21a2a692162a9121a36692152a90b1a36912153490b153690d153490aa42c5d3a44854ba42c553a42e54ba42c552242e9cba42a5d3244854b9548593242e54ba44858aa42e98ba42a58aa42a90b174a912152e90b154a90b952e90b154890ba52e90a9b4868a9a4890b154868d9a4854b154868da44854d154858c152e54b962e58a952e60b962a58a972e60a962a5ca972c80ba32e59116445cba34059117445cb23405d1172c5cb222e58a9e2a5ca972c58a972a5cf172c54a972c5cf152c54ba02e84b963e58f972e850163e5cf972c850173e5cb172c7cb962a78a972a5cb162a5ca973c5cb152a5cb173c54b152e58a9d2a74d9c2c54a9d2c74d952c54e1d2c54d953a54e162c54d15346cd162a54d16346ca962a68d162a6ca9a2a68b152e58b982a58a972e58a982a5ca972c58a972a5cc172c54d953454d163458a95346cd162a58a9a346ca962a68a9a2c58a972a5cb173254a972c5cb153254b972c54b152e54b992a5cc172c54b152e5cc152c54b952e58c152e54b962e58a81221f787021c0ee221c08703b40ec0e1c09103ac3ea0e04987021c0930250387024c0930e50381024c3930e04381282810404134840a0810414134020a08204140b38208082050c4810304181062448106041818624081062418182240830a04181062418482041850624084820c1850224083020c24886cc1b2e4c63c306c4470e00c3c35fbc4435d0d7035b1e102820608202096828208082030964102081420305601040404981280898202049822808082024c9820208094024c10624081820c0831224083020c0c31204083120c0c112041ab870c1c3090c283870d583090e283860d543890e18386141aa53a43c3110d4684f0c3c34e0d348cc0d2c34a1f24886161c087020c08e0e1c08b020c38e0e0408b0e0c3810e047101a0c68e1e3018d1a0c80e1e3418d180c80d1e3470d180c282020808303201020214083051c101021410304041018d143860e1a206161c386861a107161c306821e0070c1c30b0e18486141c4870c18487141c3070c244870c1c30a0c243867e1df070c1c3087a1c3070cf03080e1c33b0ce83880e18239041410404101b804101040a101820411b840a08182080c101040400100081010604002000808106080020208080⟩
set_option maxHeartbeats 5000000 in
private theorem valid180 : ∀ r ∈ rows180, Valid cfg 180 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_40 : ∀ i ∈ List.range' 40 26, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
private theorem run180 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 180 a b c keys180 := by
  apply refine step180 h bad (by decide) (by decide) valid180 _ old
  intro i hi
  change i < 66 at hi
  by_cases h0 : i < 40
  · exact test180_0 i (by simp only [List.mem_range'_1]; omega)
  exact test180_40 i (by simp only [List.mem_range'_1]; omega)
private def keys360 : Keys := ⟨6,9,0x1ed3f613d916c27b4fc1cf645838b54b9716a967a⟩
private def rows360 : List Rule := [
  .pool ⟨37,21,[37,3,7,17],[2,5,11,13,19],803,0x268338a1b06726fc40ab8604a3c4501f87ae46053a967bcb31a01bc29cae8d012a0023118682a6d8b15338d611205d34a0a136af8d305d37694c33172648abc8e3733feab5f4a8a46a425fa33242096835b990a0e05f59c32de9e08f9c01b09f07aa3369a⟩,
  .pool ⟨73,8,[73,2],[3,5,7],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨41,24,[41,2,3,17,23],[5,7,11,13,19],61,0x1ffffffffffffffe⟩,
  .pool ⟨73,16,[73,2],[3,5,7,11,13],111,0x14122102590d06410d329345b6⟩,
  .pool ⟨31,26,[31,2,13,17,23],[3,5,7,11,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .prime 41,
  .pool ⟨41,23,[41,17,23],[2,3,5,7,11,13,19],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨73,16,[73,2],[3,5,7,11,13],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨41,23,[41,17,23],[2,3,5,7,11,13,19],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨37,24,[37,2,3,17,23],[5,7,11,13,19],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  .pool ⟨41,9,[41,3],[2,5,7],37,0x165e211e9a⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],703,0x54d100f940c4050089934adc310008f52318201106001009a08c8484e02e108861d0595202740c44a2824d0810b2414522302e404a9a0b86110874072121310590080060880418c4af10008c3b52c99100a023029f008b2a⟩,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],427,0x54419250004488602030c2014002001403c28008015210980224000244019084a80100143c02800400280430c04061122000a49822a⟩,
  .pool ⟨41,5,[41,5],[2,3],61,0x1713e6940a59f23a⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],365,0x29000821008c301e30a8411208159900000201906461100030000200070008108800982808004420a10010b2082⟩,
  .pool ⟨41,25,[41,5,17,23],[2,3,7,11,13,19],1147,0x448c615c00e90019f1080620f4a030255188d02902500580008c208cb1f0204000200800493e205c8ca19129da1910d92121404a225a4b03241010eb862d03c0a1a2e6d028280aa955014140b67458503c0b461d7080824c0d25a44520284849b08985b948985313a047c920010040002040f8d3104310001a00a40940b118aa40c052f0460108f980097003a863122⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩]
private def step360 : Stage := ⟨cfg,180,2,keys180,keys360,rows360,5,0x6528c6528c4a9494a94900000000005252a5252a03014030144a9494a94974e6e74e6e039c0039c074c0e74c0e4c2094c2098c2118c2116ca4d6ca4d040110401182530825308463084630935b2935b28c2118c2114c2094c2096824d6824d84630846300000000000200802008023c8c23c8c21084210842b9c52b9c52b9c52b9c5714ae714ae52d6a52d6a6b5ad6b5ad00000000004a9494a9495a94b5a94b6b5ad6b5ad02c0c02c0c5252a5252a6b5ad6b5ad5a94b5a94b5b18b5b18b4a9494a949414a8414a828005280052a0052a005390e4390e4190641906421084210842108421084d1324c12e4200802008029885298852900529005214a6214a62988529885214a4214a4214a4214a4058020540218841188410000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid360 : ∀ r ∈ rows360, Valid cfg 360 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test360_0 : ∀ i ∈ List.range' 0 57, ∀ x y z : Fin 2, Test step360 i x y z := by decide +kernel
private theorem run360 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 180 a b c keys180) : Match 360 a b c keys360 := by
  apply refine step360 h bad (by decide) (by decide) valid360 _ old
  intro i hi
  change i < 57 at hi
  exact test360_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨37,21,[37,3,7],[2,5,11,13,17,19],671,0x51401410840040610100c00880a50008044054060012200444800400a208900018488810801002c2018421804340080108111218000910450020012220044800602a02201000a50110030080860200210828028a⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨31,26,[31,2,13,23],[3,5,7,11,17,19],777,0x1a2124596090ca49a4020d029360921a60800060029904264868a44208205a60a01300141144a01001221a0c049121b48304b6122480c161120020148a20a00320141968104108945849908265001800041961241b2502c10096494c241a6892116⟩]
private def step720 : Stage := ⟨cfg,360,2,keys360,keys720,rows720,2,0xaaaa5555aaaa555500000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 6, ∀ x y z : Fin 2, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 360 a b c keys360) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 6 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+12=2^a*3^b*17^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=2 ∧ b%12=1 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h180 := run180 h bad h60
  have h360 := run360 h bad h180
  have h720 := run720 h bad h360
  obtain ⟨i,hi,_⟩ := h720
  exact Nat.not_lt_zero i hi
end D12

namespace D13
private def cfg : Config := ⟨13,13,17,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨5,4,0x6b009067005063⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .target,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x131018101310101010101010101310131017101010101010131016101310101010101010101310131015101010101010131014101310101010101010101310131012101010101010⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨2,6,0xc840335⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,21,[31,3,7,19],[2,5,11,13,17],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨31,17,[31],[2,3,5,7,11,13,17],3,0x2⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],72,0x88a2200aaa208aaa⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],16,0xd397⟩,
  .pool ⟨31,29,[31,19,23,29],[2,3,5,7,11,13,17],136,0x202a082000820a8088a80228aaa28802a2⟩,
  .prime 61,
  .prime 31,
  .pool ⟨31,7,[31,7],[2,3,5],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .pool ⟨31,10,[31,2,5],[3,7],884,0x11111111111109910191111132595111101151011111111115041151111111112190111b11111019111101111109111111111030911119911111010111133111341151189311114511111111011011511111111100111119311112d11101131111011111131015105111193111536⟩,
  .pool ⟨31,23,[31,19,23],[2,3,5,7,11,13,17],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨31,18,[31,2,3],[5,7,11,13,17],80,0x5511415110b19d05335e⟩,
  .pool ⟨61,26,[61,2,13,19,23],[3,5,7,11,17],112,0x1131950bd9b33a5571d14f9db77e⟩,
  .pool ⟨31,22,[31,2,11,19],[3,5,7,13,17],240,0xd12124030410000500100180080912912020030010014000104180490916⟩,
  .pool ⟨31,2,[31,2],[],16,0xd117⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],136,0x11531115159313d185d157559397d553d6⟩,
  .pool ⟨31,10,[31,2,5],[3,7],48,0x1109b2514db6⟩,
  .pool ⟨31,27,[31,3,19,23],[2,5,7,11,13,17],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨31,20,[31,2,5,19],[3,7,11,13,17],75,0x116026c145829b0536⟩,
  .pool ⟨31,7,[31,7],[2,3,5],80,0x82000202000080800082⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,5,0x260000003c80000011000000400000c000000200000054000000578000038000000d00000030000000b0000002800050000000940000000e0000003000001400000040000000c400000008000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 5, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 5 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨0,7,0x0⟩
private def rows120 : List Rule := [
  .pool ⟨31,27,[31,3,19,23],[2,5,7,11,13,17],328,0xa0a822aaa200888028a08a082a888a820002280a00a028800082a222a820a20a280222008aaa882a0a⟩,
  .pool ⟨41,20,[41,2,5,19],[3,7,11,13,17],31,0x121d47b6⟩,
  .pool ⟨41,6,[41,2,3],[5],99,0x7ac8e0d5bc44f223dab07135e⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,2,0x6914⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 2 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+13=13^a*17^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  obtain ⟨i,hi,_⟩ := h120
  exact Nat.not_lt_zero i hi
end D13

namespace D14
private def cfg : Config := ⟨14,2,7,17,1,1,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨17,4,0xbb47b83b0994598198b70774378950554154b3873033491851⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,5,0x40200402004140040100401004010080100801008010040100401004010040200413004020040100401004010080100801008010040100401004010041200402004020040100401004010080100801008010040100401004010804008040080400802008020080201002010020100200802008020080200804008040080400802008020080201002010020100200802008020080200804008040080400802008020080201002010020100200802008020080200080100801008010040100401004010040200402004110040100401004010080100801008010040100401004010040200410004020040100401004010080100801008010040100401004010040f00402004020040100401004011002010020100200802008020080200804008040080400802008020080201002010020100200802008020080200804008040080400802008020080201002010020100200802008020080200804008040080400802008020080200040e004020040200401004010040100801008010080100401004010040100402004020040d004010040100401008010080100801004010040100401004020040c004020040100401004010080100801008010040100401004010804008040080400802008020080201002010020100200802008020080200804008040080400802008020080201002010020100200802008020080200804008040080400802008020080201002010020100200802008020080200080100801008010040100401004010040b004020040200401004010040100801008010080100401004010040100402004020040a004010040100401008010080100801004010040100401004020040900402004010040100401100201002010020080200802008020080400804008040080200802008020100201002010020080200802008020080400804008040080200802008020100201002010020080200802008020080400804008040080200802008020004020040800402004010040100401008010080100801004010040100401004070040200402004010040100401008010080100801004010040100401004020040200406004010040100401008010080100801004010040100401080400804008040080200802008020100201002010020080200802008020080400804008040080200802008020100201002010020080200802008020080400804008040080200802008020100201002010020080200802008020008010080100801004010040100401004020040500402004010040100401008010080100801004010040100401004040040200402004010040100401008010080100801004010040100401004020040200403004010040100401100201002010020080200802008020080400804008040080200802008020100201002010020080200802008020080400804008040080200802008020100201002010020080200802008020080400804008040080200802008020⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨171,6,0x248fb90bbd0dfb113ec4def41fbc47e31075c4acba1f2c8cfbb27ef83fbe33be09efb338c80e3b1b5f80d720f2ec0cbc39e58b79021e7086d615b58e61c09870b55621540e49c15258249a35e5c479105e5cd6da1db5046d71d844461a05844d55a29574d49729250149225e6c679e25b6066d20db6c06d23186c96182556c355b31260349201254ef7823dd48eb80bae0bdf50b7e05d320b4c8bc75171ccdf7013de41f7037acc7eb01f7ccad3c1f4d8dc702b1f01c7a27df43f7a0faf46df70f7dccd3a1b4f49c771b1e80c7b39d7887522da6c869e2d74855db09778551809448845b1516415d92944497510da6806913175065d1194500511011445f3a0bcd08e7d179dc2e772f6c48dba176e8ecf42f3dc5cf73b0c4bc3a230ecaf3807ce0ae721f9ec4e7b376c81db8373c8acfb1f3f81cf2130ec1c3c0fcd80f3c339d89e701b9f06db60f6c00db6333f00cfc270d86c3a39c5c571739968865d09974b59a09668b4dd3905cb41835c48a7153594846551d66015982935414d529060441⟩
private def rows60 : List Rule := [
  .pool ⟨61,9,[61,3],[2,5,7],45,0x108805020a⟩,
  .div 11,
  .pool ⟨31,7,[31,7],[2,3,5],793,0x12d020a252081880644c112020006092460020080020180882a080f008c000022017044708b2850016000655a08040086844885840080416a98001a0028534438883a01100000c403c0415044060100040100189241800101220c8980460412914102d2⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,7,[31,7],[2,3,5],549,0x82080002000012080080490090000012010000080000000000082002090002000000480092400080082002412000410482012080010090480000080010002082090010092⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],819,0x40904001001020008009008044001040008244000000001000001000000000800005000049005104000004a00000040000008000100000020000005200000208a00920000a0000100000000080000080000000022410002080022010090010004080080020902⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],117,0x509d474f8985b8c7bb134b559f7e⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],651,0x20a0522084922020090934c341b24221a2002d04810800d100a0412402c021300204a65a2000900c02986824db2000892936012982c905960a6502d26584102cb08221820301041060b28b0924422912832⟩,
  .pool ⟨31,10,[31,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,6,[31,2,3],[5],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],45,0x55898f135e⟩,
  .pool ⟨31,10,[31,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,10,[31,2,5],[3,7],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,6,[31,2,3],[5],45,0x55898f135e⟩,
  .pool ⟨61,10,[61,2,5],[3,7],75,0x116026c145829b0536⟩,
  .pool ⟨61,9,[61,3],[2,5,7],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,9,[61,3],[2,5,7],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,9,[31,3],[2,5,7],45,0x108805020a⟩,
  .pool ⟨31,4,[31,2],[3],63,0x6880800180010116⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩,
  .pool ⟨61,10,[61,2,5],[3,7],775,0x6ca08954c1832225a016805a4c0c18368910536d9411229830e044b442d00b6881831651220a6db2862453060c0897805a01e9103060ca24614db650448a68c18116d00b422d22070c19448829b6ca08916c1830325a016805a444c1832a910536⟩,
  .pool ⟨31,27,[31,3,17,19,23],[2,5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨31,9,[31,3],[2,5,7],9,0x9b⟩,
  .pool ⟨31,5,[31,5],[2,3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,27,[61,3,17,19,23],[2,5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨61,9,[61,3],[2,5,7],9,0x9b⟩,
  .pool ⟨31,4,[31,2],[3],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],225,0x108815020b088440ac10580622014182c031900a04560108a05822b⟩,
  .pool ⟨31,9,[31,3],[2,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,4,[31,2],[3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,5,[31,5],[2,3],1281,0x1b28221060300800a0002800020000032000000522000000002100000000002930010010100000886020000000400000000020080000000000010000100022082800000800000c000800000000021200b4012100000000004000c00000400000504110002000020000000000004010000000000800000010184400002020020032500000000002100000000112800000130000010000500014004030182110536⟩,
  .pool ⟨61,10,[61,2,5],[3,7],325,0x1b282210302018116d1430001a000809b68808802d0044045b6404001600030a2da206010302110536⟩,
  .pool ⟨31,26,[31,2,13,17,19,23],[3,5,7,11],61,0x1ffffffffffffffe⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,8,0x101190101010101011b01cf01010101010115011a0101010101010115011a010101010101190101010101011701ce0101010101010117011601010101010115011a0101010101011901011a0101010101011901010101010117011d0101010101011501011601010101010115011a010101010101190101010101011c010101cd011501010101010114010101010101cc011001010101010101cb0117010101010101ca01150101010101011401011501010101010114010101010101c901170101010101011601011701010101010118011501010101010114010101010101c8010114010101010101c701c60101010101011601150101010101010101c501c40101010101012201c3010101010101210101c2010101010101c101010101010120011f010101010101170101c00101010101011701160101010101011e010101010101bf0101210101010101012001be0101010101011701bd010101010101011b01160101010101011e010101010101bc01bb010101ba010101010101b9010101010101b8010c0101010101010b0101090101010101010b01b7010101010101b60101010101010a0101b50101010101010a01090101010101010b01b4010101010101010b01b3010101010101b20101010101010a010c01010101010101b101090101010101010b01b0010101010101af010101ae0101010101010c0112010101010101ad010101010101ac0101ab0101010101011101aa010101010101a9010d0101010101010109010d010101010101a8010101010101a701a601010101010101a501a40101010101010c010d010101010101110101a3010101010101a201010101010113010a010101010101a10101010d010101010101a0019f0101010101010f010c010101010101010f019e0101010101019d0101010101019c019b010101010101019a01990101010101010f010e0101010101010d01010c010101010101980101010101011001970101010101010f0101960101010101010f010901010101010195010101010101940101019301020101010101019201010101010104010301010101010101040103010101010101910105010101010101900101020101010101018f0101010101010001030101010101018e0101030101010101010001050101010101018d0101010101018c0101000101010101018b01060101010101018a0105010101010101018901040101010101010301010101010188018701010101010101860105010101010101850104010101010101030101100101010101010301010101010184010501010101010124010105010101010101830182010101010101030101010101011001018101010101010180010501010101010123017f010101010101010103017e01010101010105017d010101010101040101080101010101010401010101010106017c0101010101010501010701010101010105017b0101010101017a0101010101010301017901010101010106017801010101010102010701010101010101050177010101010101760101010101010301750101010174010101010101170173010101010101210101010101012001011e0101010101017201710101010101011b011601010101010101220170010101010101210101010101016f016e0101010101010120011f01010101010117016d0101010101016c0101160101010101011e0101010101016b016a0101010101011701011d01010101010115011a01010101010119010101010101170101190101010101011c011601010101010115011a0101010101010115011a010101010101190101010101011b01690101010101010117016801010101010115011a0101010101011901011a01010101010119010101010101170116010101010101150101011401010101010167011701010101010118011501010101010101160115010101010101140101010101016601650101010101010164011001010101010163011501010101010114010115010101010101140101010101016201170101010101016101011701010101010116011501010101010114010101010101600101010c010d010101010101110101010101015f015e0101010101010113010a0101010101015d015c0101010101015b0101120101010101015a0101010101015901580101010101010c01015701010101010156010d010101010101550101010101011101015401010101010153015201010101010109010d01010101010101011001510101010101010f010c010101010101500101090101010101014f0101010101014e014d0101010101010f01014c0101010101010f010c0101010101010d0101010101014b01014a0101010101014901480101010101010f0147010101010101010f010e0101010101010d010101010101460145010101010101010a010c0101010101010b014401010101010143010142010101010101410101010101014001090101010101010b01010c0101010101010b013f0101010101013e0101010101013d01013c0101010101010a01090101010101010b013b010101010101010b013a010101010101390101010101010a010901010101380101010101010201070101010101013701010101010106010136010101010101030135010101010101050134010101010101010501330101010101010401010101010103013201010101010101060131010101010101050108010101010101040101300101010101012f010101010101030107010101010101050101012e0101010101012d0103010101010101000105010101010101012c0105010101010101000101010101012b0106010101010101010401030101010101012a01020101010101012901010501010101010128010101010101040103010101010101270101030101010101012601020101010101012501010101010100⟩
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
private def keys180 : Keys := ⟨52,8,0x40895d7c89217cad8d40ad1598a7975ca71f8437af0c37734837373c13af78137300133778afa30037a300af673c37673caf2b78372b485ba3845b670c5b2b789797785b97781f973c1f9700975b005b5b781f5b3c971f3c5b1f001f1f84a38b48678b0ca34f84674f0c674f48a3130c671300a37f3ca34378a307a4b1712cb135a445952c455958839f9483631c83271ca79358a75794a71b1c3b03⟩
private def rows180 : List Rule := [
  .pool ⟨19,15,[19,3,5],[2,7,11,13],481,0x1fba6e34e2a13996a02730197b0f08f3604424ad7c451b0cba2c06a81652fd29a05580d174c36288fad490881b3c43c37a60339015a672151cb1d977e⟩,
  .pool ⟨19,2,[19,2],[],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,6,[19,2,3],[5],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨37,12,[37,2,3],[5,7,11],95,0x102450d207310b30d453b5e⟩,
  .pool ⟨19,6,[19,2,3],[5],135,0x116063c45780ab131626bc055898f135e⟩,
  .pool ⟨19,6,[19,2,3],[5],837,0x510cd194687c91b19d5f604aac7485a7c1a5ad9caadf105c67266c1e9d654cf75ff800a319a328f0f9236738bec09558e91b4f834b5a3955fe20b8ce4cd83d3aca99eebff005443346d1a1f256c6717f812ab1d2169f0e96b473ab7c41719c99b47a7595b3dd7fe⟩,
  .pool ⟨19,15,[19,3,5],[2,7,11,13],427,0x54419250004488602030c2014002001403c28008015210980224000244019084a80100143c02800400280430c04061122000a49822a⟩,
  .pool ⟨19,15,[19,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨19,2,[19,2],[],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,2,[19,2],[],481,0x1a206404e0801082a00200100802002360000020000018000200002014503028a010000100006000001000001b10010040200100150420041c8098116⟩,
  .pool ⟨19,2,[19,2],[],31,0x121d47b6⟩,
  .pool ⟨31,20,[31,2,5,17],[3,7,11,13,19],399,0x100300044a0114106120c80006122102512d060904a0d14504102816490802410d32120db24069009344348905a6132536⟩,
  .pool ⟨19,2,[19,2],[],275,0x688090048210002084080200010008108060108100080004010210400084120090116⟩,
  .pool ⟨19,18,[19,2,3,17],[5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨19,4,[19,2],[3],31,0x121d47b6⟩,
  .prime 19,
  .pool ⟨19,4,[19,2],[3],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,4,[19,2],[3],275,0x688090048210002084080200010008108060108100080004010210400084120090116⟩,
  .prime 181,
  .pool ⟨19,6,[19,2,3],[5],37,0x1ffffffffe⟩,
  .pool ⟨19,15,[19,3,5],[2,7,11,13],837,0x510cd194687c91b19d5f604aac7485a7c1a5ad9caadf105c67266c1e9d654cf75ff800a319a328f0f9236738bec09558e91b4f834b5a3955fe20b8ce4cd83d3aca99eebff005443346d1a1f256c6717f812ab1d2169f0e96b473ab7c41719c99b47a7595b3dd7fe⟩,
  .pool ⟨19,6,[19,2,3],[5],1647,0x5230c1b04f5038b5025fe37001bd19e77544d26efa91e2e5450128ba30796e96b6e672425e2186ce8beddd756ac5da8326537544709d09fdc5e016bd639fdc37c9f2ced782b19605867a81c52852df0b8809eacf3b2a66b377dc8f172b288945f193c370b7b7331252f11c3e705d6feb2b162ec4113699ab2384a86ffe2f04b7eb1c7ee19e5f9e72bc158cb06c33c4062d4297f8dc406f5671dd53359b3ee458a95944482f8c9e5ba5bdb19c929688e1f3a2fb7f5d5ab076a0c9b4dd591827437ff13825bf50e7f50df2fcf3b5e⟩,
  .pool ⟨31,29,[31,17,23,29],[2,3,5,7,11,13,19],1443,0x25800a08a21225361245a4c32510910484824190430d00802194086934d92c82030d26d10820186882c00904da20029b20a44809320b0110c00c004924104a20a0502800d20404802d32012da41a00324a41128b25349b0800032136d260041020a25308901968340021a2102ca4d16906d82d028b2892590496d865861360b20264148b20029a2804d22d80ca0c360a6100906032c02404100ca4432d82d041964241a48965264121048109101029308a28b4c12⟩,
  .pool ⟨31,29,[31,17,23,29],[2,3,5,7,11,13,19],247,0x40a9631d5030001191249040ed0100a50080b70209248988000c0ab8c69502⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],133,0x161f2054da76220c210c111b96ca813e1a⟩,
  .pool ⟨19,15,[19,3,5],[2,7,11,13],675,0x700008220001124040180808062b0002006001100400820488c02010300416100000c800200c00040b110041202208ac000041800460100018120308804044105802000301088020801024460100a08822b⟩,
  .pool ⟨19,6,[19,2,3],[5],31,0x7ffffffe⟩,
  .pool ⟨31,6,[31,2,3],[5],135,0x116063c45780ab131626bc055898f135e⟩,
  .pool ⟨31,6,[31,2,3],[5],297,0x1eb238356f103c88b6ac1c457bd646062de227911ed18189af7a88e0d5b444f023dab07135e⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨31,6,[31,2,3],[5],189,0x1eb22824620160c5b4605009e402818b68c1a0118905135e⟩,
  .prime 37,
  .pool ⟨31,6,[31,2,3],[5],481,0x1fba6e34e2a13996a02730197b0f08f3604424ad7c451b0cba2c06a81652fd29a05580d174c36288fad490881b3c43c37a60339015a672151cb1d977e⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],93,0x124c345b00221100368b0c92⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],549,0x158cb06c33d40e2d4297f8dc406f5679dd53359bbee478b959444a2f8c9e5ba5bdb99c929788e1f3a2fb7f5d5ab176a0c9b4dd591c27437ff17825bf58e7f70df2fcf3b5e⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],279,0x5463346d1e1f256ce757f812ab1d2369f0e96b673abfc41719c99b47a7595b3dd7fe⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨37,9,[37,3],[2,5,7],27,0x8060b⟩,
  .pool ⟨37,9,[37,3],[2,5,7],61,0x1434026619900b0a⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],259,0x30a92334e3d1b04a00d110ac04ae5a20abb2408dbc2e750bf2cf07010c31b2a72⟩,
  .pool ⟨61,27,[61,3,17,23],[2,5,7,11,13,19],351,0x5040c31002809186240540030c082a8006188054048c31202a01186001541030c002a0246189014008c3020a⟩,
  .pool ⟨61,27,[61,3,17,23],[2,5,7,11,13,19],135,0x116063c45780ab131626bc055898f135e⟩,
  .pool ⟨61,29,[61,17,23,29],[2,3,5,7,11,13,19],1267,0x42a043140f048c0cc11080041f04401c48f524103e3ad0886044138b0abc4102401b1414e18080aa00036420499226098372004084a14114343410528884032484986020000600840024208e2c643402c263471042400210060000406192124c021114a082c2c2882852102004ec1906449920426c000550101872828d80240823d50d1c82206110b5c7c0824af12380220f820010883303120f028c20542⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],185,0x2900000480214212802020424280a00840429025294802⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],217,0x102e4c05010003003610e1a232848531161c21b00300020280c9d02⟩,
  .pool ⟨31,10,[31,2,5],[3,7],481,0x1fba6e34e2a13996a02730197b0f08f3604424ad7c451b0cba2c06a81652fd29a05580d174c36288fad490881b3c43c37a60339015a672151cb1d977e⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],481,0x1fba6e34e2a13996a02730197b0f08f3604424ad7c451b0cba2c06a81652fd29a05580d174c36288fad490881b3c43c37a60339015a672151cb1d977e⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],31,0x7ffffffe⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],189,0x1eb22824620160c5b4605009e402818b68c1a0118905135e⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],1647,0x7bcaa4998c34c68380a15a64b529940ec150d84732982824ca2708c3c27410ecb4133300a6d5243b0e0cc3d148805961b1884c3a45c0b45ab0192b340745a8a0ce60170e5b4e1500dc68a2361d250a9b01b944a4f40aa6527190c14022d339468e53808564a41bd82526a101ca71629ccb440283098e4a65502f25229d80d950a4b86c45163b00a872da70e806730515a2e02cd4980d5a2d03a25c32118d869a01128bc33070dc24ab6500ccc82d37082e43c310e4532414194ce21b0a83702994ad265a8501c1632c31992553de⟩,
  .pool ⟨37,9,[37,3],[2,5,7],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨37,19,[37,17],[2,3,5,7,11,13,19],9,0x102⟩,
  .pool ⟨19,15,[19,3,5],[2,7,11,13],775,0x30006ad083210000120a6098400a84202c420094210002008040284230002822163001804840100491000a208021000210802a094210042104101084630802108629000208843108021088800070008022084010802b0a52120420000a18822a⟩,
  .pool ⟨19,2,[19,2],[],819,0x6880904082102000800802004800000090000080000800002084100004000000820000000100900000000080004000000804806012010000002000100000000090080000000410000002000082104000010000100000900000012004010010004084102090116⟩,
  .pool ⟨31,5,[31,5],[2,3],181,0x11e0049dc628b42426480880440499090b4518ee4801e2⟩,
  .pool ⟨181,9,[181,3],[2,5,7],27,0x8060b⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],37,0x1ffffffffe⟩,
  .pool ⟨31,27,[31,3,17,23],[2,5,7,11,13,19],135,0x116063c45780ab131626bc055898f135e⟩,
  .pool ⟨37,12,[37,2,3],[5,7,11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,23,[61,17,23],[2,3,5,7,11,13,19],1267,0x42a043140f048c0cc11080041f04401c48f524103e3ad0886044138b0abc4102401b1414e18080aa00036420499226098372004084a14114343410528884032484986020000600840024208e2c643402c263471042400210060000406192124c021114a082c2c2882852102004ec1906449920426c000550101872828d80240823d50d1c82206110b5c7c0824af12380220f820010883303120f028c20542⟩,
  .pool ⟨37,31,[37,17,23,29],[2,3,5,7,11,13,19,31],285,0x1201b0c101105225a64104b21048021040140a0082100482134820996912822020c36012⟩,
  .pool ⟨37,12,[37,2,3],[5,7,11],513,0x1eb3286c2345a2806528d18a34264141b0cc32168c5b4625299460b0d00d850a794286c02c3418a652918b68c5a130cc360a0990b1462c529805168b10d85335e⟩,
  .pool ⟨31,9,[31,3],[2,5,7],481,0x143002244080080620201001400c080100040080244112002208002800108420005000411001220890040080020040c00a0020101180400408910030a⟩,
  .pool ⟨31,9,[31,3],[2,5,7],27,0x269369b⟩,
  .pool ⟨31,4,[31,2],[3],481,0x1a206000e0000002a000000000000022200000000000000000000000101030202000000000000000000000001110000000000000150000001c0018116⟩,
  .pool ⟨181,5,[181,5],[2,3],25,0x210863⟩,
  .pool ⟨37,12,[37,2,3],[5,7,11],1395,0x7adcb2b4cf19ca61a0ea43c2b09d6d43c805b8c8605eb00c8a01d2b338e3311ae4940423cec0a0c5690472ad8e5150f495884106a71ccb5a4ad5bc4e5b12439ced30d2740561194aa4a8e0109c44b067788644246b589cf391ad62422611ee60d223908071525529886a02e4b0cb739c248da723dab525ad338e5608211a92f0a8a71b54e2096a3050373c4202927588cc71ccd4b8051300d7a06131da013c2b6b90d43c25705865398f32d4d3b5e⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],703,0x20800200800000000010008001000020800000000004000000000010000020000040000000080020000000008400000200000008000200010010000000804000800100002040000002000000000000012000100000010812⟩,
  .pool ⟨181,26,[181,2,13,17,23],[3,5,7,11,19],1767,0x420080410910524524086424526182432182400812830496136182806c00c200a0d068009241141804208801b0134d368124a29169009904169b44100a41905048801a2102984500182582516532112d00424190584c004169a44125b21b61a2c80424d34990992022c82114196920024532c828b2424420104996402820032012590800516d84816414996902532010412c10c36d14c225328264a4d164208b6514020596402d201228125a0004134036c86996434124926da0d028b6806d80da0c101300961a25a6492c30182c30914190ca4910916522516c36996⟩,
  .pool ⟨31,20,[31,2,5,17],[3,7,11,13,19],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨37,8,[37,2],[3,5,7],549,0x1a60a00261041120a0084490094824032014120184820800120982106094002924004c800925000a41821064120004104860120a01300904a4024884014122082190014196⟩,
  .pool ⟨19,11,[19,11],[2,3,5,7],775,0x405010200002000000004a4090000840000404000010000000084010002000400004204200000020001000002040000000000002040000080004000000420420000200040008021000000008000020200002100009025200000000400004080a02⟩,
  .pool ⟨61,39,[61,3,13,17,23,29],[2,5,7,11,19,31,37],855,0x584ee3140d61da97bd8453c851290c530054b84a28c0532ccf6986e5a56a18c8a79d894ad0763c222a0e44bdc830d6661908421a4381c258421098666b0c13bd227054443c6e0b5291b9e5131856a5a76196f334ca0314521d2a00ca30948a13ca21bde95b86b028c7721a⟩,
  .pool ⟨37,6,[37,2,3],[5],1629,0x15ccf87d2ab00bfd822336d15432febca5060713c6cf2dd0dc9c46836bea76fc770dd50e411e90d2ed5e2d6fd639edd178f975ec0c1b3553db72bf764bdf3abd1a9ec478b9d9d46a1d4495fa24d42d863a2dd9eb43289e6fad8e13a5bb79ad949ff47ff1ca99eb3c107c05b79398c8d6acf39a8663bbcfca5932f8ef96f737e895f771fa7d1d1ab177a1e9f0b8c90f6641acc94d74d9fbf6165938dd5238b50a56e3532dbde1ff73dd17c67124ea4a6fb779b53f11c3a74de7f7deb4a22df5dd64eeff980ffeabd0f87335e⟩,
  .pool ⟨37,8,[37,2],[3,5,7],171,0x6884812084120800902106084090010482104812116⟩,
  .pool ⟨37,6,[37,2,3],[5],513,0x1eb3286c2345a2806528d18a34264141b0cc32168c5b4625299460b0d00d850a794286c02c3418a652918b68c5a130cc360a0990b1462c529805168b10d85335e⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],259,0x30a92334e3d1b04a00d110ac04ae5a20abb2408dbc2e750bf2cf07010c31b2a72⟩,
  .pool ⟨37,8,[37,2],[3,5,7],465,0x1a25248921865208201a00b08825125060004a2010132c02020034884c30c844b0010100d32020114800182922904434016010412986124492916⟩,
  .pool ⟨37,8,[37,2],[3,5,7],95,0x102450d207310b30d453b5e⟩,
  .pool ⟨37,8,[37,2],[3,5,7],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨37,8,[37,2],[3,5,7],543,0x5321a0d028800b64008849045049b2d20410184d12182502526112092da0db61941344300068024b2530912d10c32504c36596902024d14d24ca6d900b6ca2d06832116⟩,
  .pool ⟨37,6,[37,2,3],[5],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,7,[31,7],[2,3,5],181,0x11e0049dc628b42426480880440499090b4518ee4801e2⟩,
  .pool ⟨37,6,[37,2,3],[5],1647,0x7bcaa4998c34c68380a15a64b529940ec150d84732982824ca2708c3c27410ecb4133300a6d5243b0e0cc3d148805961b1884c3a45c0b45ab0192b340745a8a0ce60170e5b4e1500dc68a2361d250a9b01b944a4f40aa6527190c14022d339468e53808564a41bd82526a101ca71629ccb440283098e4a65502f25229d80d950a4b86c45163b00a872da70e806730515a2e02cd4980d5a2d03a25c32118d869a01128bc33070dc24ab6500ccc82d37082e43c310e4532414194ce21b0a83702994ad265a8501c1632c31992553de⟩,
  .pool ⟨37,29,[37,17,23,29],[2,3,5,7,11,13,19],285,0x1201b0c101105225a64104b21048021040140a0082100482134820996912822020c36012⟩,
  .pool ⟨37,29,[37,17,23,29],[2,3,5,7,11,13,19],61,0x1ffffffffffffffe⟩,
  .pool ⟨37,19,[37,17,19],[2,3,5,7,11,13],305,0x1200bc4011401120662218830001000006000303000180000200030461119812200a2008f4012⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],703,0x4410302402041a100820000800241288020040840c1100010094010008200218c081104800002000806100a442024400000240008225010610000481480000090280a000800312402180010000014810100184412916⟩,
  .pool ⟨37,19,[37,17,19],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨31,6,[31,2,3],[5],1197,0x100804120100c50d2050080402c18c42c820118901125451914026900b0680812682442014081a424d001c482098858c0a090c904120a74904027900a24102004824a2012494816450498402410b30c020928805114ed5824120120a06048b06804320124903920d009008201261ac920914804035af09040221209049143040049241608731201049648249835049a091c905935e⟩,
  .pool ⟨37,27,[37,3,17,23],[2,5,7,11,13,19],1755,0x22823295a03302c020a87184a72c0a2bd6e621262198308d261042c2bc0272500485071086e5a5473bd8442ce0230e35b4c328da17a0ce020412a1e2029494a8ee5b0ac4988429c62691610942d4198060901438c25b920514eb7350b310cc18449308a1215e01312c004283880372d2a39dee23167011a70ada65946d0b502721020950f3004a4a14773d8d624e4314e35348b08ca56a0cc0b0482a0c612dcb028af5b9a85980620c23490450b0af009c960121418421a96151ccf7118b3808d38d6932ca3605e833908100a87980a5252a2b9ec6b127218a31a9a⟩,
  .pool ⟨31,6,[31,2,3],[5],1647,0x7bcaa4998c34c68380a15a64b529940ec150d84732982824ca2708c3c27410ecb4133300a6d5243b0e0cc3d148805961b1884c3a45c0b45ab0192b340745a8a0ce60170e5b4e1500dc68a2361d250a9b01b944a4f40aa6527190c14022d339468e53808564a41bd82526a101ca71629ccb440283098e4a65502f25229d80d950a4b86c45163b00a872da70e806730515a2e02cd4980d5a2d03a25c32118d869a01128bc33070dc24ab6500ccc82d37082e43c310e4532414194ce21b0a83702994ad265a8501c1632c31992553de⟩,
  .pool ⟨37,27,[37,3,17,23],[2,5,7,11,13,19],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,29,[31,17,23,29],[2,3,5,7,11,13,19],1463,0x425082205d50c081122a62200a1549443064c1d892c180805408c063661c231210a042825b053e6849618f1438541d01036744195a0112d4a687906a5180e42191201cc4024189048338f51261aac39d121832806d5bb56200f91323003f20502001e692a7124038226985102034da264d939c46e9705388d23428541a8244853d2425d1102f5e035441c300690d21024d01b0ad5aa73431839028dc8f50f87a6424c42c50f0d945038f3328a8b336c4d4015ab87135e⟩,
  .pool ⟨37,34,[37,2,17,23,29],[3,5,7,11,13,19,31],1209,0x1b2832512930d90c225929028a48069121209b49220804320221960045a6190c205960161b6982092024020404d129201160201a08b44040809a61b04a4d068024009a08a41008b04b28b20b4134534834402094416400900582c948361964040808b44160101a2012522c808100901241065b61a01a6810c261968801a61101308041124b6412122580494502526910c26c32522930536⟩,
  .pool ⟨37,16,[37,2],[3,5,7,11,13],543,0x5321a0d028800b64008849045049b2d20410184d12182502526112092da0db61941344300068024b2530912d10c32504c36596902024d14d24ca6d900b6ca2d06832116⟩,
  .pool ⟨37,29,[37,17,23,29],[2,3,5,7,11,13,19],1209,0x1b2832512930d90c225929028a48069121209b49220804320221960045a6190c205960161b6982092024020404d129201160201a08b44040809a61b04a4d068024009a08a41008b04b28b20b4134534834402094416400900582c948361964040808b44160101a2012522c808100901241065b61a01a6810c261968801a61101308041124b6412122580494502526910c26c32522930536⟩,
  .pool ⟨31,9,[31,3],[2,5,7],999,0x10020002000800c000000a2000010004002000100500080084000090000802000020420000082802010000102000004404000080110010000022000000c008004800200104000060000805001000800140100000028000804200200800008900000021000004040040820001100020020200004008008800020a⟩,
  .pool ⟨31,9,[31,3],[2,5,7],1525,0x141000866080000008181a0321481a000000c04080c1008600802004800284c21001225020004100848004860008000000000000000900408109001812000d02005001048c021294000408c800302100000011880008b0182308801019400a001400a60200443106034400046200000021030004c408000a52100c48200280102c00120600242040802400000000000000040018480048402080010291200210c8500048010040184020c04080c000001604a130160604000000419840020a⟩,
  .pool ⟨37,16,[37,2],[3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨37,34,[37,2,17,23,29],[3,5,7,11,13,19,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,9,[31,3],[2,5,7],247,0x7ac8a0918840830680847404810a013c805081202e210160c102118905135e⟩,
  .pool ⟨37,16,[37,2],[3,5,7,11,13],465,0x1a25248921865208201a00b08825125060004a2010132c02020034884c30c844b0010100d32020114800182922904434016010412986124492916⟩]
private def step180 : Stage := ⟨cfg,60,3,keys60,keys180,rows180,8,0xf10120f10120f101210120f10120f10120f120f10120f10120f100d0f110d0f110d0f110f110d0f110d0f110d110d0f110d0f110d0f0c1f020c341f1f19021f040c191f0c34021f020c1f1f0c34041f34020a1f1f0a07021f070a1f040a071f1f07021f020a071f0a07041f1f020a191f0a34041f020a1f1f0a34021f190a1f040a191f1f19021f0c07041f07020c1f0c071f1f07020c1f02071f0c07021f1f040c0a061f1f06020a1f04061f0a06041f1f020a1f0a06021f06020a1f021f07020a1f1f0a071f07020a1f040a071f07041f1f020a071f0a25041f1f020a371f0a021f19020a1f1f0a371f25020a1f040a191f191f0834041f1f02081f0834021f1902081f08191f1f1902081f041d213f6621631d213e213e1d216266213f1d3e1d213f3f213e1d21232b61232b39232b5f2b39232b64232b5f2361232b64232b39232b436723435f234361236723435f234361234323436723435f234361232b64232b5f232b612b64232b5f232b612364232b5f232b61232b214023214023214023402321402321402321232140232140232140246423245f2324392364232439232461232423243923245f232461213f1d213e1d2162663e1d213e1d213f3f211d213e1d213f66215f232b65232b61232b392b65232b39232b642339232b61232b64232b246123246423245f236123246423245f232423246123246423245f3e1d213f22213e1d211d213f2221631d213e213e1d216222213f1d61234360234339234323436123433923435f433923436023435f2318010602010604010601060501060401061806040106020106050101070401075e010702071601075e010704011601070401070201071c1a0a1b1a0a001a0a1a0a1b1a0a191a0a000a191a0a1c1a0a001a070201070501070401020107040107180107010704010718010705040c07020c07150c070c075e0c07020c070407150c07040c07160c00150c17040c14160c040c00020c14150c140c005e0c14020c1704010718010705010704070501070401070201040107180107020107040c07180c07020c070c07180c07050c070407050c07040c07020c01060201060401065e060401061601065e010201061601060401060a071a0a071a0a071a071a0a071a0a071a0a1a0a071a0a071a0a0700040c19020c18050c180c00020c18040c180c00050c18040c191816010704010702010701070401075e010702071601075e010704012022211e1d211e222122211e1d211e22215c211e2221201d211e2224582224581d245822582224581d245822242224581d24582224581623245d232416232423241623245d232416241623245d23241623222b581d2b58222c582b58222b581d2c582258222b581d2b58222c21201d211e22211e221e1d211e22212022211d211e22215c22211e2d23212d232157232123212d23212d232157212d23212d23215723581d245818245818241d245818245818245824581d24581824581823245b232416232416249b232416232416239a232416232416232422215c22211e1d211e211e22211e2221201d1e22212022211e1d2199232416232416232423245b2324162324162498232416232416231e1e21205a211e1d212021591e211e1d211e211e1e211e1e21201d302f24312f24302f242f242e2f24302f243024302f24302f24312f2224582224581d245824582224582224581d582224582224581d245723212d23212d232123215723212d23212d215723212d23212d230f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f110d0f110d0f110d110d0f110d0f110d0f0d0f110d0f110d0f110e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f04010755010702010701070201070501070407020107040107020109065508060209060406050906040806020904090602080602090600040119020134020156010002013404013401000501340401190202010702010704010701070201070401075507040107020107050197040119020100050102011902015604010001960201560401005601060401060201060506020106020106040102010604010655010601060401065501060206020106050106040102010604010602010606020a06040a060b0a040a06020a06050a060a06020a06020a06040a07020a07020a070407020a07040a070b0a040a07020a07050a0706020c06040c06020c040c06550c06020c060c06020c06050c06044c49214e1d21954b214921541d214e4b2194214c49214e1d21934b244c2224501d249222542224501d2491222422244c1d24502224902153232153232153235323215323215323212321532321532321538f244c1d24514b248e244c8d24511d248c4b528b24511d248a4b2421501d218922214c22501d218822214c22211d215022218722214a861d2b854b2b84834f1d2b824b2b81804f4c2b7f1d2b7e4b4f4c7d7c4b214c7b214e1d214b217a7921781d214e21774b214c76214e1d461d2b460b2b460b461d2b460b2b460b46462b461d2b460b46460b4d4d214d1d214d4d214d214d1d214d4d214d214d4d214d1d214d4d4b2b7549484c1d2b472b744b484c492b471d734b2b4a4948471d2b24462224462224461d462224462224461d242224462224461d24461f0f100d0f100d0f1f0f101f0f100d0f1f0d101f0f100d0f1f0d0f0f100d0f1f0d0f101f100d0f1f0d0f101f0f0d0f100d0f1f1f0f10100d0f1f0d0f101f0f0d0f100d0f1f1f0f100f100d0f1f0d0f101f1f0d0f101f0f100d0f0d0f1f1f0f100d0f100f1f0d0f101f0f100d0d0f0e0d0f1f1f0f0e0f0e0d0f1f0d0f0e1f0e0d0f1f0d0f0e1f0f120d0f1f0d0f121f0f0d0f120d0f1f1f0f120f120d0f1f0d0f121f0d0f1f1f0f120d0f120f1f0d0f121f0f120d1f0d0f121f0f120d0f1f0f110d0f110d0f1f0f111f0f110d0f1f0d111f0f110d0f1f0d0f0f1f0d0f0e1f0f0e0d1f0d0f0e1f0f0e0d0f0d0f1f1f0f0e0d0f0e101f0f100d0f1f0d0f1f0f100d0f100d0f1f0f101f0f100d0f1f0d2c39232b3d232c3c3872232c42232b39382c232c71232b39382c3c3d23243c382445232423243a38243c232445243d23243c3824452338213e1d213e1d213f213e38213f1d213e1d3f38213e1d213e1d2123433938433c234344433d23433c3843392342234339384344234338433c234344234342433c38434423433d233c38434423433d23433e1d213e1d213f38211d213e1d213f38213e213f1d213e1d213e3839382c70232c42232b382c3c232c6f232b392c3c382c39232b3d2341232c3d232b3c382c232c41232b42382c3c2c41232b3d232c3c383821402321402321402140382140232140234038214023214023211d213f38213e1d213e213e1d213e38213f1d3e1d213f38213e1d2123243b23243938243c243923243d23243c383b23243a2324393824120f10120f10120f100f10120f10120f101210120f10120f10120f110d0f110d0f110d0f0d0f110d0f110d0f110f110d0f110d0f110d0a07040a07020a070207330a07020a07040a150a07040a07020a07040a37020a00150a000a19020a00020a000437020a00040a00330a15090004353402080009000435190208000200360919023500040807020a07040a07330a040a07020a07330a070a07020a07020a0704040c00330c00020c340c00020c00050c340400020c00040c19020c0a00020a00040a190200040a00330a19020a020a00150a00040a3407040c07020c07020c330c07020c07040c070c07050c07040c0702330a06040a06020a060a06040a06020a060206330a06020a06040a231f3223241f1f24161f2523241f2324161f32231f1f2324161f241f211e1d1f201e211f21201f1f1e1d211f1e1e1f211e1d1f1f202123211f1f212d231f32211f23212d1f1f32231f23212d1f2125231f2f1f302f241f1f24301f312f241f2f24301f302f1f1f2f242e1f24246e1f1f271d241f226d1f24271d1f1f22241f246c1d1f2722241f1f246b1d1f2722241f246a1f1f271d241f22691f24271d1f1f2224241f2324161f1f25231f2324161f2426231f23241f1f2416231f261f1e1d211f2221201f1e1d1f1f22211e1f211d1f2022211f1f211e1d1f2022211f1f211e1f1e1d211f2221201f1e1d1f1f22211e1f21212d1f1f2623211f232d1f2125231f1f23211f212d231f2623211f271d1f1f222c2a1f2b1d1f27222c1f1f2b2a1f271d2c1f222b2a1f1f271d241f1824291f271d1f1f1824281f241d1f2718241f1f2468161f2426231f1f23241f2416231f2623241f24161f1f2523241f231f22211e1f211e1d1f22211f1f211e1d1f20211f2221201f1f1e1d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0d0f110d0f110d0f110f110d0f110d0f110d110d0f110d0f110d0f0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0c07130c07180c070507130c07050c07040c130c07040c07180c07061601061301061601040106130106160106010616010613010604130c00040c18180c000c00130c19180c000500130c18050c00040c010716010713010704071601071301071601040107130107160107071a0a071a0a071a0a1a0a071a0a071a0a070a071a0a071a0a071a0605010604010613010401061801061301060106180106050106131301071601070401070107130107040107160713010716010716010a001a0a001a0a1c1a001a0a001a0a1b1a0a1a0a001a0a001a0a1907130c07160c07150c130c07150c07040c070c07130c07040c07160107050107130107180704010713010705011801071301070401071801071301070401070107050107130107180704010713010705010c17040c00160c001314160c00150c00130c150c14040c00130c000f120d0f120d0f120d120d0f120d0f120d0f0d0f120d0f120d0f120d0f120d0f120d0f120f120d0f120d0f120d120d0f120d0f120d0f0e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d0d0f100d0f100d0f100f100d0f100d0f100d100d0f100d0f100d0f0f110d0f110d0f110d110d0f110d0f110d0f0d0f110d0f110d0f110d0f100d0f100d0f100f100d0f100d0f100d100d0f100d0f100d0f100d0f100d0f100d0f0d0f100d0f100d0f100f100d0f100d0f100d0f100d0f100d0f100d100d0f100d0f100d0f0d0f100d0f100d0f100f100d0f100d0f100d100d0f100d0f100d0f0d0f100d0f100d0f100e0d0f0e0d0f0e0d0f0d0f0e0d0f0e0d0f0e0f0e0d0f0e0d0f0e0d060201060401060201040106030106020106010602010605010604020a06020a06040a060a06020a06040a060b06040a06020a06050a020c06050c06040c060c06020c06040c060206040c06030c06020c07020a07050a07040a020a07040a07020a070a07040a070b0a0702070301070201070401050107040107020107010704010702010702020806040906030806080604090602080605060208060209060408070201070201070401020107040107030107010704010702010705010002010002010004000201000401000301040100020100050100040106020106050106010602010602010604060201060401060301010002010005010004000201000401000201040100030100020100⟩
set_option maxHeartbeats 5000000 in
private theorem valid180 : ∀ r ∈ rows180, Valid cfg 180 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_40 : ∀ i ∈ List.range' 40 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_80 : ∀ i ∈ List.range' 80 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_120 : ∀ i ∈ List.range' 120 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_160 : ∀ i ∈ List.range' 160 11, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
private theorem run180 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 180 a b c keys180 := by
  apply refine step180 h bad (by decide) (by decide) valid180 _ old
  intro i hi
  change i < 171 at hi
  by_cases h0 : i < 40
  · exact test180_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : i < 80
  · exact test180_40 i (by simp only [List.mem_range'_1]; omega)
  by_cases h80 : i < 120
  · exact test180_80 i (by simp only [List.mem_range'_1]; omega)
  by_cases h120 : i < 160
  · exact test180_120 i (by simp only [List.mem_range'_1]; omega)
  exact test180_160 i (by simp only [List.mem_range'_1]; omega)
private def keys360 : Keys := ⟨12,9,0x1e55deef051bdc795721bc146439655d767851aee5957039e1460716595d2e058ba459651ab816235⟩
private def rows360 : List Rule := [
  .pool ⟨41,25,[41,5,17,23],[2,3,7,11,13,19],657,0x1b28325128308808220169020200160125205009a60800201121000008a0004830c860009800020b20b4134100006400184c304800144000021220100041964028129201a00101025a0110404430522930536⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨41,26,[41,2,13,17,23],[3,5,7,11,19],185,0x1a3539c82a1e921022601ae31d6019102125e1504e72b16⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],657,0x2490000080400400002080012082010002400000080090490400010000412080000010000000480000010410002002480480000400480400010080482480492410402010410010400092000400080002402⟩,
  .pool ⟨41,2,[41,2],[],73,0x1a30280023100050316⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨41,29,[41,17,23,29],[2,3,5,7,11,13,19],1147,0x48820100008001060080600708030255088500800100580008c200090b02000000008000828201080818029121110800000000a22004b0120101043800803c0812020d0082808884400004006341040000a4601500002040005a00020284849a0010130088043032006882000004000200028431000000000002408401008000000421040000899000870032822002⟩,
  .pool ⟨41,40,[41,2,5,17,23,29],[3,7,11,13,19,31,37],657,0x1b28325128308808220169020200160125205009a60800201121000008a0004830c860009800020b20b4134100006400184c304800144000021220100041964028129201a00101025a0110404430522930536⟩,
  .pool ⟨41,31,[41,17,23,29],[2,3,5,7,11,13,19,31],285,0x1201b0c101105225a64104b21048021040140a0082100482134820996912822020c36012⟩,
  .pool ⟨73,9,[73,3],[2,5,7],41,0x1410800420a⟩,
  .pool ⟨41,7,[41,7],[2,3,5],365,0x29000821008c301e30a8411208159900000201906461100030000200070008108800982808004420a10010b2082⟩,
  .prime 73,
  .pool ⟨41,7,[41,7],[2,3,5],915,0x20820000a6020080100022002020004090810c840040008001000021900200001029000000000000208000a00200041120840000008001000024340328000000840800209020000a6000886092502c021204100068220001000120008301200000060008120001000141100220a00108b0092⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨31,26,[31,2,13,17,23],[3,5,7,11,19],41,0x1fffffffffe⟩,
  .pool ⟨31,26,[31,2,13,17,23],[3,5,7,11,19],511,0x121912960358972c041a22c5d23b48a001254388181cf433f64c0f8b30c5995545461c72240bc580139046e5ea314b5fba6c21b054ab859f4a14e13786972736⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  .pool ⟨41,11,[41,11],[2,3,5,7],37,0x165e211e9a⟩,
  .pool ⟨41,17,[41,17],[2,3,5,7,11,13],185,0x1a3539c82a1e921022601ae31d6019102125e1504e72b16⟩,
  .pool ⟨37,8,[37,2],[3,5,7],73,0x10080002100010116⟩,
  .pool ⟨37,8,[37,2],[3,5,7],41,0x1b382b50736⟩,
  .pool ⟨37,6,[37,2,3],[5],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  .pool ⟨37,6,[37,2,3],[5],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨41,25,[41,5,17,23],[2,3,7,11,13,19],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  .pool ⟨41,3,[41,3],[2],61,0x141002040810020a⟩,
  .pool ⟨41,25,[41,5,17,23],[2,3,7,11,13,19],925,0x1b3d3bd82a3f9a5032643beb1f709d112925e1d06e7af36d1abdec571fc90919320d758fb00e8810b3f0aa27bd78b6cd4e722b8fa6948cb80ebad75c074c4a597c75139cacdb47af791543f342045c037c6bac13262424fe3a8def562db3d79d82e1e925222e43be35f7099302967f1506f72f36⟩,
  .prime 41,
  .pool ⟨41,27,[41,3,17,23],[2,5,7,11,13,19],1891,0x50404118804010100640c81080800810000000600101e00040a128110001900819244048e0a4908c0040208c000140c24d020000000800844217000920000f482004f20080081218100000830004020a482040440002404402078d40894008900448870601003400001d0818928600828180845040a9095020a210181410061491810b800002c008060e112200910029102b1e040220240002202041250402000c100000818481001004f200412f000049000e84221001000000040b243028000310402003109250712022498100980008814850200078080060000000810010108130260080802011882020a⟩,
  .pool ⟨41,27,[41,3,17,23],[2,5,7,11,13,19],1755,0x22823295a03302c020a87184a72c0a2bd6e621262198308d261042c2bc0272500485071086e5a5473bd8442ce0230e35b4c328da17a0ce020412a1e2029494a8ee5b0ac4988429c62691610942d4198060901438c25b920514eb7350b310cc18449308a1215e01312c004283880372d2a39dee23167011a70ada65946d0b502721020950f3004a4a14773d8d624e4314e35348b08ca56a0cc0b0482a0c612dcb028af5b9a85980620c23490450b0af009c960121418421a96151ccf7118b3808d38d6932ca3605e833908100a87980a5252a2b9ec6b127218a31a9a⟩,
  .pool ⟨41,27,[41,3,17,23],[2,5,7,11,13,19],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨19,15,[19,3,5],[2,7,11,13],1825,0x1fba6e74a3b1b893256f781e7a034c7d60d8e7a8aa154bf4aa354539d6c1af8cb0079e07b5ab32436371499d977efdd373253d8d84992b5bc8f3c01e63eb06c7394550aa5fa550aa69ce362d7c65903cf03dad49961b1b8a4cecbbf7ee9b9928ec6c24c97ade079e00d31f58363dca2a8752fd2b85514ef1b06be32c01e781ed7a4c90d8dc526765dfbf74dcc9476361a64ad6f03cf02698fad1b1ce59542a97e9542a8a738d835f19e00f3c4f6b526486c6f2933b2efdfba6e64a3b1b093356b781e78034c7d60dae728ab154bf4aa154579c6c1af8cb0179e07bda9324763714b9d977e⟩,
  .pool ⟨31,29,[31,17,23,29],[2,3,5,7,11,13,19],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨31,29,[31,17,23,29],[2,3,5,7,11,13,19],1025,0x1a20304178408108ea00800210080202a720000200001520080006004020043220a820001001012100000000088820000240104000e00000c00020001081392030127204200010000c00001c000820090000104440000000021202002000105411308010080180004012a0000100001395010040210004015c4204087a0830116⟩]
private def step360 : Stage := ⟨cfg,180,2,keys180,keys360,rows360,6,0x7df7df7df7df7df7df7df7df81f7e081f7e07e081f7e081f3de78f3de78f2de78b2de78b75a69d75a69d3da68f3da68f68b2da68b2da69c71a69c71a6da69b6da69b2da68b2da68b34b2cd34b2cd64b2d964b2d934d34d34d34d61965861965840d35040d3506586196586192cf3cb2cf3cb3d860f3d860f5cf3d75cf3d75134d45134d449145249145255659555659540d35040d35050b2d450b2d42d144b2d144b34b2cd34b2cd4d45134d451345249145249134d34d34d34d38410e38410e34d34d34d34d38f3ce38f3ce40d35040d3503ce38f3ce38f2ce38b2ce38b2cd34b2cd34b2cc30b2cc30b2acaca2aaa4aa0a2a798a2a52092482092482248c82228481871c61871c61871c61871c61430c51430c50841020841020830c20830c2041041041041041041041041041041041041001040001040⟩
set_option maxHeartbeats 5000000 in
private theorem valid360 : ∀ r ∈ rows360, Valid cfg 360 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test360_0 : ∀ i ∈ List.range' 0 52, ∀ x y z : Fin 2, Test step360 i x y z := by decide +kernel
private theorem run360 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 180 a b c keys180) : Match 360 a b c keys360 := by
  apply refine step360 h bad (by decide) (by decide) valid360 _ old
  intro i hi
  change i < 52 at hi
  exact test360_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨31,27,[31,3,23],[2,5,7,11,13,17,19],949,0x175663565e83704f610d7e83069a2c1342e3a4641549fb43bb08c49a9967f79738894ed4187a1e4ea63621f400946bc59106a9b94f6ce050b1a218000611634281cdbca765582268f58a400be11b195c9e17860adca4473a7bf9a65648c43770b7e4aa098971d0b20d1658305fac21bc83b05e9ab19aba⟩,
  .pool ⟨41,21,[41,3,7],[2,5,11,13,17,19],351,0x51c02d90085c668d9ce84022500e0a1e49489243e3b42dc7c24912927850700a44021739b1663a1009b4038a⟩]
private def step720 : Stage := ⟨cfg,360,2,keys360,keys720,rows720,1,0xffffffffffffffff00000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 12, ∀ x y z : Fin 2, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 360 a b c keys360) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 12 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+14=2^a*7^b*17^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=1 ∧ b%12=1 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h180 := run180 h bad h60
  have h360 := run360 h bad h180
  have h720 := run720 h bad h360
  obtain ⟨i,hi,_⟩ := h720
  exact Nat.not_lt_zero i hi
end D14

namespace D15
private def cfg : Config := ⟨15,3,5,17,1,1,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨23,4,0xa9b49b97a37a859259738138617017bb65b6a95495974374853253732132611bb05b0⟩
private def rows12 : List Rule := [
  .div 13,
  .div 7,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,5,0x842108021084200042108401084210e4210843808421084010842100421084200842108021084210042108401084210802108420004210840108421080210842008421084010842100421084200842108021084210042108401084210042108401084210802108420004210840108421080210842008421086e108421b042108420084210802108421004210840108421080210842000421084010842108021084200842108401084210042108420084210802108420084210802108421004210840108421080210842000421084010842108021084200842108401084210042108435084210d021084210042108401084210802108420004210840108421080210842008421084010842100421084010842100421084200842108021084210042108401084210802108420004210840108421080210842008421084010842100421084200842108021084219842108641084210802108420004210840108421080210842008421080210842008421084010842100421084200842108021084210042108401084210802108420004210840108421080210842008421084010842100421084200842108021084210042108401084210c4210843000421084010842178421085c1084210802108420084210840108421004210842008421080210842100421084010842108021084200042108401084210802108420084210840108421004210842008421080210842100421084010842108021084200842108021084200042108401084210b4210842c0842108401084210042108420084210802108421004210840108421080210842000421084010842108021084200842108401084210042108420084210802108421004210840108421004210840108421080210842000421084010842108021084200842108561084215042108420084210802108421004210840108421080210842000421084010842108021084200842108401084210042108420084210802108420084210802108421004210840108421080210842000421084010842108021084200842108401084210042108429084210a0210842100421084010842108021084200042108401084210802108420084210840108421004210840108421004210842008421080210842100421084010842108021084200042108401084210802108420084210840108421004210842008421080210842138421084c1084210802108420004210840108421080210842008421080210842008421084010842100421084200842108021084210042108401084210802108420004210840108421080210842008421084010842100421084200842108021084210042108401084210942108422004210840108421204210846108421080210842008421084010842100421084200842108021084210042108401084210802108420004210840108421080210842008421084010842100421084200842108021084210042108401084210802108420⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨113,6,0x1687b895eee27bbb98fab638898cae578a15ca54bd21ec457b409ef4e6fa09bd0e6372d8c42631215d0b4b7212e854b811e4816db35848d5552957815583526ca49e1d24247939db6616d3b5872461085866d55ca954e455685542d4969d276c771a5dd26771997d235f7817c6c537b11ea9474811d8c77925df0677025acc66b60dae465fc0d7c005f9314cc3536014cae758a1d6e575295a5685d89576e25dbb917ab4588914487542da5c869a15a7485d11575025dd39444b51a09450e4572d174545109148d73529cf81738359eca67e1d9e6d73ca9cda1730b59da7673b50f24430850c6c717b196a965481976c591a5652659d8d34664148d05e041⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,10,[61,2,5],[3,7],124,0x5151111111115113315113113111536⟩,
  .pool ⟨61,31,[61,17,19,23,29],[2,3,5,7,11,13,31],1155,0x20840001a64308201141020004340228908009801a0034892502900424c001024108221808301028000220b0400000412400480000880802420510832180820080190026802520102034810980122420430886802000506100ca2806912086490492186d020021948228141220221a04109129008845004020000328060244a4080120182520c141168200800248b0012⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],16,0x8002⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],48,0x190014116⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],80,0x129a543ce1139a553de⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],48,0x2106012116⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],31,0x68818116⟩,
  .pool ⟨61,35,[61,5,7,17,19,23,29],[2,3,11,13,31],1364,0x8a20820220220800a0a002280a80a022208888280880a0008aa008022aa00820a0a0a80028a0028a000a8282820802aa200802a8800280880a088882220280a80a20028280082202202082288000000002aa2aaaa08822822a2282288a0282a820a802822202888820a88880aa8002a88a200220a2808280a2a0828a082a280a080a2822002288aa000aa80888a820888a02220a00a820aa0a0288a20a22a20a20882aaaa2aa⟩,
  .pool ⟨61,6,[61,2,3],[5],112,0x1131950bd9b33a5571d14f9db77e⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],560,0xf5b1c723d8153c0d59d0a119ad5210d31141519254912b714e5331243910738d831b1ab1b183639c1138491994e51da91254931505119610956b310a17356079503789c71b5e⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,14,[61,2,7],[3,5,11,13],176,0xf79d59f91341d57b31379ab3d919bd5705913f3573de⟩,
  .pool ⟨61,29,[61,17,19,23,29],[2,3,5,7,11,13],1364,0x8a20820220220800a0a002280a80a022208888280880a0008aa008022aa00820a0a0a80028a0028a000a8282820802aa200802a8800280880a088882220280a80a20028280082202202082288000000002aa2aaaa08822822a2282288a0282a820a802822202888820a88880aa8002a88a200220a2808280a2a0828a082a280a080a2822002288aa000aa80888a820888a02220a00a820aa0a0288a20a22a20a20882aaaa2aa⟩,
  .pool ⟨61,3,[61,3],[2],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,19,[61,17,19],[2,3,5,7,11,13],744,0x200020820a00820008800200228a20028208008020200000808020020828008a28800800220008200a08208000808828a08008028208a20228828800008a00820a00a08828a28220a00a08200a20000228228808a20828020020a2822⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .prime 61,
  .pool ⟨61,27,[61,3,17,19,23],[2,5,7,11,13],1364,0x8a20820220220800a0a002280a80a022208888280880a0008aa008022aa00820a0a0a80028a0028a000a8282820802aa200802a8800280880a088882220280a80a20028280082202202082288000000002aa2aaaa08822822a2282288a0282a820a802822202888820a88880aa8002a88a200220a2808280a2a0828a082a280a080a2822002288aa000aa80888a820888a02220a00a820aa0a0288a20a22a20a20882aaaa2aa⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],248,0x802a200200822a0a882008008a8020a2a808a88aa2880a0228aa22a202a8a⟩,
  .pool ⟨61,2,[61,2],[],31,0x68818116⟩,
  .pool ⟨61,2,[61,2],[],112,0x131050301332215211107152736⟩,
  .pool ⟨61,10,[61,2,5],[3,7],112,0x131050301332215211107152736⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,6,[61,2,3],[5],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨61,14,[61,2,7],[3,5,11,13],496,0x1953b315751d33b1bd9311d11dbd570b7fd1db9dbb39d1b133dbf77b313f9a5d17f751315977f1f9d7559559f9134f3b959fd9ff7d95b5779fb33f757bde⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,8,0x70000000000000000060000008e0000008d0000008c00000000000014000000140000001400000014000000000000000014008b0000008a0000000000000000070000000600000089000000000000880000001600000087000000070000000600000000000006000000150000001500000000000000008600000007000000070000000600000085000000000000000084000000830082000000000000000007000000060000001000000081000000000000800000007f000000070000000600000000000000007e00130000001200000000000000007d0000000700000006000000000000060000007c0000007b0000007a0000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000001d0000001d000000790000000300000000000003000000010000000e0000000e0000000000000000780077000000020000000000000000010000001c0000001c000000000000760000007500000002000000010000007400000000000073000000720000007100000000000000000300000001000000010000000a0000000a0000000000000000700000001b00020000000000000000010000006f0000001a0000006e0000000000006d00000002000000010000006c00000000000000006b006a000000690000000000000000020000006800000067000000000000660000000b00000065000000020000000100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006400000000000000006300000062000000070000000600000000000006000000190000001900000019000000000000000007000700000006000000000000000061000000600000005f0000000000005e000000070000000600000005000000050000000000005d0000005c000000070000000000000000060000005b0000005a000000590000005800000000000000000700000006000600000000000000005700000056000000550000000700000000000007000000060000005400000053000000000000000052005100000007000000000000000006000000500000004f00000000000017000000180000000700000006000000170000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e000000160000004d0000004c0000000100000000000015000000150000001500000000000000004b0000000200020000000000000000010000004a000000490000004800000000000014000000140000001400000014000000000000000014004700000046000000000000000002000000010000004500000013000000120000000000000000440000000200000001000000000000010000004300000042000000410000001100000000000002000000010000004000000000000000003f0000003e003d00000000000000003c00000001000000100000003b0000000000003a0000003900000003000000380000000000000000370000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000360000003500000007000000060000003400000000000033000000320000003100000000000000000700000006000600000000000000000f0000000f0000000f0000000700000000000007000000060000000e0000000e00000000000000000d000c000000070000000000000000060000000c0000000c000000300000002f000000000000000007000000060000002e0000000000002d0000000b0000002c0000000700000006000000000000060000000a0000000a0000000000000000090000000700070000000000000000060000000800000008000000080000000000002b00000007000000060000002a00000000000000002900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002800000005000000010000000500000005000000000000270000002600000002000000000000000001000000250024000000000000000023000000220000000300000001000000000000010000000400000004000000210000000000000000030002000000010000000000000000200000001f0000001e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000⟩
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
private def keys180 : Keys := ⟨24,8,0xa2257f2a2543a29d072a6107a891af6c19af6c5573a819736c9137a855373c3d973c795b00015b003d1f24a98b606d8b24314f246d136031134849132a259da29d612a6161a22525⟩
private def rows180 : List Rule := [
  .pool ⟨19,2,[19,2],[],296,0x1f5d1559511b155b1b11115f1119595f1d5507131d1351555519575357591f5f5b531d1316⟩,
  .pool ⟨37,30,[37,2,3,5,17,23,29],[7,11,13,19],61,0x1ffffffffffffffe⟩,
  .pool ⟨19,5,[19,5],[2,3],259,0x800014419080000001000400040000038040842c020000128305010420a0062⟩,
  .pool ⟨37,17,[37,17],[2,3,5,7,11,13],305,0x1200bc4011401120662218830001000006000303000180000200030461119812200a2008f4012⟩,
  .pool ⟨19,2,[19,2],[],724,0x5111111115111111111111111111111111111111111111111111111111111111111111111111111111111111113111191111111111111111111111111111111111111111111111111111111111111111111111111115111191116⟩,
  .pool ⟨181,11,[181,11],[2,3,5,7],37,0x165e211e9a⟩,
  .pool ⟨19,2,[19,2],[],793,0x1a207404ac8001c266c20040150e8421e4a6842400418010088d42e254d5201af08320f711c020904445844e10151804470303888062a021c886888824100e23bc13043d6012aca91d0ac440200608009085949e1085c2a008010d990e0004d480b8116⟩,
  .pool ⟨61,30,[61,2,3,5,17,23,29],[7,11,13,19],181,0x1ffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨181,4,[181,2],[3],111,0x14122102590d06410d329345b6⟩,
  .pool ⟨31,23,[31,17,23],[2,3,5,7,11,13,19],1443,0x25800a08a21225361245a4c32510910484824190430d00802194086934d92c82030d26d10820186882c00904da20029b20a44809320b0110c00c004924104a20a0502800d20404802d32012da41a00324a41128b25349b0800032136d260041020a25308901968340021a2102ca4d16906d82d028b2892590496d865861360b20264148b20029a2804d22d80ca0c360a6100906032c02404100ca4432d82d041964241a48965264121048109101029308a28b4c12⟩,
  .pool ⟨19,5,[19,5],[2,3],31,0x121d47b6⟩,
  .pool ⟨37,17,[37,17],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],1464,0x8a20a08228028220008a08828000028808000a28228208a00800808220a28820220828a08a20000820800a08008808a08028820828820008000820220800020208828828008200200028a08800a28a00808008a00200a00208020000008020800a00800a20020200a28a00220a28000800820028228220808000208808200020008228208228020a20220020a00208200008a20a28208808228a08820200200a20828828a00020228000028220a20008828028820a08a2⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],259,0x30a92334e3d1b04a00d110ac04ae5a20abb2408dbc2e750bf2cf07010c31b2a72⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],1267,0x348c2b12e204bd7201f2a78f041d44b5eab5459233003941b2cf990d1e9d71d40212241898c874e284b12aece0118ad821721c1120298e0c28542905c489081ef9b2b4a6828b787979330e0f904a11a372cf40b87234121602cba12c2922006ed6ad44f4b956acd8a63eb57873079e0a663d8882a70dab0c1cca666d9b3b7c45106064d6204a25d037e31b2554288125c45db060a903f3040dbb0a70b8e52⟩,
  .pool ⟨19,5,[19,5],[2,3],181,0x11e0049dc628b42426480880440499090b4518ee4801e2⟩,
  .pool ⟨61,10,[61,2,5],[3,7],1036,0x1111112113311451511705111110111113010115101111512113135211111101113510115031215111501111110111111431113503551104117111011111305111110511331011111100151134113111011113103131110111111031013101113110551111011511105511114111101011135501513112111113035115503131536⟩,
  .pool ⟨61,10,[61,2,5],[3,7],592,0x315211125110111071105170511051501150113011305350131011123110135051101330015011505112735271105112111051103350107053525310115051703152517031327150536⟩,
  .pool ⟨61,37,[61,17,23,29],[2,3,5,7,11,13,19,31,37],13,0x161a⟩,
  .pool ⟨19,5,[19,5],[2,3],61,0x1713e6940a59f23a⟩,
  .pool ⟨19,2,[19,2],[],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩,
  .pool ⟨61,28,[61,2,7,17,23],[3,5,11,13,19],181,0x1ffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨61,31,[61,17,23,29,31],[2,3,5,7,11,13,19],1628,0x828a828a000088aa0000a02202a80a2282a80288a0822802a2aa2aa8882880220a2a0a80a0222208082222802288228202aa208800a0a08a008aa0080a2828888282a00808080aa20822000000808208a20220a800a0802800888a822aa80022aa2020a000a0a000a0808aa88002aa882a2220028020a002a08808a20820200000088208aa02020200a8282222828a0200aa200a20a0a002208aa8082882288028888202088880a02a0a8a0880228222aa8aa8a8028820a22802a8288a02a80880a0000aa220000a282a282⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],112,0x1111010b19030a4501510b0d135e⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],61,0x1713e6940a59f23a⟩,
  .prime 19,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],244,0xa08820a00200008000a88000002008020080000022a00020000800a08220a⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],259,0x30a92334e3d1b04a00d110ac04ae5a20abb2408dbc2e750bf2cf07010c31b2a72⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],592,0xa8000080020202882000022000008882880000228222000008800008228080800200002a080082080a08a80020880800800080002000082000080002000200202208002a20a02082002⟩,
  .prime 37,
  .pool ⟨19,3,[19,3],[2],61,0x1713e6940a59f23a⟩,
  .pool ⟨19,7,[19,7],[2,3,5],181,0x1040040800003000000000000000000003000004080082⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨19,7,[19,7],[2,3,5],31,0x121d47b6⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],31,0x121d47b6⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩,
  .pool ⟨19,3,[19,3],[2],244,0xa08820a00200008000a88000002008020080000022a00020000800a08220a⟩,
  .pool ⟨19,7,[19,7],[2,3,5],296,0x8a882088a0aaa02a8a80802a0008088a2880820228a2202000a80202a2a80aaa0a220822a2⟩,
  .pool ⟨19,7,[19,7],[2,3,5],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],1443,0x100004002000000402000000d000000000000200008000000104040a2000000000000000000000000080004010080000014000000020020002400c80800000004400400000004000000000000000000000000000000804000402000020000c000000000001220000000000000000840001800000008200000a0800080000000000000002020000020000010000000002010000000000000000000000000100000100000000000010010000004100090116⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],481,0x1a206404e0801082a00200100802002360000020000018000200002014503028a010000100006000001000001b10010040200100150420041c8098116⟩,
  .pool ⟨19,3,[19,3],[2],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,3,[19,3],[2],671,0x50401010000040600000c00000240000004014020012200004000000820090001800001000000202010000804040000008000018000900410000002000044800402802000000240000030000060200000808020a⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],793,0x1a207404ac8001c266c20040150e8421e4a6842400418010088d42e254d5201af08320f711c020904445844e10151804470303888062a021c886888824100e23bc13043d6012aca91d0ac440200608009085949e1085c2a008010d990e0004d480b8116⟩,
  .pool ⟨19,2,[19,2],[],16,0x1b5f⟩,
  .pool ⟨31,23,[31,17,23],[2,3,5,7,11,13,19],208,0x280008080000000020200028080028202008282820080828002⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],181,0x1ffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨37,13,[37,13],[2,3,5,7,11],80,0x2000002202⟩,
  .pool ⟨181,26,[181,2,13,17,23],[3,5,7,11,19],304,0x19731517b1b9111dd70b7dd9bb91b17bf3379a5d375153f1fd5559934f399dffd5b53fb773de⟩,
  .pool ⟨37,32,[37,2,17,23,29],[3,5,7,11,13,19,31],1209,0x1b2832512930d90c225929028a48069121209b49220804320221960045a6190c205960161b6982092024020404d129201160201a08b44040809a61b04a4d068024009a08a41008b04b28b20b4134534834402094416400900582c948361964040808b44160101a2012522c808100901241065b61a01a6810c261968801a61101308041124b6412122580494502526910c26c32522930536⟩,
  .pool ⟨181,35,[181,5,7,17,23,29],[2,3,11,13,19,31],111,0x14122102590d06410d329345b6⟩,
  .pool ⟨181,26,[181,2,13,17,23],[3,5,7,11,19],185,0x1a3539c82a1e921022601ae31d6019102125e1504e72b16⟩,
  .pool ⟨19,5,[19,5],[2,3],208,0x88202080000002202000a2020000808a00080880000002080822⟩,
  .pool ⟨181,12,[181,2,3],[5,7,11],80,0x129a543ce1139a553de⟩,
  .pool ⟨61,20,[61,2,5,17],[3,7,11,13,19],16,0x2737⟩,
  .pool ⟨181,4,[181,2],[3],16,0x2737⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],407,0x5230d0b00e6009b4440bc7d4510c39f253065009aa57aa735331310a05a86fb49734b043c375540c2d9d9267f88dd2f0f335e⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],488,0x5519514117015511011d01011111490301014551530111111109050113410b0d130b41011119110b1d154503010105191101035b01135501510f1d135e⟩,
  .pool ⟨19,13,[19,13],[2,3,5,7,11],724,0x2022882002a00aa8282a0a88a08a8200022a28880208000820088a2a200020a88288a82a0a0aa802a00208a20222a208a2aa02a800a0a0280882880a2aaa202088aa28a8a8a2a8882022aaa2808a0880a0282800aa02aa28822a2⟩,
  .pool ⟨37,7,[37,7],[2,3,5],19,0x41982⟩,
  .pool ⟨31,23,[31,17,23],[2,3,5,7,11,13,19],247,0x28021c0000000100009000810100050000360200248908000c0a80868102⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],976,0x1119014113011001011d00011111090300010151020100010109010112410a0d020b00011019110b19050003010101090101024b00130001010f18030a4508510107004510010801010101490301004501530111101108050003000b08130b41010108010a0d114502010105191100031b01025501510b0d135e⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],61,0x1ffffffffffffffe⟩,
  .pool ⟨37,9,[37,3],[2,5,7],61,0x1434026619900b0a⟩,
  .pool ⟨19,12,[19,2,3],[5,7,11],181,0x1ffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨19,16,[19,2],[3,5,7,11,13],48,0x84112090116⟩]
private def step180 : Stage := ⟨cfg,60,3,keys60,keys180,rows180,7,0x80fc33f0d043407cfc3410d01f407e1c3407d01f867e1a0447d19f46891a23e7d1a24688fa23e8d1a23e88fa33e8d1203f0cfc3410d01f3f0d043407d01f870d01f407e19f86811a23e88fa33e8d1223e8cfa3448d11f3e8d123447d11f470d01f407e19f868101f867e1a08680f9f86821a03e80fc3407e19f86821a03e7e1a08680fa03f0e1a03e80fc33f0d01f86821a03e80fc38680fa03f0cfc34080fc33f0d043407cfc3410d01f407e1c3407d01f867e1a0407e19f86821a03e80fc33f0d043407cfc3410d01f407e1c3407d01f867e1a04b0d3434e95025870d0254e961a586993a586961a0869d2a3449512546951a244951a546891a24a951a246892a24a8e1a04a812c34b0d0204b0d2c3410d0254b0d0434095025870d01f407e19f868101f867e1a08680f9f86821a03e80fc3447d19f46891a23e7d1a24688fa23e8d1a23e88fa33e8d11f46891a23e88fa34688fa23e8cfa34488fa33e8d123447cfc3410d01f407e1c3407d01f867e1a0407e19f86821a03f0d01f407e19f868101f867e1a08680f9f86821a03e80fc340ae1ac869e1a056b21a086815a6570e1a756815c3590d01f86821a03e9cfc3869cfa03f0cfc34080fc33f0d343407cfa3448d11f447d1a3447d11f467d1a2447d19f46891a23e7e1a7869cfa03f0e1a03e98fc33f0d3a63f0cfc3410d39f3ceccbb3268c9a3cecc9a3268f1e7664c9a3c79d997664d193aece1e32ecc9e3878cbb3278c9d76ecc9e3275d9c3c64c988460f197664f183c661193c64c3b7664f1930ecc1e32ecc9e3261d983c64c987660f197664f183c65d993c64c3b3c64c193cecc3b3264f3b30ecc9e3260c3b3278c983279d9e3260c9e7661d993279d988464f193061d993c64c193d08c983c79d997664c1e7665d993064c1e7664c193078f3b3264c3b3078cbb3278c1e32ecc9e3261dbb3278c987660f193279d987664f193061d993c64c193cecf193064f3b30ecc993904e3a32e8cbc38e8cba32f0c9c82e8cbd327209c7464dc03300c9b326e040326cc9b806e019326e01b806601936720198065e9939020197a64e403900c993900e403300cbd7464c1930e8c3f3264c3a30fccba3260c3f32e8c983261d3a3260c987461f993261d187e65d193061f997464c1930e8c987e61d197464c187465d193064c3f7464c1930fcc3a3264e3b38e8cba32f0e3a32e8cbc3271dba32f8c9c7671d1932f5d1c7665d193871d997464e1978e9d193865e3a38ecc9c7665d193865e3a7464e1978e8e3b3265e3a38eccba3270dba32ecc9b326dd3b326cc9b746dd19326dd1b7465d9936e8c9b326dd9b7464c9b766dd197464d9b7465d193664dbb7664d1934e8d3a3264d3a34e8cbb3268d3a32ecc9a3269d2e143450d5c3170a143570e5c2970a1a3170a5c2868a1ab852f5cbd70a5c297af5c2970a5e297ae5c2978a5eb97ae144c92e06b89ae26481ae26b8992264972e26489925c0d713143970d5c2970a1a3570a5c2868a18b970a1a2862e1ab850a5eb97ae14b852f5eb852e14bc52f5cb852f14bd72f5c29b015c1d7365cd81855cd973606d80ae5cd81b602b9cae6c597135c4cb1306b97132c4c1ae2cb899306b8b2e26b89965c2978a5eb97ae14297ae5eb852e14bd7ae14b852f14bd72e26549835d6d713260d7155c4d713b5657135c4ec1306b850d5c0d70a5c286835c2970a1a286ae5c2868a1ab872e143170a5c2860a18b970a182862e18b850a18b862e14b850c5eb852e14bc52f5cb852f14bd72f5c2852f5cbd70a5c297d75c3d70f623eb2e5c3d88faabaa2e1e3e9aea4b87ae1ec45335cc570a5c29c315c2970a70299ae5c29c0a66b98ae14297ae5eb852e14bd7ae14b852f14bd72e14bc52f5cbd70a1ec57385cd970f70e170f5c3dc3662b9736703d8ae70b87b15c2970a1c2872e5c2870a66b872e142872e1cb852e14dd7ae14b852f14bd72e14bc52f5cbd70a14bd72f5c2970a5eb9b321f457315c3c7d05cc57365c3e7b15c3d70f9cd9aae5c4e69398b98ae264da2e62b89ae272d8ae26b89ca272570a60b99ae14b853166b852e14c05325cb853115217305c2852f5cbd70a5c297af5c2970a5e297ae5c2978a5eb97ae149101f407d21f488101f487d2204880f9f48812203e80fa44880fa03e90fa44080fa43e91024407cfa4409101f407d223447d11f467d1a2447d19f46891a23e7d1a24688fa23e8cfa1408501f407d0a1407d01f427d0a0407d09f42810a03e8501f407d09f428101f427d0a04280f9f42810a03e80fa14688fa23e8cfa34488fa33e8d123447cfa3448d11f447d1a1407d01f427d0a0407d09f42810a03e7d0a04280fa03e84fa3448d11f447d1a3447d11f467d1a2447d19f46891a23e7d4a05280fa03ea54a03e80fa93ea50203ea4fa940a501f5280fa03ea4fa94080fa93ea5029407cfa940a501f407d4ac54814a056995ad529d5a056b562a40815ad58a93a940ad5273e80fa93ea10203ea4fa84ca901f3ea102a407d39f528d11f447d19f468911f467d1a24688f9f46891a23e88fa35280fa63ea0faa4e98fa83ea90294e7cfaa4ea539f407d4274a852a140853a54a853214e9502542850254e950a542992a3448d12544951a3449512546951a244951a546891a24a950a042812a04a850a04a812a14a850204a852a140850253e91024407d01f489101f407d21f488101f487d2204880fa3447d11f467d1a2447d19f46891a23e7d1a24688fa23e8d1a23e88fa33e8d1223e8cfa3448d11f3e8d123447d11f4688fa33e8d123447cfa3448d11f447d1a3447d11f467d1a2407d09f42810a03e7d0a04280fa03e850a03e80fa13e850223e8cfa3448d11f3e8d123447d11f468d11f447d19f4688fa1408501f407d0a1407d01f427d0a0407d09f42810a03e64c173078c973278c1e325cc9e3260b973278c982e60f193278b982e64f193060b993c64c193c5cf193064f17305cc993c5cc173278c98305cc9e3260c9e2e78c983278b982e64f17325cc983260f173260c983c78b993260f1e2e64b993060f192e64f19305cb993c64c173078c99305cc1e325cc9e305cc9e3260c9e2e78c983278b982e64c9e2e60b993c64c1c2e64b993a64e172e64e99385ce173264e17385cc973274e17325cc9c3274b973270c9d2e70b993274b9c2e64b99385cc9b326cb9b2e64c9b2e6cb992e64d9b2e64b993664d97326cb9b2e64b99366cb992e64d99365cb993664d97365cc99345cd17325cc9a345cc973268c9a2e5cc9a3268b9a2e64c17325cc983260b973260c982e60b993260b982e64b993060b992e64c19305cb993064c17305cc99305cc17325cc982e64c19305cc173264c17305cc973260c17325cc983260b8426589830058013260c016004c2132c58013084cb1306005090024a0a0028589282800a1628480002858a1200494144c1802a00994271e30026509c5260c014265498301100130600500143450d280050d1434a0e002850d280c00a002868c002800a1a28684002868a1a1060014286841c00500143420a1228580120050a160048014105091200506142450b00009922648203004c992080c013004c903004c013244c9041e40203000800f220c00f003c8822010002223c8040600784143450c003400a143800d002820a1a3400a082868a180000a1228484160050a1210580140050916005001424509080010304040080808101001c302000818508080020608080⟩
set_option maxHeartbeats 5000000 in
private theorem valid180 : ∀ r ∈ rows180, Valid cfg 180 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_0 : ∀ i ∈ List.range' 0 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_40 : ∀ i ∈ List.range' 40 40, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test180_80 : ∀ i ∈ List.range' 80 33, ∀ x y z : Fin 3, Test step180 i x y z := by decide +kernel
private theorem run180 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 180 a b c keys180 := by
  apply refine step180 h bad (by decide) (by decide) valid180 _ old
  intro i hi
  change i < 113 at hi
  by_cases h0 : i < 40
  · exact test180_0 i (by simp only [List.mem_range'_1]; omega)
  by_cases h40 : i < 80
  · exact test180_40 i (by simp only [List.mem_range'_1]; omega)
  exact test180_80 i (by simp only [List.mem_range'_1]; omega)
private def keys360 : Keys := ⟨4,9,0x2d61eb40096c55158ab78c261⟩
private def rows360 : List Rule := [
  .pool ⟨41,18,[41,2,3,17],[5,7,11,13],1480,0x11110719101519495b181711035910511147435a131d43111c1719411310111149135415180d195c5715095112151d031b5815154d591c011d0f531853190b131a51150d1b12551101525653194b11521315091158511d0919161319055354151d4711505119451956511541595a10114f51105715071b52171d4d515057110f114e151101111c531545131e57114d1b1a131d045b141315435b5c551503511617154b1b54530901595a571947591e51194b5b16551d0f535e⟩,
  .pool ⟨41,12,[41,2,3],[5,7,11],296,0x57154d1111534d034309590759510107550d4f4b554b091d1d411f0b0f014717131b455b5e⟩,
  .pool ⟨41,12,[41,2,3],[5,7,11],32,0xb4f1b5f⟩,
  .pool ⟨37,35,[37,5,7,17,23,29],[2,3,11,13,19,31],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨61,28,[61,2,7,17,23],[3,5,11,13,19],1056,0x101200b0d20016500d104820b01941109a0d929021869848b65228349128321a24145205b49244121048140964b4190414db4992d06482d90cb2126c30d068365a61101301b0d20116510c104921b01840109b0c929120869949b65328349029321b25145304b49245121149140865b4180514da4892d16582d80db2136c30d169365b6⟩,
  .pool ⟨37,35,[37,5,7,17,23,29],[2,3,11,13,19,31],876,0x8a00828a28208808020008008a08a28800228220a08208800a20828020800a20208200808008a20000200228228028220208000020a00000a08000020808828028828800800008a20020200820808a00208028208a00220820a08828800228a20a20020008020220828a28200a2⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨37,32,[37,2,17,23,29],[3,5,7,11,13,19,31],1056,0x84910432100180d248128a20369a0592490c00126404484820d16cb64229b4186194900522100090c349028b21368b0482580d10136504594930c06cb65328b4096094910432000190d248128a20269a0592590c10126404584830d16cb65229a4186194800532100090d349128b21369b0492580d10036504594930d06ca65328b4196⟩,
  .pool ⟨41,28,[41,2,7,17,23],[3,5,11,13,19],528,0x10110030100110500810082030180110190c10102004184830512834102930182114100530100010114910092134190410580910116500590930106c30512834196⟩,
  .pool ⟨41,2,[41,2],[],16,0x317⟩,
  .pool ⟨41,28,[41,2,7,17,23],[3,5,11,13,19],32,0xd387c397⟩,
  .pool ⟨41,27,[41,3,17,23],[2,5,7,11,13,19],1460,0x200280808220082020a22208a22020080880000a22800080000a8800a0882a08a00808228022a0aa00802008a002880200802a82a200a2080802882a08828008a800008000a2280000880802022288222282020802208080a0020282a2088a0a02a0a0a002022080222288a088aa280202a88a2a8800288208802080a8288202a002000a82a0a8028a00a82a0a8002002a0208a0a80820088208a0008aa288aa0200a2a888288a22200822020028282a028288822a0a⟩,
  .pool ⟨41,3,[41,3],[2],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨181,19,[181,17,19],[2,3,5,7,11,13],219,0x21a40309b2d02820412400ca2122932886d905969a2d020261b4832⟩,
  .pool ⟨41,3,[41,3],[2],560,0x80000020008000000000000000800000000020008000200000000000000000000000000000208000000020200080002000000000208000000000a000800000a000800020a⟩,
  .pool ⟨73,30,[73,2,3,5,17,23,29],[7,11,13,19],1232,0xfdd3d3ad51ad74711bb1ce511538b53983c5dd9952d49913091b3f60dd11b763581f5811d3514151931471b071c99b153249b9f525d53612d1733303c73d1e3d1150a35fb158192b512f93933ab99393e915a930351bf58a151178f179c781999d1690d957495f3b249951b3271c1b1c5193150515971035f0358ddb11760df9b1219132569533774783395a395114e71bb11c5d6b156b97977e⟩,
  .pool ⟨41,27,[41,3,17,23],[2,5,7,11,13,19],1480,0xa080a2280080a8a82a08a220822880a02002228a02a8a20088820880020020a088028000a8082888a2a0280082a088020a882000080808a008aa028802082a228a80a0880a820000a00202a2280a0002822008200800088828020288002280802822200020082008828000a0288a80800a000082a0220a02a288a820802280aa200a202020000822a080220a8200280a8a2228202a000280220a08008002208222008a2a80a28880080a022882088a20a82a2a0200288a020a⟩,
  .pool ⟨41,3,[41,3],[2],37,0x165e211e9a⟩,
  .pool ⟨41,8,[41,2],[3,5,7],160,0x102000001000600010000020100010116⟩,
  .pool ⟨41,22,[41,2,11,17],[3,5,7,13,19],16,0x1b5f⟩,
  .pool ⟨41,8,[41,2],[3,5,7],73,0x1a30280023100050316⟩,
  .pool ⟨41,8,[41,2],[3,5,7],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .prime 41,
  .pool ⟨41,29,[41,17,23,29],[2,3,5,7,11,13,19],1891,0x31ad2218f2a2b87955f633a2242b8511cdcd1087e5a53283e79ab2243ecdf1291b1d4a4db9fe3d9047c933dcf1b537e042c4282374a2928be4171a0841782278e860bc0d9a71cb5860685152955538bf8ec44e6cb1844c0e40b96081e01447badea74b9eb47aa2f5908b60b370b76b21029fec80c832ab3e8fec006b77b2912e132b92ed650baa192842d1a04a21dd6f86ef960fd8fcdda72498dd48e02e34552b575c9f9e52c31864fc279e8e1bae07defa517d82eb2b2d13be3dcbdf8031270c4136c1df60180624d2d47276a604c83d9b2a6183a335a5816f74c4c635e2bdb9a33905501e2bab067bb4a72⟩,
  .pool ⟨41,29,[41,17,23,29],[2,3,5,7,11,13,19],1147,0x48820100008001060080600708030255088500800100580008c200090b02000000008000828201080818029121110800000000a22004b0120101043800803c0812020d0082808884400004006341040000a4601500002040005a00020284849a0010130088043032006882000004000200028431000000000002408401008000000421040000899000870032822002⟩]
private def step360 : Stage := ⟨cfg,180,2,keys180,keys360,rows360,5,0xb62d8c5b162d8b6b16c5b62d8c5b16b5ed7bdaf6a4ce739e749d274a4e9394eb39d67239e74a4ce79d275ace9339e539c8e739e30844e739e118c0e7771cf7bb6e5b1ae7358b4a92842549424e739d28425494a9284a12a5250939d094a0e7318c6318c628ca31946510020004021e86420f230040210020⟩
set_option maxHeartbeats 5000000 in
private theorem valid360 : ∀ r ∈ rows360, Valid cfg 360 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test360_0 : ∀ i ∈ List.range' 0 24, ∀ x y z : Fin 2, Test step360 i x y z := by decide +kernel
private theorem run360 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 180 a b c keys180) : Match 360 a b c keys360 := by
  apply refine step360 h bad (by decide) (by decide) valid360 _ old
  intro i hi
  change i < 24 at hi
  exact test360_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨37,35,[37,5,7,23,29],[2,3,11,13,17,19,31],136,0x202a082000820a8088a80228aaa28802a2⟩,
  .pool ⟨41,27,[41,3,23],[2,5,7,11,13,17,19],1105,0x1eb228642210e08021201802a0020014211920000a0000226000402000001c8024080b0c200004000220110410047424a000400480406000101000000a86000020801205027902812004100001854000002020001808048008001490b880208220110000800010c340409004e00000100800191000014000126210a001001500601210041c2110985135e⟩]
private def step720 : Stage := ⟨cfg,360,2,keys360,keys720,rows720,1,0xffff0000⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 2, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 360 a b c keys360) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 4 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b c : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+15=3^a*5^b*17^c) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a%12=1 ∧ b%12=1 ∧ c%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b c := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1,c1⟩
  have h : H cfg n a b c := ⟨shape,ha,hb,Or.inl hc,by simp [cfg],hn,div,pp,sol⟩
  have h1 : Match 1 a b c keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h180 := run180 h bad h60
  have h360 := run360 h bad h180
  have h720 := run720 h bad h360
  obtain ⟨i,hi,_⟩ := h720
  exact Nat.not_lt_zero i hi
end D15

namespace D16
private def cfg : Config := ⟨16,2,17,1,4,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x48080⟩
private def rows12 : List Rule := [
  .div 7,
  .div 3,
  .div 5,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x44144144120a2ca20a05105105128828e28844144144120a20a2ca05105105128828828c4414414412ca20a20a05105105128d288288⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨3,6,0xa2c004200518⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,7,[31,7],[2,3,5],549,0x82080002000012080080490090000012010000080000000000082002090002000000480092400080082002412000410482012080010090480000080010002082090010092⟩,
  .prime 61,
  .pool ⟨61,3,[61,3],[2],9,0x9b⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],819,0x40904001001020008009008044001040008244000000001000001000000000800005000049005104000004a00000040000008000100000020000005200000208a00920000a0000100000000080000080000000022410002080022010090010004080080020902⟩,
  .pool ⟨31,2,[31,2],[],63,0x6880800180010116⟩,
  .pool ⟨31,9,[31,3],[2,5,7],9,0x9b⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0x60000090000020000050000080400000300000700000210000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨0,7,0x0⟩
private def rows120 : List Rule := [
  .pool ⟨31,29,[31,19,23,29],[2,3,5,7,11,13,17],819,0xa00000000000000800240000200200005020841200a48200000208028000804008100020000344000300000000008200004000020100000020024000000000800200020004000020008848044000808100000004000240200100001840100008000a0c80002⟩,
  .pool ⟨41,17,[41],[2,3,5,7,11,13,17],5,0x2⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨31,19,[31,19],[2,3,5,7,11,13,17],595,0x42009005094800140421424290a4204010002100000204a100400280042042408080004a100085200010102420420014002008520400000840008020425094242842028001290a0090042⟩,
  .pool ⟨31,19,[31,19],[2,3,5,7,11,13,17],451,0x20008000000000000820001000010080000e8000008000000800048010002000040008820044025212040c00000008800000083080022⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0x8e3451000⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 3 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 30030∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+16=2^a*17^b) (ha : 0<a) (hb : 0<b) : a%12=4 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  obtain ⟨i,hi,_⟩ := h120
  exact Nat.not_lt_zero i hi
end D16
private theorem supported_three (m x y : ℕ) (pos : 0 < m)
    (sup : ∀ p : ℕ, p.Prime → p∣m → p=x ∨ p=y ∨ p=17) :
    ∃ a b c : ℕ, m=x^a*y^b*17^c := by
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

private theorem supported_offset {n j x y : ℕ} (hj : 0<j) (jl : j<17) (div : 30030∣n)
    (hit : 17∣n+j) (xy : x*y∣n+j) (cop : (x*y).Coprime 17)
    (small : ∀ p : Fin 17, p.val.Prime → p.val∣j → p.val=x ∨ p.val=y)
    (sol : v_l 1 n=1) : ∃ a b c : ℕ, n+j=x^a*y^b*17^c ∧ 0<a ∧ 0<b ∧ 0<c := by
  have whole := cop.mul_dvd_of_dvd_of_dvd xy hit
  obtain ⟨t,ht⟩ := whole
  have pos : 0<t := by by_contra! h; rw [show t=0 by omega,mul_zero] at ht; omega
  obtain ⟨a,b,c,eq⟩ := supported_three t x y pos (by
    intro p pp dp
    have dn : p∣n+j := ht ▸ dvd_mul_of_dvd_right dp _
    by_cases low : p≤j
    · have tab : ∀ r : Fin 17, r.val.Prime → r.val∣30030 := by decide
      have dj := (Nat.dvd_add_iff_right ((tab ⟨p,by omega⟩ pp).trans div)).mpr dn
      rcases small ⟨p,by omega⟩ pp dj with h|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · by_contra! neq
      exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.two_primes hj pp
        (by decide : Nat.Prime 17) neq.2.2 (by omega) jl dn hit sol)
  refine ⟨a+1,b+1,c+1,?_,by omega,by omega,by omega⟩
  rw [ht,eq,pow_succ,pow_succ,pow_succ]
  ring

private theorem close_from_three {n j x y a b c u v : ℕ} (hj : 0<j) (small : j≤16)
    (big : 2000<n) (hit : 17∣n+j) (sol : v_l 1 n=1)
    (jval : j=x^u*y^v) (shape : n+j=x^a*y^b*17^c)
    (ha : a%12=u) (hb : b%12=v) (hc : c%12=0) : False := by
  let z := x^(a/12)*y^(b/12)*17^(c/12)
  have regroup (p i r : ℕ) (eq : i%12=r) : p^i=p^r*(p^(i/12))^12 := by
    rw [←pow_mul,←pow_add,show r+i/12*12=i by omega]
  have twelfth : n+j=j*z^12 := by
    calc
      n+j=x^a*y^b*17^c := shape
      _=j*z^12 := by
        rw [regroup x a u ha,regroup y b v hb,regroup 17 c 0 hc,jval]
        dsimp only [z]
        rw [mul_pow,mul_pow,pow_zero]
        ring
  have hi : 1<z := by
    by_contra! low
    have zz := Nat.pow_le_pow_left low 12
    have nj := Nat.mul_le_mul_left j zz
    omega
  have pr : Nat.Prime 17 := by decide
  have dz : 17∣z := pr.dvd_of_dvd_pow ((pr.dvd_mul.mp (twelfth ▸ hit)).resolve_left
    (Nat.not_dvd_of_pos_of_lt hj (by omega)))
  exact no_seventeenth_twelfth hj small dz hi twelfth sol


/-- No positive offset below seventeen can be the first multiple of seventeen after a large prime-successor solution of the stated divisibility. -/
theorem exclude_offset {n j : ℕ} (big : 2000<n) (div : 30030∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (lo : 0<j) (hi : j<17) (hit : 17∣n+j) : False := by
  interval_cases j
  · have e := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 17) pp).mp hit
    omega
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D2.exponents big div pp sol eq ha hc
    exact close_from_three (j:=2) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big hit sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D3.exponents big div pp sol eq ha hc
    exact close_from_three (j:=3) (x:=3) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big hit sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D4.exponents big div pp sol eq ha hc
    exact close_from_three (j:=4) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0) (by decide) (by decide) big hit sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=5) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D5.exponents big div pp sol eq ha hc
    exact close_from_three (j:=5) (x:=5) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big hit sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=3) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D6.exponents big div pp sol eq ha hb hc
    exact close_from_three (j:=6) (x:=2) (y:=3) (u:=1) (v:=1) (by decide) (by decide) big hit sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=7) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D7.exponents big div pp sol eq ha hc
    exact close_from_three (j:=7) (x:=7) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big hit sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D8.exponents big div pp sol eq ha hc
    exact close_from_three (j:=8) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=3) (v:=0) (by decide) (by decide) big hit sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D9.exponents big div pp sol eq ha hc
    exact close_from_three (j:=9) (x:=3) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0) (by decide) (by decide) big hit sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=5) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D10.exponents big div pp sol eq ha hb hc
    exact close_from_three (j:=10) (x:=2) (y:=5) (u:=1) (v:=1) (by decide) (by decide) big hit sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=11) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D11.exponents big div pp sol eq ha hc
    exact close_from_three (j:=11) (x:=11) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big hit sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=3) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D12.exponents big div pp sol eq ha hb hc
    exact close_from_three (j:=12) (x:=2) (y:=3) (u:=2) (v:=1) (by decide) (by decide) big hit sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=13) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D13.exponents big div pp sol eq ha hc
    exact close_from_three (j:=13) (x:=13) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big hit sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=7) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D14.exponents big div pp sol eq ha hb hc
    exact close_from_three (j:=14) (x:=2) (y:=7) (u:=1) (v:=1) (by decide) (by decide) big hit sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=5) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D15.exponents big div pp sol eq ha hb hc
    exact close_from_three (j:=15) (x:=3) (y:=5) (u:=1) (v:=1) (by decide) (by decide) big hit sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D16.exponents big div pp sol eq ha hc
    exact close_from_three (j:=16) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=4) (v:=0) (by decide) (by decide) big hit sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
/-- Every sufficiently large prime-successor solution divisible by the primes through
thirteen is also divisible by their product with seventeen. -/
theorem primorial_seventeen {n : ℕ} (big : 2000<n) (div : 30030∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) : 510510∣n := by
  have d : 17∣n := by
    by_contra missing
    let j := 17-n%17
    have nz : n%17≠0 := fun h => missing (Nat.dvd_of_mod_eq_zero h)
    have hj : 0<j := by dsimp only [j]; omega
    have lo : j<17 := by dsimp only [j]; omega
    have sum : n%17+j=17 := by dsimp only [j]; omega
    have hit : 17∣n+j := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod,Nat.mod_eq_of_lt lo,sum,Nat.mod_self]
    exact exclude_offset big div pp sol hj lo hit
  exact (by decide : Nat.Coprime 30030 17).mul_dvd_of_dvd_of_dvd div d

end Erdos889.PrimeSeventeen
#print axioms Erdos889.PrimeSeventeen.primorial_seventeen
