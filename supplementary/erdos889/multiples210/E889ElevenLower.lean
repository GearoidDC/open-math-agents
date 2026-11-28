import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
import Mathlib.Data.Nat.Factorization.Induction

/-! A modular certificate for the first multiple of eleven. -/
namespace Erdos889.PrimeElevenLower

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
  div : 210∣n
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
  | .div p => p∣210 ∧ Stable g L p
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



namespace D2
private def cfg : Config := ⟨2,2,11,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨4,4,0x290a5045061⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .target,
  .div 7,
  .pool ⟨13,9,[13,3],[2,5,7],63,0xc028940844220a⟩]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x10101010101101010101010030403030803101010101010010101010101101010101010070303060303101010101010010101010101101010101010030305030302101010101010⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨9,6,0xb9034a40a2903474041d01c440111028140705⟩
private def rows60 : List Rule := [
  .pool ⟨13,4,[13,2],[3],55,0x12081594076396⟩,
  .prime 31,
  .pool ⟨13,10,[13,2,5],[3,7],275,0x120915d60763b62c103b280fcf6c58a457505f8e589140eeb0bf3cb16291d961767b6⟩,
  .pool ⟨31,13,[31,11],[2,3,5,7,13],5,0x2⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],11,0x23a⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨13,7,[13,7],[2,3,5],55,0x12081594076396⟩,
  .pool ⟨13,8,[13,2],[3,5,7],775,0x6884c020a0000850880000005084220084c004000040100026008024190810408120a40040210041400430000300001418280000c0000c20028200840200250481020810982401006400080200002003210044210a000000110a10000504032116⟩,
  .pool ⟨13,8,[13,2],[3,5,7],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨13,8,[13,2],[3,5,7],31,0x7ffffffe⟩,
  .pool ⟨13,8,[13,2],[3,5,7],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,5,0x41d099a4e83a14a4a94a52949424e8398c6318c6318c6318c6318c6318c63186520852888448084f1884e2344c58c40000200800000001000000002008000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 4 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨8,7,0xba8004e4034ca01a2900d2c8068740648203205⟩
private def rows120 : List Rule := [
  .pool ⟨13,10,[13,2,5],[3,7],1271,0x1021508163300c5176c1a1b4445b123423e2ca4029903cf647175339b52495e600d4eec1cb1c934110dc3c2540fb0ae7d246b476f224b0bc38e2359659223e86c5400a275f9b9e552a1da12f4971f71070650b7a45ab518622051badf55c9e83aa65965398e342f29bb091921db418ae00fd5bc1c4e77d32c72c7480d4ff9842db526315151d9083f66afd2cb83bd23725ddd07a3c9171cff31976f57bf7e⟩,
  .pool ⟨41,22,[41,2,17,19],[3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,23,[41,13,17,19,23],[2,3,5,7,11],77,0x129974700330038ba652⟩,
  .pool ⟨41,4,[41,2],[3],31,0x121d47b6⟩,
  .pool ⟨31,23,[31,13,17,19,23],[2,3,5,7,11],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,7,[41,7],[2,3,5],165,0x1241204348945300201800060100328a44b0812092⟩,
  .pool ⟨13,8,[13,2],[3,5,7],451,0x688580269400082c82200000008448a0800c0810005000001001903060c09800800000a00081030010512210000000441341000296401a116⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,4,0x6e6d5c5b04040a0900000303212180700000⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 9, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 9 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨0,8,0x0⟩
private def rows240 : List Rule := [
  .pool ⟨13,10,[13,2,5],[3,7],17,0x1fffe⟩,
  .pool ⟨13,10,[13,2,5],[3,7],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨13,8,[13,2],[3,5,7],17,0x1a316⟩,
  .pool ⟨13,8,[13,2],[3,5,7],679,0x120901974503926e3172004a871838b94b426e19050070c8902b12801ed5dac7258e255c2cf852c7013754117b14a5c08344598a530c841406fcb323e2ccb17e5d6381ad0d2262e518a5ef913308b43b55065f2f36⟩,
  .pool ⟨17,6,[17,2,3],[5],1261,0x1eb238252f10648822e95840a09342052523a2189a01800221020978c06144882188252a30601a560a61504a00001560211950304748ea078004e41c84830201644e0200208823306804e4014b3089e44334a009c8058331044100101c89a01030484e09c8007815c4b88302a62101aa00001482a1941a960183152904610448a180c7a4102110006016461171292810b2414086a5d10449823d2907135e⟩,
  .pool ⟨241,17,[241],[2,3,5,7,11,13,17],3,0x2⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,3,0x55489a208041041208041208⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 8 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 210∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+2=2^a*11^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D2


namespace D3
private def cfg : Config := ⟨3,3,11,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x49085⟩
private def rows12 : List Rule := [
  .div 5,
  .target,
  .div 7,
  .prime 13,
  .pool ⟨13,6,[13,2,3],[5],80,0x5511415110b19d05335e⟩,
  .pool ⟨13,5,[13,5],[2,3],4,0x2⟩]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x5126974aa0000000000000000000000000006964aa5120000000000000000000000000004aa512691000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨10,6,0x1ce40139028840721010840d15028540415004540229⟩
private def rows60 : List Rule := [
  .pool ⟨31,5,[31,5],[2,3],11,0x23a⟩,
  .pool ⟨31,4,[31,2],[3],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],264,0x8808a08200a08828800008028208000800200020828020000228220a00820a2022⟩,
  .pool ⟨31,11,[31],[2,3,5,7,11],3,0x2⟩,
  .pool ⟨31,7,[31,7],[2,3,5],55,0x12081594076396⟩,
  .pool ⟨31,4,[31,2],[3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,23,[61,17,19,23],[2,3,5,7,11,13],868,0x280000288a882a80aa2028028820200880a80008220882020a00222200282020882208000a8088020208a00a022a80aa08a88a00000a202aa8a00008800a0020a0a00882a2288880a2a082280a282822a2022a20a0a280a2082a280888a22a0880282820028008800028aaa02⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .pool ⟨31,8,[31,2],[3,5,7],33,0x1a2030116⟩,
  .pool ⟨61,4,[61,2],[3],31,0x68818116⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],61,0x1ffffffffffffffe⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,5,0x1acbaacb52d674d69354a2a83d4941cc2280830106270c46010a020c4418820⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨12,7,0x192e805084010ba0262101c28806854028a203215010288009440402a00215⟩
private def rows120 : List Rule := [
  .pool ⟨31,4,[31,2],[3],123,0x10000124014004012182110536⟩,
  .pool ⟨31,4,[31,2],[3],32,0xd1010117⟩,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩,
  .pool ⟨41,6,[41,2,3],[5],143,0x42148073495103e1b21836746511bad53de⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],160,0x1111010110a19901230a4501415100b18d05335e⟩,
  .pool ⟨41,14,[41,2,7,11],[3,5,13],488,0x3513b93ddf531d515975399f1bf11333bb51b5993f79f9fdb3f5dd3913bf27157fd799b1759151d317ddb5fb55737ff15f1dd7b3dbdb9f7b1997d57fb6⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],1312,0xf599416313111545011581191b11991311114119418501411145910151416105211113011b53094110017113014151098131311151219d0511411331150101710541030505050191035511054141315101000101151905054111558113014141418105411d01015119910511417309151119190321150501911d0011052195b101911109410d0515011345110501430531051111913311b131035101455111918d05335e⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,10,[41,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],656,0x109834b4325396599052fb98f693f13e1e389bba555cd61e17717c30dd503afdda3d7a56b4b6dcfee1119935b5335297589153fa99f792f03f1f399aba545dd71f16707d31dc513bfcdb3c7b57b5b7ddffe⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,5,0x4252810842a9cf4218c42ce45890901bdc3108426b16a00420⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 10, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 10 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨1,8,0x6415⟩
private def rows240 : List Rule := [
  .pool ⟨31,23,[31,19,23],[2,3,5,7,11,13,17],964,0x200a8820880200a0a8a22aa808a80a2082822a8a080802aa0800280202222220200a00082aa0080828aa20a082280a880aaa228a828020088208a80222a808a288aa2a8280822000a880a8228a0a200828a8aa0028aaa0aa2a220222a2a82aa8a002a8a8a08022828a20a808a80022080a0aa2a88a2880aa2⟩,
  .pool ⟨17,6,[17,2,3],[5],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨17,15,[17,3,5],[2,7,11,13],1025,0x242031006008a0f6204002402122053040c00ab80c0da43222a12101880100c126b14000962101523902260815c0644c2193050909040208860835c80000b000089148303802ae0702614e982869402000c41041ec4084248000540a40898205f4391b0a6441434a410082008a4d72802024401220730c0e002fa0c09a43a22a⟩,
  .pool ⟨17,8,[17,2],[3,5,7],32,0x30117⟩,
  .pool ⟨17,15,[17,3,5],[2,7,11,13],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨241,15,[241,3,5],[2,7,11,13],217,0x1530503d00a30404202c9942104008210a64d01080831402f02832a⟩,
  .pool ⟨97,14,[97,2,7,11],[3,5,13],372,0xd325b6994514d941b0192190d34912814d901149b69361b0d92db25101365029125961309301b0536514532db4996⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],97,0x1eb628b476067981b8b451b5e⟩,
  .pool ⟨41,31,[41,19,23,29],[2,3,5,7,11,13,17,31],51,0x21a0022996832⟩,
  .pool ⟨17,15,[17,3,5],[2,7,11,13],217,0x1530503d00a30404202c9942104008210a64d01080831402f02832a⟩,
  .pool ⟨31,23,[31,19,23],[2,3,5,7,11,13,17],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,4,0x1bb11bb13aa3a33a911981181771611c0115342323320110⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 12, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 12 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨19,10,[19,2,5],[3,7],481,0x1fba6e34e2a13996a02730197b0f08f3604424ad7c451b0cba2c06a81652fd29a05580d174c36288fad490881b3c43c37a60339015a672151cb1d977e⟩,
  .pool ⟨19,14,[19,2,7,11],[3,5,13],372,0xd325b6994514d941b0192190d34912814d901149b69361b0d92db25101365029125961309301b0536514532db4996⟩,
  .pool ⟨19,4,[19,2],[3],73,0x1eb22c742790b8d135e⟩,
  .pool ⟨19,4,[19,2],[3],241,0x1a246480a08200027002003000005430a8000030010039000104140498916⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,2,0x2e540⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 1 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 210∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+3=3^a*11^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D3


namespace D4
private def cfg : Config := ⟨4,2,11,1,2,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨4,4,0x8a02a046062⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .target,
  .div 7,
  .prime 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x10101010101131813131713010101010101101010101010010101010101141313161313010101010101101010101010010101010101131315131312010101010101101010101010⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨2,6,0x32e803a2⟩
private def rows60 : List Rule := [
  .pool ⟨13,8,[13,2],[3,5,7],55,0x12081594076396⟩,
  .prime 61,
  .pool ⟨13,7,[13,7],[2,3,5],55,0x12081594076396⟩,
  .pool ⟨13,3,[13,3],[2],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩,
  .pool ⟨13,3,[13,3],[2],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨13,3,[13,3],[2],61,0x1713e6940a59f23a⟩,
  .pool ⟨13,5,[13,5],[2,3],279,0x4584024032d24080d021005001864804000000201261800a00840b01024b4c024021a2⟩,
  .pool ⟨13,5,[13,5],[2,3],175,0x280024220d02040041a00080883400500102a002022⟩,
  .pool ⟨13,5,[13,5],[2,3],61,0x1713e6940a59f23a⟩,
  .pool ⟨13,5,[13,5],[2,3],183,0x4406824020400020424880000112420400020402416022⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0x7999788888667768888877666b334355555334a3555553433322222222222222222222111110000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 4 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨2,7,0x6eec0373a⟩
private def rows120 : List Rule := [
  .pool ⟨41,6,[41,2,3],[5],99,0x7ac8e0d5bc44f223dab07135e⟩,
  .pool ⟨13,3,[13,3],[2],205,0x24201000200820d6200002400022052040c002b80c09843220a⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,2,0xd944⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 2 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨0,8,0x0⟩
private def rows240 : List Rule := [
  .pool ⟨13,3,[13,3],[2],1037,0x20206800200123aa8180000420a8010440085021224822a20c8000481001140024940a189032281e20a0124300d48050a100043008a0250d2004324040602e01008182202b0860420400901c184c8250002548a0204c40800a2042041180800010f230989d302052838004c0288400126c068622882014b38420001e6800a01e22a⟩,
  .pool ⟨13,3,[13,3],[2],935,0x1021409022104c3114808160530a00a024625854194062c45720e1198410188500d6579082785226002c334412808b120227a5c11b84613c685310610129580634000a339622bc254910c3bd03308096900500ce54a5a352447098015818e525c50190c2b8c72b10712cec5212c534ab12d85335e⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0x5a⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 2 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 210∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+4=2^a*11^b) (ha : 0<a) (hb : 0<b) : a%12=2 ∧ b%12=0 := by
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
end D4


namespace D5
private def cfg : Config := ⟨5,5,11,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨9,4,0xab04b0890290670a5045083023⟩
private def rows12 : List Rule := [
  .div 3,
  .div 7,
  .target,
  .pool ⟨13,10,[13,2,5],[3,7],112,0x131050301332215211107152736⟩]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0xc01010b0101101010101010010a01010901101010101010010108010103101010101010070101060101101010101010010501010401101010101010010103010102101010101010⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨17,6,0xdb702adc07b7012dc0dab02aac07ab012ac0d9302a4c07930124c0d8702a1c07870121c0187⟩
private def rows60 : List Rule := [
  .pool ⟨13,12,[13,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨13,12,[13,2,3],[5,7,11],495,0x4031140e43066514a9610a452d6c3216748dc77812018c207318a328a55b0856292b6190b3a46e3bc4120d4103d0e119452a5a4391c95b0c959d2773de⟩,
  .pool ⟨13,12,[13,2,3],[5,7,11],488,0xf59971e11701559101bd8101113149030181455173a11131110905a19361ab0d930b41211119110b9d154503018125191101037b01135501d10f1d335e⟩,
  .pool ⟨13,11,[13],[2,3,5,7,11],3,0x2⟩,
  .pool ⟨13,3,[13,3],[2],244,0xa08820a00200008000a88000002008020080000022a00020000800a08220a⟩,
  .prime 31,
  .pool ⟨13,3,[13,3],[2],31,0x7ffffffe⟩,
  .pool ⟨13,3,[13,3],[2],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .prime 61,
  .pool ⟨13,3,[13,3],[2],61,0x1713e6940a59f23a⟩,
  .pool ⟨13,7,[13,7],[2,3,5],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .pool ⟨13,7,[13,7],[2,3,5],248,0x802a200200822a0a882008008a8020a2a808a88aa2880a0228aa22a202a8a⟩,
  .pool ⟨13,7,[13,7],[2,3,5],279,0x480000012400080402000400082480400000000002080080080090002490402402082⟩,
  .pool ⟨31,16,[31,2,11],[3,5,7,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨61,10,[61,2,5],[3,7],124,0x5151111111115113315113113111536⟩,
  .pool ⟨61,10,[61,2,5],[3,7],231,0x410120520402090136084524500910c201160b2c14816126192536⟩,
  .pool ⟨13,3,[13,3],[2],549,0x100004020900000000100000020100804020000004020000800000100004000000000000000800020000004000100a00000100804020100000020000000020900800220a⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,6,0x61492491852492461501d018524924614924930b30530c2cc14c28a28528c2cc14c2082052000400010020000800800020020000800400010c30c30c30c30c30c30c30c30c30c30c30c30e181f78d75c6da34e38f38d6585d635551349130530c2cc14c30b28528a28a14a28a28528a2892461492082052071061441c41851071061440c30c30c30c30c30c30c30c30c30c30c30c30c0040040001001000040040002002000040040⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 9, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 9 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨10,7,0x12e60093701cb380e4ac05a9e02d13016a180b41c0128600907⟩
private def rows120 : List Rule := [
  .prime 41,
  .pool ⟨31,16,[31,2,11],[3,5,7,13],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨41,21,[41,3,7,17,19],[2,5,11,13],396,0x88a00222208080a2080a8aa02a8a8082280808222200288828a02aaa022aa828a288a08022008288a28a0aaa202aaa028a⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],820,0x131509111051112b11101131011116d53121111803118719101191811114d13187199411190111d8109503115ab5316311989391c113501111011b9051010d115015b14959101311817192111121715011304931923511031154771125119417b90959d07335e⟩,
  .pool ⟨41,23,[41,17,19,23],[2,3,5,7,11,13],77,0x129974700330038ba652⟩,
  .pool ⟨41,28,[41,2,7,17,19,23],[3,5,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨41,15,[41,3,5],[2,7,11,13],616,0xa88282a800a820200aa08a000028a0288280888802808802080a2a208800a222080a080082000000820020a020888a002208a8a0208022028022220282280a280000a20aa008082a002a82822a⟩,
  .pool ⟨41,6,[41,2,3],[5],99,0x7ac8e0d5bc44f223dab07135e⟩,
  .pool ⟨41,4,[41,2],[3],32,0x2070317⟩,
  .pool ⟨41,4,[41,2],[3],33,0x1a2030116⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,5,0x380e021886525691d47498a4201004314c54ad2a5a549210848a20801c07314c52108478dc31344c08020⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 17, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 17 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨4,8,0xd28b005a1300d2bb005a43⟩
private def rows240 : List Rule := [
  .pool ⟨17,2,[17,2],[],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨17,8,[17,2],[3,5,7],33,0x1a2030116⟩,
  .pool ⟨17,10,[17,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,26,[31,2,13,19,23],[3,5,7,11,17],176,0x3f5591315b891db3b9f7527b11d1751fcd59f7bdb316⟩,
  .pool ⟨31,27,[31,3,11,19,23],[2,5,7,13,17],328,0xa0a822aaa200888028a08a082a888a820002280a00a028800082a222a820a20a280222008aaa882a0a⟩,
  .pool ⟨17,2,[17,2],[],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,4,0x2332511501104224011092287226100123320110⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 10, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 10 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨19,7,[19,7],[2,3,5],164,0x8820a0220282088002aa88a282a02a0a288aaa⟩,
  .pool ⟨37,10,[37,2,5],[3,7],44,0x13153151776⟩,
  .pool ⟨19,8,[19,2],[3,5,7],64,0xa4f1a5f0b4f1b5f⟩,
  .pool ⟨37,10,[37,2,5],[3,7],41,0x1b382b50736⟩,
  .pool ⟨19,7,[19,7],[2,3,5],181,0x1040040800003000000000000000000003000004080082⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,3,0x4936e49244936c9200492489200⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 4 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 210∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+5=5^a*11^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D5

namespace SmallOffsets
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
private theorem two_factor_support {m p q : ℕ} (mp : 0 < m) (pp : p.Prime)
    (pool : ∀ r : ℕ, r.Prime → r∣m → r=p ∨ r=q) :
    ∃ a b : ℕ, m=p^a*q^b := by
  let k := m/p^m.factorization p
  have pos : 0<k := Nat.ordCompl_pos p mp.ne'
  have no : ¬p∣k := Nat.not_dvd_ordCompl pp mp.ne'
  have form : p^m.factorization p*k=m := Nat.ordProj_mul_ordCompl_eq_self _ _
  have pure : k=q^k.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd pos.ne' (by
    intro r pr dr
    exact (pool r pr (dr.trans (Nat.ordCompl_dvd m p))).resolve_left (by rintro rfl; exact no dr))
  exact ⟨_,_,by rw [←pure]; exact form.symm⟩


private theorem no_twelfth {n j z : ℕ} (hj : 0<j) (small : j≤6) (big : 1<z)
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
  have classifyA (p : ℕ) (pp : p.Prime) (low : p≤12) (dp : p∣t+1) : p=2 := by
    have tab : ∀ q : Fin 13, q.val.Prime → ∀ u : Fin q.val, (u.val^4+1)%q.val=0 → q.val=2 := by decide +kernel
    have m := ((Nat.mod_modEq z p).pow 4).add_right 1
    exact tab ⟨p,by omega⟩ pp ⟨z%p,Nat.mod_lt _ pp.pos⟩ (m.trans (Nat.modEq_zero_iff_dvd.mpr dp))
  obtain ⟨p,pp,hp,dp⟩ : ∃ p : ℕ, p.Prime ∧ 12<p ∧ p∣t+1 := by
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
  have hq : 12<q := by
    by_contra! low
    have tab : ∀ q : Fin 13, q.val.Prime → ∀ u : Fin q.val, ¬Nat.ModEq q.val (u.val^4) (u.val^8+1) := by decide +kernel
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

private abbrev Offset (k p : ℕ) := (k=2 ∧ p=2) ∨ (k=3 ∧ p=3) ∨ (k=4 ∧ p=2) ∨ (k=5 ∧ p=5)

private theorem small_shape {n k p : ℕ} (div : 210∣n) (which : Offset k p)
    (hit : 11∣n+k) (sol : Erdos889.v_l 1 n=1) :
    ∃ a b : ℕ, 0<a ∧ 0<b ∧ n+k=p^a*11^b := by
  have pp : p.Prime := by rcases which with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
  have hp : 0<k ∧ k≤5 ∧ p≤5 ∧ p∣n+k := by
    rcases which with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> omega
  obtain ⟨a,b,e⟩ : ∃ a b : ℕ, n+k=p^a*11^b := by
    apply two_factor_support (by omega) pp
    intro r pr dr
    by_cases early : r≤k
    · left
      have tab : ∀ q : Fin 6, q.val.Prime → q.val=2 ∨ q.val=3 ∨ q.val=5 := by decide
      have options := tab ⟨r,by omega⟩ pr
      change r=2 ∨ r=3 ∨ r=5 at options
      rcases which with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases options with rfl|rfl|rfl <;> omega
    by_contra! ne
    exact two_primes (by omega) pr (by decide : Nat.Prime 11) ne.2 (by omega) (by omega) dr hit sol
  refine ⟨a,b,?_,?_,e⟩
  · by_contra! ha
    have z : a=0 := by omega
    have d := hp.2.2.2
    rw [e,z,pow_zero,one_mul] at d
    have eq := (Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 11)).mp (pp.dvd_of_dvd_pow d)
    omega
  · by_contra! hb
    have z : b=0 := by omega
    rw [e,z,pow_zero,mul_one] at hit
    have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 11) pp).mp
      ((by decide : Nat.Prime 11).dvd_of_dvd_pow hit)
    omega

private theorem finish {n k p a b i : ℕ} (hn : 2000<n) (hk : 0<k) (small : k≤5)
    (power : k=p^i) (shape : n+k=p^a*11^b) (ra : a%12=i) (rb : b%12=0)
    (sol : Erdos889.v_l 1 n=1) : False := by
  let z := p^(a/12)*11^(b/12)
  have split (x s : ℕ) : x^s=x^(s%12)*(x^(s/12))^12 := by
    rw [←pow_mul,←pow_add,Nat.mul_comm (s/12),Nat.mod_add_div]
  have tw : n+k=k*z^12 := by
    rw [shape,split p a,split 11 b,ra,rb,←power,pow_zero,one_mul]
    dsimp only [z]; rw [mul_pow]; ring
  have high : 1<z := by
    by_contra! low
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp low with h|h <;> simp [h] at tw <;> omega
  exact no_twelfth hk (by omega) high tw sol

theorem exclude {n k : ℕ} (hn : 2000<n) (div : 210∣n) (succ : (n+1).Prime)
    (sol : Erdos889.v_l 1 n=1) (pos : 0<k) (low : k≤5) (hit : 11∣n+k) : False := by
  interval_cases k
  · have e := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 11) succ).mp hit; omega
  · obtain ⟨a,b,ha,hb,shape⟩ := small_shape div (p:=2) (by decide : Offset 2 2) hit sol
    obtain ⟨ra,rb⟩ := D2.exponents hn div succ sol shape ha hb
    exact finish hn (by decide : 0<2) (by decide) (by decide : 2=2^1) shape ra rb sol
  · obtain ⟨a,b,ha,hb,shape⟩ := small_shape div (p:=3) (by decide : Offset 3 3) hit sol
    obtain ⟨ra,rb⟩ := D3.exponents hn div succ sol shape ha hb
    exact finish hn (by decide : 0<3) (by decide) (by decide : 3=3^1) shape ra rb sol
  · obtain ⟨a,b,ha,hb,shape⟩ := small_shape div (p:=2) (by decide : Offset 4 2) hit sol
    obtain ⟨ra,rb⟩ := D4.exponents hn div succ sol shape ha hb
    exact finish hn (by decide : 0<4) (by decide) (by decide : 4=2^2) shape ra rb sol
  · obtain ⟨a,b,ha,hb,shape⟩ := small_shape div (p:=5) (by decide : Offset 5 5) hit sol
    obtain ⟨ra,rb⟩ := D5.exponents hn div succ sol shape ha hb
    exact finish hn (by decide : 0<5) (by decide) (by decide : 5=5^1) shape ra rb sol
end SmallOffsets

end Erdos889.PrimeElevenLower
#print axioms Erdos889.PrimeElevenLower.SmallOffsets.exclude
