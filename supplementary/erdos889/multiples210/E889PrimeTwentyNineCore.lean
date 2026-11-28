import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
import Mathlib.Data.Nat.Factorization.Induction

/-! A modular certificate for the first multiples of 29 and 41. -/
namespace Erdos889.PrimeTwentyNine

structure Config where
  d : ℕ
  x : ℕ
  y : ℕ
  z : ℕ
  ax : ℕ
  byy : ℕ
  cz : ℕ

structure Row where
  q : ℕ
  k : ℕ
  pool : List ℕ
  other : List ℕ
  m : ℕ
  mask : ℕ
  deriving Inhabited

abbrev Stable (g : Config) (L m : ℕ) :=
  0 < m ∧ g.x^(L+1)%m=g.x%m ∧ g.y^(L+1)%m=g.y%m ∧ g.z^(L+1)%m=g.z%m

theorem cycle {L p m : ℕ} (hL : 0<L) (one : Nat.ModEq m (p^(L+1)) p) (e : ℕ)
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

def residue (g : Config) (L m k a b c : ℕ) :=
  (((g.x^(L+a)%m)*(g.y^(L+b)%m)%m)*(g.z^(L+c)%m)%m+k+g.d*m-g.d)%m

structure H (g : Config) (n a b c : ℕ) : Prop where
  shape : n+g.d=g.x^a*g.y^b*g.z^c
  ha : 0<a
  hb : 0<b
  hc : 0<c ∨ g.z=1
  flat : g.z=1 → c=0
  big : 2000<n
  div : 223092870∣n
  prime : (n+1).Prime
  sol : Erdos889.v_l 1 n=1

theorem residue_eq {g : Config} {n a b c L m : ℕ} (h : H g n a b c) (hL : 0<L)
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

abbrev RowOK (g : Config) (L : ℕ) (r : Row) :=
  r.q.Prime ∧ 0<r.k ∧ r.k<r.q ∧ r.q∈r.pool ∧ Stable g L r.q ∧ Stable g L r.m ∧
  r.mask.testBit (1%r.m)=true ∧
  (∀ i : Fin r.m, r.mask.testBit i.val=true → ∀ p∈r.pool, r.mask.testBit (i.val*p%r.m)=true) ∧
  (∀ p∈r.other, Stable g L p) ∧
  (∀ p : Fin (r.k+1), p.val.Prime → p.val∈r.pool ∨ p.val∈r.other)

abbrev CellOK (g : Config) (L : ℕ) (r : Row) (i j k : ℕ) :=
  residue g L r.q r.k i j k=0 ∧ r.mask.testBit (residue g L r.m r.k i j k)=false ∧
  ∀ p∈r.other, residue g L p r.k i j k≠0

theorem killRow {g : Config} {n a b c L : ℕ} (h : H g n a b c) (hL : 0<L)
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

inductive Rule where
  | target | div (p : ℕ) | prime (q : ℕ) | pool (r : Row)
  deriving Inhabited

def Valid (g : Config) (L : ℕ) : Rule → Prop
  | .target => 12∣L
  | .div p => p∣223092870 ∧ Stable g L p
  | .prime q => q.Prime ∧ q≤2000 ∧ Stable g L q
  | .pool r => RowOK g L r

instance (g : Config) (L : ℕ) (r : Rule) : Decidable (Valid g L r) := by
  cases r <;> unfold Valid <;> infer_instance

abbrev Target (g : Config) (a b c : ℕ) := a%12=g.ax ∧ b%12=g.byy ∧ c%12=g.cz

def Hit (g : Config) (L i j k : ℕ) : Rule → Prop
  | .target => Target g i j k
  | .div p => residue g L p 0 i j k≠0
  | .prime q => residue g L q 1 i j k=0
  | .pool r => CellOK g L r i j k

instance (g : Config) (L i j k : ℕ) (r : Rule) : Decidable (Hit g L i j k r) := by
  cases r <;> unfold Hit <;> infer_instance

theorem kill {g : Config} {n a b c L : ℕ} (h : H g n a b c) (hL : 0<L) (bad : ¬Target g a b c)
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

structure Keys where
  count : ℕ
  bits : ℕ
  data : ℕ

def coord (keys : Keys) (i d : ℕ) :=
  (keys.data >>> (keys.bits*(3*i+d))) % 2^keys.bits

abbrev Match (t a b c : ℕ) (keys : Keys) :=
  ∃ i<keys.count, a%t=coord keys i 0 ∧ b%t=coord keys i 1 ∧ c%t=coord keys i 2

structure Stage where
  cfg : Config
  t : ℕ
  s : ℕ
  old : Keys
  next : Keys
  rules : List Rule
  bits : ℕ
  codes : ℕ

def pick (g : Stage) (i x y z : ℕ) :=
  (g.codes >>> (g.bits*(if g.cfg.z=1 then (i*g.s+x)*g.s+y else ((i*g.s+x)*g.s+y)*g.s+z))) % 2^g.bits

abbrev Test (g : Stage) (i x y z : ℕ) : Prop :=
  if g.cfg.z=1 ∧ z≠0 then True else
  let u := coord g.old i 0 + g.t*x
  let v := coord g.old i 1 + g.t*y
  let w := coord g.old i 2 + g.t*z
  let code := pick g i x y z
  if code<g.rules.length then Hit g.cfg (g.t*g.s) u v w g.rules[code]!
  else let j := code-g.rules.length
       j<g.next.count ∧ u=coord g.next j 0 ∧ v=coord g.next j 1 ∧ w=coord g.next j 2

theorem refine {n a b c : ℕ} (g : Stage) (h : H g.cfg n a b c) (bad : ¬Target g.cfg a b c)
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

theorem supported_offset {n j x y q : ℕ} (pq : q.Prime) (jq : j<q) (hj : 0<j) (jl : j<29) (div : 223092870∣n)
    (hit : q∣n+j) (xy : x*y∣n+j) (cop : (x*y).Coprime q)
    (small : ∀ p : Fin 29, p.val.Prime → p.val∣j → p.val=x ∨ p.val=y)
    (sol : v_l 1 n=1) : ∃ a b c : ℕ, n+j=x^a*y^b*q^c ∧ 0<a ∧ 0<b ∧ 0<c := by
  have whole := cop.mul_dvd_of_dvd_of_dvd xy hit
  obtain ⟨t,ht⟩ := whole
  have pos : 0<t := by by_contra! h; rw [show t=0 by omega,mul_zero] at ht; omega
  obtain ⟨a,b,c,eq⟩ := supported_three t x y q pos (by
    intro p pp dp
    have dn : p∣n+j := ht ▸ dvd_mul_of_dvd_right dp _
    by_cases low : p≤j
    · have tab : ∀ r : Fin 29, r.val.Prime → r.val∣223092870 := by decide
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

end Erdos889.PrimeTwentyNine
