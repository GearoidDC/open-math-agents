import E889Finite30Core

/-! A finite sieve using a modular filter to join two lists of smooth factors.
The filter may admit extra pairs. Every admitted product is checked directly. -/
namespace Erdos889.JoinSieve
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
def walk (B : ℕ) (f : ℕ → Bool) : List ℕ → ℕ → Bool
  | [], x => f x
  | r::rs, x => FiniteThirty.scan B r (walk B f rs) 201 x

theorem walk_sound {B x z : ℕ} (f : ℕ → Bool) (rs : List ℕ)
    (hi : B<2^201) (xp : 0<x) (zp : 0<z) (cap : x*z≤B)
    (prime : ∀ q∈rs, q.Prime) (support : ∀ q : ℕ, q.Prime → q∣z → q∈rs)
    (all : walk B f rs x=true) : f (x*z)=true := by
  induction rs generalizing x z with
  | nil =>
    have one : z=1 := by
      by_contra ne
      obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd ne
      simpa using support q pq dq
    simpa only [walk,one,mul_one] using all
  | cons r rs ih =>
    have pr := prime r (by simp)
    let e := z.factorization r
    let w := z/r^e
    have wp : 0<w := Nat.ordCompl_pos r zp.ne'
    have eq : r^e*w=z := Nat.ordProj_mul_ordCompl_eq_self _ _
    have nz : ¬r∣w := Nat.not_dvd_ordCompl pr zp.ne'
    have re : 0<r^e := pow_pos pr.pos _
    have cap' : x*r^e*w≤B := by simpa only [Nat.mul_assoc,eq] using cap
    have capR := (Nat.le_mul_of_pos_right (x*r^e) wp).trans cap'
    have exp : e<201 := by
      by_contra! low
      have := calc
        2^201 ≤ 2^e := Nat.pow_le_pow_right (by decide) low
        _ ≤ r^e := Nat.pow_le_pow_left pr.two_le e
        _ ≤ x*r^e := Nat.le_mul_of_pos_left _ xp
        _ ≤ B := capR
      omega
    have after := FiniteThirty.scan_sound (walk B f rs) pr.pos all exp capR
    have res := ih (Nat.mul_pos xp re) wp cap'
      (fun q mq => prime q (List.mem_cons_of_mem r mq)) (fun q pq dq =>
        (List.mem_cons.mp (support q pq (dq.trans (Nat.ordCompl_dvd z r)))).resolve_left
          (by rintro rfl; exact nz dq)) after
    simpa only [Nat.mul_assoc,eq] using res

def Supported (primes : List ℕ) (x : ℕ) := ∀ q : ℕ, q.Prime → q∣x → q∈primes

private theorem split_factors (l r : List ℕ) (z : ℕ) (pos : 0<z)
    (support : Supported (l++r) z) :
    ∃ x y, 0<x ∧ 0<y ∧ x*y=z ∧ Supported l x ∧ Supported r y := by
  induction z using induction_on_primes with
  | zero => omega
  | one =>
    have h (s : List ℕ) : Supported s 1 := by intro q pq dq; exact (pq.not_dvd_one dq).elim
    exact ⟨1,1,by decide,by decide,rfl,h l,h r⟩
  | prime_mul q z pq ih =>
    have zp : 0<z := Nat.pos_of_mul_pos_left pos
    obtain ⟨x,y,xp,yp,hx,sx,sy⟩ := ih zp (fun a pa da => support a pa (dvd_mul_of_dvd_right da q))
    have ext (s : List ℕ) (w : ℕ) (sw : Supported s w) (mq : q∈s) : Supported s (q*w) := by
      intro a pa da
      rcases pa.dvd_mul.mp da with da|da
      · exact (Nat.prime_dvd_prime_iff_eq pa pq).mp da ▸ mq
      · exact sw a pa da
    rcases List.mem_append.mp (support q pq (dvd_mul_right q z)) with mq|mq
    · exact ⟨q*x,y,Nat.mul_pos pq.pos xp,yp,by rw [Nat.mul_assoc,hx],ext l x sx mq,sy⟩
    · exact ⟨x,q*y,xp,Nat.mul_pos pq.pos yp,by rw [Nat.mul_left_comm,hx],sx,ext r y sy mq⟩

structure Row where
  left : List ℕ
  right : List ℕ
  modulus : ℕ
  filters : List (ℕ × ℕ)
  codes : List ℕ

def marked (g : Row) (t : ℕ) :=
  g.filters.all (fun f => f.2.testBit (t%f.1))

def inverse (y m : ℕ) : ℕ := (Nat.gcdA y m % (m:ℤ)).toNat

def rightOK (g : Row) (k y : ℕ) :=
  let i := inverse y g.modulus
  decide (y*i % g.modulus = 1%g.modulus) && marked g (k*i%g.modulus)

def pairOK (g : Row) (M k hi x y : ℕ) :=
  let n := x*y-k
  if 10^30<n ∧ n≤hi ∧ M∣n then g.codes.any (FiniteThirty.test n) else true

def rowOK (g : Row) (M p k hi : ℕ) :=
  walk (hi+p) (rightOK g k) g.right p &&
  walk (hi+p) (fun x => !marked g (x%g.modulus) ||
      walk (hi+p) (pairOK g M k hi x) g.right p) g.left 1

def valid (g : Row) (M p k : ℕ) : Prop :=
  g.modulus∣M ∧ (∀ q∈g.left, Nat.Prime q) ∧ (∀ q∈g.right, Nat.Prime q) ∧ p∈g.left++g.right ∧
    ∀ i : Fin (k+1), i.val.Prime → i.val∣k → i.val∈g.left++g.right

instance (g : Row) (M p k : ℕ) : Decidable (valid g M p k) := by unfold valid; infer_instance

theorem row_sound {n M p k hi : ℕ} (g : Row) (pp : p.Prime) (kp : k<p)
    (div : M∣n) (hit : p∣n+k) (lo : 10^30<n) (hn : n≤hi) (bound : hi+p<2^201)
    (support : ∀ q : ℕ, q.Prime → q∣n+k → q=p ∨ q∣k) (positive : 0<k)
    (val : valid g M p k) (check : rowOK g M p k hi=true) : v_l 1 n≠1 := by
  obtain ⟨md,pl,pr,pm,sp⟩ := val
  obtain ⟨w,fac⟩ := hit
  have wp : 0<w := by by_contra! h; rw [show w=0 by omega,mul_zero] at fac; omega
  have sw : Supported (g.left++g.right) w := by
    intro q pq dq
    rcases support q pq (fac ▸ dvd_mul_of_dvd_right dq p) with rfl|d
    · exact pm
    · exact sp ⟨q,Nat.lt_succ_of_le (Nat.le_of_dvd positive d)⟩ pq d
  obtain ⟨x,y,xp,yp,eq,sx,sy⟩ := split_factors g.left g.right w wp sw
  let Y := p*y
  have yp' : 0<Y := Nat.mul_pos pp.pos yp
  have xy : x*Y=n+k := by dsimp only [Y]; rw [Nat.mul_left_comm,eq,←fac]
  have cap : x*Y≤hi+p := by omega
  have capY := (Nat.le_mul_of_pos_left Y xp).trans cap
  have capX := (Nat.le_mul_of_pos_right x yp').trans cap
  simp only [rowOK,Bool.and_eq_true] at check
  obtain ⟨okR,okL⟩ := check
  have r := walk_sound (rightOK g k) g.right bound pp.pos yp capY pr sy okR
  change rightOK g k Y=true at r
  simp only [rightOK,Bool.and_eq_true,decide_eq_true_eq] at r
  obtain ⟨invOK,mark⟩ := r
  let i := inverse Y g.modulus
  have yi : Nat.ModEq g.modulus (Y*i) 1 := invOK
  have nk : Nat.ModEq g.modulus (n+k) k := by
    simpa only [zero_add] using (Nat.modEq_zero_iff_dvd.mpr (md.trans div)).add_right k
  have key : Nat.ModEq g.modulus x (k*i) := calc
    x = x*1 := (Nat.mul_one _).symm
    _ ≡ x*(Y*i) [MOD g.modulus] := yi.symm.mul_left x
    _ = (n+k)*i := by rw [←Nat.mul_assoc,xy]
    _ ≡ k*i [MOD g.modulus] := nk.mul_right i
  change marked g (k*i%g.modulus)=true at mark
  have mx : marked g (x%g.modulus)=true := by rw [show x%g.modulus = k*i%g.modulus from key]; exact mark
  have l := walk_sound (fun a => !marked g (a%g.modulus) || walk (hi+p) (pairOK g M k hi a) g.right p)
    g.left bound (by decide : 0<1) xp (by simpa only [one_mul] using capX) pl sx okL
  simp only [one_mul,mx,Bool.not_true,Bool.false_or] at l
  have pair := walk_sound (pairOK g M k hi x) g.right bound pp.pos yp capY pr sy l
  change pairOK g M k hi x Y=true at pair
  simp only [pairOK,xy,Nat.add_sub_cancel,if_pos (show 10^30<n ∧ n≤hi ∧ M∣n from ⟨lo,hn,div⟩)] at pair
  obtain ⟨c,_,ok⟩ := List.any_eq_true.mp pair
  exact FiniteThirty.test_sound ok

theorem step {n M p hi : ℕ} (pp : p.Prime) (cop : M.Coprime p)
    (small : ∀ q∈List.range p, q.Prime → q∣M) (div : M∣n) (sol : v_l 1 n=1)
    (lo : 10^30<n) (hn : n≤hi) (bound : hi+p<2^201) (g : ℕ → Row)
    (tabs : ∀ k : Fin p, 0<k.val → valid (g k.val) M p k.val ∧ rowOK (g k.val) M p k.val hi=true) : M*p∣n := by
  apply FiniteThirty.force_step pp cop small div sol
  intro k pos lt hit support
  obtain ⟨v,c⟩ := tabs ⟨k,lt⟩ pos
  exact row_sound (g k) pp lt div hit lo hn bound support pos v c sol

end Erdos889.JoinSieve

#print axioms Erdos889.JoinSieve.step

