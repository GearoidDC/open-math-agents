import E889SquareTwentyNine

/-! Pell and congruence certificates for a missing 37. -/

namespace Erdos889.SquareThirtySeven

def mul (d : ℕ) (a b : ℕ × ℕ) : ℕ × ℕ :=
  (a.1*b.1+d*a.2*b.2,a.1*b.2+a.2*b.1)

private def norm (m : ℕ) (a : ℕ × ℕ) := (a.1%m,a.2%m)

private theorem assoc (d : ℕ) (a b c : ℕ × ℕ) :
    mul d (mul d a b) c=mul d a (mul d b c) := by
  ext <;> simp only [mul] <;> ring

private theorem comm (d : ℕ) (a b : ℕ × ℕ) : mul d a b=mul d b a := by
  ext <;> simp only [mul] <;> ring

private theorem one_mul (d : ℕ) (a : ℕ × ℕ) : mul d (1,0) a=a := by simp [mul]

private theorem norm_mul (d m : ℕ) (a b : ℕ × ℕ) :
    norm m (mul d (norm m a) (norm m b))=norm m (mul d a b) := by
  ext <;> simp only [mul,norm] <;> simp [Nat.add_mod,Nat.mul_mod]

def power (d : ℕ) (unit : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | n+1 => mul d (power d unit n) unit

private theorem power_add (d : ℕ) (unit : ℕ × ℕ) (i j : ℕ) :
    power d unit (i+j)=mul d (power d unit i) (power d unit j) := by
  induction j with
  | zero => simp only [Nat.add_zero,power,comm d _ (1,0),one_mul]
  | succ j ih => rw [Nat.add_succ,power,ih,assoc,power]

def orbit (d : ℕ) (unit seed : ℕ × ℕ) (n : ℕ) := mul d (power d unit n) seed

theorem orbit_zero (d : ℕ) (unit seed : ℕ × ℕ) : orbit d unit seed 0=seed := one_mul d seed

theorem orbit_succ (d : ℕ) (unit seed : ℕ × ℕ) (n : ℕ) :
    orbit d unit seed (n+1)=mul d unit (orbit d unit seed n) := by
  simp only [orbit,power,comm d (power d unit n) unit,assoc]

private def fastAux (d m : ℕ) (unit : ℕ × ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0,_ => norm m (1,0)
  | k+1,n =>
      let a := fastAux d m unit k (n/2)
      let b := norm m (mul d a a)
      if n%2=0 then b else norm m (mul d b (norm m unit))

private def fast (d m : ℕ) (unit : ℕ × ℕ) (n : ℕ) :=
  fastAux d m unit (n.log2+1) n

private theorem fast_eq (d m : ℕ) (unit : ℕ × ℕ) (n : ℕ) :
    fast d m unit n=norm m (power d unit n) := by
  have sound (k e : ℕ) (he : e<2^k) : fastAux d m unit k e=norm m (power d unit e) := by
    induction k generalizing e with
    | zero =>
      have h : e=0 := by simpa using he
      subst e
      rfl
    | succ k ih =>
      rw [pow_succ] at he
      have h : e/2<2^k := by omega
      rw [fastAux,ih (e/2) h,norm_mul,←power_add]
      split_ifs with ev
      · congr 2
        omega
      · rw [norm_mul,←power]
        congr 2
        omega
  exact sound _ _ Nat.lt_log2_self

private def atMod (d m : ℕ) (unit seed : ℕ × ℕ) (n : ℕ) :=
  (norm m (mul d (fast d m unit n) (norm m seed))).2

private theorem atMod_eq (d m : ℕ) (unit seed : ℕ × ℕ) (n : ℕ) :
    atMod d m unit seed n=(orbit d unit seed n).2%m := by
  rw [atMod,fast_eq,norm_mul]
  rfl

private theorem reduced {d m t : ℕ} {unit seed : ℕ × ℕ}
    (per : fast d m unit t=norm m (1,0)) (n : ℕ) :
    atMod d m unit seed (n%t)=(orbit d unit seed n).2%m := by
  rw [fast_eq] at per
  have step (i : ℕ) : norm m (power d unit (i+t))=norm m (power d unit i) := by
    rw [power_add,←norm_mul,per,norm_mul,comm d _ (1,0),one_mul]
  have steps (i j : ℕ) : norm m (power d unit (i+t*j))=norm m (power d unit i) := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ,←Nat.add_assoc,step,ih]
  have en := steps (n%t) (n/t)
  rw [Nat.mod_add_div] at en
  rw [atMod,fast_eq,←en,norm_mul]
  rfl

private def Good (d m t : ℕ) (unit seed : ℕ × ℕ) (roots : List ℕ) :=
  ∀ n : ℕ, m∣(orbit d unit seed n).2 → n%t∈roots

private theorem good_one (d : ℕ) (unit seed : ℕ × ℕ) : Good d 1 1 unit seed [0] := by
  intro n _
  simp [Nat.mod_one]

private theorem lift {d m m' t s : ℕ} {unit seed : ℕ × ℕ} {rr next : List ℕ}
    (old : Good d m t unit seed rr) (dvd : m∣m') (ht : 0<t) (hs : 0<s)
    (per : fast d m' unit (t*s)=norm m' (1,0))
    (cells : ∀ r∈rr, ∀ i : Fin s, atMod d m' unit seed (r+t*i.val)=0 → r+t*i.val∈next) :
    Good d m' (t*s) unit seed next := by
  intro n hit
  let a := n%(t*s)
  have small : a<t*s := Nat.mod_lt _ (Nat.mul_pos ht hs)
  have ai : a/t<s := (Nat.div_lt_iff_lt_mul ht).mpr (by simpa only [Nat.mul_comm t s] using small)
  have split := Nat.mod_add_div a t
  have rmem : a%t∈rr := by
    dsimp [a]
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right t s)]
    exact old n (dvd.trans hit)
  have h := cells (a%t) rmem ⟨a/t,ai⟩
  rw [split] at h
  exact h ((reduced per n).trans (Nat.mod_eq_zero_of_dvd hit))


private theorem smooth_dvd {y R B : ℕ}
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣R)
    (avoid : ∀ p : ℕ, p.Prime → p∣R → ¬p^(B+1)∣y) : y∣R^B := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p k pp d
  by_cases zero : k=0
  · simp [zero]
  have h := sup p pp ((dvd_pow_self p zero).trans d)
  apply pow_dvd_pow_of_dvd_of_le h
  by_contra! high
  exact avoid p pp h ((pow_dvd_pow p high).trans d)


private theorem descent2 {x y : ℕ} (eqn : x^2+1=2*y^2) :
    ∃ s ∈ ([(1,1)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 2 (3,2) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<3
    · have hx : x<3 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤2 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 3, ∀ j : Fin 3, i.val^2+1=2*j.val^2 →
          (i.val,j.val)∈([(1,1)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 3^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 4*y≤3*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 2*x≤3*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 2*y<2*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 3*x-4*y
    let v := 3*y-2*x
    have hu : u+4*y=3*x := Nat.sub_add_cancel ax
    have hv : v+2*x=3*y := Nat.sub_add_cancel ay
    have ev : u^2+1=2*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid2_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 2 (3,2) (1,1) k).2 := by
  have h0 : Good 2 2 1 (3,2) (1,1) [] :=
    lift (t:=1) (s:=1) (good_one 2 (3,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid2_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 2 (3,2) (1,1) k).2 := by
  have h0 : Good 2 37 38 (3,2) (1,1) [9, 28] :=
    lift (t:=1) (s:=38) (good_one 2 (3,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 1369 1406 (3,2) (1,1) [351, 1054] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 50653 52022 (3,2) (1,1) [13005, 39016] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 1874161 1924814 (3,2) (1,1) [481203, 1443610] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 69343957 71218118 (3,2) (1,1) [17804529, 53413588] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth2 {x y : ℕ} (eqn : x^2+1=2*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣74) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent2 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣74^5 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=37 := by
      have h : p∣2*(37) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h))
    have horb : p^(5+1)∣(orbit 2 (3,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    subst s
    rcases tags with rfl|rfl
    · exact avoid2_1_2 low ((pow_dvd_pow 2 (by decide : 1≤5+1)).trans horb)
    · exact avoid2_1_37 low ((pow_dvd_pow 37 (by decide : 5≤5+1)).trans horb)
  have limK : k<32 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<74^5) dv
    have : 74^5<2^32 := by decide
    omega
  have small : ∀ s ∈ ([(1,1)] : List (ℕ×ℕ)), ∀ i : Fin 32,
      (orbit 2 (3,2) s i.val).2∣74^5 → (orbit 2 (3,2) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent5 {x y : ℕ} (eqn : x^2+4=5*y^2) :
    ∃ s ∈ ([(1,1),(4,2),(11,5)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 5 (9,4) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<9
    · have hx : x<18 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤8 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 18, ∀ j : Fin 9, i.val^2+4=5*j.val^2 →
          (i.val,j.val)∈([(1,1),(4,2),(11,5)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 9^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 20*y≤9*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 4*x≤9*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 8*y<4*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 9*x-20*y
    let v := 9*y-4*x
    have hu : u+20*y=9*x := Nat.sub_add_cancel ax
    have hv : v+4*x=9*y := Nat.sub_add_cancel ay
    have ev : u^2+4=5*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid5_1_5 {k : ℕ} (hk : k<2097152) : ¬5^11∣(orbit 5 (9,4) (1,1) k).2 := by
  have h0 : Good 5 5 10 (9,4) (1,1) [4, 9] :=
    lift (t:=1) (s:=10) (good_one 5 (9,4) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 25 50 (9,4) (1,1) [4, 29] :=
    lift (t:=10) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 5 125 250 (9,4) (1,1) [104, 229] :=
    lift (t:=50) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 5 625 1250 (9,4) (1,1) [104, 729] :=
    lift (t:=250) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 5 3125 6250 (9,4) (1,1) [2604, 5729] :=
    lift (t:=1250) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 5 15625 31250 (9,4) (1,1) [2604, 18229] :=
    lift (t:=6250) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 5 78125 156250 (9,4) (1,1) [65104, 143229] :=
    lift (t:=31250) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 5 390625 781250 (9,4) (1,1) [65104, 455729] :=
    lift (t:=156250) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 5 1953125 3906250 (9,4) (1,1) [1627604, 3580729] :=
    lift (t:=781250) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 5 9765625 19531250 (9,4) (1,1) [1627604, 11393229] :=
    lift (t:=3906250) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 5 48828125 97656250 (9,4) (1,1) [40690104, 89518229] :=
    lift (t:=19531250) (s:=5) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h10 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid5_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 5 (9,4) (1,1) k).2 := by
  have h0 : Good 5 37 38 (9,4) (1,1) [3, 22] :=
    lift (t:=1) (s:=38) (good_one 5 (9,4) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 1369 1406 (9,4) (1,1) [117, 820] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 5 50653 52022 (9,4) (1,1) [4335, 30346] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 5 1874161 1924814 (9,4) (1,1) [160401, 1122808] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 5 69343957 71218118 (9,4) (1,1) [5934843, 41543902] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid5_4_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 5 (9,4) (4,2) k).2 := by
  have h0 : Good 5 5 10 (9,4) (4,2) [2, 7] :=
    lift (t:=1) (s:=10) (good_one 5 (9,4) (4,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 25 50 (9,4) (4,2) [12, 37] :=
    lift (t:=10) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 5 125 250 (9,4) (4,2) [62, 187] :=
    lift (t:=50) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 5 625 1250 (9,4) (4,2) [312, 937] :=
    lift (t:=250) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 5 3125 6250 (9,4) (4,2) [1562, 4687] :=
    lift (t:=1250) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 5 15625 31250 (9,4) (4,2) [7812, 23437] :=
    lift (t:=6250) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 5 78125 156250 (9,4) (4,2) [39062, 117187] :=
    lift (t:=31250) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 5 390625 781250 (9,4) (4,2) [195312, 585937] :=
    lift (t:=156250) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 5 1953125 3906250 (9,4) (4,2) [976562, 2929687] :=
    lift (t:=781250) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 5 9765625 19531250 (9,4) (4,2) [4882812, 14648437] :=
    lift (t:=3906250) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid5_4_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 5 (9,4) (4,2) k).2 := by
  have h0 : Good 5 37 38 (9,4) (4,2) [9, 28] :=
    lift (t:=1) (s:=38) (good_one 5 (9,4) (4,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 1369 1406 (9,4) (4,2) [351, 1054] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 5 50653 52022 (9,4) (4,2) [13005, 39016] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 5 1874161 1924814 (9,4) (4,2) [481203, 1443610] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 5 69343957 71218118 (9,4) (4,2) [17804529, 53413588] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid5_11_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 5 (9,4) (11,5) k).2 := by
  have h0 : Good 5 5 10 (9,4) (11,5) [0, 5] :=
    lift (t:=1) (s:=10) (good_one 5 (9,4) (11,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 25 50 (9,4) (11,5) [20, 45] :=
    lift (t:=10) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 5 125 250 (9,4) (11,5) [20, 145] :=
    lift (t:=50) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 5 625 1250 (9,4) (11,5) [520, 1145] :=
    lift (t:=250) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 5 3125 6250 (9,4) (11,5) [520, 3645] :=
    lift (t:=1250) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 5 15625 31250 (9,4) (11,5) [13020, 28645] :=
    lift (t:=6250) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 5 78125 156250 (9,4) (11,5) [13020, 91145] :=
    lift (t:=31250) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 5 390625 781250 (9,4) (11,5) [325520, 716145] :=
    lift (t:=156250) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 5 1953125 3906250 (9,4) (11,5) [325520, 2278645] :=
    lift (t:=781250) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 5 9765625 19531250 (9,4) (11,5) [8138020, 17903645] :=
    lift (t:=3906250) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid5_11_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 5 (9,4) (11,5) k).2 := by
  have h0 : Good 5 37 38 (9,4) (11,5) [15, 34] :=
    lift (t:=1) (s:=38) (good_one 5 (9,4) (11,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 1369 1406 (9,4) (11,5) [585, 1288] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 5 50653 52022 (9,4) (11,5) [21675, 47686] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 5 1874161 1924814 (9,4) (11,5) [802005, 1764412] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 5 69343957 71218118 (9,4) (11,5) [29674215, 65283274] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth5 {x y : ℕ} (eqn : x^2+4=5*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣185) : x≤11 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent5 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣185^11 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=5 ∨ p=37 := by
      have h : p∣5*(37) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 5)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h))
    have horb : p^(11+1)∣(orbit 5 (9,4) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid5_1_5 low ((pow_dvd_pow 5 (by decide : 11≤11+1)).trans horb)
      · exact avoid5_1_37 low ((pow_dvd_pow 37 (by decide : 5≤11+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid5_4_5 low ((pow_dvd_pow 5 (by decide : 10≤11+1)).trans horb)
      · exact avoid5_4_37 low ((pow_dvd_pow 37 (by decide : 5≤11+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid5_11_5 low ((pow_dvd_pow 5 (by decide : 10≤11+1)).trans horb)
      · exact avoid5_11_37 low ((pow_dvd_pow 37 (by decide : 5≤11+1)).trans horb)
  have limK : k<83 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<185^11) dv
    have : 185^11<2^83 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(4,2),(11,5)] : List (ℕ×ℕ)), ∀ i : Fin 83,
      (orbit 5 (9,4) s i.val).2∣185^11 → (orbit 5 (9,4) s i.val).1≤11 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent8 {x y : ℕ} (eqn : x^2+7=2*y^2) :
    ∃ s ∈ ([(1,2),(5,4)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 2 (3,2) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<6
    · have hx : x<8 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤5 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 8, ∀ j : Fin 6, i.val^2+7=2*j.val^2 →
          (i.val,j.val)∈([(1,2),(5,4)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 6^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 4*y≤3*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 2*x≤3*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 2*y<2*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 3*x-4*y
    let v := 3*y-2*x
    have hu : u+4*y=3*x := Nat.sub_add_cancel ax
    have hv : v+2*x=3*y := Nat.sub_add_cancel ay
    have ev : u^2+7=2*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid8_1_2 {k : ℕ} (hk : k<2097152) : ¬2^24∣(orbit 2 (3,2) (1,2) k).2 := by
  have h0 : Good 2 2 1 (3,2) (1,2) [0] :=
    lift (t:=1) (s:=1) (good_one 2 (3,2) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 4 2 (3,2) (1,2) [1] :=
    lift (t:=1) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 8 4 (3,2) (1,2) [1] :=
    lift (t:=2) (s:=2) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 16 8 (3,2) (1,2) [5] :=
    lift (t:=4) (s:=2) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 32 16 (3,2) (1,2) [13] :=
    lift (t:=8) (s:=2) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 64 32 (3,2) (1,2) [29] :=
    lift (t:=16) (s:=2) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 2 128 64 (3,2) (1,2) [61] :=
    lift (t:=32) (s:=2) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 2 256 128 (3,2) (1,2) [61] :=
    lift (t:=64) (s:=2) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 2 512 256 (3,2) (1,2) [189] :=
    lift (t:=128) (s:=2) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 2 1024 512 (3,2) (1,2) [445] :=
    lift (t:=256) (s:=2) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 2 2048 1024 (3,2) (1,2) [957] :=
    lift (t:=512) (s:=2) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 2 4096 2048 (3,2) (1,2) [957] :=
    lift (t:=1024) (s:=2) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 2 8192 4096 (3,2) (1,2) [3005] :=
    lift (t:=2048) (s:=2) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 2 16384 8192 (3,2) (1,2) [3005] :=
    lift (t:=4096) (s:=2) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 2 32768 16384 (3,2) (1,2) [3005] :=
    lift (t:=8192) (s:=2) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h15 : Good 2 65536 32768 (3,2) (1,2) [3005] :=
    lift (t:=16384) (s:=2) (h14) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h16 : Good 2 131072 65536 (3,2) (1,2) [35773] :=
    lift (t:=32768) (s:=2) (h15) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h17 : Good 2 262144 131072 (3,2) (1,2) [101309] :=
    lift (t:=65536) (s:=2) (h16) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h18 : Good 2 524288 262144 (3,2) (1,2) [232381] :=
    lift (t:=131072) (s:=2) (h17) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h19 : Good 2 1048576 524288 (3,2) (1,2) [232381] :=
    lift (t:=262144) (s:=2) (h18) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h20 : Good 2 2097152 1048576 (3,2) (1,2) [232381] :=
    lift (t:=524288) (s:=2) (h19) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h21 : Good 2 4194304 2097152 (3,2) (1,2) [1280957] :=
    lift (t:=1048576) (s:=2) (h20) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h22 : Good 2 8388608 4194304 (3,2) (1,2) [1280957] :=
    lift (t:=2097152) (s:=2) (h21) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h23 : Good 2 16777216 8388608 (3,2) (1,2) [5475261] :=
    lift (t:=4194304) (s:=2) (h22) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h23 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid8_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 2 (3,2) (1,2) k).2 := by
  have h0 : Good 2 37 38 (3,2) (1,2) [12, 31] :=
    lift (t:=1) (s:=38) (good_one 2 (3,2) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 1369 1406 (3,2) (1,2) [506, 1209] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 50653 52022 (3,2) (1,2) [6833, 32844] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 1874161 1924814 (3,2) (1,2) [423009, 1385416] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 69343957 71218118 (3,2) (1,2) [3310230, 38919289] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid8_5_2 {k : ℕ} (hk : k<2097152) : ¬2^23∣(orbit 2 (3,2) (5,4) k).2 := by
  have h0 : Good 2 2 1 (3,2) (5,4) [0] :=
    lift (t:=1) (s:=1) (good_one 2 (3,2) (5,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 4 2 (3,2) (5,4) [0] :=
    lift (t:=1) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 8 4 (3,2) (5,4) [2] :=
    lift (t:=2) (s:=2) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 16 8 (3,2) (5,4) [2] :=
    lift (t:=4) (s:=2) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 32 16 (3,2) (5,4) [2] :=
    lift (t:=8) (s:=2) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 64 32 (3,2) (5,4) [2] :=
    lift (t:=16) (s:=2) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 2 128 64 (3,2) (5,4) [2] :=
    lift (t:=32) (s:=2) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 2 256 128 (3,2) (5,4) [66] :=
    lift (t:=64) (s:=2) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 2 512 256 (3,2) (5,4) [66] :=
    lift (t:=128) (s:=2) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 2 1024 512 (3,2) (5,4) [66] :=
    lift (t:=256) (s:=2) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 2 2048 1024 (3,2) (5,4) [66] :=
    lift (t:=512) (s:=2) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 2 4096 2048 (3,2) (5,4) [1090] :=
    lift (t:=1024) (s:=2) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 2 8192 4096 (3,2) (5,4) [1090] :=
    lift (t:=2048) (s:=2) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 2 16384 8192 (3,2) (5,4) [5186] :=
    lift (t:=4096) (s:=2) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 2 32768 16384 (3,2) (5,4) [13378] :=
    lift (t:=8192) (s:=2) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h15 : Good 2 65536 32768 (3,2) (5,4) [29762] :=
    lift (t:=16384) (s:=2) (h14) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h16 : Good 2 131072 65536 (3,2) (5,4) [29762] :=
    lift (t:=32768) (s:=2) (h15) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h17 : Good 2 262144 131072 (3,2) (5,4) [29762] :=
    lift (t:=65536) (s:=2) (h16) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h18 : Good 2 524288 262144 (3,2) (5,4) [29762] :=
    lift (t:=131072) (s:=2) (h17) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h19 : Good 2 1048576 524288 (3,2) (5,4) [291906] :=
    lift (t:=262144) (s:=2) (h18) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h20 : Good 2 2097152 1048576 (3,2) (5,4) [816194] :=
    lift (t:=524288) (s:=2) (h19) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h21 : Good 2 4194304 2097152 (3,2) (5,4) [816194] :=
    lift (t:=1048576) (s:=2) (h20) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h22 : Good 2 8388608 4194304 (3,2) (5,4) [2913346] :=
    lift (t:=2097152) (s:=2) (h21) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h22 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid8_5_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 2 (3,2) (5,4) k).2 := by
  have h0 : Good 2 37 38 (3,2) (5,4) [6, 25] :=
    lift (t:=1) (s:=38) (good_one 2 (3,2) (5,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 1369 1406 (3,2) (5,4) [196, 899] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 50653 52022 (3,2) (5,4) [19177, 45188] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 1874161 1924814 (3,2) (5,4) [539397, 1501804] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 69343957 71218118 (3,2) (5,4) [32298828, 67907887] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth8 {x y : ℕ} (eqn : x^2+7=2*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣74) : x≤181 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent8 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣74^24 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=37 := by
      have h : p∣2*(37) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h))
    have horb : p^(24+1)∣(orbit 2 (3,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid8_1_2 low ((pow_dvd_pow 2 (by decide : 24≤24+1)).trans horb)
      · exact avoid8_1_37 low ((pow_dvd_pow 37 (by decide : 5≤24+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid8_5_2 low ((pow_dvd_pow 2 (by decide : 23≤24+1)).trans horb)
      · exact avoid8_5_37 low ((pow_dvd_pow 37 (by decide : 5≤24+1)).trans horb)
  have limK : k<150 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<74^24) dv
    have : 74^24<2^150 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(5,4)] : List (ℕ×ℕ)), ∀ i : Fin 150,
      (orbit 2 (3,2) s i.val).2∣74^24 → (orbit 2 (3,2) s i.val).1≤181 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent10 {x y : ℕ} (eqn : x^2+9=10*y^2) :
    ∃ s ∈ ([(1,1),(9,3),(41,13)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 10 (19,6) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<19
    · have hx : x<57 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤18 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 57, ∀ j : Fin 19, i.val^2+9=10*j.val^2 →
          (i.val,j.val)∈([(1,1),(9,3),(41,13)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 19^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 60*y≤19*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 6*x≤19*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 18*y<6*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 19*x-60*y
    let v := 19*y-6*x
    have hu : u+60*y=19*x := Nat.sub_add_cancel ax
    have hv : v+6*x=19*y := Nat.sub_add_cancel ay
    have ev : u^2+9=10*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid10_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 10 (19,6) (1,1) k).2 := by
  have h0 : Good 10 2 1 (19,6) (1,1) [] :=
    lift (t:=1) (s:=1) (good_one 10 (19,6) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid10_1_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 10 (19,6) (1,1) k).2 := by
  have h0 : Good 10 5 10 (19,6) (1,1) [1, 6] :=
    lift (t:=1) (s:=10) (good_one 10 (19,6) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 10 25 50 (19,6) (1,1) [1, 26] :=
    lift (t:=10) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 10 125 250 (19,6) (1,1) [101, 226] :=
    lift (t:=50) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 10 625 1250 (19,6) (1,1) [226, 851] :=
    lift (t:=250) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 10 3125 6250 (19,6) (1,1) [2101, 5226] :=
    lift (t:=1250) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 10 15625 31250 (19,6) (1,1) [14601, 30226] :=
    lift (t:=6250) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 10 78125 156250 (19,6) (1,1) [45851, 123976] :=
    lift (t:=31250) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 10 390625 781250 (19,6) (1,1) [123976, 514601] :=
    lift (t:=156250) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 10 1953125 3906250 (19,6) (1,1) [514601, 2467726] :=
    lift (t:=781250) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 10 9765625 19531250 (19,6) (1,1) [2467726, 12233351] :=
    lift (t:=3906250) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid10_1_37 {k : ℕ} (_hk : k<2097152) : ¬37^1∣(orbit 10 (19,6) (1,1) k).2 := by
  have h0 : Good 10 37 6 (19,6) (1,1) [] :=
    lift (t:=1) (s:=6) (good_one 10 (19,6) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid10_9_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 10 (19,6) (9,3) k).2 := by
  have h0 : Good 10 2 1 (19,6) (9,3) [] :=
    lift (t:=1) (s:=1) (good_one 10 (19,6) (9,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid10_9_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 10 (19,6) (9,3) k).2 := by
  have h0 : Good 10 5 10 (19,6) (9,3) [2, 7] :=
    lift (t:=1) (s:=10) (good_one 10 (19,6) (9,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 10 25 50 (19,6) (9,3) [12, 37] :=
    lift (t:=10) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 10 125 250 (19,6) (9,3) [62, 187] :=
    lift (t:=50) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 10 625 1250 (19,6) (9,3) [312, 937] :=
    lift (t:=250) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 10 3125 6250 (19,6) (9,3) [1562, 4687] :=
    lift (t:=1250) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 10 15625 31250 (19,6) (9,3) [7812, 23437] :=
    lift (t:=6250) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 10 78125 156250 (19,6) (9,3) [39062, 117187] :=
    lift (t:=31250) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 10 390625 781250 (19,6) (9,3) [195312, 585937] :=
    lift (t:=156250) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 10 1953125 3906250 (19,6) (9,3) [976562, 2929687] :=
    lift (t:=781250) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 10 9765625 19531250 (19,6) (9,3) [4882812, 14648437] :=
    lift (t:=3906250) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid10_9_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 10 (19,6) (9,3) k).2 := by
  have h0 : Good 10 37 6 (19,6) (9,3) [1, 4] :=
    lift (t:=1) (s:=6) (good_one 10 (19,6) (9,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 10 1369 222 (19,6) (9,3) [55, 166] :=
    lift (t:=6) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 10 50653 8214 (19,6) (9,3) [2053, 6160] :=
    lift (t:=222) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 10 1874161 303918 (19,6) (9,3) [75979, 227938] :=
    lift (t:=8214) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 10 69343957 11244966 (19,6) (9,3) [2811241, 8433724] :=
    lift (t:=303918) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid10_41_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 10 (19,6) (41,13) k).2 := by
  have h0 : Good 10 2 1 (19,6) (41,13) [] :=
    lift (t:=1) (s:=1) (good_one 10 (19,6) (41,13)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid10_41_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 10 (19,6) (41,13) k).2 := by
  have h0 : Good 10 5 10 (19,6) (41,13) [3, 8] :=
    lift (t:=1) (s:=10) (good_one 10 (19,6) (41,13)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 10 25 50 (19,6) (41,13) [23, 48] :=
    lift (t:=10) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 10 125 250 (19,6) (41,13) [23, 148] :=
    lift (t:=50) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 10 625 1250 (19,6) (41,13) [398, 1023] :=
    lift (t:=250) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 10 3125 6250 (19,6) (41,13) [1023, 4148] :=
    lift (t:=1250) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 10 15625 31250 (19,6) (41,13) [1023, 16648] :=
    lift (t:=6250) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 10 78125 156250 (19,6) (41,13) [32273, 110398] :=
    lift (t:=31250) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 10 390625 781250 (19,6) (41,13) [266648, 657273] :=
    lift (t:=156250) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 10 1953125 3906250 (19,6) (41,13) [1438523, 3391648] :=
    lift (t:=781250) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 10 9765625 19531250 (19,6) (41,13) [7297898, 17063523] :=
    lift (t:=3906250) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid10_41_37 {k : ℕ} (_hk : k<2097152) : ¬37^1∣(orbit 10 (19,6) (41,13) k).2 := by
  have h0 : Good 10 37 6 (19,6) (41,13) [] :=
    lift (t:=1) (s:=6) (good_one 10 (19,6) (41,13)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
theorem smooth10 {x y : ℕ} (eqn : x^2+9=10*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣370) : x≤79 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent10 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣370^10 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=5 ∨ p=37 := by
      have h : p∣2*(5*(37)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 5)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h)))
    have horb : p^(10+1)∣(orbit 10 (19,6) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid10_1_2 low ((pow_dvd_pow 2 (by decide : 1≤10+1)).trans horb)
      · exact avoid10_1_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid10_1_37 low ((pow_dvd_pow 37 (by decide : 1≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid10_9_2 low ((pow_dvd_pow 2 (by decide : 1≤10+1)).trans horb)
      · exact avoid10_9_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid10_9_37 low ((pow_dvd_pow 37 (by decide : 5≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid10_41_2 low ((pow_dvd_pow 2 (by decide : 1≤10+1)).trans horb)
      · exact avoid10_41_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid10_41_37 low ((pow_dvd_pow 37 (by decide : 1≤10+1)).trans horb)
  have limK : k<86 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<370^10) dv
    have : 370^10<2^86 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(9,3),(41,13)] : List (ℕ×ℕ)), ∀ i : Fin 86,
      (orbit 10 (19,6) s i.val).2∣370^10 → (orbit 10 (19,6) s i.val).1≤79 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent11 {x y : ℕ} (eqn : x^2+10=11*y^2) :
    ∃ s ∈ ([(1,1),(23,7)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 11 (10,3) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<10
    · have hx : x<30 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤9 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 30, ∀ j : Fin 10, i.val^2+10=11*j.val^2 →
          (i.val,j.val)∈([(1,1),(23,7)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 10^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 33*y≤10*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 3*x≤10*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 9*y<3*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 10*x-33*y
    let v := 10*y-3*x
    have hu : u+33*y=10*x := Nat.sub_add_cancel ax
    have hv : v+3*x=10*y := Nat.sub_add_cancel ay
    have ev : u^2+10=11*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid11_1_11 {k : ℕ} (hk : k<2097152) : ¬11^7∣(orbit 11 (10,3) (1,1) k).2 := by
  have h0 : Good 11 11 22 (10,3) (1,1) [4, 15] :=
    lift (t:=1) (s:=22) (good_one 11 (10,3) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 11 121 242 (10,3) (1,1) [81, 202] :=
    lift (t:=22) (s:=11) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 11 1331 2662 (10,3) (1,1) [565, 1896] :=
    lift (t:=242) (s:=11) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 11 14641 29282 (10,3) (1,1) [7220, 21861] :=
    lift (t:=2662) (s:=11) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 11 161051 322102 (10,3) (1,1) [80425, 241476] :=
    lift (t:=29282) (s:=11) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 11 1771561 3543122 (10,3) (1,1) [1207782, 2979343] :=
    lift (t:=322102) (s:=11) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 11 19487171 38974342 (10,3) (1,1) [11837148, 31324319] :=
    lift (t:=3543122) (s:=11) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid11_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 11 (10,3) (1,1) k).2 := by
  have h0 : Good 11 37 36 (10,3) (1,1) [2, 20] :=
    lift (t:=1) (s:=36) (good_one 11 (10,3) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 11 1369 1332 (10,3) (1,1) [272, 938] :=
    lift (t:=36) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 11 50653 49284 (10,3) (1,1) [3602, 28244] :=
    lift (t:=1332) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 11 1874161 1823508 (10,3) (1,1) [151454, 1063208] :=
    lift (t:=49284) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 11 69343957 67469796 (10,3) (1,1) [32062844, 65797742] :=
    lift (t:=1823508) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid11_23_11 {k : ℕ} (hk : k<2097152) : ¬11^7∣(orbit 11 (10,3) (23,7) k).2 := by
  have h0 : Good 11 11 22 (10,3) (23,7) [6, 17] :=
    lift (t:=1) (s:=22) (good_one 11 (10,3) (23,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 11 121 242 (10,3) (23,7) [39, 160] :=
    lift (t:=22) (s:=11) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 11 1331 2662 (10,3) (23,7) [765, 2096] :=
    lift (t:=242) (s:=11) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 11 14641 29282 (10,3) (23,7) [7420, 22061] :=
    lift (t:=2662) (s:=11) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 11 161051 322102 (10,3) (23,7) [80625, 241676] :=
    lift (t:=29282) (s:=11) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 11 1771561 3543122 (10,3) (23,7) [563778, 2335339] :=
    lift (t:=322102) (s:=11) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 11 19487171 38974342 (10,3) (23,7) [7650022, 27137193] :=
    lift (t:=3543122) (s:=11) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid11_23_37 {k : ℕ} (hk : k<2097152) : ¬37^6∣(orbit 11 (10,3) (23,7) k).2 := by
  have h0 : Good 11 37 36 (10,3) (23,7) [15, 33] :=
    lift (t:=1) (s:=36) (good_one 11 (10,3) (23,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 11 1369 1332 (10,3) (23,7) [393, 1059] :=
    lift (t:=36) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 11 50653 49284 (10,3) (23,7) [21039, 45681] :=
    lift (t:=1332) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 11 1874161 1823508 (10,3) (23,7) [760299, 1672053] :=
    lift (t:=49284) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 11 69343957 67469796 (10,3) (23,7) [1672053, 35406951] :=
    lift (t:=1823508) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 11 2565726409 2496382452 (10,3) (23,7) [1081188789, 2329380015] :=
    lift (t:=67469796) (s:=37) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth11 {x y : ℕ} (eqn : x^2+10=11*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣407) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent11 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣407^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=11 ∨ p=37 := by
      have h : p∣11*(37) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 11)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h))
    have horb : p^(7+1)∣(orbit 11 (10,3) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid11_1_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid11_1_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid11_23_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid11_23_37 low ((pow_dvd_pow 37 (by decide : 6≤7+1)).trans horb)
  have limK : k<61 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<407^7) dv
    have : 407^7<2^61 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(23,7)] : List (ℕ×ℕ)), ∀ i : Fin 61,
      (orbit 11 (10,3) s i.val).2∣407^7 → (orbit 11 (10,3) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent12 {x y : ℕ} (eqn : x^2+11=3*y^2) :
    ∃ s ∈ ([(1,2),(4,3)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 3 (2,1) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<4
    · have hx : x<6 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤3 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 6, ∀ j : Fin 4, i.val^2+11=3*j.val^2 →
          (i.val,j.val)∈([(1,2),(4,3)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 4^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 3*y≤2*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 1*x≤2*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 1*y<1*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 2*x-3*y
    let v := 2*y-1*x
    have hu : u+3*y=2*x := Nat.sub_add_cancel ax
    have hv : v+1*x=2*y := Nat.sub_add_cancel ay
    have ev : u^2+11=3*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid12_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^2∣(orbit 3 (2,1) (1,2) k).2 := by
  have h0 : Good 3 2 2 (2,1) (1,2) [0] :=
    lift (t:=1) (s:=2) (good_one 3 (2,1) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 4 4 (2,1) (1,2) [] :=
    lift (t:=2) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid12_1_3 {k : ℕ} (hk : k<2097152) : ¬3^16∣(orbit 3 (2,1) (1,2) k).2 := by
  have h0 : Good 3 3 6 (2,1) (1,2) [2, 5] :=
    lift (t:=1) (s:=6) (good_one 3 (2,1) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 9 18 (2,1) (1,2) [2, 11] :=
    lift (t:=6) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 27 54 (2,1) (1,2) [11, 38] :=
    lift (t:=18) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 81 162 (2,1) (1,2) [11, 92] :=
    lift (t:=54) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 243 486 (2,1) (1,2) [92, 335] :=
    lift (t:=162) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 3 729 1458 (2,1) (1,2) [335, 1064] :=
    lift (t:=486) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 3 2187 4374 (2,1) (1,2) [1064, 3251] :=
    lift (t:=1458) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 3 6561 13122 (2,1) (1,2) [1064, 7625] :=
    lift (t:=4374) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 3 19683 39366 (2,1) (1,2) [1064, 20747] :=
    lift (t:=13122) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 3 59049 118098 (2,1) (1,2) [40430, 99479] :=
    lift (t:=39366) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 3 177147 354294 (2,1) (1,2) [99479, 276626] :=
    lift (t:=118098) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 3 531441 1062882 (2,1) (1,2) [453773, 985214] :=
    lift (t:=354294) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 3 1594323 3188646 (2,1) (1,2) [985214, 2579537] :=
    lift (t:=1062882) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 3 4782969 9565938 (2,1) (1,2) [985214, 5768183] :=
    lift (t:=3188646) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 3 14348907 28697814 (2,1) (1,2) [985214, 15334121] :=
    lift (t:=9565938) (s:=3) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h15 : Good 3 43046721 86093442 (2,1) (1,2) [29683028, 72729749] :=
    lift (t:=28697814) (s:=3) (h14) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h15 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid12_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 3 (2,1) (1,2) k).2 := by
  have h0 : Good 3 37 36 (2,1) (1,2) [15, 33] :=
    lift (t:=1) (s:=36) (good_one 3 (2,1) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 1369 1332 (2,1) (1,2) [141, 807] :=
    lift (t:=36) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 50653 49284 (2,1) (1,2) [2139, 26781] :=
    lift (t:=1332) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 1874161 1823508 (2,1) (1,2) [494979, 1406733] :=
    lift (t:=49284) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 69343957 67469796 (2,1) (1,2) [4141995, 37876893] :=
    lift (t:=1823508) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid12_4_2 {k : ℕ} (_hk : k<2097152) : ¬2^2∣(orbit 3 (2,1) (4,3) k).2 := by
  have h0 : Good 3 2 2 (2,1) (4,3) [1] :=
    lift (t:=1) (s:=2) (good_one 3 (2,1) (4,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 4 4 (2,1) (4,3) [] :=
    lift (t:=2) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid12_4_3 {k : ℕ} (hk : k<2097152) : ¬3^14∣(orbit 3 (2,1) (4,3) k).2 := by
  have h0 : Good 3 3 6 (2,1) (4,3) [0, 3] :=
    lift (t:=1) (s:=6) (good_one 3 (2,1) (4,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 9 18 (2,1) (4,3) [6, 15] :=
    lift (t:=6) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 27 54 (2,1) (4,3) [15, 42] :=
    lift (t:=18) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 81 162 (2,1) (4,3) [69, 150] :=
    lift (t:=54) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 243 486 (2,1) (4,3) [150, 393] :=
    lift (t:=162) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 3 729 1458 (2,1) (4,3) [393, 1122] :=
    lift (t:=486) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 3 2187 4374 (2,1) (4,3) [1122, 3309] :=
    lift (t:=1458) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 3 6561 13122 (2,1) (4,3) [5496, 12057] :=
    lift (t:=4374) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 3 19683 39366 (2,1) (4,3) [18618, 38301] :=
    lift (t:=13122) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 3 59049 118098 (2,1) (4,3) [18618, 77667] :=
    lift (t:=39366) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 3 177147 354294 (2,1) (4,3) [77667, 254814] :=
    lift (t:=118098) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 3 531441 1062882 (2,1) (4,3) [77667, 609108] :=
    lift (t:=354294) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 3 1594323 3188646 (2,1) (4,3) [609108, 2203431] :=
    lift (t:=1062882) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 3 4782969 9565938 (2,1) (4,3) [3797754, 8580723] :=
    lift (t:=3188646) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h13 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid12_4_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 3 (2,1) (4,3) k).2 := by
  have h0 : Good 3 37 36 (2,1) (4,3) [2, 20] :=
    lift (t:=1) (s:=36) (good_one 3 (2,1) (4,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 1369 1332 (2,1) (4,3) [524, 1190] :=
    lift (t:=36) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 50653 49284 (2,1) (4,3) [22502, 47144] :=
    lift (t:=1332) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 1874161 1823508 (2,1) (4,3) [416774, 1328528] :=
    lift (t:=49284) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 69343957 67469796 (2,1) (4,3) [29592902, 63327800] :=
    lift (t:=1823508) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth12 {x y : ℕ} (eqn : x^2+11=3*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣222) : x≤64 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent12 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣222^16 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=3 ∨ p=37 := by
      have h : p∣2*(3*(37)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 3)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h)))
    have horb : p^(16+1)∣(orbit 3 (2,1) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid12_1_2 low ((pow_dvd_pow 2 (by decide : 2≤16+1)).trans horb)
      · exact avoid12_1_3 low ((pow_dvd_pow 3 (by decide : 16≤16+1)).trans horb)
      · exact avoid12_1_37 low ((pow_dvd_pow 37 (by decide : 5≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid12_4_2 low ((pow_dvd_pow 2 (by decide : 2≤16+1)).trans horb)
      · exact avoid12_4_3 low ((pow_dvd_pow 3 (by decide : 14≤16+1)).trans horb)
      · exact avoid12_4_37 low ((pow_dvd_pow 37 (by decide : 5≤16+1)).trans horb)
  have limK : k<125 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<222^16) dv
    have : 222^16<2^125 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(4,3)] : List (ℕ×ℕ)), ∀ i : Fin 125,
      (orbit 3 (2,1) s i.val).2∣222^16 → (orbit 3 (2,1) s i.val).1≤64 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent13 {x y : ℕ} (eqn : x^2+12=13*y^2) :
    ∃ s ∈ ([(1,1),(14,4),(25,7),(155,43),(274,76),(1691,469)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 13 (649,180) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<624
    · have calcX : 13*y^2-12=x^2 := by omega
      have tab : ∀ t : Fin 624, let a := 13*t.val^2-12
        (Nat.sqrt a)^2+12=13*t.val^2 →
          (Nat.sqrt a,t.val)∈([(1,1),(14,4),(25,7),(155,43),(274,76),(1691,469)] : List (ℕ×ℕ)) := by decide +kernel
      have mem := tab ⟨y,small⟩
      dsimp only at mem
      rw [calcX,Nat.sqrt_eq'] at mem
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),mem eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 624^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 2340*y≤649*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 180*x≤649*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 648*y<180*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 649*x-2340*y
    let v := 649*y-180*x
    have hu : u+2340*y=649*x := Nat.sub_add_cancel ax
    have hv : v+180*x=649*y := Nat.sub_add_cancel ay
    have ev : u^2+12=13*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid13_1_13 {k : ℕ} (hk : k<2097152) : ¬13^6∣(orbit 13 (649,180) (1,1) k).2 := by
  have h0 : Good 13 13 26 (649,180) (1,1) [6, 19] :=
    lift (t:=1) (s:=26) (good_one 13 (649,180) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 169 338 (649,180) (1,1) [32, 201] :=
    lift (t:=26) (s:=13) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 2197 4394 (649,180) (1,1) [1891, 4088] :=
    lift (t:=338) (s:=13) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 28561 57122 (649,180) (1,1) [6285, 34846] :=
    lift (t:=4394) (s:=13) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 371293 742586 (649,180) (1,1) [291895, 663188] :=
    lift (t:=57122) (s:=13) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 4826809 9653618 (649,180) (1,1) [4376118, 9202927] :=
    lift (t:=742586) (s:=13) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 13 (649,180) (1,1) k).2 := by
  have h0 : Good 13 37 38 (649,180) (1,1) [17, 36] :=
    lift (t:=1) (s:=38) (good_one 13 (649,180) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 1369 1406 (649,180) (1,1) [587, 1290] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 50653 52022 (649,180) (1,1) [25895, 51906] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 1874161 1924814 (649,180) (1,1) [416060, 1378467] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 69343957 71218118 (649,180) (1,1) [31213084, 66822143] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_14_13 {k : ℕ} (hk : k<2097152) : ¬13^7∣(orbit 13 (649,180) (14,4) k).2 := by
  have h0 : Good 13 13 26 (649,180) (14,4) [11, 24] :=
    lift (t:=1) (s:=26) (good_one 13 (649,180) (14,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 169 338 (649,180) (14,4) [24, 193] :=
    lift (t:=26) (s:=13) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 2197 4394 (649,180) (14,4) [1038, 3235] :=
    lift (t:=338) (s:=13) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 28561 57122 (649,180) (14,4) [3235, 31796] :=
    lift (t:=4394) (s:=13) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 371293 742586 (649,180) (14,4) [203162, 574455] :=
    lift (t:=57122) (s:=13) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 4826809 9653618 (649,180) (14,4) [2059627, 6886436] :=
    lift (t:=742586) (s:=13) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 13 62748517 125497034 (649,180) (14,4) [50327717, 113076234] :=
    lift (t:=9653618) (s:=13) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_14_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 13 (649,180) (14,4) k).2 := by
  have h0 : Good 13 37 38 (649,180) (14,4) [8, 27] :=
    lift (t:=1) (s:=38) (good_one 13 (649,180) (14,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 1369 1406 (649,180) (14,4) [350, 1053] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 50653 52022 (649,180) (14,4) [8786, 34797] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 1874161 1924814 (649,180) (14,4) [867149, 1829556] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 69343957 71218118 (649,180) (14,4) [16265661, 51874720] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_25_13 {k : ℕ} (hk : k<2097152) : ¬13^7∣(orbit 13 (649,180) (25,7) k).2 := by
  have h0 : Good 13 13 26 (649,180) (25,7) [10, 23] :=
    lift (t:=1) (s:=26) (good_one 13 (649,180) (25,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 169 338 (649,180) (25,7) [88, 257] :=
    lift (t:=26) (s:=13) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 2197 4394 (649,180) (25,7) [426, 2623] :=
    lift (t:=338) (s:=13) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 28561 57122 (649,180) (25,7) [15805, 44366] :=
    lift (t:=4394) (s:=13) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 371293 742586 (649,180) (25,7) [44366, 415659] :=
    lift (t:=57122) (s:=13) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 4826809 9653618 (649,180) (25,7) [1158245, 5985054] :=
    lift (t:=742586) (s:=13) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 13 62748517 125497034 (649,180) (25,7) [54253144, 117001661] :=
    lift (t:=9653618) (s:=13) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_25_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 13 (649,180) (25,7) k).2 := by
  have h0 : Good 13 37 38 (649,180) (25,7) [4, 23] :=
    lift (t:=1) (s:=38) (good_one 13 (649,180) (25,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 1369 1406 (649,180) (25,7) [118, 821] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 50653 52022 (649,180) (25,7) [8554, 34565] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 1874161 1924814 (649,180) (25,7) [736862, 1699269] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 69343957 71218118 (649,180) (25,7) [7473711, 43082770] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_155_13 {k : ℕ} (hk : k<2097152) : ¬13^6∣(orbit 13 (649,180) (155,43) k).2 := by
  have h0 : Good 13 13 26 (649,180) (155,43) [2, 15] :=
    lift (t:=1) (s:=26) (good_one 13 (649,180) (155,43)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 169 338 (649,180) (155,43) [80, 249] :=
    lift (t:=26) (s:=13) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 2197 4394 (649,180) (155,43) [1770, 3967] :=
    lift (t:=338) (s:=13) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 28561 57122 (649,180) (155,43) [12755, 41316] :=
    lift (t:=4394) (s:=13) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 371293 742586 (649,180) (155,43) [326926, 698219] :=
    lift (t:=57122) (s:=13) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 4826809 9653618 (649,180) (155,43) [3668563, 8495372] :=
    lift (t:=742586) (s:=13) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_155_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 13 (649,180) (155,43) k).2 := by
  have h0 : Good 13 37 38 (649,180) (155,43) [14, 33] :=
    lift (t:=1) (s:=38) (good_one 13 (649,180) (155,43)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 1369 1406 (649,180) (155,43) [584, 1287] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 50653 52022 (649,180) (155,43) [17456, 43467] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 1874161 1924814 (649,180) (155,43) [225544, 1187951] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 69343957 71218118 (649,180) (155,43) [28135347, 63744406] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_274_13 {k : ℕ} (hk : k<2097152) : ¬13^6∣(orbit 13 (649,180) (274,76) k).2 := by
  have h0 : Good 13 13 26 (649,180) (274,76) [1, 14] :=
    lift (t:=1) (s:=26) (good_one 13 (649,180) (274,76)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 169 338 (649,180) (274,76) [144, 313] :=
    lift (t:=26) (s:=13) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 2197 4394 (649,180) (274,76) [1158, 3355] :=
    lift (t:=338) (s:=13) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 28561 57122 (649,180) (274,76) [25325, 53886] :=
    lift (t:=4394) (s:=13) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 371293 742586 (649,180) (274,76) [168130, 539423] :=
    lift (t:=57122) (s:=13) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 4826809 9653618 (649,180) (274,76) [2767181, 7593990] :=
    lift (t:=742586) (s:=13) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_274_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 13 (649,180) (274,76) k).2 := by
  have h0 : Good 13 37 38 (649,180) (274,76) [10, 29] :=
    lift (t:=1) (s:=38) (good_one 13 (649,180) (274,76)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 1369 1406 (649,180) (274,76) [352, 1055] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 50653 52022 (649,180) (274,76) [17224, 43235] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 1874161 1924814 (649,180) (274,76) [95257, 1057664] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 69343957 71218118 (649,180) (274,76) [19343397, 54952456] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_1691_13 {k : ℕ} (hk : k<2097152) : ¬13^7∣(orbit 13 (649,180) (1691,469) k).2 := by
  have h0 : Good 13 13 26 (649,180) (1691,469) [6, 19] :=
    lift (t:=1) (s:=26) (good_one 13 (649,180) (1691,469)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 169 338 (649,180) (1691,469) [136, 305] :=
    lift (t:=26) (s:=13) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 2197 4394 (649,180) (1691,469) [305, 2502] :=
    lift (t:=338) (s:=13) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 28561 57122 (649,180) (1691,469) [22275, 50836] :=
    lift (t:=4394) (s:=13) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 371293 742586 (649,180) (1691,469) [79397, 450690] :=
    lift (t:=57122) (s:=13) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 4826809 9653618 (649,180) (1691,469) [450690, 5277499] :=
    lift (t:=742586) (s:=13) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 13 62748517 125497034 (649,180) (1691,469) [29411544, 92160061] :=
    lift (t:=9653618) (s:=13) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid13_1691_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 13 (649,180) (1691,469) k).2 := by
  have h0 : Good 13 37 38 (649,180) (1691,469) [1, 20] :=
    lift (t:=1) (s:=38) (good_one 13 (649,180) (1691,469)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 1369 1406 (649,180) (1691,469) [115, 818] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 50653 52022 (649,180) (1691,469) [115, 26126] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 1874161 1924814 (649,180) (1691,469) [546346, 1508753] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 69343957 71218118 (649,180) (1691,469) [4395974, 40005033] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth13 {x y : ℕ} (eqn : x^2+12=13*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣481) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent13 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣481^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=13 ∨ p=37 := by
      have h : p∣13*(37) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 13)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h))
    have horb : p^(7+1)∣(orbit 13 (649,180) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid13_1_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid13_1_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_14_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid13_14_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_25_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid13_25_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_155_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid13_155_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_274_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid13_274_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_1691_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid13_1691_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
  have limK : k<63 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<481^7) dv
    have : 481^7<2^63 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(14,4),(25,7),(155,43),(274,76),(1691,469)] : List (ℕ×ℕ)), ∀ i : Fin 63,
      (orbit 13 (649,180) s i.val).2∣481^7 → (orbit 13 (649,180) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent17 {x y : ℕ} (eqn : x^2+16=17*y^2) :
    ∃ s ∈ ([(1,1),(16,4),(103,25)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 17 (33,8) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<33
    · have hx : x<132 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤32 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 132, ∀ j : Fin 33, i.val^2+16=17*j.val^2 →
          (i.val,j.val)∈([(1,1),(16,4),(103,25)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 33^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 136*y≤33*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 8*x≤33*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 32*y<8*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 33*x-136*y
    let v := 33*y-8*x
    have hu : u+136*y=33*x := Nat.sub_add_cancel ax
    have hv : v+8*x=33*y := Nat.sub_add_cancel ay
    have ev : u^2+16=17*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid17_1_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 17 (33,8) (1,1) k).2 := by
  have h0 : Good 17 17 34 (33,8) (1,1) [15, 32] :=
    lift (t:=1) (s:=34) (good_one 17 (33,8) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 17 289 578 (33,8) (1,1) [168, 457] :=
    lift (t:=34) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 17 4913 9826 (33,8) (1,1) [746, 5659] :=
    lift (t:=578) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 17 83521 167042 (33,8) (1,1) [74441, 157962] :=
    lift (t:=9826) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 17 1419857 2839714 (33,8) (1,1) [241483, 1661340] :=
    lift (t:=167042) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 17 24137569 48275138 (33,8) (1,1) [8760625, 32898194] :=
    lift (t:=2839714) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid17_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 17 (33,8) (1,1) k).2 := by
  have h0 : Good 17 37 38 (33,8) (1,1) [11, 30] :=
    lift (t:=1) (s:=38) (good_one 17 (33,8) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 17 1369 1406 (33,8) (1,1) [619, 1322] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 17 50653 52022 (33,8) (1,1) [2728, 28739] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 17 1874161 1924814 (33,8) (1,1) [262838, 1225245] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 17 69343957 71218118 (33,8) (1,1) [31059862, 66668921] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid17_16_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 17 (33,8) (16,4) k).2 := by
  have h0 : Good 17 17 34 (33,8) (16,4) [8, 25] :=
    lift (t:=1) (s:=34) (good_one 17 (33,8) (16,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 17 289 578 (33,8) (16,4) [144, 433] :=
    lift (t:=34) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 17 4913 9826 (33,8) (16,4) [2456, 7369] :=
    lift (t:=578) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 17 83521 167042 (33,8) (16,4) [41760, 125281] :=
    lift (t:=9826) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 17 1419857 2839714 (33,8) (16,4) [709928, 2129785] :=
    lift (t:=167042) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 17 24137569 48275138 (33,8) (16,4) [12068784, 36206353] :=
    lift (t:=2839714) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid17_16_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 17 (33,8) (16,4) k).2 := by
  have h0 : Good 17 37 38 (33,8) (16,4) [9, 28] :=
    lift (t:=1) (s:=38) (good_one 17 (33,8) (16,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 17 1369 1406 (33,8) (16,4) [351, 1054] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 17 50653 52022 (33,8) (16,4) [13005, 39016] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 17 1874161 1924814 (33,8) (16,4) [481203, 1443610] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 17 69343957 71218118 (33,8) (16,4) [17804529, 53413588] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid17_103_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 17 (33,8) (103,25) k).2 := by
  have h0 : Good 17 17 34 (33,8) (103,25) [1, 18] :=
    lift (t:=1) (s:=34) (good_one 17 (33,8) (103,25)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 17 289 578 (33,8) (103,25) [120, 409] :=
    lift (t:=34) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 17 4913 9826 (33,8) (103,25) [4166, 9079] :=
    lift (t:=578) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 17 83521 167042 (33,8) (103,25) [9079, 92600] :=
    lift (t:=9826) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 17 1419857 2839714 (33,8) (103,25) [1178373, 2598230] :=
    lift (t:=167042) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 17 24137569 48275138 (33,8) (103,25) [15376943, 39514512] :=
    lift (t:=2839714) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid17_103_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 17 (33,8) (103,25) k).2 := by
  have h0 : Good 17 37 38 (33,8) (103,25) [7, 26] :=
    lift (t:=1) (s:=38) (good_one 17 (33,8) (103,25)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 17 1369 1406 (33,8) (103,25) [83, 786] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 17 50653 52022 (33,8) (103,25) [23282, 49293] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 17 1874161 1924814 (33,8) (103,25) [699568, 1661975] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 17 69343957 71218118 (33,8) (103,25) [4549196, 40158255] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth17 {x y : ℕ} (eqn : x^2+16=17*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣629) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent17 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣629^6 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=17 ∨ p=37 := by
      have h : p∣17*(37) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 17)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h))
    have horb : p^(6+1)∣(orbit 17 (33,8) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid17_1_17 low ((pow_dvd_pow 17 (by decide : 6≤6+1)).trans horb)
      · exact avoid17_1_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid17_16_17 low ((pow_dvd_pow 17 (by decide : 6≤6+1)).trans horb)
      · exact avoid17_16_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid17_103_17 low ((pow_dvd_pow 17 (by decide : 6≤6+1)).trans horb)
      · exact avoid17_103_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
  have limK : k<56 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<629^6) dv
    have : 629^6<2^56 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(16,4),(103,25)] : List (ℕ×ℕ)), ∀ i : Fin 56,
      (orbit 17 (33,8) s i.val).2∣629^6 → (orbit 17 (33,8) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent22 {x y : ℕ} (eqn : x^2+21=22*y^2) :
    ∃ s ∈ ([(1,1),(23,5),(89,19),(727,155)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 22 (197,42) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<193
    · have calcX : 22*y^2-21=x^2 := by omega
      have tab : ∀ t : Fin 193, let a := 22*t.val^2-21
        (Nat.sqrt a)^2+21=22*t.val^2 →
          (Nat.sqrt a,t.val)∈([(1,1),(23,5),(89,19),(727,155)] : List (ℕ×ℕ)) := by decide +kernel
      have mem := tab ⟨y,small⟩
      dsimp only at mem
      rw [calcX,Nat.sqrt_eq'] at mem
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),mem eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 193^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 924*y≤197*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 42*x≤197*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 196*y<42*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 197*x-924*y
    let v := 197*y-42*x
    have hu : u+924*y=197*x := Nat.sub_add_cancel ax
    have hv : v+42*x=197*y := Nat.sub_add_cancel ay
    have ev : u^2+21=22*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid22_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 22 (197,42) (1,1) k).2 := by
  have h0 : Good 22 2 1 (197,42) (1,1) [] :=
    lift (t:=1) (s:=1) (good_one 22 (197,42) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid22_1_11 {k : ℕ} (hk : k<2097152) : ¬11^7∣(orbit 22 (197,42) (1,1) k).2 := by
  have h0 : Good 22 11 22 (197,42) (1,1) [5, 16] :=
    lift (t:=1) (s:=22) (good_one 22 (197,42) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 121 242 (197,42) (1,1) [38, 159] :=
    lift (t:=22) (s:=11) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 1331 2662 (197,42) (1,1) [1006, 2337] :=
    lift (t:=242) (s:=11) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 14641 29282 (197,42) (1,1) [11654, 26295] :=
    lift (t:=2662) (s:=11) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 161051 322102 (197,42) (1,1) [99500, 260551] :=
    lift (t:=29282) (s:=11) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 22 1771561 3543122 (197,42) (1,1) [1065806, 2837367] :=
    lift (t:=322102) (s:=11) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 22 19487171 38974342 (197,42) (1,1) [8152050, 27639221] :=
    lift (t:=3543122) (s:=11) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid22_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 22 (197,42) (1,1) k).2 := by
  have h0 : Good 22 37 19 (197,42) (1,1) [2] :=
    lift (t:=1) (s:=19) (good_one 22 (197,42) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 1369 703 (197,42) (1,1) [458] :=
    lift (t:=19) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 50653 26011 (197,42) (1,1) [5379] :=
    lift (t:=703) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 1874161 962407 (197,42) (1,1) [603632] :=
    lift (t:=26011) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 69343957 35609059 (197,42) (1,1) [28513435] :=
    lift (t:=962407) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid22_23_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 22 (197,42) (23,5) k).2 := by
  have h0 : Good 22 2 1 (197,42) (23,5) [] :=
    lift (t:=1) (s:=1) (good_one 22 (197,42) (23,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid22_23_11 {k : ℕ} (hk : k<2097152) : ¬11^7∣(orbit 22 (197,42) (23,5) k).2 := by
  have h0 : Good 22 11 22 (197,42) (23,5) [3, 14] :=
    lift (t:=1) (s:=22) (good_one 22 (197,42) (23,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 121 242 (197,42) (23,5) [47, 168] :=
    lift (t:=22) (s:=11) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 1331 2662 (197,42) (23,5) [773, 2104] :=
    lift (t:=242) (s:=11) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 14641 29282 (197,42) (23,5) [11421, 26062] :=
    lift (t:=2662) (s:=11) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 161051 322102 (197,42) (23,5) [69985, 231036] :=
    lift (t:=29282) (s:=11) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 22 1771561 3543122 (197,42) (23,5) [875240, 2646801] :=
    lift (t:=322102) (s:=11) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 22 19487171 38974342 (197,42) (23,5) [16819289, 36306460] :=
    lift (t:=3543122) (s:=11) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid22_23_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 22 (197,42) (23,5) k).2 := by
  have h0 : Good 22 37 19 (197,42) (23,5) [14] :=
    lift (t:=1) (s:=19) (good_one 22 (197,42) (23,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 1369 703 (197,42) (23,5) [470] :=
    lift (t:=19) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 50653 26011 (197,42) (23,5) [6797] :=
    lift (t:=703) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 1874161 962407 (197,42) (23,5) [917182] :=
    lift (t:=26011) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 69343957 35609059 (197,42) (23,5) [34601427] :=
    lift (t:=962407) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid22_89_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 22 (197,42) (89,19) k).2 := by
  have h0 : Good 22 2 1 (197,42) (89,19) [] :=
    lift (t:=1) (s:=1) (good_one 22 (197,42) (89,19)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid22_89_11 {k : ℕ} (hk : k<2097152) : ¬11^7∣(orbit 22 (197,42) (89,19) k).2 := by
  have h0 : Good 22 11 22 (197,42) (89,19) [7, 18] :=
    lift (t:=1) (s:=22) (good_one 22 (197,42) (89,19)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 121 242 (197,42) (89,19) [73, 194] :=
    lift (t:=22) (s:=11) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 1331 2662 (197,42) (89,19) [557, 1888] :=
    lift (t:=242) (s:=11) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 14641 29282 (197,42) (89,19) [3219, 17860] :=
    lift (t:=2662) (s:=11) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 161051 322102 (197,42) (89,19) [91065, 252116] :=
    lift (t:=29282) (s:=11) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 22 1771561 3543122 (197,42) (89,19) [896320, 2667881] :=
    lift (t:=322102) (s:=11) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 22 19487171 38974342 (197,42) (89,19) [2667881, 22155052] :=
    lift (t:=3543122) (s:=11) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid22_89_37 {k : ℕ} (hk : k<2097152) : ¬37^6∣(orbit 22 (197,42) (89,19) k).2 := by
  have h0 : Good 22 37 19 (197,42) (89,19) [4] :=
    lift (t:=1) (s:=19) (good_one 22 (197,42) (89,19)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 1369 703 (197,42) (89,19) [232] :=
    lift (t:=19) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 50653 26011 (197,42) (89,19) [19213] :=
    lift (t:=703) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 1874161 962407 (197,42) (89,19) [45224] :=
    lift (t:=26011) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 69343957 35609059 (197,42) (89,19) [1007631] :=
    lift (t:=962407) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 22 2565726409 1317535183 (197,42) (89,19) [606361634] :=
    lift (t:=35609059) (s:=37) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid22_727_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 22 (197,42) (727,155) k).2 := by
  have h0 : Good 22 2 1 (197,42) (727,155) [] :=
    lift (t:=1) (s:=1) (good_one 22 (197,42) (727,155)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid22_727_11 {k : ℕ} (hk : k<2097152) : ¬11^7∣(orbit 22 (197,42) (727,155) k).2 := by
  have h0 : Good 22 11 22 (197,42) (727,155) [5, 16] :=
    lift (t:=1) (s:=22) (good_one 22 (197,42) (727,155)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 121 242 (197,42) (727,155) [82, 203] :=
    lift (t:=22) (s:=11) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 1331 2662 (197,42) (727,155) [324, 1655] :=
    lift (t:=242) (s:=11) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 14641 29282 (197,42) (727,155) [2986, 17627] :=
    lift (t:=2662) (s:=11) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 161051 322102 (197,42) (727,155) [61550, 222601] :=
    lift (t:=29282) (s:=11) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 22 1771561 3543122 (197,42) (727,155) [705754, 2477315] :=
    lift (t:=322102) (s:=11) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 22 19487171 38974342 (197,42) (727,155) [11335120, 30822291] :=
    lift (t:=3543122) (s:=11) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid22_727_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 22 (197,42) (727,155) k).2 := by
  have h0 : Good 22 37 19 (197,42) (727,155) [16] :=
    lift (t:=1) (s:=19) (good_one 22 (197,42) (727,155)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 1369 703 (197,42) (727,155) [244] :=
    lift (t:=19) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 50653 26011 (197,42) (727,155) [20631] :=
    lift (t:=703) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 1874161 962407 (197,42) (727,155) [358774] :=
    lift (t:=26011) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 69343957 35609059 (197,42) (727,155) [7095623] :=
    lift (t:=962407) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth22 {x y : ℕ} (eqn : x^2+21=22*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣814) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent22 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣814^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=11 ∨ p=37 := by
      have h : p∣2*(11*(37)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 11)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h)))
    have horb : p^(7+1)∣(orbit 22 (197,42) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_1_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_1_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_1_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_23_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_23_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_23_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_89_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_89_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_89_37 low ((pow_dvd_pow 37 (by decide : 6≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_727_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_727_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_727_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
  have limK : k<68 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<814^7) dv
    have : 814^7<2^68 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(23,5),(89,19),(727,155)] : List (ℕ×ℕ)), ∀ i : Fin 68,
      (orbit 22 (197,42) s i.val).2∣814^7 → (orbit 22 (197,42) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent26 {x y : ℕ} (eqn : x^2+25=26*y^2) :
    ∃ s ∈ ([(1,1),(25,5),(209,41)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 26 (51,10) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<51
    · have hx : x<255 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤50 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 255, ∀ j : Fin 51, i.val^2+25=26*j.val^2 →
          (i.val,j.val)∈([(1,1),(25,5),(209,41)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 51^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 260*y≤51*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 10*x≤51*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 50*y<10*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 51*x-260*y
    let v := 51*y-10*x
    have hu : u+260*y=51*x := Nat.sub_add_cancel ax
    have hv : v+10*x=51*y := Nat.sub_add_cancel ay
    have ev : u^2+25=26*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid26_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 26 (51,10) (1,1) k).2 := by
  have h0 : Good 26 2 1 (51,10) (1,1) [] :=
    lift (t:=1) (s:=1) (good_one 26 (51,10) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid26_1_13 {k : ℕ} (hk : k<2097152) : ¬13^7∣(orbit 26 (51,10) (1,1) k).2 := by
  have h0 : Good 26 13 26 (51,10) (1,1) [4, 17] :=
    lift (t:=1) (s:=26) (good_one 26 (51,10) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 26 169 338 (51,10) (1,1) [95, 264] :=
    lift (t:=26) (s:=13) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 26 2197 4394 (51,10) (1,1) [602, 2799] :=
    lift (t:=338) (s:=13) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 26 28561 57122 (51,10) (1,1) [7193, 35754] :=
    lift (t:=4394) (s:=13) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 26 371293 742586 (51,10) (1,1) [92876, 464169] :=
    lift (t:=57122) (s:=13) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 26 4826809 9653618 (51,10) (1,1) [1949341, 6776150] :=
    lift (t:=742586) (s:=13) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 26 62748517 125497034 (51,10) (1,1) [16429768, 79178285] :=
    lift (t:=9653618) (s:=13) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid26_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 26 (51,10) (1,1) k).2 := by
  have h0 : Good 26 37 18 (51,10) (1,1) [7, 16] :=
    lift (t:=1) (s:=18) (good_one 26 (51,10) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 26 1369 666 (51,10) (1,1) [88, 421] :=
    lift (t:=18) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 26 50653 24642 (51,10) (1,1) [11410, 23731] :=
    lift (t:=666) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 26 1874161 911754 (51,10) (1,1) [220867, 676744] :=
    lift (t:=24642) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 26 69343957 33734898 (51,10) (1,1) [15720685, 32588134] :=
    lift (t:=911754) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid26_25_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 26 (51,10) (25,5) k).2 := by
  have h0 : Good 26 2 1 (51,10) (25,5) [] :=
    lift (t:=1) (s:=1) (good_one 26 (51,10) (25,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid26_25_13 {k : ℕ} (hk : k<2097152) : ¬13^6∣(orbit 26 (51,10) (25,5) k).2 := by
  have h0 : Good 26 13 26 (51,10) (25,5) [6, 19] :=
    lift (t:=1) (s:=26) (good_one 26 (51,10) (25,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 26 169 338 (51,10) (25,5) [84, 253] :=
    lift (t:=26) (s:=13) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 26 2197 4394 (51,10) (25,5) [1098, 3295] :=
    lift (t:=338) (s:=13) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 26 28561 57122 (51,10) (25,5) [14280, 42841] :=
    lift (t:=4394) (s:=13) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 26 371293 742586 (51,10) (25,5) [185646, 556939] :=
    lift (t:=57122) (s:=13) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 26 4826809 9653618 (51,10) (25,5) [2413404, 7240213] :=
    lift (t:=742586) (s:=13) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid26_25_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 26 (51,10) (25,5) k).2 := by
  have h0 : Good 26 37 18 (51,10) (25,5) [4, 13] :=
    lift (t:=1) (s:=18) (good_one 26 (51,10) (25,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 26 1369 666 (51,10) (25,5) [166, 499] :=
    lift (t:=18) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 26 50653 24642 (51,10) (25,5) [6160, 18481] :=
    lift (t:=666) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 26 1874161 911754 (51,10) (25,5) [227938, 683815] :=
    lift (t:=24642) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 26 69343957 33734898 (51,10) (25,5) [8433724, 25301173] :=
    lift (t:=911754) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid26_209_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 26 (51,10) (209,41) k).2 := by
  have h0 : Good 26 2 1 (51,10) (209,41) [] :=
    lift (t:=1) (s:=1) (good_one 26 (51,10) (209,41)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid26_209_13 {k : ℕ} (hk : k<2097152) : ¬13^6∣(orbit 26 (51,10) (209,41) k).2 := by
  have h0 : Good 26 13 26 (51,10) (209,41) [8, 21] :=
    lift (t:=1) (s:=26) (good_one 26 (51,10) (209,41)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 26 169 338 (51,10) (209,41) [73, 242] :=
    lift (t:=26) (s:=13) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 26 2197 4394 (51,10) (209,41) [1594, 3791] :=
    lift (t:=338) (s:=13) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 26 28561 57122 (51,10) (209,41) [21367, 49928] :=
    lift (t:=4394) (s:=13) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 26 371293 742586 (51,10) (209,41) [278416, 649709] :=
    lift (t:=57122) (s:=13) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 26 4826809 9653618 (51,10) (209,41) [2877467, 7704276] :=
    lift (t:=742586) (s:=13) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid26_209_37 {k : ℕ} (hk : k<2097152) : ¬37^6∣(orbit 26 (51,10) (209,41) k).2 := by
  have h0 : Good 26 37 18 (51,10) (209,41) [1, 10] :=
    lift (t:=1) (s:=18) (good_one 26 (51,10) (209,41)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 26 1369 666 (51,10) (209,41) [244, 577] :=
    lift (t:=18) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 26 50653 24642 (51,10) (209,41) [910, 13231] :=
    lift (t:=666) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 26 1874161 911754 (51,10) (209,41) [235009, 690886] :=
    lift (t:=24642) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 26 69343957 33734898 (51,10) (209,41) [1146763, 18014212] :=
    lift (t:=911754) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 26 2565726409 1248191226 (51,10) (209,41) [591507478, 1215603091] :=
    lift (t:=33734898) (s:=37) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth26 {x y : ℕ} (eqn : x^2+25=26*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣962) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent26 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣962^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=13 ∨ p=37 := by
      have h : p∣2*(13*(37)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 13)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h)))
    have horb : p^(7+1)∣(orbit 26 (51,10) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid26_1_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid26_1_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid26_1_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid26_25_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid26_25_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid26_25_37 low ((pow_dvd_pow 37 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid26_209_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid26_209_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid26_209_37 low ((pow_dvd_pow 37 (by decide : 6≤7+1)).trans horb)
  have limK : k<70 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<962^7) dv
    have : 962^7<2^70 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(25,5),(209,41)] : List (ℕ×ℕ)), ∀ i : Fin 70,
      (orbit 26 (51,10) s i.val).2∣962^7 → (orbit 26 (51,10) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent27 {x y : ℕ} (eqn : x^2+26=3*y^2) :
    ∃ s ∈ ([(1,3),(7,5)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 3 (2,1) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<6
    · have hx : x<9 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤5 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 9, ∀ j : Fin 6, i.val^2+26=3*j.val^2 →
          (i.val,j.val)∈([(1,3),(7,5)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 6^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 3*y≤2*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 1*x≤2*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 1*y<1*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 2*x-3*y
    let v := 2*y-1*x
    have hu : u+3*y=2*x := Nat.sub_add_cancel ax
    have hv : v+1*x=2*y := Nat.sub_add_cancel ay
    have ev : u^2+26=3*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid27_1_3 {k : ℕ} (hk : k<2097152) : ¬3^15∣(orbit 3 (2,1) (1,3) k).2 := by
  have h0 : Good 3 3 6 (2,1) (1,3) [0, 3] :=
    lift (t:=1) (s:=6) (good_one 3 (2,1) (1,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 9 18 (2,1) (1,3) [6, 15] :=
    lift (t:=6) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 27 54 (2,1) (1,3) [6, 33] :=
    lift (t:=18) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 81 162 (2,1) (1,3) [33, 114] :=
    lift (t:=54) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 243 486 (2,1) (1,3) [195, 438] :=
    lift (t:=162) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 3 729 1458 (2,1) (1,3) [438, 1167] :=
    lift (t:=486) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 3 2187 4374 (2,1) (1,3) [1167, 3354] :=
    lift (t:=1458) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 3 6561 13122 (2,1) (1,3) [5541, 12102] :=
    lift (t:=4374) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 3 19683 39366 (2,1) (1,3) [18663, 38346] :=
    lift (t:=13122) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 3 59049 118098 (2,1) (1,3) [18663, 77712] :=
    lift (t:=39366) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 3 177147 354294 (2,1) (1,3) [136761, 313908] :=
    lift (t:=118098) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 3 531441 1062882 (2,1) (1,3) [491055, 1022496] :=
    lift (t:=354294) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 3 1594323 3188646 (2,1) (1,3) [491055, 2085378] :=
    lift (t:=1062882) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 3 4782969 9565938 (2,1) (1,3) [491055, 5274024] :=
    lift (t:=3188646) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 3 14348907 28697814 (2,1) (1,3) [10056993, 24405900] :=
    lift (t:=9565938) (s:=3) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h14 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid27_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 3 (2,1) (1,3) k).2 := by
  have h0 : Good 3 37 36 (2,1) (1,3) [5, 23] :=
    lift (t:=1) (s:=36) (good_one 3 (2,1) (1,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 1369 1332 (2,1) (1,3) [401, 1067] :=
    lift (t:=36) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 50653 49284 (2,1) (1,3) [1733, 26375] :=
    lift (t:=1332) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 1874161 1823508 (2,1) (1,3) [790277, 1702031] :=
    lift (t:=49284) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 69343957 67469796 (2,1) (1,3) [15378341, 49113239] :=
    lift (t:=1823508) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid27_7_3 {k : ℕ} (hk : k<2097152) : ¬3^14∣(orbit 3 (2,1) (7,5) k).2 := by
  have h0 : Good 3 3 6 (2,1) (7,5) [2, 5] :=
    lift (t:=1) (s:=6) (good_one 3 (2,1) (7,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 9 18 (2,1) (7,5) [2, 11] :=
    lift (t:=6) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 27 54 (2,1) (7,5) [20, 47] :=
    lift (t:=18) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 81 162 (2,1) (7,5) [47, 128] :=
    lift (t:=54) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 243 486 (2,1) (7,5) [47, 290] :=
    lift (t:=162) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 3 729 1458 (2,1) (7,5) [290, 1019] :=
    lift (t:=486) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 3 2187 4374 (2,1) (7,5) [1019, 3206] :=
    lift (t:=1458) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 3 6561 13122 (2,1) (7,5) [1019, 7580] :=
    lift (t:=4374) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 3 19683 39366 (2,1) (7,5) [1019, 20702] :=
    lift (t:=13122) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 3 59049 118098 (2,1) (7,5) [40385, 99434] :=
    lift (t:=39366) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 3 177147 354294 (2,1) (7,5) [40385, 217532] :=
    lift (t:=118098) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 3 531441 1062882 (2,1) (7,5) [40385, 571826] :=
    lift (t:=354294) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 3 1594323 3188646 (2,1) (7,5) [1103267, 2697590] :=
    lift (t:=1062882) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 3 4782969 9565938 (2,1) (7,5) [4291913, 9074882] :=
    lift (t:=3188646) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h13 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid27_7_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 3 (2,1) (7,5) k).2 := by
  have h0 : Good 3 37 36 (2,1) (7,5) [12, 30] :=
    lift (t:=1) (s:=36) (good_one 3 (2,1) (7,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 1369 1332 (2,1) (7,5) [264, 930] :=
    lift (t:=36) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 50653 49284 (2,1) (7,5) [22908, 47550] :=
    lift (t:=1332) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 1874161 1823508 (2,1) (7,5) [121476, 1033230] :=
    lift (t:=49284) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 69343957 67469796 (2,1) (7,5) [18356556, 52091454] :=
    lift (t:=1823508) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth27 {x y : ℕ} (eqn : x^2+26=3*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣111) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent27 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣111^15 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=3 ∨ p=37 := by
      have h : p∣3*(37) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 3)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h))
    have horb : p^(15+1)∣(orbit 3 (2,1) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid27_1_3 low ((pow_dvd_pow 3 (by decide : 15≤15+1)).trans horb)
      · exact avoid27_1_37 low ((pow_dvd_pow 37 (by decide : 5≤15+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid27_7_3 low ((pow_dvd_pow 3 (by decide : 14≤15+1)).trans horb)
      · exact avoid27_7_37 low ((pow_dvd_pow 37 (by decide : 5≤15+1)).trans horb)
  have limK : k<102 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<111^15) dv
    have : 111^15<2^102 := by decide
    omega
  have small : ∀ s ∈ ([(1,3),(7,5)] : List (ℕ×ℕ)), ∀ i : Fin 102,
      (orbit 3 (2,1) s i.val).2∣111^15 → (orbit 3 (2,1) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent28 {x y : ℕ} (eqn : x^2+27=7*y^2) :
    ∃ s ∈ ([(1,2),(6,3),(15,6),(34,13)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 7 (8,3) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<16
    · have hx : x<40 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤15 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 40, ∀ j : Fin 16, i.val^2+27=7*j.val^2 →
          (i.val,j.val)∈([(1,2),(6,3),(15,6),(34,13)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 16^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 21*y≤8*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 3*x≤8*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 7*y<3*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 8*x-21*y
    let v := 8*y-3*x
    have hu : u+21*y=8*x := Nat.sub_add_cancel ax
    have hv : v+3*x=8*y := Nat.sub_add_cancel ay
    have ev : u^2+27=7*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid28_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^2∣(orbit 7 (8,3) (1,2) k).2 := by
  have h0 : Good 7 2 2 (8,3) (1,2) [0] :=
    lift (t:=1) (s:=2) (good_one 7 (8,3) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 4 4 (8,3) (1,2) [] :=
    lift (t:=2) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid28_1_7 {k : ℕ} (hk : k<2097152) : ¬7^10∣(orbit 7 (8,3) (1,2) k).2 := by
  have h0 : Good 7 7 7 (8,3) (1,2) [4] :=
    lift (t:=1) (s:=7) (good_one 7 (8,3) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 49 49 (8,3) (1,2) [46] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 343 343 (8,3) (1,2) [46] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 2401 2401 (8,3) (1,2) [2104] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 16807 16807 (8,3) (1,2) [6906] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 117649 117649 (8,3) (1,2) [90941] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 7 823543 823543 (8,3) (1,2) [443888] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 7 5764801 5764801 (8,3) (1,2) [443888] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 7 40353607 40353607 (8,3) (1,2) [443888] :=
    lift (t:=5764801) (s:=7) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 7 282475249 282475249 (8,3) (1,2) [81151102] :=
    lift (t:=40353607) (s:=7) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid28_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 7 (8,3) (1,2) k).2 := by
  have h0 : Good 7 37 36 (8,3) (1,2) [13, 31] :=
    lift (t:=1) (s:=36) (good_one 7 (8,3) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 1369 1332 (8,3) (1,2) [265, 931] :=
    lift (t:=36) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 50653 49284 (8,3) (1,2) [11587, 36229] :=
    lift (t:=1332) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 1874161 1823508 (8,3) (1,2) [159439, 1071193] :=
    lift (t:=49284) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 69343957 67469796 (8,3) (1,2) [19306273, 53041171] :=
    lift (t:=1823508) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid28_6_2 {k : ℕ} (_hk : k<2097152) : ¬2^2∣(orbit 7 (8,3) (6,3) k).2 := by
  have h0 : Good 7 2 2 (8,3) (6,3) [1] :=
    lift (t:=1) (s:=2) (good_one 7 (8,3) (6,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 4 4 (8,3) (6,3) [] :=
    lift (t:=2) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid28_6_7 {k : ℕ} (hk : k<2097152) : ¬7^8∣(orbit 7 (8,3) (6,3) k).2 := by
  have h0 : Good 7 7 7 (8,3) (6,3) [1] :=
    lift (t:=1) (s:=7) (good_one 7 (8,3) (6,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 49 49 (8,3) (6,3) [15] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 343 343 (8,3) (6,3) [15] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 2401 2401 (8,3) (6,3) [701] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 16807 16807 (8,3) (6,3) [7904] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 117649 117649 (8,3) (6,3) [108746] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 7 823543 823543 (8,3) (6,3) [696991] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 7 5764801 5764801 (8,3) (6,3) [3991163] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h7 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid28_6_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 7 (8,3) (6,3) k).2 := by
  have h0 : Good 7 37 36 (8,3) (6,3) [10, 28] :=
    lift (t:=1) (s:=36) (good_one 7 (8,3) (6,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 1369 1332 (8,3) (6,3) [532, 1198] :=
    lift (t:=36) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 50653 49284 (8,3) (6,3) [3862, 28504] :=
    lift (t:=1332) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 1874161 1823508 (8,3) (6,3) [53146, 964900] :=
    lift (t:=49284) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 69343957 67469796 (8,3) (6,3) [6435424, 40170322] :=
    lift (t:=1823508) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid28_15_2 {k : ℕ} (_hk : k<2097152) : ¬2^2∣(orbit 7 (8,3) (15,6) k).2 := by
  have h0 : Good 7 2 2 (8,3) (15,6) [0] :=
    lift (t:=1) (s:=2) (good_one 7 (8,3) (15,6)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 4 4 (8,3) (15,6) [] :=
    lift (t:=2) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid28_15_7 {k : ℕ} (hk : k<2097152) : ¬7^9∣(orbit 7 (8,3) (15,6) k).2 := by
  have h0 : Good 7 7 7 (8,3) (15,6) [5] :=
    lift (t:=1) (s:=7) (good_one 7 (8,3) (15,6)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 49 49 (8,3) (15,6) [33] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 343 343 (8,3) (15,6) [327] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 2401 2401 (8,3) (15,6) [1699] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 16807 16807 (8,3) (15,6) [8902] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 117649 117649 (8,3) (15,6) [8902] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 7 823543 823543 (8,3) (15,6) [126551] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 7 5764801 5764801 (8,3) (15,6) [1773637] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 7 40353607 40353607 (8,3) (15,6) [13303239] :=
    lift (t:=5764801) (s:=7) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h8 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid28_15_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 7 (8,3) (15,6) k).2 := by
  have h0 : Good 7 37 36 (8,3) (15,6) [7, 25] :=
    lift (t:=1) (s:=36) (good_one 7 (8,3) (15,6)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 1369 1332 (8,3) (15,6) [133, 799] :=
    lift (t:=36) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 50653 49284 (8,3) (15,6) [20779, 45421] :=
    lift (t:=1332) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 1874161 1823508 (8,3) (15,6) [858607, 1770361] :=
    lift (t:=49284) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 69343957 67469796 (8,3) (15,6) [27299473, 61034371] :=
    lift (t:=1823508) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid28_34_2 {k : ℕ} (_hk : k<2097152) : ¬2^2∣(orbit 7 (8,3) (34,13) k).2 := by
  have h0 : Good 7 2 2 (8,3) (34,13) [1] :=
    lift (t:=1) (s:=2) (good_one 7 (8,3) (34,13)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 4 4 (8,3) (34,13) [] :=
    lift (t:=2) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid28_34_7 {k : ℕ} (hk : k<2097152) : ¬7^8∣(orbit 7 (8,3) (34,13) k).2 := by
  have h0 : Good 7 7 7 (8,3) (34,13) [2] :=
    lift (t:=1) (s:=7) (good_one 7 (8,3) (34,13)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 49 49 (8,3) (34,13) [2] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 343 343 (8,3) (34,13) [296] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 2401 2401 (8,3) (34,13) [296] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 16807 16807 (8,3) (34,13) [9900] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 117649 117649 (8,3) (34,13) [26707] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 7 823543 823543 (8,3) (34,13) [379654] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 7 5764801 5764801 (8,3) (34,13) [5320912] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h7 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid28_34_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 7 (8,3) (34,13) k).2 := by
  have h0 : Good 7 37 36 (8,3) (34,13) [4, 22] :=
    lift (t:=1) (s:=36) (good_one 7 (8,3) (34,13)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 1369 1332 (8,3) (34,13) [400, 1066] :=
    lift (t:=36) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 50653 49284 (8,3) (34,13) [13054, 37696] :=
    lift (t:=1332) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 1874161 1823508 (8,3) (34,13) [752314, 1664068] :=
    lift (t:=49284) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 69343957 67469796 (8,3) (34,13) [14428624, 48163522] :=
    lift (t:=1823508) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth28 {x y : ℕ} (eqn : x^2+27=7*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣518) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent28 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣518^10 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=7 ∨ p=37 := by
      have h : p∣2*(7*(37)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 7)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h)))
    have horb : p^(10+1)∣(orbit 7 (8,3) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid28_1_2 low ((pow_dvd_pow 2 (by decide : 2≤10+1)).trans horb)
      · exact avoid28_1_7 low ((pow_dvd_pow 7 (by decide : 10≤10+1)).trans horb)
      · exact avoid28_1_37 low ((pow_dvd_pow 37 (by decide : 5≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid28_6_2 low ((pow_dvd_pow 2 (by decide : 2≤10+1)).trans horb)
      · exact avoid28_6_7 low ((pow_dvd_pow 7 (by decide : 8≤10+1)).trans horb)
      · exact avoid28_6_37 low ((pow_dvd_pow 37 (by decide : 5≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid28_15_2 low ((pow_dvd_pow 2 (by decide : 2≤10+1)).trans horb)
      · exact avoid28_15_7 low ((pow_dvd_pow 7 (by decide : 9≤10+1)).trans horb)
      · exact avoid28_15_37 low ((pow_dvd_pow 37 (by decide : 5≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid28_34_2 low ((pow_dvd_pow 2 (by decide : 2≤10+1)).trans horb)
      · exact avoid28_34_7 low ((pow_dvd_pow 7 (by decide : 8≤10+1)).trans horb)
      · exact avoid28_34_37 low ((pow_dvd_pow 37 (by decide : 5≤10+1)).trans horb)
  have limK : k<91 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<518^10) dv
    have : 518^10<2^91 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(6,3),(15,6),(34,13)] : List (ℕ×ℕ)), ∀ i : Fin 91,
      (orbit 7 (8,3) s i.val).2∣518^10 → (orbit 7 (8,3) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent29 {x y : ℕ} (eqn : x^2+28=29*y^2) :
    ∃ s ∈ ([(1,1),(59,11),(86,16),(1594,296),(2321,431),(42979,7981)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 29 (9801,1820) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<9631
    · have calcX : 29*y^2-28=x^2 := by omega
      have tab : ∀ hi : Fin 76, ∀ lo : Fin 128, hi.val*128+lo.val<9631 → let a := 29*(hi.val*128+lo.val)^2-28
        (Nat.sqrt a)^2+28=29*(hi.val*128+lo.val)^2 →
          (Nat.sqrt a,(hi.val*128+lo.val))∈([(1,1),(59,11),(86,16),(1594,296),(2321,431),(42979,7981)] : List (ℕ×ℕ)) := by decide +kernel
      have mem := tab ⟨y/128,by omega⟩ ⟨y%128,by omega⟩
      dsimp only at mem
      rw [show y/128*128+y%128=y by omega] at mem
      specialize mem small
      rw [calcX,Nat.sqrt_eq'] at mem
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),mem eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 9631^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 52780*y≤9801*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 1820*x≤9801*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 9800*y<1820*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 9801*x-52780*y
    let v := 9801*y-1820*x
    have hu : u+52780*y=9801*x := Nat.sub_add_cancel ax
    have hv : v+1820*x=9801*y := Nat.sub_add_cancel ay
    have ev : u^2+28=29*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid29_1_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 29 (9801,1820) (1,1) k).2 := by
  have h0 : Good 29 29 58 (9801,1820) (1,1) [4, 33] :=
    lift (t:=1) (s:=58) (good_one 29 (9801,1820) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 841 1682 (9801,1820) (1,1) [468, 1309] :=
    lift (t:=58) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 24389 48778 (9801,1820) (1,1) [468, 24857] :=
    lift (t:=1682) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 707281 1414562 (9801,1820) (1,1) [98024, 805305] :=
    lift (t:=48778) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 20511149 41022298 (9801,1820) (1,1) [10707239, 31218388] :=
    lift (t:=1414562) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 29 (9801,1820) (1,1) k).2 := by
  have h0 : Good 29 37 38 (9801,1820) (1,1) [12, 31] :=
    lift (t:=1) (s:=38) (good_one 29 (9801,1820) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 1369 1406 (9801,1820) (1,1) [107, 810] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 50653 52022 (9801,1820) (1,1) [19791, 45802] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 1874161 1924814 (9801,1820) (1,1) [904165, 1866572] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 69343957 71218118 (9801,1820) (1,1) [12453049, 48062108] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_59_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 29 (9801,1820) (59,11) k).2 := by
  have h0 : Good 29 29 58 (9801,1820) (59,11) [15, 44] :=
    lift (t:=1) (s:=58) (good_one 29 (9801,1820) (59,11)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 841 1682 (9801,1820) (59,11) [653, 1494] :=
    lift (t:=58) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 24389 48778 (9801,1820) (59,11) [15791, 40180] :=
    lift (t:=1682) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 707281 1414562 (9801,1820) (59,11) [137736, 845017] :=
    lift (t:=48778) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 20511149 41022298 (9801,1820) (59,11) [2966860, 23478009] :=
    lift (t:=1414562) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_59_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 29 (9801,1820) (59,11) k).2 := by
  have h0 : Good 29 37 38 (9801,1820) (59,11) [13, 32] :=
    lift (t:=1) (s:=38) (good_one 29 (9801,1820) (59,11)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 1369 1406 (9801,1820) (59,11) [127, 830] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 50653 52022 (9801,1820) (59,11) [14890, 40901] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 1874161 1924814 (9801,1820) (59,11) [379044, 1341451] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 69343957 71218118 (9801,1820) (59,11) [35025696, 70634755] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_86_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 29 (9801,1820) (86,16) k).2 := by
  have h0 : Good 29 29 58 (9801,1820) (86,16) [23, 52] :=
    lift (t:=1) (s:=58) (good_one 29 (9801,1820) (86,16)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 841 1682 (9801,1820) (86,16) [748, 1589] :=
    lift (t:=58) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 24389 48778 (9801,1820) (86,16) [16727, 41116] :=
    lift (t:=1682) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 707281 1414562 (9801,1820) (86,16) [333784, 1041065] :=
    lift (t:=48778) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 20511149 41022298 (9801,1820) (86,16) [3870189, 24381338] :=
    lift (t:=1414562) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_86_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 29 (9801,1820) (86,16) k).2 := by
  have h0 : Good 29 37 38 (9801,1820) (86,16) [18, 37] :=
    lift (t:=1) (s:=38) (good_one 29 (9801,1820) (86,16)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 1369 1406 (9801,1820) (86,16) [341, 1044] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 50653 52022 (9801,1820) (86,16) [2450, 28461] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 1874161 1924814 (9801,1820) (86,16) [262560, 1224967] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 69343957 71218118 (9801,1820) (86,16) [24322735, 59931794] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_1594_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 29 (9801,1820) (1594,296) k).2 := by
  have h0 : Good 29 29 58 (9801,1820) (1594,296) [5, 34] :=
    lift (t:=1) (s:=58) (good_one 29 (9801,1820) (1594,296)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 841 1682 (9801,1820) (1594,296) [92, 933] :=
    lift (t:=58) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 24389 48778 (9801,1820) (1594,296) [7661, 32050] :=
    lift (t:=1682) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 707281 1414562 (9801,1820) (1594,296) [373496, 1080777] :=
    lift (t:=48778) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 20511149 41022298 (9801,1820) (1594,296) [16640959, 37152108] :=
    lift (t:=1414562) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_1594_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 29 (9801,1820) (1594,296) k).2 := by
  have h0 : Good 29 37 38 (9801,1820) (1594,296) [0, 19] :=
    lift (t:=1) (s:=38) (good_one 29 (9801,1820) (1594,296)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 1369 1406 (9801,1820) (1594,296) [361, 1064] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 50653 52022 (9801,1820) (1594,296) [23560, 49571] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 1874161 1924814 (9801,1820) (1594,296) [699846, 1662253] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 69343957 71218118 (9801,1820) (1594,296) [11286323, 46895382] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_2321_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 29 (9801,1820) (2321,431) k).2 := by
  have h0 : Good 29 29 58 (9801,1820) (2321,431) [13, 42] :=
    lift (t:=1) (s:=58) (good_one 29 (9801,1820) (2321,431)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 841 1682 (9801,1820) (2321,431) [187, 1028] :=
    lift (t:=58) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 24389 48778 (9801,1820) (2321,431) [8597, 32986] :=
    lift (t:=1682) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 707281 1414562 (9801,1820) (2321,431) [569544, 1276825] :=
    lift (t:=48778) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 20511149 41022298 (9801,1820) (2321,431) [17544288, 38055437] :=
    lift (t:=1414562) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_2321_37 {k : ℕ} (hk : k<2097152) : ¬37^6∣(orbit 29 (9801,1820) (2321,431) k).2 := by
  have h0 : Good 29 37 38 (9801,1820) (2321,431) [5, 24] :=
    lift (t:=1) (s:=38) (good_one 29 (9801,1820) (2321,431)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 1369 1406 (9801,1820) (2321,431) [575, 1278] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 50653 52022 (9801,1820) (2321,431) [11120, 37131] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 1874161 1924814 (9801,1820) (2321,431) [583362, 1545769] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 69343957 71218118 (9801,1820) (2321,431) [583362, 36192421] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 29 2565726409 2635070366 (9801,1820) (2321,431) [1104464191, 2421999374] :=
    lift (t:=71218118) (s:=37) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_42979_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 29 (9801,1820) (42979,7981) k).2 := by
  have h0 : Good 29 29 58 (9801,1820) (42979,7981) [24, 53] :=
    lift (t:=1) (s:=58) (good_one 29 (9801,1820) (42979,7981)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 841 1682 (9801,1820) (42979,7981) [372, 1213] :=
    lift (t:=58) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 24389 48778 (9801,1820) (42979,7981) [23920, 48309] :=
    lift (t:=1682) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 707281 1414562 (9801,1820) (42979,7981) [609256, 1316537] :=
    lift (t:=48778) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 20511149 41022298 (9801,1820) (42979,7981) [9803909, 30315058] :=
    lift (t:=1414562) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid29_42979_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 29 (9801,1820) (42979,7981) k).2 := by
  have h0 : Good 29 37 38 (9801,1820) (42979,7981) [6, 25] :=
    lift (t:=1) (s:=38) (good_one 29 (9801,1820) (42979,7981)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 29 1369 1406 (9801,1820) (42979,7981) [595, 1298] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 29 50653 52022 (9801,1820) (42979,7981) [6219, 32230] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 29 1874161 1924814 (9801,1820) (42979,7981) [58241, 1020648] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 29 69343957 71218118 (9801,1820) (42979,7981) [23156009, 58765068] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth29 {x y : ℕ} (eqn : x^2+28=29*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣1073) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent29 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣1073^6 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=29 ∨ p=37 := by
      have h : p∣29*(37) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 29)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h))
    have horb : p^(6+1)∣(orbit 29 (9801,1820) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid29_1_29 low ((pow_dvd_pow 29 (by decide : 5≤6+1)).trans horb)
      · exact avoid29_1_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid29_59_29 low ((pow_dvd_pow 29 (by decide : 5≤6+1)).trans horb)
      · exact avoid29_59_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid29_86_29 low ((pow_dvd_pow 29 (by decide : 5≤6+1)).trans horb)
      · exact avoid29_86_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid29_1594_29 low ((pow_dvd_pow 29 (by decide : 5≤6+1)).trans horb)
      · exact avoid29_1594_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid29_2321_29 low ((pow_dvd_pow 29 (by decide : 5≤6+1)).trans horb)
      · exact avoid29_2321_37 low ((pow_dvd_pow 37 (by decide : 6≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid29_42979_29 low ((pow_dvd_pow 29 (by decide : 5≤6+1)).trans horb)
      · exact avoid29_42979_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
  have limK : k<61 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<1073^6) dv
    have : 1073^6<2^61 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(59,11),(86,16),(1594,296),(2321,431),(42979,7981)] : List (ℕ×ℕ)), ∀ i : Fin 61,
      (orbit 29 (9801,1820) s i.val).2∣1073^6 → (orbit 29 (9801,1820) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent31 {x y : ℕ} (eqn : x^2+30=31*y^2) :
    ∃ s ∈ ([(1,1),(61,11),(373,67),(6943,1247)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 31 (1520,273) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<1496
    · have calcX : 31*y^2-30=x^2 := by omega
      have tab : ∀ hi : Fin 12, ∀ lo : Fin 128, hi.val*128+lo.val<1496 → let a := 31*(hi.val*128+lo.val)^2-30
        (Nat.sqrt a)^2+30=31*(hi.val*128+lo.val)^2 →
          (Nat.sqrt a,(hi.val*128+lo.val))∈([(1,1),(61,11),(373,67),(6943,1247)] : List (ℕ×ℕ)) := by decide +kernel
      have mem := tab ⟨y/128,by omega⟩ ⟨y%128,by omega⟩
      dsimp only at mem
      rw [show y/128*128+y%128=y by omega] at mem
      specialize mem small
      rw [calcX,Nat.sqrt_eq'] at mem
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),mem eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 1496^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 8463*y≤1520*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 273*x≤1520*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 1519*y<273*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 1520*x-8463*y
    let v := 1520*y-273*x
    have hu : u+8463*y=1520*x := Nat.sub_add_cancel ax
    have hv : v+273*x=1520*y := Nat.sub_add_cancel ay
    have ev : u^2+30=31*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid31_1_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 31 (1520,273) (1,1) k).2 := by
  have h0 : Good 31 31 31 (1520,273) (1,1) [26] :=
    lift (t:=1) (s:=31) (good_one 31 (1520,273) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 31 961 961 (1520,273) (1,1) [708] :=
    lift (t:=31) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 31 29791 29791 (1520,273) (1,1) [18967] :=
    lift (t:=961) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 31 923521 923521 (1520,273) (1,1) [495623] :=
    lift (t:=29791) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 31 28629151 28629151 (1520,273) (1,1) [24507169] :=
    lift (t:=923521) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid31_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 31 (1520,273) (1,1) k).2 := by
  have h0 : Good 31 37 38 (1520,273) (1,1) [14, 33] :=
    lift (t:=1) (s:=38) (good_one 31 (1520,273) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 31 1369 1406 (1520,273) (1,1) [432, 1135] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 31 50653 52022 (1520,273) (1,1) [9571, 35582] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 31 1874161 1924814 (1520,273) (1,1) [763890, 1726297] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 31 69343957 71218118 (1520,273) (1,1) [29636100, 65245159] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid31_61_31 {k : ℕ} (hk : k<2097152) : ¬31^6∣(orbit 31 (1520,273) (61,11) k).2 := by
  have h0 : Good 31 31 31 (1520,273) (61,11) [24] :=
    lift (t:=1) (s:=31) (good_one 31 (1520,273) (61,11)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 31 961 961 (1520,273) (61,11) [396] :=
    lift (t:=31) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 31 29791 29791 (1520,273) (61,11) [2318] :=
    lift (t:=961) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 31 923521 923521 (1520,273) (61,11) [181064] :=
    lift (t:=29791) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 31 28629151 28629151 (1520,273) (61,11) [1104585] :=
    lift (t:=923521) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 31 887503681 887503681 (1520,273) (61,11) [316025246] :=
    lift (t:=28629151) (s:=31) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid31_61_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 31 (1520,273) (61,11) k).2 := by
  have h0 : Good 31 37 38 (1520,273) (61,11) [15, 34] :=
    lift (t:=1) (s:=38) (good_one 31 (1520,273) (61,11)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 31 1369 1406 (1520,273) (61,11) [452, 1155] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 31 50653 52022 (1520,273) (61,11) [10997, 37008] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 31 1874161 1924814 (1520,273) (61,11) [349140, 1311547] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 31 69343957 71218118 (1520,273) (61,11) [21522094, 57131153] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid31_373_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 31 (1520,273) (373,67) k).2 := by
  have h0 : Good 31 31 31 (1520,273) (373,67) [6] :=
    lift (t:=1) (s:=31) (good_one 31 (1520,273) (373,67)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 31 961 961 (1520,273) (373,67) [564] :=
    lift (t:=31) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 31 29791 29791 (1520,273) (373,67) [27472] :=
    lift (t:=961) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 31 923521 923521 (1520,273) (373,67) [742456] :=
    lift (t:=29791) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 31 28629151 28629151 (1520,273) (373,67) [27524565] :=
    lift (t:=923521) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid31_373_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 31 (1520,273) (373,67) k).2 := by
  have h0 : Good 31 37 38 (1520,273) (373,67) [3, 22] :=
    lift (t:=1) (s:=38) (good_one 31 (1520,273) (373,67)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 31 1369 1406 (1520,273) (373,67) [250, 953] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 31 50653 52022 (1520,273) (373,67) [15013, 41024] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 31 1874161 1924814 (1520,273) (373,67) [613266, 1575673] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 31 69343957 71218118 (1520,273) (373,67) [14086964, 49696023] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid31_6943_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 31 (1520,273) (6943,1247) k).2 := by
  have h0 : Good 31 31 31 (1520,273) (6943,1247) [4] :=
    lift (t:=1) (s:=31) (good_one 31 (1520,273) (6943,1247)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 31 961 961 (1520,273) (6943,1247) [252] :=
    lift (t:=31) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 31 29791 29791 (1520,273) (6943,1247) [10823] :=
    lift (t:=961) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 31 923521 923521 (1520,273) (6943,1247) [427897] :=
    lift (t:=29791) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 31 28629151 28629151 (1520,273) (6943,1247) [4121981] :=
    lift (t:=923521) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid31_6943_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 31 (1520,273) (6943,1247) k).2 := by
  have h0 : Good 31 37 38 (1520,273) (6943,1247) [4, 23] :=
    lift (t:=1) (s:=38) (good_one 31 (1520,273) (6943,1247)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 31 1369 1406 (1520,273) (6943,1247) [270, 973] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 31 50653 52022 (1520,273) (6943,1247) [16439, 42450] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 31 1874161 1924814 (1520,273) (6943,1247) [198516, 1160923] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 31 69343957 71218118 (1520,273) (6943,1247) [5972958, 41582017] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth31 {x y : ℕ} (eqn : x^2+30=31*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣1147) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent31 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣1147^6 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=31 ∨ p=37 := by
      have h : p∣31*(37) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h))
    have horb : p^(6+1)∣(orbit 31 (1520,273) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid31_1_31 low ((pow_dvd_pow 31 (by decide : 5≤6+1)).trans horb)
      · exact avoid31_1_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid31_61_31 low ((pow_dvd_pow 31 (by decide : 6≤6+1)).trans horb)
      · exact avoid31_61_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid31_373_31 low ((pow_dvd_pow 31 (by decide : 5≤6+1)).trans horb)
      · exact avoid31_373_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid31_6943_31 low ((pow_dvd_pow 31 (by decide : 5≤6+1)).trans horb)
      · exact avoid31_6943_37 low ((pow_dvd_pow 37 (by decide : 5≤6+1)).trans horb)
  have limK : k<61 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<1147^6) dv
    have : 1147^6<2^61 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(61,11),(373,67),(6943,1247)] : List (ℕ×ℕ)), ∀ i : Fin 61,
      (orbit 31 (1520,273) s i.val).2∣1147^6 → (orbit 31 (1520,273) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent34 {x y : ℕ} (eqn : x^2+33=34*y^2) :
    ∃ s ∈ ([(1,1),(169,29)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 34 (35,6) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<35
    · have hx : x<199 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤34 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 199, ∀ j : Fin 35, i.val^2+33=34*j.val^2 →
          (i.val,j.val)∈([(1,1),(169,29)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 35^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 204*y≤35*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 6*x≤35*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 34*y<6*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 35*x-204*y
    let v := 35*y-6*x
    have hu : u+204*y=35*x := Nat.sub_add_cancel ax
    have hv : v+6*x=35*y := Nat.sub_add_cancel ay
    have ev : u^2+33=34*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid34_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 34 (35,6) (1,1) k).2 := by
  have h0 : Good 34 2 1 (35,6) (1,1) [] :=
    lift (t:=1) (s:=1) (good_one 34 (35,6) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid34_1_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 34 (35,6) (1,1) k).2 := by
  have h0 : Good 34 17 17 (35,6) (1,1) [14] :=
    lift (t:=1) (s:=17) (good_one 34 (35,6) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 34 289 289 (35,6) (1,1) [269] :=
    lift (t:=17) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 34 4913 4913 (35,6) (1,1) [2870] :=
    lift (t:=289) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 34 83521 83521 (35,6) (1,1) [66739] :=
    lift (t:=4913) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 34 1419857 1419857 (35,6) (1,1) [1319554] :=
    lift (t:=83521) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 34 24137569 24137569 (35,6) (1,1) [15518124] :=
    lift (t:=1419857) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid34_1_37 {k : ℕ} (_hk : k<2097152) : ¬37^2∣(orbit 34 (35,6) (1,1) k).2 := by
  have h0 : Good 34 37 36 (35,6) (1,1) [12, 30] :=
    lift (t:=1) (s:=36) (good_one 34 (35,6) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 34 1369 36 (35,6) (1,1) [] :=
    lift (t:=36) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid34_169_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 34 (35,6) (169,29) k).2 := by
  have h0 : Good 34 2 1 (35,6) (169,29) [] :=
    lift (t:=1) (s:=1) (good_one 34 (35,6) (169,29)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid34_169_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 34 (35,6) (169,29) k).2 := by
  have h0 : Good 34 17 17 (35,6) (169,29) [2] :=
    lift (t:=1) (s:=17) (good_one 34 (35,6) (169,29)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 34 289 289 (35,6) (169,29) [19] :=
    lift (t:=17) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 34 4913 4913 (35,6) (169,29) [2042] :=
    lift (t:=289) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 34 83521 83521 (35,6) (169,29) [16781] :=
    lift (t:=4913) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 34 1419857 1419857 (35,6) (169,29) [100302] :=
    lift (t:=83521) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 34 24137569 24137569 (35,6) (169,29) [8619444] :=
    lift (t:=1419857) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid34_169_37 {k : ℕ} (_hk : k<2097152) : ¬37^2∣(orbit 34 (35,6) (169,29) k).2 := by
  have h0 : Good 34 37 36 (35,6) (169,29) [5, 23] :=
    lift (t:=1) (s:=36) (good_one 34 (35,6) (169,29)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 34 1369 36 (35,6) (169,29) [] :=
    lift (t:=36) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
theorem smooth34 {x y : ℕ} (eqn : x^2+33=34*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣1258) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent34 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣1258^6 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=17 ∨ p=37 := by
      have h : p∣2*(17*(37)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 17)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h)))
    have horb : p^(6+1)∣(orbit 34 (35,6) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid34_1_2 low ((pow_dvd_pow 2 (by decide : 1≤6+1)).trans horb)
      · exact avoid34_1_17 low ((pow_dvd_pow 17 (by decide : 6≤6+1)).trans horb)
      · exact avoid34_1_37 low ((pow_dvd_pow 37 (by decide : 2≤6+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid34_169_2 low ((pow_dvd_pow 2 (by decide : 1≤6+1)).trans horb)
      · exact avoid34_169_17 low ((pow_dvd_pow 17 (by decide : 6≤6+1)).trans horb)
      · exact avoid34_169_37 low ((pow_dvd_pow 37 (by decide : 2≤6+1)).trans horb)
  have limK : k<62 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<1258^6) dv
    have : 1258^6<2^62 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(169,29)] : List (ℕ×ℕ)), ∀ i : Fin 62,
      (orbit 34 (35,6) s i.val).2∣1258^6 → (orbit 34 (35,6) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent35 {x y : ℕ} (eqn : x^2+34=35*y^2) :
    ∃ s ∈ ([(1,1),(29,5)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 35 (6,1) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<6
    · have hx : x<30 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤5 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 30, ∀ j : Fin 6, i.val^2+34=35*j.val^2 →
          (i.val,j.val)∈([(1,1),(29,5)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 6^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 35*y≤6*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 1*x≤6*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 5*y<1*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 6*x-35*y
    let v := 6*y-1*x
    have hu : u+35*y=6*x := Nat.sub_add_cancel ax
    have hv : v+1*x=6*y := Nat.sub_add_cancel ay
    have ev : u^2+34=35*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid35_1_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 35 (6,1) (1,1) k).2 := by
  have h0 : Good 35 5 5 (6,1) (1,1) [4] :=
    lift (t:=1) (s:=5) (good_one 35 (6,1) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 35 25 25 (6,1) (1,1) [19] :=
    lift (t:=5) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 35 125 125 (6,1) (1,1) [19] :=
    lift (t:=25) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 35 625 625 (6,1) (1,1) [394] :=
    lift (t:=125) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 35 3125 3125 (6,1) (1,1) [2894] :=
    lift (t:=625) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 35 15625 15625 (6,1) (1,1) [9144] :=
    lift (t:=3125) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 35 78125 78125 (6,1) (1,1) [71644] :=
    lift (t:=15625) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 35 390625 390625 (6,1) (1,1) [384144] :=
    lift (t:=78125) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 35 1953125 1953125 (6,1) (1,1) [774769] :=
    lift (t:=390625) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 35 9765625 9765625 (6,1) (1,1) [8587269] :=
    lift (t:=1953125) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid35_1_7 {k : ℕ} (hk : k<2097152) : ¬7^8∣(orbit 35 (6,1) (1,1) k).2 := by
  have h0 : Good 35 7 14 (6,1) (1,1) [1, 8] :=
    lift (t:=1) (s:=14) (good_one 35 (6,1) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 35 49 98 (6,1) (1,1) [43, 92] :=
    lift (t:=14) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 35 343 686 (6,1) (1,1) [288, 631] :=
    lift (t:=98) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 35 2401 4802 (6,1) (1,1) [631, 3032] :=
    lift (t:=686) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 35 16807 33614 (6,1) (1,1) [7834, 24641] :=
    lift (t:=4802) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 35 117649 235298 (6,1) (1,1) [24641, 142290] :=
    lift (t:=33614) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 35 823543 1647086 (6,1) (1,1) [730535, 1554078] :=
    lift (t:=235298) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 35 5764801 11529602 (6,1) (1,1) [4024707, 9789508] :=
    lift (t:=1647086) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h7 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid35_1_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 35 (6,1) (1,1) k).2 := by
  have h0 : Good 35 37 38 (6,1) (1,1) [16, 35] :=
    lift (t:=1) (s:=38) (good_one 35 (6,1) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 35 1369 1406 (6,1) (1,1) [453, 1156] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 35 50653 52022 (6,1) (1,1) [14513, 40524] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 35 1874161 1924814 (6,1) (1,1) [170579, 1132986] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 35 69343957 71218118 (6,1) (1,1) [32892417, 68501476] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid35_29_5 {k : ℕ} (hk : k<2097152) : ¬5^12∣(orbit 35 (6,1) (29,5) k).2 := by
  have h0 : Good 35 5 5 (6,1) (29,5) [0] :=
    lift (t:=1) (s:=5) (good_one 35 (6,1) (29,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 35 25 25 (6,1) (29,5) [5] :=
    lift (t:=5) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 35 125 125 (6,1) (29,5) [105] :=
    lift (t:=25) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 35 625 625 (6,1) (29,5) [230] :=
    lift (t:=125) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 35 3125 3125 (6,1) (29,5) [230] :=
    lift (t:=625) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 35 15625 15625 (6,1) (29,5) [6480] :=
    lift (t:=3125) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 35 78125 78125 (6,1) (29,5) [6480] :=
    lift (t:=15625) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 35 390625 390625 (6,1) (29,5) [6480] :=
    lift (t:=78125) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 35 1953125 1953125 (6,1) (29,5) [1178355] :=
    lift (t:=390625) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 35 9765625 9765625 (6,1) (29,5) [1178355] :=
    lift (t:=1953125) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 35 48828125 48828125 (6,1) (29,5) [1178355] :=
    lift (t:=9765625) (s:=5) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 35 244140625 244140625 (6,1) (29,5) [147662730] :=
    lift (t:=48828125) (s:=5) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h11 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid35_29_7 {k : ℕ} (hk : k<2097152) : ¬7^9∣(orbit 35 (6,1) (29,5) k).2 := by
  have h0 : Good 35 7 14 (6,1) (29,5) [5, 12] :=
    lift (t:=1) (s:=14) (good_one 35 (6,1) (29,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 35 49 98 (6,1) (29,5) [5, 54] :=
    lift (t:=14) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 35 343 686 (6,1) (29,5) [54, 397] :=
    lift (t:=98) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 35 2401 4802 (6,1) (29,5) [1769, 4170] :=
    lift (t:=686) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 35 16807 33614 (6,1) (29,5) [8972, 25779] :=
    lift (t:=4802) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 35 117649 235298 (6,1) (29,5) [93007, 210656] :=
    lift (t:=33614) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 35 823543 1647086 (6,1) (29,5) [93007, 916550] :=
    lift (t:=235298) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 35 5764801 11529602 (6,1) (29,5) [1740093, 7504894] :=
    lift (t:=1647086) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 35 40353607 80707214 (6,1) (29,5) [36328899, 76682506] :=
    lift (t:=11529602) (s:=7) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h8 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid35_29_37 {k : ℕ} (hk : k<2097152) : ¬37^5∣(orbit 35 (6,1) (29,5) k).2 := by
  have h0 : Good 35 37 38 (6,1) (29,5) [2, 21] :=
    lift (t:=1) (s:=38) (good_one 35 (6,1) (29,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 35 1369 1406 (6,1) (29,5) [249, 952] :=
    lift (t:=38) (s:=37) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 35 50653 52022 (6,1) (29,5) [11497, 37508] :=
    lift (t:=1406) (s:=37) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 35 1874161 1924814 (6,1) (29,5) [791827, 1754234] :=
    lift (t:=52022) (s:=37) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 35 69343957 71218118 (6,1) (29,5) [2716641, 38325700] :=
    lift (t:=1924814) (s:=37) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
theorem smooth35 {x y : ℕ} (eqn : x^2+34=35*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣1295) : x≤41 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent35 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣1295^12 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=5 ∨ p=7 ∨ p=37 := by
      have h : p∣5*(7*(37)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 5)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 7)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 37)).mp h)))
    have horb : p^(12+1)∣(orbit 35 (6,1) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid35_1_5 low ((pow_dvd_pow 5 (by decide : 10≤12+1)).trans horb)
      · exact avoid35_1_7 low ((pow_dvd_pow 7 (by decide : 8≤12+1)).trans horb)
      · exact avoid35_1_37 low ((pow_dvd_pow 37 (by decide : 5≤12+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid35_29_5 low ((pow_dvd_pow 5 (by decide : 12≤12+1)).trans horb)
      · exact avoid35_29_7 low ((pow_dvd_pow 7 (by decide : 9≤12+1)).trans horb)
      · exact avoid35_29_37 low ((pow_dvd_pow 37 (by decide : 5≤12+1)).trans horb)
  have limK : k<125 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<1295^12) dv
    have : 1295^12<2^125 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(29,5)] : List (ℕ×ℕ)), ∀ i : Fin 125,
      (orbit 35 (6,1) s i.val).2∣1295^12 → (orbit 35 (6,1) s i.val).1≤41 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


end Erdos889.SquareThirtySeven
