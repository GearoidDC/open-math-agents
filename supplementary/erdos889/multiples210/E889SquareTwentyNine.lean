import E889SquareTwentyThree

/-! Prime-square successor solutions when 29 is the first missing prime. -/

namespace Erdos889.SquareTwentyNine

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
private theorem avoid2_1_29 {k : ℕ} (hk : k<2097152) : ¬29^6∣(orbit 2 (3,2) (1,1) k).2 := by
  have h0 : Good 2 29 10 (3,2) (1,1) [2, 7] :=
    lift (t:=1) (s:=10) (good_one 2 (3,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 841 290 (3,2) (1,1) [72, 217] :=
    lift (t:=10) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 24389 8410 (3,2) (1,1) [2102, 6307] :=
    lift (t:=290) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 707281 243890 (3,2) (1,1) [60972, 182917] :=
    lift (t:=8410) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 20511149 7072810 (3,2) (1,1) [1768202, 5304607] :=
    lift (t:=243890) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 594823321 205111490 (3,2) (1,1) [51277872, 153833617] :=
    lift (t:=7072810) (s:=29) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth2 {x y : ℕ} (eqn : x^2+1=2*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣58) : x≤41 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent2 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣58^6 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 59, i.val.Prime → i.val∣58 → i.val=2 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=29 at tags
    have horb : p^(6+1)∣(orbit 2 (3,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    subst s
    rcases tags with rfl|rfl
    · exact avoid2_1_2 low ((pow_dvd_pow 2 (by decide : 1≤6+1)).trans horb)
    · exact avoid2_1_29 low ((pow_dvd_pow 29 (by decide : 6≤6+1)).trans horb)
  have limK : k<36 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<58^6) dv
    have : 58^6<2^36 := by decide
    omega
  have small : ∀ s ∈ ([(1,1)] : List (ℕ×ℕ)), ∀ i : Fin 36,
      (orbit 2 (3,2) s i.val).2∣58^6 → (orbit 2 (3,2) s i.val).1≤41 := by decide +kernel
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
private theorem avoid5_1_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 5 (9,4) (1,1) k).2 := by
  have h0 : Good 5 29 7 (9,4) (1,1) [] :=
    lift (t:=1) (s:=7) (good_one 5 (9,4) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
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
private theorem avoid5_4_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 5 (9,4) (4,2) k).2 := by
  have h0 : Good 5 29 7 (9,4) (4,2) [] :=
    lift (t:=1) (s:=7) (good_one 5 (9,4) (4,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
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
private theorem avoid5_11_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 5 (9,4) (11,5) k).2 := by
  have h0 : Good 5 29 7 (9,4) (11,5) [] :=
    lift (t:=1) (s:=7) (good_one 5 (9,4) (11,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth5 {x y : ℕ} (eqn : x^2+4=5*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣145) : x≤11 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent5 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣145^11 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 146, i.val.Prime → i.val∣145 → i.val=5 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=5 ∨ p=29 at tags
    have horb : p^(11+1)∣(orbit 5 (9,4) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid5_1_5 low ((pow_dvd_pow 5 (by decide : 11≤11+1)).trans horb)
      · exact avoid5_1_29 low ((pow_dvd_pow 29 (by decide : 1≤11+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid5_4_5 low ((pow_dvd_pow 5 (by decide : 10≤11+1)).trans horb)
      · exact avoid5_4_29 low ((pow_dvd_pow 29 (by decide : 1≤11+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid5_11_5 low ((pow_dvd_pow 5 (by decide : 10≤11+1)).trans horb)
      · exact avoid5_11_29 low ((pow_dvd_pow 29 (by decide : 1≤11+1)).trans horb)
  have limK : k<79 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<145^11) dv
    have : 145^11<2^79 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(4,2),(11,5)] : List (ℕ×ℕ)), ∀ i : Fin 79,
      (orbit 5 (9,4) s i.val).2∣145^11 → (orbit 5 (9,4) s i.val).1≤11 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent6 {x y : ℕ} (eqn : x^2+5=6*y^2) :
    ∃ s ∈ ([(1,1),(7,3)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 6 (5,2) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<5
    · have hx : x<10 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤4 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 10, ∀ j : Fin 5, i.val^2+5=6*j.val^2 →
          (i.val,j.val)∈([(1,1),(7,3)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 5^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 12*y≤5*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 2*x≤5*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 4*y<2*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 5*x-12*y
    let v := 5*y-2*x
    have hu : u+12*y=5*x := Nat.sub_add_cancel ax
    have hv : v+2*x=5*y := Nat.sub_add_cancel ay
    have ev : u^2+5=6*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid6_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 6 (5,2) (1,1) k).2 := by
  have h0 : Good 6 2 1 (5,2) (1,1) [] :=
    lift (t:=1) (s:=1) (good_one 6 (5,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid6_1_3 {k : ℕ} (_hk : k<2097152) : ¬3^2∣(orbit 6 (5,2) (1,1) k).2 := by
  have h0 : Good 6 3 6 (5,2) (1,1) [2, 5] :=
    lift (t:=1) (s:=6) (good_one 6 (5,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 9 6 (5,2) (1,1) [] :=
    lift (t:=6) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid6_1_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 6 (5,2) (1,1) k).2 := by
  have h0 : Good 6 29 28 (5,2) (1,1) [12, 26] :=
    lift (t:=1) (s:=28) (good_one 6 (5,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 841 812 (5,2) (1,1) [96, 502] :=
    lift (t:=28) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 6 24389 23548 (5,2) (1,1) [9840, 21614] :=
    lift (t:=812) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 6 707281 682892 (5,2) (1,1) [327738, 669184] :=
    lift (t:=23548) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 6 20511149 19803868 (5,2) (1,1) [9205334, 19107268] :=
    lift (t:=682892) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid6_7_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 6 (5,2) (7,3) k).2 := by
  have h0 : Good 6 2 1 (5,2) (7,3) [] :=
    lift (t:=1) (s:=1) (good_one 6 (5,2) (7,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid6_7_3 {k : ℕ} (_hk : k<2097152) : ¬3^2∣(orbit 6 (5,2) (7,3) k).2 := by
  have h0 : Good 6 3 6 (5,2) (7,3) [0, 3] :=
    lift (t:=1) (s:=6) (good_one 6 (5,2) (7,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 9 6 (5,2) (7,3) [] :=
    lift (t:=6) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid6_7_29 {k : ℕ} (hk : k<2097152) : ¬29^6∣(orbit 6 (5,2) (7,3) k).2 := by
  have h0 : Good 6 29 28 (5,2) (7,3) [1, 15] :=
    lift (t:=1) (s:=28) (good_one 6 (5,2) (7,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 841 812 (5,2) (7,3) [309, 715] :=
    lift (t:=28) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 6 24389 23548 (5,2) (7,3) [1933, 13707] :=
    lift (t:=812) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 6 707281 682892 (5,2) (7,3) [13707, 355153] :=
    lift (t:=23548) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 6 20511149 19803868 (5,2) (7,3) [696599, 10598533] :=
    lift (t:=682892) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 6 594823321 574312172 (5,2) (7,3) [268048817, 555204903] :=
    lift (t:=19803868) (s:=29) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth6 {x y : ℕ} (eqn : x^2+5=6*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣174) : x≤71 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent6 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣174^6 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 175, i.val.Prime → i.val∣174 → i.val=2 ∨ i.val=3 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=3 ∨ p=29 at tags
    have horb : p^(6+1)∣(orbit 6 (5,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid6_1_2 low ((pow_dvd_pow 2 (by decide : 1≤6+1)).trans horb)
      · exact avoid6_1_3 low ((pow_dvd_pow 3 (by decide : 2≤6+1)).trans horb)
      · exact avoid6_1_29 low ((pow_dvd_pow 29 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid6_7_2 low ((pow_dvd_pow 2 (by decide : 1≤6+1)).trans horb)
      · exact avoid6_7_3 low ((pow_dvd_pow 3 (by decide : 2≤6+1)).trans horb)
      · exact avoid6_7_29 low ((pow_dvd_pow 29 (by decide : 6≤6+1)).trans horb)
  have limK : k<45 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<174^6) dv
    have : 174^6<2^45 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(7,3)] : List (ℕ×ℕ)), ∀ i : Fin 45,
      (orbit 6 (5,2) s i.val).2∣174^6 → (orbit 6 (5,2) s i.val).1≤71 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent7 {x y : ℕ} (eqn : x^2+6=7*y^2) :
    ∃ s ∈ ([(1,1),(13,5)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 7 (8,3) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<8
    · have hx : x<19 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤7 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 19, ∀ j : Fin 8, i.val^2+6=7*j.val^2 →
          (i.val,j.val)∈([(1,1),(13,5)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 8^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
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
    have ev : u^2+6=7*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid7_1_7 {k : ℕ} (hk : k<2097152) : ¬7^8∣(orbit 7 (8,3) (1,1) k).2 := by
  have h0 : Good 7 7 7 (8,3) (1,1) [2] :=
    lift (t:=1) (s:=7) (good_one 7 (8,3) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 49 49 (8,3) (1,1) [9] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 343 343 (8,3) (1,1) [156] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 2401 2401 (8,3) (1,1) [499] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 16807 16807 (8,3) (1,1) [499] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 117649 117649 (8,3) (1,1) [67727] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 7 823543 823543 (8,3) (1,1) [538323] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 7 5764801 5764801 (8,3) (1,1) [4656038] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h7 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid7_1_29 {k : ℕ} (hk : k<2097152) : ¬29^6∣(orbit 7 (8,3) (1,1) k).2 := by
  have h0 : Good 7 29 28 (8,3) (1,1) [8, 22] :=
    lift (t:=1) (s:=28) (good_one 7 (8,3) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 841 812 (8,3) (1,1) [64, 470] :=
    lift (t:=28) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 24389 23548 (8,3) (1,1) [6560, 18334] :=
    lift (t:=812) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 707281 682892 (8,3) (1,1) [159622, 501068] :=
    lift (t:=23548) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 20511149 19803868 (8,3) (1,1) [501068, 10403002] :=
    lift (t:=682892) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 594823321 574312172 (8,3) (1,1) [158932012, 446088098] :=
    lift (t:=19803868) (s:=29) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid7_13_7 {k : ℕ} (hk : k<2097152) : ¬7^9∣(orbit 7 (8,3) (13,5) k).2 := by
  have h0 : Good 7 7 7 (8,3) (13,5) [4] :=
    lift (t:=1) (s:=7) (good_one 7 (8,3) (13,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 49 49 (8,3) (13,5) [39] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 343 343 (8,3) (13,5) [186] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 2401 2401 (8,3) (13,5) [1901] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 16807 16807 (8,3) (13,5) [16307] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 117649 117649 (8,3) (13,5) [49921] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 7 823543 823543 (8,3) (13,5) [285219] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 7 5764801 5764801 (8,3) (13,5) [1108762] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 7 40353607 40353607 (8,3) (13,5) [6873563] :=
    lift (t:=5764801) (s:=7) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h8 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid7_13_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 7 (8,3) (13,5) k).2 := by
  have h0 : Good 7 29 28 (8,3) (13,5) [5, 19] :=
    lift (t:=1) (s:=28) (good_one 7 (8,3) (13,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 841 812 (8,3) (13,5) [341, 747] :=
    lift (t:=28) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 24389 23548 (8,3) (13,5) [5213, 16987] :=
    lift (t:=812) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 707281 682892 (8,3) (13,5) [181823, 523269] :=
    lift (t:=23548) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 20511149 19803868 (8,3) (13,5) [9400865, 19302799] :=
    lift (t:=682892) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth7 {x y : ℕ} (eqn : x^2+6=7*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣203) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent7 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣203^9 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 204, i.val.Prime → i.val∣203 → i.val=7 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=7 ∨ p=29 at tags
    have horb : p^(9+1)∣(orbit 7 (8,3) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid7_1_7 low ((pow_dvd_pow 7 (by decide : 8≤9+1)).trans horb)
      · exact avoid7_1_29 low ((pow_dvd_pow 29 (by decide : 6≤9+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid7_13_7 low ((pow_dvd_pow 7 (by decide : 9≤9+1)).trans horb)
      · exact avoid7_13_29 low ((pow_dvd_pow 29 (by decide : 5≤9+1)).trans horb)
  have limK : k<69 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<203^9) dv
    have : 203^9<2^69 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(13,5)] : List (ℕ×ℕ)), ∀ i : Fin 69,
      (orbit 7 (8,3) s i.val).2∣203^9 → (orbit 7 (8,3) s i.val).1≤1 := by decide +kernel
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
private theorem avoid8_1_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 2 (3,2) (1,2) k).2 := by
  have h0 : Good 2 29 10 (3,2) (1,2) [] :=
    lift (t:=1) (s:=10) (good_one 2 (3,2) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
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
private theorem avoid8_5_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 2 (3,2) (5,4) k).2 := by
  have h0 : Good 2 29 10 (3,2) (5,4) [] :=
    lift (t:=1) (s:=10) (good_one 2 (3,2) (5,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth8 {x y : ℕ} (eqn : x^2+7=2*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣58) : x≤181 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent8 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣58^24 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 59, i.val.Prime → i.val∣58 → i.val=2 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=29 at tags
    have horb : p^(24+1)∣(orbit 2 (3,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid8_1_2 low ((pow_dvd_pow 2 (by decide : 24≤24+1)).trans horb)
      · exact avoid8_1_29 low ((pow_dvd_pow 29 (by decide : 1≤24+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid8_5_2 low ((pow_dvd_pow 2 (by decide : 23≤24+1)).trans horb)
      · exact avoid8_5_29 low ((pow_dvd_pow 29 (by decide : 1≤24+1)).trans horb)
  have limK : k<141 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<58^24) dv
    have : 58^24<2^141 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(5,4)] : List (ℕ×ℕ)), ∀ i : Fin 141,
      (orbit 2 (3,2) s i.val).2∣58^24 → (orbit 2 (3,2) s i.val).1≤181 := by decide +kernel
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
private theorem avoid10_1_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 10 (19,6) (1,1) k).2 := by
  have h0 : Good 10 29 30 (19,6) (1,1) [13, 28] :=
    lift (t:=1) (s:=30) (good_one 10 (19,6) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 10 841 870 (19,6) (1,1) [238, 673] :=
    lift (t:=30) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 10 24389 25230 (19,6) (1,1) [6328, 18943] :=
    lift (t:=870) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 10 707281 731670 (19,6) (1,1) [145093, 510928] :=
    lift (t:=25230) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 10 20511149 21218430 (19,6) (1,1) [9656803, 20266018] :=
    lift (t:=731670) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
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
private theorem avoid10_9_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 10 (19,6) (9,3) k).2 := by
  have h0 : Good 10 29 30 (19,6) (9,3) [7, 22] :=
    lift (t:=1) (s:=30) (good_one 10 (19,6) (9,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 10 841 870 (19,6) (9,3) [217, 652] :=
    lift (t:=30) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 10 24389 25230 (19,6) (9,3) [6307, 18922] :=
    lift (t:=870) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 10 707281 731670 (19,6) (9,3) [182917, 548752] :=
    lift (t:=25230) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 10 20511149 21218430 (19,6) (9,3) [5304607, 15913822] :=
    lift (t:=731670) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid10_41_29 {k : ℕ} (hk : k<2097152) : ¬29^6∣(orbit 10 (19,6) (41,13) k).2 := by
  have h0 : Good 10 29 30 (19,6) (41,13) [1, 16] :=
    lift (t:=1) (s:=30) (good_one 10 (19,6) (41,13)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 10 841 870 (19,6) (41,13) [196, 631] :=
    lift (t:=30) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 10 24389 25230 (19,6) (41,13) [6286, 18901] :=
    lift (t:=870) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 10 707281 731670 (19,6) (41,13) [220741, 586576] :=
    lift (t:=25230) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 10 20511149 21218430 (19,6) (41,13) [952411, 11561626] :=
    lift (t:=731670) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 10 594823321 615334470 (19,6) (41,13) [255573571, 563240806] :=
    lift (t:=21218430) (s:=29) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth10 {x y : ℕ} (eqn : x^2+9=10*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣290) : x≤79 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent10 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣290^10 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 291, i.val.Prime → i.val∣290 → i.val=2 ∨ i.val=5 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=5 ∨ p=29 at tags
    have horb : p^(10+1)∣(orbit 10 (19,6) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid10_1_2 low ((pow_dvd_pow 2 (by decide : 1≤10+1)).trans horb)
      · exact avoid10_1_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid10_1_29 low ((pow_dvd_pow 29 (by decide : 5≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid10_9_2 low ((pow_dvd_pow 2 (by decide : 1≤10+1)).trans horb)
      · exact avoid10_9_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid10_9_29 low ((pow_dvd_pow 29 (by decide : 5≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid10_41_2 low ((pow_dvd_pow 2 (by decide : 1≤10+1)).trans horb)
      · exact avoid10_41_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid10_41_29 low ((pow_dvd_pow 29 (by decide : 6≤10+1)).trans horb)
  have limK : k<82 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<290^10) dv
    have : 290^10<2^82 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(9,3),(41,13)] : List (ℕ×ℕ)), ∀ i : Fin 82,
      (orbit 10 (19,6) s i.val).2∣290^10 → (orbit 10 (19,6) s i.val).1≤79 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent14 {x y : ℕ} (eqn : x^2+13=14*y^2) :
    ∃ s ∈ ([(1,1),(41,11)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 14 (15,4) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<15
    · have hx : x<53 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤14 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 53, ∀ j : Fin 15, i.val^2+13=14*j.val^2 →
          (i.val,j.val)∈([(1,1),(41,11)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 15^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 56*y≤15*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 4*x≤15*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 14*y<4*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 15*x-56*y
    let v := 15*y-4*x
    have hu : u+56*y=15*x := Nat.sub_add_cancel ax
    have hv : v+4*x=15*y := Nat.sub_add_cancel ay
    have ev : u^2+13=14*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid14_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 14 (15,4) (1,1) k).2 := by
  have h0 : Good 14 2 1 (15,4) (1,1) [] :=
    lift (t:=1) (s:=1) (good_one 14 (15,4) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid14_1_7 {k : ℕ} (hk : k<2097152) : ¬7^9∣(orbit 14 (15,4) (1,1) k).2 := by
  have h0 : Good 14 7 7 (15,4) (1,1) [5] :=
    lift (t:=1) (s:=7) (good_one 14 (15,4) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 14 49 49 (15,4) (1,1) [26] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 14 343 343 (15,4) (1,1) [271] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 14 2401 2401 (15,4) (1,1) [2329] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 14 16807 16807 (15,4) (1,1) [4730] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 14 117649 117649 (15,4) (1,1) [38344] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 14 823543 823543 (15,4) (1,1) [155993] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 14 5764801 5764801 (15,4) (1,1) [1803079] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 14 40353607 40353607 (15,4) (1,1) [36391885] :=
    lift (t:=5764801) (s:=7) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h8 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid14_1_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 14 (15,4) (1,1) k).2 := by
  have h0 : Good 14 29 6 (15,4) (1,1) [] :=
    lift (t:=1) (s:=6) (good_one 14 (15,4) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid14_41_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 14 (15,4) (41,11) k).2 := by
  have h0 : Good 14 2 1 (15,4) (41,11) [] :=
    lift (t:=1) (s:=1) (good_one 14 (15,4) (41,11)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid14_41_7 {k : ℕ} (hk : k<2097152) : ¬7^8∣(orbit 14 (15,4) (41,11) k).2 := by
  have h0 : Good 14 7 7 (15,4) (41,11) [1] :=
    lift (t:=1) (s:=7) (good_one 14 (15,4) (41,11)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 14 49 49 (15,4) (41,11) [22] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 14 343 343 (15,4) (41,11) [71] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 14 2401 2401 (15,4) (41,11) [71] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 14 16807 16807 (15,4) (41,11) [12076] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 14 117649 117649 (15,4) (41,11) [79304] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 14 823543 823543 (15,4) (41,11) [667549] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 14 5764801 5764801 (15,4) (41,11) [3961721] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h7 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid14_41_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 14 (15,4) (41,11) k).2 := by
  have h0 : Good 14 29 6 (15,4) (41,11) [] :=
    lift (t:=1) (s:=6) (good_one 14 (15,4) (41,11)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth14 {x y : ℕ} (eqn : x^2+13=14*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣406) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent14 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣406^9 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 407, i.val.Prime → i.val∣406 → i.val=2 ∨ i.val=7 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=7 ∨ p=29 at tags
    have horb : p^(9+1)∣(orbit 14 (15,4) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid14_1_2 low ((pow_dvd_pow 2 (by decide : 1≤9+1)).trans horb)
      · exact avoid14_1_7 low ((pow_dvd_pow 7 (by decide : 9≤9+1)).trans horb)
      · exact avoid14_1_29 low ((pow_dvd_pow 29 (by decide : 1≤9+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid14_41_2 low ((pow_dvd_pow 2 (by decide : 1≤9+1)).trans horb)
      · exact avoid14_41_7 low ((pow_dvd_pow 7 (by decide : 8≤9+1)).trans horb)
      · exact avoid14_41_29 low ((pow_dvd_pow 29 (by decide : 1≤9+1)).trans horb)
  have limK : k<78 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<406^9) dv
    have : 406^9<2^78 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(41,11)] : List (ℕ×ℕ)), ∀ i : Fin 78,
      (orbit 14 (15,4) s i.val).2∣406^9 → (orbit 14 (15,4) s i.val).1≤1 := by decide +kernel
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
private theorem avoid17_1_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 17 (33,8) (1,1) k).2 := by
  have h0 : Good 17 29 30 (33,8) (1,1) [6, 21] :=
    lift (t:=1) (s:=30) (good_one 17 (33,8) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 17 841 870 (33,8) (1,1) [111, 546] :=
    lift (t:=30) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 17 24389 25230 (33,8) (1,1) [9246, 21861] :=
    lift (t:=870) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 17 707281 731670 (33,8) (1,1) [185856, 551691] :=
    lift (t:=25230) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 17 20511149 21218430 (33,8) (1,1) [6039216, 16648431] :=
    lift (t:=731670) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid17_16_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 17 (33,8) (16,4) k).2 := by
  have h0 : Good 17 29 30 (33,8) (16,4) [7, 22] :=
    lift (t:=1) (s:=30) (good_one 17 (33,8) (16,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 17 841 870 (33,8) (16,4) [217, 652] :=
    lift (t:=30) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 17 24389 25230 (33,8) (16,4) [6307, 18922] :=
    lift (t:=870) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 17 707281 731670 (33,8) (16,4) [182917, 548752] :=
    lift (t:=25230) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 17 20511149 21218430 (33,8) (16,4) [5304607, 15913822] :=
    lift (t:=731670) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid17_103_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 17 (33,8) (103,25) k).2 := by
  have h0 : Good 17 29 30 (33,8) (103,25) [8, 23] :=
    lift (t:=1) (s:=30) (good_one 17 (33,8) (103,25)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 17 841 870 (33,8) (103,25) [323, 758] :=
    lift (t:=30) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 17 24389 25230 (33,8) (103,25) [3368, 15983] :=
    lift (t:=870) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 17 707281 731670 (33,8) (103,25) [179978, 545813] :=
    lift (t:=25230) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 17 20511149 21218430 (33,8) (103,25) [4569998, 15179213] :=
    lift (t:=731670) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth17 {x y : ℕ} (eqn : x^2+16=17*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣493) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent17 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣493^6 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 494, i.val.Prime → i.val∣493 → i.val=17 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=17 ∨ p=29 at tags
    have horb : p^(6+1)∣(orbit 17 (33,8) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid17_1_17 low ((pow_dvd_pow 17 (by decide : 6≤6+1)).trans horb)
      · exact avoid17_1_29 low ((pow_dvd_pow 29 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid17_16_17 low ((pow_dvd_pow 17 (by decide : 6≤6+1)).trans horb)
      · exact avoid17_16_29 low ((pow_dvd_pow 29 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid17_103_17 low ((pow_dvd_pow 17 (by decide : 6≤6+1)).trans horb)
      · exact avoid17_103_29 low ((pow_dvd_pow 29 (by decide : 5≤6+1)).trans horb)
  have limK : k<54 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<493^6) dv
    have : 493^6<2^54 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(16,4),(103,25)] : List (ℕ×ℕ)), ∀ i : Fin 54,
      (orbit 17 (33,8) s i.val).2∣493^6 → (orbit 17 (33,8) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent21 {x y : ℕ} (eqn : x^2+20=21*y^2) :
    ∃ s ∈ ([(1,1),(8,2),(13,3),(41,9),(64,14),(197,43)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 21 (55,12) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<54
    · have hx : x<243 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤53 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 243, ∀ j : Fin 54, i.val^2+20=21*j.val^2 →
          (i.val,j.val)∈([(1,1),(8,2),(13,3),(41,9),(64,14),(197,43)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 54^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 252*y≤55*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 12*x≤55*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 54*y<12*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 55*x-252*y
    let v := 55*y-12*x
    have hu : u+252*y=55*x := Nat.sub_add_cancel ax
    have hv : v+12*x=55*y := Nat.sub_add_cancel ay
    have ev : u^2+20=21*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid21_1_3 {k : ℕ} (_hk : k<2097152) : ¬3^1∣(orbit 21 (55,12) (1,1) k).2 := by
  have h0 : Good 21 3 1 (55,12) (1,1) [] :=
    lift (t:=1) (s:=1) (good_one 21 (55,12) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid21_1_7 {k : ℕ} (hk : k<2097152) : ¬7^8∣(orbit 21 (55,12) (1,1) k).2 := by
  have h0 : Good 21 7 14 (55,12) (1,1) [3, 10] :=
    lift (t:=1) (s:=14) (good_one 21 (55,12) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 21 49 98 (55,12) (1,1) [10, 59] :=
    lift (t:=14) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 21 343 686 (55,12) (1,1) [59, 402] :=
    lift (t:=98) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 21 2401 4802 (55,12) (1,1) [745, 3146] :=
    lift (t:=686) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 21 16807 33614 (55,12) (1,1) [10349, 27156] :=
    lift (t:=4802) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 21 117649 235298 (55,12) (1,1) [111191, 228840] :=
    lift (t:=33614) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 21 823543 1647086 (55,12) (1,1) [228840, 1052383] :=
    lift (t:=235298) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 21 5764801 11529602 (55,12) (1,1) [4346555, 10111356] :=
    lift (t:=1647086) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h7 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid21_1_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 21 (55,12) (1,1) k).2 := by
  have h0 : Good 21 29 5 (55,12) (1,1) [] :=
    lift (t:=1) (s:=5) (good_one 21 (55,12) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid21_8_3 {k : ℕ} (_hk : k<2097152) : ¬3^1∣(orbit 21 (55,12) (8,2) k).2 := by
  have h0 : Good 21 3 1 (55,12) (8,2) [] :=
    lift (t:=1) (s:=1) (good_one 21 (55,12) (8,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid21_8_7 {k : ℕ} (hk : k<2097152) : ¬7^8∣(orbit 21 (55,12) (8,2) k).2 := by
  have h0 : Good 21 7 14 (55,12) (8,2) [6, 13] :=
    lift (t:=1) (s:=14) (good_one 21 (55,12) (8,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 21 49 98 (55,12) (8,2) [6, 55] :=
    lift (t:=14) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 21 343 686 (55,12) (8,2) [55, 398] :=
    lift (t:=98) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 21 2401 4802 (55,12) (8,2) [55, 2456] :=
    lift (t:=686) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 21 16807 33614 (55,12) (8,2) [12060, 28867] :=
    lift (t:=4802) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 21 117649 235298 (55,12) (8,2) [45674, 163323] :=
    lift (t:=33614) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 21 823543 1647086 (55,12) (8,2) [45674, 869217] :=
    lift (t:=235298) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 21 5764801 11529602 (55,12) (8,2) [3339846, 9104647] :=
    lift (t:=1647086) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h7 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid21_8_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 21 (55,12) (8,2) k).2 := by
  have h0 : Good 21 29 5 (55,12) (8,2) [] :=
    lift (t:=1) (s:=5) (good_one 21 (55,12) (8,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid21_13_3 {k : ℕ} (hk : k<2097152) : ¬3^16∣(orbit 21 (55,12) (13,3) k).2 := by
  have h0 : Good 21 3 1 (55,12) (13,3) [0] :=
    lift (t:=1) (s:=1) (good_one 21 (55,12) (13,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 21 9 3 (55,12) (13,3) [2] :=
    lift (t:=1) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 21 27 9 (55,12) (13,3) [5] :=
    lift (t:=3) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 21 81 27 (55,12) (13,3) [14] :=
    lift (t:=9) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 21 243 81 (55,12) (13,3) [68] :=
    lift (t:=27) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 21 729 243 (55,12) (13,3) [149] :=
    lift (t:=81) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 21 2187 729 (55,12) (13,3) [149] :=
    lift (t:=243) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 21 6561 2187 (55,12) (13,3) [149] :=
    lift (t:=729) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 21 19683 6561 (55,12) (13,3) [149] :=
    lift (t:=2187) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 21 59049 19683 (55,12) (13,3) [6710] :=
    lift (t:=6561) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 21 177147 59049 (55,12) (13,3) [46076] :=
    lift (t:=19683) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 21 531441 177147 (55,12) (13,3) [105125] :=
    lift (t:=59049) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 21 1594323 531441 (55,12) (13,3) [105125] :=
    lift (t:=177147) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 21 4782969 1594323 (55,12) (13,3) [105125] :=
    lift (t:=531441) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 21 14348907 4782969 (55,12) (13,3) [1699448] :=
    lift (t:=1594323) (s:=3) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h15 : Good 21 43046721 14348907 (55,12) (13,3) [11265386] :=
    lift (t:=4782969) (s:=3) (h14) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h15 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid21_13_7 {k : ℕ} (hk : k<2097152) : ¬7^9∣(orbit 21 (55,12) (13,3) k).2 := by
  have h0 : Good 21 7 14 (55,12) (13,3) [5, 12] :=
    lift (t:=1) (s:=14) (good_one 21 (55,12) (13,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 21 49 98 (55,12) (13,3) [26, 75] :=
    lift (t:=14) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 21 343 686 (55,12) (13,3) [173, 516] :=
    lift (t:=98) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 21 2401 4802 (55,12) (13,3) [1545, 3946] :=
    lift (t:=686) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 21 16807 33614 (55,12) (13,3) [15951, 32758] :=
    lift (t:=4802) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 21 117649 235298 (55,12) (13,3) [32758, 150407] :=
    lift (t:=33614) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 21 823543 1647086 (55,12) (13,3) [503354, 1326897] :=
    lift (t:=235298) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 21 5764801 11529602 (55,12) (13,3) [503354, 6268155] :=
    lift (t:=1647086) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 21 40353607 80707214 (55,12) (13,3) [6268155, 46621762] :=
    lift (t:=11529602) (s:=7) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h8 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid21_13_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 21 (55,12) (13,3) k).2 := by
  have h0 : Good 21 29 5 (55,12) (13,3) [] :=
    lift (t:=1) (s:=5) (good_one 21 (55,12) (13,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid21_41_3 {k : ℕ} (hk : k<2097152) : ¬3^15∣(orbit 21 (55,12) (41,9) k).2 := by
  have h0 : Good 21 3 1 (55,12) (41,9) [0] :=
    lift (t:=1) (s:=1) (good_one 21 (55,12) (41,9)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 21 9 3 (55,12) (41,9) [0] :=
    lift (t:=1) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 21 27 9 (55,12) (41,9) [3] :=
    lift (t:=3) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 21 81 27 (55,12) (41,9) [12] :=
    lift (t:=9) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 21 243 81 (55,12) (41,9) [12] :=
    lift (t:=27) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 21 729 243 (55,12) (41,9) [93] :=
    lift (t:=81) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 21 2187 729 (55,12) (41,9) [579] :=
    lift (t:=243) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 21 6561 2187 (55,12) (41,9) [2037] :=
    lift (t:=729) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 21 19683 6561 (55,12) (41,9) [6411] :=
    lift (t:=2187) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 21 59049 19683 (55,12) (41,9) [12972] :=
    lift (t:=6561) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 21 177147 59049 (55,12) (41,9) [12972] :=
    lift (t:=19683) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 21 531441 177147 (55,12) (41,9) [72021] :=
    lift (t:=59049) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 21 1594323 531441 (55,12) (41,9) [426315] :=
    lift (t:=177147) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 21 4782969 1594323 (55,12) (41,9) [1489197] :=
    lift (t:=531441) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 21 14348907 4782969 (55,12) (41,9) [3083520] :=
    lift (t:=1594323) (s:=3) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h14 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid21_41_7 {k : ℕ} (hk : k<2097152) : ¬7^8∣(orbit 21 (55,12) (41,9) k).2 := by
  have h0 : Good 21 7 14 (55,12) (41,9) [1, 8] :=
    lift (t:=1) (s:=14) (good_one 21 (55,12) (41,9)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 21 49 98 (55,12) (41,9) [22, 71] :=
    lift (t:=14) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 21 343 686 (55,12) (41,9) [169, 512] :=
    lift (t:=98) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 21 2401 4802 (55,12) (41,9) [855, 3256] :=
    lift (t:=686) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 21 16807 33614 (55,12) (41,9) [855, 17662] :=
    lift (t:=4802) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 21 117649 235298 (55,12) (41,9) [84890, 202539] :=
    lift (t:=33614) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 21 823543 1647086 (55,12) (41,9) [320188, 1143731] :=
    lift (t:=235298) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 21 5764801 11529602 (55,12) (41,9) [5261446, 11026247] :=
    lift (t:=1647086) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h7 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid21_41_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 21 (55,12) (41,9) k).2 := by
  have h0 : Good 21 29 5 (55,12) (41,9) [] :=
    lift (t:=1) (s:=5) (good_one 21 (55,12) (41,9)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid21_64_3 {k : ℕ} (_hk : k<2097152) : ¬3^1∣(orbit 21 (55,12) (64,14) k).2 := by
  have h0 : Good 21 3 1 (55,12) (64,14) [] :=
    lift (t:=1) (s:=1) (good_one 21 (55,12) (64,14)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid21_64_7 {k : ℕ} (hk : k<2097152) : ¬7^8∣(orbit 21 (55,12) (64,14) k).2 := by
  have h0 : Good 21 7 14 (55,12) (64,14) [0, 7] :=
    lift (t:=1) (s:=14) (good_one 21 (55,12) (64,14)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 21 49 98 (55,12) (64,14) [42, 91] :=
    lift (t:=14) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 21 343 686 (55,12) (64,14) [287, 630] :=
    lift (t:=98) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 21 2401 4802 (55,12) (64,14) [2345, 4746] :=
    lift (t:=686) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 21 16807 33614 (55,12) (64,14) [4746, 21553] :=
    lift (t:=4802) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 21 117649 235298 (55,12) (64,14) [71974, 189623] :=
    lift (t:=33614) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 21 823543 1647086 (55,12) (64,14) [777868, 1601411] :=
    lift (t:=235298) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 21 5764801 11529602 (55,12) (64,14) [2424954, 8189755] :=
    lift (t:=1647086) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h7 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid21_64_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 21 (55,12) (64,14) k).2 := by
  have h0 : Good 21 29 5 (55,12) (64,14) [] :=
    lift (t:=1) (s:=5) (good_one 21 (55,12) (64,14)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid21_197_3 {k : ℕ} (_hk : k<2097152) : ¬3^1∣(orbit 21 (55,12) (197,43) k).2 := by
  have h0 : Good 21 3 1 (55,12) (197,43) [] :=
    lift (t:=1) (s:=1) (good_one 21 (55,12) (197,43)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid21_197_7 {k : ℕ} (hk : k<2097152) : ¬7^9∣(orbit 21 (55,12) (197,43) k).2 := by
  have h0 : Good 21 7 14 (55,12) (197,43) [3, 10] :=
    lift (t:=1) (s:=14) (good_one 21 (55,12) (197,43)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 21 49 98 (55,12) (197,43) [38, 87] :=
    lift (t:=14) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 21 343 686 (55,12) (197,43) [283, 626] :=
    lift (t:=98) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 21 2401 4802 (55,12) (197,43) [1655, 4056] :=
    lift (t:=686) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 21 16807 33614 (55,12) (197,43) [6457, 23264] :=
    lift (t:=4802) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 21 117649 235298 (55,12) (197,43) [6457, 124106] :=
    lift (t:=33614) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 21 823543 1647086 (55,12) (197,43) [594702, 1418245] :=
    lift (t:=235298) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 21 5764801 11529602 (55,12) (197,43) [1418245, 7183046] :=
    lift (t:=1647086) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 21 40353607 80707214 (55,12) (197,43) [7183046, 47536653] :=
    lift (t:=11529602) (s:=7) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h8 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid21_197_29 {k : ℕ} (_hk : k<2097152) : ¬29^1∣(orbit 21 (55,12) (197,43) k).2 := by
  have h0 : Good 21 29 5 (55,12) (197,43) [] :=
    lift (t:=1) (s:=5) (good_one 21 (55,12) (197,43)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth21 {x y : ℕ} (eqn : x^2+20=21*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣609) : x≤41 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent21 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣609^16 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 610, i.val.Prime → i.val∣609 → i.val=3 ∨ i.val=7 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=3 ∨ p=7 ∨ p=29 at tags
    have horb : p^(16+1)∣(orbit 21 (55,12) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_1_3 low ((pow_dvd_pow 3 (by decide : 1≤16+1)).trans horb)
      · exact avoid21_1_7 low ((pow_dvd_pow 7 (by decide : 8≤16+1)).trans horb)
      · exact avoid21_1_29 low ((pow_dvd_pow 29 (by decide : 1≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_8_3 low ((pow_dvd_pow 3 (by decide : 1≤16+1)).trans horb)
      · exact avoid21_8_7 low ((pow_dvd_pow 7 (by decide : 8≤16+1)).trans horb)
      · exact avoid21_8_29 low ((pow_dvd_pow 29 (by decide : 1≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_13_3 low ((pow_dvd_pow 3 (by decide : 16≤16+1)).trans horb)
      · exact avoid21_13_7 low ((pow_dvd_pow 7 (by decide : 9≤16+1)).trans horb)
      · exact avoid21_13_29 low ((pow_dvd_pow 29 (by decide : 1≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_41_3 low ((pow_dvd_pow 3 (by decide : 15≤16+1)).trans horb)
      · exact avoid21_41_7 low ((pow_dvd_pow 7 (by decide : 8≤16+1)).trans horb)
      · exact avoid21_41_29 low ((pow_dvd_pow 29 (by decide : 1≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_64_3 low ((pow_dvd_pow 3 (by decide : 1≤16+1)).trans horb)
      · exact avoid21_64_7 low ((pow_dvd_pow 7 (by decide : 8≤16+1)).trans horb)
      · exact avoid21_64_29 low ((pow_dvd_pow 29 (by decide : 1≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_197_3 low ((pow_dvd_pow 3 (by decide : 1≤16+1)).trans horb)
      · exact avoid21_197_7 low ((pow_dvd_pow 7 (by decide : 9≤16+1)).trans horb)
      · exact avoid21_197_29 low ((pow_dvd_pow 29 (by decide : 1≤16+1)).trans horb)
  have limK : k<149 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<609^16) dv
    have : 609^16<2^149 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(8,2),(13,3),(41,9),(64,14),(197,43)] : List (ℕ×ℕ)), ∀ i : Fin 149,
      (orbit 21 (55,12) s i.val).2∣609^16 → (orbit 21 (55,12) s i.val).1≤41 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent23 {x y : ℕ} (eqn : x^2+22=23*y^2) :
    ∃ s ∈ ([(1,1),(91,19)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 23 (24,5) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<24
    · have hx : x<111 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤23 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 111, ∀ j : Fin 24, i.val^2+22=23*j.val^2 →
          (i.val,j.val)∈([(1,1),(91,19)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 24^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 115*y≤24*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 5*x≤24*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 23*y<5*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 24*x-115*y
    let v := 24*y-5*x
    have hu : u+115*y=24*x := Nat.sub_add_cancel ax
    have hv : v+5*x=24*y := Nat.sub_add_cancel ay
    have ev : u^2+22=23*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid23_1_23 {k : ℕ} (hk : k<2097152) : ¬23^5∣(orbit 23 (24,5) (1,1) k).2 := by
  have h0 : Good 23 23 23 (24,5) (1,1) [9] :=
    lift (t:=1) (s:=23) (good_one 23 (24,5) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 23 529 529 (24,5) (1,1) [32] :=
    lift (t:=23) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 23 12167 12167 (24,5) (1,1) [561] :=
    lift (t:=529) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 23 279841 279841 (24,5) (1,1) [12728] :=
    lift (t:=12167) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 23 6436343 6436343 (24,5) (1,1) [3090979] :=
    lift (t:=279841) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid23_1_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 23 (24,5) (1,1) k).2 := by
  have h0 : Good 23 29 28 (24,5) (1,1) [1, 15] :=
    lift (t:=1) (s:=28) (good_one 23 (24,5) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 23 841 812 (24,5) (1,1) [253, 659] :=
    lift (t:=28) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 23 24389 23548 (24,5) (1,1) [4719, 16493] :=
    lift (t:=812) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 23 707281 682892 (24,5) (1,1) [193103, 534549] :=
    lift (t:=23548) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 23 20511149 19803868 (24,5) (1,1) [6680577, 16582511] :=
    lift (t:=682892) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid23_91_23 {k : ℕ} (hk : k<2097152) : ¬23^5∣(orbit 23 (24,5) (91,19) k).2 := by
  have h0 : Good 23 23 23 (24,5) (91,19) [13] :=
    lift (t:=1) (s:=23) (good_one 23 (24,5) (91,19)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 23 529 529 (24,5) (91,19) [496] :=
    lift (t:=23) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 23 12167 12167 (24,5) (91,19) [11605] :=
    lift (t:=529) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 23 279841 279841 (24,5) (91,19) [267112] :=
    lift (t:=12167) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 23 6436343 6436343 (24,5) (91,19) [3345363] :=
    lift (t:=279841) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid23_91_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 23 (24,5) (91,19) k).2 := by
  have h0 : Good 23 29 28 (24,5) (91,19) [12, 26] :=
    lift (t:=1) (s:=28) (good_one 23 (24,5) (91,19)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 23 841 812 (24,5) (91,19) [152, 558] :=
    lift (t:=28) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 23 24389 23548 (24,5) (91,19) [7054, 18828] :=
    lift (t:=812) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 23 707281 682892 (24,5) (91,19) [148342, 489788] :=
    lift (t:=23548) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 23 20511149 19803868 (24,5) (91,19) [3221356, 13123290] :=
    lift (t:=682892) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth23 {x y : ℕ} (eqn : x^2+22=23*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣667) : x≤139 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent23 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣667^5 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 668, i.val.Prime → i.val∣667 → i.val=23 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=23 ∨ p=29 at tags
    have horb : p^(5+1)∣(orbit 23 (24,5) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid23_1_23 low ((pow_dvd_pow 23 (by decide : 5≤5+1)).trans horb)
      · exact avoid23_1_29 low ((pow_dvd_pow 29 (by decide : 5≤5+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid23_91_23 low ((pow_dvd_pow 23 (by decide : 5≤5+1)).trans horb)
      · exact avoid23_91_29 low ((pow_dvd_pow 29 (by decide : 5≤5+1)).trans horb)
  have limK : k<47 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<667^5) dv
    have : 667^5<2^47 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(91,19)] : List (ℕ×ℕ)), ∀ i : Fin 47,
      (orbit 23 (24,5) s i.val).2∣667^5 → (orbit 23 (24,5) s i.val).1≤139 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent24 {x y : ℕ} (eqn : x^2+23=6*y^2) :
    ∃ s ∈ ([(1,2),(19,8)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 6 (5,2) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<10
    · have hx : x<23 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤9 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 23, ∀ j : Fin 10, i.val^2+23=6*j.val^2 →
          (i.val,j.val)∈([(1,2),(19,8)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 10^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 12*y≤5*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 2*x≤5*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 4*y<2*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 5*x-12*y
    let v := 5*y-2*x
    have hu : u+12*y=5*x := Nat.sub_add_cancel ax
    have hv : v+2*x=5*y := Nat.sub_add_cancel ay
    have ev : u^2+23=6*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid24_1_2 {k : ℕ} (hk : k<2097152) : ¬2^24∣(orbit 6 (5,2) (1,2) k).2 := by
  have h0 : Good 6 2 1 (5,2) (1,2) [0] :=
    lift (t:=1) (s:=1) (good_one 6 (5,2) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 4 2 (5,2) (1,2) [1] :=
    lift (t:=1) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 6 8 4 (5,2) (1,2) [3] :=
    lift (t:=2) (s:=2) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 6 16 8 (5,2) (1,2) [3] :=
    lift (t:=4) (s:=2) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 6 32 16 (5,2) (1,2) [11] :=
    lift (t:=8) (s:=2) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 6 64 32 (5,2) (1,2) [27] :=
    lift (t:=16) (s:=2) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 6 128 64 (5,2) (1,2) [59] :=
    lift (t:=32) (s:=2) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 6 256 128 (5,2) (1,2) [59] :=
    lift (t:=64) (s:=2) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 6 512 256 (5,2) (1,2) [59] :=
    lift (t:=128) (s:=2) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 6 1024 512 (5,2) (1,2) [59] :=
    lift (t:=256) (s:=2) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 6 2048 1024 (5,2) (1,2) [59] :=
    lift (t:=512) (s:=2) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 6 4096 2048 (5,2) (1,2) [59] :=
    lift (t:=1024) (s:=2) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 6 8192 4096 (5,2) (1,2) [2107] :=
    lift (t:=2048) (s:=2) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 6 16384 8192 (5,2) (1,2) [6203] :=
    lift (t:=4096) (s:=2) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 6 32768 16384 (5,2) (1,2) [14395] :=
    lift (t:=8192) (s:=2) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h15 : Good 6 65536 32768 (5,2) (1,2) [14395] :=
    lift (t:=16384) (s:=2) (h14) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h16 : Good 6 131072 65536 (5,2) (1,2) [47163] :=
    lift (t:=32768) (s:=2) (h15) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h17 : Good 6 262144 131072 (5,2) (1,2) [47163] :=
    lift (t:=65536) (s:=2) (h16) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h18 : Good 6 524288 262144 (5,2) (1,2) [178235] :=
    lift (t:=131072) (s:=2) (h17) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h19 : Good 6 1048576 524288 (5,2) (1,2) [178235] :=
    lift (t:=262144) (s:=2) (h18) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h20 : Good 6 2097152 1048576 (5,2) (1,2) [702523] :=
    lift (t:=524288) (s:=2) (h19) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h21 : Good 6 4194304 2097152 (5,2) (1,2) [702523] :=
    lift (t:=1048576) (s:=2) (h20) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h22 : Good 6 8388608 4194304 (5,2) (1,2) [702523] :=
    lift (t:=2097152) (s:=2) (h21) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h23 : Good 6 16777216 8388608 (5,2) (1,2) [4896827] :=
    lift (t:=4194304) (s:=2) (h22) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h23 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid24_1_3 {k : ℕ} (_hk : k<2097152) : ¬3^2∣(orbit 6 (5,2) (1,2) k).2 := by
  have h0 : Good 6 3 6 (5,2) (1,2) [1, 4] :=
    lift (t:=1) (s:=6) (good_one 6 (5,2) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 9 6 (5,2) (1,2) [] :=
    lift (t:=6) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid24_1_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 6 (5,2) (1,2) k).2 := by
  have h0 : Good 6 29 28 (5,2) (1,2) [8, 22] :=
    lift (t:=1) (s:=28) (good_one 6 (5,2) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 841 812 (5,2) (1,2) [316, 722] :=
    lift (t:=28) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 6 24389 23548 (5,2) (1,2) [6812, 18586] :=
    lift (t:=812) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 6 707281 682892 (5,2) (1,2) [242292, 583738] :=
    lift (t:=23548) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 6 20511149 19803868 (5,2) (1,2) [2973860, 12875794] :=
    lift (t:=682892) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid24_19_2 {k : ℕ} (hk : k<2097152) : ¬2^23∣(orbit 6 (5,2) (19,8) k).2 := by
  have h0 : Good 6 2 1 (5,2) (19,8) [0] :=
    lift (t:=1) (s:=1) (good_one 6 (5,2) (19,8)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 4 2 (5,2) (19,8) [0] :=
    lift (t:=1) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 6 8 4 (5,2) (19,8) [0] :=
    lift (t:=2) (s:=2) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 6 16 8 (5,2) (19,8) [4] :=
    lift (t:=4) (s:=2) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 6 32 16 (5,2) (19,8) [4] :=
    lift (t:=8) (s:=2) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 6 64 32 (5,2) (19,8) [4] :=
    lift (t:=16) (s:=2) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 6 128 64 (5,2) (19,8) [4] :=
    lift (t:=32) (s:=2) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 6 256 128 (5,2) (19,8) [68] :=
    lift (t:=64) (s:=2) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 6 512 256 (5,2) (19,8) [196] :=
    lift (t:=128) (s:=2) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 6 1024 512 (5,2) (19,8) [452] :=
    lift (t:=256) (s:=2) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 6 2048 1024 (5,2) (19,8) [964] :=
    lift (t:=512) (s:=2) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 6 4096 2048 (5,2) (19,8) [1988] :=
    lift (t:=1024) (s:=2) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 6 8192 4096 (5,2) (19,8) [1988] :=
    lift (t:=2048) (s:=2) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 6 16384 8192 (5,2) (19,8) [1988] :=
    lift (t:=4096) (s:=2) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 6 32768 16384 (5,2) (19,8) [1988] :=
    lift (t:=8192) (s:=2) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h15 : Good 6 65536 32768 (5,2) (19,8) [18372] :=
    lift (t:=16384) (s:=2) (h14) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h16 : Good 6 131072 65536 (5,2) (19,8) [18372] :=
    lift (t:=32768) (s:=2) (h15) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h17 : Good 6 262144 131072 (5,2) (19,8) [83908] :=
    lift (t:=65536) (s:=2) (h16) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h18 : Good 6 524288 262144 (5,2) (19,8) [83908] :=
    lift (t:=131072) (s:=2) (h17) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h19 : Good 6 1048576 524288 (5,2) (19,8) [346052] :=
    lift (t:=262144) (s:=2) (h18) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h20 : Good 6 2097152 1048576 (5,2) (19,8) [346052] :=
    lift (t:=524288) (s:=2) (h19) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h21 : Good 6 4194304 2097152 (5,2) (19,8) [1394628] :=
    lift (t:=1048576) (s:=2) (h20) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h22 : Good 6 8388608 4194304 (5,2) (19,8) [3491780] :=
    lift (t:=2097152) (s:=2) (h21) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h22 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid24_19_3 {k : ℕ} (_hk : k<2097152) : ¬3^2∣(orbit 6 (5,2) (19,8) k).2 := by
  have h0 : Good 6 3 6 (5,2) (19,8) [1, 4] :=
    lift (t:=1) (s:=6) (good_one 6 (5,2) (19,8)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 9 6 (5,2) (19,8) [] :=
    lift (t:=6) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid24_19_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 6 (5,2) (19,8) k).2 := by
  have h0 : Good 6 29 28 (5,2) (19,8) [5, 19] :=
    lift (t:=1) (s:=28) (good_one 6 (5,2) (19,8)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 841 812 (5,2) (19,8) [89, 495] :=
    lift (t:=28) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 6 24389 23548 (5,2) (19,8) [4961, 16735] :=
    lift (t:=812) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 6 707281 682892 (5,2) (19,8) [99153, 440599] :=
    lift (t:=23548) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 6 20511149 19803868 (5,2) (19,8) [6928073, 16830007] :=
    lift (t:=682892) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth24 {x y : ℕ} (eqn : x^2+23=6*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣174) : x≤29 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent24 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣174^24 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 175, i.val.Prime → i.val∣174 → i.val=2 ∨ i.val=3 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=3 ∨ p=29 at tags
    have horb : p^(24+1)∣(orbit 6 (5,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid24_1_2 low ((pow_dvd_pow 2 (by decide : 24≤24+1)).trans horb)
      · exact avoid24_1_3 low ((pow_dvd_pow 3 (by decide : 2≤24+1)).trans horb)
      · exact avoid24_1_29 low ((pow_dvd_pow 29 (by decide : 5≤24+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid24_19_2 low ((pow_dvd_pow 2 (by decide : 23≤24+1)).trans horb)
      · exact avoid24_19_3 low ((pow_dvd_pow 3 (by decide : 2≤24+1)).trans horb)
      · exact avoid24_19_29 low ((pow_dvd_pow 29 (by decide : 5≤24+1)).trans horb)
  have limK : k<179 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<174^24) dv
    have : 174^24<2^179 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(19,8)] : List (ℕ×ℕ)), ∀ i : Fin 179,
      (orbit 6 (5,2) s i.val).2∣174^24 → (orbit 6 (5,2) s i.val).1≤29 := by decide +kernel
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
private theorem avoid26_1_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 26 (51,10) (1,1) k).2 := by
  have h0 : Good 26 29 30 (51,10) (1,1) [5, 20] :=
    lift (t:=1) (s:=30) (good_one 26 (51,10) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 26 841 870 (51,10) (1,1) [155, 590] :=
    lift (t:=30) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 26 24389 25230 (51,10) (1,1) [9725, 22340] :=
    lift (t:=870) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 26 707281 731670 (51,10) (1,1) [312485, 678320] :=
    lift (t:=25230) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 26 20511149 21218430 (51,10) (1,1) [2141660, 12750875] :=
    lift (t:=731670) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid26_25_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 26 (51,10) (25,5) k).2 := by
  have h0 : Good 26 29 30 (51,10) (25,5) [7, 22] :=
    lift (t:=1) (s:=30) (good_one 26 (51,10) (25,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 26 841 870 (51,10) (25,5) [217, 652] :=
    lift (t:=30) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 26 24389 25230 (51,10) (25,5) [6307, 18922] :=
    lift (t:=870) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 26 707281 731670 (51,10) (25,5) [182917, 548752] :=
    lift (t:=25230) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 26 20511149 21218430 (51,10) (25,5) [5304607, 15913822] :=
    lift (t:=731670) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid26_209_29 {k : ℕ} (hk : k<2097152) : ¬29^5∣(orbit 26 (51,10) (209,41) k).2 := by
  have h0 : Good 26 29 30 (51,10) (209,41) [9, 24] :=
    lift (t:=1) (s:=30) (good_one 26 (51,10) (209,41)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 26 841 870 (51,10) (209,41) [279, 714] :=
    lift (t:=30) (s:=29) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 26 24389 25230 (51,10) (209,41) [2889, 15504] :=
    lift (t:=870) (s:=29) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 26 707281 731670 (51,10) (209,41) [53349, 419184] :=
    lift (t:=25230) (s:=29) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 26 20511149 21218430 (51,10) (209,41) [8467554, 19076769] :=
    lift (t:=731670) (s:=29) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth26 {x y : ℕ} (eqn : x^2+25=26*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣754) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent26 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣754^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 755, i.val.Prime → i.val∣754 → i.val=2 ∨ i.val=13 ∨ i.val=29 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=13 ∨ p=29 at tags
    have horb : p^(7+1)∣(orbit 26 (51,10) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid26_1_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid26_1_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid26_1_29 low ((pow_dvd_pow 29 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid26_25_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid26_25_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid26_25_29 low ((pow_dvd_pow 29 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid26_209_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid26_209_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid26_209_29 low ((pow_dvd_pow 29 (by decide : 5≤7+1)).trans horb)
  have limK : k<67 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<754^7) dv
    have : 754^7<2^67 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(25,5),(209,41)] : List (ℕ×ℕ)), ∀ i : Fin 67,
      (orbit 26 (51,10) s i.val).2∣754^7 → (orbit 26 (51,10) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


end Erdos889.SquareTwentyNine


namespace Erdos889.SquareTwentyNine
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem extract {n j R : ℕ} (div : 892371480∣n) (hj : 0<j) (lj : j≤28)
    (rad : ∀ p : Fin 29, p.val.Prime → p.val∣j → p.val∣R) (large : 29∣R)
    (pos : R≠0) (hit : 29∣n+j) (sol : v_l 1 n=1) :
    ∃ D y : ℕ, D∣R ∧ D*y^2=n+j ∧ (∀ p : ℕ, p.Prime → p∣y → p∣R) := by
  have sup (p : ℕ) (pp : p.Prime) (hd : p∣n+j) : p∣R := by
    by_cases small : p≤j
    · have t : ∀ t : Fin 29, t.val.Prime → t.val∣892371480 := by decide
      have dp := (t ⟨p,by omega⟩ pp).trans div
      exact rad ⟨p,by omega⟩ pp ((Nat.dvd_add_iff_right dp).mpr hd)
    · by_cases same : p=29
      · exact same ▸ large
      exact False.elim (two_primes hj pp (by decide : Nat.Prime 29) same (by omega) (by omega) hd hit sol)
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
    (shape : n+1=p^2) (one : 2≤D) (small : j≤28) (big : 100<p) :
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

private theorem reject2 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+2) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=58) div (by decide : 0<2) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=2 := coefficient (m:=12) fac dr (by decide) (by decide)
    ((by decide : 12∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+1=2*y^2 := by omega
  have h := smooth2 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject5 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+5) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=145) div (by decide : 0<5) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=5 := coefficient (m:=21) fac dr (by decide) (by decide)
    ((by decide : 21∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+4=5*y^2 := by omega
  have h := smooth5 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject6 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+6) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=174) div (by decide : 0<6) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=6 := coefficient (m:=88) fac dr (by decide) (by decide)
    ((by decide : 88∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+5=6*y^2 := by omega
  have h := smooth6 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject7 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+7) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=203) div (by decide : 0<7) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=7 := coefficient (m:=8) fac dr (by decide) (by decide)
    ((by decide : 8∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+6=7*y^2 := by omega
  have h := smooth7 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject8 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+8) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=58) div (by decide : 0<8) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=2 := coefficient (m:=15) fac dr (by decide) (by decide)
    ((by decide : 15∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+7=2*y^2 := by omega
  have h := smooth8 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject10 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+10) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=290) div (by decide : 0<10) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=10 := coefficient (m:=84) fac dr (by decide) (by decide)
    ((by decide : 84∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+9=10*y^2 := by omega
  have h := smooth10 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject14 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+14) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=406) div (by decide : 0<14) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=14 := coefficient (m:=24) fac dr (by decide) (by decide)
    ((by decide : 24∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+13=14*y^2 := by omega
  have h := smooth14 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject17 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+17) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=493) div (by decide : 0<17) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=17 := coefficient (m:=15) fac dr (by decide) (by decide)
    ((by decide : 15∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+16=17*y^2 := by omega
  have h := smooth17 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject21 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+21) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=609) div (by decide : 0<21) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=21 := coefficient (m:=104) fac dr (by decide) (by decide)
    ((by decide : 104∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+20=21*y^2 := by omega
  have h := smooth21 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject23 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+23) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=667) div (by decide : 0<23) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=23 := coefficient (m:=8) fac dr (by decide) (by decide)
    ((by decide : 8∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+22=23*y^2 := by omega
  have h := smooth23 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject24 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+24) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=174) div (by decide : 0<24) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=6 := coefficient (m:=385) fac dr (by decide) (by decide)
    ((by decide : 385∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+23=6*y^2 := by omega
  have h := smooth24 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject25 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+25) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=145) div (by decide : 0<25) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (m:=21) fac dr (by decide) (by decide)
    ((by decide : 21∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : y^2=p^2+24 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

private theorem reject26 {n p : ℕ} (big : 1000<p) (div : 892371480∣n) (shape : n+1=p^2)
    (hit : 29∣n+26) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=754) div (by decide : 0<26) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=26 := coefficient (m:=60) fac dr (by decide) (by decide)
    ((by decide : 60∣892371480).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+25=26*y^2 := by omega
  have h := smooth26 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxHeartbeats 2000000 in
/-- Any further solution with a prime-square successor is divisible by every prime through 29. -/
theorem square_multiple_of_25878772920 {n p : ℕ} (big : 330<n) (pp : p.Prime)
    (shape : n+1=p^2) (sol : v_l 1 n=1) : 25878772920∣n := by
  have div := Erdos889.SquareTwentyThree.square_multiple_of_892371480 big pp shape sol
  have huge := (Erdos889.MissingPrimeSieve.further_solution_bounds_thirty big sol).1
  have large : 1000<p := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have nz : ¬29∣p := by
    intro dvd
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 29) pp).mp dvd
    omega
  have twentyNine : 29∣n := by
    by_contra miss
    have alts : 29∣n+2 ∨ 29∣n+5 ∨ 29∣n+6 ∨ 29∣n+7 ∨ 29∣n+8 ∨ 29∣n+10 ∨ 29∣n+14 ∨ 29∣n+17 ∨ 29∣n+21 ∨ 29∣n+23 ∨ 29∣n+24 ∨ 29∣n+25 ∨ 29∣n+26 := by
      have table : ∀ a b : Fin 29, (a.val+1)%29=(b.val^2)%29 →
          a.val≠0 → b.val≠0 → 29∣a.val+2 ∨ 29∣a.val+5 ∨ 29∣a.val+6 ∨ 29∣a.val+7 ∨ 29∣a.val+8 ∨ 29∣a.val+10 ∨ 29∣a.val+14 ∨ 29∣a.val+17 ∨ 29∣a.val+21 ∨ 29∣a.val+23 ∨ 29∣a.val+24 ∨ 29∣a.val+25 ∨ 29∣a.val+26 := by decide +kernel
      have localProof := table ⟨n%29,Nat.mod_lt _ (by decide)⟩ ⟨p%29,Nat.mod_lt _ (by decide)⟩
        (by dsimp; rw [Nat.mod_add_mod,shape,Nat.pow_mod p 2 29])
        (fun h => miss (Nat.dvd_of_mod_eq_zero h)) (fun h => nz (Nat.dvd_of_mod_eq_zero h))
      simpa only [Nat.dvd_iff_mod_eq_zero,Nat.mod_add_mod] using localProof
    rcases alts with h|h|h|h|h|h|h|h|h|h|h|h|h
    · exact reject2 large div shape h sol
    · exact reject5 large div shape h sol
    · exact reject6 large div shape h sol
    · exact reject7 large div shape h sol
    · exact reject8 large div shape h sol
    · exact reject10 large div shape h sol
    · exact reject14 large div shape h sol
    · exact reject17 large div shape h sol
    · exact reject21 large div shape h sol
    · exact reject23 large div shape h sol
    · exact reject24 large div shape h sol
    · exact reject25 large div shape h sol
    · exact reject26 large div shape h sol
  omega

theorem prime_square_outside_25878772920 {n p : ℕ} (pp : p.Prime) (shape : n+1=p^2)
    (miss : ¬25878772920∣n) : v_l 1 n=1 ↔ n∈[3,8,24,48,120] := by
  by_cases large : 330<n
  · constructor
    · intro sol
      exact (miss (square_multiple_of_25878772920 large pp shape sol)).elim
    · intro mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      omega
  · apply Erdos889.SquareTwentyThree.prime_square_outside_892371480 pp shape
    have := Nat.pow_le_pow_left pp.two_le 2
    omega
end Erdos889.SquareTwentyNine

#print axioms Erdos889.SquareTwentyNine.prime_square_outside_25878772920
