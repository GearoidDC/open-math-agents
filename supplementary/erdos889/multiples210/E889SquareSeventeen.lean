import E889SquareThirteen
/-! The next missing prime for square successors. -/
namespace Erdos889.SquareSeventeen

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
private theorem avoid2_1_17 {k : ℕ} (_hk : k<2097152) : ¬17^1∣(orbit 2 (3,2) (1,1) k).2 := by
  have h0 : Good 2 17 8 (3,2) (1,1) [] :=
    lift (t:=1) (s:=8) (good_one 2 (3,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth2 {x y : ℕ} (eqn : x^2+1=2*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣34) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent2 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣34^1 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 35, i.val.Prime → i.val∣34 → i.val=2 ∨ i.val=17 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=17 at tags
    have horb : p^(1+1)∣(orbit 2 (3,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    subst s
    rcases tags with rfl|rfl
    · exact avoid2_1_2 low ((pow_dvd_pow 2 (by decide : 1≤1+1)).trans horb)
    · exact avoid2_1_17 low ((pow_dvd_pow 17 (by decide : 1≤1+1)).trans horb)
  have limK : k<6 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<34^1) dv
    have : 34^1<2^6 := by decide
    omega
  have small : ∀ s ∈ ([(1,1)] : List (ℕ×ℕ)), ∀ i : Fin 6,
      (orbit 2 (3,2) s i.val).2∣34^1 → (orbit 2 (3,2) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent3 {x y : ℕ} (eqn : x^2+2=3*y^2) :
    ∃ s ∈ ([(1,1)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 3 (2,1) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<2
    · have hx : x<2 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤1 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 2, ∀ j : Fin 2, i.val^2+2=3*j.val^2 →
          (i.val,j.val)∈([(1,1)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 2^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
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
    have ev : u^2+2=3*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid3_1_3 {k : ℕ} (hk : k<2097152) : ¬3^14∣(orbit 3 (2,1) (1,1) k).2 := by
  have h0 : Good 3 3 6 (2,1) (1,1) [1, 4] :=
    lift (t:=1) (s:=6) (good_one 3 (2,1) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 9 18 (2,1) (1,1) [4, 13] :=
    lift (t:=6) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 27 54 (2,1) (1,1) [13, 40] :=
    lift (t:=18) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 81 162 (2,1) (1,1) [40, 121] :=
    lift (t:=54) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 243 486 (2,1) (1,1) [121, 364] :=
    lift (t:=162) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 3 729 1458 (2,1) (1,1) [364, 1093] :=
    lift (t:=486) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 3 2187 4374 (2,1) (1,1) [1093, 3280] :=
    lift (t:=1458) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 3 6561 13122 (2,1) (1,1) [3280, 9841] :=
    lift (t:=4374) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 3 19683 39366 (2,1) (1,1) [9841, 29524] :=
    lift (t:=13122) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 3 59049 118098 (2,1) (1,1) [29524, 88573] :=
    lift (t:=39366) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 3 177147 354294 (2,1) (1,1) [88573, 265720] :=
    lift (t:=118098) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 3 531441 1062882 (2,1) (1,1) [265720, 797161] :=
    lift (t:=354294) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 3 1594323 3188646 (2,1) (1,1) [797161, 2391484] :=
    lift (t:=1062882) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 3 4782969 9565938 (2,1) (1,1) [2391484, 7174453] :=
    lift (t:=3188646) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h13 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid3_1_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 3 (2,1) (1,1) k).2 := by
  have h0 : Good 3 17 18 (2,1) (1,1) [4, 13] :=
    lift (t:=1) (s:=18) (good_one 3 (2,1) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 289 306 (2,1) (1,1) [76, 229] :=
    lift (t:=18) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 4913 5202 (2,1) (1,1) [1300, 3901] :=
    lift (t:=306) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 83521 88434 (2,1) (1,1) [22108, 66325] :=
    lift (t:=5202) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 1419857 1503378 (2,1) (1,1) [375844, 1127533] :=
    lift (t:=88434) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 3 24137569 25557426 (2,1) (1,1) [6389356, 19168069] :=
    lift (t:=1503378) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth3 {x y : ℕ} (eqn : x^2+2=3*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣51) : x≤265 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent3 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣51^14 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 52, i.val.Prime → i.val∣51 → i.val=3 ∨ i.val=17 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=3 ∨ p=17 at tags
    have horb : p^(14+1)∣(orbit 3 (2,1) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    subst s
    rcases tags with rfl|rfl
    · exact avoid3_1_3 low ((pow_dvd_pow 3 (by decide : 14≤14+1)).trans horb)
    · exact avoid3_1_17 low ((pow_dvd_pow 17 (by decide : 6≤14+1)).trans horb)
  have limK : k<80 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<51^14) dv
    have : 51^14<2^80 := by decide
    omega
  have small : ∀ s ∈ ([(1,1)] : List (ℕ×ℕ)), ∀ i : Fin 80,
      (orbit 3 (2,1) s i.val).2∣51^14 → (orbit 3 (2,1) s i.val).1≤265 := by decide +kernel
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
private theorem avoid5_1_17 {k : ℕ} (_hk : k<2097152) : ¬17^1∣(orbit 5 (9,4) (1,1) k).2 := by
  have h0 : Good 5 17 6 (9,4) (1,1) [] :=
    lift (t:=1) (s:=6) (good_one 5 (9,4) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid5_4_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 5 (9,4) (4,2) k).2 := by
  have h0 : Good 5 17 6 (9,4) (4,2) [1, 4] :=
    lift (t:=1) (s:=6) (good_one 5 (9,4) (4,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 289 102 (9,4) (4,2) [25, 76] :=
    lift (t:=6) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 5 4913 1734 (9,4) (4,2) [433, 1300] :=
    lift (t:=102) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 5 83521 29478 (9,4) (4,2) [7369, 22108] :=
    lift (t:=1734) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 5 1419857 501126 (9,4) (4,2) [125281, 375844] :=
    lift (t:=29478) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 5 24137569 8519142 (9,4) (4,2) [2129785, 6389356] :=
    lift (t:=501126) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
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
private theorem avoid5_11_17 {k : ℕ} (_hk : k<2097152) : ¬17^1∣(orbit 5 (9,4) (11,5) k).2 := by
  have h0 : Good 5 17 6 (9,4) (11,5) [] :=
    lift (t:=1) (s:=6) (good_one 5 (9,4) (11,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth5 {x y : ℕ} (eqn : x^2+4=5*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣85) : x≤11 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent5 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣85^11 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 86, i.val.Prime → i.val∣85 → i.val=5 ∨ i.val=17 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=5 ∨ p=17 at tags
    have horb : p^(11+1)∣(orbit 5 (9,4) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid5_1_5 low ((pow_dvd_pow 5 (by decide : 11≤11+1)).trans horb)
      · exact avoid5_1_17 low ((pow_dvd_pow 17 (by decide : 1≤11+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid5_4_5 low ((pow_dvd_pow 5 (by decide : 10≤11+1)).trans horb)
      · exact avoid5_4_17 low ((pow_dvd_pow 17 (by decide : 6≤11+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid5_11_5 low ((pow_dvd_pow 5 (by decide : 10≤11+1)).trans horb)
      · exact avoid5_11_17 low ((pow_dvd_pow 17 (by decide : 1≤11+1)).trans horb)
  have limK : k<71 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<85^11) dv
    have : 85^11<2^71 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(4,2),(11,5)] : List (ℕ×ℕ)), ∀ i : Fin 71,
      (orbit 5 (9,4) s i.val).2∣85^11 → (orbit 5 (9,4) s i.val).1≤11 := by decide +kernel
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
private theorem avoid10_1_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 10 (19,6) (1,1) k).2 := by
  have h0 : Good 10 17 18 (19,6) (1,1) [7, 16] :=
    lift (t:=1) (s:=18) (good_one 10 (19,6) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 10 289 306 (19,6) (1,1) [61, 214] :=
    lift (t:=18) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 10 4913 5202 (19,6) (1,1) [2356, 4957] :=
    lift (t:=306) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 10 83521 88434 (19,6) (1,1) [41371, 85588] :=
    lift (t:=5202) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 10 1419857 1503378 (19,6) (1,1) [306673, 1058362] :=
    lift (t:=88434) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 10 24137569 25557426 (19,6) (1,1) [5568496, 18347209] :=
    lift (t:=1503378) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
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
private theorem avoid10_9_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 10 (19,6) (9,3) k).2 := by
  have h0 : Good 10 17 18 (19,6) (9,3) [4, 13] :=
    lift (t:=1) (s:=18) (good_one 10 (19,6) (9,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 10 289 306 (19,6) (9,3) [76, 229] :=
    lift (t:=18) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 10 4913 5202 (19,6) (9,3) [1300, 3901] :=
    lift (t:=306) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 10 83521 88434 (19,6) (9,3) [22108, 66325] :=
    lift (t:=5202) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 10 1419857 1503378 (19,6) (9,3) [375844, 1127533] :=
    lift (t:=88434) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 10 24137569 25557426 (19,6) (9,3) [6389356, 19168069] :=
    lift (t:=1503378) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
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
private theorem avoid10_41_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 10 (19,6) (41,13) k).2 := by
  have h0 : Good 10 17 18 (19,6) (41,13) [1, 10] :=
    lift (t:=1) (s:=18) (good_one 10 (19,6) (41,13)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 10 289 306 (19,6) (41,13) [91, 244] :=
    lift (t:=18) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 10 4913 5202 (19,6) (41,13) [244, 2845] :=
    lift (t:=306) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 10 83521 88434 (19,6) (41,13) [2845, 47062] :=
    lift (t:=5202) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 10 1419857 1503378 (19,6) (41,13) [445015, 1196704] :=
    lift (t:=88434) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 10 24137569 25557426 (19,6) (41,13) [7210216, 19988929] :=
    lift (t:=1503378) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth10 {x y : ℕ} (eqn : x^2+9=10*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣170) : x≤79 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent10 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣170^10 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 171, i.val.Prime → i.val∣170 → i.val=2 ∨ i.val=5 ∨ i.val=17 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=5 ∨ p=17 at tags
    have horb : p^(10+1)∣(orbit 10 (19,6) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid10_1_2 low ((pow_dvd_pow 2 (by decide : 1≤10+1)).trans horb)
      · exact avoid10_1_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid10_1_17 low ((pow_dvd_pow 17 (by decide : 6≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid10_9_2 low ((pow_dvd_pow 2 (by decide : 1≤10+1)).trans horb)
      · exact avoid10_9_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid10_9_17 low ((pow_dvd_pow 17 (by decide : 6≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid10_41_2 low ((pow_dvd_pow 2 (by decide : 1≤10+1)).trans horb)
      · exact avoid10_41_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid10_41_17 low ((pow_dvd_pow 17 (by decide : 6≤10+1)).trans horb)
  have limK : k<75 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<170^10) dv
    have : 170^10<2^75 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(9,3),(41,13)] : List (ℕ×ℕ)), ∀ i : Fin 75,
      (orbit 10 (19,6) s i.val).2∣170^10 → (orbit 10 (19,6) s i.val).1≤79 := by decide +kernel
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
private theorem avoid14_1_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 14 (15,4) (1,1) k).2 := by
  have h0 : Good 14 17 9 (15,4) (1,1) [3] :=
    lift (t:=1) (s:=9) (good_one 14 (15,4) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 14 289 153 (15,4) (1,1) [3] :=
    lift (t:=9) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 14 4913 2601 (15,4) (1,1) [2298] :=
    lift (t:=153) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 14 83521 44217 (15,4) (1,1) [2298] :=
    lift (t:=2601) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 14 1419857 751689 (15,4) (1,1) [488685] :=
    lift (t:=44217) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 14 24137569 12778713 (15,4) (1,1) [2743752] :=
    lift (t:=751689) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
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
private theorem avoid14_41_17 {k : ℕ} (hk : k<2097152) : ¬17^6∣(orbit 14 (15,4) (41,11) k).2 := by
  have h0 : Good 14 17 9 (15,4) (41,11) [5] :=
    lift (t:=1) (s:=9) (good_one 14 (15,4) (41,11)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 14 289 153 (15,4) (41,11) [149] :=
    lift (t:=9) (s:=17) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 14 4913 2601 (15,4) (41,11) [302] :=
    lift (t:=153) (s:=17) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 14 83521 44217 (15,4) (41,11) [41918] :=
    lift (t:=2601) (s:=17) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 14 1419857 751689 (15,4) (41,11) [263003] :=
    lift (t:=44217) (s:=17) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 14 24137569 12778713 (15,4) (41,11) [10034960] :=
    lift (t:=751689) (s:=17) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth14 {x y : ℕ} (eqn : x^2+13=14*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣238) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent14 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣238^9 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 239, i.val.Prime → i.val∣238 → i.val=2 ∨ i.val=7 ∨ i.val=17 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=7 ∨ p=17 at tags
    have horb : p^(9+1)∣(orbit 14 (15,4) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid14_1_2 low ((pow_dvd_pow 2 (by decide : 1≤9+1)).trans horb)
      · exact avoid14_1_7 low ((pow_dvd_pow 7 (by decide : 9≤9+1)).trans horb)
      · exact avoid14_1_17 low ((pow_dvd_pow 17 (by decide : 6≤9+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid14_41_2 low ((pow_dvd_pow 2 (by decide : 1≤9+1)).trans horb)
      · exact avoid14_41_7 low ((pow_dvd_pow 7 (by decide : 8≤9+1)).trans horb)
      · exact avoid14_41_17 low ((pow_dvd_pow 17 (by decide : 6≤9+1)).trans horb)
  have limK : k<72 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<238^9) dv
    have : 238^9<2^72 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(41,11)] : List (ℕ×ℕ)), ∀ i : Fin 72,
      (orbit 14 (15,4) s i.val).2∣238^9 → (orbit 14 (15,4) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv

end Erdos889.SquareSeventeen



namespace Erdos889.SquareSeventeen
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem extract {n j R : ℕ} (div : 120120∣n) (hj : 0<j) (lj : j≤16)
    (rad : ∀ p : Fin 17, p.val.Prime → p.val∣j → p.val∣R) (large : 17∣R)
    (pos : R≠0) (hit : 17∣n+j) (sol : v_l 1 n=1) :
    ∃ D y : ℕ, D∣R ∧ D*y^2=n+j ∧ (∀ p : ℕ, p.Prime → p∣y → p∣R) := by
  have sup (p : ℕ) (pp : p.Prime) (hd : p∣n+j) : p∣R := by
    by_cases small : p≤j
    · have t : ∀ t : Fin 17, t.val.Prime → t.val∣120120 := by decide
      have dp := (t ⟨p,by omega⟩ pp).trans div
      exact rad ⟨p,by omega⟩ pp ((Nat.dvd_add_iff_right dp).mpr hd)
    · by_cases same : p=17
      · exact same ▸ large
      exact False.elim (two_primes hj pp (by decide : Nat.Prime 17) same (by omega) (by omega) hd hit sol)
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
    (shape : n+1=p^2) (one : 2≤D) (small : j≤16) (big : 100<p) :
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

private theorem reject2 {n p : ℕ} (big : 1000<p) (div : 120120∣n) (shape : n+1=p^2)
    (hit : 17∣n+2) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=34) div (by decide : 0<2) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=2 := coefficient (m:=12) fac dr (by decide) (by decide)
    ((by decide : 12∣120120).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+1=2*y^2 := by omega
  have h := smooth2 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject3 {n p : ℕ} (big : 1000<p) (div : 120120∣n) (shape : n+1=p^2)
    (hit : 17∣n+3) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=51) div (by decide : 0<3) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=3 := coefficient (m:=20) fac dr (by decide) (by decide)
    ((by decide : 20∣120120).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+2=3*y^2 := by omega
  have h := smooth3 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject5 {n p : ℕ} (big : 1000<p) (div : 120120∣n) (shape : n+1=p^2)
    (hit : 17∣n+5) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=85) div (by decide : 0<5) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=5 := coefficient (m:=24) fac dr (by decide) (by decide)
    ((by decide : 24∣120120).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+4=5*y^2 := by omega
  have h := smooth5 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject9 {n p : ℕ} (big : 1000<p) (div : 120120∣n) (shape : n+1=p^2)
    (hit : 17∣n+9) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=51) div (by decide : 0<9) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (m:=20) fac dr (by decide) (by decide)
    ((by decide : 20∣120120).trans div) (by decide +kernel)
  subst D
  have eqn : y^2=p^2+8 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

private theorem reject10 {n p : ℕ} (big : 1000<p) (div : 120120∣n) (shape : n+1=p^2)
    (hit : 17∣n+10) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=170) div (by decide : 0<10) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=10 := coefficient (m:=132) fac dr (by decide) (by decide)
    ((by decide : 132∣120120).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+9=10*y^2 := by omega
  have h := smooth10 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject14 {n p : ℕ} (big : 1000<p) (div : 120120∣n) (shape : n+1=p^2)
    (hit : 17∣n+14) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=238) div (by decide : 0<14) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=14 := coefficient (m:=24) fac dr (by decide) (by decide)
    ((by decide : 24∣120120).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+13=14*y^2 := by omega
  have h := smooth14 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject16 {n p : ℕ} (big : 1000<p) (div : 120120∣n) (shape : n+1=p^2)
    (hit : 17∣n+16) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=34) div (by decide : 0<16) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (m:=21) fac dr (by decide) (by decide)
    ((by decide : 21∣120120).trans div) (by decide +kernel)
  subst D
  have eqn : y^2=p^2+15 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

set_option maxHeartbeats 2000000 in
/-- Any further solution with a prime-square successor is divisible by every prime through 17. -/
theorem square_multiple_of_2042040 {n p : ℕ} (big : 330<n) (pp : p.Prime)
    (shape : n+1=p^2) (sol : v_l 1 n=1) : 2042040∣n := by
  have div := Erdos889.SquareThirteen.square_multiple_of_120120 big pp shape sol
  have huge := (Erdos889.MissingPrimeSieve.further_solution_bounds_thirty big sol).1
  have large : 1000<p := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have nz : ¬17∣p := by
    intro dvd
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 17) pp).mp dvd
    omega
  have seventeen : 17∣n := by
    by_contra miss
    have alts : 17∣n+2 ∨ 17∣n+3 ∨ 17∣n+5 ∨ 17∣n+9 ∨ 17∣n+10 ∨ 17∣n+14 ∨ 17∣n+16 := by
      have sq := Nat.pow_mod p 2 17
      have lt := Nat.mod_lt p (by decide : 0<17)
      interval_cases h : p%17 <;> norm_num at sq <;> omega
    rcases alts with h|h|h|h|h|h|h
    · exact reject2 large div shape h sol
    · exact reject3 large div shape h sol
    · exact reject5 large div shape h sol
    · exact reject9 large div shape h sol
    · exact reject10 large div shape h sol
    · exact reject14 large div shape h sol
    · exact reject16 large div shape h sol
  omega

theorem prime_square_outside_2042040 {n p : ℕ} (pp : p.Prime) (shape : n+1=p^2)
    (miss : ¬2042040∣n) : v_l 1 n=1 ↔ n∈[3,8,24,48,120] := by
  by_cases large : 330<n
  · constructor
    · intro sol
      exact (miss (square_multiple_of_2042040 large pp shape sol)).elim
    · intro mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      omega
  · apply Erdos889.SquareThirteen.prime_square_outside_120120 pp shape
    have := Nat.pow_le_pow_left pp.two_le 2
    omega
end Erdos889.SquareSeventeen

#print axioms Erdos889.SquareSeventeen.prime_square_outside_2042040
