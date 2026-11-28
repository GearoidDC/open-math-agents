import E889SquareSeventeen
/-! The next missing prime for square successors. -/
namespace Erdos889.SquareNineteen

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
private theorem avoid3_1_19 {k : ℕ} (_hk : k<2097152) : ¬19^1∣(orbit 3 (2,1) (1,1) k).2 := by
  have h0 : Good 3 19 5 (2,1) (1,1) [] :=
    lift (t:=1) (s:=5) (good_one 3 (2,1) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth3 {x y : ℕ} (eqn : x^2+2=3*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣57) : x≤5 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent3 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣57^14 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 58, i.val.Prime → i.val∣57 → i.val=3 ∨ i.val=19 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=3 ∨ p=19 at tags
    have horb : p^(14+1)∣(orbit 3 (2,1) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    subst s
    rcases tags with rfl|rfl
    · exact avoid3_1_3 low ((pow_dvd_pow 3 (by decide : 14≤14+1)).trans horb)
    · exact avoid3_1_19 low ((pow_dvd_pow 19 (by decide : 1≤14+1)).trans horb)
  have limK : k<82 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<57^14) dv
    have : 57^14<2^82 := by decide
    omega
  have small : ∀ s ∈ ([(1,1)] : List (ℕ×ℕ)), ∀ i : Fin 82,
      (orbit 3 (2,1) s i.val).2∣57^14 → (orbit 3 (2,1) s i.val).1≤5 := by decide +kernel
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
private theorem avoid11_1_19 {k : ℕ} (_hk : k<2097152) : ¬19^1∣(orbit 11 (10,3) (1,1) k).2 := by
  have h0 : Good 11 19 6 (10,3) (1,1) [] :=
    lift (t:=1) (s:=6) (good_one 11 (10,3) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
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
private theorem avoid11_23_19 {k : ℕ} (_hk : k<2097152) : ¬19^1∣(orbit 11 (10,3) (23,7) k).2 := by
  have h0 : Good 11 19 6 (10,3) (23,7) [] :=
    lift (t:=1) (s:=6) (good_one 11 (10,3) (23,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth11 {x y : ℕ} (eqn : x^2+10=11*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣209) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent11 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣209^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 210, i.val.Prime → i.val∣209 → i.val=11 ∨ i.val=19 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=11 ∨ p=19 at tags
    have horb : p^(7+1)∣(orbit 11 (10,3) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid11_1_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid11_1_19 low ((pow_dvd_pow 19 (by decide : 1≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid11_23_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid11_23_19 low ((pow_dvd_pow 19 (by decide : 1≤7+1)).trans horb)
  have limK : k<54 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<209^7) dv
    have : 209^7<2^54 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(23,7)] : List (ℕ×ℕ)), ∀ i : Fin 54,
      (orbit 11 (10,3) s i.val).2∣209^7 → (orbit 11 (10,3) s i.val).1≤1 := by decide +kernel
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
private theorem avoid13_1_19 {k : ℕ} (hk : k<2097152) : ¬19^6∣(orbit 13 (649,180) (1,1) k).2 := by
  have h0 : Good 13 19 20 (649,180) (1,1) [4, 14] :=
    lift (t:=1) (s:=20) (good_one 13 (649,180) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 361 380 (649,180) (1,1) [14, 204] :=
    lift (t:=20) (s:=19) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 6859 7220 (649,180) (1,1) [964, 4574] :=
    lift (t:=380) (s:=19) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 130321 137180 (649,180) (1,1) [8184, 76774] :=
    lift (t:=7220) (s:=19) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 2476099 2606420 (649,180) (1,1) [556904, 1860114] :=
    lift (t:=137180) (s:=19) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 47045881 49521980 (649,180) (1,1) [7072954, 31833944] :=
    lift (t:=2606420) (s:=19) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
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
private theorem avoid13_14_19 {k : ℕ} (hk : k<2097152) : ¬19^7∣(orbit 13 (649,180) (14,4) k).2 := by
  have h0 : Good 13 19 20 (649,180) (14,4) [9, 19] :=
    lift (t:=1) (s:=20) (good_one 13 (649,180) (14,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 361 380 (649,180) (14,4) [49, 239] :=
    lift (t:=20) (s:=19) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 6859 7220 (649,180) (14,4) [239, 3849] :=
    lift (t:=380) (s:=19) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 130321 137180 (649,180) (14,4) [14679, 83269] :=
    lift (t:=7220) (s:=19) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 2476099 2606420 (649,180) (14,4) [1180709, 2483919] :=
    lift (t:=137180) (s:=19) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 47045881 49521980 (649,180) (14,4) [1180709, 25941699] :=
    lift (t:=2606420) (s:=19) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 13 893871739 940917620 (649,180) (14,4) [347834569, 818293379] :=
    lift (t:=49521980) (s:=19) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
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
private theorem avoid13_25_19 {k : ℕ} (hk : k<2097152) : ¬19^6∣(orbit 13 (649,180) (25,7) k).2 := by
  have h0 : Good 13 19 20 (649,180) (25,7) [7, 17] :=
    lift (t:=1) (s:=20) (good_one 13 (649,180) (25,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 361 380 (649,180) (25,7) [77, 267] :=
    lift (t:=20) (s:=19) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 6859 7220 (649,180) (25,7) [2167, 5777] :=
    lift (t:=380) (s:=19) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 130321 137180 (649,180) (25,7) [31047, 99637] :=
    lift (t:=7220) (s:=19) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 2476099 2606420 (649,180) (25,7) [991307, 2294517] :=
    lift (t:=137180) (s:=19) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 47045881 49521980 (649,180) (25,7) [15326617, 40087607] :=
    lift (t:=2606420) (s:=19) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
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
private theorem avoid13_155_19 {k : ℕ} (hk : k<2097152) : ¬19^6∣(orbit 13 (649,180) (155,43) k).2 := by
  have h0 : Good 13 19 20 (649,180) (155,43) [2, 12] :=
    lift (t:=1) (s:=20) (good_one 13 (649,180) (155,43)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 361 380 (649,180) (155,43) [112, 302] :=
    lift (t:=20) (s:=19) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 6859 7220 (649,180) (155,43) [1442, 5052] :=
    lift (t:=380) (s:=19) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 130321 137180 (649,180) (155,43) [37542, 106132] :=
    lift (t:=7220) (s:=19) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 2476099 2606420 (649,180) (155,43) [311902, 1615112] :=
    lift (t:=137180) (s:=19) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 47045881 49521980 (649,180) (155,43) [9434372, 34195362] :=
    lift (t:=2606420) (s:=19) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
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
private theorem avoid13_274_19 {k : ℕ} (hk : k<2097152) : ¬19^6∣(orbit 13 (649,180) (274,76) k).2 := by
  have h0 : Good 13 19 20 (649,180) (274,76) [0, 10] :=
    lift (t:=1) (s:=20) (good_one 13 (649,180) (274,76)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 361 380 (649,180) (274,76) [140, 330] :=
    lift (t:=20) (s:=19) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 6859 7220 (649,180) (274,76) [3370, 6980] :=
    lift (t:=380) (s:=19) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 130321 137180 (649,180) (274,76) [53910, 122500] :=
    lift (t:=7220) (s:=19) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 2476099 2606420 (649,180) (274,76) [122500, 1425710] :=
    lift (t:=137180) (s:=19) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 47045881 49521980 (649,180) (274,76) [23580280, 48341270] :=
    lift (t:=2606420) (s:=19) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
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
private theorem avoid13_1691_19 {k : ℕ} (hk : k<2097152) : ¬19^6∣(orbit 13 (649,180) (1691,469) k).2 := by
  have h0 : Good 13 19 20 (649,180) (1691,469) [5, 15] :=
    lift (t:=1) (s:=20) (good_one 13 (649,180) (1691,469)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 361 380 (649,180) (1691,469) [175, 365] :=
    lift (t:=20) (s:=19) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 6859 7220 (649,180) (1691,469) [2645, 6255] :=
    lift (t:=380) (s:=19) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 130321 137180 (649,180) (1691,469) [60405, 128995] :=
    lift (t:=7220) (s:=19) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 2476099 2606420 (649,180) (1691,469) [746305, 2049515] :=
    lift (t:=137180) (s:=19) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 47045881 49521980 (649,180) (1691,469) [17688035, 42449025] :=
    lift (t:=2606420) (s:=19) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth13 {x y : ℕ} (eqn : x^2+12=13*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣247) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent13 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣247^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 248, i.val.Prime → i.val∣247 → i.val=13 ∨ i.val=19 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=13 ∨ p=19 at tags
    have horb : p^(7+1)∣(orbit 13 (649,180) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid13_1_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid13_1_19 low ((pow_dvd_pow 19 (by decide : 6≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_14_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid13_14_19 low ((pow_dvd_pow 19 (by decide : 7≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_25_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid13_25_19 low ((pow_dvd_pow 19 (by decide : 6≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_155_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid13_155_19 low ((pow_dvd_pow 19 (by decide : 6≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_274_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid13_274_19 low ((pow_dvd_pow 19 (by decide : 6≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_1691_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid13_1691_19 low ((pow_dvd_pow 19 (by decide : 6≤7+1)).trans horb)
  have limK : k<56 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<247^7) dv
    have : 247^7<2^56 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(14,4),(25,7),(155,43),(274,76),(1691,469)] : List (ℕ×ℕ)), ∀ i : Fin 56,
      (orbit 13 (649,180) s i.val).2∣247^7 → (orbit 13 (649,180) s i.val).1≤1 := by decide +kernel
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
private theorem avoid14_1_19 {k : ℕ} (hk : k<2097152) : ¬19^6∣(orbit 14 (15,4) (1,1) k).2 := by
  have h0 : Good 14 19 20 (15,4) (1,1) [1, 11] :=
    lift (t:=1) (s:=20) (good_one 14 (15,4) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 14 361 380 (15,4) (1,1) [41, 231] :=
    lift (t:=20) (s:=19) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 14 6859 7220 (15,4) (1,1) [3271, 6881] :=
    lift (t:=380) (s:=19) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 14 130321 137180 (15,4) (1,1) [53811, 122401] :=
    lift (t:=7220) (s:=19) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 14 2476099 2606420 (15,4) (1,1) [808301, 2111511] :=
    lift (t:=137180) (s:=19) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 14 47045881 49521980 (15,4) (1,1) [7324351, 32085341] :=
    lift (t:=2606420) (s:=19) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid14_41_19 {k : ℕ} (hk : k<2097152) : ¬19^6∣(orbit 14 (15,4) (41,11) k).2 := by
  have h0 : Good 14 19 20 (15,4) (41,11) [8, 18] :=
    lift (t:=1) (s:=20) (good_one 14 (15,4) (41,11)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 14 361 380 (15,4) (41,11) [148, 338] :=
    lift (t:=20) (s:=19) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 14 6859 7220 (15,4) (41,11) [338, 3948] :=
    lift (t:=380) (s:=19) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 14 130321 137180 (15,4) (41,11) [14778, 83368] :=
    lift (t:=7220) (s:=19) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 14 2476099 2606420 (15,4) (41,11) [494908, 1798118] :=
    lift (t:=137180) (s:=19) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 14 47045881 49521980 (15,4) (41,11) [17436638, 42197628] :=
    lift (t:=2606420) (s:=19) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth14 {x y : ℕ} (eqn : x^2+13=14*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣266) : x≤71 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent14 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣266^9 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 267, i.val.Prime → i.val∣266 → i.val=2 ∨ i.val=7 ∨ i.val=19 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=7 ∨ p=19 at tags
    have horb : p^(9+1)∣(orbit 14 (15,4) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid14_1_2 low ((pow_dvd_pow 2 (by decide : 1≤9+1)).trans horb)
      · exact avoid14_1_7 low ((pow_dvd_pow 7 (by decide : 9≤9+1)).trans horb)
      · exact avoid14_1_19 low ((pow_dvd_pow 19 (by decide : 6≤9+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid14_41_2 low ((pow_dvd_pow 2 (by decide : 1≤9+1)).trans horb)
      · exact avoid14_41_7 low ((pow_dvd_pow 7 (by decide : 8≤9+1)).trans horb)
      · exact avoid14_41_19 low ((pow_dvd_pow 19 (by decide : 6≤9+1)).trans horb)
  have limK : k<73 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<266^9) dv
    have : 266^9<2^73 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(41,11)] : List (ℕ×ℕ)), ∀ i : Fin 73,
      (orbit 14 (15,4) s i.val).2∣266^9 → (orbit 14 (15,4) s i.val).1≤71 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent15 {x y : ℕ} (eqn : x^2+14=15*y^2) :
    ∃ s ∈ ([(1,1),(11,3)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 15 (4,1) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<4
    · have hx : x<12 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤3 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 12, ∀ j : Fin 4, i.val^2+14=15*j.val^2 →
          (i.val,j.val)∈([(1,1),(11,3)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 4^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 15*y≤4*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 1*x≤4*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 3*y<1*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 4*x-15*y
    let v := 4*y-1*x
    have hu : u+15*y=4*x := Nat.sub_add_cancel ax
    have hv : v+1*x=4*y := Nat.sub_add_cancel ay
    have ev : u^2+14=15*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid15_1_3 {k : ℕ} (_hk : k<2097152) : ¬3^2∣(orbit 15 (4,1) (1,1) k).2 := by
  have h0 : Good 15 3 3 (4,1) (1,1) [2] :=
    lift (t:=1) (s:=3) (good_one 15 (4,1) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 15 9 3 (4,1) (1,1) [] :=
    lift (t:=3) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid15_1_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 15 (4,1) (1,1) k).2 := by
  have h0 : Good 15 5 10 (4,1) (1,1) [1, 6] :=
    lift (t:=1) (s:=10) (good_one 15 (4,1) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 15 25 50 (4,1) (1,1) [21, 46] :=
    lift (t:=10) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 15 125 250 (4,1) (1,1) [46, 171] :=
    lift (t:=50) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 15 625 1250 (4,1) (1,1) [296, 921] :=
    lift (t:=250) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 15 3125 6250 (4,1) (1,1) [296, 3421] :=
    lift (t:=1250) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 15 15625 31250 (4,1) (1,1) [12796, 28421] :=
    lift (t:=6250) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 15 78125 156250 (4,1) (1,1) [12796, 90921] :=
    lift (t:=31250) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 15 390625 781250 (4,1) (1,1) [325296, 715921] :=
    lift (t:=156250) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 15 1953125 3906250 (4,1) (1,1) [1497171, 3450296] :=
    lift (t:=781250) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 15 9765625 19531250 (4,1) (1,1) [5403421, 15169046] :=
    lift (t:=3906250) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid15_1_19 {k : ℕ} (hk : k<2097152) : ¬19^6∣(orbit 15 (4,1) (1,1) k).2 := by
  have h0 : Good 15 19 20 (4,1) (1,1) [6, 16] :=
    lift (t:=1) (s:=20) (good_one 15 (4,1) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 15 361 380 (4,1) (1,1) [6, 196] :=
    lift (t:=20) (s:=19) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 15 6859 7220 (4,1) (1,1) [3046, 6656] :=
    lift (t:=380) (s:=19) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 15 130321 137180 (4,1) (1,1) [68026, 136616] :=
    lift (t:=7220) (s:=19) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 15 2476099 2606420 (4,1) (1,1) [1302646, 2605856] :=
    lift (t:=137180) (s:=19) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 15 47045881 49521980 (4,1) (1,1) [23457216, 48218206] :=
    lift (t:=2606420) (s:=19) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid15_11_3 {k : ℕ} (_hk : k<2097152) : ¬3^2∣(orbit 15 (4,1) (11,3) k).2 := by
  have h0 : Good 15 3 3 (4,1) (11,3) [0] :=
    lift (t:=1) (s:=3) (good_one 15 (4,1) (11,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 15 9 3 (4,1) (11,3) [] :=
    lift (t:=3) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid15_11_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 15 (4,1) (11,3) k).2 := by
  have h0 : Good 15 5 10 (4,1) (11,3) [3, 8] :=
    lift (t:=1) (s:=10) (good_one 15 (4,1) (11,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 15 25 50 (4,1) (11,3) [3, 28] :=
    lift (t:=10) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 15 125 250 (4,1) (11,3) [78, 203] :=
    lift (t:=50) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 15 625 1250 (4,1) (11,3) [328, 953] :=
    lift (t:=250) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 15 3125 6250 (4,1) (11,3) [2828, 5953] :=
    lift (t:=1250) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 15 15625 31250 (4,1) (11,3) [2828, 18453] :=
    lift (t:=6250) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 15 78125 156250 (4,1) (11,3) [65328, 143453] :=
    lift (t:=31250) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 15 390625 781250 (4,1) (11,3) [65328, 455953] :=
    lift (t:=156250) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 15 1953125 3906250 (4,1) (11,3) [455953, 2409078] :=
    lift (t:=781250) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 15 9765625 19531250 (4,1) (11,3) [4362203, 14127828] :=
    lift (t:=3906250) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid15_11_19 {k : ℕ} (hk : k<2097152) : ¬19^7∣(orbit 15 (4,1) (11,3) k).2 := by
  have h0 : Good 15 19 20 (4,1) (11,3) [3, 13] :=
    lift (t:=1) (s:=20) (good_one 15 (4,1) (11,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 15 361 380 (4,1) (11,3) [183, 373] :=
    lift (t:=20) (s:=19) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 15 6859 7220 (4,1) (11,3) [563, 4173] :=
    lift (t:=380) (s:=19) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 15 130321 137180 (4,1) (11,3) [563, 69153] :=
    lift (t:=7220) (s:=19) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 15 2476099 2606420 (4,1) (11,3) [563, 1303773] :=
    lift (t:=137180) (s:=19) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 15 47045881 49521980 (4,1) (11,3) [1303773, 26064763] :=
    lift (t:=2606420) (s:=19) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 15 893871739 940917620 (4,1) (11,3) [298435653, 768894463] :=
    lift (t:=49521980) (s:=19) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth15 {x y : ℕ} (eqn : x^2+14=15*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣285) : x≤5519 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent15 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣285^10 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 286, i.val.Prime → i.val∣285 → i.val=3 ∨ i.val=5 ∨ i.val=19 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=3 ∨ p=5 ∨ p=19 at tags
    have horb : p^(10+1)∣(orbit 15 (4,1) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid15_1_3 low ((pow_dvd_pow 3 (by decide : 2≤10+1)).trans horb)
      · exact avoid15_1_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid15_1_19 low ((pow_dvd_pow 19 (by decide : 6≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid15_11_3 low ((pow_dvd_pow 3 (by decide : 2≤10+1)).trans horb)
      · exact avoid15_11_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid15_11_19 low ((pow_dvd_pow 19 (by decide : 7≤10+1)).trans horb)
  have limK : k<82 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<285^10) dv
    have : 285^10<2^82 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(11,3)] : List (ℕ×ℕ)), ∀ i : Fin 82,
      (orbit 15 (4,1) s i.val).2∣285^10 → (orbit 15 (4,1) s i.val).1≤5519 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv

end Erdos889.SquareNineteen



namespace Erdos889.SquareNineteen
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem extract {n j R : ℕ} (div : 2042040∣n) (hj : 0<j) (lj : j≤18)
    (rad : ∀ p : Fin 19, p.val.Prime → p.val∣j → p.val∣R) (large : 19∣R)
    (pos : R≠0) (hit : 19∣n+j) (sol : v_l 1 n=1) :
    ∃ D y : ℕ, D∣R ∧ D*y^2=n+j ∧ (∀ p : ℕ, p.Prime → p∣y → p∣R) := by
  have sup (p : ℕ) (pp : p.Prime) (hd : p∣n+j) : p∣R := by
    by_cases small : p≤j
    · have t : ∀ t : Fin 19, t.val.Prime → t.val∣2042040 := by decide
      have dp := (t ⟨p,by omega⟩ pp).trans div
      exact rad ⟨p,by omega⟩ pp ((Nat.dvd_add_iff_right dp).mpr hd)
    · by_cases same : p=19
      · exact same ▸ large
      exact False.elim (two_primes hj pp (by decide : Nat.Prime 19) same (by omega) (by omega) hd hit sol)
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
    (shape : n+1=p^2) (one : 2≤D) (small : j≤18) (big : 100<p) :
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

private theorem reject3 {n p : ℕ} (big : 10000<p) (div : 2042040∣n) (shape : n+1=p^2)
    (hit : 19∣n+3) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=57) div (by decide : 0<3) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=3 := coefficient (m:=20) fac dr (by decide) (by decide)
    ((by decide : 20∣2042040).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+2=3*y^2 := by omega
  have h := smooth3 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject4 {n p : ℕ} (big : 10000<p) (div : 2042040∣n) (shape : n+1=p^2)
    (hit : 19∣n+4) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=38) div (by decide : 0<4) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (m:=21) fac dr (by decide) (by decide)
    ((by decide : 21∣2042040).trans div) (by decide +kernel)
  subst D
  have eqn : y^2=p^2+3 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

private theorem reject9 {n p : ℕ} (big : 10000<p) (div : 2042040∣n) (shape : n+1=p^2)
    (hit : 19∣n+9) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=57) div (by decide : 0<9) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (m:=20) fac dr (by decide) (by decide)
    ((by decide : 20∣2042040).trans div) (by decide +kernel)
  subst D
  have eqn : y^2=p^2+8 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

private theorem reject11 {n p : ℕ} (big : 10000<p) (div : 2042040∣n) (shape : n+1=p^2)
    (hit : 19∣n+11) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=209) div (by decide : 0<11) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=11 := coefficient (m:=12) fac dr (by decide) (by decide)
    ((by decide : 12∣2042040).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+10=11*y^2 := by omega
  have h := smooth11 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject13 {n p : ℕ} (big : 10000<p) (div : 2042040∣n) (shape : n+1=p^2)
    (hit : 19∣n+13) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=247) div (by decide : 0<13) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=13 := coefficient (m:=8) fac dr (by decide) (by decide)
    ((by decide : 8∣2042040).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+12=13*y^2 := by omega
  have h := smooth13 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject14 {n p : ℕ} (big : 10000<p) (div : 2042040∣n) (shape : n+1=p^2)
    (hit : 19∣n+14) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=266) div (by decide : 0<14) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=14 := coefficient (m:=40) fac dr (by decide) (by decide)
    ((by decide : 40∣2042040).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+13=14*y^2 := by omega
  have h := smooth14 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject15 {n p : ℕ} (big : 10000<p) (div : 2042040∣n) (shape : n+1=p^2)
    (hit : 19∣n+15) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=285) div (by decide : 0<15) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=15 := coefficient (m:=88) fac dr (by decide) (by decide)
    ((by decide : 88∣2042040).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+14=15*y^2 := by omega
  have h := smooth15 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject16 {n p : ℕ} (big : 10000<p) (div : 2042040∣n) (shape : n+1=p^2)
    (hit : 19∣n+16) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=38) div (by decide : 0<16) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (m:=21) fac dr (by decide) (by decide)
    ((by decide : 21∣2042040).trans div) (by decide +kernel)
  subst D
  have eqn : y^2=p^2+15 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

set_option maxHeartbeats 2000000 in
/-- Any further solution with a prime-square successor is divisible by every prime through 19. -/
theorem square_multiple_of_38798760 {n p : ℕ} (big : 330<n) (pp : p.Prime)
    (shape : n+1=p^2) (sol : v_l 1 n=1) : 38798760∣n := by
  have div := Erdos889.SquareSeventeen.square_multiple_of_2042040 big pp shape sol
  have huge := (Erdos889.MissingPrimeSieve.further_solution_bounds_thirty big sol).1
  have large : 10000<p := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have nz : ¬19∣p := by
    intro dvd
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 19) pp).mp dvd
    omega
  have nineteen : 19∣n := by
    by_contra miss
    have alts : 19∣n+3 ∨ 19∣n+4 ∨ 19∣n+9 ∨ 19∣n+11 ∨ 19∣n+13 ∨ 19∣n+14 ∨ 19∣n+15 ∨ 19∣n+16 := by
      have sq := Nat.pow_mod p 2 19
      have lt := Nat.mod_lt p (by decide : 0<19)
      interval_cases h : p%19 <;> norm_num at sq <;> omega
    rcases alts with h|h|h|h|h|h|h|h
    · exact reject3 large div shape h sol
    · exact reject4 large div shape h sol
    · exact reject9 large div shape h sol
    · exact reject11 large div shape h sol
    · exact reject13 large div shape h sol
    · exact reject14 large div shape h sol
    · exact reject15 large div shape h sol
    · exact reject16 large div shape h sol
  omega

theorem prime_square_outside_38798760 {n p : ℕ} (pp : p.Prime) (shape : n+1=p^2)
    (miss : ¬38798760∣n) : v_l 1 n=1 ↔ n∈[3,8,24,48,120] := by
  by_cases large : 330<n
  · constructor
    · intro sol
      exact (miss (square_multiple_of_38798760 large pp shape sol)).elim
    · intro mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      omega
  · apply Erdos889.SquareSeventeen.prime_square_outside_2042040 pp shape
    have := Nat.pow_le_pow_left pp.two_le 2
    omega
end Erdos889.SquareNineteen

#print axioms Erdos889.SquareNineteen.prime_square_outside_38798760
