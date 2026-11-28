import E889SquareTwentyNine

/-! Prime-square successor solutions when 31 is the first missing prime. -/

namespace Erdos889.SquareThirtyOne

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
private theorem avoid7_1_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 7 (8,3) (1,1) k).2 := by
  have h0 : Good 7 31 15 (8,3) (1,1) [9] :=
    lift (t:=1) (s:=15) (good_one 7 (8,3) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 961 465 (8,3) (1,1) [114] :=
    lift (t:=15) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 29791 14415 (8,3) (1,1) [12204] :=
    lift (t:=465) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 923521 446865 (8,3) (1,1) [113109] :=
    lift (t:=14415) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 28629151 13852815 (8,3) (1,1) [2794299] :=
    lift (t:=446865) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
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
private theorem avoid7_13_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 7 (8,3) (13,5) k).2 := by
  have h0 : Good 7 31 15 (8,3) (13,5) [5] :=
    lift (t:=1) (s:=15) (good_one 7 (8,3) (13,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 961 465 (8,3) (13,5) [350] :=
    lift (t:=15) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 29791 14415 (8,3) (13,5) [2210] :=
    lift (t:=465) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 923521 446865 (8,3) (13,5) [333755] :=
    lift (t:=14415) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 28629151 13852815 (8,3) (13,5) [11058515] :=
    lift (t:=446865) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth7 {x y : ℕ} (eqn : x^2+6=7*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣217) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent7 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣217^9 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=7 ∨ p=31 := by
      have h : p∣7*(31) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 7)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h))
    have horb : p^(9+1)∣(orbit 7 (8,3) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid7_1_7 low ((pow_dvd_pow 7 (by decide : 8≤9+1)).trans horb)
      · exact avoid7_1_31 low ((pow_dvd_pow 31 (by decide : 5≤9+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid7_13_7 low ((pow_dvd_pow 7 (by decide : 9≤9+1)).trans horb)
      · exact avoid7_13_31 low ((pow_dvd_pow 31 (by decide : 5≤9+1)).trans horb)
  have limK : k<70 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<217^9) dv
    have : 217^9<2^70 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(13,5)] : List (ℕ×ℕ)), ∀ i : Fin 70,
      (orbit 7 (8,3) s i.val).2∣217^9 → (orbit 7 (8,3) s i.val).1≤1 := by decide +kernel
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
private theorem avoid12_1_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 3 (2,1) (1,2) k).2 := by
  have h0 : Good 3 31 32 (2,1) (1,2) [10, 26] :=
    lift (t:=1) (s:=32) (good_one 3 (2,1) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 961 992 (2,1) (1,2) [490, 986] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 29791 30752 (2,1) (1,2) [9914, 25290] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 923521 953312 (2,1) (1,2) [132922, 609578] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 28629151 29552672 (2,1) (1,2) [12525978, 27302314] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid12_4_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 3 (2,1) (4,3) k).2 := by
  have h0 : Good 3 31 32 (2,1) (4,3) [5, 21] :=
    lift (t:=1) (s:=32) (good_one 3 (2,1) (4,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 961 992 (2,1) (4,3) [5, 501] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 29791 30752 (2,1) (4,3) [5461, 20837] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 923521 953312 (2,1) (4,3) [343733, 820389] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 28629151 29552672 (2,1) (4,3) [2250357, 17026693] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth12 {x y : ℕ} (eqn : x^2+11=3*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣186) : x≤3329 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent12 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣186^16 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=3 ∨ p=31 := by
      have h : p∣2*(3*(31)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 3)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h)))
    have horb : p^(16+1)∣(orbit 3 (2,1) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid12_1_2 low ((pow_dvd_pow 2 (by decide : 2≤16+1)).trans horb)
      · exact avoid12_1_3 low ((pow_dvd_pow 3 (by decide : 16≤16+1)).trans horb)
      · exact avoid12_1_31 low ((pow_dvd_pow 31 (by decide : 5≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid12_4_2 low ((pow_dvd_pow 2 (by decide : 2≤16+1)).trans horb)
      · exact avoid12_4_3 low ((pow_dvd_pow 3 (by decide : 14≤16+1)).trans horb)
      · exact avoid12_4_31 low ((pow_dvd_pow 31 (by decide : 5≤16+1)).trans horb)
  have limK : k<121 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<186^16) dv
    have : 186^16<2^121 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(4,3)] : List (ℕ×ℕ)), ∀ i : Fin 121,
      (orbit 3 (2,1) s i.val).2∣186^16 → (orbit 3 (2,1) s i.val).1≤3329 := by decide +kernel
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
private theorem avoid13_1_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 13 (649,180) (1,1) k).2 := by
  have h0 : Good 13 31 32 (649,180) (1,1) [2, 18] :=
    lift (t:=1) (s:=32) (good_one 13 (649,180) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 961 992 (649,180) (1,1) [354, 850] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 29791 30752 (649,180) (1,1) [8290, 23666] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 923521 953312 (649,180) (1,1) [285058, 761714] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 28629151 29552672 (649,180) (1,1) [6481586, 21257922] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid13_14_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 13 (649,180) (14,4) k).2 := by
  have h0 : Good 13 31 32 (649,180) (14,4) [3, 19] :=
    lift (t:=1) (s:=32) (good_one 13 (649,180) (14,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 961 992 (649,180) (14,4) [307, 803] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 29791 30752 (649,180) (14,4) [12211, 27587] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 923521 953312 (649,180) (14,4) [350483, 827139] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 28629151 29552672 (649,180) (14,4) [13220195, 27996531] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid13_25_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 13 (649,180) (25,7) k).2 := by
  have h0 : Good 13 31 32 (649,180) (25,7) [7, 23] :=
    lift (t:=1) (s:=32) (good_one 13 (649,180) (25,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 961 992 (649,180) (25,7) [23, 519] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 29791 30752 (649,180) (25,7) [13415, 28791] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 923521 953312 (649,180) (25,7) [443943, 920599] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 28629151 29552672 (649,180) (25,7) [11407031, 26183367] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid13_155_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 13 (649,180) (155,43) k).2 := by
  have h0 : Good 13 31 32 (649,180) (155,43) [8, 24] :=
    lift (t:=1) (s:=32) (good_one 13 (649,180) (155,43)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 961 992 (649,180) (155,43) [472, 968] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 29791 30752 (649,180) (155,43) [1960, 17336] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 923521 953312 (649,180) (155,43) [32712, 509368] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 28629151 29552672 (649,180) (155,43) [3369304, 18145640] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid13_274_31 {k : ℕ} (hk : k<2097152) : ¬31^6∣(orbit 13 (649,180) (274,76) k).2 := by
  have h0 : Good 13 31 32 (649,180) (274,76) [12, 28] :=
    lift (t:=1) (s:=32) (good_one 13 (649,180) (274,76)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 961 992 (649,180) (274,76) [188, 684] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 29791 30752 (649,180) (274,76) [3164, 18540] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 923521 953312 (649,180) (274,76) [126172, 602828] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 28629151 29552672 (649,180) (274,76) [1556140, 16332476] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 13 887503681 916132832 (649,180) (274,76) [164095836, 622162252] :=
    lift (t:=29552672) (s:=31) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid13_1691_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 13 (649,180) (1691,469) k).2 := by
  have h0 : Good 13 31 32 (649,180) (1691,469) [13, 29] :=
    lift (t:=1) (s:=32) (good_one 13 (649,180) (1691,469)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 13 961 992 (649,180) (1691,469) [141, 637] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 13 29791 30752 (649,180) (1691,469) [7085, 22461] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 13 923521 953312 (649,180) (1691,469) [191597, 668253] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 13 28629151 29552672 (649,180) (1691,469) [8294749, 23071085] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth13 {x y : ℕ} (eqn : x^2+12=13*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣403) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent13 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣403^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=13 ∨ p=31 := by
      have h : p∣13*(31) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 13)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h))
    have horb : p^(7+1)∣(orbit 13 (649,180) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid13_1_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid13_1_31 low ((pow_dvd_pow 31 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_14_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid13_14_31 low ((pow_dvd_pow 31 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_25_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid13_25_31 low ((pow_dvd_pow 31 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_155_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid13_155_31 low ((pow_dvd_pow 31 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_274_13 low ((pow_dvd_pow 13 (by decide : 6≤7+1)).trans horb)
      · exact avoid13_274_31 low ((pow_dvd_pow 31 (by decide : 6≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid13_1691_13 low ((pow_dvd_pow 13 (by decide : 7≤7+1)).trans horb)
      · exact avoid13_1691_31 low ((pow_dvd_pow 31 (by decide : 5≤7+1)).trans horb)
  have limK : k<61 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<403^7) dv
    have : 403^7<2^61 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(14,4),(25,7),(155,43),(274,76),(1691,469)] : List (ℕ×ℕ)), ∀ i : Fin 61,
      (orbit 13 (649,180) s i.val).2∣403^7 → (orbit 13 (649,180) s i.val).1≤1 := by decide +kernel
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
private theorem avoid14_1_31 {k : ℕ} (_hk : k<2097152) : ¬31^1∣(orbit 14 (15,4) (1,1) k).2 := by
  have h0 : Good 14 31 3 (15,4) (1,1) [] :=
    lift (t:=1) (s:=3) (good_one 14 (15,4) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid14_41_31 {k : ℕ} (_hk : k<2097152) : ¬31^1∣(orbit 14 (15,4) (41,11) k).2 := by
  have h0 : Good 14 31 3 (15,4) (41,11) [] :=
    lift (t:=1) (s:=3) (good_one 14 (15,4) (41,11)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth14 {x y : ℕ} (eqn : x^2+13=14*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣434) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent14 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣434^9 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=7 ∨ p=31 := by
      have h : p∣2*(7*(31)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 7)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h)))
    have horb : p^(9+1)∣(orbit 14 (15,4) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid14_1_2 low ((pow_dvd_pow 2 (by decide : 1≤9+1)).trans horb)
      · exact avoid14_1_7 low ((pow_dvd_pow 7 (by decide : 9≤9+1)).trans horb)
      · exact avoid14_1_31 low ((pow_dvd_pow 31 (by decide : 1≤9+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid14_41_2 low ((pow_dvd_pow 2 (by decide : 1≤9+1)).trans horb)
      · exact avoid14_41_7 low ((pow_dvd_pow 7 (by decide : 8≤9+1)).trans horb)
      · exact avoid14_41_31 low ((pow_dvd_pow 31 (by decide : 1≤9+1)).trans horb)
  have limK : k<79 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<434^9) dv
    have : 434^9<2^79 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(41,11)] : List (ℕ×ℕ)), ∀ i : Fin 79,
      (orbit 14 (15,4) s i.val).2∣434^9 → (orbit 14 (15,4) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent18 {x y : ℕ} (eqn : x^2+17=2*y^2) :
    ∃ s ∈ ([(1,3),(9,7)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 2 (3,2) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<9
    · have hx : x<12 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤8 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 12, ∀ j : Fin 9, i.val^2+17=2*j.val^2 →
          (i.val,j.val)∈([(1,3),(9,7)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 9^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
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
    have ev : u^2+17=2*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid18_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 2 (3,2) (1,3) k).2 := by
  have h0 : Good 2 2 1 (3,2) (1,3) [] :=
    lift (t:=1) (s:=1) (good_one 2 (3,2) (1,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid18_1_3 {k : ℕ} (hk : k<2097152) : ¬3^16∣(orbit 2 (3,2) (1,3) k).2 := by
  have h0 : Good 2 3 4 (3,2) (1,3) [0, 2] :=
    lift (t:=1) (s:=4) (good_one 2 (3,2) (1,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 9 12 (3,2) (1,3) [2, 8] :=
    lift (t:=4) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 27 36 (3,2) (1,3) [14, 32] :=
    lift (t:=12) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 81 108 (3,2) (1,3) [14, 68] :=
    lift (t:=36) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 243 324 (3,2) (1,3) [68, 230] :=
    lift (t:=108) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 729 972 (3,2) (1,3) [68, 554] :=
    lift (t:=324) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 2 2187 2916 (3,2) (1,3) [554, 2012] :=
    lift (t:=972) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 2 6561 8748 (3,2) (1,3) [554, 4928] :=
    lift (t:=2916) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 2 19683 26244 (3,2) (1,3) [9302, 22424] :=
    lift (t:=8748) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 2 59049 78732 (3,2) (1,3) [9302, 48668] :=
    lift (t:=26244) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 2 177147 236196 (3,2) (1,3) [9302, 127400] :=
    lift (t:=78732) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 2 531441 708588 (3,2) (1,3) [9302, 363596] :=
    lift (t:=236196) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 2 1594323 2125764 (3,2) (1,3) [717890, 1780772] :=
    lift (t:=708588) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 2 4782969 6377292 (3,2) (1,3) [717890, 3906536] :=
    lift (t:=2125764) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 2 14348907 19131876 (3,2) (1,3) [717890, 10283828] :=
    lift (t:=6377292) (s:=3) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h15 : Good 2 43046721 57395628 (3,2) (1,3) [10283828, 38981642] :=
    lift (t:=19131876) (s:=3) (h14) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h15 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid18_1_31 {k : ℕ} (_hk : k<2097152) : ¬31^2∣(orbit 2 (3,2) (1,3) k).2 := by
  have h0 : Good 2 31 15 (3,2) (1,3) [4] :=
    lift (t:=1) (s:=15) (good_one 2 (3,2) (1,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 961 15 (3,2) (1,3) [] :=
    lift (t:=15) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid18_9_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 2 (3,2) (9,7) k).2 := by
  have h0 : Good 2 2 1 (3,2) (9,7) [] :=
    lift (t:=1) (s:=1) (good_one 2 (3,2) (9,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid18_9_3 {k : ℕ} (hk : k<2097152) : ¬3^14∣(orbit 2 (3,2) (9,7) k).2 := by
  have h0 : Good 2 3 4 (3,2) (9,7) [1, 3] :=
    lift (t:=1) (s:=4) (good_one 2 (3,2) (9,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 9 12 (3,2) (9,7) [3, 9] :=
    lift (t:=4) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 27 36 (3,2) (9,7) [3, 21] :=
    lift (t:=12) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 81 108 (3,2) (9,7) [39, 93] :=
    lift (t:=36) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 243 324 (3,2) (9,7) [93, 255] :=
    lift (t:=108) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 729 972 (3,2) (9,7) [417, 903] :=
    lift (t:=324) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 2 2187 2916 (3,2) (9,7) [903, 2361] :=
    lift (t:=972) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 2 6561 8748 (3,2) (9,7) [3819, 8193] :=
    lift (t:=2916) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 2 19683 26244 (3,2) (9,7) [3819, 16941] :=
    lift (t:=8748) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 2 59049 78732 (3,2) (9,7) [30063, 69429] :=
    lift (t:=26244) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 2 177147 236196 (3,2) (9,7) [108795, 226893] :=
    lift (t:=78732) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 2 531441 708588 (3,2) (9,7) [344991, 699285] :=
    lift (t:=236196) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 2 1594323 2125764 (3,2) (9,7) [344991, 1407873] :=
    lift (t:=708588) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 2 4782969 6377292 (3,2) (9,7) [2470755, 5659401] :=
    lift (t:=2125764) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h13 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid18_9_31 {k : ℕ} (_hk : k<2097152) : ¬31^2∣(orbit 2 (3,2) (9,7) k).2 := by
  have h0 : Good 2 31 15 (3,2) (9,7) [10] :=
    lift (t:=1) (s:=15) (good_one 2 (3,2) (9,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 961 15 (3,2) (9,7) [] :=
    lift (t:=15) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth18 {x y : ℕ} (eqn : x^2+17=2*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣186) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent18 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣186^16 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=3 ∨ p=31 := by
      have h : p∣2*(3*(31)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 3)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h)))
    have horb : p^(16+1)∣(orbit 2 (3,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid18_1_2 low ((pow_dvd_pow 2 (by decide : 1≤16+1)).trans horb)
      · exact avoid18_1_3 low ((pow_dvd_pow 3 (by decide : 16≤16+1)).trans horb)
      · exact avoid18_1_31 low ((pow_dvd_pow 31 (by decide : 2≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid18_9_2 low ((pow_dvd_pow 2 (by decide : 1≤16+1)).trans horb)
      · exact avoid18_9_3 low ((pow_dvd_pow 3 (by decide : 14≤16+1)).trans horb)
      · exact avoid18_9_31 low ((pow_dvd_pow 31 (by decide : 2≤16+1)).trans horb)
  have limK : k<121 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<186^16) dv
    have : 186^16<2^121 := by decide
    omega
  have small : ∀ s ∈ ([(1,3),(9,7)] : List (ℕ×ℕ)), ∀ i : Fin 121,
      (orbit 2 (3,2) s i.val).2∣186^16 → (orbit 2 (3,2) s i.val).1≤1 := by decide +kernel
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
private theorem avoid22_1_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 22 (197,42) (1,1) k).2 := by
  have h0 : Good 22 31 32 (197,42) (1,1) [15, 31] :=
    lift (t:=1) (s:=32) (good_one 22 (197,42) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 961 992 (197,42) (1,1) [175, 671] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 29791 30752 (197,42) (1,1) [671, 16047] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 923521 953312 (197,42) (1,1) [308191, 784847] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 28629151 29552672 (197,42) (1,1) [8411343, 23187679] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid22_23_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 22 (197,42) (23,5) k).2 := by
  have h0 : Good 22 31 32 (197,42) (23,5) [5, 21] :=
    lift (t:=1) (s:=32) (good_one 22 (197,42) (23,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 961 992 (197,42) (23,5) [101, 597] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 29791 30752 (197,42) (23,5) [3077, 18453] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 923521 953312 (197,42) (23,5) [18453, 495109] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 28629151 29552672 (197,42) (23,5) [11458197, 26234533] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid22_89_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 22 (197,42) (89,19) k).2 := by
  have h0 : Good 22 31 32 (197,42) (89,19) [10, 26] :=
    lift (t:=1) (s:=32) (good_one 22 (197,42) (89,19)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 961 992 (197,42) (89,19) [394, 890] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 29791 30752 (197,42) (89,19) [12298, 27674] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 923521 953312 (197,42) (89,19) [458202, 934858] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 28629151 29552672 (197,42) (89,19) [3318138, 18094474] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
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
private theorem avoid22_727_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 22 (197,42) (727,155) k).2 := by
  have h0 : Good 22 31 32 (197,42) (727,155) [0, 16] :=
    lift (t:=1) (s:=32) (good_one 22 (197,42) (727,155)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 961 992 (197,42) (727,155) [320, 816] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 29791 30752 (197,42) (727,155) [14704, 30080] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 923521 953312 (197,42) (727,155) [168464, 645120] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 28629151 29552672 (197,42) (727,155) [6364992, 21141328] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth22 {x y : ℕ} (eqn : x^2+21=22*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣682) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent22 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣682^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=11 ∨ p=31 := by
      have h : p∣2*(11*(31)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 11)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h)))
    have horb : p^(7+1)∣(orbit 22 (197,42) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_1_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_1_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_1_31 low ((pow_dvd_pow 31 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_23_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_23_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_23_31 low ((pow_dvd_pow 31 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_89_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_89_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_89_31 low ((pow_dvd_pow 31 (by decide : 5≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_727_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_727_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_727_31 low ((pow_dvd_pow 31 (by decide : 5≤7+1)).trans horb)
  have limK : k<66 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<682^7) dv
    have : 682^7<2^66 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(23,5),(89,19),(727,155)] : List (ℕ×ℕ)), ∀ i : Fin 66,
      (orbit 22 (197,42) s i.val).2∣682^7 → (orbit 22 (197,42) s i.val).1≤1 := by decide +kernel
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
private theorem avoid23_1_31 {k : ℕ} (_hk : k<2097152) : ¬31^1∣(orbit 23 (24,5) (1,1) k).2 := by
  have h0 : Good 23 31 16 (24,5) (1,1) [] :=
    lift (t:=1) (s:=16) (good_one 23 (24,5) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
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
private theorem avoid23_91_31 {k : ℕ} (_hk : k<2097152) : ¬31^1∣(orbit 23 (24,5) (91,19) k).2 := by
  have h0 : Good 23 31 16 (24,5) (91,19) [] :=
    lift (t:=1) (s:=16) (good_one 23 (24,5) (91,19)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth23 {x y : ℕ} (eqn : x^2+22=23*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣713) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent23 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣713^5 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=23 ∨ p=31 := by
      have h : p∣23*(31) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 23)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h))
    have horb : p^(5+1)∣(orbit 23 (24,5) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid23_1_23 low ((pow_dvd_pow 23 (by decide : 5≤5+1)).trans horb)
      · exact avoid23_1_31 low ((pow_dvd_pow 31 (by decide : 1≤5+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid23_91_23 low ((pow_dvd_pow 23 (by decide : 5≤5+1)).trans horb)
      · exact avoid23_91_31 low ((pow_dvd_pow 31 (by decide : 1≤5+1)).trans horb)
  have limK : k<48 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<713^5) dv
    have : 713^5<2^48 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(91,19)] : List (ℕ×ℕ)), ∀ i : Fin 48,
      (orbit 23 (24,5) s i.val).2∣713^5 → (orbit 23 (24,5) s i.val).1≤1 := by decide +kernel
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
private theorem avoid24_1_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 6 (5,2) (1,2) k).2 := by
  have h0 : Good 6 31 32 (5,2) (1,2) [5, 21] :=
    lift (t:=1) (s:=32) (good_one 6 (5,2) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 961 992 (5,2) (1,2) [261, 757] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 6 29791 30752 (5,2) (1,2) [8693, 24069] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 6 923521 953312 (5,2) (1,2) [70197, 546853] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 6 28629151 29552672 (5,2) (1,2) [9126661, 23902997] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid24_19_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 6 (5,2) (19,8) k).2 := by
  have h0 : Good 6 31 32 (5,2) (19,8) [10, 26] :=
    lift (t:=1) (s:=32) (good_one 6 (5,2) (19,8)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 961 992 (5,2) (19,8) [234, 730] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 6 29791 30752 (5,2) (19,8) [6682, 22058] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 6 923521 953312 (5,2) (19,8) [406458, 883114] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 6 28629151 29552672 (5,2) (19,8) [5649674, 20426010] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth24 {x y : ℕ} (eqn : x^2+23=6*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣186) : x≤29 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent24 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣186^24 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=3 ∨ p=31 := by
      have h : p∣2*(3*(31)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 3)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h)))
    have horb : p^(24+1)∣(orbit 6 (5,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid24_1_2 low ((pow_dvd_pow 2 (by decide : 24≤24+1)).trans horb)
      · exact avoid24_1_3 low ((pow_dvd_pow 3 (by decide : 2≤24+1)).trans horb)
      · exact avoid24_1_31 low ((pow_dvd_pow 31 (by decide : 5≤24+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid24_19_2 low ((pow_dvd_pow 2 (by decide : 23≤24+1)).trans horb)
      · exact avoid24_19_3 low ((pow_dvd_pow 3 (by decide : 2≤24+1)).trans horb)
      · exact avoid24_19_31 low ((pow_dvd_pow 31 (by decide : 5≤24+1)).trans horb)
  have limK : k<181 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<186^24) dv
    have : 186^24<2^181 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(19,8)] : List (ℕ×ℕ)), ∀ i : Fin 181,
      (orbit 6 (5,2) s i.val).2∣186^24 → (orbit 6 (5,2) s i.val).1≤29 := by decide +kernel
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
private theorem avoid27_1_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 3 (2,1) (1,3) k).2 := by
  have h0 : Good 3 31 32 (2,1) (1,3) [3, 19] :=
    lift (t:=1) (s:=32) (good_one 3 (2,1) (1,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 961 992 (2,1) (1,3) [35, 531] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 29791 30752 (2,1) (1,3) [7971, 23347] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 923521 953312 (2,1) (1,3) [38723, 515379] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 28629151 29552672 (2,1) (1,3) [8618531, 23394867] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid27_7_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 3 (2,1) (7,5) k).2 := by
  have h0 : Good 3 31 32 (2,1) (7,5) [12, 28] :=
    lift (t:=1) (s:=32) (good_one 3 (2,1) (7,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 961 992 (2,1) (7,5) [460, 956] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 29791 30752 (2,1) (7,5) [7404, 22780] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 923521 953312 (2,1) (7,5) [437932, 914588] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 28629151 29552672 (2,1) (7,5) [6157804, 20934140] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth27 {x y : ℕ} (eqn : x^2+26=3*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣93) : x≤161 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent27 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣93^15 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=3 ∨ p=31 := by
      have h : p∣3*(31) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 3)).mp h)
      ·
        exact Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h))
    have horb : p^(15+1)∣(orbit 3 (2,1) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid27_1_3 low ((pow_dvd_pow 3 (by decide : 15≤15+1)).trans horb)
      · exact avoid27_1_31 low ((pow_dvd_pow 31 (by decide : 5≤15+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid27_7_3 low ((pow_dvd_pow 3 (by decide : 14≤15+1)).trans horb)
      · exact avoid27_7_31 low ((pow_dvd_pow 31 (by decide : 5≤15+1)).trans horb)
  have limK : k<99 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<93^15) dv
    have : 93^15<2^99 := by decide
    omega
  have small : ∀ s ∈ ([(1,3),(7,5)] : List (ℕ×ℕ)), ∀ i : Fin 99,
      (orbit 3 (2,1) s i.val).2∣93^15 → (orbit 3 (2,1) s i.val).1≤161 := by decide +kernel
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
private theorem avoid28_1_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 7 (8,3) (1,2) k).2 := by
  have h0 : Good 7 31 15 (8,3) (1,2) [10] :=
    lift (t:=1) (s:=15) (good_one 7 (8,3) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 961 465 (8,3) (1,2) [355] :=
    lift (t:=15) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 29791 14415 (8,3) (1,2) [13840] :=
    lift (t:=465) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 923521 446865 (8,3) (1,2) [330970] :=
    lift (t:=14415) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 28629151 13852815 (8,3) (1,2) [12396325] :=
    lift (t:=446865) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid28_6_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 7 (8,3) (6,3) k).2 := by
  have h0 : Good 7 31 15 (8,3) (6,3) [13] :=
    lift (t:=1) (s:=15) (good_one 7 (8,3) (6,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 961 465 (8,3) (6,3) [118] :=
    lift (t:=15) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 29791 14415 (8,3) (6,3) [9418] :=
    lift (t:=465) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 923521 446865 (8,3) (6,3) [110323] :=
    lift (t:=14415) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 28629151 13852815 (8,3) (6,3) [4132108] :=
    lift (t:=446865) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid28_15_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 7 (8,3) (15,6) k).2 := by
  have h0 : Good 7 31 15 (8,3) (15,6) [1] :=
    lift (t:=1) (s:=15) (good_one 7 (8,3) (15,6)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 961 465 (8,3) (15,6) [346] :=
    lift (t:=15) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 29791 14415 (8,3) (15,6) [4996] :=
    lift (t:=465) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 923521 446865 (8,3) (15,6) [336541] :=
    lift (t:=14415) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 28629151 13852815 (8,3) (15,6) [9720706] :=
    lift (t:=446865) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid28_34_31 {k : ℕ} (hk : k<2097152) : ¬31^6∣(orbit 7 (8,3) (34,13) k).2 := by
  have h0 : Good 7 31 15 (8,3) (34,13) [4] :=
    lift (t:=1) (s:=15) (good_one 7 (8,3) (34,13)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 961 465 (8,3) (34,13) [109] :=
    lift (t:=15) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 29791 14415 (8,3) (34,13) [574] :=
    lift (t:=465) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 923521 446865 (8,3) (34,13) [115894] :=
    lift (t:=14415) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 28629151 13852815 (8,3) (34,13) [1456489] :=
    lift (t:=446865) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 887503681 429437265 (8,3) (34,13) [56867749] :=
    lift (t:=13852815) (s:=31) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth28 {x y : ℕ} (eqn : x^2+27=7*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣434) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent28 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣434^10 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=7 ∨ p=31 := by
      have h : p∣2*(7*(31)) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 7)).mp h))
        ·
          exact Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h)))
    have horb : p^(10+1)∣(orbit 7 (8,3) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid28_1_2 low ((pow_dvd_pow 2 (by decide : 2≤10+1)).trans horb)
      · exact avoid28_1_7 low ((pow_dvd_pow 7 (by decide : 10≤10+1)).trans horb)
      · exact avoid28_1_31 low ((pow_dvd_pow 31 (by decide : 5≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid28_6_2 low ((pow_dvd_pow 2 (by decide : 2≤10+1)).trans horb)
      · exact avoid28_6_7 low ((pow_dvd_pow 7 (by decide : 8≤10+1)).trans horb)
      · exact avoid28_6_31 low ((pow_dvd_pow 31 (by decide : 5≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid28_15_2 low ((pow_dvd_pow 2 (by decide : 2≤10+1)).trans horb)
      · exact avoid28_15_7 low ((pow_dvd_pow 7 (by decide : 9≤10+1)).trans horb)
      · exact avoid28_15_31 low ((pow_dvd_pow 31 (by decide : 5≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid28_34_2 low ((pow_dvd_pow 2 (by decide : 2≤10+1)).trans horb)
      · exact avoid28_34_7 low ((pow_dvd_pow 7 (by decide : 8≤10+1)).trans horb)
      · exact avoid28_34_31 low ((pow_dvd_pow 31 (by decide : 6≤10+1)).trans horb)
  have limK : k<88 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<434^10) dv
    have : 434^10<2^88 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(6,3),(15,6),(34,13)] : List (ℕ×ℕ)), ∀ i : Fin 88,
      (orbit 7 (8,3) s i.val).2∣434^10 → (orbit 7 (8,3) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent30 {x y : ℕ} (eqn : x^2+29=30*y^2) :
    ∃ s ∈ ([(1,1),(49,9)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 30 (11,2) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<11
    · have hx : x<55 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤10 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 55, ∀ j : Fin 11, i.val^2+29=30*j.val^2 →
          (i.val,j.val)∈([(1,1),(49,9)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 11^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 60*y≤11*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 2*x≤11*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 10*y<2*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 11*x-60*y
    let v := 11*y-2*x
    have hu : u+60*y=11*x := Nat.sub_add_cancel ax
    have hv : v+2*x=11*y := Nat.sub_add_cancel ay
    have ev : u^2+29=30*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid30_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 30 (11,2) (1,1) k).2 := by
  have h0 : Good 30 2 1 (11,2) (1,1) [] :=
    lift (t:=1) (s:=1) (good_one 30 (11,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid30_1_3 {k : ℕ} (hk : k<2097152) : ¬3^14∣(orbit 30 (11,2) (1,1) k).2 := by
  have h0 : Good 30 3 6 (11,2) (1,1) [2, 5] :=
    lift (t:=1) (s:=6) (good_one 30 (11,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 30 9 18 (11,2) (1,1) [8, 17] :=
    lift (t:=6) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 30 27 54 (11,2) (1,1) [17, 44] :=
    lift (t:=18) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 30 81 162 (11,2) (1,1) [71, 152] :=
    lift (t:=54) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 30 243 486 (11,2) (1,1) [152, 395] :=
    lift (t:=162) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 30 729 1458 (11,2) (1,1) [395, 1124] :=
    lift (t:=486) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 30 2187 4374 (11,2) (1,1) [1853, 4040] :=
    lift (t:=1458) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 30 6561 13122 (11,2) (1,1) [4040, 10601] :=
    lift (t:=4374) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 30 19683 39366 (11,2) (1,1) [10601, 30284] :=
    lift (t:=13122) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 30 59049 118098 (11,2) (1,1) [30284, 89333] :=
    lift (t:=39366) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 30 177147 354294 (11,2) (1,1) [30284, 207431] :=
    lift (t:=118098) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 30 531441 1062882 (11,2) (1,1) [30284, 561725] :=
    lift (t:=354294) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 30 1594323 3188646 (11,2) (1,1) [1093166, 2687489] :=
    lift (t:=1062882) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 30 4782969 9565938 (11,2) (1,1) [4281812, 9064781] :=
    lift (t:=3188646) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h13 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid30_1_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 30 (11,2) (1,1) k).2 := by
  have h0 : Good 30 5 5 (11,2) (1,1) [2] :=
    lift (t:=1) (s:=5) (good_one 30 (11,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 30 25 25 (11,2) (1,1) [22] :=
    lift (t:=5) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 30 125 125 (11,2) (1,1) [22] :=
    lift (t:=25) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 30 625 625 (11,2) (1,1) [147] :=
    lift (t:=125) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 30 3125 3125 (11,2) (1,1) [772] :=
    lift (t:=625) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 30 15625 15625 (11,2) (1,1) [3897] :=
    lift (t:=3125) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 30 78125 78125 (11,2) (1,1) [50772] :=
    lift (t:=15625) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 30 390625 390625 (11,2) (1,1) [128897] :=
    lift (t:=78125) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 30 1953125 1953125 (11,2) (1,1) [128897] :=
    lift (t:=390625) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 30 9765625 9765625 (11,2) (1,1) [5988272] :=
    lift (t:=1953125) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid30_1_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 30 (11,2) (1,1) k).2 := by
  have h0 : Good 30 31 32 (11,2) (1,1) [12, 28] :=
    lift (t:=1) (s:=32) (good_one 30 (11,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 30 961 992 (11,2) (1,1) [188, 684] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 30 29791 30752 (11,2) (1,1) [5644, 21020] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 30 923521 953312 (11,2) (1,1) [82524, 559180] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 30 28629151 29552672 (11,2) (1,1) [8185676, 22962012] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid30_49_2 {k : ℕ} (_hk : k<2097152) : ¬2^1∣(orbit 30 (11,2) (49,9) k).2 := by
  have h0 : Good 30 2 1 (11,2) (49,9) [] :=
    lift (t:=1) (s:=1) (good_one 30 (11,2) (49,9)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid30_49_3 {k : ℕ} (hk : k<2097152) : ¬3^16∣(orbit 30 (11,2) (49,9) k).2 := by
  have h0 : Good 30 3 6 (11,2) (49,9) [0, 3] :=
    lift (t:=1) (s:=6) (good_one 30 (11,2) (49,9)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 30 9 18 (11,2) (49,9) [0, 9] :=
    lift (t:=6) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 30 27 54 (11,2) (49,9) [9, 36] :=
    lift (t:=18) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 30 81 162 (11,2) (49,9) [9, 90] :=
    lift (t:=54) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 30 243 486 (11,2) (49,9) [90, 333] :=
    lift (t:=162) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 30 729 1458 (11,2) (49,9) [333, 1062] :=
    lift (t:=486) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 30 2187 4374 (11,2) (49,9) [333, 2520] :=
    lift (t:=1458) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 30 6561 13122 (11,2) (49,9) [2520, 9081] :=
    lift (t:=4374) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 30 19683 39366 (11,2) (49,9) [9081, 28764] :=
    lift (t:=13122) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 30 59049 118098 (11,2) (49,9) [28764, 87813] :=
    lift (t:=39366) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 30 177147 354294 (11,2) (49,9) [146862, 324009] :=
    lift (t:=118098) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 30 531441 1062882 (11,2) (49,9) [501156, 1032597] :=
    lift (t:=354294) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 30 1594323 3188646 (11,2) (49,9) [501156, 2095479] :=
    lift (t:=1062882) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 30 4782969 9565938 (11,2) (49,9) [501156, 5284125] :=
    lift (t:=3188646) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 30 14348907 28697814 (11,2) (49,9) [501156, 14850063] :=
    lift (t:=9565938) (s:=3) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h15 : Good 30 43046721 86093442 (11,2) (49,9) [14850063, 57896784] :=
    lift (t:=28697814) (s:=3) (h14) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h15 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid30_49_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 30 (11,2) (49,9) k).2 := by
  have h0 : Good 30 5 5 (11,2) (49,9) [2] :=
    lift (t:=1) (s:=5) (good_one 30 (11,2) (49,9)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 30 25 25 (11,2) (49,9) [2] :=
    lift (t:=5) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 30 125 125 (11,2) (49,9) [102] :=
    lift (t:=25) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 30 625 625 (11,2) (49,9) [477] :=
    lift (t:=125) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 30 3125 3125 (11,2) (49,9) [2352] :=
    lift (t:=625) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 30 15625 15625 (11,2) (49,9) [11727] :=
    lift (t:=3125) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 30 78125 78125 (11,2) (49,9) [27352] :=
    lift (t:=15625) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 30 390625 390625 (11,2) (49,9) [261727] :=
    lift (t:=78125) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 30 1953125 1953125 (11,2) (49,9) [1824227] :=
    lift (t:=390625) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 30 9765625 9765625 (11,2) (49,9) [3777352] :=
    lift (t:=1953125) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid30_49_31 {k : ℕ} (hk : k<2097152) : ¬31^5∣(orbit 30 (11,2) (49,9) k).2 := by
  have h0 : Good 30 31 32 (11,2) (49,9) [3, 19] :=
    lift (t:=1) (s:=32) (good_one 30 (11,2) (49,9)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 30 961 992 (11,2) (49,9) [307, 803] :=
    lift (t:=32) (s:=31) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 30 29791 30752 (11,2) (49,9) [9731, 25107] :=
    lift (t:=992) (s:=31) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 30 923521 953312 (11,2) (49,9) [394131, 870787] :=
    lift (t:=30752) (s:=31) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 30 28629151 29552672 (11,2) (49,9) [6590659, 21366995] :=
    lift (t:=953312) (s:=31) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth30 {x y : ℕ} (eqn : x^2+29=30*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣930) : x≤49 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent30 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣930^16 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tags : p=2 ∨ p=3 ∨ p=5 ∨ p=31 := by
      have h : p∣2*(3*(5*(31))) := dr
      rcases pp.dvd_mul.mp h with h|h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 2)).mp h)
      ·
        rcases pp.dvd_mul.mp h with h|h
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 3)).mp h))
        ·
          rcases pp.dvd_mul.mp h with h|h
          · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 5)).mp h)))
          ·
            exact Or.inr (Or.inr (Or.inr (((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 31)).mp h))))
    have horb : p^(16+1)∣(orbit 30 (11,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl|rfl
      · exact avoid30_1_2 low ((pow_dvd_pow 2 (by decide : 1≤16+1)).trans horb)
      · exact avoid30_1_3 low ((pow_dvd_pow 3 (by decide : 14≤16+1)).trans horb)
      · exact avoid30_1_5 low ((pow_dvd_pow 5 (by decide : 10≤16+1)).trans horb)
      · exact avoid30_1_31 low ((pow_dvd_pow 31 (by decide : 5≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl|rfl
      · exact avoid30_49_2 low ((pow_dvd_pow 2 (by decide : 1≤16+1)).trans horb)
      · exact avoid30_49_3 low ((pow_dvd_pow 3 (by decide : 16≤16+1)).trans horb)
      · exact avoid30_49_5 low ((pow_dvd_pow 5 (by decide : 10≤16+1)).trans horb)
      · exact avoid30_49_31 low ((pow_dvd_pow 31 (by decide : 5≤16+1)).trans horb)
  have limK : k<158 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<930^16) dv
    have : 930^16<2^158 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(49,9)] : List (ℕ×ℕ)), ∀ i : Fin 158,
      (orbit 30 (11,2) s i.val).2∣930^16 → (orbit 30 (11,2) s i.val).1≤49 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


end Erdos889.SquareThirtyOne


namespace Erdos889.SquareThirtyOne
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem extract {n j R : ℕ} (div : 25878772920∣n) (hj : 0<j) (lj : j≤30)
    (rad : ∀ p : Fin 31, p.val.Prime → p.val∣j → p.val∣R) (large : 31∣R)
    (pos : R≠0) (hit : 31∣n+j) (sol : v_l 1 n=1) :
    ∃ D y : ℕ, D∣R ∧ D*y^2=n+j ∧ (∀ p : ℕ, p.Prime → p∣y → p∣R) := by
  have sup (p : ℕ) (pp : p.Prime) (hd : p∣n+j) : p∣R := by
    by_cases small : p≤j
    · have t : ∀ t : Fin 31, t.val.Prime → t.val∣25878772920 := by decide
      have dp := (t ⟨p,by omega⟩ pp).trans div
      exact rad ⟨p,by omega⟩ pp ((Nat.dvd_add_iff_right dp).mpr hd)
    · by_cases same : p=31
      · exact same ▸ large
      exact False.elim (two_primes hj pp (by decide : Nat.Prime 31) same (by omega) (by omega) hd hit sol)
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
    (shape : n+1=p^2) (one : 2≤D) (small : j≤30) (big : 100<p) :
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

private theorem reject4 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+4) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=62) div (by decide : 0<4) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (m:=21) fac dr (by decide) (by decide)
    ((by decide : 21∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : y^2=p^2+3 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

private theorem reject7 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+7) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=217) div (by decide : 0<7) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=7 := coefficient (m:=20) fac dr (by decide) (by decide)
    ((by decide : 20∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+6=7*y^2 := by omega
  have h := smooth7 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject12 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+12) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=186) div (by decide : 0<12) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=3 := coefficient (m:=280) fac dr (by decide) (by decide)
    ((by decide : 280∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+11=3*y^2 := by omega
  have h := smooth12 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject13 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+13) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=403) div (by decide : 0<13) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=13 := coefficient (m:=8) fac dr (by decide) (by decide)
    ((by decide : 8∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+12=13*y^2 := by omega
  have h := smooth13 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject14 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+14) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=434) div (by decide : 0<14) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=14 := coefficient (m:=40) fac dr (by decide) (by decide)
    ((by decide : 40∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+13=14*y^2 := by omega
  have h := smooth14 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject16 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+16) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=62) div (by decide : 0<16) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (m:=21) fac dr (by decide) (by decide)
    ((by decide : 21∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : y^2=p^2+15 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

private theorem reject18 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+18) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=186) div (by decide : 0<18) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=2 := coefficient (m:=40) fac dr (by decide) (by decide)
    ((by decide : 40∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+17=2*y^2 := by omega
  have h := smooth18 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject22 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+22) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=682) div (by decide : 0<22) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=22 := coefficient (m:=24) fac dr (by decide) (by decide)
    ((by decide : 24∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+21=22*y^2 := by omega
  have h := smooth22 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject23 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+23) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=713) div (by decide : 0<23) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=23 := coefficient (m:=12) fac dr (by decide) (by decide)
    ((by decide : 12∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+22=23*y^2 := by omega
  have h := smooth23 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject24 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+24) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=186) div (by decide : 0<24) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=6 := coefficient (m:=385) fac dr (by decide) (by decide)
    ((by decide : 385∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+23=6*y^2 := by omega
  have h := smooth24 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject25 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+25) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=155) div (by decide : 0<25) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (m:=8) fac dr (by decide) (by decide)
    ((by decide : 8∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : y^2=p^2+24 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

private theorem reject27 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+27) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=93) div (by decide : 0<27) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=3 := coefficient (m:=8) fac dr (by decide) (by decide)
    ((by decide : 8∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+26=3*y^2 := by omega
  have h := smooth27 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject28 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+28) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=434) div (by decide : 0<28) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=7 := coefficient (m:=195) fac dr (by decide) (by decide)
    ((by decide : 195∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+27=7*y^2 := by omega
  have h := smooth28 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject30 {n p : ℕ} (big : 10000000<p) (div : 25878772920∣n) (shape : n+1=p^2)
    (hit : 31∣n+30) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=930) div (by decide : 0<30) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=30 := coefficient (m:=728) fac dr (by decide) (by decide)
    ((by decide : 728∣25878772920).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+29=30*y^2 := by omega
  have h := smooth30 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxHeartbeats 2000000 in
/-- Any further solution with a prime-square successor is divisible by every prime through 31. -/
theorem square_multiple_of_802241960520 {n p : ℕ} (big : 330<n) (pp : p.Prime)
    (shape : n+1=p^2) (sol : v_l 1 n=1) : 802241960520∣n := by
  have div := Erdos889.SquareTwentyNine.square_multiple_of_25878772920 big pp shape sol
  have huge := (Erdos889.MissingPrimeSieve.further_solution_bounds_thirty big sol).1
  have large : 10000000<p := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have nz : ¬31∣p := by
    intro dvd
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 31) pp).mp dvd
    omega
  have thirtyOne : 31∣n := by
    by_contra miss
    have alts : 31∣n+4 ∨ 31∣n+7 ∨ 31∣n+12 ∨ 31∣n+13 ∨ 31∣n+14 ∨ 31∣n+16 ∨ 31∣n+18 ∨ 31∣n+22 ∨ 31∣n+23 ∨ 31∣n+24 ∨ 31∣n+25 ∨ 31∣n+27 ∨ 31∣n+28 ∨ 31∣n+30 := by
      have table : ∀ a b : Fin 31, (a.val+1)%31=(b.val^2)%31 →
          a.val≠0 → b.val≠0 → 31∣a.val+4 ∨ 31∣a.val+7 ∨ 31∣a.val+12 ∨ 31∣a.val+13 ∨ 31∣a.val+14 ∨ 31∣a.val+16 ∨ 31∣a.val+18 ∨ 31∣a.val+22 ∨ 31∣a.val+23 ∨ 31∣a.val+24 ∨ 31∣a.val+25 ∨ 31∣a.val+27 ∨ 31∣a.val+28 ∨ 31∣a.val+30 := by decide +kernel
      have localProof := table ⟨n%31,Nat.mod_lt _ (by decide)⟩ ⟨p%31,Nat.mod_lt _ (by decide)⟩
        (by dsimp; rw [Nat.mod_add_mod,shape,Nat.pow_mod p 2 31])
        (fun h => miss (Nat.dvd_of_mod_eq_zero h)) (fun h => nz (Nat.dvd_of_mod_eq_zero h))
      simpa only [Nat.dvd_iff_mod_eq_zero,Nat.mod_add_mod] using localProof
    rcases alts with h|h|h|h|h|h|h|h|h|h|h|h|h|h
    · exact reject4 large div shape h sol
    · exact reject7 large div shape h sol
    · exact reject12 large div shape h sol
    · exact reject13 large div shape h sol
    · exact reject14 large div shape h sol
    · exact reject16 large div shape h sol
    · exact reject18 large div shape h sol
    · exact reject22 large div shape h sol
    · exact reject23 large div shape h sol
    · exact reject24 large div shape h sol
    · exact reject25 large div shape h sol
    · exact reject27 large div shape h sol
    · exact reject28 large div shape h sol
    · exact reject30 large div shape h sol
  omega

theorem prime_square_outside_802241960520 {n p : ℕ} (pp : p.Prime) (shape : n+1=p^2)
    (miss : ¬802241960520∣n) : v_l 1 n=1 ↔ n∈[3,8,24,48,120] := by
  by_cases large : 330<n
  · constructor
    · intro sol
      exact (miss (square_multiple_of_802241960520 large pp shape sol)).elim
    · intro mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      omega
  · apply Erdos889.SquareTwentyNine.prime_square_outside_25878772920 pp shape
    have := Nat.pow_le_pow_left pp.two_le 2
    omega
end Erdos889.SquareThirtyOne

#print axioms Erdos889.SquareThirtyOne.prime_square_outside_802241960520
