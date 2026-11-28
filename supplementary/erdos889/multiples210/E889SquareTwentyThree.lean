import E889SquareNineteen

/-! Prime-square successor solutions when 23 is the first missing prime. -/

namespace Erdos889.SquareTwentyThree

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
private theorem avoid6_1_23 {k : ℕ} (hk : k<2097152) : ¬23^5∣(orbit 6 (5,2) (1,1) k).2 := by
  have h0 : Good 6 23 11 (5,2) (1,1) [2] :=
    lift (t:=1) (s:=11) (good_one 6 (5,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 529 253 (5,2) (1,1) [244] :=
    lift (t:=11) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 6 12167 5819 (5,2) (1,1) [1509] :=
    lift (t:=253) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 6 279841 133837 (5,2) (1,1) [59699] :=
    lift (t:=5819) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 6 6436343 3078251 (5,2) (1,1) [2468765] :=
    lift (t:=133837) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid6_7_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 6 (5,2) (7,3) k).2 := by
  have h0 : Good 6 23 11 (5,2) (7,3) [8] :=
    lift (t:=1) (s:=11) (good_one 6 (5,2) (7,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 529 253 (5,2) (7,3) [8] :=
    lift (t:=11) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 6 12167 5819 (5,2) (7,3) [4309] :=
    lift (t:=253) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 6 279841 133837 (5,2) (7,3) [74137] :=
    lift (t:=5819) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 6 6436343 3078251 (5,2) (7,3) [609485] :=
    lift (t:=133837) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 6 148035889 70799773 (5,2) (7,3) [31391995] :=
    lift (t:=3078251) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth6 {x y : ℕ} (eqn : x^2+5=6*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣138) : x≤169 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent6 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣138^6 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 139, i.val.Prime → i.val∣138 → i.val=2 ∨ i.val=3 ∨ i.val=23 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=3 ∨ p=23 at tags
    have horb : p^(6+1)∣(orbit 6 (5,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid6_1_2 low ((pow_dvd_pow 2 (by decide : 1≤6+1)).trans horb)
      · exact avoid6_1_3 low ((pow_dvd_pow 3 (by decide : 2≤6+1)).trans horb)
      · exact avoid6_1_23 low ((pow_dvd_pow 23 (by decide : 5≤6+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid6_7_2 low ((pow_dvd_pow 2 (by decide : 1≤6+1)).trans horb)
      · exact avoid6_7_3 low ((pow_dvd_pow 3 (by decide : 2≤6+1)).trans horb)
      · exact avoid6_7_23 low ((pow_dvd_pow 23 (by decide : 6≤6+1)).trans horb)
  have limK : k<43 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<138^6) dv
    have : 138^6<2^43 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(7,3)] : List (ℕ×ℕ)), ∀ i : Fin 43,
      (orbit 6 (5,2) s i.val).2∣138^6 → (orbit 6 (5,2) s i.val).1≤169 := by decide +kernel
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
private theorem avoid8_1_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 2 (3,2) (1,2) k).2 := by
  have h0 : Good 2 23 11 (3,2) (1,2) [2] :=
    lift (t:=1) (s:=11) (good_one 2 (3,2) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 529 253 (3,2) (1,2) [233] :=
    lift (t:=11) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 12167 5819 (3,2) (1,2) [1245] :=
    lift (t:=253) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 279841 133837 (3,2) (1,2) [129263] :=
    lift (t:=5819) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 6436343 3078251 (3,2) (1,2) [1735307] :=
    lift (t:=133837) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 148035889 70799773 (3,2) (1,2) [60222076] :=
    lift (t:=3078251) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
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
private theorem avoid8_5_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 2 (3,2) (5,4) k).2 := by
  have h0 : Good 2 23 11 (3,2) (5,4) [8] :=
    lift (t:=1) (s:=11) (good_one 2 (3,2) (5,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 529 253 (3,2) (5,4) [19] :=
    lift (t:=11) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 12167 5819 (3,2) (5,4) [4573] :=
    lift (t:=253) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 279841 133837 (3,2) (5,4) [4573] :=
    lift (t:=5819) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 6436343 3078251 (3,2) (5,4) [1342943] :=
    lift (t:=133837) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 148035889 70799773 (3,2) (5,4) [10577696] :=
    lift (t:=3078251) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth8 {x y : ℕ} (eqn : x^2+7=2*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣46) : x≤181 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent8 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣46^24 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 47, i.val.Prime → i.val∣46 → i.val=2 ∨ i.val=23 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=23 at tags
    have horb : p^(24+1)∣(orbit 2 (3,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid8_1_2 low ((pow_dvd_pow 2 (by decide : 24≤24+1)).trans horb)
      · exact avoid8_1_23 low ((pow_dvd_pow 23 (by decide : 6≤24+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid8_5_2 low ((pow_dvd_pow 2 (by decide : 23≤24+1)).trans horb)
      · exact avoid8_5_23 low ((pow_dvd_pow 23 (by decide : 6≤24+1)).trans horb)
  have limK : k<133 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<46^24) dv
    have : 46^24<2^133 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(5,4)] : List (ℕ×ℕ)), ∀ i : Fin 133,
      (orbit 2 (3,2) s i.val).2∣46^24 → (orbit 2 (3,2) s i.val).1≤181 := by decide +kernel
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
private theorem avoid11_1_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 11 (10,3) (1,1) k).2 := by
  have h0 : Good 11 23 24 (10,3) (1,1) [5, 17] :=
    lift (t:=1) (s:=24) (good_one 11 (10,3) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 11 529 552 (10,3) (1,1) [185, 461] :=
    lift (t:=24) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 11 12167 12696 (10,3) (1,1) [185, 6533] :=
    lift (t:=552) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 11 279841 292008 (10,3) (1,1) [114449, 260453] :=
    lift (t:=12696) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 11 6436343 6716184 (10,3) (1,1) [1428485, 4786577] :=
    lift (t:=292008) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 11 148035889 154472232 (10,3) (1,1) [4786577, 82022693] :=
    lift (t:=6716184) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
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
private theorem avoid11_23_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 11 (10,3) (23,7) k).2 := by
  have h0 : Good 11 23 24 (10,3) (23,7) [6, 18] :=
    lift (t:=1) (s:=24) (good_one 11 (10,3) (23,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 11 529 552 (10,3) (23,7) [90, 366] :=
    lift (t:=24) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 11 12167 12696 (10,3) (23,7) [6162, 12510] :=
    lift (t:=552) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 11 279841 292008 (10,3) (23,7) [31554, 177558] :=
    lift (t:=12696) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 11 6436343 6716184 (10,3) (23,7) [1929606, 5287698] :=
    lift (t:=292008) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 11 148035889 154472232 (10,3) (23,7) [72449538, 149685654] :=
    lift (t:=6716184) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth11 {x y : ℕ} (eqn : x^2+10=11*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣253) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent11 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣253^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 254, i.val.Prime → i.val∣253 → i.val=11 ∨ i.val=23 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=11 ∨ p=23 at tags
    have horb : p^(7+1)∣(orbit 11 (10,3) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl
      · exact avoid11_1_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid11_1_23 low ((pow_dvd_pow 23 (by decide : 6≤7+1)).trans horb)
    · rcases tags with rfl|rfl
      · exact avoid11_23_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid11_23_23 low ((pow_dvd_pow 23 (by decide : 6≤7+1)).trans horb)
  have limK : k<56 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<253^7) dv
    have : 253^7<2^56 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(23,7)] : List (ℕ×ℕ)), ∀ i : Fin 56,
      (orbit 11 (10,3) s i.val).2∣253^7 → (orbit 11 (10,3) s i.val).1≤1 := by decide +kernel
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
private theorem avoid12_1_23 {k : ℕ} (hk : k<2097152) : ¬23^5∣(orbit 3 (2,1) (1,2) k).2 := by
  have h0 : Good 3 23 11 (2,1) (1,2) [7] :=
    lift (t:=1) (s:=11) (good_one 3 (2,1) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 529 253 (2,1) (1,2) [95] :=
    lift (t:=11) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 12167 5819 (2,1) (1,2) [4649] :=
    lift (t:=253) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 279841 133837 (2,1) (1,2) [45382] :=
    lift (t:=5819) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 6436343 3078251 (2,1) (1,2) [2320611] :=
    lift (t:=133837) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid12_4_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 3 (2,1) (4,3) k).2 := by
  have h0 : Good 3 23 11 (2,1) (4,3) [3] :=
    lift (t:=1) (s:=11) (good_one 3 (2,1) (4,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 3 529 253 (2,1) (4,3) [157] :=
    lift (t:=11) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 3 12167 5819 (2,1) (4,3) [1169] :=
    lift (t:=253) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 3 279841 133837 (2,1) (4,3) [88454] :=
    lift (t:=5819) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 3 6436343 3078251 (2,1) (4,3) [757639] :=
    lift (t:=133837) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 3 148035889 70799773 (2,1) (4,3) [62322659] :=
    lift (t:=3078251) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth12 {x y : ℕ} (eqn : x^2+11=3*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣138) : x≤239 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent12 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣138^16 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 139, i.val.Prime → i.val∣138 → i.val=2 ∨ i.val=3 ∨ i.val=23 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=3 ∨ p=23 at tags
    have horb : p^(16+1)∣(orbit 3 (2,1) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid12_1_2 low ((pow_dvd_pow 2 (by decide : 2≤16+1)).trans horb)
      · exact avoid12_1_3 low ((pow_dvd_pow 3 (by decide : 16≤16+1)).trans horb)
      · exact avoid12_1_23 low ((pow_dvd_pow 23 (by decide : 5≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid12_4_2 low ((pow_dvd_pow 2 (by decide : 2≤16+1)).trans horb)
      · exact avoid12_4_3 low ((pow_dvd_pow 3 (by decide : 14≤16+1)).trans horb)
      · exact avoid12_4_23 low ((pow_dvd_pow 23 (by decide : 6≤16+1)).trans horb)
  have limK : k<114 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<138^16) dv
    have : 138^16<2^114 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(4,3)] : List (ℕ×ℕ)), ∀ i : Fin 114,
      (orbit 3 (2,1) s i.val).2∣138^16 → (orbit 3 (2,1) s i.val).1≤239 := by decide +kernel
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
private theorem avoid15_1_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 15 (4,1) (1,1) k).2 := by
  have h0 : Good 15 23 24 (4,1) (1,1) [10, 22] :=
    lift (t:=1) (s:=24) (good_one 15 (4,1) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 15 529 552 (4,1) (1,1) [34, 310] :=
    lift (t:=24) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 15 12167 12696 (4,1) (1,1) [2242, 8590] :=
    lift (t:=552) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 15 279841 292008 (4,1) (1,1) [27634, 173638] :=
    lift (t:=12696) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 15 6436343 6716184 (4,1) (1,1) [757654, 4115746] :=
    lift (t:=292008) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 15 148035889 154472232 (4,1) (1,1) [17548114, 94784230] :=
    lift (t:=6716184) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid15_11_23 {k : ℕ} (hk : k<2097152) : ¬23^5∣(orbit 15 (4,1) (11,3) k).2 := by
  have h0 : Good 15 23 24 (4,1) (11,3) [1, 13] :=
    lift (t:=1) (s:=24) (good_one 15 (4,1) (11,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 15 529 552 (4,1) (11,3) [241, 517] :=
    lift (t:=24) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 15 12167 12696 (4,1) (11,3) [4105, 10453] :=
    lift (t:=552) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 15 279841 292008 (4,1) (11,3) [118369, 264373] :=
    lift (t:=12696) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 15 6436343 6716184 (4,1) (11,3) [2600437, 5958529] :=
    lift (t:=292008) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth15 {x y : ℕ} (eqn : x^2+14=15*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣345) : x≤89 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent15 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣345^10 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 346, i.val.Prime → i.val∣345 → i.val=3 ∨ i.val=5 ∨ i.val=23 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=3 ∨ p=5 ∨ p=23 at tags
    have horb : p^(10+1)∣(orbit 15 (4,1) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid15_1_3 low ((pow_dvd_pow 3 (by decide : 2≤10+1)).trans horb)
      · exact avoid15_1_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid15_1_23 low ((pow_dvd_pow 23 (by decide : 6≤10+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid15_11_3 low ((pow_dvd_pow 3 (by decide : 2≤10+1)).trans horb)
      · exact avoid15_11_5 low ((pow_dvd_pow 5 (by decide : 10≤10+1)).trans horb)
      · exact avoid15_11_23 low ((pow_dvd_pow 23 (by decide : 5≤10+1)).trans horb)
  have limK : k<85 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<345^10) dv
    have : 345^10<2^85 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(11,3)] : List (ℕ×ℕ)), ∀ i : Fin 85,
      (orbit 15 (4,1) s i.val).2∣345^10 → (orbit 15 (4,1) s i.val).1≤89 := by decide +kernel
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
private theorem avoid18_1_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 2 (3,2) (1,3) k).2 := by
  have h0 : Good 2 23 11 (3,2) (1,3) [4] :=
    lift (t:=1) (s:=11) (good_one 2 (3,2) (1,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 529 253 (3,2) (1,3) [92] :=
    lift (t:=11) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 12167 5819 (3,2) (1,3) [4646] :=
    lift (t:=253) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 279841 133837 (3,2) (1,3) [51198] :=
    lift (t:=5819) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 6436343 3078251 (3,2) (1,3) [1924916] :=
    lift (t:=133837) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 148035889 70799773 (3,2) (1,3) [60411685] :=
    lift (t:=3078251) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
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
private theorem avoid18_9_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 2 (3,2) (9,7) k).2 := by
  have h0 : Good 2 23 11 (3,2) (9,7) [6] :=
    lift (t:=1) (s:=11) (good_one 2 (3,2) (9,7)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 529 253 (3,2) (9,7) [160] :=
    lift (t:=11) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 12167 5819 (3,2) (9,7) [1172] :=
    lift (t:=253) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 279841 133837 (3,2) (9,7) [82638] :=
    lift (t:=5819) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 6436343 3078251 (3,2) (9,7) [1153334] :=
    lift (t:=133837) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 148035889 70799773 (3,2) (9,7) [10388087] :=
    lift (t:=3078251) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth18 {x y : ℕ} (eqn : x^2+17=2*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣138) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent18 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣138^16 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 139, i.val.Prime → i.val∣138 → i.val=2 ∨ i.val=3 ∨ i.val=23 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=3 ∨ p=23 at tags
    have horb : p^(16+1)∣(orbit 2 (3,2) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid18_1_2 low ((pow_dvd_pow 2 (by decide : 1≤16+1)).trans horb)
      · exact avoid18_1_3 low ((pow_dvd_pow 3 (by decide : 16≤16+1)).trans horb)
      · exact avoid18_1_23 low ((pow_dvd_pow 23 (by decide : 6≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid18_9_2 low ((pow_dvd_pow 2 (by decide : 1≤16+1)).trans horb)
      · exact avoid18_9_3 low ((pow_dvd_pow 3 (by decide : 14≤16+1)).trans horb)
      · exact avoid18_9_23 low ((pow_dvd_pow 23 (by decide : 6≤16+1)).trans horb)
  have limK : k<114 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<138^16) dv
    have : 138^16<2^114 := by decide
    omega
  have small : ∀ s ∈ ([(1,3),(9,7)] : List (ℕ×ℕ)), ∀ i : Fin 114,
      (orbit 2 (3,2) s i.val).2∣138^16 → (orbit 2 (3,2) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


private theorem descent20 {x y : ℕ} (eqn : x^2+19=5*y^2) :
    ∃ s ∈ ([(1,2),(31,14)] : List (ℕ×ℕ)), ∃ k : ℕ, orbit 5 (9,4) s k=(x,y) ∧ 2^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<18
    · have hx : x<39 := by
        by_contra! high
        have := Nat.pow_le_pow_left high 2
        have := Nat.pow_le_pow_left (show y≤17 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 39, ∀ j : Fin 18, i.val^2+19=5*j.val^2 →
          (i.val,j.val)∈([(1,2),(31,14)] : List (ℕ×ℕ)) := by decide +kernel
      have yp : 0<y := by by_contra! z; rw [show y=0 by omega] at eqn; norm_num at eqn
      exact ⟨(x,y),tab ⟨x,hx⟩ ⟨y,small⟩ eqn,0,orbit_zero _ _ _,by simpa only [pow_zero] using (show 1≤y by omega)⟩
    have low : 18^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
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
    have ev : u^2+19=5*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,lim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · rw [orbit_succ,hk]
      apply Prod.ext <;> dsimp [mul] <;> omega
    · rw [pow_succ]
      omega

private theorem avoid20_1_2 {k : ℕ} (_hk : k<2097152) : ¬2^2∣(orbit 5 (9,4) (1,2) k).2 := by
  have h0 : Good 5 2 1 (9,4) (1,2) [0] :=
    lift (t:=1) (s:=1) (good_one 5 (9,4) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 4 1 (9,4) (1,2) [] :=
    lift (t:=1) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid20_1_5 {k : ℕ} (hk : k<2097152) : ¬5^11∣(orbit 5 (9,4) (1,2) k).2 := by
  have h0 : Good 5 5 10 (9,4) (1,2) [3, 8] :=
    lift (t:=1) (s:=10) (good_one 5 (9,4) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 25 50 (9,4) (1,2) [23, 48] :=
    lift (t:=10) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 5 125 250 (9,4) (1,2) [123, 248] :=
    lift (t:=50) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 5 625 1250 (9,4) (1,2) [373, 998] :=
    lift (t:=250) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 5 3125 6250 (9,4) (1,2) [2248, 5373] :=
    lift (t:=1250) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 5 15625 31250 (9,4) (1,2) [14748, 30373] :=
    lift (t:=6250) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 5 78125 156250 (9,4) (1,2) [14748, 92873] :=
    lift (t:=31250) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 5 390625 781250 (9,4) (1,2) [170998, 561623] :=
    lift (t:=156250) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 5 1953125 3906250 (9,4) (1,2) [561623, 2514748] :=
    lift (t:=781250) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 5 9765625 19531250 (9,4) (1,2) [561623, 10327248] :=
    lift (t:=3906250) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 5 48828125 97656250 (9,4) (1,2) [29858498, 78686623] :=
    lift (t:=19531250) (s:=5) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h10 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid20_1_23 {k : ℕ} (_hk : k<2097152) : ¬23^1∣(orbit 5 (9,4) (1,2) k).2 := by
  have h0 : Good 5 23 8 (9,4) (1,2) [] :=
    lift (t:=1) (s:=8) (good_one 5 (9,4) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm
private theorem avoid20_31_2 {k : ℕ} (_hk : k<2097152) : ¬2^2∣(orbit 5 (9,4) (31,14) k).2 := by
  have h0 : Good 5 2 1 (9,4) (31,14) [0] :=
    lift (t:=1) (s:=1) (good_one 5 (9,4) (31,14)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 4 1 (9,4) (31,14) [] :=
    lift (t:=1) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h1 k h
  exact List.not_mem_nil hm
private theorem avoid20_31_5 {k : ℕ} (hk : k<2097152) : ¬5^10∣(orbit 5 (9,4) (31,14) k).2 := by
  have h0 : Good 5 5 10 (9,4) (31,14) [1, 6] :=
    lift (t:=1) (s:=10) (good_one 5 (9,4) (31,14)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 5 25 50 (9,4) (31,14) [1, 26] :=
    lift (t:=10) (s:=5) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 5 125 250 (9,4) (31,14) [1, 126] :=
    lift (t:=50) (s:=5) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 5 625 1250 (9,4) (31,14) [251, 876] :=
    lift (t:=250) (s:=5) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 5 3125 6250 (9,4) (31,14) [876, 4001] :=
    lift (t:=1250) (s:=5) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 5 15625 31250 (9,4) (31,14) [876, 16501] :=
    lift (t:=6250) (s:=5) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 5 78125 156250 (9,4) (31,14) [63376, 141501] :=
    lift (t:=31250) (s:=5) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 5 390625 781250 (9,4) (31,14) [219626, 610251] :=
    lift (t:=156250) (s:=5) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 5 1953125 3906250 (9,4) (31,14) [1391501, 3344626] :=
    lift (t:=781250) (s:=5) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 5 9765625 19531250 (9,4) (31,14) [9204001, 18969626] :=
    lift (t:=3906250) (s:=5) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h9 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega
private theorem avoid20_31_23 {k : ℕ} (_hk : k<2097152) : ¬23^1∣(orbit 5 (9,4) (31,14) k).2 := by
  have h0 : Good 5 23 8 (9,4) (31,14) [] :=
    lift (t:=1) (s:=8) (good_one 5 (9,4) (31,14)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth20 {x y : ℕ} (eqn : x^2+19=5*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣230) : x≤559 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent20 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣230^11 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 231, i.val.Prime → i.val∣230 → i.val=2 ∨ i.val=5 ∨ i.val=23 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=5 ∨ p=23 at tags
    have horb : p^(11+1)∣(orbit 5 (9,4) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid20_1_2 low ((pow_dvd_pow 2 (by decide : 2≤11+1)).trans horb)
      · exact avoid20_1_5 low ((pow_dvd_pow 5 (by decide : 11≤11+1)).trans horb)
      · exact avoid20_1_23 low ((pow_dvd_pow 23 (by decide : 1≤11+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid20_31_2 low ((pow_dvd_pow 2 (by decide : 2≤11+1)).trans horb)
      · exact avoid20_31_5 low ((pow_dvd_pow 5 (by decide : 10≤11+1)).trans horb)
      · exact avoid20_31_23 low ((pow_dvd_pow 23 (by decide : 1≤11+1)).trans horb)
  have limK : k<87 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<230^11) dv
    have : 230^11<2^87 := by decide
    omega
  have small : ∀ s ∈ ([(1,2),(31,14)] : List (ℕ×ℕ)), ∀ i : Fin 87,
      (orbit 5 (9,4) s i.val).2∣230^11 → (orbit 5 (9,4) s i.val).1≤559 := by decide +kernel
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
private theorem avoid21_1_23 {k : ℕ} (_hk : k<2097152) : ¬23^1∣(orbit 21 (55,12) (1,1) k).2 := by
  have h0 : Good 21 23 8 (55,12) (1,1) [] :=
    lift (t:=1) (s:=8) (good_one 21 (55,12) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid21_8_23 {k : ℕ} (_hk : k<2097152) : ¬23^1∣(orbit 21 (55,12) (8,2) k).2 := by
  have h0 : Good 21 23 8 (55,12) (8,2) [] :=
    lift (t:=1) (s:=8) (good_one 21 (55,12) (8,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid21_13_23 {k : ℕ} (_hk : k<2097152) : ¬23^1∣(orbit 21 (55,12) (13,3) k).2 := by
  have h0 : Good 21 23 8 (55,12) (13,3) [] :=
    lift (t:=1) (s:=8) (good_one 21 (55,12) (13,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid21_41_23 {k : ℕ} (_hk : k<2097152) : ¬23^1∣(orbit 21 (55,12) (41,9) k).2 := by
  have h0 : Good 21 23 8 (55,12) (41,9) [] :=
    lift (t:=1) (s:=8) (good_one 21 (55,12) (41,9)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid21_64_23 {k : ℕ} (_hk : k<2097152) : ¬23^1∣(orbit 21 (55,12) (64,14) k).2 := by
  have h0 : Good 21 23 8 (55,12) (64,14) [] :=
    lift (t:=1) (s:=8) (good_one 21 (55,12) (64,14)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid21_197_23 {k : ℕ} (_hk : k<2097152) : ¬23^1∣(orbit 21 (55,12) (197,43) k).2 := by
  have h0 : Good 21 23 8 (55,12) (197,43) [] :=
    lift (t:=1) (s:=8) (good_one 21 (55,12) (197,43)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h0 k h
  exact List.not_mem_nil hm

set_option maxRecDepth 4096 in
private theorem smooth21 {x y : ℕ} (eqn : x^2+20=21*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣483) : x≤41 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent21 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣483^16 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 484, i.val.Prime → i.val∣483 → i.val=3 ∨ i.val=7 ∨ i.val=23 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=3 ∨ p=7 ∨ p=23 at tags
    have horb : p^(16+1)∣(orbit 21 (55,12) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_1_3 low ((pow_dvd_pow 3 (by decide : 1≤16+1)).trans horb)
      · exact avoid21_1_7 low ((pow_dvd_pow 7 (by decide : 8≤16+1)).trans horb)
      · exact avoid21_1_23 low ((pow_dvd_pow 23 (by decide : 1≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_8_3 low ((pow_dvd_pow 3 (by decide : 1≤16+1)).trans horb)
      · exact avoid21_8_7 low ((pow_dvd_pow 7 (by decide : 8≤16+1)).trans horb)
      · exact avoid21_8_23 low ((pow_dvd_pow 23 (by decide : 1≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_13_3 low ((pow_dvd_pow 3 (by decide : 16≤16+1)).trans horb)
      · exact avoid21_13_7 low ((pow_dvd_pow 7 (by decide : 9≤16+1)).trans horb)
      · exact avoid21_13_23 low ((pow_dvd_pow 23 (by decide : 1≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_41_3 low ((pow_dvd_pow 3 (by decide : 15≤16+1)).trans horb)
      · exact avoid21_41_7 low ((pow_dvd_pow 7 (by decide : 8≤16+1)).trans horb)
      · exact avoid21_41_23 low ((pow_dvd_pow 23 (by decide : 1≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_64_3 low ((pow_dvd_pow 3 (by decide : 1≤16+1)).trans horb)
      · exact avoid21_64_7 low ((pow_dvd_pow 7 (by decide : 8≤16+1)).trans horb)
      · exact avoid21_64_23 low ((pow_dvd_pow 23 (by decide : 1≤16+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid21_197_3 low ((pow_dvd_pow 3 (by decide : 1≤16+1)).trans horb)
      · exact avoid21_197_7 low ((pow_dvd_pow 7 (by decide : 9≤16+1)).trans horb)
      · exact avoid21_197_23 low ((pow_dvd_pow 23 (by decide : 1≤16+1)).trans horb)
  have limK : k<143 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<483^16) dv
    have : 483^16<2^143 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(8,2),(13,3),(41,9),(64,14),(197,43)] : List (ℕ×ℕ)), ∀ i : Fin 143,
      (orbit 21 (55,12) s i.val).2∣483^16 → (orbit 21 (55,12) s i.val).1≤41 := by decide +kernel
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
private theorem avoid22_1_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 22 (197,42) (1,1) k).2 := by
  have h0 : Good 22 23 24 (197,42) (1,1) [3, 15] :=
    lift (t:=1) (s:=24) (good_one 22 (197,42) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 529 552 (197,42) (1,1) [111, 387] :=
    lift (t:=24) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 12167 12696 (197,42) (1,1) [1215, 7563] :=
    lift (t:=552) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 279841 292008 (197,42) (1,1) [109131, 255135] :=
    lift (t:=12696) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 6436343 6716184 (197,42) (1,1) [985155, 4343247] :=
    lift (t:=292008) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 22 148035889 154472232 (197,42) (1,1) [37924167, 115160283] :=
    lift (t:=6716184) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h5 k h
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
private theorem avoid22_23_23 {k : ℕ} (hk : k<2097152) : ¬23^7∣(orbit 22 (197,42) (23,5) k).2 := by
  have h0 : Good 22 23 24 (197,42) (23,5) [6, 18] :=
    lift (t:=1) (s:=24) (good_one 22 (197,42) (23,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 529 552 (197,42) (23,5) [6, 282] :=
    lift (t:=24) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 12167 12696 (197,42) (23,5) [4146, 10494] :=
    lift (t:=552) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 279841 292008 (197,42) (23,5) [124758, 270762] :=
    lift (t:=12696) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 6436343 6716184 (197,42) (23,5) [1584798, 4942890] :=
    lift (t:=292008) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 22 148035889 154472232 (197,42) (23,5) [1584798, 78820914] :=
    lift (t:=6716184) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 22 3404825447 3552861336 (197,42) (23,5) [156057030, 1932487698] :=
    lift (t:=154472232) (s:=23) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h6 k h
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
private theorem avoid22_89_23 {k : ℕ} (hk : k<2097152) : ¬23^6∣(orbit 22 (197,42) (89,19) k).2 := by
  have h0 : Good 22 23 24 (197,42) (89,19) [5, 17] :=
    lift (t:=1) (s:=24) (good_one 22 (197,42) (89,19)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 529 552 (197,42) (89,19) [269, 545] :=
    lift (t:=24) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 12167 12696 (197,42) (89,19) [2201, 8549] :=
    lift (t:=552) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 279841 292008 (197,42) (89,19) [21245, 167249] :=
    lift (t:=12696) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 6436343 6716184 (197,42) (89,19) [1773293, 5131385] :=
    lift (t:=292008) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 22 148035889 154472232 (197,42) (89,19) [75651317, 152887433] :=
    lift (t:=6716184) (s:=23) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
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
private theorem avoid22_727_23 {k : ℕ} (hk : k<2097152) : ¬23^5∣(orbit 22 (197,42) (727,155) k).2 := by
  have h0 : Good 22 23 24 (197,42) (727,155) [8, 20] :=
    lift (t:=1) (s:=24) (good_one 22 (197,42) (727,155)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 22 529 552 (197,42) (727,155) [164, 440] :=
    lift (t:=24) (s:=23) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 22 12167 12696 (197,42) (727,155) [5132, 11480] :=
    lift (t:=552) (s:=23) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 22 279841 292008 (197,42) (727,155) [36872, 182876] :=
    lift (t:=12696) (s:=23) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 22 6436343 6716184 (197,42) (727,155) [2372936, 5731028] :=
    lift (t:=292008) (s:=23) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro h
  have hm := h4 k h
  rw [Nat.mod_eq_of_lt (by omega)] at hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
  omega

set_option maxRecDepth 4096 in
private theorem smooth22 {x y : ℕ} (eqn : x^2+21=22*y^2) (size : y<2^2097152)
    (sup : ∀ p : ℕ, p.Prime → p∣y → p∣506) : x≤1 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent22 eqn
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    omega
  have dv : y∣506^7 := by
    apply smooth_dvd sup
    intro p pp dr h
    have tab : ∀ i : Fin 507, i.val.Prime → i.val∣506 → i.val=2 ∨ i.val=11 ∨ i.val=23 := by decide +kernel
    have tags := tab ⟨p,Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) dr)⟩ pp dr
    change p=2 ∨ p=11 ∨ p=23 at tags
    have horb : p^(7+1)∣(orbit 22 (197,42) s k).2 := by rw [hk]; exact h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hs

    rcases hs with rfl|rfl|rfl|rfl
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_1_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_1_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_1_23 low ((pow_dvd_pow 23 (by decide : 6≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_23_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_23_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_23_23 low ((pow_dvd_pow 23 (by decide : 7≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_89_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_89_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_89_23 low ((pow_dvd_pow 23 (by decide : 6≤7+1)).trans horb)
    · rcases tags with rfl|rfl|rfl
      · exact avoid22_727_2 low ((pow_dvd_pow 2 (by decide : 1≤7+1)).trans horb)
      · exact avoid22_727_11 low ((pow_dvd_pow 11 (by decide : 7≤7+1)).trans horb)
      · exact avoid22_727_23 low ((pow_dvd_pow 23 (by decide : 5≤7+1)).trans horb)
  have limK : k<63 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.le_of_dvd (by decide : 0<506^7) dv
    have : 506^7<2^63 := by decide
    omega
  have small : ∀ s ∈ ([(1,1),(23,5),(89,19),(727,155)] : List (ℕ×ℕ)), ∀ i : Fin 63,
      (orbit 22 (197,42) s i.val).2∣506^7 → (orbit 22 (197,42) s i.val).1≤1 := by decide +kernel
  have result := small s hs ⟨k,limK⟩
  rw [hk] at result
  exact result dv


end Erdos889.SquareTwentyThree


namespace Erdos889.SquareTwentyThree
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem extract {n j R : ℕ} (div : 38798760∣n) (hj : 0<j) (lj : j≤22)
    (rad : ∀ p : Fin 23, p.val.Prime → p.val∣j → p.val∣R) (large : 23∣R)
    (pos : R≠0) (hit : 23∣n+j) (sol : v_l 1 n=1) :
    ∃ D y : ℕ, D∣R ∧ D*y^2=n+j ∧ (∀ p : ℕ, p.Prime → p∣y → p∣R) := by
  have sup (p : ℕ) (pp : p.Prime) (hd : p∣n+j) : p∣R := by
    by_cases small : p≤j
    · have t : ∀ t : Fin 23, t.val.Prime → t.val∣38798760 := by decide
      have dp := (t ⟨p,by omega⟩ pp).trans div
      exact rad ⟨p,by omega⟩ pp ((Nat.dvd_add_iff_right dp).mpr hd)
    · by_cases same : p=23
      · exact same ▸ large
      exact False.elim (two_primes hj pp (by decide : Nat.Prime 23) same (by omega) (by omega) hd hit sol)
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
    (shape : n+1=p^2) (one : 2≤D) (small : j≤22) (big : 100<p) :
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

private theorem reject6 {n p : ℕ} (big : 1000<p) (div : 38798760∣n) (shape : n+1=p^2)
    (hit : 23∣n+6) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=138) div (by decide : 0<6) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=6 := coefficient (m:=56) fac dr (by decide) (by decide)
    ((by decide : 56∣38798760).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+5=6*y^2 := by omega
  have h := smooth6 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject8 {n p : ℕ} (big : 1000<p) (div : 38798760∣n) (shape : n+1=p^2)
    (hit : 23∣n+8) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=46) div (by decide : 0<8) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=2 := coefficient (m:=33) fac dr (by decide) (by decide)
    ((by decide : 33∣38798760).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+7=2*y^2 := by omega
  have h := smooth8 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject11 {n p : ℕ} (big : 1000<p) (div : 38798760∣n) (shape : n+1=p^2)
    (hit : 23∣n+11) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=253) div (by decide : 0<11) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=11 := coefficient (m:=8) fac dr (by decide) (by decide)
    ((by decide : 8∣38798760).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+10=11*y^2 := by omega
  have h := smooth11 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject12 {n p : ℕ} (big : 1000<p) (div : 38798760∣n) (shape : n+1=p^2)
    (hit : 23∣n+12) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=138) div (by decide : 0<12) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=3 := coefficient (m:=280) fac dr (by decide) (by decide)
    ((by decide : 280∣38798760).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+11=3*y^2 := by omega
  have h := smooth12 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject15 {n p : ℕ} (big : 1000<p) (div : 38798760∣n) (shape : n+1=p^2)
    (hit : 23∣n+15) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=345) div (by decide : 0<15) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=15 := coefficient (m:=104) fac dr (by decide) (by decide)
    ((by decide : 104∣38798760).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+14=15*y^2 := by omega
  have h := smooth15 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject16 {n p : ℕ} (big : 1000<p) (div : 38798760∣n) (shape : n+1=p^2)
    (hit : 23∣n+16) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=46) div (by decide : 0<16) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=1 := coefficient (m:=33) fac dr (by decide) (by decide)
    ((by decide : 33∣38798760).trans div) (by decide +kernel)
  subst D
  have eqn : y^2=p^2+15 := by omega
  have hi : p<y := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have bound := Nat.pow_le_pow_left (show p+1≤y by omega) 2
  nlinarith

private theorem reject18 {n p : ℕ} (big : 1000<p) (div : 38798760∣n) (shape : n+1=p^2)
    (hit : 23∣n+18) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=138) div (by decide : 0<18) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=2 := coefficient (m:=56) fac dr (by decide) (by decide)
    ((by decide : 56∣38798760).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+17=2*y^2 := by omega
  have h := smooth18 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject20 {n p : ℕ} (big : 1000<p) (div : 38798760∣n) (shape : n+1=p^2)
    (hit : 23∣n+20) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=230) div (by decide : 0<20) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=5 := coefficient (m:=168) fac dr (by decide) (by decide)
    ((by decide : 168∣38798760).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+19=5*y^2 := by omega
  have h := smooth20 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject21 {n p : ℕ} (big : 1000<p) (div : 38798760∣n) (shape : n+1=p^2)
    (hit : 23∣n+21) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=483) div (by decide : 0<21) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=21 := coefficient (m:=88) fac dr (by decide) (by decide)
    ((by decide : 88∣38798760).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+20=21*y^2 := by omega
  have h := smooth21 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

private theorem reject22 {n p : ℕ} (big : 1000<p) (div : 38798760∣n) (shape : n+1=p^2)
    (hit : 23∣n+22) (sol : v_l 1 n=1) : False := by
  obtain ⟨D,y,dr,fac,sup⟩ := extract (R:=506) div (by decide : 0<22) (by decide)
    (by decide) (by decide) (by decide) hit sol
  have val : D=22 := coefficient (m:=40) fac dr (by decide) (by decide)
    ((by decide : 40∣38798760).trans div) (by decide +kernel)
  subst D
  have eqn : p^2+21=22*y^2 := by omega
  have h := smooth22 eqn (coord_bound sol fac shape (by decide) (by decide) (by omega)) sup
  omega

set_option maxHeartbeats 2000000 in
/-- Any further solution with a prime-square successor is divisible by every prime through 23. -/
theorem square_multiple_of_892371480 {n p : ℕ} (big : 330<n) (pp : p.Prime)
    (shape : n+1=p^2) (sol : v_l 1 n=1) : 892371480∣n := by
  have div := Erdos889.SquareNineteen.square_multiple_of_38798760 big pp shape sol
  have huge := (Erdos889.MissingPrimeSieve.further_solution_bounds_thirty big sol).1
  have large : 1000<p := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have nz : ¬23∣p := by
    intro dvd
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 23) pp).mp dvd
    omega
  have twentyThree : 23∣n := by
    by_contra miss
    have alts : 23∣n+6 ∨ 23∣n+8 ∨ 23∣n+11 ∨ 23∣n+12 ∨ 23∣n+15 ∨ 23∣n+16 ∨ 23∣n+18 ∨ 23∣n+20 ∨ 23∣n+21 ∨ 23∣n+22 := by
      have table : ∀ a b : Fin 23, (a.val+1)%23=(b.val^2)%23 →
          a.val≠0 → b.val≠0 → 23∣a.val+6 ∨ 23∣a.val+8 ∨ 23∣a.val+11 ∨ 23∣a.val+12 ∨ 23∣a.val+15 ∨ 23∣a.val+16 ∨ 23∣a.val+18 ∨ 23∣a.val+20 ∨ 23∣a.val+21 ∨ 23∣a.val+22 := by decide +kernel
      have localProof := table ⟨n%23,Nat.mod_lt _ (by decide)⟩ ⟨p%23,Nat.mod_lt _ (by decide)⟩
        (by dsimp; rw [Nat.mod_add_mod,shape,Nat.pow_mod p 2 23])
        (fun h => miss (Nat.dvd_of_mod_eq_zero h)) (fun h => nz (Nat.dvd_of_mod_eq_zero h))
      simpa only [Nat.dvd_iff_mod_eq_zero,Nat.mod_add_mod] using localProof
    rcases alts with h|h|h|h|h|h|h|h|h|h
    · exact reject6 large div shape h sol
    · exact reject8 large div shape h sol
    · exact reject11 large div shape h sol
    · exact reject12 large div shape h sol
    · exact reject15 large div shape h sol
    · exact reject16 large div shape h sol
    · exact reject18 large div shape h sol
    · exact reject20 large div shape h sol
    · exact reject21 large div shape h sol
    · exact reject22 large div shape h sol
  omega

theorem prime_square_outside_892371480 {n p : ℕ} (pp : p.Prime) (shape : n+1=p^2)
    (miss : ¬892371480∣n) : v_l 1 n=1 ↔ n∈[3,8,24,48,120] := by
  by_cases large : 330<n
  · constructor
    · intro sol
      exact (miss (square_multiple_of_892371480 large pp shape sol)).elim
    · intro mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      omega
  · apply Erdos889.SquareNineteen.prime_square_outside_38798760 pp shape
    have := Nat.pow_le_pow_left pp.two_le 2
    omega
end Erdos889.SquareTwentyThree

#print axioms Erdos889.SquareTwentyThree.prime_square_outside_892371480
