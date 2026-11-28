import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

/-! Restrictions on the middle term following a prime successor. -/

namespace OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H1_R1

open Finset
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem minus_root_binary {x d : ℕ} (ox : Odd x) (hx : 1 < x) (od : Odd d) (hd : 1 < d)
    (unique : ∀ q s : ℕ, q.Prime → s.Prime → 2<q → 2<s →
      q ∣ x^d-1 → s ∣ x^d-1 → q=s) : ∃ a : ℕ, x-1=2^a := by
  let S := ∑ i ∈ range d, x^i
  have os : Odd S := by
    dsimp [S]
    rw [Finset.odd_sum_iff_odd_card_odd]
    simpa [ox.pow] using od
  have big : d<S := by
    have h : (∑ _i ∈ range d, (1:ℕ)) < ∑ i ∈ range d, x^i := by
      apply Finset.sum_lt_sum
      · intro i _
        exact Nat.one_le_pow _ _ (by omega)
      · exact ⟨1,mem_range.mpr hd,by simpa using hx⟩
    simpa [S] using h
  have fac : S*(x-1)=x^d-1 := geom_sum_mul_of_one_le hx.le d
  refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
  intro q pq dq
  by_contra q2
  have lq : 2<q := by have := pq.two_le; omega
  have pure : S=q^S.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
    intro z pz dz
    have z2 : 2<z := by
      have := pz.two_le
      by_contra! low
      have ez : z=2 := by omega
      rw [ez] at dz
      obtain ⟨k,hk⟩ := os
      omega
    exact unique z q pz pq z2 lq (fac ▸ dvd_mul_of_dvd_left dz _)
      (fac ▸ dvd_mul_of_dvd_right dq _))
  let _ : Fact q.Prime := ⟨pq⟩
  have nd : ¬ q ∣ x := by
    intro div
    have h := Nat.dvd_sub div dq
    rw [show x-(x-1)=1 by omega] at h
    have := Nat.le_of_dvd Nat.one_pos h
    omega
  have val := padicValNat.pow_sub_pow (x:=x) (y:=1) (pq.odd_of_ne_two q2) hx dq nd (by omega : d≠0)
  rw [one_pow,←fac,padicValNat.mul (by omega) (by omega)] at val
  have eq : padicValNat q S=padicValNat q d := by omega
  have power : q^(padicValNat q S)=S := by
    conv_lhs => arg 2; rw [pure,padicValNat.prime_pow]
    exact pure.symm
  have div : S ∣ d := by rw [←power,eq]; exact pow_padicValNat_dvd
  exact (Nat.not_le_of_gt big) (Nat.le_of_dvd (by omega) div)

private theorem missing_left {p : ℕ} (missing : ¬∃ d q s : ℕ,
    q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) :
    ∀ q s : ℕ, q.Prime → s.Prime → 2<q → 2<s → q ∣ p+1 → s ∣ p+1 → q=s := by
  intro q s pq ps hq hs dq ds
  by_contra ne
  exact missing ⟨1,q,s,pq,ps,ne,hq,hs,dq,ds⟩

/-- Between p+1 and p+3, the only possible nontrivial odd-power root is three. -/
theorem odd_middle_root {p x d : ℕ} (pp : p.Prime) (hp : 3<p) (ox : Odd x) (hx : 1<x)
    (od : Odd d) (hd : 1<d) (eq : p+2=x^d)
    (missing : ¬∃ k q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ k+1<q ∧ k+1<s ∧
      q ∣ p+k ∧ s ∣ p+k) : x=3 := by
  have elig (q : ℕ) (pq : q.Prime) (hq : 2<q) (dq : q ∣ p+3) : 4<q := by
    by_contra! small
    have e : q=3 := by interval_cases q <;> norm_num at *
    rw [e] at dq
    have d3 : 3 ∣ p := by omega
    have bad := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp d3
    omega
  obtain ⟨a,minus⟩ := minus_root_binary ox hx od hd (by
    rw [←eq,show p+2-1=p+1 by omega]
    exact missing_left missing)
  obtain ⟨b,plus⟩ := odd_root_with_unique_odd_prime ox hx od hd (by
    intro q s pq ps hq hs dq ds
    rw [←eq,show p+2+1=p+3 by omega] at dq ds
    by_contra ne
    exact missing ⟨3,q,s,pq,ps,ne,elig q pq hq dq,elig s ps hs ds,dq,ds⟩)
  obtain ⟨u,hu⟩ := ox
  by_contra bad
  have a2 : 2≤a := by by_contra! low; interval_cases a <;> norm_num at minus <;> omega
  have b2 : 2≤b := by by_contra! low; interval_cases b <;> norm_num at plus <;> omega
  have m4 : 4 ∣ x-1 := minus ▸ pow_dvd_pow (2:ℕ) a2
  have p4 : 4 ∣ x+1 := plus ▸ pow_dvd_pow (2:ℕ) b2
  omega

private theorem shifted_square_binary {p x : ℕ} (hx : 3<x) (eq : p+2=x^2)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : (∃ a : ℕ, x-1=2^a) ∨ (∃ a : ℕ, x+1=2^a) := by
  have fac : p+1=(x-1)*(x+1) := by
    have h : x-1+1=x := by omega
    nlinarith
  have oddprime (y : ℕ) (hy : 1<y) (nopow : ¬∃ a : ℕ, y=2^a) :
      ∃ q : ℕ, q.Prime ∧ 2<q ∧ q ∣ y := by
    by_contra! none
    exact nopow ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
      intro q pq dq
      have := pq.two_le
      by_contra ne
      exact none q pq (by omega) dq)⟩
  by_contra! neither
  obtain ⟨q,pq,hq,dq⟩ := oddprime (x-1) (by omega) (by simpa using neither.1)
  obtain ⟨s,ps,hs,ds⟩ := oddprime (x+1) (by omega) (by simpa using neither.2)
  have ne : q≠s := by
    rintro rfl
    have diff := Nat.dvd_sub ds dq
    rw [show x+1-(x-1)=2 by omega] at diff
    have := Nat.le_of_dvd (by decide) diff
    omega
  exact missing ⟨1,q,s,pq,ps,ne,hq,hs,fac ▸ dvd_mul_of_dvd_left dq _,fac ▸ dvd_mul_of_dvd_right ds _⟩

private theorem odd_factor_pure {p m : ℕ} (hm : 2 ≤ m) (om : ¬2 ∣ m) (dm : m ∣ p+1)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : IsPrimePow m := by
  by_contra bad
  obtain ⟨q,hq,s,hs,ne⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le hm).mp bad
  obtain ⟨pq,dq,_⟩ := Nat.mem_primeFactors.mp hq
  obtain ⟨ps,ds,_⟩ := Nat.mem_primeFactors.mp hs
  apply ne (missing_left missing q s pq ps _ _ (dq.trans dm) (ds.trans dm))
  · have := pq.two_le
    by_contra! low
    have id : q=2 := by omega
    exact om (id ▸ dq)
  · have := ps.two_le
    by_contra! low
    have id : s=2 := by omega
    exact om (id ▸ ds)

private theorem dyadic_minus_bound {p j : ℕ} (hj : 2≤j) (div : 2^(j+j)-1 ∣ p+1)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : False := by
  let y := 2^j
  have big : 4≤y := Nat.pow_le_pow_right (by decide : 0<2) hj
  have even : 2 ∣ y := dvd_pow_self _ (by omega)
  have fac : 2^(j+j)-1=(y-1)*(y+1) := by
    rw [pow_add]
    change y*y-1=(y-1)*(y+1)
    have h : y-1+1=y := by omega
    have pos : 1 ≤ y*y := Nat.mul_pos (by omega) (by omega)
    have h2 : y*y-1+1=y*y := by omega
    nlinarith
  let q := (y-1).minFac
  let s := (y+1).minFac
  have pq : q.Prime := Nat.minFac_prime (by omega)
  have ps : s.Prime := Nat.minFac_prime (by omega)
  have dq : q ∣ y-1 := Nat.minFac_dvd _
  have ds : s ∣ y+1 := Nat.minFac_dvd _
  have hq : 2<q := by
    have := pq.two_le
    by_contra! low
    have e : q=2 := by omega
    rw [e] at dq
    omega
  have hs : 2<s := by
    have := ps.two_le
    by_contra! low
    have e : s=2 := by omega
    rw [e] at ds
    omega
  have ne : q≠s := by
    intro same
    rw [←same] at ds
    have df := Nat.dvd_sub ds dq
    rw [show y+1-(y-1)=2 by omega] at df
    have := Nat.le_of_dvd (by decide) df
    omega
  rw [fac] at div
  exact missing ⟨1,q,s,pq,ps,ne,hq,hs,(dvd_mul_of_dvd_left dq _).trans div,
    (dvd_mul_of_dvd_right ds _).trans div⟩

private theorem prime_power_middle_square {p s k : ℕ} (ps : s.Prime) (os : Odd s)
    (kp : 0<k) (hp : 47<p) (pp : p.Prime) (pm : p%3=2) (eq : p+2=(s^k)^2)
    (missing : ¬∃ d q z : ℕ, q.Prime ∧ z.Prime ∧ q≠z ∧ d+1<q ∧ d+1<z ∧
      q ∣ p+d ∧ z ∣ p+d) : False := by
  let x := s^k
  change p+2=x^2 at eq
  have xbig : 3<x := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    norm_num at this
    omega
  have fac : p+1=(x-1)*(x+1) := by
    have h : x-1+1=x := by omega
    nlinarith
  have bound : x≤17 := by
    rcases shifted_square_binary xbig eq missing with ⟨a,ha⟩|⟨a,ha⟩
    · have ax : x=2^a+1 := by omega
      have am : 0<a := by
        by_contra! low
        have zz : a=0 := by omega
        rw [zz,pow_zero] at ax; omega
      have pure : IsPrimePow (2^a+1) := (isPrimePow_nat_iff _).mpr ⟨s,k,ps,kp,ax⟩
      let c := a-1
      have ac : a=c+1 := by dsimp [c]; omega
      by_cases cz : c=0
      · rw [ac,cz] at ax; norm_num at ax
        omega
      have plus : x+1=2*(2^c+1) := by rw [ax,ac,pow_succ]; ring
      have odd : ¬2 ∣ 2^c+1 := by have := dvd_pow_self (2:ℕ) cz; omega
      have div : 2^c+1 ∣ p+1 := by
        rw [fac,plus]
        exact (dvd_mul_left (2^c+1) 2).trans (dvd_mul_left _ _)
      have ppc := odd_factor_pure (by have := @Nat.one_le_two_pow c; omega) odd div missing
      rcases prime_power_neighbor am.ne' pure with a3|⟨t,ht⟩
      · rw [a3] at ax
        omega
      · by_cases tz : t=0
        · simp [tz] at ht
          simp [ht] at ax
          omega
        have ae : 2 ∣ a := ht ▸ dvd_pow_self 2 tz
        have ab : a≤4 := by
          rcases prime_power_neighbor cz ppc with cf|⟨v,hv⟩
          · omega
          · by_cases vz : v=0
            · simp [vz] at hv; omega
            · have cd : 2 ∣ c := hv ▸ dvd_pow_self 2 vz
              omega
        have := Nat.pow_le_pow_right (by decide : 0<2) ab
        omega
    · have one := mersenne_power_exponent os ps.one_lt kp ha
      have xs : x=s := by dsimp [x]; rw [one,pow_one]
      have xm : s=2^a-1 := by omega
      have an : a≠1 := by rintro rfl; norm_num at xm; have := ps.two_le; omega
      have pa := (Nat.prime_of_pow_sub_one_prime an (xm ▸ ps)).2
      by_contra! high
      have a5 : 5≤a := by
        by_contra! low
        interval_cases a <;> norm_num at ha <;> omega
      obtain ⟨j,hj⟩ := pa.odd_of_ne_two (by omega)
      have j2 : 2≤j := by omega
      have left : x-1=2*(2^(j+j)-1) := by
        have exp : a=(j+j)+1 := by omega
        have npos := @Nat.one_le_two_pow (j+j)
        rw [exp,pow_succ] at ha
        omega
      apply dyadic_minus_bound j2 _ missing
      rw [fac,left]
      exact (dvd_mul_left _ 2).trans (dvd_mul_right _ _)
  have classification : x=13 := by
    have test : ∀ y : Fin 18, 47<y.val^2-2 → (y.val^2-2).Prime → (y.val^2-2)%3=2 →
        Odd y.val → y.val=13 := by decide +kernel
    have po : p=x^2-2 := by omega
    exact test ⟨x,by omega⟩ (po ▸ hp) (po ▸ pp) (po ▸ pm) os.pow
  rw [classification] at eq
  have q : p=167 := by omega
  subst p
  exact missing ⟨1,3,7,by decide +kernel⟩

/-- Apart from the small exceptions, a survivor congruent to two modulo
three must start a pair of twin primes. -/
theorem prime_successor_twin {p : ℕ} (pp : p.Prime) (hp : 47<p) (pm : p%3=2)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : (p+2).Prime := by
  have op := pp.odd_of_ne_two (by omega)
  obtain ⟨j,hj⟩ := op
  have middle : IsPrimePow (p+2) := by
    by_contra bad
    obtain ⟨q,hq,s,hs,ne⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le (show 2≤p+2 by omega)).mp bad
    have eligible (z : ℕ) (pz : z.Prime) (dz : z ∣ p+2) : 3<z := by
      by_contra! low
      have choose : z=2 ∨ z=3 := by interval_cases z <;> norm_num at *
      rcases choose with rfl|rfl <;> omega
    obtain ⟨pq,dq,_⟩ := Nat.mem_primeFactors.mp hq
    obtain ⟨ps,ds,_⟩ := Nat.mem_primeFactors.mp hs
    exact missing ⟨2,q,s,pq,ps,ne,eligible q pq dq,eligible s ps ds,dq,ds⟩
  obtain ⟨s,e,ps,ep,eq⟩ := (isPrimePow_nat_iff _).mp middle
  have os := ps.odd_of_ne_two (by
    rintro rfl
    have d := dvd_pow_self (2:ℕ) ep.ne'
    rw [eq] at d
    omega)
  rcases Nat.even_or_odd e with ⟨k,hk⟩|oe
  · have sq : p+2=(s^k)^2 := by rw [←eq,hk,pow_add,pow_two]
    exact False.elim (prime_power_middle_square ps os (by omega) hp pp pm sq missing)
  · by_cases unit : e=1
    · rw [unit,pow_one] at eq; exact eq ▸ ps
    · have three := odd_middle_root pp (by omega) os ps.one_lt oe (by omega) eq.symm missing
      subst s
      have div := dvd_pow_self (3:ℕ) ep.ne'
      rw [eq] at div
      omega

private theorem prime_above_three {m : ℕ} (hm : 1 < m) (om : ¬2 ∣ m)
    (ex : ∀ e : ℕ, m≠3^e) : ∃ q : ℕ, q.Prime ∧ 3<q ∧ q ∣ m := by
  by_contra! none
  exact ex _ (Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
    intro q pq dq
    have low : q ≤ 3 := by by_contra! high; exact none q pq high dq
    have := pq.two_le
    by_contra ne
    have e : q=2 := by omega
    exact om (e ▸ dq)))

private theorem power_plus_one_not_three {j e : ℕ} (hj : 4≤j) : 2^j+1≠3^e := by
  intro eq
  have ep : e≠0 := by
    rintro rfl
    have := @Nat.one_le_two_pow j
    simp at eq
  have primepower : IsPrimePow (2^j+1) := (isPrimePow_nat_iff _).mpr
    ⟨3,e,Nat.prime_three,Nat.pos_of_ne_zero ep,eq.symm⟩
  obtain ⟨t,ht⟩ := (prime_power_neighbor (by omega) primepower).resolve_left (by omega)
  have tn : t≠0 := by rintro rfl; simp at ht; omega
  obtain ⟨u,hu⟩ : 2 ∣ j := ht ▸ dvd_pow_self 2 tn
  have red : Nat.ModEq 3 (2^j) 1 := by
    rw [hu,pow_mul]
    have m : Nat.ModEq 3 (2^2) 1 := by decide
    simpa only [one_pow] using m.pow u
  change 2^j%3=1 at red
  have d : 3 ∣ 2^j+1 := eq ▸ dvd_pow_self _ ep
  omega

private theorem square_mersenne_bound {p x b : ℕ} (hb : x+1=2^b) (eq : p+2=x^2)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : x≤63 := by
  by_contra! high
  have b7 : 7≤b := by
    by_contra! low
    have := Nat.pow_le_pow_right (by decide : 0<2) (show b≤6 by omega)
    omega
  let j := b/2
  let y := 2^j
  have j3 : 3≤j := by dsimp [j]; omega
  have big : 8≤y := Nat.pow_le_pow_right (by decide : 0<2) j3
  have even : 8 ∣ y := pow_dvd_pow (2:ℕ) j3
  have fac : y*y=(y-1)*(y+1)+1 := by
    have h : y-1+1=y := by omega
    nlinarith
  by_cases bj : b=2*j
  · have j4 : 4≤j := by omega
    have mid : x=(y-1)*(y+1) := by
      rw [bj,Nat.mul_comm 2 j,pow_mul,pow_two] at hb
      change x+1=y*y at hb
      omega
    obtain ⟨q,pq,hq,dq⟩ := prime_above_three (m:=y-1) (by omega) (by omega) (by
      intro e h
      have := three_pow_mod_eight e
      omega)
    obtain ⟨s,ps,hs,ds⟩ := prime_above_three (m:=y+1) (by omega) (by omega)
      (fun _ => power_plus_one_not_three j4)
    have ne : q≠s := by
      rintro rfl
      have df := Nat.dvd_sub ds dq
      rw [show y+1-(y-1)=2 by omega] at df
      have := Nat.le_of_dvd (by decide) df
      omega
    have xd : x ∣ p+2 := eq ▸ dvd_pow_self x (by decide : 2≠0)
    exact missing ⟨2,q,s,pq,ps,ne,hq,hs,(mid ▸ dvd_mul_of_dvd_left dq _).trans xd,
      (mid ▸ dvd_mul_of_dvd_right ds _).trans xd⟩
  · have bform : b=(j+j)+1 := by dsimp [j] at *; omega
    have xx : x-1=2*(2^(j+j)-1) := by
      rw [bform,pow_succ] at hb
      have := @Nat.one_le_two_pow (j+j)
      omega
    have dm : x-1 ∣ p+1 := by
      have h : x-1+1=x := by omega
      have f : p+1=(x-1)*(x+1) := by nlinarith
      rw [f]; exact dvd_mul_right _ _
    apply dyadic_minus_bound (by omega : 2≤j) _ missing
    rw [xx] at dm
    exact (dvd_mul_left _ 2).trans dm

private theorem middle_fifth_witness {p t : ℕ} (ht : 2≤t)
    (eq : p+2=(2*(2^(2^t))+1)^2)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q ∣ p+d ∧ s ∣ p+d) : False := by
  have orbit (i : ℕ) : 2^(2^(i+2))%91=16 ∨ 2^(2^(i+2))%91=74 := by
    induction i with
    | zero => decide
    | succ i ih =>
      have step : 2^(2^(i+1+2))=(2^(2^(i+2)))^2 := by
        rw [show i+1+2=i+2+1 by omega,pow_succ (2:ℕ) (i+2),pow_mul]
      rw [step,Nat.pow_mod]
      rcases ih with h|h <;> rw [h] <;> decide
  let z := 2^(2^t)
  have res : z%91=16 ∨ z%91=74 := by
    have := orbit (t-2)
    simpa [z,Nat.sub_add_cancel ht] using this
  have div : 91 ∣ (2*z+1)^2+3 := by
    have co := ((((Nat.mod_modEq z 91).mul_left 2).add_right 1).pow 2).add_right 3
    apply Nat.modEq_zero_iff_dvd.mp
    apply co.symm.trans
    rcases res with h|h <;> rw [h] <;> decide
  have expr : p+5=(2*z+1)^2+3 := by dsimp [z]; omega
  rw [←expr] at div
  exact missing ⟨5,7,13,by decide,by decide,by decide,by decide,by decide,
    (show 7∣91 by decide).trans div,(show 13∣91 by decide).trans div⟩

set_option maxHeartbeats 600000 in
/-- Beyond the last small example, a multiple of three two above the successor
cannot be a square. -/
theorem middle_not_square {p x : ℕ} (pp : p.Prime) (hp : 223<p) (pm : p%3=1)
    (eq : p+2=x^2) (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) : False := by
  have xbig : 3<x := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    norm_num at this
    omega
  have bound : x≤63 := by
    rcases shifted_square_binary xbig eq missing with ⟨a,ha⟩|⟨a,ha⟩
    · have ax : x=2^a+1 := by omega
      have ap : a≠0 := by rintro rfl; norm_num at ax; omega
      let c := a-1
      have ac : a=c+1 := by dsimp only [c]; omega
      by_cases cz : c=0
      · rw [ac,cz] at ax; norm_num at ax; omega
      have plus : x+1=2*(2^c+1) := by rw [ax,ac,pow_succ]; ring
      have odd : ¬2 ∣ 2^c+1 := by have := dvd_pow_self (2:ℕ) cz; omega
      have fac : p+1=(x-1)*(x+1) := by
        have h : x-1+1=x := by omega
        nlinarith
      have div : 2^c+1 ∣ p+1 := by
        rw [fac,plus]
        exact (dvd_mul_left (2^c+1) 2).trans (dvd_mul_left _ _)
      have pure := odd_factor_pure (by have := @Nat.one_le_two_pow c; omega) odd div missing
      rcases prime_power_neighbor cz pure with c3|⟨t,ht⟩
      · rw [ac,c3] at ax; norm_num at ax; omega
      · by_cases small : t<2
        · interval_cases t <;> norm_num at ht <;> rw [ac,ht] at ax <;> norm_num at ax <;> omega
        · apply False.elim (middle_fifth_witness (by omega : 2≤t) _ missing)
          rw [eq,ax,ac,ht,pow_succ (2:ℕ) (2^t),Nat.mul_comm (2^(2^t)) 2]
    · exact square_mersenne_bound ha eq missing
  have oddm : Odd (p+2) := (pp.odd_of_ne_two (by omega)).add_even (by decide : Even 2)
  rw [eq,Nat.odd_pow_iff (by decide : 2≠0)] at oddm
  obtain ⟨u,hu⟩ := oddm
  have div3 : 3∣x := Nat.prime_three.dvd_of_dvd_pow (by rw [←eq]; omega)
  have xmin : 15<x := by
    by_contra! low
    have z := Nat.pow_le_pow_left low 2
    norm_num at z
    omega
  have alternatives : x=21 ∨ x=27 ∨ x=33 ∨ x=39 ∨ x=45 ∨ x=51 ∨ x=57 ∨ x=63 := by omega
  rcases alternatives with h|h|h|h|h|h|h|h <;> rw [h] at eq <;> norm_num at eq
  · have ep : p=439 := by omega
    rw [ep] at missing; exact missing ⟨1,5,11,by decide +kernel⟩
  · have ep : p=727 := by omega
    rw [ep] at missing; exact missing ⟨1,7,13,by decide +kernel⟩
  · have ep : p=1087 := by omega
    rw [ep] at missing; exact missing ⟨3,5,109,by decide +kernel⟩
  · have ep : p=1519 := by omega
    exact Nat.not_prime_of_dvd_of_lt (by norm_num : 7∣1519) (by decide) (by decide) (ep ▸ pp)
  · have ep : p=2023 := by omega
    exact Nat.not_prime_of_dvd_of_lt (by norm_num : 7∣2023) (by decide) (by decide) (ep ▸ pp)
  · have ep : p=2599 := by omega
    exact Nat.not_prime_of_dvd_of_lt (by norm_num : 23∣2599) (by decide) (by decide) (ep ▸ pp)
  · have ep : p=3247 := by omega
    exact Nat.not_prime_of_dvd_of_lt (by norm_num : 17∣3247) (by decide) (by decide) (ep ▸ pp)
  · have ep : p=3967 := by omega
    rw [ep] at missing; exact missing ⟨3,5,397,by decide +kernel⟩

/-- A power of three two above p produces a witness. The odd-prime exponent
case reduces to Fermat exponents, which give the primes seven and eleven. -/
theorem pure_three_exclusion {p r : ℕ} (pp : p.Prime) (hp : 223<p) (pr : r.Prime)
    (od : Odd r) (eq : p+2=3^r) (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) : False := by
  have ro := od
  obtain ⟨j,hj⟩ := ro
  have rr : r%4=1 := by
    by_contra b
    have e : r%4=3 := by omega
    have h := pow_cycle (a:=3) (d:=4) (m:=5) (by decide) r
    change 3^r%5=3^(r%4)%5 at h
    rw [e] at h
    norm_num at h
    have bad := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) pp).mp (by omega)
    omega
  let a := r-1
  have rp := pr.one_lt
  have ap : 0<a := by dsimp [a]; omega
  have ra : r=a+1 := by dsimp [a]; omega
  have a4 : a%4=0 := by omega
  have m5 := pow_cycle (a:=3) (d:=4) (m:=5) (by decide) a
  change 3^a%5=3^(a%4)%5 at m5
  rw [a4] at m5
  norm_num at m5
  have m3 := dvd_pow_self (3:ℕ) ap.ne'
  have eligible (q : ℕ) (pq : q.Prime) (lo : 2<q) (div : q ∣ 3^a+1) : 6<q := by
    by_contra! small
    have choice : q=3 ∨ q=5 := by interval_cases q <;> norm_num at *
    rcases choice with rfl|rfl <;> omega
  have dyadic : ∃ t : ℕ, a=2^t := by
    refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd ap.ne' ?_⟩
    intro l pl dl
    by_contra l2
    obtain ⟨s,hs⟩ := dl
    have sp : 0<s := by
      by_contra! bad
      have zz : s=0 := by omega
      simp [zz] at hs
      omega
    have form : (3^s)^l=3^a := by rw [←pow_mul,hs,Nat.mul_comm s l]
    have raised : p+5=3*(3^a+1) := by
      rw [ra,pow_succ] at eq
      omega
    obtain ⟨e,binary⟩ := odd_root_with_unique_odd_prime ((by decide : Odd 3).pow (n:=s))
      (Nat.one_lt_pow sp.ne' (by decide : 1<3)) (pl.odd_of_ne_two l2) pl.one_lt (by
        intro q z pq pz hq hz dq dz
        rw [form] at dq dz
        by_contra ne
        exact missing ⟨5,q,z,pq,pz,ne,eligible q pq hq dq,eligible z pz hz dz,
          raised ▸ dvd_mul_of_dvd_right dq 3,raised ▸ dvd_mul_of_dvd_right dz 3⟩)
    have one := mersenne_power_exponent (by decide : Odd 3) (by decide : 1<3) sp binary
    rw [one,mul_one] at hs
    obtain ⟨v,hv⟩ := pl.odd_of_ne_two l2
    omega
  obtain ⟨t,ht⟩ := dyadic
  have re : r=2^t+1 := by omega
  have tn : t≠0 := by rintro rfl; norm_num at re; omega
  have primepower : IsPrimePow (2^t+1) := re ▸ (isPrimePow_nat_iff _).mpr ⟨r,1,pr,by decide,by simp⟩
  rcases prime_power_neighbor tn primepower with three|⟨u,hu⟩
  · rw [three] at re
    norm_num at re
    rw [re] at pr
    norm_num at pr
  · by_cases small : u≤1
    · interval_cases u
      · norm_num at hu; rw [hu] at re; norm_num at re; omega
      · norm_num at hu; rw [hu] at re; norm_num at re
        rw [re] at eq
        have pe : p=241 := by norm_num at eq; omega
        rw [pe] at missing
        exact missing ⟨6,13,19,by decide +kernel⟩
    have t4 : 4 ∣ t := hu ▸ pow_dvd_pow (2:ℕ) (by omega : 2≤u)
    have t_mod : t%4=0 := by omega
    have t_even : t%2=0 := by omega
    have m := pow_cycle (a:=2) (d:=2) (m:=3) (by decide) t
    have n := pow_cycle (a:=2) (d:=4) (m:=5) (by decide) t
    change 2^t%3=2^(t%2)%3 at m
    change 2^t%5=2^(t%4)%5 at n
    rw [t_even] at m
    rw [t_mod] at n
    norm_num at m n
    have c6 : r%6=5 := by omega
    have c5 : r%5=2 := by omega
    have seven := pow_cycle (a:=3) (d:=6) (m:=7) (by decide) r
    have eleven := pow_cycle (a:=3) (d:=5) (m:=11) (by decide) r
    change 3^r%7=3^(r%6)%7 at seven
    change 3^r%11=3^(r%5)%11 at eleven
    rw [c6] at seven
    rw [c5] at eleven
    norm_num at seven eleven
    exact missing ⟨4,7,11,by decide,by decide,by decide,by decide,by decide,by omega,by omega⟩

private theorem three_exponent_prime {p c : ℕ} (pp : p.Prime) (hp : 223<p) (pm : p%3=1)
    (eq : p+2=3^c) (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) : c.Prime ∧ Odd c := by
  have large : 1<c := by
    by_contra! small
    interval_cases c <;> norm_num at eq <;> omega
  have oc : Odd c := by
    rcases Nat.even_or_odd c with ⟨k,hk⟩|od
    · exact (middle_not_square pp hp pm (x:=3^k) (by rw [eq,hk,pow_add,pow_two]) missing).elim
    · exact od
  refine ⟨?_,oc⟩
  by_contra notprime
  obtain ⟨d,pd,k,hk⟩ := Nat.exists_prime_and_dvd (by omega : c≠1)
  have kd : k≠1 := by
    rintro rfl
    simp only [mul_one] at hk
    exact notprime (hk ▸ pd)
  have k2 : 2≤k := by
    by_cases zero : k=0
    · simp [zero] at hk; omega
    · omega
  have oddd := pd.odd_of_ne_two (by
    rintro rfl
    obtain ⟨a,ha⟩ := oc
    omega)
  have xlarge : 9≤3^k := Nat.pow_le_pow_right (by decide : 0<3) k2
  have three := odd_middle_root pp (by omega) ((by decide : Odd 3).pow (n:=k)) (by omega)
    oddd pd.one_lt (by rw [eq,hk,Nat.mul_comm d k,pow_mul]) missing
  omega

private theorem mixed_coprime {p t a b : ℕ} (pp : p.Prime) (hp : 223<p) (pm : p%3=1)
    (pt : t.Prime) (ht : 3<t) (bp : 0<b) (eq : p+2=3^a*t^b)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) : a.Coprime b := by
  by_contra bad
  obtain ⟨d,pd,dc,de⟩ := Nat.Prime.not_coprime_iff_dvd.mp bad
  obtain ⟨u,hu⟩ := dc
  obtain ⟨v,hv⟩ := de
  have vp : v≠0 := by rintro rfl; simp at hv; omega
  have lb := Nat.le_self_pow vp t
  have yb : 3 < 3^u*t^v := by
    have pos : 0<3^u := pow_pos (by decide) _
    have := Nat.mul_le_mul_right (t^v) pos
    omega
  have power : p+2=(3^u*t^v)^d := by
    rw [mul_pow,←pow_mul,←pow_mul,Nat.mul_comm u d,Nat.mul_comm v d,←hu,←hv,eq]
  by_cases ev : d=2
  · rw [ev] at power
    exact middle_not_square pp hp pm power missing
  · have oy := ((by decide : Odd 3).pow (n:=u)).mul ((pt.odd_of_ne_two (by omega)).pow (n:=v))
    have three := odd_middle_root pp (by omega) oy (by omega) (pd.odd_of_ne_two ev)
      pd.one_lt power missing
    omega

private theorem middle_classification {p : ℕ} (pp : p.Prime) (hp : 223<p) (pm : p%3=1)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧
      d+1<q ∧ d+1<s ∧ q ∣ p+d ∧ s ∣ p+d) :
    (∃ c : ℕ, c.Prime ∧ Odd c ∧ p+2=3^c) ∨
    (∃ t a b : ℕ, t.Prime ∧ 3<t ∧ 0<a ∧ 0<b ∧ a.Coprime b ∧ p+2=3^a*t^b) := by
  let n := p+2
  let a := n.factorization 3
  let m := n/3^a
  have nz : n≠0 := by dsimp [n]; omega
  have fac : 3^a*m=n := Nat.ordProj_mul_ordCompl_eq_self n 3
  have dm : m ∣ n := Nat.ordCompl_dvd n 3
  have pos : 0 < m := Nat.ordCompl_pos 3 nz
  have no3 : ¬3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three nz
  have op := pp.odd_of_ne_two (by omega)
  have no2 : ¬2 ∣ m := by
    intro h
    have bad := h.trans dm
    change 2 ∣ p+2 at bad
    obtain ⟨i,hi⟩ := op
    omega
  have ap : 0<a := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three nz).mp
    (by change 3 ∣ p+2; omega)
  by_cases one : m=1
  · have eq : p+2=3^a := by simpa only [one,mul_one,n] using fac.symm
    have h := three_exponent_prime pp hp pm eq missing
    exact Or.inl ⟨a,h.1,h.2,eq⟩
  have eligible (q : ℕ) (pq : q.Prime) (dq : q ∣ m) : 3<q := by
    have := pq.two_le
    by_contra! small
    rcases (show q=2 ∨ q=3 by omega) with rfl|rfl
    · exact no2 dq
    · exact no3 dq
  have pure : IsPrimePow m := by
    by_contra bad
    obtain ⟨q,hq,s,hs,ne⟩ := (Nat.not_isPrimePow_iff_nontrivial_of_two_le
      (by omega : 2 ≤ m)).mp bad
    obtain ⟨pq,dq,_⟩ := Nat.mem_primeFactors.mp hq
    obtain ⟨ps,ds,_⟩ := Nat.mem_primeFactors.mp hs
    exact missing ⟨2,q,s,pq,ps,ne,eligible q pq dq,eligible s ps ds,dq.trans dm,ds.trans dm⟩
  obtain ⟨t,b,pt,bp,rep⟩ := (isPrimePow_nat_iff _).mp pure
  have dt : t ∣ m := rep ▸ dvd_pow_self _ bp.ne'
  have ht := eligible t pt dt
  have eq : p+2=3^a*t^b := by rw [rep]; exact fac.symm
  exact Or.inr ⟨t,a,b,pt,ht,ap,bp,mixed_coprime pp hp pm pt ht bp eq missing,eq⟩

private theorem twin_binary_orbit (t : ℕ) (ht : 2≤t) :
    let z := 3^(2^t)
    z%7=4 ∨ z%11=5 ∨ (z%73=64 ∧ z%1181=1172) := by
  let M : ℕ := 6638401
  let states : List ℕ := [81,6561,3216315,2155316]
  have orbit (i : ℕ) : 3^(2^(i+2))%M ∈ states := by
    induction i with
    | zero => decide
    | succ i ih =>
      have step : 3^(2^(i+1+2))=(3^(2^(i+2)))^2 := by
        rw [show i+1+2=i+2+1 by omega,pow_succ (2:ℕ) (i+2),pow_mul]
      rw [step,Nat.pow_mod]
      exact (show ∀ s ∈ states, s^2%M ∈ states by decide +kernel) _ ih
  let z := 3^(2^t)
  have res : z%M ∈ states := by
    have := orbit (t-2)
    simpa [z,Nat.sub_add_cancel ht] using this
  have cover : ∀ s ∈ states, s%7=4 ∨ s%11=5 ∨ (s%73=64 ∧ s%1181=1172) := by decide +kernel
  have h := cover _ res
  rw [Nat.mod_mod_of_dvd _ (by decide : 7∣M),Nat.mod_mod_of_dvd _ (by decide : 11∣M),
    Nat.mod_mod_of_dvd _ (by decide : 73∣M),Nat.mod_mod_of_dvd _ (by decide : 1181∣M)] at h
  exact h

/-- A surviving pair of twin primes cannot straddle twice a power of three. -/
theorem twin_twice_three_exclusion {p b : ℕ} (pp : p.Prime) (sp : (p+2).Prime)
    (hp : 223<p) (bp : 0<b) (eq : p+1=2*3^b)
    (missing : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q∣p+d ∧ s∣p+d) : False := by
  have nodiv (q : ℕ) (pq : q.Prime) (lo : q<p) : ¬q∣p ∧ ¬q∣p+2 := by
    constructor <;> intro dv
    · have := (Nat.prime_dvd_prime_iff_eq pq pp).mp dv; omega
    · have := (Nat.prime_dvd_prime_iff_eq pq sp).mp dv; omega
  have eb : Even b := by
    rcases Nat.even_or_odd b with ev|⟨k,hk⟩
    · exact ev
    · exfalso
      have per := pow_cycle (a:=3) (d:=4) (m:=5) (by decide) b
      change 3^b%5=3^(b%4)%5 at per
      have nd := nodiv 5 (by decide) (by omega)
      rcases (show b%4=1 ∨ b%4=3 by omega) with c|c <;> rw [c] at per <;> norm_num at per <;> omega
  have reg (q : ℕ) (pq : q.Prime) (hq : 2<q) (dq : q∣3^b+1) : 4<q := by
    by_contra! low
    have q3 : q=3 := by interval_cases q <;> norm_num at *
    rw [q3] at dq
    have db := dvd_pow_self (3:ℕ) bp.ne'
    omega
  have binary : ∃ t : ℕ, b=2^t := by
    refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd bp.ne' ?_⟩
    intro l pl dl
    by_contra l2
    obtain ⟨s,hs⟩ := dl
    have spos : 0<s := by
      by_contra! bad
      have zero : s=0 := by omega
      simp [zero] at hs; omega
    have form : (3^s)^l=3^b := by rw [←pow_mul,hs,Nat.mul_comm s l]
    have raised : p+3=2*(3^b+1) := by omega
    obtain ⟨e,h⟩ := odd_root_with_unique_odd_prime ((by decide : Odd 3).pow (n:=s))
      (Nat.one_lt_pow spos.ne' (by decide : 1<3)) (pl.odd_of_ne_two l2) pl.one_lt (by
        intro q z pq pz hq hz dq dz
        rw [form] at dq dz
        by_contra ne
        exact missing ⟨3,q,z,pq,pz,ne,reg q pq hq dq,reg z pz hz dz,
          raised ▸ dvd_mul_of_dvd_right dq 2,raised ▸ dvd_mul_of_dvd_right dz 2⟩)
    have one := mersenne_power_exponent (by decide : Odd 3) (by decide : 1<3) spos h
    rw [one,mul_one] at hs
    obtain ⟨k,hk⟩ := eb
    obtain ⟨j,hj⟩ := pl.odd_of_ne_two l2
    omega
  obtain ⟨t,ht⟩ := binary
  have big : 2≤t := by
    by_contra! low
    interval_cases t <;> norm_num at ht <;> rw [ht] at eq <;> norm_num at eq <;> omega
  rw [ht] at eq
  rcases twin_binary_orbit t big with h|h|⟨h,k⟩
  · exact (nodiv 7 (by decide) (by omega)).1 (by omega)
  · exact (nodiv 11 (by decide) (by omega)).2 (by omega)
  · exact missing ⟨19,73,1181,by decide,by norm_num,by decide,by decide,by decide,by omega,by omega⟩

/-- For a successor two modulo three, an odd prime power equal to (p+3)/2
has exponent one once p exceeds 575. -/
theorem twin_upper_prime {p r d : ℕ} (hp : 575<p) (pm : p%3=2) (pr : r.Prime)
    (hr : 3<r) (dp : 0<d) (eq : p+3=2*r^d)
    (missing : ¬∃ k q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ k+1<q ∧ k+1<s ∧
      q∣p+k ∧ s∣p+k) : d=1 := by
  have d3 : 3∣p+1 := by omega
  have forbid (q : ℕ) (pq : q.Prime) (hq : 3<q) (dq : q∣p+1) : False :=
    missing ⟨1,3,q,Nat.prime_three,pq,by omega,by decide,by omega,d3,dq⟩
  rcases Nat.even_or_odd d with ⟨k,hk⟩|od
  · let y := r^k
    have sq : p+3=2*y^2 := by rw [eq,hk,pow_add]; simp only [y,pow_two]
    have big : 17<y := by
      by_contra! small
      have := Nat.pow_le_pow_left small 2
      norm_num at this
      omega
    have fac : p+1=2*((y-1)*(y+1)) := by
      have h : y-1+1=y := by omega
      nlinarith
    have left : y-1 ∣ p+1 := by
      rw [fac]; exact (dvd_mul_right _ _).trans (dvd_mul_left _ _)
    have right : y+1 ∣ p+1 := by
      rw [fac]; exact (dvd_mul_left _ _).trans (dvd_mul_left _ _)
    have binary (m : ℕ) (hm : 1 < m) (dm : m∣p+1) (nd : ¬3∣m) : ∃ a : ℕ, m=2^a := by
      refine ⟨_,Nat.eq_prime_pow_of_unique_prime_dvd (by omega) ?_⟩
      intro q pq dq
      have low : q≤3 := by by_contra! high; exact forbid q pq high (dq.trans dm)
      have nz : q≠3 := by rintro rfl; exact nd dq
      have := pq.two_le
      omega
    have base : (∃ a : ℕ, y-1=2^a) ∨ (∃ a : ℕ, y+1=2^a) := by
      by_cases q : 3∣y-1
      · exact Or.inr (binary _ (by omega) right (by omega))
      · exact Or.inl (binary _ (by omega) left q)
    obtain ⟨a,ha⟩ : ∃ a : ℕ, y-1=2^a ∨ y+1=2^a := by
      rcases base with ⟨a,h⟩|⟨a,h⟩
      · exact ⟨a,Or.inl h⟩
      · exact ⟨a,Or.inr h⟩
    have a5 : 5≤a := by
      by_contra! small
      have := Nat.pow_le_pow_right (by decide : 0<2) (by omega : a≤4)
      rcases ha with h|h <;> omega
    let j := a-1
    have aj : a=j+1 := by dsimp [j]; omega
    have j4 : 4≤j := by omega
    let z := 2^j
    have high : 16≤z := Nat.pow_le_pow_right (by decide : 0<2) j4
    have z8 : 8∣z := pow_dvd_pow 2 (by omega : 3≤j)
    rcases ha with h|h
    · have other : y+1=2*(z+1) := by rw [aj,pow_succ] at h; change y-1=z*2 at h; omega
      obtain ⟨q,pq,hq,dq⟩ := prime_above_three (m:=z+1) (by omega) (by omega)
        (fun _ => power_plus_one_not_three j4)
      rw [other] at right
      exact (forbid q pq hq ((dvd_mul_of_dvd_right dq 2).trans right)).elim
    · have other : y-1=2*(z-1) := by rw [aj,pow_succ] at h; change y+1=z*2 at h; omega
      obtain ⟨q,pq,hq,dq⟩ := prime_above_three (m:=z-1) (by omega) (by omega) (by
        intro e he
        have := three_pow_mod_eight e
        omega)
      rw [other] at left
      exact (forbid q pq hq ((dvd_mul_of_dvd_right dq 2).trans left)).elim
  · by_contra ne
    obtain ⟨a,bin⟩ := minus_root_binary (pr.odd_of_ne_two (by omega)) pr.one_lt od
      (by omega) (by
        intro q s pq ps hq hs dq ds
        have rp : 0<r^d := pow_pos (by omega) _
        have f : p+1=2*(r^d-1) := by omega
        apply missing_left missing q s pq ps hq hs <;> rw [f]
        · exact dvd_mul_of_dvd_right dq _
        · exact dvd_mul_of_dvd_right ds _)
    have nz : r%3≠0 := by
      intro z
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pr).mp (Nat.dvd_of_mod_eq_zero z)
      omega
    have rr : r%3=1 := by
      by_contra diff
      have two : r%3=2 := by omega
      obtain ⟨k,hk⟩ := od
      have ed : d%2=1 := by omega
      have cf := (Nat.mod_modEq r 3).pow d
      change (r%3)^d%3=r^d%3 at cf
      rw [two] at cf
      have cy := pow_cycle (a:=2) (d:=2) (m:=3) (by decide) d
      change 2^d%3=2^(d%2)%3 at cy
      rw [ed] at cy
      norm_num at cy
      omega
    have bad : 3∣r-1 := by omega
    rw [bin] at bad
    have := Nat.prime_three.dvd_of_dvd_pow bad
    omega

/-- The three required primes force their common parameter to equal one modulo five. -/
theorem twin_parameter_mod_five {p r : ℕ} (pp : p.Prime) (sp : (p+2).Prime) (pr : r.Prime)
    (hp : 575<p) (eq : p+3=2*r) (nd : ¬5∣r-1) : (r-1)%5=1 := by
  have nonzero (a : ℕ) (pa : a.Prime) (ha : 5<a) : ¬5∣a := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) pa).mp h
    omega
  have a := nonzero p pp (by omega)
  have b := nonzero (p+2) sp (by omega)
  have c := nonzero r pr (by omega)
  let j := (r-1)/5
  have split : (r-1)%5+5*j=r-1 := Nat.mod_add_div _ _
  by_contra bad
  rcases (show (r-1)%5=2 ∨ (r-1)%5=3 ∨ (r-1)%5=4 by omega) with h|h|h
  · exact b ⟨2*j+1,by omega⟩
  · exact a ⟨2*j+1,by omega⟩
  · exact c ⟨j+1,by omega⟩

/-- When p is two modulo three, the next odd integer is another prime
and p+1 is divisible by four with odd part a power of three. -/
def H1 : Prop := ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B<p →
    (∀ x : ℕ, 1<x → p≠x^4+1) → (∀ e : ℕ, p≠2^e+1) →
    p%3=2 → (p+2).Prime →
    (∃ r a b : ℕ, r.Prime ∧ 3<r ∧ 2≤a ∧ 0<b ∧ (r-1)%5=1 ∧
      p+1=2^a*3^b ∧ p+3=2*r) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p+d ∧ s∣p+d

/-- A middle term with a second prime factor has coprime exponents. -/
def H2 : Prop := ∃ B : ℕ, ∀ p : ℕ, p.Prime → Odd p → B<p →
    (∀ x : ℕ, 1<x → p≠x^4+1) → (∀ e : ℕ, p≠2^e+1) →
    p%3=1 → (∃ t u v : ℕ, t.Prime ∧ 3<t ∧ 0<u ∧ 0<v ∧ u.Coprime v ∧ p+2=3^u*t^v) →
    (∃ q r a b c d : ℕ, q.Prime ∧ r.Prime ∧ 2<q ∧ 3<r ∧ q≠r ∧ 0<a ∧ 0<b ∧
      0<c ∧ 0<d ∧ (a=1 ∨ c=1) ∧ p+1=2^a*q^b ∧ p+3=2^c*r^d) →
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p+d ∧ s∣p+d

theorem main : H1 → H2 → OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.H1 := by
  rintro ⟨A,h₁⟩ ⟨B,h₂⟩
  refine ⟨max A B+575,?_⟩
  intro p pp op bound fourth outer
  have ha := Nat.le_max_left A B
  have hb := Nat.le_max_right A B
  obtain ⟨fermat,data⟩ := outer
  by_contra missing
  have nz : p%3≠0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three pp).mp (Nat.dvd_of_mod_eq_zero h)
    omega
  by_cases two : p%3=2
  · obtain ⟨q,r,a,b,c,d,pq,pr,_hq,hr,_ne,ap,bp,cp,dp,one,left,right⟩ := data
    have dv : 3 ∣ p+1 := by omega
    rw [left] at dv
    have qq : 3=q := by
      rcases Nat.prime_three.dvd_mul.mp dv with z|z
      · have := Nat.prime_three.dvd_of_dvd_pow z; omega
      · exact (Nat.prime_dvd_prime_iff_eq Nat.prime_three pq).mp (Nat.prime_three.dvd_of_dvd_pow z)
    subst q
    have twin := prime_successor_twin pp (by omega) two missing
    by_cases aone : a=1
    · exact twin_twice_three_exclusion pp twin (by omega) bp (by simpa only [aone,pow_one] using left) missing
    · have cone := one.resolve_left aone
      rw [cone,pow_one] at right
      have exponentOne := twin_upper_prime (by omega) two pr hr dp right missing
      rw [exponentOne,pow_one] at right
      have nd : ¬5∣r-1 := by
        intro bad
        have scaled : p+1=2*(r-1) := by omega
        have dv : 5∣p+1 := scaled ▸ dvd_mul_of_dvd_right bad 2
        rw [left] at dv
        have p5 : Nat.Prime 5 := by decide
        rcases p5.dvd_mul.mp dv with f|f <;> have := p5.dvd_of_dvd_pow f <;> omega
      exact missing (h₁ p pp op (by omega) fourth fermat two twin
        ⟨r,a,b,pr,hr,by omega,bp,twin_parameter_mod_five pp twin pr (by omega) right nd,left,right⟩)
  · have one : p%3=1 := by omega
    rcases middle_classification pp (by omega) one missing with pure|mixed
    · obtain ⟨r,pr,od,eq⟩ := pure
      exact pure_three_exclusion pp (by omega) pr od eq missing
    · exact missing (h₂ p pp op (by omega) fourth fermat one mixed data)

end OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H1_R1
