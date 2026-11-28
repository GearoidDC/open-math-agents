import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1

/-! An explicit upper bound for solutions to Erdős 889. The polynomial and
interval-counting lemmas below follow the merged reduction and the finiteness
argument of @MrSeizy (lefttosolve2/open-math-agents#23442). The fixed-scale
argument tracks the exponent range and interval lengths separately. -/
namespace Erdos889.FixedInterval
open Finset Polynomial
private noncomputable def strip (s : ℕ) (f : ℤ[X]) : ℕ → ℤ[X]
  | 0 => f
  | i+1 => X * (strip s f i).derivative - C ((s : ℤ)+i) * strip s f i

private lemma strip_coeff (s j : ℕ) (f : ℤ[X]) (i : ℕ) :
    (strip s f i).coeff j = f.coeff j * ∏ l ∈ range i, ((j : ℤ) - (s+l)) := by
  induction i with
  | zero => simp [strip]
  | succ i ih =>
    simp only [strip, coeff_sub, coeff_C_mul, prod_range_succ]
    have h (g : ℤ[X]) : (X * g.derivative).coeff j = j * g.coeff j := by
      cases j with
      | zero => simp
      | succ j => rw [coeff_X_mul, coeff_derivative]; push_cast; ring
    rw [h, ih]
    ring

private lemma strip_dvd (s i b : ℕ) (g f : ℤ[X]) (h : g ^ (b+i) ∣ f) :
    g ^ b ∣ strip s f i := by
  induction i generalizing b with
  | zero => simpa [strip] using h
  | succ i ih =>
    obtain ⟨w, hw⟩ := ih (b+1) (by rwa [show b+1+i = b+(i+1) by omega])
    rw [strip, hw, derivative_mul, derivative_pow_succ]
    refine dvd_sub ?_ ?_
    · apply dvd_mul_of_dvd_right
      apply dvd_add
      · apply dvd_mul_of_dvd_left; apply dvd_mul_of_dvd_left; exact dvd_mul_left _ _
      · exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _
    · exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _) _


private lemma binomial_tail (N b u h : ℕ) (hb : b ≤ N) :
    ∑ j ∈ Ico b (N+1), h^j * u^(N-j) * N.choose j ≤
      N^b * h^b * (h+u)^(N-b) := by
  rw [add_pow, mul_sum, sum_Ico_eq_sum_range, show N+1-b=N-b+1 by omega]
  apply sum_le_sum
  intro j hj
  have hc : N.choose (b+j) ≤ N^b * (N-b).choose j := calc
    _ ≤ N.choose (b+j) * (b+j).choose b := Nat.le_mul_of_pos_right _ (Nat.choose_pos (by omega))
    _ = _ := by rw [Nat.choose_mul (by omega : b ≤ b+j), Nat.add_sub_cancel_left]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)
  rw [pow_add]
  calc
    _ ≤ (h^b*h^j) * u^(N-(b+j)) * (N^b*(N-b).choose j) := Nat.mul_le_mul_left _ hc
    _ = _ := by rw [Nat.sub_sub]; simp only [Nat.cast_id]; ring

/-- Apply the Euler operators at degrees d+1 through 2d to the binomial of
degree a+d. Its evaluation at h is divisible by (u+h)^a. The terms through
degree d are divisible by u^a, and all remaining nonzero terms are positive.
The first and last estimates on this tail give the integer separation below. -/
private lemma nearby_power_approx (a d u h : ℕ) (ha : d+1 ≤ a) (hu : 0 < u) (hh : 0 < h) :
    ∃ U V E : ℤ,
      ((u+h : ℕ) : ℤ)^a * V - (u : ℤ)^a * U = E ∧
      (u : ℤ)^(a-d-1) ≤ E ∧
      E ≤ ((a+d : ℕ) : ℤ)^(d+(2*d+1)) * (h : ℤ)^(2*d+1) *
        ((u+h : ℕ) : ℤ)^(a-d-1) ∧
      |V| ≤ (((a+d)*(u+h) : ℕ) : ℤ)^d := by
  let N := a+d
  let b := 2*d+1
  let v := u+h
  have hb : b ≤ N := by dsimp [N,b]; omega
  let f := strip (d+1) ((X+C (u : ℤ))^N) d
  let w (j : ℕ) := ∏ l ∈ range d, ((j : ℤ) - ((d+1 : ℕ)+ (l:ℤ)))
  let T (j : ℕ) := (h : ℤ)^j * (u : ℤ)^(N-j) * (N.choose j : ℤ) * w j
  have hf (j : ℕ) : f.coeff j * (h : ℤ)^j = T j := by
    simp only [f, strip_coeff, coeff_X_add_C_pow, w, T]; ring
  have hdeg : f.natDegree ≤ N := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    simp only [f, strip_coeff, coeff_X_add_C_pow, Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, mul_zero, zero_mul]
  obtain ⟨g,hg⟩ := strip_dvd (d+1) d a (X+C (u:ℤ)) ((X+C (u:ℤ))^N) (dvd_refl _)
  let V := g.eval (h:ℤ)
  have hs : (v:ℤ)^a * V = ∑ j ∈ range (N+1), T j := by
    calc
      _ = f.eval (h:ℤ) := by simp [f,hg,V,v,add_comm]
      _ = _ := by rw [eval_eq_sum_range' (by omega : f.natDegree < N+1)]; simp_rw [hf]
  have low : (u:ℤ)^a ∣ ∑ j ∈ range b, T j := by
    apply dvd_sum
    intro j hj
    have hj' := mem_range.mp hj
    by_cases hjd : j ≤ d
    · have he : a ≤ N-j := by dsimp [N]; omega
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (pow_dvd_pow _ he) _) _) _
    · have hz : w j = 0 := by
        apply prod_eq_zero (i := j-(d+1)) (mem_range.mpr ?_)
        · have he : j-(d+1)+(d+1) = j := by omega
          exact_mod_cast (show (j:ℤ)-((d+1:ℕ)+(↑(j-(d+1)):ℤ))=0 by omega)
        · dsimp [b] at hj'; omega
      simp [T,hz]
  obtain ⟨U,hU⟩ := low
  let E := ∑ j ∈ Ico b (N+1), T j
  have hsplit := sum_range_add_sum_Ico T (by omega : b ≤ N+1)
  have hw (j : ℕ) (hj : j ≤ N) : |w j| ≤ (N:ℤ)^d := by
    dsimp only [w]; rw [abs_prod]
    have hh₁ : ∀ l ∈ range d, |(j:ℤ)-((d+1:ℕ)+(l:ℤ))| ≤ N := by
      intro l hl
      have := mem_range.mp hl
      dsimp [b] at hb
      exact abs_le.mpr ⟨by omega, by omega⟩
    simpa using prod_le_prod (fun l _ => abs_nonneg _) hh₁
  have hwpos (j : ℕ) (hj : b ≤ j) : 1 ≤ w j := by
    apply Finset.one_le_prod
    intro l hl
    have := mem_range.mp hl
    dsimp [b] at hj
    omega
  have hwT (j : ℕ) (hj : j ≤ N) :
      |T j| ≤ (N:ℤ)^d * ((h:ℤ)^j * (u:ℤ)^(N-j) * N.choose j) := by
    simp only [T, abs_mul, abs_pow, abs_of_nonneg (Int.natCast_nonneg _)]
    rw [mul_comm ((N:ℤ)^d)]
    exact mul_le_mul_of_nonneg_left (hw j hj) (by positivity)
  have htail₀ (j : ℕ) (hj : b ≤ j) (hj' : j ≤ N) : (u:ℤ)^(N-j) ≤ T j := by
    have hc : (1:ℤ) ≤ N.choose j := by exact_mod_cast Nat.choose_pos hj'
    have hh' : (1:ℤ) ≤ (h:ℤ)^j := one_le_pow₀ (by exact_mod_cast hh)
    dsimp [T]
    calc
      _ = 1 * (u:ℤ)^(N-j) * 1 * 1 := by ring
      _ ≤ _ := by gcongr; exact hwpos _ hj
  refine ⟨U,V,E,?_,?_,?_,?_⟩
  · change (v:ℤ)^a * V - (u:ℤ)^a * U = E
    dsimp [E]; omega
  · have hsingle := single_le_sum (f := T) (fun i hi => (by positivity : 0 ≤ (u:ℤ)^(N-i)).trans
        (htail₀ i (mem_Ico.mp hi).1 (by have := (mem_Ico.mp hi).2; omega))) (mem_Ico.mpr ⟨le_rfl, (show b < N+1 by omega)⟩)
    simpa [N,b, show a+d-(2*d+1) = a-d-1 by omega] using (htail₀ b le_rfl hb).trans hsingle
  · calc
      E ≤ ∑ j ∈ Ico b (N+1), (N:ℤ)^d * ((h:ℤ)^j * (u:ℤ)^(N-j) * N.choose j) :=
        sum_le_sum fun j hj => (le_abs_self _).trans (hwT _ (by have := (mem_Ico.mp hj).2; omega))
      _ = _ := (mul_sum ..).symm
      _ ≤ (N:ℤ)^d * ((N:ℤ)^b * (h:ℤ)^b * ((h+u:ℕ):ℤ)^(N-b)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); exact_mod_cast binomial_tail N b u h hb
      _ = _ := by rw [show N-b=a-d-1 by dsimp [N,b]; omega, Nat.add_comm h u, pow_add]; dsimp [N,b]; ring
  · have hsum : |(v:ℤ)^a * V| ≤ (N:ℤ)^d * (v:ℤ)^N := by
      rw [hs]
      calc
        _ ≤ _ := abs_sum_le_sum_abs _ _
        _ ≤ _ := sum_le_sum (fun j hj => hwT j (by have := mem_range.mp hj; omega))
        _ = _ := by rw [← mul_sum]; congr 1; simp [v, Nat.cast_add, add_comm (u:ℤ), add_pow]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (v:ℤ)^a)] at hsum
    have H : (v:ℤ)^a * |V| ≤ (v:ℤ)^a * ((N:ℤ)*(v:ℤ))^d := by
      convert hsum using 1; dsimp [N]; rw [pow_add,mul_pow]; ring
    exact (le_of_mul_le_mul_left H (by dsimp [v]; positivity))

private def giants (P x : ℕ) := P.primesLE.filter (fun q => P < q ^ x.factorization q)
private def smallExp (P x q : ℕ) := if q ^ x.factorization q ≤ P then x.factorization q else 0
private def residue (P x : ℕ) := ∏ q ∈ P.primesLE, q ^ smallExp P x q

private lemma residue_pos (P x : ℕ) : 0 < residue P x :=
  prod_pos fun _ hq => pow_pos (Nat.mem_primesLE.mp hq).2.pos _

private lemma split_residue {P x : ℕ} (hx : x ≠ 0) (hs : x.primeFactors ⊆ P.primesLE) :
    residue P x * (∏ q ∈ giants P x, q ^ x.factorization q) = x := by
  have hd : residue P x = ∏ q ∈ P.primesLE with ¬ P < q ^ x.factorization q, q ^ x.factorization q := by
    simp [residue, smallExp, prod_filter]
  rw [hd, mul_comm, giants, prod_filter_mul_prod_filter_not]
  rw [← prod_subset hs (fun q _ hq => by
    have : x.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
    simp [this])]
  exact Nat.prod_factorization_pow_eq_self hx

private lemma interval_count {P n m : ℕ} (hm : 0 < m) (hmP : m ≤ P) :
    ((Ioc n (n+P)).filter fun x => m ∣ x).card ≤ P/m+1 := by
  have hsub : (Ioc 0 n).filter (fun x => m ∣ x) ⊆ (Ioc 0 (n+P)).filter (fun x => m ∣ x) := by
    intro x hx
    simp only [mem_filter,mem_Ioc] at hx ⊢; omega
  have he : (Ioc n (n+P)).filter (fun x => m ∣ x) =
      ((Ioc 0 (n+P)).filter fun x => m ∣ x) \ ((Ioc 0 n).filter fun x => m ∣ x) := by
    ext x
    simp only [mem_filter, mem_Ioc, mem_sdiff]; omega
  rw [he,card_sdiff_of_subset hsub, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div,
    Nat.add_div hm]
  have := Nat.div_pos hmP hm
  split <;> omega

private lemma residual_exp_le {P n q : ℕ} (hP : P ≠ 0) (hq : q.Prime) (S : Finset ℕ)
    (hS : S ⊆ Ioc n (n+P)) :
    ∑ x ∈ S, smallExp P x q ≤ P.factorial.factorization q + Nat.log q P := by
  let L := Nat.log q P
  have he (x : ℕ) : smallExp P x q ≤ L := by
    dsimp [smallExp]; split
    · exact Nat.le_log_of_pow_le hq.one_lt ‹_›
    · omega
  have hex (x : ℕ) : smallExp P x q = ∑ i ∈ Ico 1 (L+1), if i ≤ smallExp P x q then 1 else 0 := by
    rw [sum_boole]
    have H : (Ico 1 (L+1)).filter (fun i => i ≤ smallExp P x q) = Ico 1 (smallExp P x q+1) := by
      ext i; simp only [mem_filter,mem_Ico]; have := he x; omega
    simp [H,Nat.card_Ico]
  rw [sum_congr rfl (fun x _ => hex x)]
  rw [sum_comm,Nat.factorization_factorial hq (Nat.lt_succ_self L)]
  have ones : (∑ _i ∈ Ico 1 (L+1), (1:ℕ))=L := by simp [Nat.card_Ico]
  change _ ≤ _ + L
  conv_rhs => rhs; rw [← ones]
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro i hi
  rw [sum_boole]
  have hsub : S.filter (fun x => i ≤ smallExp P x q) ⊆ (Ioc n (n+P)).filter (fun x => q^i ∣ x) := by
    intro x hx
    obtain ⟨hxS,he⟩ := mem_filter.mp hx
    have hxI := mem_Ioc.mp (hS hxS)
    apply mem_filter.mpr ⟨hS hxS, (hq.pow_dvd_iff_le_factorization (by omega)).mpr ?_⟩
    dsimp [smallExp] at he
    split at he <;> omega
  apply (card_le_card hsub).trans
  apply interval_count (pow_pos hq.pos _)
  have := (mem_Ico.mp hi).2
  exact (Nat.pow_le_pow_right hq.pos (by omega : i ≤ L)).trans (Nat.pow_log_le_self _ hP)

/-- For each prime, count its powers up to P across the interval. A modulus
m ≤ P has at most floor(P/m)+1 multiples there. Legendre's formula supplies the
factorial term, leaving at most one extra power q^floor(log_q P) for that prime. -/
private lemma residual_product {P n : ℕ} (hP : P ≠ 0) (S : Finset ℕ) (hS : S ⊆ Ioc n (n+P)) :
    ∏ x ∈ S, residue P x ≤ P.factorial*P^P.primesLE.card := by
  simp only [residue, prod_comm (s := S) (t := P.primesLE), Finset.prod_pow_eq_pow_sum]
  calc
    _ ≤ ∏ q ∈ P.primesLE, q ^ (P.factorial.factorization q + Nat.log q P) := by
      apply prod_le_prod (fun _ _ => Nat.zero_le _)
      intro q hq
      exact Nat.pow_le_pow_right (Nat.mem_primesLE.mp hq).2.pos (residual_exp_le hP (Nat.mem_primesLE.mp hq).2 S hS)
    _ ≤ _ := by
      simp only [pow_add,prod_mul_distrib]
      apply Nat.mul_le_mul
      · apply le_of_eq
        have hsub : P.factorial.primeFactors ⊆ P.primesLE := by
          intro q hq
          obtain ⟨hqp,hqd,_⟩ := Nat.mem_primeFactors.mp hq
          exact Nat.mem_primesLE.mpr ⟨(hqp.dvd_factorial.mp hqd), hqp⟩
        rw [← prod_subset hsub (fun q _ hq => by
          have h : P.factorial.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
          simp [h])]
        exact Nat.prod_factorization_pow_eq_self (Nat.factorial_ne_zero _)


      · calc
          _ ≤ ∏ _q ∈ P.primesLE, P :=
            prod_le_prod (fun _ _ => Nat.zero_le _) (fun q _ => Nat.pow_log_le_self q hP)
          _ = _ := by simp

private def smoothHits (n P : ℕ) :=
  (Ioc n (n+P)).filter (fun x => x.primeFactors ⊆ P.primesLE)

private lemma card_hits {n P : ℕ} (hnP : P^2 < n)
    (hwin : ∀ k : ℕ, 1 ≤ k → k^2 < n →
      ((n+k).primeFactors.filter fun q => k < q).card ≤ 1) :
    P.primesLE.card ≤ (smoothHits n P).card + n.primeFactors.card := by
  classical
  let D := P.primesLE.filter (fun p => ¬ p ∣ n)
  let k (p : ℕ) := p - n%p
  have hhit (p : ℕ) (hp : p ∈ D) :
      n+k p ∈ smoothHits n P ∧ p ∣ n+k p ∧ k p < p := by
    obtain ⟨hmem,hnd⟩ := mem_filter.mp hp
    obtain ⟨hpP,hprime⟩ := Nat.mem_primesLE.mp hmem
    have hrem := Nat.mod_lt n hprime.pos
    have hrem₁ : n%p ≠ 0 := fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    have hk : 0 < k p ∧ k p < p := by dsimp [k]; omega
    have hplus : n+k p = p*(n/p+1) := by
      rw [Nat.mul_add,Nat.mul_one]; dsimp [k]; have := Nat.mod_add_div n p; omega
    have hpd : p ∣ n+k p := hplus ▸ dvd_mul_right _ _
    have hc := hwin (k p) hk.1 ((Nat.pow_le_pow_left (by omega : k p ≤ P) 2).trans_lt hnP)
    have hpm : p ∈ (n+k p).primeFactors.filter (fun r => k p < r) := mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hprime,hpd,by omega⟩, hk.2⟩
    refine ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,?_⟩,hpd,hk.2⟩
    intro q hq
    apply Nat.mem_primesLE.mpr ⟨?_,(Nat.mem_primeFactors.mp hq).1⟩
    by_contra! H
    have := card_le_one.mp hc p hpm q (mem_filter.mpr ⟨hq,by omega⟩)
    omega
  have hcard := card_le_card_of_injOn (s := D) (t := smoothHits n P) (fun p => n+k p)
    (fun p hp => (hhit p hp).1) (by
      intro p hp q hq heq
      have hpc := (hhit p hp).2; have hqc := (hhit q hq).2
      have hP := Nat.mem_primesLE.mp (mem_filter.mp hp).1
      have hQ := Nat.mem_primesLE.mp (mem_filter.mp hq).1
      change n+k p = n+k q at heq
      have hk : k p = k q := by omega
      have hkp : 0 < k p := by dsimp [k]; have := Nat.mod_lt n hP.2.pos; omega
      have hc := hwin (k p) hkp ((Nat.pow_le_pow_left (by omega : k p ≤ P) 2).trans_lt hnP)
      rw [← hk] at hqc
      exact card_le_one.mp hc p (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hP.2,hpc.1,by omega⟩,hpc.2⟩)
        q (mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hQ.2,hqc.1,by omega⟩,hqc.2⟩))
  have HD : P.primesLE \ D ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨hp₁,hp₂⟩ := mem_sdiff.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesLE.mp hp₁).2, by simpa [D,hp₁] using hp₂, by omega⟩
  have := card_le_card HD
  rw [card_sdiff_of_subset (show D ⊆ P.primesLE from filter_subset ..)] at this
  omega

private lemma primeFactors_count {n : ℕ} (hn : n ≠ 0) : n.primeFactors.card ≤ Nat.log 2 n := by
  apply Nat.le_log_of_pow_le (by decide)
  calc
    2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ n.primeFactors, p := prod_le_prod (fun _ _ => by decide) (fun _ hp => (Nat.mem_primeFactors.mp hp).1.two_le)
    _ ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)

private lemma disjoint_giants {P n x y : ℕ} (hx : x ∈ Ioc n (n+P)) (hy : y ∈ Ioc n (n+P))
    (hne : x ≠ y) : Disjoint (giants P x) (giants P y) := by
  rw [disjoint_left]
  intro q hqx hqy
  obtain ⟨hxp,hxg⟩ := mem_filter.mp hqx
  obtain ⟨_,hyg⟩ := mem_filter.mp hqy
  have hq := (Nat.mem_primesLE.mp hxp).2
  obtain ⟨hx₁,hx₂⟩ := mem_Ioc.mp hx; obtain ⟨hy₁,hy₂⟩ := mem_Ioc.mp hy
  let m := min (x.factorization q) (y.factorization q)
  have hxD : q^m ∣ x := (hq.pow_dvd_iff_le_factorization (by omega)).mpr (min_le_left ..)
  have hyD : q^m ∣ y := (hq.pow_dvd_iff_le_factorization (by omega)).mpr (min_le_right ..)
  have hlarge : P < q^m := by
    dsimp [m]; rcases le_total (x.factorization q) (y.factorization q) with he|he
    · simpa [min_eq_left he] using hxg
    · simpa [min_eq_right he] using hyg
  rcases lt_or_gt_of_ne hne with h|h
  · have := Nat.le_of_dvd (by omega : 0 < y-x) (Nat.dvd_sub hyD hxD); omega
  · have := Nat.le_of_dvd (by omega : 0 < x-y) (Nat.dvd_sub hxD hyD); omega

private lemma giant_budget {P n : ℕ} (S : Finset ℕ) (hS : S ⊆ Ioc n (n+P)) :
    ∑ x ∈ S, (giants P x).card ≤ P.primesLE.card := by
  rw [← card_biUnion (fun x hx y hy hne => disjoint_giants (hS hx) (hS hy) hne)]
  exact card_le_card (biUnion_subset.mpr fun _ _ => filter_subset ..)

private lemma primes_lower (L : ℕ) (hL : 0 < L) :
    2^L ≤ L*(2^L).primesLE.card+(L+1) := by
  let P := (2:ℕ)^L
  have hP : 1 < P := Nat.one_lt_two_pow hL.ne'
  have hc := Chebyshev.pi_ge P
  have hl : 0 < Real.log (P:ℝ) := Real.log_pos (by exact_mod_cast hP)
  have hc' := (div_le_iff₀ hl).mp hc
  have hlog : Real.log (P:ℝ) = L*Real.log 2 := by simp [P,Real.log_pow]
  have hlog' : Real.log (P+1:ℝ) ≤ Real.log (P:ℝ) + Real.log 2 := by
    rw [← Real.log_mul (by positivity : (P:ℝ) ≠ 0) (by norm_num)]
    apply Real.log_le_log (by positivity); have : (1:ℝ) ≤ P := by exact_mod_cast hP.le
    linarith
  have h₂ := Real.log_pos (by norm_num : (1:ℝ) < 2)
  rw [hlog] at hlog' hc'
  rw [← Nat.primesLE_card_eq_primeCounting] at hc'
  change P ≤ L*P.primesLE.card + (L+1)
  have h : (P:ℝ)*Real.log 2 ≤ ((L:ℝ)*P.primesLE.card + (L+1))*Real.log 2 := by
    linarith only [hc',hlog']
  exact_mod_cast (le_of_mul_le_mul_right h h₂)

private def base (P x : ℕ) := (giants P x).sup id

private lemma base_single {P x : ℕ} (h : (giants P x).card = 1) :
    giants P x = {base P x} := by
  obtain ⟨q,hq⟩ := card_eq_one.mp h
  simp [base,hq]

private lemma fixed_short_gap (a u h c e d aMin bN uBits pBits hBits cBits : ℕ)
    (order : d+1 ≤ aMin)
    (upperErr : 2+cBits+cBits+bN*(d+(2*d+1))+hBits*(2*d+1) < uBits*(d+1))
    (lowerErr : 2+cBits+(bN+pBits)*d+pBits < uBits*(aMin-d-1))
    (ha : aMin ≤ a) (hN : a+d ≤ 2^bN) (hu : 2^uBits ≤ u) (hv : u+h ≤ 2^pBits)
    (hh : 0 < h) (hs : h ≤ 2^hBits) (hc : 0 < c) (he : 0 < e)
    (hc' : c ≤ 2^cBits) (he' : e ≤ 2^cBits) :
    ¬ |(c*u^a : ℕ) - ((e*(u+h)^a : ℕ) : ℤ)| ≤ (2:ℤ)^pBits := by
  intro hclose
  let v := u+h
  let N := a+d
  let b := 2*d+1
  let r := a-d-1
  have har : a = r+(d+1) := by dsimp [r]; omega
  have hbig : 4*c*e*N^(d+b)*h^b < v^(d+1) := calc
    _ ≤ 2^2*(2^cBits)*(2^cBits)*(2^bN)^(d+b)*(2^hBits)^b := by gcongr; decide
    _ = 2^(2+cBits+cBits+bN*(d+b)+hBits*b) := by simp only [pow_add,pow_mul]
    _ < (2^uBits)^(d+1) := by rw [← pow_mul]; exact Nat.pow_lt_pow_right (by decide) upperErr
    _ ≤ _ := Nat.pow_le_pow_left (by dsimp [v]; omega) _
  have hlow : 4*c*(N*v)^d*2^pBits < u^r := calc
    _ ≤ 2^2*(2^cBits)*(2^bN*2^pBits)^d*2^pBits := by gcongr; decide
    _ = 2^(2+cBits+(bN+pBits)*d+pBits) := by simp only [pow_add,pow_mul]
    _ < (2^uBits)^r := by
      rw [← pow_mul]
      apply Nat.pow_lt_pow_right (by decide)
      exact lowerErr.trans_le (Nat.mul_le_mul_left _ (by dsimp [r]; omega))
    _ ≤ _ := Nat.pow_le_pow_left hu _
  have hupos : 0 < u := lt_of_lt_of_le (pow_pos (by decide : 0 < 2) _) hu
  obtain ⟨U,V,E,hid,hEₗ,hEᵤ,hV⟩ := nearby_power_approx a d u h (by omega) hupos hh
  change (v:ℤ)^a*V - (u:ℤ)^a*U = E at hid
  change (u:ℤ)^r ≤ E at hEₗ
  change E ≤ (N:ℤ)^(d+b)*(h:ℤ)^b*(v:ℤ)^r at hEᵤ
  push_cast at hV hclose
  change |V| ≤ ((N:ℤ)*(v:ℤ))^d at hV
  change |(c:ℤ)*(u:ℤ)^a - (e:ℤ)*(v:ℤ)^a| ≤ (2:ℤ)^pBits at hclose
  have hl : 4*(c:ℤ)*|V| *(2:ℤ)^pBits < (u:ℤ)^r := by
    apply lt_of_le_of_lt _ (by exact_mod_cast hlow : (4:ℤ)*c*((N:ℤ)*v)^d*(2:ℤ)^pBits < (u:ℤ)^r)
    gcongr
  have hbE : 4*(c:ℤ)*e*E < (v:ℤ)^a := calc
    _ ≤ 4*(c:ℤ)*e*((N:ℤ)^(d+b)*(h:ℤ)^b*(v:ℤ)^r) := by gcongr
    _ = (4*(c:ℤ)*e*(N:ℤ)^(d+b)*(h:ℤ)^b)*(v:ℤ)^r := by ring
    _ < (v:ℤ)^(d+1)*(v:ℤ)^r := by
      apply mul_lt_mul_of_pos_right _ (by dsimp [v]; positivity); exact_mod_cast hbig
    _ = _ := by rw [← pow_add]; congr 1; omega
  have hur : (u:ℤ)^r ≤ (u:ℤ)^a := pow_le_pow_right₀ (by exact_mod_cast hupos) (by omega)
  have hc1 : (1:ℤ) ≤ c := by exact_mod_cast hc
  have he1 : (1:ℤ) ≤ e := by exact_mod_cast he
  let x : ℤ := c*(u:ℤ)^a
  let y : ℤ := e*(v:ℤ)^a
  let M : ℤ := (c:ℤ)*e*E
  let err : ℤ := (c:ℤ)*V*(x-y)
  have hx : (u:ℤ)^a ≤ x := le_mul_of_one_le_left (by positivity) hc1
  have hy : (v:ℤ)^a ≤ y := le_mul_of_one_le_left (by positivity) he1
  have hM : E ≤ M := le_mul_of_one_le_left (le_trans (by positivity) hEₗ)
    (one_le_mul_of_one_le_of_one_le hc1 he1)
  have herr : |err| ≤ (c:ℤ)*|V| *(2:ℤ)^pBits := by
    dsimp [err]; simp only [abs_mul, abs_of_nonneg (Int.natCast_nonneg c)]
    exact mul_le_mul_of_nonneg_left hclose (by positivity)
  have hdist : (2:ℤ)^pBits < x := by
    have hnv : 0 < (N*v)^d := pow_pos (Nat.mul_pos (by dsimp [N]; omega) (by dsimp [v]; omega)) _
    have hh' : 2^pBits < u^r := by
      apply lt_of_le_of_lt _ hlow
      exact Nat.le_mul_of_pos_left _ (by positivity)
    exact (by exact_mod_cast hh' : (2:ℤ)^pBits < (u:ℤ)^r).trans_le (hur.trans hx)
  change |x-y| ≤ _ at hclose
  have hid' : x * (c*V - e*U) = M+err := by
    dsimp [M,err,x,y]; rw [← hid]; ring
  have hstrict : 0 < M+err ∧ M+err < x := by
    have hse : -|err| ≤ err := neg_abs_le _
    have hse' := le_abs_self err
    have hd := abs_le.mp hclose
    have hm4 : 4*M < (v:ℤ)^a := by dsimp [M]; linarith only [hbE]
    have he4 : 4*((c:ℤ)*|V| *(2:ℤ)^pBits) < (u:ℤ)^r := by linarith only [hl]
    constructor <;> omega
  have hz : 1 ≤ (c:ℤ)*V-e*U := by
    by_contra! H
    have hn := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x by omega) (show (c:ℤ)*V-e*U ≤ 0 by omega)
    omega
  have := le_mul_of_one_le_right (show 0 ≤ x by omega) hz
  omega


private lemma fixed_singletons {n : ℕ} (d aMin bN uBits pBits hBits cBits loBits topBits aMax keyBits : ℕ)
    (order : d+1 ≤ aMin)
    (upperErr : 2+cBits+cBits+bN*(d+(2*d+1))+hBits*(2*d+1) < uBits*(d+1))
    (lowerErr : 2+cBits+(bN+pBits)*d+pBits < uBits*(aMin-d-1))
    (expoHi : topBits ≤ uBits*(aMax+1)) (expoLo : cBits+pBits*aMin ≤ loBits)
    (pPos : 0<pBits) (keyEq : pBits=keyBits+hBits) (room : aMax+d≤2^bN) (hlo : 2^loBits ≤ n)
    (hhi : n+2^pBits < 2^topBits)
    (T : Finset ℕ) (hT : T ⊆ smoothHits n (2^pBits))
    (hres : ∀ x ∈ T, residue (2^pBits) x ≤ 2^cBits)
    (hone : ∀ x ∈ T, (giants (2^pBits) x).card=1) :
    T.card ≤ 2^uBits+(2^keyBits+1)*(aMax+1-aMin) := by
  classical
  let P := 2^pBits
  let q := base P
  let a (x : ℕ) := x.factorization (q x)
  let c := residue P
  have hxI {x : ℕ} (hx : x ∈ T) := (mem_filter.mp (hT hx)).1
  have qmem {x : ℕ} (hx : x ∈ T) : q x ∈ giants P x := by
    rw [base_single (hone x hx)]; exact mem_singleton_self _
  have hrepr {x : ℕ} (hx : x ∈ T) : c x * q x ^ a x = x := by
    have hlo' := (mem_Ioc.mp (hxI hx)).1
    have H := split_residue (by omega : x ≠ 0) (mem_filter.mp (hT hx)).2
    rw [base_single (hone x hx), prod_singleton] at H
    exact H
  have qbound {x : ℕ} (hx : x ∈ T) := Nat.mem_primesLE.mp (mem_filter.mp (qmem hx)).1
  have hqa {x : ℕ} (hx : x ∈ T) (high : 2^uBits ≤ q x) : a x ≤ aMax := by
    have lowpow : 2^(uBits*a x) ≤ x := calc
      _ = (2^uBits)^(a x) := pow_mul .. 
      _ ≤ (q x)^(a x) := Nat.pow_le_pow_left high _
      _ ≤ c x*(q x)^(a x) := Nat.le_mul_of_pos_left _ (residue_pos _ _)
      _ = _ := hrepr hx
    have h := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      (lowpow.trans_lt ((mem_Ioc.mp (hxI hx)).2.trans_lt hhi))
    by_contra! bad
    exact (Nat.not_le_of_lt h) (expoHi.trans (Nat.mul_le_mul_left _ bad))
  have hqa' {x : ℕ} (hx : x ∈ T) : aMin ≤ a x := by
    by_contra! small
    have hle : x ≤ 2^(cBits+pBits*a x) := calc
      _ = c x*(q x)^(a x) := (hrepr hx).symm
      _ ≤ (2^cBits)*(2^pBits)^(a x) := Nat.mul_le_mul (hres x hx) (Nat.pow_le_pow_left (qbound hx).1 _)
      _ = _ := by rw [pow_add,pow_mul]
    have lt := Nat.pow_lt_pow_right (by decide : 1 < 2) ((Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left small pPos) _).trans_le expoLo)
    exact (Nat.not_lt_of_ge hlo) (((mem_Ioc.mp (hxI hx)).1).trans (hle.trans_lt lt))
  have hinj {x y : ℕ} (hx : x ∈ T) (hy : y ∈ T) (heq : q x = q y) : x=y := by
    by_contra h
    exact (disjoint_left.mp (disjoint_giants (hxI hx) (hxI hy) h) (qmem hx)) (heq ▸ qmem hy)
  let S := T.filter (fun x => q x < 2^uBits)
  have hsm : S.card ≤ 2^uBits := by
    rw [← card_range (2^uBits)]
    apply card_le_card_of_injOn q (fun x hx => mem_range.mpr (mem_filter.mp hx).2)
    intro x hx y hy; exact hinj (mem_filter.mp hx).1 (mem_filter.mp hy).1
  let R := T \ S
  let H := 2^hBits
  let key (x : ℕ) := (q x / H, a x-aMin)
  have hR {x : ℕ} (hx : x ∈ R) : x ∈ T ∧ 2^uBits ≤ q x := by
    obtain ⟨hx,hn⟩ := mem_sdiff.mp hx
    exact ⟨hx,by simpa [S,hx] using hn⟩
  have hcoll {x y : ℕ} (hxR : x ∈ R) (hyR : y ∈ R) (hkey : key x = key y) :
      ¬ q x < q y := by
    intro hlt
    obtain ⟨hx,hqx⟩ := hR hxR
    obtain ⟨hy,_⟩ := hR hyR
    have hj : q x / H = q y / H := congrArg Prod.fst hkey
    have heq : a x-aMin = a y-aMin := congrArg Prod.snd hkey
    have he : a x = a y := by have := hqa' hx; have := hqa' hy; omega
    let h := q y - q x
    have hadd : q x + h = q y := by dsimp [h]; omega
    have hh : h ≤ H := by
      have h₁ := Nat.mod_add_div (q x) H; have h₂ := Nat.mod_add_div (q y) H
      rw [hj] at h₁
      have := Nat.mod_lt (q y) (show 0 < H by dsimp [H]; positivity)
      dsimp [h]; omega
    have ax := hqa hx hqx
    have hgap := fixed_short_gap (a x) (q x) h (c x) (c y) d aMin bN uBits pBits hBits cBits order upperErr lowerErr (hqa' hx)
      (by omega) hqx (hadd ▸ (qbound hy).1) (by dsimp [h]; omega) hh
      (residue_pos _ _) (residue_pos _ _) (hres x hx) (hres y hy)
    rw [hadd,hrepr hx,he,hrepr hy] at hgap
    have hxi := mem_Ioc.mp (hxI hx); have hyi := mem_Ioc.mp (hxI hy)
    apply hgap
    have H₁ : (x:ℤ) ≤ n+(2:ℤ)^pBits := by exact_mod_cast hxi.2
    have H₂ : (y:ℤ) ≤ n+(2:ℤ)^pBits := by exact_mod_cast hyi.2
    exact abs_le.mpr ⟨by omega,by omega⟩
  have hcard : R.card ≤ ((range (2^keyBits+1)) ×ˢ (range (aMax+1-aMin))).card := by
    apply card_le_card_of_injOn key
    · intro x hx
      have hp := (qbound (hR hx).1).1
      have hdiv : q x / H ≤ 2^keyBits := by
        apply (Nat.div_le_div_right hp).trans
        change 2^pBits / 2^hBits ≤ 2^keyBits
        rw [keyEq,pow_add,Nat.mul_div_cancel _ (by positivity)]
      exact mem_product.mpr ⟨mem_range.mpr (by dsimp [key]; omega), mem_range.mpr (by dsimp [key]; have := hqa (hR hx).1 (hR hx).2; have := hqa' (hR hx).1; omega)⟩
    · intro x hx y hy he
      exact hinj (hR hx).1 (hR hy).1 (by have := hcoll hx hy he; have := hcoll hy hx he.symm; omega)
  rw [card_product,card_range,card_range] at hcard
  have ht : R.card = T.card - S.card := card_sdiff_of_subset (filter_subset ..)
  omega


private theorem fixed_interval_exclusion (n d aMin bN uBits pBits hBits cBits loBits hiBits aMax keyBits : ℕ)
    (order : d+1 ≤ aMin)
    (upperErr : 2+cBits+cBits+bN*(d+(2*d+1))+hBits*(2*d+1) < uBits*(d+1))
    (lowerErr : 2+cBits+(bN+pBits)*d+pBits < uBits*(aMin-d-1))
    (expoHi : hiBits+1 ≤ uBits*(aMax+1)) (expoLo : cBits+pBits*aMin ≤ loBits)
    (pPos : 0<pBits) (keyEq : pBits=keyBits+hBits) (room : aMax+d≤2^bN)
    (near : pBits*2 < loBits) (inRange : pBits ≤ hiBits)
    (count : ∀ D Z : ℕ, cBits*D ≤ pBits*(2^pBits+Z) →
       Z ≤ 2*D+2*hiBits+2^uBits+(2^keyBits+1)*(aMax+1-aMin) →
       2^pBits ≤ pBits*Z+(pBits+1) → False)
    (hlo : 2^loBits ≤ n) (hhi : n < 2^hiBits)
    (hwin : ∀ k : ℕ, 1 ≤ k → k^2 < n →
      ((n+k).primeFactors.filter fun q => k < q).card ≤ 1) : False := by
  classical
  let P := (2:ℕ)^pBits
  have hsmallP : P^2 < n := by
    apply lt_of_lt_of_le _ hlo
    change (2^pBits)^2 < 2^loBits
    rw [← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) near
  have hsum : n+P < 2^(hiBits+1) := by
    have add : P ≤ 2^hiBits := Nat.pow_le_pow_right (by decide) inRange
    have times : (2:ℕ)^(hiBits+1)=2^hiBits*2 := pow_succ 2 hiBits
    rw [times]
    omega
  let S := smoothHits n P
  let D := S.filter (fun x => 2^cBits < residue P x)
  let G := S \ D
  let T := G.filter (fun x => (giants P x).card = 1)
  have hSI : S ⊆ Ioc n (n+P) := filter_subset ..
  have hDS : D ⊆ S := filter_subset ..
  have hGS : G ⊆ S := sdiff_subset
  have hTG : T ⊆ G := filter_subset ..
  have hres {x : ℕ} (hx : x ∈ G) : residue P x ≤ 2^cBits := by
    obtain ⟨hxS,hxD⟩ := mem_sdiff.mp hx; simpa [D,hxS] using hxD
  have htc := fixed_singletons d aMin bN uBits pBits hBits cBits loBits (hiBits+1) aMax keyBits order upperErr lowerErr expoHi expoLo pPos keyEq room hlo hsum T (hTG.trans hGS)
    (fun _ hx => hres (hTG hx)) (fun _ hx => (mem_filter.mp hx).2)
  have hdcount : cBits*D.card ≤ pBits*(P+P.primesLE.card) := by
    apply (pow_le_pow_iff_right₀ (by decide : 1 < (2:ℕ))).mp
    calc
      2^(cBits*D.card) = ∏ _x ∈ D, 2^cBits := by simp [pow_mul]
      _ ≤ ∏ x ∈ D, residue P x := prod_le_prod (fun _ _ => Nat.zero_le _) (fun _ hx => (mem_filter.mp hx).2.le)
      _ ≤ P.factorial*P^P.primesLE.card := residual_product (by dsimp [P]; positivity) D (hDS.trans hSI)
      _ ≤ P^P*P^P.primesLE.card := Nat.mul_le_mul_right _ (Nat.factorial_le_pow _)
      _ = 2^(pBits*(P+P.primesLE.card)) := by rw [← pow_add,pow_mul 2 pBits (P+P.primesLE.card)]
  have hpos {x : ℕ} (hxG : x ∈ G) : 0 < (giants P x).card := by
    have hxS := hGS hxG
    have hxI := mem_Ioc.mp (hSI hxS)
    by_contra! H
    have he := card_eq_zero.mp (Nat.eq_zero_of_le_zero H)
    have hr := split_residue (by omega : x ≠ 0) (mem_filter.mp hxS).2
    rw [he,prod_empty,mul_one] at hr
    have hm := hres hxG
    rw [hr] at hm
    have bound : (2:ℕ)^cBits ≤ 2^loBits := Nat.pow_le_pow_right (by decide) (by omega)
    exact (not_lt_of_ge (hm.trans (bound.trans hlo))) hxI.1
  have hgb : 2*G.card ≤ P.primesLE.card + T.card := calc
    _ = ∑ _x ∈ G, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ G, ((giants P x).card + if (giants P x).card=1 then 1 else 0) := by
      apply sum_le_sum
      intro x hxG
      have := hpos hxG
      split <;> omega
    _ = (∑ x ∈ G, (giants P x).card) + T.card := by rw [sum_add_distrib,sum_boole]; rfl
    _ ≤ _ := Nat.add_le_add_right (giant_budget G (hGS.trans hSI)) _
  have hw : n.primeFactors.card ≤ hiBits := by
    have hn : n ≠ 0 := by
      have hh : 0 < (2:ℕ)^loBits := by positivity
      omega
    exact (primeFactors_count hn).trans (Nat.log_lt_of_lt_pow hn hhi).le
  have hch := card_hits hsmallP hwin
  change P.primesLE.card ≤ S.card+n.primeFactors.card at hch
  have hgcard : G.card = S.card-D.card := card_sdiff_of_subset hDS
  have hpcount : P.primesLE.card ≤ 2*D.card+2*hiBits+2^uBits+(2^keyBits+1)*(aMax+1-aMin) := by omega
  have hpl := primes_lower pBits pPos
  change P ≤ pBits*P.primesLE.card+ (pBits+1) at hpl
  exact count D.card P.primesLE.card hdcount hpcount hpl

/-- A fixed-scale count of first prime hits sharpens the earlier 2,097,152-bit bound. -/
theorem solution_upper_bound {n : ℕ} (sol : Erdos889.v_l 1 n=1) : n<2^650917 := by
  have win (k : ℕ) (hk : 1≤k) (_ : k^2<n) :
      ((n+k).primeFactors.filter fun q => k<q).card ≤ 1 := by
    rw [←OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.v_as_card]
    exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.offset_le_one sol hk
  have cap2097152 : n<2^2097152 := by
    rw [← (by decide : (2:ℕ)^21=2097152)]
    exact Erdos889.effective_binary_cutoff sol
  have cap832053 : n<2^832053 := by
    by_contra! lower
    apply fixed_interval_exclusion n 2057 4853 14 148 160 26 55573 832053 2097152 14169 134
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ lower cap2097152 win
    intro D Z ha hb hc
    norm_num1 at ha hb hc
    omega
  have cap697631 : n<2^697631 := by
    by_contra! lower
    apply fixed_interval_exclusion n 1867 4428 13 135 147 23 46715 697631 832053 6163 124
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ lower cap832053 win
    intro D Z ha hb hc
    norm_num1 at ha hb hc
    omega
  have cap666330 : n<2^666330 := by
    by_contra! lower
    apply fixed_interval_exclusion n 1928 4568 13 125 137 22 40514 666330 697631 5581 115
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ lower cap697631 win
    intro D Z ha hb hc
    norm_num1 at ha hb hc
    omega
  have cap656231 : n<2^656231 := by
    by_contra! lower
    apply fixed_interval_exclusion n 1971 4680 13 120 132 21 38471 656231 666330 5552 111
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ lower cap666330 win
    intro D Z ha hb hc
    norm_num1 at ha hb hc
    omega
  have cap653915 : n<2^653915 := by
    by_contra! lower
    apply fixed_interval_exclusion n 1897 4508 13 124 136 21 40827 653915 656231 5292 115
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ lower cap656231 win
    intro D Z ha hb hc
    norm_num1 at ha hb hc
    omega
  have cap652466 : n<2^652466 := by
    by_contra! lower
    apply fixed_interval_exclusion n 1961 4653 13 120 132 21 38270 652466 653915 5449 111
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ lower cap653915 win
    intro D Z ha hb hc
    norm_num1 at ha hb hc
    omega
  have cap651293 : n<2^651293 := by
    by_contra! lower
    apply fixed_interval_exclusion n 1923 4566 13 122 134 21 39449 651293 652466 5348 113
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ lower cap652466 win
    intro D Z ha hb hc
    norm_num1 at ha hb hc
    omega
  have cap650917 : n<2^650917 := by
    by_contra! lower
    apply fixed_interval_exclusion n 1905 4525 13 123 135 21 40042 650917 651293 5295 114
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ?_ lower cap651293 win
    intro D Z ha hb hc
    norm_num1 at ha hb hc
    omega
  exact cap650917

end Erdos889.FixedInterval

#print axioms Erdos889.FixedInterval.solution_upper_bound
