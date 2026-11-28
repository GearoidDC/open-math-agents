import Erdos849OddExponentBridge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.Data.Rat.Lemmas

namespace Erdos849FourteenSquareClass

open Erdos849OddExponentBridge

abbrev K := QuadraticAlgebra ℚ 14 0

/-- Writing a square root as u+v√14 shows that a rational square in
the quadratic algebra has one of the two rational square classes. -/
theorem rational_square_in_fourteen (q : ℚ) :
    (∃ w : K, algebraMap ℚ K q = w^2) ↔
      (∃ t : ℚ, q=t^2) ∨ (∃ t : ℚ, q=14*t^2) := by
  constructor
  · rintro ⟨⟨u,v⟩,h⟩
    have hre := congrArg QuadraticAlgebra.re h
    have him := congrArg QuadraticAlgebra.im h
    simp only [sq, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.re_mul] at hre
    simp only [sq, QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.im_mul] at him
    change q = u*u+14*v*v at hre
    change 0 = u*v+v*u+0*v*v at him
    have uv : u*v=0 := by nlinarith only [him]
    rcases mul_eq_zero.mp uv with rfl | rfl
    · exact Or.inr ⟨v,by nlinarith only [hre]⟩
    · exact Or.inl ⟨u,by nlinarith only [hre]⟩
  · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
    · refine ⟨⟨t,0⟩,?_⟩
      apply QuadraticAlgebra.ext <;> simp [sq]
    · refine ⟨⟨0,t⟩,?_⟩
      apply QuadraticAlgebra.ext <;> simp [sq]
      ring

theorem natural_square_in_fourteen (N : ℕ) :
    (∃ w : K, algebraMap ℚ K (N : ℚ) = w^2) ↔
      IsSquare N ∨ ∃ t : ℕ, N=14*t^2 := by
  rw [rational_square_in_fourteen]
  constructor
  · rintro (⟨t,h⟩ | ⟨t,h⟩)
    · exact Or.inl (Rat.isSquare_natCast_iff.mp ⟨t,by simpa [sq] using h⟩)
    · have hs : IsSquare ((14*N : ℕ) : ℚ) := by
        refine ⟨14*t,?_⟩
        push_cast
        rw [h]
        ring
      obtain ⟨b,hb⟩ := Rat.isSquare_natCast_iff.mp hs
      have hdiv : 14 ∣ b^2 := ⟨N,by simpa [sq] using hb.symm⟩
      have sf : Squarefree (14:ℕ) :=
        (Nat.squarefree_mul (by decide : Nat.Coprime 2 7)).mpr
          ⟨Nat.prime_two.prime.squarefree, (by decide : Nat.Prime 7).prime.squarefree⟩
      obtain ⟨v,rfl⟩ := (sf.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hdiv
      refine Or.inr ⟨v,?_⟩
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0<14)
      rw [hb]
      ring
  · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
    · exact Or.inl ⟨t,by push_cast; ring⟩
    · exact Or.inr ⟨t,by push_cast; ring⟩

theorem full_row_identity {x n a : ℕ} (h₆ : x.choose 6 = a) (h₈ : n.choose 8 = a) :
    x.descFactorial 6 * n.descFactorial 8 = 14*(1440*a)^2 := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    h₆, h₈, show Nat.factorial 6 = 720 by decide, show Nat.factorial 8 = 40320 by decide]
  ring

/-- The positive integer complement of a square factor in a positive square is a square. -/
private theorem square_quotient {C z t : ℕ} (hz : z ≠ 0) (h : z^2*C = t^2) :
    ∃ v : ℕ, C=v^2 := by
  have hd : z^2 ∣ t^2 := ⟨C,h.symm⟩
  obtain ⟨v, hv⟩ := (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp hd
  refine ⟨v, ?_⟩
  rw [hv, mul_pow] at h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.pos_of_ne_zero hz) _) h

open scoped symmDiff

def fullSixEight : Finset (ℕ × ℕ) :=
  ((Finset.range 6).image fun s => (6,s)) ∪ ((Finset.range 8).image fun s => (8,s))

set_option maxRecDepth 2000 in
set_option maxHeartbeats 3000000 in
/-- For a pair in any one of the four represented columns, toggling both
full even rows produces a nonempty selection of even size in every row. -/
theorem toggled_pair_admissible :
    ∀ k ∈ Finset.Icc 5 8, ∀ i ∈ Finset.range k, ∀ j ∈ Finset.range k, i < j →
      (fullSixEight ∆ {(k,i),(k,j)}).Nonempty ∧
      ∀ l ∈ Finset.Icc 5 8,
        ((fullSixEight ∆ {(k,i),(k,j)}).filter (fun t => t.1=l)).card % 2 = 0 := by
  decide

/-- Toggle an arbitrary class-14 selection against the two full rows.
This treats pairs in any of the four columns, including slots outside
the two full rows, by the same product identity. -/
theorem square_of_toggle {α : Type*} [DecidableEq α] (A B : Finset α) (f : α → ℕ)
    (nonzero : ∀ s ∈ A ∩ B, f s ≠ 0) (u v : ℕ)
    (hA : A.prod f = 14*u^2) (hB : B.prod f = 14*v^2) :
    ∃ w : ℕ, (A ∆ B).prod f = w^2 := by
  let T := A ∩ B
  have ht : T.prod f ≠ 0 := Finset.prod_ne_zero_iff.mpr nonzero
  have h₁ := Finset.prod_sdiff (show T ⊆ A from Finset.inter_subset_left) (f := f)
  have h₂ := Finset.prod_sdiff (show T ⊆ B from Finset.inter_subset_right) (f := f)
  have hdis : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht'
    exact (Finset.mem_sdiff.mp hs).2 (Finset.mem_sdiff.mp ht').1
  have val : (A ∆ B).prod f = (A \ T).prod f * (B \ T).prod f := by
    rw [Finset.symmDiff_def, Finset.prod_union hdis]
    simp only [T,Finset.sdiff_inter_self_left,Finset.sdiff_inter_self_right]
  apply square_quotient (t:=14*u*v) ht
  calc
    _ = ((A \ T).prod f * T.prod f) * ((B \ T).prod f * T.prod f) := by rw [val]; ring
    _ = _ := by rw [h₁,h₂,hA,hB]; ring

/-- The pair's removal leaves an integer square, using all six factors of
the sixth-column row and exactly the other six factors of the eighth-column row. -/
theorem square_complement {x n a i j z : ℕ} (h₆ : x.choose 6 = a) (h₈ : n.choose 8 = a)
    (hn : 16 ≤ n) (hi : i < 8) (hj : j < 8) (hne : i ≠ j)
    (pair : (n-i)*(n-j) = 14*z^2) :
    ∃ v : ℕ, x.descFactorial 6 * (∏ s ∈ Finset.range 8 \ {i,j}, (n-s)) = v^2 := by
  let S : Finset ℕ := {i,j}
  have hsub : S ⊆ Finset.range 8 := by
    intro s hs
    rcases (show s=i ∨ s=j by simpa [S] using hs) with rfl | rfl <;> simp [*]
  have fac := Finset.prod_sdiff hsub (f := fun s : ℕ => n-s)
  have pval : (∏ s ∈ S, (n-s)) = 14*z^2 := by simpa [S,hne] using pair
  rw [pval, ← Nat.descFactorial_eq_prod_range] at fac
  have hz : z ≠ 0 := by
    intro h
    have pos := Nat.mul_pos (show 0<n-i by omega) (show 0<n-j by omega)
    simp [h] at pair
    omega
  apply square_quotient (t:=1440*a) hz
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 14 by decide)
  calc
    _ = x.descFactorial 6 * ((∏ s ∈ Finset.range 8 \ S, (n-s)) * (14*z^2)) := by
      dsimp [S]; ring
    _ = _ := fac ▸ full_row_identity h₆ h₈

private theorem term_small {x y z : ℕ} (hx : 0 < x) (hy : 0 < y)
    (pair : x*y=14*z^2) (unique : ∀ p, 8 < p → p ∣ x → ¬p ∣ y) : smallSquareClass x := by
  apply small_of_no_odd hx
  rintro ⟨p,hprime,hgt,hodd⟩
  have dv : p ∣ x := Nat.dvd_of_factorization_pos (by omega)
  have ez := Nat.factorization_eq_zero_of_not_dvd (unique p hgt dv)
  have e₁ := congrArg (fun m : ℕ => m.factorization p) pair
  have nz : z ≠ 0 := by rintro rfl; simp [hx.ne',hy.ne'] at pair
  have h14 : ¬p ∣ 14 := by
    intro hp
    have := (hprime.dvd_mul.mp (show p ∣ 2*7 by simpa using hp))
    rcases this with h | h
    · have := Nat.le_of_dvd (by decide : 0<2) h; omega
    · have := Nat.le_of_dvd (by decide : 0<7) h; omega
  simp only [Nat.factorization_mul hx.ne' hy.ne', Nat.factorization_mul
    (by decide : 14 ≠ 0) (pow_ne_zero 2 nz), Finsupp.add_apply, ez,
    Nat.factorization_eq_zero_of_not_dvd h14, Nat.factorization_pow, Finsupp.smul_apply,
    smul_eq_mul, zero_add, add_zero] at e₁
  omega

theorem pair_gives_two_small {n i j z : ℕ} (hn : 16 ≤ n) (hi : i<8) (hj : j<8)
    (hlt : i<j) (pair : (n-i)*(n-j)=14*z^2) :
    smallSquareClass (n-i) ∧ smallSquareClass (n-j) := by
  have unique (p : ℕ) (hgt : 8<p) (h₁ : p ∣ n-i) (h₂ : p ∣ n-j) : False := by
    have pos : 0 < (n-i)-(n-j) := by omega
    have := Nat.le_of_dvd pos (Nat.dvd_sub h₁ h₂)
    omega
  exact ⟨term_small (by omega) (by omega) pair unique,
    term_small (by omega) (by omega) ((Nat.mul_comm _ _).trans pair)
      (fun p hp h₂ h₁ => unique p hp h₁ h₂)⟩

#print axioms full_row_identity
#print axioms rational_square_in_fourteen
#print axioms natural_square_in_fourteen
#print axioms toggled_pair_admissible
#print axioms square_of_toggle
#print axioms square_complement
#print axioms pair_gives_two_small

end Erdos849FourteenSquareClass
