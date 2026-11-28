import E889TwentyNineTwelfth
import E889FortyOneEven
import E889MultiplesFrontier

/-! Nine excluded residue classes modulo 41 for all solutions above 330. -/
namespace Erdos889.FortyOne
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
open Erdos889.PrimeTwentyNine

set_option maxHeartbeats 1200000 in
theorem forbidden_offset {n k : ℕ} (big : 330<n) (sol : v_l 1 n=1)
    (mem : k ∈ [1,4,7,8,13,14,15,16,20]) (hit : 41∣n+k) : False := by
  obtain ⟨huge,div⟩ := Multiples.further_solutions big sol
  have high : 1000000000000000000<n := by omega
  rcases PowerPairs.large_successor big sol with pp|⟨p,pp,shape⟩
  · by_cases odd : k%2=1
    · apply no_forty_one_up_to_nineteen high div pp sol ?_ odd hit
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      omega
    have cases : k=4 ∨ k=8 ∨ k=14 ∨ k=16 ∨ k=20 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      omega
    rcases cases with rfl|rfl|rfl|rfl|rfl
    · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
      simp only [one_pow,mul_one] at eq
      obtain ⟨ra,rc⟩ := PrimeTwentyThree.FortyOneD4.exponents (by omega) div pp sol eq ha hc
      exact close_forty_one_exponents (j:=4) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0)
        (by decide) (by decide) high div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
    · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
      simp only [one_pow,mul_one] at eq
      obtain ⟨ra,rc⟩ := PrimeTwentyThree.FortyOneD8.exponents (by omega) div pp sol eq ha hc
      exact close_forty_one_exponents (j:=8) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=3) (v:=0)
        (by decide) (by decide) high div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
    · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=2) (y:=7) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
      obtain ⟨ra,rb,rc⟩ := PrimeTwentyThree.FortyOneD14.exponents (by omega) div pp sol eq ha hb hc
      exact close_forty_one_exponents (j:=14) (x:=2) (y:=7) (u:=1) (v:=1) (by decide) (by decide)
        high div pp sol (by decide) eq ra rb rc
    · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
      simp only [one_pow,mul_one] at eq
      obtain ⟨ra,rc⟩ := PrimeTwentyThree.FortyOneD16.exponents (by omega) div pp sol eq ha hc
      exact close_forty_one_exponents (j:=16) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=4) (v:=0)
        (by decide) (by decide) high div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
    · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := PrimeTwentyThree.supported_offset (x:=2) (y:=5) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
      obtain ⟨ra,rb,rc⟩ := PrimeTwentyThree.FortyOneD20.exponents (by omega) div pp sol eq ha hb hc
      exact close_forty_one_exponents (j:=20) (x:=2) (y:=5) (u:=2) (v:=1) (by decide) (by decide)
        high div pp sol (by decide) eq ra rb rc
  · have nonzero : p%41≠0 := by
      intro hz
      have ep := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 41) pp).mp (Nat.dvd_of_mod_eq_zero hz)
      subst p
      omega
    have tab : ∀ t : Fin 41, t.val≠0 → ∀ i ∈ ([1,4,7,8,13,14,15,16,20] : List ℕ), (t.val^2+i)%41≠1 := by decide +kernel
    have m := ((Nat.mod_modEq p 41).pow 2).add_right k
    change ((p%41)^2+k)%41 = (p^2+k)%41 at m
    have one : (p^2+k)%41=1 := by rw [←shape]; omega
    exact tab ⟨p%41,Nat.mod_lt _ (by decide)⟩ nonzero k mem (m.trans one)

/-- These classes stay excluded at every size. -/
theorem forbidden_residues {n : ℕ} (big : 330<n) (sol : v_l 1 n=1) :
    n%41 ∉ [21,25,26,27,28,33,34,37,40] := by
  intro mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with h|h|h|h|h|h|h|h|h
  · exact forbidden_offset (k:=20) big sol (by decide) (by omega)
  · exact forbidden_offset (k:=16) big sol (by decide) (by omega)
  · exact forbidden_offset (k:=15) big sol (by decide) (by omega)
  · exact forbidden_offset (k:=14) big sol (by decide) (by omega)
  · exact forbidden_offset (k:=13) big sol (by decide) (by omega)
  · exact forbidden_offset (k:=8) big sol (by decide) (by omega)
  · exact forbidden_offset (k:=7) big sol (by decide) (by omega)
  · exact forbidden_offset (k:=4) big sol (by decide) (by omega)
  · exact forbidden_offset (k:=1) big sol (by decide) (by omega)

end Erdos889.FortyOne

#print axioms Erdos889.FortyOne.forbidden_residues
