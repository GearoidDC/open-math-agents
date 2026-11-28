import E889PrimeTwentyThreeTwelfth
import E889PrimeTwentyThreeD2
import E889PrimeTwentyThreeD3
import E889PrimeTwentyThreeD4
import E889PrimeTwentyThreeD5
import E889PrimeTwentyThreeD6
import E889PrimeTwentyThreeD7
import E889PrimeTwentyThreeD8
import E889PrimeTwentyThreeD9
import E889PrimeTwentyThreeD10
import E889PrimeTwentyThreeD11
import E889PrimeTwentyThreeD12
import E889PrimeTwentyThreeD13
import E889PrimeTwentyThreeD14
import E889PrimeTwentyThreeD15
import E889PrimeTwentyThreeD16
import E889PrimeTwentyThreeD17
import E889PrimeTwentyThreeD18
import E889PrimeTwentyThreeD19
import E889PrimeTwentyThreeD20
import E889PrimeTwentyThreeD21
import E889PrimeTwentyThreeD22

/-! Every large prime-successor exception is divisible by each prime through 23. -/

namespace Erdos889.PrimeTwentyThree
private theorem close_from_three {n j x y a b c u v : ℕ} (hj : 0<j) (small : j≤22)
    (big : 1000000000000000000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1)
    (jval : j=x^u*y^v) (shape : n+j=x^a*y^b*23^c)
    (ha : a%12=u) (hb : b%12=v) (hc : c%12=0) : False := by
  let z := x^(a/12)*y^(b/12)*23^(c/12)
  have regroup (p i r : ℕ) (eq : i%12=r) : p^i=p^r*(p^(i/12))^12 := by
    rw [←pow_mul,←pow_add,show r+i/12*12=i by omega]
  have twelfth : n+j=j*z^12 := by
    calc
      n+j=x^a*y^b*23^c := shape
      _=j*z^12 := by
        rw [regroup x a u ha,regroup y b v hb,regroup 23 c 0 hc,jval]
        dsimp only [z]
        rw [mul_pow,mul_pow,pow_zero]
        ring
  have hi : 1<z := by
    by_contra! low
    have zz := Nat.pow_le_pow_left low 12
    have nj := Nat.mul_le_mul_left j zz
    omega
  exact no_twenty_third_twelfth hj small big div pp hi twelfth sol


theorem exclude_offset {n j : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (lo : 0<j) (hi : j<23) (hit : 23∣n+j) : False := by
  interval_cases j
  · have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 23) pp).mp hit
    omega
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D2.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=2) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D3.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=3) (x:=3) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D4.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=4) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=5) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D5.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=5) (x:=5) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=3) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D6.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=6) (x:=2) (y:=3) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=7) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D7.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=7) (x:=7) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D8.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=8) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=3) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D9.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=9) (x:=3) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=5) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D10.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=10) (x:=2) (y:=5) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=11) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D11.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=11) (x:=11) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=3) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D12.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=12) (x:=2) (y:=3) (u:=2) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=13) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D13.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=13) (x:=13) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=7) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D14.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=14) (x:=2) (y:=7) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=5) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D15.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=15) (x:=3) (y:=5) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D16.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=16) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=4) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=17) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D17.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=17) (x:=17) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=3) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D18.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=18) (x:=2) (y:=3) (u:=1) (v:=2) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=19) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    simp only [one_pow,mul_one] at eq
    obtain ⟨ra,rc⟩ := D19.exponents (by omega) div pp sol eq ha hc
    exact close_from_three (j:=19) (x:=19) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=5) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D20.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=20) (x:=2) (y:=5) (u:=2) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=3) (y:=7) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D21.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=21) (x:=3) (y:=7) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc
  · obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (x:=2) (y:=11) (by decide) (by decide) (by decide) (by decide) div hit (by norm_num; omega) (by decide) (by decide) sol
    obtain ⟨ra,rb,rc⟩ := D22.exponents (by omega) div pp sol eq ha hb hc
    exact close_from_three (j:=22) (x:=2) (y:=11) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

theorem primorial_twenty_three {n : ℕ} (big : 1000000000000000000<n) (div : 9699690∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) : 223092870∣n := by
  have d : 23∣n := by
    by_contra missing
    let j := 23-n%23
    have nz : n%23≠0 := fun h => missing (Nat.dvd_of_mod_eq_zero h)
    have hj : 0<j := by dsimp only [j]; omega
    have lo : j<23 := by dsimp only [j]; omega
    have sum : n%23+j=23 := by dsimp only [j]; omega
    have hit : 23∣n+j := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod,Nat.mod_eq_of_lt lo,sum,Nat.mod_self]
    exact exclude_offset big div pp sol hj lo hit
  exact (by decide : Nat.Coprime 9699690 23).mul_dvd_of_dvd_of_dvd div d

end Erdos889.PrimeTwentyThree
#print axioms Erdos889.PrimeTwentyThree.primorial_twenty_three
