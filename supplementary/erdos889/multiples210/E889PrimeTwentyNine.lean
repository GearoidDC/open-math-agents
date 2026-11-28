import E889PrimeTwentyNineMixedOffsets
import E889PrimeTwentyNinePrimePowerOffsets
import E889TwentyNineTwelfth
import E889PrimeTwentyNineD14
import E889PrimeTwentyNineD21
import E889PrimeTwentyNineD22
import E889PrimeTwentyNineD26
import E889PrimeTwentyNineD28

/-! Every large prime-successor exception is divisible by each prime through 29. -/

namespace Erdos889.PrimeTwentyNine
private theorem close_from_three {n j x y a b c u v : ℕ} (hj : 0<j) (small : j≤28)
    (big : 1000000000000000000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : v_l 1 n=1)
    (jval : j=x^u*y^v) (shape : n+j=x^a*y^b*29^c)
    (ha : a%12=u) (hb : b%12=v) (hc : c%12=0) : False := by
  let z := x^(a/12)*y^(b/12)*29^(c/12)
  have regroup (p i r : ℕ) (eq : i%12=r) : p^i=p^r*(p^(i/12))^12 := by
    rw [←pow_mul,←pow_add,show r+i/12*12=i by omega]
  have twelfth : n+j=j*z^12 := by
    calc
      n+j=x^a*y^b*29^c := shape
      _=j*z^12 := by
        rw [regroup x a u ha,regroup y b v hb,regroup 29 c 0 hc,jval]
        dsimp only [z]
        rw [mul_pow,mul_pow,pow_zero]
        ring
  have hi : 1<z := by
    by_contra! low
    have zz := Nat.pow_le_pow_left low 12
    have nj := Nat.mul_le_mul_left j zz
    omega
  exact no_twenty_ninth_twelfth hj small big div pp hi twelfth sol


private theorem exclude1 {n : ℕ} (big : 1000000000000000000<n) (pp : (n+1).Prime) (hit : 29∣n+1) : False := by
  have eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 29) pp).mp hit
  omega

private theorem exclude2 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+2) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=2) (q:=29) (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*1∣223092870).trans div) (by decide : 2*1∣2)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D2.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=2) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude3 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+3) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=3) (q:=29) (x:=3) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 3*1∣223092870).trans div) (by decide : 3*1∣3)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D3.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=3) (x:=3) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude4 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+4) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=4) (q:=29) (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*1∣223092870).trans div) (by decide : 2*1∣4)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D4.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=4) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude5 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+5) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=5) (q:=29) (x:=5) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 5*1∣223092870).trans div) (by decide : 5*1∣5)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D5.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=5) (x:=5) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude6 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+6) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=6) (q:=29) (x:=2) (y:=3) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*3∣223092870).trans div) (by decide : 2*3∣6)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D6.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=6) (x:=2) (y:=3) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude7 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+7) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=7) (q:=29) (x:=7) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 7*1∣223092870).trans div) (by decide : 7*1∣7)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D7.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=7) (x:=7) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude8 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+8) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=8) (q:=29) (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*1∣223092870).trans div) (by decide : 2*1∣8)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D8.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=8) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=3) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude9 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+9) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=9) (q:=29) (x:=3) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 3*1∣223092870).trans div) (by decide : 3*1∣9)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D9.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=9) (x:=3) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude10 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+10) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=10) (q:=29) (x:=2) (y:=5) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*5∣223092870).trans div) (by decide : 2*5∣10)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D10.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=10) (x:=2) (y:=5) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude11 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+11) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=11) (q:=29) (x:=11) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 11*1∣223092870).trans div) (by decide : 11*1∣11)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D11.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=11) (x:=11) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude12 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+12) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=12) (q:=29) (x:=2) (y:=3) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*3∣223092870).trans div) (by decide : 2*3∣12)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D12.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=12) (x:=2) (y:=3) (u:=2) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude13 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+13) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=13) (q:=29) (x:=13) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 13*1∣223092870).trans div) (by decide : 13*1∣13)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D13.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=13) (x:=13) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude14 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+14) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=14) (q:=29) (x:=2) (y:=7) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*7∣223092870).trans div) (by decide : 2*7∣14)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D14.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=14) (x:=2) (y:=7) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude15 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+15) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=15) (q:=29) (x:=3) (y:=5) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 3*5∣223092870).trans div) (by decide : 3*5∣15)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D15.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=15) (x:=3) (y:=5) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude16 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+16) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=16) (q:=29) (x:=2) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*1∣223092870).trans div) (by decide : 2*1∣16)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D16.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=16) (x:=2) (y:=1) (a:=a) (b:=0) (c:=c) (u:=4) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude17 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+17) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=17) (q:=29) (x:=17) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 17*1∣223092870).trans div) (by decide : 17*1∣17)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D17.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=17) (x:=17) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude18 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+18) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=18) (q:=29) (x:=2) (y:=3) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*3∣223092870).trans div) (by decide : 2*3∣18)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D18.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=18) (x:=2) (y:=3) (u:=1) (v:=2) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude19 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+19) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=19) (q:=29) (x:=19) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 19*1∣223092870).trans div) (by decide : 19*1∣19)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D19.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=19) (x:=19) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude20 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+20) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=20) (q:=29) (x:=2) (y:=5) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*5∣223092870).trans div) (by decide : 2*5∣20)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D20.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=20) (x:=2) (y:=5) (u:=2) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude21 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+21) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=21) (q:=29) (x:=3) (y:=7) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 3*7∣223092870).trans div) (by decide : 3*7∣21)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D21.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=21) (x:=3) (y:=7) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude22 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+22) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=22) (q:=29) (x:=2) (y:=11) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*11∣223092870).trans div) (by decide : 2*11∣22)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D22.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=22) (x:=2) (y:=11) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude23 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+23) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=23) (q:=29) (x:=23) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 23*1∣223092870).trans div) (by decide : 23*1∣23)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D23.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=23) (x:=23) (y:=1) (a:=a) (b:=0) (c:=c) (u:=1) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude24 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+24) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=24) (q:=29) (x:=2) (y:=3) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*3∣223092870).trans div) (by decide : 2*3∣24)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D24.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=24) (x:=2) (y:=3) (u:=3) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude25 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+25) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=25) (q:=29) (x:=5) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 5*1∣223092870).trans div) (by decide : 5*1∣25)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D25.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=25) (x:=5) (y:=1) (a:=a) (b:=0) (c:=c) (u:=2) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude26 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+26) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=26) (q:=29) (x:=2) (y:=13) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*13∣223092870).trans div) (by decide : 2*13∣26)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D26.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=26) (x:=2) (y:=13) (u:=1) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

private theorem exclude27 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+27) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=27) (q:=29) (x:=3) (y:=1) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 3*1∣223092870).trans div) (by decide : 3*1∣27)) (by decide) (by decide +kernel) sol
  simp only [one_pow,mul_one] at eq
  obtain ⟨ra,rc⟩ := D27.exponents (by omega) div pp sol eq ha hc
  exact close_from_three (j:=27) (x:=3) (y:=1) (a:=a) (b:=0) (c:=c) (u:=3) (v:=0) (by decide) (by decide) big div pp sol (by decide) (by simpa only [pow_zero,mul_one] using eq) ra rfl rc

private theorem exclude28 {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (hit : 29∣n+28) : False := by
  obtain ⟨a,b,c,eq,ha,hb,hc⟩ := supported_offset (j:=28) (q:=29) (x:=2) (y:=7) (by decide) (by decide) (by decide) (by decide) div hit (dvd_add ((by decide : 2*7∣223092870).trans div) (by decide : 2*7∣28)) (by decide) (by decide +kernel) sol
  obtain ⟨ra,rb,rc⟩ := D28.exponents (by omega) div pp sol eq ha hb hc
  exact close_from_three (j:=28) (x:=2) (y:=7) (u:=2) (v:=1) (by decide) (by decide) big div pp sol (by decide) eq ra rb rc

theorem exclude_offset {n j : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) (lo : 0<j) (hi : j<29) (hit : 29∣n+j) : False := by
  interval_cases j
  · exact exclude1 big pp hit
  · exact exclude2 big div pp sol hit
  · exact exclude3 big div pp sol hit
  · exact exclude4 big div pp sol hit
  · exact exclude5 big div pp sol hit
  · exact exclude6 big div pp sol hit
  · exact exclude7 big div pp sol hit
  · exact exclude8 big div pp sol hit
  · exact exclude9 big div pp sol hit
  · exact exclude10 big div pp sol hit
  · exact exclude11 big div pp sol hit
  · exact exclude12 big div pp sol hit
  · exact exclude13 big div pp sol hit
  · exact exclude14 big div pp sol hit
  · exact exclude15 big div pp sol hit
  · exact exclude16 big div pp sol hit
  · exact exclude17 big div pp sol hit
  · exact exclude18 big div pp sol hit
  · exact exclude19 big div pp sol hit
  · exact exclude20 big div pp sol hit
  · exact exclude21 big div pp sol hit
  · exact exclude22 big div pp sol hit
  · exact exclude23 big div pp sol hit
  · exact exclude24 big div pp sol hit
  · exact exclude25 big div pp sol hit
  · exact exclude26 big div pp sol hit
  · exact exclude27 big div pp sol hit
  · exact exclude28 big div pp sol hit

theorem primorial_twenty_nine {n : ℕ} (big : 1000000000000000000<n) (div : 223092870∣n)
    (pp : (n+1).Prime) (sol : v_l 1 n=1) : 6469693230∣n := by
  have d : 29∣n := by
    by_contra missing
    let j := 29-n%29
    have nz : n%29≠0 := fun h => missing (Nat.dvd_of_mod_eq_zero h)
    have hj : 0<j := by dsimp only [j]; omega
    have lo : j<29 := by dsimp only [j]; omega
    have sum : n%29+j=29 := by dsimp only [j]; omega
    have hit : 29∣n+j := by
      apply Nat.dvd_of_mod_eq_zero
      rw [Nat.add_mod,Nat.mod_eq_of_lt lo,sum,Nat.mod_self]
    exact exclude_offset big div pp sol hj lo hit
  exact (by decide : Nat.Coprime 223092870 29).mul_dvd_of_dvd_of_dvd div d

end Erdos889.PrimeTwentyNine
#print axioms Erdos889.PrimeTwentyNine.primorial_twenty_nine
