import E889Finite30Core

/-! A step in the unconditional finite sieve through 10^30. -/

namespace Erdos889.FiniteThirty
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
def terminal (m : ℕ) : ℕ → ℕ → Bool
  | 0,_ => true
  | j+1,x => witness (m*(x+1)) && terminal m j (x+1)
theorem terminal_sound {m k i x : ℕ} (tab : terminal m k x=true)
    (lo : x ≤ i) (hi : i < x+k) : v_l 1 (m*(i+1))≠1 := by
  induction k generalizing x with
  | zero => omega
  | succ k ih =>
    simp only [terminal,Bool.and_eq_true] at tab
    by_cases first : x=i
    · subst i; exact test_sound tab.1
    · exact ih tab.2 (by omega) (by omega)
set_option maxRecDepth 4000 in
theorem t0 : terminal 557940830126698960967415390 64 0=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t64 : terminal 557940830126698960967415390 64 64=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t128 : terminal 557940830126698960967415390 64 128=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t192 : terminal 557940830126698960967415390 64 192=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t256 : terminal 557940830126698960967415390 64 256=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t320 : terminal 557940830126698960967415390 64 320=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t384 : terminal 557940830126698960967415390 64 384=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t448 : terminal 557940830126698960967415390 64 448=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t512 : terminal 557940830126698960967415390 64 512=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t576 : terminal 557940830126698960967415390 64 576=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t640 : terminal 557940830126698960967415390 64 640=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t704 : terminal 557940830126698960967415390 64 704=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t768 : terminal 557940830126698960967415390 64 768=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t832 : terminal 557940830126698960967415390 64 832=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t896 : terminal 557940830126698960967415390 64 896=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t960 : terminal 557940830126698960967415390 64 960=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1024 : terminal 557940830126698960967415390 64 1024=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1088 : terminal 557940830126698960967415390 64 1088=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1152 : terminal 557940830126698960967415390 64 1152=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1216 : terminal 557940830126698960967415390 64 1216=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1280 : terminal 557940830126698960967415390 64 1280=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1344 : terminal 557940830126698960967415390 64 1344=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1408 : terminal 557940830126698960967415390 64 1408=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1472 : terminal 557940830126698960967415390 64 1472=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1536 : terminal 557940830126698960967415390 64 1536=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1600 : terminal 557940830126698960967415390 64 1600=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1664 : terminal 557940830126698960967415390 64 1664=true := by decide +kernel
set_option maxRecDepth 4000 in
theorem t1728 : terminal 557940830126698960967415390 64 1728=true := by decide +kernel

theorem terminal_all (i : ℕ) (low : 0 ≤ i) (high : i < 1792) : v_l 1 (557940830126698960967415390*(i+1))≠1 := by
  by_cases hcut : i<64
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=0) (i:=i) t0 (by omega) (by omega)
  by_cases hcut : i<128
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=64) (i:=i) t64 (by omega) (by omega)
  by_cases hcut : i<192
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=128) (i:=i) t128 (by omega) (by omega)
  by_cases hcut : i<256
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=192) (i:=i) t192 (by omega) (by omega)
  by_cases hcut : i<320
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=256) (i:=i) t256 (by omega) (by omega)
  by_cases hcut : i<384
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=320) (i:=i) t320 (by omega) (by omega)
  by_cases hcut : i<448
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=384) (i:=i) t384 (by omega) (by omega)
  by_cases hcut : i<512
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=448) (i:=i) t448 (by omega) (by omega)
  by_cases hcut : i<576
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=512) (i:=i) t512 (by omega) (by omega)
  by_cases hcut : i<640
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=576) (i:=i) t576 (by omega) (by omega)
  by_cases hcut : i<704
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=640) (i:=i) t640 (by omega) (by omega)
  by_cases hcut : i<768
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=704) (i:=i) t704 (by omega) (by omega)
  by_cases hcut : i<832
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=768) (i:=i) t768 (by omega) (by omega)
  by_cases hcut : i<896
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=832) (i:=i) t832 (by omega) (by omega)
  by_cases hcut : i<960
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=896) (i:=i) t896 (by omega) (by omega)
  by_cases hcut : i<1024
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=960) (i:=i) t960 (by omega) (by omega)
  by_cases hcut : i<1088
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1024) (i:=i) t1024 (by omega) (by omega)
  by_cases hcut : i<1152
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1088) (i:=i) t1088 (by omega) (by omega)
  by_cases hcut : i<1216
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1152) (i:=i) t1152 (by omega) (by omega)
  by_cases hcut : i<1280
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1216) (i:=i) t1216 (by omega) (by omega)
  by_cases hcut : i<1344
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1280) (i:=i) t1280 (by omega) (by omega)
  by_cases hcut : i<1408
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1344) (i:=i) t1344 (by omega) (by omega)
  by_cases hcut : i<1472
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1408) (i:=i) t1408 (by omega) (by omega)
  by_cases hcut : i<1536
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1472) (i:=i) t1472 (by omega) (by omega)
  by_cases hcut : i<1600
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1536) (i:=i) t1536 (by omega) (by omega)
  by_cases hcut : i<1664
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1600) (i:=i) t1600 (by omega) (by omega)
  by_cases hcut : i<1728
  · exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1664) (i:=i) t1664 (by omega) (by omega)
  exact terminal_sound (m:=557940830126698960967415390) (k:=64) (x:=1728) (i:=i) t1728 (by omega) (by omega)


end Erdos889.FiniteThirty
