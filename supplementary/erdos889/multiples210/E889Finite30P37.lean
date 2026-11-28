import E889Finite30Core

/-! A step in the unconditional finite sieve through 10^30. -/

namespace Erdos889.FiniteThirty
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_0 : groupOK 200560490130 37 [37] [1]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_1 : groupOK 200560490130 37 [37,2] [2,4,8,16,32]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_2 : groupOK 200560490130 37 [37,3] [3,9,27]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_3 : groupOK 200560490130 37 [37,5] [5,25]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_4 : groupOK 200560490130 37 [37,3,2] [6,12,18,24,36]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_5 : groupOK 200560490130 37 [37,7] [7]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_6 : groupOK 200560490130 37 [37,5,2] [10,20]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_7 : groupOK 200560490130 37 [37,11] [11]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_8 : groupOK 200560490130 37 [37,13] [13]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_9 : groupOK 200560490130 37 [37,7,2] [14,28]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_10 : groupOK 200560490130 37 [37,5,3] [15]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_11 : groupOK 200560490130 37 [37,17] [17]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_12 : groupOK 200560490130 37 [37,19] [19]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_13 : groupOK 200560490130 37 [37,7,3] [21]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_14 : groupOK 200560490130 37 [37,11,2] [22]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_15 : groupOK 200560490130 37 [37,23] [23]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_16 : groupOK 200560490130 37 [37,13,2] [26]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_17 : groupOK 200560490130 37 [37,29] [29]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_18 : groupOK 200560490130 37 [37,5,3,2] [30]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_19 : groupOK 200560490130 37 [37,31] [31]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_20 : groupOK 200560490130 37 [37,11,3] [33]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_21 : groupOK 200560490130 37 [37,17,2] [34]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g37_22 : groupOK 200560490130 37 [37,7,5] [35]=true := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem s37 {n : ℕ} (lo : lowBound<n) (hi : n≤highBound)
    (div : 200560490130∣n) (sol : v_l 1 n=1) : 7420738134810∣n := by
  apply force_step (p:=37) (M:=200560490130) (by decide) (by decide) (by decide +kernel) div sol
  intro k kp kl dp sup
  interval_cases k
  · apply group_sound [37] [1] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_0 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<1) dk
      have tab : ∀ r : Fin 2, r.val.Prime → r.val∣1 → r.val∈([37] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,2] [2,4,8,16,32] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<2) dk
      have tab : ∀ r : Fin 3, r.val.Prime → r.val∣2 → r.val∈([37,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,3] [3,9,27] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<3) dk
      have tab : ∀ r : Fin 4, r.val.Prime → r.val∣3 → r.val∈([37,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,2] [2,4,8,16,32] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<4) dk
      have tab : ∀ r : Fin 5, r.val.Prime → r.val∣4 → r.val∈([37,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,5] [5,25] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_3 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<5) dk
      have tab : ∀ r : Fin 6, r.val.Prime → r.val∣5 → r.val∈([37,5] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,3,2] [6,12,18,24,36] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<6) dk
      have tab : ∀ r : Fin 7, r.val.Prime → r.val∣6 → r.val∈([37,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,7] [7] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_5 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<7) dk
      have tab : ∀ r : Fin 8, r.val.Prime → r.val∣7 → r.val∈([37,7] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,2] [2,4,8,16,32] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<8) dk
      have tab : ∀ r : Fin 9, r.val.Prime → r.val∣8 → r.val∈([37,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,3] [3,9,27] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<9) dk
      have tab : ∀ r : Fin 10, r.val.Prime → r.val∣9 → r.val∈([37,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,5,2] [10,20] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_6 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<10) dk
      have tab : ∀ r : Fin 11, r.val.Prime → r.val∣10 → r.val∈([37,5,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,11] [11] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_7 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<11) dk
      have tab : ∀ r : Fin 12, r.val.Prime → r.val∣11 → r.val∈([37,11] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,3,2] [6,12,18,24,36] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<12) dk
      have tab : ∀ r : Fin 13, r.val.Prime → r.val∣12 → r.val∈([37,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,13] [13] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_8 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<13) dk
      have tab : ∀ r : Fin 14, r.val.Prime → r.val∣13 → r.val∈([37,13] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,7,2] [14,28] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_9 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<14) dk
      have tab : ∀ r : Fin 15, r.val.Prime → r.val∣14 → r.val∈([37,7,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,5,3] [15] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_10 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<15) dk
      have tab : ∀ r : Fin 16, r.val.Prime → r.val∣15 → r.val∈([37,5,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,2] [2,4,8,16,32] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<16) dk
      have tab : ∀ r : Fin 17, r.val.Prime → r.val∣16 → r.val∈([37,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,17] [17] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_11 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<17) dk
      have tab : ∀ r : Fin 18, r.val.Prime → r.val∣17 → r.val∈([37,17] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,3,2] [6,12,18,24,36] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<18) dk
      have tab : ∀ r : Fin 19, r.val.Prime → r.val∣18 → r.val∈([37,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,19] [19] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_12 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<19) dk
      have tab : ∀ r : Fin 20, r.val.Prime → r.val∣19 → r.val∈([37,19] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,5,2] [10,20] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_6 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<20) dk
      have tab : ∀ r : Fin 21, r.val.Prime → r.val∣20 → r.val∈([37,5,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,7,3] [21] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_13 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<21) dk
      have tab : ∀ r : Fin 22, r.val.Prime → r.val∣21 → r.val∈([37,7,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,11,2] [22] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_14 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<22) dk
      have tab : ∀ r : Fin 23, r.val.Prime → r.val∣22 → r.val∈([37,11,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,23] [23] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_15 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<23) dk
      have tab : ∀ r : Fin 24, r.val.Prime → r.val∣23 → r.val∈([37,23] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,3,2] [6,12,18,24,36] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<24) dk
      have tab : ∀ r : Fin 25, r.val.Prime → r.val∣24 → r.val∈([37,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,5] [5,25] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_3 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<25) dk
      have tab : ∀ r : Fin 26, r.val.Prime → r.val∣25 → r.val∈([37,5] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,13,2] [26] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_16 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<26) dk
      have tab : ∀ r : Fin 27, r.val.Prime → r.val∣26 → r.val∈([37,13,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,3] [3,9,27] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<27) dk
      have tab : ∀ r : Fin 28, r.val.Prime → r.val∣27 → r.val∈([37,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,7,2] [14,28] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_9 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<28) dk
      have tab : ∀ r : Fin 29, r.val.Prime → r.val∣28 → r.val∈([37,7,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,29] [29] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_17 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<29) dk
      have tab : ∀ r : Fin 30, r.val.Prime → r.val∣29 → r.val∈([37,29] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,5,3,2] [30] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_18 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<30) dk
      have tab : ∀ r : Fin 31, r.val.Prime → r.val∣30 → r.val∈([37,5,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,31] [31] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_19 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<31) dk
      have tab : ∀ r : Fin 32, r.val.Prime → r.val∣31 → r.val∈([37,31] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,2] [2,4,8,16,32] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<32) dk
      have tab : ∀ r : Fin 33, r.val.Prime → r.val∣32 → r.val∈([37,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,11,3] [33] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_20 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<33) dk
      have tab : ∀ r : Fin 34, r.val.Prime → r.val∣33 → r.val∈([37,11,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,17,2] [34] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_21 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<34) dk
      have tab : ∀ r : Fin 35, r.val.Prime → r.val∣34 → r.val∈([37,17,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,7,5] [35] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_22 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<35) dk
      have tab : ∀ r : Fin 36, r.val.Prime → r.val∣35 → r.val∈([37,7,5] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [37,3,2] [6,12,18,24,36] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g37_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<36) dk
      have tab : ∀ r : Fin 37, r.val.Prime → r.val∣36 → r.val∈([37,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk

end Erdos889.FiniteThirty
