import E889Finite30Core

/-! A step in the unconditional finite sieve through 10^30. -/

namespace Erdos889.FiniteThirty
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_0 : groupOK 7420738134810 41 [41] [1]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_1 : groupOK 7420738134810 41 [41,2] [2,4,8,16,32]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_2 : groupOK 7420738134810 41 [41,3] [3,9,27]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_3 : groupOK 7420738134810 41 [41,5] [5,25]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_4 : groupOK 7420738134810 41 [41,3,2] [6,12,18,24,36]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_5 : groupOK 7420738134810 41 [41,7] [7]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_6 : groupOK 7420738134810 41 [41,5,2] [10,20,40]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_7 : groupOK 7420738134810 41 [41,11] [11]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_8 : groupOK 7420738134810 41 [41,13] [13]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_9 : groupOK 7420738134810 41 [41,7,2] [14,28]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_10 : groupOK 7420738134810 41 [41,5,3] [15]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_11 : groupOK 7420738134810 41 [41,17] [17]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_12 : groupOK 7420738134810 41 [41,19] [19]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_13 : groupOK 7420738134810 41 [41,7,3] [21]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_14 : groupOK 7420738134810 41 [41,11,2] [22]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_15 : groupOK 7420738134810 41 [41,23] [23]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_16 : groupOK 7420738134810 41 [41,13,2] [26]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_17 : groupOK 7420738134810 41 [41,29] [29]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_18 : groupOK 7420738134810 41 [41,5,3,2] [30]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_19 : groupOK 7420738134810 41 [41,31] [31]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_20 : groupOK 7420738134810 41 [41,11,3] [33]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_21 : groupOK 7420738134810 41 [41,17,2] [34]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_22 : groupOK 7420738134810 41 [41,7,5] [35]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_23 : groupOK 7420738134810 41 [41,37] [37]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_24 : groupOK 7420738134810 41 [41,19,2] [38]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g41_25 : groupOK 7420738134810 41 [41,13,3] [39]=true := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem s41 {n : ℕ} (lo : lowBound<n) (hi : n≤highBound)
    (div : 7420738134810∣n) (sol : v_l 1 n=1) : 304250263527210∣n := by
  apply force_step (p:=41) (M:=7420738134810) (by decide) (by decide) (by decide +kernel) div sol
  intro k kp kl dp sup
  interval_cases k
  · apply group_sound [41] [1] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_0 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<1) dk
      have tab : ∀ r : Fin 2, r.val.Prime → r.val∣1 → r.val∈([41] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,2] [2,4,8,16,32] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<2) dk
      have tab : ∀ r : Fin 3, r.val.Prime → r.val∣2 → r.val∈([41,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,3] [3,9,27] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<3) dk
      have tab : ∀ r : Fin 4, r.val.Prime → r.val∣3 → r.val∈([41,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,2] [2,4,8,16,32] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<4) dk
      have tab : ∀ r : Fin 5, r.val.Prime → r.val∣4 → r.val∈([41,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,5] [5,25] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_3 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<5) dk
      have tab : ∀ r : Fin 6, r.val.Prime → r.val∣5 → r.val∈([41,5] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,3,2] [6,12,18,24,36] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<6) dk
      have tab : ∀ r : Fin 7, r.val.Prime → r.val∣6 → r.val∈([41,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,7] [7] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_5 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<7) dk
      have tab : ∀ r : Fin 8, r.val.Prime → r.val∣7 → r.val∈([41,7] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,2] [2,4,8,16,32] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<8) dk
      have tab : ∀ r : Fin 9, r.val.Prime → r.val∣8 → r.val∈([41,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,3] [3,9,27] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<9) dk
      have tab : ∀ r : Fin 10, r.val.Prime → r.val∣9 → r.val∈([41,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,5,2] [10,20,40] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_6 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<10) dk
      have tab : ∀ r : Fin 11, r.val.Prime → r.val∣10 → r.val∈([41,5,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,11] [11] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_7 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<11) dk
      have tab : ∀ r : Fin 12, r.val.Prime → r.val∣11 → r.val∈([41,11] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,3,2] [6,12,18,24,36] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<12) dk
      have tab : ∀ r : Fin 13, r.val.Prime → r.val∣12 → r.val∈([41,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,13] [13] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_8 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<13) dk
      have tab : ∀ r : Fin 14, r.val.Prime → r.val∣13 → r.val∈([41,13] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,7,2] [14,28] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_9 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<14) dk
      have tab : ∀ r : Fin 15, r.val.Prime → r.val∣14 → r.val∈([41,7,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,5,3] [15] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_10 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<15) dk
      have tab : ∀ r : Fin 16, r.val.Prime → r.val∣15 → r.val∈([41,5,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,2] [2,4,8,16,32] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<16) dk
      have tab : ∀ r : Fin 17, r.val.Prime → r.val∣16 → r.val∈([41,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,17] [17] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_11 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<17) dk
      have tab : ∀ r : Fin 18, r.val.Prime → r.val∣17 → r.val∈([41,17] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,3,2] [6,12,18,24,36] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<18) dk
      have tab : ∀ r : Fin 19, r.val.Prime → r.val∣18 → r.val∈([41,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,19] [19] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_12 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<19) dk
      have tab : ∀ r : Fin 20, r.val.Prime → r.val∣19 → r.val∈([41,19] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,5,2] [10,20,40] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_6 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<20) dk
      have tab : ∀ r : Fin 21, r.val.Prime → r.val∣20 → r.val∈([41,5,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,7,3] [21] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_13 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<21) dk
      have tab : ∀ r : Fin 22, r.val.Prime → r.val∣21 → r.val∈([41,7,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,11,2] [22] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_14 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<22) dk
      have tab : ∀ r : Fin 23, r.val.Prime → r.val∣22 → r.val∈([41,11,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,23] [23] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_15 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<23) dk
      have tab : ∀ r : Fin 24, r.val.Prime → r.val∣23 → r.val∈([41,23] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,3,2] [6,12,18,24,36] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<24) dk
      have tab : ∀ r : Fin 25, r.val.Prime → r.val∣24 → r.val∈([41,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,5] [5,25] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_3 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<25) dk
      have tab : ∀ r : Fin 26, r.val.Prime → r.val∣25 → r.val∈([41,5] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,13,2] [26] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_16 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<26) dk
      have tab : ∀ r : Fin 27, r.val.Prime → r.val∣26 → r.val∈([41,13,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,3] [3,9,27] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<27) dk
      have tab : ∀ r : Fin 28, r.val.Prime → r.val∣27 → r.val∈([41,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,7,2] [14,28] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_9 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<28) dk
      have tab : ∀ r : Fin 29, r.val.Prime → r.val∣28 → r.val∈([41,7,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,29] [29] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_17 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<29) dk
      have tab : ∀ r : Fin 30, r.val.Prime → r.val∣29 → r.val∈([41,29] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,5,3,2] [30] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_18 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<30) dk
      have tab : ∀ r : Fin 31, r.val.Prime → r.val∣30 → r.val∈([41,5,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,31] [31] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_19 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<31) dk
      have tab : ∀ r : Fin 32, r.val.Prime → r.val∣31 → r.val∈([41,31] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,2] [2,4,8,16,32] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<32) dk
      have tab : ∀ r : Fin 33, r.val.Prime → r.val∣32 → r.val∈([41,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,11,3] [33] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_20 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<33) dk
      have tab : ∀ r : Fin 34, r.val.Prime → r.val∣33 → r.val∈([41,11,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,17,2] [34] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_21 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<34) dk
      have tab : ∀ r : Fin 35, r.val.Prime → r.val∣34 → r.val∈([41,17,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,7,5] [35] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_22 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<35) dk
      have tab : ∀ r : Fin 36, r.val.Prime → r.val∣35 → r.val∈([41,7,5] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,3,2] [6,12,18,24,36] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<36) dk
      have tab : ∀ r : Fin 37, r.val.Prime → r.val∣36 → r.val∈([41,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,37] [37] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_23 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<37) dk
      have tab : ∀ r : Fin 38, r.val.Prime → r.val∣37 → r.val∈([41,37] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,19,2] [38] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_24 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<38) dk
      have tab : ∀ r : Fin 39, r.val.Prime → r.val∣38 → r.val∈([41,19,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,13,3] [39] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_25 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<39) dk
      have tab : ∀ r : Fin 40, r.val.Prime → r.val∣39 → r.val∈([41,13,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [41,5,2] [10,20,40] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g41_6 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<40) dk
      have tab : ∀ r : Fin 41, r.val.Prime → r.val∣40 → r.val∈([41,5,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk

end Erdos889.FiniteThirty
