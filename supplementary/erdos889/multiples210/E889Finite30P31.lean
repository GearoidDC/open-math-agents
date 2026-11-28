import E889Finite30Core

/-! A step in the unconditional finite sieve through 10^30. -/

namespace Erdos889.FiniteThirty
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_0 : groupOK 6469693230 31 [31] [1]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_1 : groupOK 6469693230 31 [31,2] [2,4,8,16]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_2 : groupOK 6469693230 31 [31,3] [3,9,27]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_3 : groupOK 6469693230 31 [31,5] [5,25]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_4 : groupOK 6469693230 31 [31,3,2] [6,12,18,24]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_5 : groupOK 6469693230 31 [31,7] [7]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_6 : groupOK 6469693230 31 [31,5,2] [10,20]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_7 : groupOK 6469693230 31 [31,11] [11]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_8 : groupOK 6469693230 31 [31,13] [13]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_9 : groupOK 6469693230 31 [31,7,2] [14,28]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_10 : groupOK 6469693230 31 [31,5,3] [15]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_11 : groupOK 6469693230 31 [31,17] [17]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_12 : groupOK 6469693230 31 [31,19] [19]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_13 : groupOK 6469693230 31 [31,7,3] [21]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_14 : groupOK 6469693230 31 [31,11,2] [22]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_15 : groupOK 6469693230 31 [31,23] [23]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_16 : groupOK 6469693230 31 [31,13,2] [26]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_17 : groupOK 6469693230 31 [31,29] [29]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g31_18 : groupOK 6469693230 31 [31,5,3,2] [30]=true := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem s31 {n : ℕ} (lo : lowBound<n) (hi : n≤highBound)
    (div : 6469693230∣n) (sol : v_l 1 n=1) : 200560490130∣n := by
  apply force_step (p:=31) (M:=6469693230) (by decide) (by decide) (by decide +kernel) div sol
  intro k kp kl dp sup
  interval_cases k
  · apply group_sound [31] [1] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_0 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<1) dk
      have tab : ∀ r : Fin 2, r.val.Prime → r.val∣1 → r.val∈([31] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<2) dk
      have tab : ∀ r : Fin 3, r.val.Prime → r.val∣2 → r.val∈([31,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,3] [3,9,27] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<3) dk
      have tab : ∀ r : Fin 4, r.val.Prime → r.val∣3 → r.val∈([31,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<4) dk
      have tab : ∀ r : Fin 5, r.val.Prime → r.val∣4 → r.val∈([31,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,5] [5,25] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_3 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<5) dk
      have tab : ∀ r : Fin 6, r.val.Prime → r.val∣5 → r.val∈([31,5] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,3,2] [6,12,18,24] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<6) dk
      have tab : ∀ r : Fin 7, r.val.Prime → r.val∣6 → r.val∈([31,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,7] [7] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_5 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<7) dk
      have tab : ∀ r : Fin 8, r.val.Prime → r.val∣7 → r.val∈([31,7] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<8) dk
      have tab : ∀ r : Fin 9, r.val.Prime → r.val∣8 → r.val∈([31,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,3] [3,9,27] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<9) dk
      have tab : ∀ r : Fin 10, r.val.Prime → r.val∣9 → r.val∈([31,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,5,2] [10,20] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_6 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<10) dk
      have tab : ∀ r : Fin 11, r.val.Prime → r.val∣10 → r.val∈([31,5,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,11] [11] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_7 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<11) dk
      have tab : ∀ r : Fin 12, r.val.Prime → r.val∣11 → r.val∈([31,11] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,3,2] [6,12,18,24] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<12) dk
      have tab : ∀ r : Fin 13, r.val.Prime → r.val∣12 → r.val∈([31,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,13] [13] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_8 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<13) dk
      have tab : ∀ r : Fin 14, r.val.Prime → r.val∣13 → r.val∈([31,13] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,7,2] [14,28] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_9 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<14) dk
      have tab : ∀ r : Fin 15, r.val.Prime → r.val∣14 → r.val∈([31,7,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,5,3] [15] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_10 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<15) dk
      have tab : ∀ r : Fin 16, r.val.Prime → r.val∣15 → r.val∈([31,5,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<16) dk
      have tab : ∀ r : Fin 17, r.val.Prime → r.val∣16 → r.val∈([31,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,17] [17] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_11 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<17) dk
      have tab : ∀ r : Fin 18, r.val.Prime → r.val∣17 → r.val∈([31,17] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,3,2] [6,12,18,24] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<18) dk
      have tab : ∀ r : Fin 19, r.val.Prime → r.val∣18 → r.val∈([31,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,19] [19] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_12 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<19) dk
      have tab : ∀ r : Fin 20, r.val.Prime → r.val∣19 → r.val∈([31,19] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,5,2] [10,20] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_6 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<20) dk
      have tab : ∀ r : Fin 21, r.val.Prime → r.val∣20 → r.val∈([31,5,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,7,3] [21] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_13 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<21) dk
      have tab : ∀ r : Fin 22, r.val.Prime → r.val∣21 → r.val∈([31,7,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,11,2] [22] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_14 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<22) dk
      have tab : ∀ r : Fin 23, r.val.Prime → r.val∣22 → r.val∈([31,11,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,23] [23] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_15 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<23) dk
      have tab : ∀ r : Fin 24, r.val.Prime → r.val∣23 → r.val∈([31,23] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,3,2] [6,12,18,24] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<24) dk
      have tab : ∀ r : Fin 25, r.val.Prime → r.val∣24 → r.val∈([31,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,5] [5,25] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_3 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<25) dk
      have tab : ∀ r : Fin 26, r.val.Prime → r.val∣25 → r.val∈([31,5] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,13,2] [26] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_16 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<26) dk
      have tab : ∀ r : Fin 27, r.val.Prime → r.val∣26 → r.val∈([31,13,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,3] [3,9,27] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<27) dk
      have tab : ∀ r : Fin 28, r.val.Prime → r.val∣27 → r.val∈([31,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,7,2] [14,28] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_9 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<28) dk
      have tab : ∀ r : Fin 29, r.val.Prime → r.val∣28 → r.val∈([31,7,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,29] [29] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_17 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<29) dk
      have tab : ∀ r : Fin 30, r.val.Prime → r.val∣29 → r.val∈([31,29] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [31,5,3,2] [30] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g31_18 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<30) dk
      have tab : ∀ r : Fin 31, r.val.Prime → r.val∣30 → r.val∈([31,5,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk

end Erdos889.FiniteThirty
