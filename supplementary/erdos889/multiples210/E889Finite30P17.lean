import E889Finite30Core

/-! A step in the unconditional finite sieve through 10^30. -/

namespace Erdos889.FiniteThirty
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_0 : groupOK 30030 17 [17] [1]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_1 : groupOK 30030 17 [17,2] [2,4,8,16]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_2 : groupOK 30030 17 [17,3] [3,9]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_3 : groupOK 30030 17 [17,5] [5]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_4 : groupOK 30030 17 [17,3,2] [6,12]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_5 : groupOK 30030 17 [17,7] [7]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_6 : groupOK 30030 17 [17,5,2] [10]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_7 : groupOK 30030 17 [17,11] [11]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_8 : groupOK 30030 17 [17,13] [13]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_9 : groupOK 30030 17 [17,7,2] [14]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g17_10 : groupOK 30030 17 [17,5,3] [15]=true := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem s17 {n : ℕ} (lo : lowBound<n) (hi : n≤highBound)
    (div : 30030∣n) (sol : v_l 1 n=1) : 510510∣n := by
  apply force_step (p:=17) (M:=30030) (by decide) (by decide) (by decide +kernel) div sol
  intro k kp kl dp sup
  interval_cases k
  · apply group_sound [17] [1] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_0 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<1) dk
      have tab : ∀ r : Fin 2, r.val.Prime → r.val∣1 → r.val∈([17] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<2) dk
      have tab : ∀ r : Fin 3, r.val.Prime → r.val∣2 → r.val∈([17,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,3] [3,9] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<3) dk
      have tab : ∀ r : Fin 4, r.val.Prime → r.val∣3 → r.val∈([17,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<4) dk
      have tab : ∀ r : Fin 5, r.val.Prime → r.val∣4 → r.val∈([17,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,5] [5] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_3 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<5) dk
      have tab : ∀ r : Fin 6, r.val.Prime → r.val∣5 → r.val∈([17,5] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,3,2] [6,12] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<6) dk
      have tab : ∀ r : Fin 7, r.val.Prime → r.val∣6 → r.val∈([17,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,7] [7] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_5 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<7) dk
      have tab : ∀ r : Fin 8, r.val.Prime → r.val∣7 → r.val∈([17,7] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<8) dk
      have tab : ∀ r : Fin 9, r.val.Prime → r.val∣8 → r.val∈([17,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,3] [3,9] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<9) dk
      have tab : ∀ r : Fin 10, r.val.Prime → r.val∣9 → r.val∈([17,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,5,2] [10] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_6 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<10) dk
      have tab : ∀ r : Fin 11, r.val.Prime → r.val∣10 → r.val∈([17,5,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,11] [11] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_7 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<11) dk
      have tab : ∀ r : Fin 12, r.val.Prime → r.val∣11 → r.val∈([17,11] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,3,2] [6,12] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<12) dk
      have tab : ∀ r : Fin 13, r.val.Prime → r.val∣12 → r.val∈([17,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,13] [13] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_8 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<13) dk
      have tab : ∀ r : Fin 14, r.val.Prime → r.val∣13 → r.val∈([17,13] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,7,2] [14] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_9 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<14) dk
      have tab : ∀ r : Fin 15, r.val.Prime → r.val∣14 → r.val∈([17,7,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,5,3] [15] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_10 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<15) dk
      have tab : ∀ r : Fin 16, r.val.Prime → r.val∣15 → r.val∈([17,5,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [17,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g17_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<16) dk
      have tab : ∀ r : Fin 17, r.val.Prime → r.val∣16 → r.val∈([17,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk

end Erdos889.FiniteThirty
