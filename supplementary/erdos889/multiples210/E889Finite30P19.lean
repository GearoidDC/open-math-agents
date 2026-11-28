import E889Finite30Core

/-! A step in the unconditional finite sieve through 10^30. -/

namespace Erdos889.FiniteThirty
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_0 : groupOK 510510 19 [19] [1]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_1 : groupOK 510510 19 [19,2] [2,4,8,16]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_2 : groupOK 510510 19 [19,3] [3,9]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_3 : groupOK 510510 19 [19,5] [5]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_4 : groupOK 510510 19 [19,3,2] [6,12,18]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_5 : groupOK 510510 19 [19,7] [7]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_6 : groupOK 510510 19 [19,5,2] [10]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_7 : groupOK 510510 19 [19,11] [11]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_8 : groupOK 510510 19 [19,13] [13]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_9 : groupOK 510510 19 [19,7,2] [14]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_10 : groupOK 510510 19 [19,5,3] [15]=true := by decide +kernel
set_option maxRecDepth 4096 in
set_option maxHeartbeats 18000000 in
private theorem g19_11 : groupOK 510510 19 [19,17] [17]=true := by decide +kernel

set_option maxHeartbeats 1000000 in
theorem s19 {n : ℕ} (lo : lowBound<n) (hi : n≤highBound)
    (div : 510510∣n) (sol : v_l 1 n=1) : 9699690∣n := by
  apply force_step (p:=19) (M:=510510) (by decide) (by decide) (by decide +kernel) div sol
  intro k kp kl dp sup
  interval_cases k
  · apply group_sound [19] [1] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_0 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<1) dk
      have tab : ∀ r : Fin 2, r.val.Prime → r.val∣1 → r.val∈([19] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<2) dk
      have tab : ∀ r : Fin 3, r.val.Prime → r.val∣2 → r.val∈([19,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,3] [3,9] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<3) dk
      have tab : ∀ r : Fin 4, r.val.Prime → r.val∣3 → r.val∈([19,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<4) dk
      have tab : ∀ r : Fin 5, r.val.Prime → r.val∣4 → r.val∈([19,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,5] [5] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_3 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<5) dk
      have tab : ∀ r : Fin 6, r.val.Prime → r.val∣5 → r.val∈([19,5] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,3,2] [6,12,18] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<6) dk
      have tab : ∀ r : Fin 7, r.val.Prime → r.val∣6 → r.val∈([19,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,7] [7] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_5 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<7) dk
      have tab : ∀ r : Fin 8, r.val.Prime → r.val∣7 → r.val∈([19,7] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<8) dk
      have tab : ∀ r : Fin 9, r.val.Prime → r.val∣8 → r.val∈([19,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,3] [3,9] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_2 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<9) dk
      have tab : ∀ r : Fin 10, r.val.Prime → r.val∣9 → r.val∈([19,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,5,2] [10] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_6 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<10) dk
      have tab : ∀ r : Fin 11, r.val.Prime → r.val∣10 → r.val∈([19,5,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,11] [11] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_7 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<11) dk
      have tab : ∀ r : Fin 12, r.val.Prime → r.val∣11 → r.val∈([19,11] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,3,2] [6,12,18] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<12) dk
      have tab : ∀ r : Fin 13, r.val.Prime → r.val∣12 → r.val∈([19,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,13] [13] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_8 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<13) dk
      have tab : ∀ r : Fin 14, r.val.Prime → r.val∣13 → r.val∈([19,13] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,7,2] [14] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_9 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<14) dk
      have tab : ∀ r : Fin 15, r.val.Prime → r.val∣14 → r.val∈([19,7,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,5,3] [15] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_10 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<15) dk
      have tab : ∀ r : Fin 16, r.val.Prime → r.val∣15 → r.val∈([19,5,3] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,2] [2,4,8,16] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_1 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<16) dk
      have tab : ∀ r : Fin 17, r.val.Prime → r.val∣16 → r.val∈([19,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,17] [17] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_11 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<17) dk
      have tab : ∀ r : Fin 18, r.val.Prime → r.val∣17 → r.val∈([19,17] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk
  · apply group_sound [19,3,2] [6,12,18] (by decide) (by decide) (by decide) (by decide)
      (by decide) div dp lo hi (by decide) ?_ g19_4 sol
    intro q pq dq
    rcases sup q pq dq with rfl|dk
    · decide
    · have small := Nat.le_of_dvd (by decide : 0<18) dk
      have tab : ∀ r : Fin 19, r.val.Prime → r.val∣18 → r.val∈([19,3,2] : List ℕ) := by decide
      exact tab ⟨q,by omega⟩ pq dk

end Erdos889.FiniteThirty
