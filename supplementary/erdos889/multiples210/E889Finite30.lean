import E889Finite30P13
import E889Finite30P17
import E889Finite30P19
import E889Finite30P23
import E889Finite30P29
import E889Finite30P31
import E889Finite30P37
import E889Finite30P41
import E889Finite30P43
import E889Finite30P47
import E889Finite30P53
import E889Finite30P59
import E889Finite30P61
import E889Finite30P67
import E889Finite30P71
import E889Finite30Terminal

/-! A step in the unconditional finite sieve through 10^30. -/

namespace Erdos889.FiniteThirty
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
set_option maxHeartbeats 4000000 in
theorem no_multiple_through_30 {n : ℕ} (dm : 2310∣n) (lo : 1000000000000000000000<n) (hi : n≤1000000000000000000000000000000) :
    v_l 1 n≠1 := by
  intro sol
  change lowBound<n at lo
  change n≤highBound at hi
  have dv13 := s13 lo hi dm sol
  have dv17 := s17 lo hi dv13 sol
  have dv19 := s19 lo hi dv17 sol
  have dv23 := s23 lo hi dv19 sol
  have dv29 := s29 lo hi dv23 sol
  have dv31 := s31 lo hi dv29 sol
  have dv37 := s37 lo hi dv31 sol
  have dv41 := s41 lo hi dv37 sol
  have dv43 := s43 lo hi dv41 sol
  have dv47 := s47 lo hi dv43 sol
  have dv53 := s53 lo hi dv47 sol
  have dv59 := s59 lo hi dv53 sol
  have dv61 := s61 lo hi dv59 sol
  have dv67 := s67 lo hi dv61 sol
  have dv71 := s71 lo hi dv67 sol
  obtain ⟨w,eq⟩ := dv71
  clear dv67 dv61 dv59 dv53 dv47 dv43 dv41 dv37 dv31 dv29 dv23 dv19 dv17 dv13 dm
  unfold lowBound at lo
  unfold highBound at hi
  have wp : 0<w := by omega
  let i := w-1
  have eq' : n=557940830126698960967415390*(i+1) := by dsimp only [i]; rwa [Nat.sub_add_cancel wp]
  have low : 0 ≤ i := Nat.zero_le _
  have high : i<1792 := by dsimp only [i]; omega
  rw [eq'] at sol
  exact terminal_all i low high sol

end Erdos889.FiniteThirty
#print axioms Erdos889.FiniteThirty.no_multiple_through_30
