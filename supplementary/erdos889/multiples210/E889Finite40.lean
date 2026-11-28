import E889Finite40P31
import E889Finite40P37
import E889Finite40P41
import E889Finite40P43
import E889Finite40P47
import E889Finite40P53
import E889Finite40P59
import E889Finite40P61
import E889Finite40P67
import E889Finite40P71
import E889Finite40P73
import E889Finite40P79
import E889Finite40P83
import E889Finite40P89
import E889Finite40P97
import E889Finite40Terminal

/-! All multiples surviving the first-offset tests have a verified fresh-prime witness. -/
namespace Erdos889.Finite40

theorem no_further_solution {n : ℕ} (div : 6469693230∣n) (lo : 10^30<n) (hi : n≤10^40) : v_l 1 n≠1 := by
  intro sol
  have d31 := P31.force div sol lo hi
  have d37 := P37.force d31 sol lo hi
  have d41 := P41.force d37 sol lo hi
  have d43 := P43.force d41 sol lo hi
  have d47 := P47.force d43 sol lo hi
  have d53 := P53.force d47 sol lo hi
  have d59 := P59.force d53 sol lo hi
  have d61 := P61.force d59 sol lo hi
  have d67 := P67.force d61 sol lo hi
  have d71 := P71.force d67 sol lo hi
  have d73 := P73.force d71 sol lo hi
  have d79 := P79.force d73 sol lo hi
  have d83 := P83.force d79 sol lo hi
  have d89 := P89.force d83 sol lo hi
  have d97 := P97.force d89 sol lo hi
  obtain ⟨w,rfl⟩ := d97
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show w≠0 by omega)
  exact terminal (i:=i) (by omega) sol

end Erdos889.Finite40
#print axioms Erdos889.Finite40.no_further_solution
