import Erdos849SparseCollision
import Erdos849TwoColumns
import Erdos849Factors

namespace Erdos849EffectiveMultiplicity

open Erdos849PatternBridge
open Erdos849SparseCollision

/-- An explicit common height for all pairs of columns at most w. -/
def cutoff (w : ℕ) : ℕ :=
  max ((2^(w+1) * (w+1).factorial)^w)
    ((Finset.range (w+1)).sup fun j => (Finset.range (w+1)).sup fun d => heightBound j d w)

/-- Above an explicit cutoff, L+1 distinct rows require at least 2L
    distinct primes. This conclusion has no external number-theory inputs. -/
theorem many_primes_above_cutoff {a L : ℕ} (hL : 2 ≤ L)
    (hc : L < (Erdos849Cases.rows a).ncard) (ha : cutoff (2*L-1) < a) :
    2*L ≤ a.primeFactors.card := by
  by_contra! hf
  let w := 2*L-1
  have hw : a.primeFactors.card ≤ w := by dsimp [w]; omega
  obtain ⟨j,d,hj,hjd,⟨m,hjm,hm⟩,⟨n,hdn,hn⟩⟩ :=
    Erdos849TwoColumns.two_large_columns (by omega) hc
  have hdw : d ≤ w := by
    by_contra! h
    have bound := Erdos849Factors.small_of_deep_representation (by omega : 1 ≤ w+1)
      (by omega : w+1 ≤ d) hdn hn (by omega)
    have hbase : (2^(w+1) * (w+1).factorial)^w ≤ cutoff w := le_max_left _ _
    have hsmall : a ≤ (2^(w+1) * (w+1).factorial)^w := by simpa using bound
    exact (not_le_of_gt ha) (hsmall.trans hbase)
  have hbound := height_bound (by omega : 2 ≤ j) hjd hdn hjm hn hm hw
    (by dsimp [w]; omega)
  have hmemd : d ∈ Finset.range (w+1) := Finset.mem_range.mpr (by omega)
  have hmemj : j ∈ Finset.range (w+1) := Finset.mem_range.mpr (by omega)
  have hbound' : heightBound j d w ≤ cutoff w := calc
    _ ≤ (Finset.range (w+1)).sup (fun x => heightBound j x w) := Finset.le_sup hmemd
    _ ≤ (Finset.range (w+1)).sup (fun y => (Finset.range (w+1)).sup (fun x => heightBound y x w)) :=
      Finset.le_sup (f := fun y => (Finset.range (w+1)).sup (fun x => heightBound y x w)) hmemj
    _ ≤ _ := le_max_right _ _
  exact (not_le_of_gt ha) (hbound.trans hbound')

end Erdos849EffectiveMultiplicity
