import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! Global uniqueness on the shallow diagonal of a Lind–Singmaster tie. -/

namespace Erdos849LindDiagonal

private theorem step {r c : ℕ} (hc : 0 < c) (hcr : c ≤ r) :
    (r+1).choose (c-1) * ((r-c+1)*(r-c+2)) =
      r.choose c * ((r+1)*c) := by
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc.ne'
  simp only [Nat.add_one_sub_one]
  have l := Nat.choose_mul_succ_eq r v
  have h := Nat.choose_succ_right_eq r v
  rw [show r+1-v = r-(v+1)+2 by omega] at l
  rw [show r-v = r-(v+1)+1 by omega] at h
  calc
    _ = ((r+1).choose v * (r-(v+1)+2))*(r-(v+1)+1) := by ring
    _ = (r.choose v * (r-(v+1)+1))*(r+1) := by rw [← l]; ring
    _ = _ := by rw [← h]; simp only [Nat.succ_eq_add_one]; ring

private theorem balance {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (he : (n+1).choose (k-1) = n.choose k) :
    (n-k+1)*(n-k+2) = (n+1)*k := by
  have h := step hk hkn
  rw [he] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.choose_pos hkn) h

/-- Signed error of the factorial-ratio equation at a displaced diagonal step. -/
theorem signed_error {n k u t : ℤ} (h : n=k+u)
    (he : (u+1)*(u+2) = (n+1)*k) :
    (u+2*t+1)*(u+2*t+2) - (n+t+1)*(k-t) = t*(5*u+5*t+7) := by
  rw [h] at *
  linear_combination he

private def D (S r : ℕ) := r.choose (S-r)

private theorem order_step {n k r : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (he : (n+1).choose (k-1) = n.choose k) (hleft : n+k ≤ 2*r) (hr : r < n+k) :
    (r < n → D (n+k) r < D (n+k) (r+1)) ∧
    (n < r → D (n+k) (r+1) < D (n+k) r) := by
  let c := n+k-r
  have hc : 0 < c := by dsimp [c]; omega
  have hcr : c ≤ r := by dsimp [c]; omega
  have hstep := step hc hcr
  have hpos := Nat.choose_pos hcr
  have hb := balance hk hkn he
  have hbase : (((n-k:ℕ):ℤ)+1)*(((n-k:ℕ):ℤ)+2) = ((n:ℤ)+1)*k := by exact_mod_cast hb
  have herr := signed_error (t := (r:ℤ)-n) (by omega : (n:ℤ)=k+(n-k:ℕ)) hbase
  have h₁ : ((r-c:ℕ):ℤ) = (n-k:ℕ)+2*((r:ℤ)-n) := by dsimp [c]; omega
  have h₂ : (c:ℤ) = k-((r:ℤ)-n) := by dsimp [c]; omega
  rw [← h₁, ← h₂, show (n:ℤ)+(r-n)=r by ring] at herr
  have hsign : (0:ℤ)<5*(n-k:ℕ)+5*((r:ℤ)-n)+7 := by omega
  have hnext : n+k-(r+1) = c-1 := by dsimp [c]; omega
  simp only [D,hnext]
  change (r<n → r.choose c < (r+1).choose (c-1)) ∧
    (n<r → (r+1).choose (c-1) < r.choose c)
  constructor
  · intro h
    have hneg := mul_neg_of_neg_of_pos (by omega : (r:ℤ)-n<0) hsign
    have hdiff : (r-c+1)*(r-c+2) < (r+1)*c := by
      exact_mod_cast (show (((r-c:ℕ):ℤ)+1)*(((r-c:ℕ):ℤ)+2) < ((r:ℤ)+1)*c by omega)
    have hmul := Nat.mul_lt_mul_of_pos_left hdiff hpos
    rw [← hstep] at hmul
    exact Nat.lt_of_mul_lt_mul_right hmul
  · intro h
    have hplus := mul_pos (by omega : 0<(r:ℤ)-n) hsign
    have hdiff : (r+1)*c < (r-c+1)*(r-c+2) := by
      exact_mod_cast (show ((r:ℤ)+1)*c < (((r-c:ℕ):ℤ)+1)*(((r-c:ℕ):ℤ)+2) by omega)
    have hmul := Nat.mul_lt_mul_of_pos_left hdiff hpos
    rw [← hstep] at hmul
    exact Nat.lt_of_mul_lt_mul_right hmul

/-- On a diagonal with a Lind tie, only the two tied rows can attain its value. -/
theorem unique_on_diagonal {n k r c : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (he : (n+1).choose (k-1) = n.choose k) (hrc : r+c=n+k) (hc : c ≤ r)
    (hval : r.choose c = n.choose k) : r=n ∨ r=n+1 := by
  have hnval : D (n+k) n = n.choose k := by simp [D]
  have hsval : D (n+k) (n+1) = n.choose k := by
    simpa only [D,show n+k-(n+1)=k-1 by omega] using he
  have hrval : D (n+k) r = n.choose k := by simpa [D,show n+k-r=c by omega] using hval
  by_contra! hbad
  rcases lt_or_gt_of_ne hbad.1 with hsmall | hlarge
  · have rise : ∀ j, r<j → j≤n → D (n+k) r < D (n+k) j := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base =>
        intro h
        exact (order_step hk hkn he (by omega) (by omega)).1 (by omega)
      | succ j hj ih =>
        intro h
        exact (ih (by omega)).trans ((order_step hk hkn he (by omega) (by omega)).1 (by omega))
    have := rise n hsmall le_rfl
    omega
  · have fall : ∀ j, n+1<j → j≤r → D (n+k) j < D (n+k) (n+1) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base =>
        intro h
        exact (order_step hk hkn he (by omega) (by omega)).2 (by omega)
      | succ j hj ih =>
        intro h
        exact ((order_step hk hkn he (by omega) (by omega)).2 (by omega)).trans (ih (by omega))
    have := fall r (by omega) le_rfl
    omega

private theorem row_growth (m H j : ℕ) :
    (m+H).choose (j+1) ≤ m.choose (j+1) + H*(m+H).choose j := by
  induction H with
  | zero => simp
  | succ H ih =>
    have hmono := Nat.choose_le_succ (m+H) j
    rw [Nat.add_succ, Nat.choose_succ_succ, Nat.succ_mul]
    have hmul := Nat.mul_le_mul_left H hmono
    simp only [Nat.succ_eq_add_one] at *
    omega

private theorem half_mono {n a b : ℕ} (h : a ≤ b) (hb : 2*b ≤ n) :
    n.choose a ≤ n.choose b := by
  induction b,h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Two proper occurrences with a row gap H force their earlier column to be
at least (m+H+1)/(H+2). -/
theorem earlier_column_bound {m H k l : ℕ} (hl : 1 ≤ l) (hlk : l < k)
    (hk : 2*k ≤ m) (he : m.choose k = (m+H).choose l) :
    m+H+1 ≤ (H+2)*k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (show 2 ≤ k by omega)
  let B := (m+H).choose (j+1)
  let L := m-(j+1)
  have hB : 0<B := Nat.choose_pos (by omega)
  have hentry : m.choose (2+j) ≤ B := he.le.trans (half_mono (by omega) (by omega))
  have hx := Nat.choose_succ_right_eq m (j+1)
  rw [show j+1+1=2+j by omega] at hx
  have hy := Nat.choose_succ_right_eq (m+H) j
  have hL : L ≤ m+H-j := by dsimp [L]; omega
  have hlow : m.choose (j+1)*L ≤ B*(2+j) := hx.symm.le.trans (Nat.mul_le_mul_right _ hentry)
  have hupp : (m+H).choose j*L ≤ B*(j+1) :=
    (Nat.mul_le_mul_left _ hL).trans hy.symm.le
  have hmul : B*L ≤ B*((2+j)+H*(j+1)) := calc
    _ ≤ (m.choose (j+1)+H*(m+H).choose j)*L := Nat.mul_le_mul_right _ (row_growth m H j)
    _ = m.choose (j+1)*L + H*((m+H).choose j*L) := by ring
    _ ≤ B*(2+j)+H*(B*(j+1)) := Nat.add_le_add hlow (Nat.mul_le_mul_left _ hupp)
    _ = _ := by ring
  have h := Nat.le_of_mul_le_mul_left hmul hB
  dsimp [L] at h
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one] at h ⊢
  omega

end Erdos849LindDiagonal
