import E889PrimeTwentyThreeCore
/-! Exponent residues when 41 divides the term at offset 3. -/

namespace Erdos889.PrimeTwentyThree

namespace D103
private def cfg : Config := ⟨3,3,41,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨0,4,0x0⟩
private def rows12 : List Rule := [
  .div 5,
  .target,
  .div 7,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,2,0xaaaaaa000000000000000000aaaaaa000000000000000000bbbbb9000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+3=3^a*41^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  obtain ⟨i,hi,_⟩ := h12
  exact Nat.not_lt_zero i hi
end D103
end Erdos889.PrimeTwentyThree
