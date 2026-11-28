import E889PrimeTwentyThreeCore
/-! Exponent residues when 23 divides the term at offset 3. -/

namespace Erdos889.PrimeTwentyThree

namespace D3
private def cfg : Config := ⟨3,3,23,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x67⟩
private def rows12 : List Rule := [
  .div 5,
  .div 7,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0xc00400402002002000030010010080080080401000402002002000010030010080080080400400c0200200200001001002008008008⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨1,6,0xd9f⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,10,[31,2,5],[3,7],48,0x1109b2514db6⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],16,0x8002⟩,
  .pool ⟨61,6,[61,2,3],[5],112,0x1131950bd9b33a5571d14f9db77e⟩,
  .pool ⟨61,2,[61,2],[],31,0x68818116⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x163440000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨0,7,0x0⟩
private def rows120 : List Rule := [
  .pool ⟨41,25,[41,5,17,19,23],[2,3,7,11,13],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  .pool ⟨31,22,[31,2,11,17,19],[3,5,7,13],41,0x1fffffffffe⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,1,0xc⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 1 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+3=3^a*23^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  obtain ⟨i,hi,_⟩ := h120
  exact Nat.not_lt_zero i hi
end D3
end Erdos889.PrimeTwentyThree
