import E889PrimeTwentyThreeCore
/-! Exponent residues when 23 divides the term at offset 9. -/

namespace Erdos889.PrimeTwentyThree

namespace D9
private def cfg : Config := ⟨9,3,23,1,2,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x68⟩
private def rows12 : List Rule := [
  .div 5,
  .div 7,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x200200200002001001008008008040100040200200200001002001008008008040040080200200200001001003008008008080040040⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨1,6,0x1a0⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],560,0xf5b1c723d8153c0d59d0a119ad5210d31141519254912b714e5331243910738d831b1ab1b183639c1138491994e51da91254931505119610956b310a17356079503789c71b5e⟩,
  .pool ⟨61,6,[61,2,3],[5],112,0x1131950bd9b33a5571d14f9db77e⟩,
  .pool ⟨31,4,[31,2],[3],112,0xd111410311034005811181051116⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x11a340000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨2,7,0x424000320⟩
private def rows120 : List Rule := [
  .pool ⟨41,27,[41,3,17,19,23],[2,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,2,0x9⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 1 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨2,8,0x698007e20⟩
private def rows240 : List Rule := [
  .div 17]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,2,0x24⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 2 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .div 19,
  .pool ⟨37,25,[37,5,23],[2,3,7,11,13,17,19],41,0x1b382b50736⟩,
  .pool ⟨31,30,[31,2,3,5,23,29],[7,11,13,17,19],592,0x1315b911757339b317191db79dd1d517b11d0bdbb17bfd3dd971db9b7b319337d7bb91fb3a5751fd5531377df7531d59f3d9959153f5594f9ff53fb9799d359fdb3f75d77393ffd5bf7e⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,2,0x804088090⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 2 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+9=3^a*23^b) (ha : 0<a) (hb : 0<b) : a%12=2 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  have h60 := run60 h bad h12
  have h120 := run120 h bad h60
  have h240 := run240 h bad h120
  have h720 := run720 h bad h240
  obtain ⟨i,hi,_⟩ := h720
  exact Nat.not_lt_zero i hi
end D9
end Erdos889.PrimeTwentyThree
