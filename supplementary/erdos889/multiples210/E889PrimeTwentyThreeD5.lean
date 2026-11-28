import E889PrimeTwentyThreeCore
/-! Exponent residues when 23 divides the term at offset 5. -/

namespace Erdos889.PrimeTwentyThree

namespace D5
private def cfg : Config := ⟨5,5,23,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x61⟩
private def rows12 : List Rule := [
  .div 3,
  .div 7,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x430410c12082082080c10430412082082080410c10432082082080430410c12082082080c1043041208208208041101042208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨3,6,0xa8101e040181⟩
private def rows60 : List Rule := [
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],820,0x131509111051112b11101131011116d53121111803118719101191811114d13187199411190111d8109503115ab5316311989391c113501111011b9051010d115015b14959101311817192111121715011304931923511031154771125119417b90959d07335e⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],123,0x10000124014004012182110536⟩,
  .div 11]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x2492492492492491b03⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨10,7,0x667a0153d0198080540405a7a00f3d0109e800cf40420200301⟩
private def rows120 : List Rule := [
  .pool ⟨61,10,[61,2,5],[3,7],1312,0x1000300200005000104100000021320010021001001000000020000040305040200010000050100010102001100000001010020040020001001100005001100112004020000012001200000110221002201010003012400010101000000000203200100310100040001100200041002010102000101000001001100120101000001010410201000240100000001010401000124000210001121012004050102310536⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,4,0xa98765004321⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 3 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨0,8,0x0⟩
private def rows240 : List Rule := [
  .div 17]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 10, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 10 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+5=5^a*23^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
  obtain ⟨i,hi,_⟩ := h240
  exact Nat.not_lt_zero i hi
end D5
end Erdos889.PrimeTwentyThree
