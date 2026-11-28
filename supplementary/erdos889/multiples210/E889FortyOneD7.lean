import E889PrimeTwentyThreeCore
/-! Exponent residues when 41 divides the term at the indicated offset. -/
namespace Erdos889.PrimeTwentyThree

namespace FortyOneD7
private def cfg : Config := ⟨7,7,41,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x89045⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x2082082082082082082cd2cb2cb2082082082082082082082082082cb2cc2cb2082082082082082082082082082cb2cb2ca208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨5,6,0x821014540d35028a4071d⟩
private def rows60 : List Rule := [
  .pool ⟨31,10,[31,2,5],[3,7],75,0x116026c145829b0536⟩,
  .div 11,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],100,0x28a0828a002aa082aa082aa⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0x21111101111181111171111136111115111114111112111110⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨8,7,0x14288029440502a00a1501c388069c40706a01a35⟩
private def rows120 : List Rule := [
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],1464,0x8a20a08228028220008a08828000028808000a28228208a00800808220a28820220828a08a20000820800a08008808a08028820828820008000820220800020208828828008200200028a08800a28a00808008a00200a00208020000008020800a00800a20020200a28a00220a28000800820028228220808000208808200020008228208228020a20220020a00208200008a20a28208808228a08820200200a20828828a00020228000028220a20008828028820a08a2⟩,
  .pool ⟨61,38,[61,2,17,19,23,29,37],[3,5,7,11,13,31],984,0xd305b2994d14db69b0d32190596516d16d925b25849341101361361101b4d121b4514994994514196030db0d329129109305349925b69b2112136db05929341b6d909109b2db49325941921129129961b6180d305145325325145b09165b0110d90d901105924349b4936d16d14d341309961b2db65165329b4196⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],820,0xf79dc9735253bd2f3114913dc5511ed535a9319a43918759d091918931d4f139871bd651bd0151de1095433b5ab531635998f3b9e33358d195ab5b9855210f715017b14d7b1c3391e57192313121735c31384b3192b5956f1154779125119e97b94959d2773de⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,4,0x2222a987654311110000⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 5, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 5 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨4,8,0xc8c900505100148d008c15⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨61,36,[61,2,3,19,23,29],[5,7,11,13,17,31],527,0x5270c2a01f40d890106ba6140b6d49755434129de8d384660109e29b771877a3333201e31124986e7f991e34a84617d3c55065492bd59829f6f2e47d07b2bcd1b5e⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,3,0xa040000000d0201000000048⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 8 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .div 19]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 4 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+7=7^a*41^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end FortyOneD7
end Erdos889.PrimeTwentyThree
