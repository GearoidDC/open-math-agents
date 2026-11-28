import E889PrimeTwentyThreeCore
/-! Exponent residues when 23 divides the term at offset 16. -/

namespace Erdos889.PrimeTwentyThree

namespace D16
private def cfg : Config := ⟨16,2,23,1,4,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x88040⟩
private def rows12 : List Rule := [
  .div 7,
  .div 3,
  .div 5,
  .div 13,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x65105105120a2ca20a44144145928e2882880510516512ca20a20a44145944128828828c05165105120a20a2ca45944144128828d288⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨2,6,0x14b00a18⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,8,[31,2],[3,5,7],41,0x1b382b50736⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],225,0x108815020b088440ac10580622014182c031900a04560108a05822b⟩,
  .pool ⟨61,4,[61,2],[3],31,0x68818116⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],549,0x1a60a00261041120a0084490094824032014120184820800120982106094002924004c800925000a41821064120004104860120a01300904a4024884014122082190014196⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],45,0x55898f135e⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0x765930000000000000000000000000483210000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨8,7,0x14340029a00505800a2c0192a0051500643001418⟩
private def rows120 : List Rule := [
  ]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0xfac688⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 2 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨0,8,0x0⟩
private def rows240 : List Rule := [
  .pool ⟨241,17,[241,17],[2,3,5,7,11,13],1525,0x1000100000000120440008810000000004000000000000000000000001001000000800001000000000000800080001000800000000000000008080008000010000000000000000010000400080002210000000000008000080000000000000000000000000000040000400000000000211000040008000200000000000000000200000400040400000000000000004002000040004000000000002000004000002002000000000000000000000000800000000204400088120000000020002⟩,
  .div 17,
  .pool ⟨241,31,[241,19,23,29,31],[2,3,5,7,11,13,17],819,0xa00000000000000800240000200200005020841200a48200000208028000804008100020000344000300000000008200004000020100000020024000000000800200020004000020008848044000808100000004000240200100001840100008000a0c80002⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,2,0x9955665555115544⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 8 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+16=2^a*23^b) (ha : 0<a) (hb : 0<b) : a%12=4 ∧ b%12=0 := by
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
end D16
end Erdos889.PrimeTwentyThree
