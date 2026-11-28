import E889PrimeTwentyThreeCore
/-! Exponent residues when 23 divides the term at offset 13. -/

namespace Erdos889.PrimeTwentyThree

namespace D13
private def cfg : Config := ⟨13,13,23,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨5,4,0x6b009067005063⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .target,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x131018101310101010101010101310131017101010101010131016101310101010101010101310131015101010101010131014101310101010101010101310131012101010101010⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨6,6,0x122c0d9f01e7c049f030a40029⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],16,0x8002⟩,
  .pool ⟨61,10,[61,2,5],[3,7],112,0x131050301332215211107152736⟩,
  .pool ⟨61,14,[61,2,7],[3,5,11,13],176,0xf79d59f91341d57b31379ab3d919bd5705913f3573de⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],16,0xd397⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],72,0x88a2200aaa208aaa⟩,
  .pool ⟨31,7,[31,7],[2,3,5],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .prime 31,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,2,[31,2],[],16,0xd117⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],208,0x1131371995950bf9799b7393ba5575731dd1d14fbd3ddb37d7fe⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],488,0x15139115d75315515155119713d11313935195911751d1d593d5d5111397071557d79191559151d317d595d3555357d15715d793d3d397531197d55796⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .pool ⟨61,16,[61,2],[3,5,7,11,13],31,0x68818116⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],336,0x109004901221869a0832504814094436582cb0d261109104901320869b0932514914084536582db0d36⟩,
  .pool ⟨31,10,[31,2,5],[3,7],48,0x1109b2514db6⟩,
  .pool ⟨31,7,[31,7],[2,3,5],80,0x82000202000080800082⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,5,0x78c2ef0000000000000000000e6958b00000000000000000016556890000000000000000001341cd20000000000000000000520c410000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 5, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 5 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨4,7,0x13a380251c03c5200029⟩
private def rows120 : List Rule := [
  .pool ⟨31,10,[31,2,5],[3,7],800,0x8110004001012000015000000980010517000210011100000181000041400020018011011708000005110002010101000140800001c001013700401001100800010500000340000101800181170840000130000011010108014004010182110537⟩,
  .pool ⟨41,6,[41,2,3],[5],244,0xf5915131119115111111d113111193b93111191171111115113111915135e⟩,
  .pool ⟨41,20,[41,2,5,17,19],[3,7,11,13],800,0x30d0bdb2b47594f8f6f131d1bcb3b5f495f9f7f030f0bdb2b47594f8f6f135d1bcb3b57495f9f7f0b0d0bdf2b475b4f8f6f131d1bcb3b57495f9f7f030d1bdb2b4f594f8f6f131f1bcb3b57495f9f7f034d0bdb2b47595f8f6f1b1d1bcf3b574b5f9f7f⟩,
  .pool ⟨41,35,[41,5,7,17,19,23,29],[2,3,11,13,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,32,[41,2,17,19,23,29],[3,5,7,11,13,31],1056,0x84910432100180d248128a20369a0592490c00126404484820d16cb64229b4186194900522100090c349028b21368b0482580d10136504594930c06cb65328b4096094910432000190d248128a20269a0592590c10126404584830d16cb65229a4186194800532100090d349128b21369b0492580d10036504594930d06ca65328b4196⟩,
  .pool ⟨41,7,[41,7],[2,3,5],48,0x820000000082⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,27,[41,3,17,19,23],[2,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,4,0xcb44887766554433221100a9⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 6, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 6 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨0,8,0x0⟩
private def rows240 : List Rule := [
  .pool ⟨31,10,[31,2,5],[3,7],1575,0x40000020101100000008000205020200040000001140800004000800360008101801101160040100001000020220008000004040204040009000000a2800000080030002c10102030002026c100020000200004044020004000008040809005000800045000000300020005800200060044145821004000000008808804000000001009101000a40000008a0020002010c000b0004000c000829b0420000000800010510080000000120102020014800000134000010400180016004810182110536⟩,
  .div 17]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0xfffa⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 4 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+13=13^a*23^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D13
end Erdos889.PrimeTwentyThree
