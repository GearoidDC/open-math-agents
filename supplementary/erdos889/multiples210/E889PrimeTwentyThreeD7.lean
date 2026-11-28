import E889PrimeTwentyThreeCore
/-! Exponent residues when 23 divides the term at offset 7. -/

namespace Erdos889.PrimeTwentyThree

namespace D7
private def cfg : Config := ⟨7,7,23,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨2,4,0x89045⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x2c82c82c820820820820d20b20b2082082082c82c82c820820820820b20c20b2082082082c82c82c820820820820b20b20a208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨7,6,0xe1502c540515028a40729010a40129⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨61,17,[61,17],[2,3,5,7,11,13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩,
  .pool ⟨61,15,[61,3,5],[2,7,11,13],100,0x28a0828a002aa082aa082aa⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0xa9382000000000017654000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 2 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨7,7,0xd05402c2a02851019148050a4040ca00265⟩
private def rows120 : List Rule := [
  .pool ⟨41,18,[41,2,3,17],[5,7,11,13],620,0x13350d199053114b711213b5a33192451d2b131cb11d6f39d6959501799e9039a97b9477398d3958d53123511c552dc1591ed399c3191031bd4973d471b8a75b565115e77b10b7b5af51d8f335e⟩,
  .pool ⟨31,2,[31,2],[],328,0xd101020301040085014100101000401300011001010011000190040010100105014200410180810116⟩,
  .pool ⟨31,2,[31,2],[],64,0x5101000180010117⟩,
  .pool ⟨31,2,[31,2],[],1025,0x1a20200070000000a800000000000002220000000000000000000000000000202020000000000000000000000000000000000000000000000000000000003000300030000000000000000000000000000000000000000000000000000000001010100000000000000000000000000001110000000000000054000000380010116⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨41,36,[41,2,3,17,19,23,29],[5,7,11,13,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,14,[41,2,7],[3,5,11,13],31,0x121d47b6⟩,
  .pool ⟨31,3,[31,3],[2],576,0x800020000800020000800020000800020000808020000a00020000800020000800020000800020000800028000800220000800020000800020000820020000800020008800020a⟩,
  .pool ⟨31,6,[31,2,3],[5],369,0x100844020590854130148e0c4615d890482c10089612e10280d0e5188a9f120901924032d01d0452131cb15977e⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,4,0x888800fed77666cb55443221a900⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 7, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 7 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨2,8,0xa48d002c15⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨41,37,[41,19,23,29,37],[2,3,5,7,11,13,17,31],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨31,18,[31,2,3],[5,7,11,13,17],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,3,[31,3],[2],1525,0x141000866080000008181a0321481a000000c04080c1008600802004800284c21001225020004100848004860008000000000000000900408109001812000d02005001048c021294000408c800302100000011880008b0182308801019400a001400a60200443106034400046200000021030004c408000a52100c48200280102c00120600242040802400000000000000040018480048402080010291200210c8500048010040184020c04080c000001604a130160604000000419840020a⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,3,0xa04603000402000048⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 7, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 7 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .div 19]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 2 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+7=7^a*23^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D7
end Erdos889.PrimeTwentyThree
