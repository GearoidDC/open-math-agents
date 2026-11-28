import E889PrimeTwentyThreeCore
/-! Exponent residues when 23 divides the term at offset 17. -/

namespace Erdos889.PrimeTwentyThree

namespace D17
private def cfg : Config := ⟨17,17,23,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨5,4,0xab089067045023⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .div 7,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x80102010201102010201020010701020102201020102010020106010201102010201020010201050102201020102010020102010401102010201020010201020103201020102010⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨9,6,0x88b0385405150367c079f0127c0129032cc06b3⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,2,[31,2],[],32,0xd1010117⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],99,0x7ac8e0d5bc44f223dab07135e⟩,
  .pool ⟨61,9,[61,3],[2,5,7],36,0xa00220a⟩,
  .pool ⟨31,27,[31,3,17,19,23],[2,5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨31,6,[31,2,3],[5],36,0x19f3d73df⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],248,0x802a200200822a0a882008008a8020a2a808a88aa2880a0228aa22a202a8a⟩,
  .pool ⟨31,4,[31,2],[3],63,0x6880800180010116⟩,
  .pool ⟨31,5,[31,5],[2,3],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],160,0x5105011110050105110083114303401191814196⟩,
  .pool ⟨31,2,[31,2],[],63,0x6880800180010116⟩,
  .pool ⟨31,4,[31,2],[3],32,0xd1010117⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,5,0x5251660000000000000000001312a43000000000000000000114c1e8000000000000000000073148e0000000000000000000d1b0410000000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 5, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 5 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨10,7,0x5e8e01147014288029440502a00a150168f803c7c0405200229⟩
private def rows120 : List Rule := [
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,2,[41,2],[],31,0x121d47b6⟩,
  .pool ⟨41,4,[41,2],[3],31,0x121d47b6⟩,
  .pool ⟨61,7,[61,7],[2,3,5],164,0x8820a0220282088002aa88a282a02a0a288aaa⟩,
  .pool ⟨41,6,[41,2,3],[5],288,0x2050811004b03030101115702050815020b03010901111f02070111004303110905135f⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],123,0x25841b08a0002932122d968a6034c12⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],656,0x80a020022200080028a08a00220880820000200000a020800000a0022020000000020200022a802008200802a8800080800000000808800a000002080a00000800008202208800a20a280020008880080a02⟩,
  .pool ⟨61,41,[61,17,19,23,29,37],[2,3,5,7,11,13,31,41],492,0x8200a28808008a28a08220800820028028820a20808200000220220000a08020a00008808800000820208a08228028008200208820a28a20020228a0082⟩,
  .pool ⟨41,5,[41,5],[2,3],25,0x210863⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,5,0x9c929001088c1ee39cc6295ac210631096a0842100000⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 9, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 9 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨4,8,0xc8c900505100c88d005015⟩
private def rows240 : List Rule := [
  .pool ⟨31,22,[31,2,11,19],[3,5,7,13,17],656,0xd5b1755337155d557db59b117359d1931551751141f531d11555f1537175511511131315177b917518315d13bdd15191911151155d1d951f555117195f05115d15519317359d11b35b7d557551d9955d1b56⟩,
  .pool ⟨41,28,[41,2,7,19,23],[3,5,11,13,17],160,0x2511892bc26105cd7b863501893bd27115cd6b96⟩,
  .pool ⟨61,40,[61,2,5,19,23,29,37],[3,7,11,13,17,31],1088,0x243b0d6500d31e9188a9532dabf7c903e2616e493105865bc4cdfd1778eba28d56a6342b1c7510c30f8188b9423dbbe7d813f2717f592115974bd4cdec0768fbb39d46b6253b0c6501d31f9189a9522daaf7c803e2616f493005875bc5cdfc1779eba38d57a6352b1d7511c30e8189b9433dbae7d913f2717e592015964bd5cded0769fbb29d47b6⟩,
  .pool ⟨41,34,[41,2,17,19,23,29],[3,5,7,11,13,31],241,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨31,25,[31,5,19,23],[2,3,7,11,13,17],964,0x200a8820880200a0a8a22aa808a80a2082822a8a080802aa0800280202222220200a00082aa0080828aa20a082280a880aaa228a828020088208a80222a808a288aa2a8280822000a880a8228a0a200828a8aa0028aaa0aa2a220222a2a82aa8a002a8a8a08022828a20a808a80022080a0aa2a88a2880aa2⟩,
  .pool ⟨241,34,[241,2,17,19,23,29],[3,5,7,11,13,31],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨41,29,[41,19,23,29],[2,3,5,7,11,13,17],248,0x808a2a88a880aa28200a880080208a82a208020022a00828aa022a22a8a202⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,4,0x66666666a5594224844723321111111100000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 10, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 10 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],296,0x200a800202228a2020808a288808002a0080a8aa02aa82888208a8a2a20822282aa80aa2a⟩,
  .div 19,
  .pool ⟨31,25,[31,5,23],[2,3,7,11,13,17,19],328,0x88000a8200200088000880200080a20a200000200008000008a08a0200080220002200080082a00022⟩,
  .pool ⟨37,9,[37,3],[2,5,7],27,0x8060b⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,2,0x53545415d951505654⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 4 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+17=17^a*23^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D17
end Erdos889.PrimeTwentyThree
