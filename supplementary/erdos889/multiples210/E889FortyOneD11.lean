import E889PrimeTwentyThreeCore
/-! Exponent residues when 41 divides the term at the indicated offset. -/
namespace Erdos889.PrimeTwentyThree

namespace FortyOneD11
private def cfg : Config := ⟨11,11,41,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x67⟩
private def rows12 : List Rule := [
  .div 3,
  .div 7,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x410410412082082080410410412082082080c31030c32082082080410410412082082080410410412082082080c30c30c2208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨10,6,0x36dc0ab7006dc04ab006ac0d9f0364c04930064c0487⟩
private def rows60 : List Rule := [
  .pool ⟨31,16,[31,2],[3,5,7,11,13],48,0x190014116⟩,
  .pool ⟨61,22,[61,2,11,17,19],[3,5,7,13],336,0xd129b4c94592584910134194116030d301221b2d129169b0890196180d105305901124349345265b2916⟩,
  .pool ⟨61,19,[61,17,19],[2,3,5,7,11,13],744,0x200020820a00820008800200228a20028208008020200000808020020828008a28800800220008200a08208000808828a08008028208a20228828800008a00820a00a08828a28220a00a08200a20000228228808a20828020020a2822⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],336,0x109004901221869a0832504814094436582cb0d261109104901320869b0932514914084536582db0d36⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,4,0xed04c041ba921038047632150⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨24,7,0x10b9800dcc0426e00337010b3800d9c042560032b01cad806d6c0723e01b1f01ca7806d3c0722601b13013a780253c04e2600913013a180250c04e0e00907⟩
private def rows120 : List Rule := [
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨61,19,[61,17,19],[2,3,5,7,11,13],492,0x8200a28808008a28a08220800820028028820a20808200000220220000a08020a00008808800000820208a08228028008200208820a28a20020228a0082⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,5,0x8421ce2f600000ad2728c1ee6b16a4a0e60000029062⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 10, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 10 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨20,8,0xbadf0042670006a3007e2b0036d300ae5b00729700ea1f0072c700ea4f00ae8b0036130012c7008a4f004e8b00c613004ebb00c643008a7f001207⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨31,21,[31,3,7,19],[2,5,11,13,17],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,5,0x80010800100000a8014000000000004e40000000460003dc0000000358000000000005800a000000250001cc00000001480000000000018002⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 24, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 24 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨4,10,0x1e664c001f82b0022e2ec0031a23⟩
private def rows720 : List Rule := [
  .pool ⟨73,44,[73,2,11,23,29,43],[3,5,7,13,17,19,31,37,41],1040,0x305891140c32903310a7185044980252d2909ceb709613b02b031c36b8885b1a5710cc1014972d46715a34914018d470386c588af21d207b56f434863b9cd0b4e1315890150d32903211a6195045990353d2919cea719612b12a021c37b9895a1a5611cd1114962c47705a35904019d471396d598af31c217a56f435873a9cd1b5e⟩,
  .div 19,
  .pool ⟨181,31,[181,23,29,31],[2,3,5,7,11,13,17,19],876,0x8a00828a28208808020008008a08a28800228220a08208800a20828020800a20208200808008a20000200228228028220208000020a00000a08000020808828028828800800008a20020200820808a00208028208a00220820a08828800228a20a20020008020220828a28200a2⟩,
  .pool ⟨73,6,[73,2,3],[5],16,0x1b5f⟩,
  .pool ⟨73,39,[73,3,13,23,29],[2,5,7,11,17,19,31,37],328,0xa0a822aaa200888028a08a082a888a820002280a00a028800082a222a820a20a280222008aaa882a0a⟩,
  .pool ⟨73,16,[73,2],[3,5,7,11,13],48,0x102010116⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],720,0x800220000000020800800020000800008000808220000a00028000008220000a00020000800000000800020000808020008220020200808020008a20000a00800020000800020800000020008820028200800200008820028a⟩,
  .pool ⟨31,21,[31,3,7],[2,5,11,13,17,19],584,0x208200882022280a0a2800202aa202a0220880a808aa8080028a0a02888082200820800aa8a28aa228a8882a02082aa8a8008a80a88a22a02a2002a2aa82080a8222a288aa28a2aa⟩,
  .pool ⟨61,39,[61,3,13,23,29],[2,5,7,11,17,19,31,37],779,0x23b064abd48b333108820e34b5f1c0a9aa6f2e76e607e0cd219800ad06fb602d2306d300a34715d34206f99002aa1e14a3ac785a8bff6209eb534561d3a5f349b3b4b39208f4afdc67b0cf81788908b098a62f87052538baeef71332c942ad1f23a⟩,
  .pool ⟨61,39,[61,3,13,23,29],[2,5,7,11,17,19,31,37],73,0x1fffffffffffffffffe⟩,
  .pool ⟨61,48,[61,2,3,23,29,43,47],[5,7,11,13,17,19,31,37,41],160,0x29a443ce1138a552de0129a543ce1139a553de⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,4,0xa11a11a111a11a11a1411e1151111511411d116116117171161161611711711117116117811811811118118118181181191119118118117117116161171171611611711117116116511411c1111b115114121101131113112110⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 20, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 20 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
private def keys5040 : Keys := ⟨0,13,0x0⟩
private def rows5040 : List Rule := [
  .pool ⟨43,10,[43,2,5],[3,7],48,0xd94132990536⟩,
  .pool ⟨43,33,[43,3,11,23],[2,5,7,13,17,19,29,31],639,0x587af1725cfdd6f3ccdb403819cf44f24b4cdd75aafee83ebf394ad1deaf10aece27df42c848e4dc3b27121342fbe4737508f57b8b529cfd7c177f55aebb32d24f22f3981c02db33cf6bbf3a4e8f5e1a⟩,
  .pool ⟨61,49,[61,7,23,47],[2,3,5,11,13,17,19,29,31,37,41,43],339,0x20b21020a4da25a2124d100321800220b4830d00882ca6d061a40b2996c321b65049328128048b2d320b2⟩,
  .pool ⟨43,38,[43,2,19,23],[3,5,7,11,13,17,29,31,37],48,0xd94132990536⟩,
  .pool ⟨43,19,[43,19],[2,3,5,7,11,13,17],181,0x10401408204430019030203301030260030881040a0082⟩,
  .pool ⟨43,7,[43,7],[2,3,5],25,0x1040082⟩,
  .pool ⟨43,13,[43,13],[2,3,5,7,11],80,0x80880000082000002202⟩,
  .pool ⟨29,23,[29,23],[2,3,5,7,11,13,17,19],284,0x8aa0028a2a0aa2a220888080280820aa8020802aa082028020222088a8aa0a8a2800aa2⟩,
  .pool ⟨29,23,[29,23],[2,3,5,7,11,13,17,19],211,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨29,23,[29,23],[2,3,5,7,11,13,17,19],328,0xa0a822aaa200888028a08a082a888a820002280a00a028800082a222a820a20a280222008aaa882a0a⟩,
  .pool ⟨29,19,[29,19],[2,3,5,7,11,13,17],181,0x11e0049dc628b42426480880440499090b4518ee4801e2⟩,
  .pool ⟨29,19,[29,19],[2,3,5,7,11,13,17],43,0x7fffffffffe⟩,
  .pool ⟨29,19,[29,19],[2,3,5,7,11,13,17],71,0x1164729716b1d977e⟩,
  .pool ⟨29,26,[29,2,13,23],[3,5,7,11,17,19],176,0x3f5591315b891db3b9f7527b11d1751fcd59f7bdb316⟩,
  .pool ⟨29,21,[29,3,7],[2,5,11,13,17,19],196,0xa28028aa08028aa28020aa08020aa08028aa28020aa28028a⟩,
  .pool ⟨29,21,[29,3,7],[2,5,11,13,17,19],923,0x26837b80942437ee2cc8b2caa045430787184b7365b60d3222af5b998e90aec47295a8308f208030838d5092af00b1b6e4b32740485179182e1370be36151ecfd1332989072ef0236f14e1ef2fef30ea3e856a1dc0af28e46040ab3b30f9059212d271a1f1d5cfaa4b2ac498803db56fa211e9a⟩,
  .pool ⟨29,21,[29,3,7],[2,5,11,13,17,19],904,0xaa8228aa28a880a22020820a88a200aa8a02a02000a2a8a808a802888882a808a808020aaa2a02a0800a820880a28a2a220a88082008228000028820082022a088a8a28a022082a0020a80a8aaa080202a202a822222802a202a2a8a00080a80a2aa008a22a08208088a022a28aa2882aa⟩,
  .pool ⟨29,21,[29,3,7],[2,5,11,13,17,19],441,0x110a040a5110c2c022140c1ca2018580462c102944030b02885020528887160110b040e5900c2c022140c14a20185814628102964038b⟩,
  .pool ⟨29,8,[29,2],[3,5,7],71,0x1164729716b1d977e⟩,
  .pool ⟨29,8,[29,2],[3,5,7],129,0x1b29221960201a08b44160101a6112536⟩,
  .pool ⟨29,8,[29,2],[3,5,7],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨29,9,[29,3],[2,5,7],181,0x20602001300926224004000870a4248013cc42a01e22a⟩,
  .pool ⟨29,9,[29,3],[2,5,7],71,0x1164729716b1d977e⟩,
  .pool ⟨71,23,[71,23],[2,3,5,7,11,13,17,19],16,0x82⟩,
  .pool ⟨43,19,[43,19],[2,3,5,7,11,13,17],71,0x1164729716b1d977e⟩,
  .pool ⟨43,33,[43,3,11,23],[2,5,7,13,17,19,29,31],1448,0x80aa0082a882280000222a088a2aa282a0200a02a2020200820a20208280880aaa080022222802a882a208a2a0a8a208a822a802888880020aaa02202820808a0820080808a80a0080a828aa8a220a888000028822a8200aa020a2a00aa28022882aaaa8880a2208008280a8aa0a808a828aa28a08a8a282a22a000a2aa888882a8022808a2080a0208a2028802a822222aa8a000a88a828a2a20a28aa282a202a0aa2a0282002088a0222aaaa82288028aa00a8a⟩,
  .pool ⟨29,23,[29,23],[2,3,5,7,11,13,17,19],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  .pool ⟨29,23,[29,23],[2,3,5,7,11,13,17,19],71,0x7ffffffffffffffffe⟩,
  .pool ⟨29,21,[29,3,7],[2,5,11,13,17,19],488,0x82a8000a22a2020200800a222882a0a822888a0020080808a88a0002a820a2802aaa08808a828aa2aa08882280a02882220aa8aa282a20220aaa8028a⟩,
  .pool ⟨29,8,[29,2],[3,5,7],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩]
private def step5040 : Stage := ⟨cfg,720,7,keys720,keys5040,rows5040,5,0x6b5ad6b5aa6298b5335adeb5ad1703be406b56d6ad6dd94a73949d1e71ce8d6b6b56d69ca5d94a6e745d1e71ad6b5ad6ad4c5314cd6b5ad6f59018b81dd8a5a94a61d2839d291882031495ad6b6b5a739ca52a41ee745d16b5ad6b5b6b5ab5ad652a4e73945d183dce6b5ad6b5aa5318a5a8e949d28398a418820⟩
set_option maxHeartbeats 5000000 in
private theorem valid5040 : ∀ r ∈ rows5040, Valid cfg 5040 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test5040_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 7, Test step5040 i x y z := by decide +kernel
private theorem run5040 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 720 a b c keys720) : Match 5040 a b c keys5040 := by
  apply refine step5040 h bad (by decide) (by decide) valid5040 _ old
  intro i hi
  change i < 4 at hi
  exact test5040_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+11=11^a*41^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
  have h5040 := run5040 h bad h720
  obtain ⟨i,hi,_⟩ := h5040
  exact Nat.not_lt_zero i hi
end FortyOneD11
end Erdos889.PrimeTwentyThree
