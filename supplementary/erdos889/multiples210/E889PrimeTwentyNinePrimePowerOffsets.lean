import E889PrimeTwentyNineCore

/-! Modular certificates for first offsets 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27. -/

namespace Erdos889.PrimeTwentyNine

namespace D2
private def cfg : Config := ⟨2,2,29,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x61⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .target,
  .div 13,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x410410412082082081041041042082082080410410412082082081041041042082082080410410412082082080c31430c2208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨3,6,0x499036340781⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],427,0x24800810a0402002004184001008040480a001100812400040801202240000804016004008010028810008400310040010082030412⟩,
  .prime 31]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x2040000a200000c0⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨1,7,0x2755⟩
private def rows120 : List Rule := [
  .pool ⟨61,4,[61,2],[3],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨31,25,[31,5,17,19,23],[2,3,7,11,13],41,0x1fffffffffe⟩,
  .pool ⟨241,14,[241,2,7],[3,5,11,13],305,0x1a60a40220c41020200290c00801200025004132080290001200400c25001010208c110094196⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0x89a249000⟩
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
private theorem test240_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 1 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+2=2^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D2

namespace D3
private def cfg : Config := ⟨3,3,29,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨3,4,0x97037061⟩
private def rows12 : List Rule := [
  .div 5,
  .target,
  .div 13,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x6186186180000000000c30c30c3000000000430410a100000000000c30c30c3000000000618618618000000000082102081000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨3,6,0x4b1006940a8d⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨61,6,[61,2,3],[5],112,0x1131950bd9b33a5571d14f9db77e⟩,
  .pool ⟨61,2,[61,2],[],112,0x131050301332215211107152736⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x28000880003000040⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 3 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨4,7,0x4b6809cc4042c200325⟩
private def rows120 : List Rule := [
  .pool ⟨41,25,[41,5,17,19,23],[2,3,7,11,13],775,0x23b024eef28b230510b32b70fbf0eb84acbf63a4f625959e41e040aa56756a3e761f701196ec749e4493b38a2c8835428ebdc3eecbee1236fd8691d8967779079186a95197a8fdf97d8256db90d27902caee28f030d12b3af71f3f2eb00adbf23a⟩,
  .pool ⟨41,22,[41,2,11,17,19],[3,5,7,13],16,0x1b5f⟩,
  .pool ⟨41,18,[41,2,3,17],[5,7,11,13],16,0x1b5f⟩,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0x7f3a94048⟩
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
private theorem test240_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 4 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+3=3^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D3

namespace D4
private def cfg : Config := ⟨4,2,29,1,2,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x62⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .target,
  .div 13,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x4104104130c30c30c04104104120820820804104104130c30c30c0410410412082082080410410412cb34b2ca041041041208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨3,6,0x49a036380782⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,3,[31,3],[2],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,2,[31,2],[],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x2040000a200000c0⟩
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
  .pool ⟨61,8,[61,2],[3,5,7],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨41,40,[41,2,5,17,19,23,29,37],[3,7,11,13,31],61,0x1ffffffffffffffe⟩,
  .pool ⟨41,9,[41,3],[2,5,7],61,0x141002040810020a⟩,
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,2,0xff9900⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 3 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+4=2^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=2 ∧ b%12=0 := by
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
end D4

namespace D5
private def cfg : Config := ⟨5,5,29,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x61⟩
private def rows12 : List Rule := [
  .div 3,
  .div 7,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x410410412082082080410410412082082080c30c30c32082082080410410412082082080410410412082082080c31030c2208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨2,6,0x1294018d⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨61,10,[61,2,5],[3,7],112,0x131050301332215211107152736⟩,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],48,0x190014116⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],208,0x1131371995950bf9799b7393ba5575731dd1d14fbd3ddb37d7fe⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x3000005010000020040⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨1,7,0x30d⟩
private def rows120 : List Rule := [
  .pool ⟨41,15,[41,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨313,10,[313,2,5],[3,7],48,0x10122110536⟩,
  .pool ⟨41,6,[41,2,3],[5],16,0x1b5f⟩,
  .pool ⟨41,4,[41,2],[3],16,0x317⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0x69a044⟩
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
  .div 17]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 1 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+5=5^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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

namespace D7
private def cfg : Config := ⟨7,7,29,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨5,4,0x890290a5045061⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,4,0x101010101010101010101010131813131713101010101010101010101010101010101010161313151313101010101010101010101010101010101010131314131312101010101010⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨8,6,0x2ce4051500ee4089102e140111036940199⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨61,14,[61,2,7],[3,5,11,13],176,0xf79d59f91341d57b31379ab3d919bd5705913f3573de⟩,
  .prime 61,
  .pool ⟨31,13,[31,13],[2,3,5,7,11],80,0xa08800220a⟩,
  .pool ⟨31,28,[31,2,7,17,19,23],[3,5,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,2,[31,2],[],63,0x6880800180010116⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],99,0x7ac8e0d5bc44f223dab07135e⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .pool ⟨31,2,[31,2],[],16,0xd117⟩,
  .pool ⟨31,6,[31,2,3],[5],36,0x19f3d73df⟩,
  .pool ⟨31,3,[31,3],[2],80,0xa08800220a⟩,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩,
  .pool ⟨61,13,[61,13],[2,3,5,7,11],275,0x50440010811100040008400880208401420428021040110021000200088810800220a⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,5,0xa000058000000000300004c0002400000120000b000020000a00000000004880000000000c0001000022000200000003800030000280000000003c0001000180007000000000034000080000400⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 5, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 5 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨8,7,0x1a3a8059d4068720285101aa0805c140049a02011⟩
private def rows120 : List Rule := [
  .pool ⟨31,19,[31,17,19],[2,3,5,7,11,13],1464,0x8a20a08228028220008a08828000028808000a28228208a00800808220a28820220828a08a20000820800a08008808a08028820828820008000820220800020208828828008200200028a08800a28a00808008a00200a00208020000008020800a00800a20020200a28a00220a28000800820028228220808000208808200020008228208228020a20220020a00208200008a20a28208808228a08820200200a20828828a00020228000028220a20008828028820a08a2⟩,
  .pool ⟨41,13,[41,13],[2,3,5,7,11],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .prime 41,
  .pool ⟨31,29,[31,17,19,23,29],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,22,[41,2,11,17,19],[3,5,7,13],16,0x1b5f⟩,
  .pool ⟨31,3,[31,3],[2],1312,0xa088002202000000000080080a00880200000008008000000000800000002000200002000a020800000020020000000880202000002088000000022000000020000002000000008002000000000020000000000000080000000000800200000000800000080000000880000000220800000808022000000080080000002080a00080000800080000000200000000020020000000802200a020020000000000808800220a⟩,
  .pool ⟨41,14,[41,2,7],[3,5,11,13],31,0x121d47b6⟩,
  .pool ⟨41,20,[41,2,5,17,19],[3,7,11,13],800,0x30d0bdb2b47594f8f6f131d1bcb3b5f495f9f7f030f0bdb2b47594f8f6f135d1bcb3b57495f9f7f0b0d0bdf2b475b4f8f6f131d1bcb3b57495f9f7f030d1bdb2b4f594f8f6f131f1bcb3b57495f9f7f034d0bdb2b47595f8f6f1b1d1bcf3b574b5f9f7f⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,4,0xfed7c56521123223b44a398312210000⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 8 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨4,8,0xa47500e0b100c8c9005051⟩
private def rows240 : List Rule := [
  .pool ⟨31,29,[31,19,23,29],[2,3,5,7,11,13,17],819,0xa00000000000000800240000200200005020841200a48200000208028000804008100020000344000300000000008200004000020100000020024000000000800200020004000020008848044000808100000004000240200100001840100008000a0c80002⟩,
  .div 17,
  .pool ⟨41,35,[41,5,7,19,23,29],[2,3,11,13,17,31],964,0x200a8820880200a0a8a22aa808a80a2082822a8a080802aa0800280202222220200a00082aa0080828aa20a082280a880aaa228a828020088208a80222a808a288aa2a8280822000a880a8228a0a200828a8aa0028aaa0aa2a220222a2a82aa8a002a8a8a08022828a20a808a80022080a0aa2a88a2880aa2⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,3,0x2492b1a4a84b249249201048⟩
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
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+7=7^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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

namespace D8
private def cfg : Config := ⟨8,2,29,1,3,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x63⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .target,
  .div 13,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x1041041042082082080410410412082082081041041042082082080410410412082082080c31430c2208208208041041041208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨2,6,0x363c0783⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,7,[31,7],[2,3,5],793,0x12d020a252081880644c112020006092460020080020180882a080f008c000022017044708b2850016000655a08040086844885840080416a98001a0028534438883a01100000c403c0415044060100040100189241800101220c8980460412914102d2⟩,
  .pool ⟨31,6,[31,2,3],[5],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,4,[31,2],[3],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x3080000228000100⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨4,7,0x1ca5806d2c0721e01b0f⟩
private def rows120 : List Rule := [
  .pool ⟨61,16,[61,2],[3,5,7,11,13],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0x8d1000⟩
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
  .div 17]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 4 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+8=2^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=3 ∧ b%12=0 := by
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
end D8

namespace D9
private def cfg : Config := ⟨9,3,29,1,2,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨3,4,0x98038062⟩
private def rows12 : List Rule := [
  .div 5,
  .div 7,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x41041041000000000630618a180000000000410410410000000002082082080000000000c31030c2000000000208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨2,6,0x6980a8e⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],560,0xf5b1c723d8153c0d59d0a119ad5210d31141519254912b714e5331243910738d831b1ab1b183639c1138491994e51da91254931505119610956b310a17356079503789c71b5e⟩,
  .pool ⟨61,6,[61,2,3],[5],112,0x1131950bd9b33a5571d14f9db77e⟩,
  .pool ⟨61,10,[61,2,5],[3,7],100,0x1111711117115171113711537⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x18000a80004000040⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 3 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨0,7,0x0⟩
private def rows120 : List Rule := [
  .pool ⟨61,29,[61,17,19,23,29],[2,3,5,7,11,13],492,0x8200a28808008a28a08220800820028028820a20808200000220220000a08020a00008808800000820208a08228028008200208820a28a20020228a0082⟩,
  .pool ⟨41,5,[41,5],[2,3],25,0x210863⟩,
  .pool ⟨41,13,[41,13],[2,3,5,7,11],61,0x1713e6940a59f23a⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,2,0x6900⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 2, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 2 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+9=3^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=2 ∧ b%12=0 := by
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
end D9

namespace D11
private def cfg : Config := ⟨11,11,29,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨0,4,0x0⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .target,
  .div 13,
  .pool ⟨37,22,[37,2,11,17,19],[3,5,7,13],61,0x1ffffffffffffffe⟩,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x1451451452082082081451451452082082080c30c30c32082082081451451452082082081451451452082082080c31030c2208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+11=11^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  obtain ⟨i,hi,_⟩ := h12
  exact Nat.not_lt_zero i hi
end D11

namespace D13
private def cfg : Config := ⟨13,13,29,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨17,4,0xa90890690490290090a50850650450250050a1081061041021⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .target]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,5,0x802008020080200802008020080200cc320c4300bc2e0802008020080200802008020080200802008020080200b42c0ac2a0a42808020080200802008020080200802008020080200802009c260942408c22080200802008020⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨21,6,0xead020e4022d01454072d0285409ad03a140485028a40705000a4021902c340501012640d8d02804099900e340c81⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],99,0x7ac8e0d5bc44f223dab07135e⟩,
  .pool ⟨31,2,[31,2],[],16,0xd117⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  .pool ⟨421,42,[421,2,3,7,17,19,23,29,37,41],[5,11,13,31],792,0x19db517733091d1f3595b8fb13f9b95d2791d193777057dd939f57ebf573bbd39e3ddb195331493d9f3db5bab317fbf179a5d9f5133774d5d5b31d1fcff57b9fd1d63d5959773341399d3db13afb177bf97da7d9f5917754d79db39f5fef753bbf53de⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨31,2,[31,2],[],63,0x6880800180010116⟩,
  .pool ⟨61,26,[61,2,13,17,19,23],[3,5,7,11],421,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],208,0x1131371995950bf9799b7393ba5575731dd1d14fbd3ddb37d7fe⟩,
  .pool ⟨61,14,[61,2,7],[3,5,11,13],176,0xf79d59f91341d57b31379ab3d919bd5705913f3573de⟩,
  .pool ⟨31,27,[31,3,17,19,23],[2,5,7,11,13],61,0x1ffffffffffffffe⟩,
  .pool ⟨31,7,[31,7],[2,3,5],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .pool ⟨31,20,[31,2,5,17,19],[3,7,11,13],75,0x116026c145829b0536⟩,
  .prime 31,
  .pool ⟨31,27,[31,3,17,19,23],[2,5,7,11,13],45,0x55898f135e⟩,
  .pool ⟨31,7,[31,7],[2,3,5],80,0x82000202000080800082⟩,
  .pool ⟨31,10,[31,2,5],[3,7],48,0x1109b2514db6⟩,
  .pool ⟨31,7,[31,7],[2,3,5],421,0x1756731e5683b44a660dfb81977f38db0e4ead3405d0eba5e252001291e975c2e80b2d5c9c36c73fba6077ec19948b705a9e339aba⟩,
  .pool ⟨31,10,[31,2,5],[3,7],427,0x6ca0c851a0c022028c41a5001819440c81a021168832500042c41682342000a4c11688405813022981800a58231404403058a130536⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],421,0x1756731e5683b44a660dfb81977f38db0e4ead3405d0eba5e252001291e975c2e80b2d5c9c36c73fba6077ec19948b705a9e339aba⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],72,0x88a2200aaa208aaa⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],488,0x15139115d75315515155119713d11313935195911751d1d593d5d5111397071557d79191559151d317d595d3555357d15715d793d3d397531197d55796⟩,
  .pool ⟨31,17,[31,17],[2,3,5,7,11,13],16,0x8002⟩,
  .pool ⟨31,15,[31,3,5],[2,7,11,13],200,0xa88a00a20aa88800a22aa08800220aa88a00222aa08a00a22a⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],16,0xd397⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],549,0x1a60a00261041120a0084490094824032014120184820800120982106094002924004c800925000a41821064120004104860120a01300904a4024884014122082190014196⟩,
  .pool ⟨421,26,[421,2,13,17,19,23],[3,5,7,11],620,0x13350d199053114b711213b5a33192451d2b131cb11d6f39d6959501799e9039a97b9477398d3958d53123511c552dc1591ed399c3191031bd4973d471b8a75b565115e77b10b7b5af51d8f335e⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,6,0x600bc0000000017000000000680580000000b8000000002d017000000000b004c000000060000000000901400000000024000000001664000000002b0000000005c0a800000000130000000180290000000005c01c000000001600000001500400000000050000000000301300000000d00000000040030000000000f02800000000d00000000048030000000000b00000000038d00000000040000000000c00f0000000009c000000034098000000000c01100000000094000000034040000000000c0000000003c038000000034000000002400c0000000002c02800000000800000000050090000000002400000000091800000000010000000008c08800000000210000000020080000000008007c000000000700000000600500000000010000000000301e00000000200000000004074000000001c01b000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 17, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 17 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨22,7,0x5cea01039002348088b4050a200a15016348038b4028a203215019328050a40588200e410160280381403cca000290051e80a0040647a01401⟩
private def rows120 : List Rule := [
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],915,0x20820000a6020080100022002020004090810c840040008001000021900200001029000000000000208000a00200041120840000008001000024340328000000840800209020000a6000886092502c021204100068220001000120008301200000060008120001000141100220a00108b0092⟩,
  .pool ⟨41,7,[41,7],[2,3,5],48,0x820000000082⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],155,0x239024ace20b020510a32b50f3b0eb008cb721a⟩,
  .pool ⟨41,7,[41,7],[2,3,5],31,0x121d47b6⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],341,0x10005e2024580224044800c418080600000c000180000060000c000018040608c0048809100689011e8002⟩,
  .pool ⟨61,12,[61,2,3],[5,7,11],224,0x121850bc9b32a4571c14f8da76e1131950bd9a33a5561d14f9db77e⟩,
  .pool ⟨41,19,[41,17,19],[2,3,5,7,11,13],305,0x1a70bc423bd491206e2a98c308092050a7a163331a1794281240430c6551d81224af7108f4396⟩,
  .pool ⟨61,27,[61,3,17,19,23],[2,5,7,11,13],1476,0xa280aaa80808aaaaa8a2a28028220a802a822aa288a2820822a2222080a8a0a0a8200a8088820028a0288a0a2aa02800a28228a822aa8aa20a22a8a8282a202aa888a008aa8a0a2208808a20a80a88a2aa08882020002a22a2002a88022a8008a88a80008082220aa8a22a02a08a2022088a0a2aa200a222aa808a8282a2a88a08aa2aa882a28828a00280aa8a0a2280a2800822202a0082a0a0a2a0208888a8820828a228aa882a802a08828028a8a2aaaaa20202aaa028a⟩,
  .pool ⟨61,27,[61,3,17,19,23],[2,5,7,11,13],1364,0x8a20820220220800a0a002280a80a022208888280880a0008aa008022aa00820a0a0a80028a0028a000a8282820802aa200802a8800280880a088882220280a80a20028280082202202082288000000002aa2aaaa08822822a2282288a0282a820a802822202888820a88880aa8002a88a200220a2808280a2a0828a082a280a080a2822002288aa000aa80888a820888a02220a00a820aa0a0288a20a22a20a20882aaaa2aa⟩,
  .pool ⟨31,23,[31,17,19,23],[2,3,5,7,11,13],451,0x30ab2430a393b4ee17f0196460d90203b1d0108ea02c568f95aa0920aeb6d8a160694cbca8af7746235bf24f1d863d01388522438f39b22f2⟩,
  .pool ⟨41,26,[41,2,13,17,19,23],[3,5,7,11],620,0x13350d199053114b711213b5a33192451d2b131cb11d6f39d6959501799e9039a97b9477398d3958d53123511c552dc1591ed399c3191031bd4973d471b8a75b565115e77b10b7b5af51d8f335e⟩,
  .pool ⟨31,10,[31,2,5],[3,7],800,0x8110004001012000015000000980010517000210011100000181000041400020018011011708000005110002010101000140800001c001013700401001100800010500000340000101800181170840000130000011010108014004010182110537⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],160,0x5105011110050105110083114303401191814196⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,6,0xc208388c3212a07ca78a29d70a29b29a64a0830c20c20830c208360b2d759551348b2d120a2882092481d03c71810460830c238514d0441010830c2001040⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 21, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 21 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨11,8,0x20b10080e10080690050c900505100a0a100d0b900d04100507900500100a001⟩
private def rows240 : List Rule := [
  .div 17,
  .pool ⟨61,12,[61,2,3],[5,7,11],241,0x1fba6a35a231798f24257c4cba0e12fd21c174c8fa9093c67a3116b15977e⟩,
  .pool ⟨31,10,[31,2,5],[3,7],1575,0x40000020101100000008000205020200040000001140800004000800360008101801101160040100001000020220008000004040204040009000000a2800000080030002c10102030002026c100020000200004044020004000008040809005000800045000000300020005800200060044145821004000000008808804000000001009101000a40000008a0020002010c000b0004000c000829b0420000000800010510080000000120102020014800000134000010400180016004810182110536⟩,
  .pool ⟨31,27,[31,3,19,23],[2,5,7,11,13,17],328,0xa0a822aaa200888028a08a082a888a820002280a00a028800082a222a820a20a280222008aaa882a0a⟩,
  .pool ⟨31,10,[31,2,5],[3,7],1600,0x800000400101200000100000090001040000020001110000008000004140002001801101170800000401000201010100000080000140010020000010011008000004000003400001018001811700400000200000110101080000040001020100010000008110004000002000015000000980010517000210000100000181000040000020010011000008000005100002000001000140800001c001013700401000000800010500000200000101000180010840000130000010000108014004010182110537⟩,
  .pool ⟨31,29,[31,19,23,29],[2,3,5,7,11,13,17],819,0xa00000000000000800240000200200005020841200a48200000208028000804008100020000344000300000000008200004000020100000020024000000000800200020004000020008848044000808100000004000240200100001840100008000a0c80002⟩,
  .pool ⟨31,21,[31,3,7,19],[2,5,11,13,17],9,0x9b⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],320,0x11010011000101010100821102030011818100824005010110050005100083014303400190814196⟩]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,5,0x4807882000000003c0e00000300c000000280a000000000006808060160000001806000000000000080200000028090000008100⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 22, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 22 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .div 19]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 11, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 11 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+13=13^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D13

namespace D16
private def cfg : Config := ⟨16,2,29,1,4,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x64⟩
private def rows12 : List Rule := [
  .div 7,
  .div 3,
  .div 5,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x45145145128a28a28a45145145120820820845145145128a28a28a45145145130c34c30b45145145128a28a28a451451451208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨2,6,0x36400784⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩,
  .pool ⟨31,8,[31,2],[3,5,7],793,0x1ef6a9b6730a38a4ec6d13316e467492e680b6c808287c09b2f181f0fcc60c22f4f7045738b2870016052755aad5420b6877b85b410aad56ab9281a003853473a883bcbd10c18cfc3e063d3640f850404db4059d24b989da3322d8dc94714339b655bde⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x3080000228000100⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨6,7,0x369801b10016a0003d0005a0800f04⟩
private def rows120 : List Rule := [
  .pool ⟨31,15,[31,3,5],[2,7,11,13],369,0x100844020590854130148e0c4615d890482c10089612e10280d0e5188a9f120901924032d01d0452131cb15977e⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0x1858d1⟩
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
  .div 17]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 6, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 6 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+16=2^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=4 ∧ b%12=0 := by
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

namespace D17
private def cfg : Config := ⟨17,17,29,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x61⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .target,
  .div 13,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x410410412082082081041041042082082080410410412082082081041041042082082080410410412082082080c31430c2208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨1,6,0xa99⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨61,34,[61,2,17,19,23],[3,5,7,11,13,29,31],319,0x130f00bb14019acb46301042c29ce59a65781f1553056149a44886b4bc77d39928266fd502bf0736⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],116,0x2008a002880202a2a8828a08aa2a⟩,
  .pool ⟨31,14,[31,2,7],[3,5,11,13],16,0xd397⟩,
  .pool ⟨31,5,[31,5],[2,3],25,0x210863⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x4000003028000010040⟩
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
  .pool ⟨41,10,[41,2,5],[3,7],31,0x121d47b6⟩,
  .pool ⟨31,24,[31,2,3,17,19,23],[5,7,11,13],41,0x1fffffffffe⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,1,0x6⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 1 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+17=17^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D17

namespace D19
private def cfg : Config := ⟨19,19,29,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x61⟩
private def rows12 : List Rule := [
  .div 5,
  .div 3,
  .target,
  .div 13,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x30c30c30c20820820830c30c30c2082082082cb2cb2cb20820820830c30c30c20820820830c30c30c2082082082cb34b2ca208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨2,6,0x36640781⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨61,7,[61,7],[2,3,5],181,0x10401408204430019030203301030260030881040a0082⟩,
  .pool ⟨31,5,[31,5],[2,3],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .pool ⟨31,12,[31,2,3],[5,7,11],112,0xf59161ab1d034ee58171ab0d135e⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x18000540001000100⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 1 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨4,7,0xdaa80e46405a7a00f01⟩
private def rows120 : List Rule := [
  .pool ⟨41,12,[41,2,3],[5,7,11],80,0x10901430a111905135e⟩,
  .pool ⟨41,8,[41,2],[3,5,7],31,0x121d47b6⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0x361602⟩
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
  .div 17]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,1,0x0⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 4, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 4 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+19=19^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end D19

namespace D23
private def cfg : Config := ⟨23,23,29,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨0,4,0x0⟩
private def rows12 : List Rule := [
  .div 3,
  .div 5,
  .target,
  .div 13,
  .pool ⟨37,9,[37,3],[2,5,7],80,0xa08800220a⟩,
  .div 7]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x410410412082082081451451452082082080410410412082082081451451452082082080410410412082082080c31030c2208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+23=23^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
  by_contra neg
  have bad : ¬Target cfg a b 0 := by
    rintro ⟨a1,b1,c1⟩
    exact neg ⟨a1,b1⟩
  have h : H cfg n a b 0 := ⟨by simpa [cfg] using shape,ha,hb,Or.inr rfl,fun _ => rfl,hn,div,pp,sol⟩
  have h1 : Match 1 a b 0 keys1 := ⟨0,by decide,Nat.mod_one _,Nat.mod_one _,Nat.mod_one _⟩
  have h12 := run12 h bad h1
  obtain ⟨i,hi,_⟩ := h12
  exact Nat.not_lt_zero i hi
end D23

namespace D25
private def cfg : Config := ⟨25,5,29,1,2,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨1,4,0x62⟩
private def rows12 : List Rule := [
  .div 7,
  .div 3,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x410410412082082080410410412cb2cb2cb0410410412082082080410410412082082080410410412cb30b2ca041041041208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨1,6,0x782⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,6,[31,2,3],[5],80,0x5511415110b19d05335e⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],208,0x1131371995950bf9799b7393ba5575731dd1d14fbd3ddb37d7fe⟩,
  .pool ⟨31,11,[31,11],[2,3,5,7],244,0x2002a8288a0208000820288a0aa00222aa00a0882a28a8a8a2a0882802aa2⟩,
  .pool ⟨61,11,[61,11],[2,3,5,7],248,0x802a200200822a0a882008008a8020a2a808a88aa2880a0228aa22a202a8a⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x4000003010000008140⟩
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
  .pool ⟨41,4,[41,2],[3],16,0x317⟩,
  .pool ⟨41,5,[41,5],[2,3],183,0x4406824020400020424880000112420400020402416022⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,1,0xa⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 1 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+25=5^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=2 ∧ b%12=0 := by
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
end D25

namespace D27
private def cfg : Config := ⟨27,3,29,1,3,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨3,4,0x99039063⟩
private def rows12 : List Rule := [
  .div 5,
  .div 7,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x41041041000000000630618a180000000000410410410000000002082082080000000000c31030c2000000000208208208000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨3,6,0x4b30069c0783⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨271,28,[271,2,7,17,19,23],[3,5,11,13],528,0x94910432100190d248128a20369a0592590c10126404584830d16cb65229b4186194900532100090d349128b21369b0492580d10136504594930d06cb65328b4196⟩,
  .pool ⟨61,18,[61,2,3,17],[5,7,11,13],560,0xf5b1c723d8153c0d59d0a119ad5210d31141519254912b714e5331243910738d831b1ab1b183639c1138491994e51da91254931505119610956b310a17356079503789c71b5e⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x280008800010000c0⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 3 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨6,7,0x4ede009330169f803cfc05a0600f03⟩
private def rows120 : List Rule := [
  .pool ⟨41,15,[41,3,5],[2,7,11,13],61,0x1713e6940a59f23a⟩,
  .pool ⟨61,7,[61,7],[2,3,5],164,0x8820a0220282088002aa88a282a02a0a288aaa⟩,
  .pool ⟨41,14,[41,2,7],[3,5,11,13],16,0xd397⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,4,0x822701106543⟩
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
private theorem test240_0 : ∀ i ∈ List.range' 0 6, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 6 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 223092870∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+27=3^a*29^b) (ha : 0<a) (hb : 0<b) : a%12=3 ∧ b%12=0 := by
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
end D27
end Erdos889.PrimeTwentyNine
