import E889PrimeTwentyThreeCore
/-! Exponent residues when 41 divides the term at the indicated offset. -/
namespace Erdos889.PrimeTwentyThree

namespace FortyOneD5
private def cfg : Config := ⟨5,5,41,1,1,0,0⟩
private def keys1 : Keys := ⟨1,1,0x0⟩
private def keys12 : Keys := ⟨3,4,0x3a067094⟩
private def rows12 : List Rule := [
  .div 3,
  .div 7,
  .target,
  .div 13]
private def step12 : Stage := ⟨cfg,1,12,keys1,keys12,rows12,3,0x41041041618618c180410410412082082080c31430c32082082080410410416206186180410410412082082080c30c30c2208208208⟩
set_option maxHeartbeats 5000000 in
private theorem valid12 : ∀ r ∈ rows12, Valid cfg 12 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test12_0 : ∀ i ∈ List.range' 0 1, ∀ x y z : Fin 12, Test step12 i x y z := by decide +kernel
private theorem run12 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 1 a b c keys1) : Match 12 a b c keys12 := by
  apply refine step12 h bad (by decide) (by decide) valid12 _ old
  intro i hi
  change i < 1 at hi
  exact test12_0 i (by simp only [List.mem_range'_1]; omega)
private def keys60 : Keys := ⟨3,6,0x4b701e7c0193⟩
private def rows60 : List Rule := [
  .div 11,
  .pool ⟨31,16,[31,2],[3,5,7,11,13],41,0x1b382b50736⟩,
  .pool ⟨31,18,[31,2,3,17],[5,7,11,13],208,0x1131371995950bf9799b7393ba5575731dd1d14fbd3ddb37d7fe⟩]
private def step60 : Stage := ⟨cfg,12,5,keys12,keys60,rows60,3,0x1420000200000c1000000000000000000000⟩
set_option maxHeartbeats 5000000 in
private theorem valid60 : ∀ r ∈ rows60, Valid cfg 60 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test60_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 5, Test step60 i x y z := by decide +kernel
private theorem run60 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 12 a b c keys12) : Match 60 a b c keys60 := by
  apply refine step60 h bad (by decide) (by decide) valid60 _ old
  intro i hi
  change i < 3 at hi
  exact test60_0 i (by simp only [List.mem_range'_1]; omega)
private def keys120 : Keys := ⟨6,7,0x12e602737016ad803c7c0069e02113⟩
private def rows120 : List Rule := [
  .pool ⟨241,10,[241,2,5],[3,7],48,0x10122110536⟩]
private def step120 : Stage := ⟨cfg,60,2,keys60,keys120,rows120,3,0x1a8803088⟩
set_option maxHeartbeats 5000000 in
private theorem valid120 : ∀ r ∈ rows120, Valid cfg 120 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test120_0 : ∀ i ∈ List.range' 0 3, ∀ x y z : Fin 2, Test step120 i x y z := by decide +kernel
private theorem run120 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 60 a b c keys60) : Match 120 a b c keys120 := by
  apply refine step120 h bad (by decide) (by decide) valid120 _ old
  intro i hi
  change i < 3 at hi
  exact test120_0 i (by simp only [List.mem_range'_1]; omega)
private def keys240 : Keys := ⟨8,8,0x8aeb001273004eaf00c63700d2d3005a5b009697001e1f⟩
private def rows240 : List Rule := [
  .pool ⟨31,26,[31,2,13,19,23],[3,5,7,11,17],176,0x3f5591315b891db3b9f7527b11d1751fcd59f7bdb316⟩,
  .div 17]
private def step240 : Stage := ⟨cfg,120,2,keys120,keys240,rows240,4,0x911817615114311210010110⟩
set_option maxHeartbeats 5000000 in
private theorem valid240 : ∀ r ∈ rows240, Valid cfg 240 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test240_0 : ∀ i ∈ List.range' 0 6, ∀ x y z : Fin 2, Test step240 i x y z := by decide +kernel
private theorem run240 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 120 a b c keys120) : Match 240 a b c keys240 := by
  apply refine step240 h bad (by decide) (by decide) valid240 _ old
  intro i hi
  change i < 6 at hi
  exact test240_0 i (by simp only [List.mem_range'_1]; omega)
private def keys720 : Keys := ⟨0,10,0x0⟩
private def rows720 : List Rule := [
  .div 19,
  .pool ⟨37,10,[37,2,5],[3,7],123,0x10000124014004012182110536⟩,
  .pool ⟨31,27,[31,3,23],[2,5,7,11,13,17,19],296,0x200a800202228a2020808a288808002a0080a8aa02aa82888208a8a2a20822282aa80aa2a⟩]
private def step720 : Stage := ⟨cfg,240,3,keys240,keys720,rows720,2,0x802202220220088802044404401401101110⟩
set_option maxHeartbeats 5000000 in
private theorem valid720 : ∀ r ∈ rows720, Valid cfg 720 r := by decide +kernel
set_option maxHeartbeats 5000000 in
private theorem test720_0 : ∀ i ∈ List.range' 0 8, ∀ x y z : Fin 3, Test step720 i x y z := by decide +kernel
private theorem run720 {n a b c : ℕ} (h : H cfg n a b c) (bad : ¬Target cfg a b c) (old : Match 240 a b c keys240) : Match 720 a b c keys720 := by
  apply refine step720 h bad (by decide) (by decide) valid720 _ old
  intro i hi
  change i < 8 at hi
  exact test720_0 i (by simp only [List.mem_range'_1]; omega)
theorem exponents {n a b : ℕ} (hn : 2000<n) (div : 9699690∣n) (pp : (n+1).Prime) (sol : Erdos889.v_l 1 n=1) (shape : n+5=5^a*41^b) (ha : 0<a) (hb : 0<b) : a%12=1 ∧ b%12=0 := by
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
end FortyOneD5
end Erdos889.PrimeTwentyThree
