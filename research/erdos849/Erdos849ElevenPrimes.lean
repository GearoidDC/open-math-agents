import Erdos849ElevenColumns
import Erdos849ElevenHosts
import Erdos849ElevenCollision

namespace Erdos849ElevenPrimes

open Erdos849PatternBridge

/-- The finite exclusion and published fixed-column classifications are the
    two external inputs to this all-size restriction on five-row witnesses. -/
theorem eleven_distinct_prime_factors {a : ℕ}
    (hc : 5 ≤ (Erdos849Cases.rows a).ncard)
    (base : ∀ b ≤ 10^100, (Erdos849Cases.rows b).ncard ≤ 4)
    (classified : 10^100 < a → ∀ t ∈ classifiedPairs, ¬∀ j ∈ t, occurs a j) :
    11 ≤ a.primeFactors.card := by
  have ha : 10^100 < a := by
    by_contra! h
    have := base a h
    omega
  by_contra! hf
  obtain ⟨j,d,h7,hjd,hd,⟨m,hjm,hm⟩,⟨n,hdn,hn⟩⟩ :=
    Erdos849ElevenColumns.deep_pair ha (by omega) hc (classified ha)
  have hsize : 10^100 < n.choose d := by rwa [hn]
  have hcount : (n.choose d).primeFactors.card ≤ 10 := by rw [hn]; omega
  have hrow : 10^7 < n := by
    by_contra! h
    have hle := (Nat.choose_le_pow n d).trans ((Nat.pow_le_pow_left h d).trans
      (Nat.pow_le_pow_right (by decide : 0 < (10:ℕ)^7) hd))
    have : ((10:ℕ)^7)^10 < 10^100 := by decide
    omega
  have eq := hm.trans hn.symm
  have applyHost {p e b s : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (hdiv : p^e ∣ n.choose d)
      (hb : 1 ≤ b) (hB : b ≤ Erdos849ElevenCollision.cofactorLimit d)
      (hs : s < d) (hint : d = 8 ∨ (1 ≤ s ∧ s + 1 < d)) (heq : n = b*p^e+s) : False := by
    subst n
    exact Erdos849ElevenCollision.no_collision (by omega) hd h7 hjd hp h11 hb hB hs hint
      hsize hjm (eq ▸ hdiv) eq
  rcases (by omega : d=8 ∨ d=9 ∨ d=10) with rfl | rfl | rfl
  · obtain ⟨p,e,b,s,hp,h11,_,hdiv,hb,hB,hs,heq⟩ :=
      Erdos849ElevenHosts.column_eight hrow hcount
    exact applyHost hp h11 hdiv hb hB hs (Or.inl rfl) heq
  · obtain ⟨p,e,b,s,hp,h11,_,hdiv,hb,hB,hs1,hs7,heq⟩ :=
      Erdos849ElevenHosts.column_nine hrow hcount
    exact applyHost hp h11 hdiv hb hB (by omega) (Or.inr ⟨hs1,by omega⟩) heq
  · obtain ⟨p,e,b,s,hp,h11,_,hdiv,hb,hB,hs1,hs8,heq⟩ :=
      Erdos849ElevenHosts.column_ten hrow hcount
    exact applyHost hp h11 hdiv hb hB (by omega) (Or.inr ⟨hs1,by omega⟩) heq

end Erdos849ElevenPrimes
