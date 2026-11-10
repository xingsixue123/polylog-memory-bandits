import Pool.P0234.Absorb
import Pool.P0228.ExpD

/-!
# The ALG term `algTerm` (P0217/P0234) in expectation, from a pathwise bound on a good event (generic in the `ParD`)
-/

namespace Pool.P0250

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (rc₀ : RC P)

/-- **Expectation step for ALG's term (generic).** If on a decidable good event `G` of the `T`-coin path the ALG
gap against arm `i` is at most `rest`, then P0234's `algTerm` (P0217's `algT` integrand form) is at most
`wE·E[[G]·rest] + wE·T·P(¬G)`. Off `G` the gap is at most `T` (`aPol ≤ 1`, losses `≥ 0`). -/
theorem alg_expect_of (hL : P.IsLaw) (hN : 0 < P.N) (hwE : 0 ≤ P.wE) (T : ℕ) (i : Fin n)
    (G : (Fin T → RC P) → Prop) [DecidablePred G] (rest : (Fin T → RC P) → ℝ)
    (hG : ∀ ω, G ω → ∑ u ∈ range T, (aPol P ℓ ωs φ (Pool.P0210.extR P rc₀ ω) u - ((ℓ u i).toNat : ℝ)) ≤ rest ω) :
    Pool.P0234.algTerm P ℓ ωs φ rc₀ T i ≤
      P.wE * ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if G ω then rest ω else 0) +
        P.wE * T * ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if G ω then 0 else 1) := by
  unfold Pool.P0234.algTerm
  have hm := Pool.P0228.marg P rc₀ hL hN (fun ω u => P.wE * (aPol P ℓ ωs φ ω u - ((ℓ u i).toNat : ℝ)))
    (fun u _ _ h => by rw [Pool.P0228.aPol_congr P ℓ ωs φ u h]) T
  rw [hm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hp := Pool.P0228.pw_nonneg P hL ω
  rw [← Finset.mul_sum]
  have key : ∑ u ∈ range T, (aPol P ℓ ωs φ (Pool.P0210.extR P rc₀ ω) u - ((ℓ u i).toNat : ℝ)) ≤
      (if G ω then rest ω else 0) + T * (if G ω then 0 else 1) := by
    split_ifs with hg
    · simpa using hG ω hg
    · have : ∀ u ∈ range T, aPol P ℓ ωs φ (Pool.P0210.extR P rc₀ ω) u - ((ℓ u i).toNat : ℝ) ≤ 1 := fun u _ => by
        have h1 := Pool.P0228.aPol_le_one P ℓ ωs φ (Pool.P0210.extR P rc₀ ω) u
        have h2 : (0 : ℝ) ≤ ((ℓ u i).toNat : ℝ) := Nat.cast_nonneg _
        linarith
      calc _ ≤ ∑ _u ∈ range T, (1 : ℝ) := Finset.sum_le_sum this
        _ = 0 + T * 1 := by simp
  have e : P.wE * T * (Pool.P0202.pw (wR P) ω * (if G ω then 0 else 1)) +
      P.wE * (Pool.P0202.pw (wR P) ω * (if G ω then rest ω else 0)) =
      Pool.P0202.pw (wR P) ω * (P.wE * ((if G ω then rest ω else 0) + T * (if G ω then 0 else 1))) := by ring
  rw [add_comm, e]
  refine mul_le_mul_of_nonneg_left ?_ hp
  exact mul_le_mul_of_nonneg_left key hwE

end Pool.P0250
