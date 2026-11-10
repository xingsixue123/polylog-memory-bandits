import Pool.P0277.Bad
import Pool.P0257.Fit
import Pool.P0276.Bad

/-!
# P0257's joint fitting event is the same for the finite twin and the self-rounding ALG
-/

namespace Pool.P0283

attribute [local instance] Pool.P0082.coinFintype

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0212 Pool.P0236

variable {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι]
  (P : ParD n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (S KM : ℕ)

local notation "QG" => Pool.P0236.PG P η ε L N G γ wE
local notation "TW" => Pool.P0236.withTwin P η ε L N G γ wE S KM

variable (ℓ : LossSeq n)

/-- The forced copy-last runs (P0218's `PL`) of the twin and of the self-rounding ALG have the same start pools. -/
theorem sp_PL_twin (c : ι) (ω : ℕ → RC (QG)) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (QG).K → ι → Bool) (t : ℕ) :
    sp (Pool.P0218.PL (TW) c) ℓ ω ωs φ t = sp (Pool.P0218.PL (QG) c) ℓ ω ωs φ t := by
  unfold sp
  rw [show pool (Pool.P0218.PL (TW) c) ℓ ω ωs φ t = pool (Pool.P0218.PL (QG) c) ℓ ω ωs φ t from
    pool_swap (Pool.P0218.PL (QG) c) ℓ ω ωs φ t]
  rfl

/-- **P0257's `FitAll` is the same for the twin and the self-rounding ALG** (same coin prefix, same bits). -/
theorem fitAll_twin_iff (T : ℕ) (rc₀ : RC (TW)) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (QG).K → ι → Bool)
    (rc : Fin T → RC (TW)) :
    Pool.P0257.FitAll (TW) T ℓ rc₀ ωs φ rc ↔ Pool.P0257.FitAll (QG) T ℓ rc₀ ωs φ rc := by
  unfold Pool.P0257.FitAll
  have h1 : ∀ t, sp (TW) ℓ (Pool.P0210.extR (TW) rc₀ rc) ωs φ t = sp (QG) ℓ (Pool.P0210.extR (QG) rc₀ rc) ωs φ t :=
    fun t => Pool.P0253.sp_twin P η ε L N G γ wE S KM ℓ ωs φ _ t
  have h2 : ∀ c t, sp (Pool.P0218.PL (TW) c) ℓ (Pool.P0210.extR (TW) rc₀ rc) (Pool.P0065.forceS ωs c)
      (Pool.P0065.forceF (TW).K φ c) t = sp (Pool.P0218.PL (QG) c) ℓ (Pool.P0210.extR (QG) rc₀ rc)
      (Pool.P0065.forceS ωs c) (Pool.P0065.forceF (QG).K φ c) t :=
    fun c t => sp_PL_twin P η ε L N G γ wE S KM ℓ c _ _ _ t
  simp only [h1, h2]
  rfl

open Classical in
/-- **The averaged no-overflow bounds coincide**: P0276's `B₁` (twin) and `B₂` (self-rounding ALG) can be taken equal,
since the indicator sums are equal for every array. -/
theorem sum_notFitAll_twin_eq (T : ℕ) (rc₀ : RC (TW)) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (QG).K → ι → Bool) :
    ∑ rc : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) rc *
        (if Pool.P0257.FitAll (TW) T ℓ rc₀ ωs φ rc then 0 else 1) =
      ∑ rc : Fin T → RC (QG), Pool.P0202.pw (wR (QG)) rc *
        (if Pool.P0257.FitAll (QG) T ℓ rc₀ ωs φ rc then 0 else 1) := by
  refine Finset.sum_congr rfl fun rc _ => ?_
  rw [Pool.P0253.pw_twin P η ε L N G γ wE S KM rc]
  have h := fitAll_twin_iff P η ε L N G γ wE S KM ℓ T rc₀ ωs φ rc
  by_cases hf : Pool.P0257.FitAll (QG) T ℓ rc₀ ωs φ rc
  · rw [if_pos (h.2 hf), if_pos hf]
  · rw [if_neg (fun h' => hf (h.1 h')), if_neg hf]

open Classical in
/-- **P0276's `badTermP_twin_avg` with ONE no-overflow bound**: by `sum_notFitAll_twin_eq` the twin's averaged
`P(¬FitAll)` equals the self-rounding ALG's, so a single bound `B` on the latter (e.g. P0257's `sum_not_fitAll_le` for
`QG`) serves for both: `E_arr[badTermP_TW] ≤ 2B + |ι|·2(T+1)²e^{−Lp} + 2(T+1)²e^{−Lp} + (|ι|+2)(T+1)²e^{−Lc}`. -/
theorem badTermP_twin_avg1 (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (hG : 1 ≤ G)
    (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 ≤ η)
    (hS : (∑ j : Fin P.D, (P.sl j : ℝ)) + 1 ≤ S) (hL : (QG).IsLaw) (hN : 0 < (QG).N)
    (hη' : 0 < η) (hwE' : P.wE = wE) {T Lt : ℕ} (hTL : T ≤ 2 ^ L) (hTK : T ≤ KM)
    (rc₀ : RC (TW)) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (Lp Lc : ℝ) {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (B : ℝ)
    (hB : ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QG).D) (Lt := Lt) (K := (QG).K) ps q) ω2 *
      ∑ rc : Fin T → RC (QG), Pool.P0202.pw (wR (QG)) rc *
        (if Pool.P0257.FitAll (QG) T ℓ rc₀ (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2)
            (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc then 0 else 1) ≤ B) :
    ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QG).D) (Lt := Lt) (K := (QG).K) ps q) ω2 *
      Pool.P0246.badTermP (TW) ℓ (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2)
        (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc₀ T Lp
        (Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ
          (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2) (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc₀ T κ)
        (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
        (Pool.P0243.rOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ
          (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2) (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc₀ T ε κ Lc) ≤
      2 * B + (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lp)) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lp)) +
        ((Fintype.card ι : ℝ) + 2) * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) := by
  have hB₁ : ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QG).D) (Lt := Lt) (K := (QG).K) ps q) ω2 *
      ∑ rc : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) rc *
        (if Pool.P0257.FitAll (TW) T ℓ rc₀ (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2)
            (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc then 0 else 1) ≤ B := by
    refine le_trans (le_of_eq ?_) hB
    refine Finset.sum_congr rfl fun ω2 _ => ?_
    rw [sum_notFitAll_twin_eq P η ε L N G γ wE S KM ℓ T rc₀]
  have h := Pool.P0276.badTermP_twin_avg P η ε L N G γ wE S KM hD hLv hlev hG hγ hwE hε hη hS hL hN hη' hwE'
    hTL hTK ℓ rc₀ hκ0 hκ1 Lp Lc hps hq0 hq1 B B hB₁ hB
  linarith

end Pool.P0283
