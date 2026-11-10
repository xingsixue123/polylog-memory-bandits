import Pool.P0246.AbsorbP
import Pool.P0257.Fit
import Pool.P0250.WalkParam
import Pool.P0253.Twin

/-!
# F6 of P0262's endgame: the bad events, averaged over the sampling/filter arrays

Two bad-event terms of the machine bound are averaged over the sampling/filter arrays here.
* P0246/P0263's `badTermP` (`badTermP_avg`) is bounded by an averaged no-overflow bound `B` (any bound on P0257's
  `P(¬FitAll)`, e.g. P0257's `sum_not_fitAll_le`, see `badTermP_avg_ovf`), plus exponential terms, plus the averaged
  `P(¬AlgOK)` for the same process and budgets, which is NOT bounded by `badTermP_avg` itself.
* P0253's `P(¬AlgOK)` for the finite twin with P0243's budgets (`algOK_twin_avg`) is bounded by exponential terms plus
  the no-overflow bound of the self-rounding process `QG`.
* `badTermP_twin_avg` composes the two for the twin `TW`, with two no-overflow bounds (`TW`'s and `QG`'s).
P0250/P0268's `P(¬GoodAll)` is NOT treated here (it is P0266's). `exp_term_le` and `badExp_le` make the
exponential terms `≤ 1/(T+1)`.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065

namespace Pool.P0276

attribute [local instance] Pool.P0082.coinFintype

/-- Averaging a pointwise bound against a probability weight. -/
theorem avg_le {α : Type} [Fintype α] (w f g : α → ℝ) (C : ℝ) (hw0 : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1)
    (h : ∀ a, f a ≤ g a + C) : ∑ a, w a * f a ≤ ∑ a, w a * g a + C := by
  have : ∑ a, w a * f a ≤ ∑ a, w a * (g a + C) :=
    Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hw0 a)
  simpa [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1] using this

/-- **Numerics.** If `L ≥ 3·log(T+1) + log c` with `c > 0`, then `c·(T+1)²·e^{−L} ≤ 1/(T+1)`. -/
theorem exp_term_le {T : ℕ} {c L : ℝ} (hc : 0 < c) (hL : 3 * Real.log ((T : ℝ) + 1) + Real.log c ≤ L) :
    c * (((T : ℝ) + 1) ^ 2 * Real.exp (-L)) ≤ 1 / ((T : ℝ) + 1) := by
  have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hexp : Real.exp (-L) ≤ Real.exp (-(3 * Real.log ((T : ℝ) + 1) + Real.log c)) :=
    Real.exp_le_exp.2 (by linarith)
  have e1 : Real.exp (-(3 * Real.log ((T : ℝ) + 1) + Real.log c)) = 1 / (c * ((T : ℝ) + 1) ^ 3) := by
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hc, ← Real.log_rpow hT,
      Real.exp_log (by positivity)]
    rw [show ((T : ℝ) + 1) ^ (3 : ℝ) = ((T : ℝ) + 1) ^ 3 by norm_cast]
    field_simp
  rw [e1] at hexp
  calc c * (((T : ℝ) + 1) ^ 2 * Real.exp (-L)) ≤ c * (((T : ℝ) + 1) ^ 2 * (1 / (c * ((T : ℝ) + 1) ^ 3))) := by
        gcongr
    _ = 1 / ((T : ℝ) + 1) := by field_simp


/-- The exponential part of `badTermP` (P0246) is `≤ 1/(T+1)` once `L ≥ 3·log(T+1) + log(2|ι| + 2)`. -/
theorem badExp_le {ι : Type} [Fintype ι] {T : ℕ} {L : ℝ}
    (hL : 3 * Real.log ((T : ℝ) + 1) + Real.log (2 * Fintype.card ι + 2) ≤ L) :
    Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) ≤
      1 / ((T : ℝ) + 1) := by
  have h := exp_term_le (T := T) (c := 2 * Fintype.card ι + 2) (by positivity) hL
  calc Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)
      = (2 * Fintype.card ι + 2) * (((T : ℝ) + 1) ^ 2 * Real.exp (-L)) := by ring
    _ ≤ 1 / ((T : ℝ) + 1) := h

section Generic

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] [DecidableEq ι] (P : ParD n ι)

open Classical in
/-- The averaged probability of an event implied by P0257's `FitAll` on every coin prefix is at most `FitAll`'s
(round coins only, for fixed sampling/filter bits). -/
theorem prob_le_fitAll (hL : P.IsLaw) {T : ℕ} (ℓ : LossSeq n) (rc₀ : RC P) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (G : (Fin T → RC P) → Prop) [DecidablePred G]
    (hG : ∀ rc, Pool.P0257.FitAll P T ℓ rc₀ ωs φ rc → G rc) :
    ∑ rc : Fin T → RC P, Pool.P0202.pw (wR P) rc * (if G rc then 0 else 1) ≤
      ∑ rc : Fin T → RC P, Pool.P0202.pw (wR P) rc *
        (if Pool.P0257.FitAll P T ℓ rc₀ ωs φ rc then 0 else 1) := by
  refine Finset.sum_le_sum fun rc _ => mul_le_mul_of_nonneg_left ?_ (Pool.P0228.pw_nonneg P hL rc)
  by_cases hF : Pool.P0257.FitAll P T ℓ rc₀ ωs φ rc
  · rw [if_pos (hG rc hF), if_pos hF]
  · rw [if_neg hF]; split_ifs <;> norm_num

variable {T Lt : ℕ} {ps q : ℝ}

/-- The sampling/filter law of P0091 (horizon `T`, `Lt` clock levels) is a probability weight. -/
theorem wtv_nonneg' (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ω2 : Pool.P0082.SlotC T P.D Lt P.K × ι → Bool) :
    0 ≤ Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 := by
  refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) ω2
  · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [hps.1, hq0]
  · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [hps.2, hq1]

open Classical in
/-- **The probing failure term (P0246's `badTermP`, used by P0263's `regret_le_absorbedS`), averaged over the
arrays.** If `B` bounds P0257's averaged `P(¬FitAll)`, then
`E_arr[badTermP] ≤ B + |ι|·2(T+1)²e^{−L} + 2(T+1)²e^{−L} + E_arr[P(¬AlgOK)]` (the budgets `v`, `r` may depend on the
array). -/
theorem badTermP_avg (hL : P.IsLaw) (ℓ : LossSeq n) (rc₀ : RC P) (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (L : ℝ) (ρ₀ c : ℝ)
    (v : (Pool.P0082.SlotC T P.D Lt P.K × ι → Bool) → (ℕ → RC P) → ℕ → ℝ)
    (r : (Pool.P0082.SlotC T P.D Lt P.K × ι → Bool) → (ℕ → RC P) → ι → ℕ → ℝ) (B : ℝ)
    (hB : ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
      ∑ rc : Fin T → RC P, Pool.P0202.pw (wR P) rc *
        (if Pool.P0257.FitAll P T ℓ rc₀ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc
          then 0 else 1) ≤ B) :
    ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
      Pool.P0246.badTermP P ℓ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc₀ T L
        (v ω2) ρ₀ c (r ω2) ≤
    B + (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) +
      ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
        ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
          (if Pool.P0228.AlgOK P ℓ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) T
              (v ω2 (Pool.P0210.extR P rc₀ ω)) ρ₀ c (r ω2 (Pool.P0210.extR P rc₀ ω)) (Pool.P0210.extR P rc₀ ω)
            then 0 else 1) := by
  set w := fun (ω2 : Pool.P0082.SlotC T P.D Lt P.K × ι → Bool) => Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2
  have hw0 : ∀ ω2, 0 ≤ w ω2 := wtv_nonneg' P hps hq0 hq1
  have hw1 : ∑ ω2, w ω2 = 1 := Pool.P0048.sum_wtv _
  set E := Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)
    with hE
  have hpt : ∀ ω2, Pool.P0246.badTermP P ℓ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2)
      rc₀ T L (v ω2) ρ₀ c (r ω2) ≤
      ((∑ rc : Fin T → RC P, Pool.P0202.pw (wR P) rc *
        (if Pool.P0257.FitAll P T ℓ rc₀ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc
          then 0 else 1)) +
        ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
          (if Pool.P0228.AlgOK P ℓ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) T
              (v ω2 (Pool.P0210.extR P rc₀ ω)) ρ₀ c (r ω2 (Pool.P0210.extR P rc₀ ω)) (Pool.P0210.extR P rc₀ ω)
            then 0 else 1)) + E := by
    intro ω2
    have hF := prob_le_fitAll P hL ℓ rc₀ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2)
      (fun rc => ∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ rc) (Pool.P0082.ωsC P.E T P.D Lt P.K ω2)
        (Pool.P0082.φC T P.D Lt P.K ω2) t)) (fun rc h => h.1)
    unfold Pool.P0246.badTermP
    linarith [hE]
  have h := avg_le w _ _ E hw0 hw1 hpt
  simp only [mul_add, Finset.sum_add_distrib] at h
  linarith

end Generic

section Ovf

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι)

open Classical in
/-- **`badTermP_avg` with P0257's overflow bound plugged in** (`hB := P0257.sum_not_fitAll_le`): under P0185/P0257's
hypotheses (entry-order layout, P0185's slot condition `hsl` in every thread block, P0221's merge/sampling
conditions), `E_arr[badTermP] ≤ (T·D·δs + T·D·(Lt+1)·K·delta) + exponential terms + E_arr[P(¬AlgOK)]`. -/
theorem badTermP_avg_ovf (hlay : P.lay = sortLay P.sl) (hL : P.IsLaw) (hN : 0 < P.N) {T Lt : ℕ}
    (ℓ : LossSeq n) (rc₀ : RC P) {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hE : Monotone P.E) (hB : BtHyp P.D P.Bt) (hLv : 0 < P.Lv)
    (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ P.xr j) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hR : 1 ≤ P.R) (hT : 1 / xmin * T ≤ 2 ^ (P.R - 1) * P.θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * P.R ≤ M0)
    (hk : 4 * P.R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * P.R))
    (hlevLt : ∀ a < T, ∀ r < P.D, P.lev r a ≤ Lt) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < T → r < P.D →
      ∑ F ∈ (Finset.univ.filter fun c => P.E c = a ∧ P.thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => P.E c = a ∧ P.thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S')
    (hρS : (1 - 1 / (4 * P.R : ℝ)) ^ P.K * ((S' : ℝ) + (s0 + P.D * P.Lv * S')) ≤ S')
    (hsl : ∀ j, (P.D : ℝ) * ((s0 + P.D * P.Lv * S') + (P.Lv - 1 : ℕ) * S') + P.D * s0 + 1 ≤ P.sl j)
    (L ρ₀ c : ℝ) (v : (Pool.P0082.SlotC T P.D Lt P.K × ι → Bool) → (ℕ → RC P) → ℕ → ℝ)
    (r : (Pool.P0082.SlotC T P.D Lt P.K × ι → Bool) → (ℕ → RC P) → ι → ℕ → ℝ) :
    ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
      Pool.P0246.badTermP P ℓ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc₀ T L
        (v ω2) ρ₀ c (r ω2) ≤
    (T * P.D * δs + T * P.D * (Lt + 1) * P.K * Pool.P0042.delta (Fintype.card ι) q P.R kk M0) +
      (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) +
      ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
        ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
          (if Pool.P0228.AlgOK P ℓ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) T
              (v ω2 (Pool.P0210.extR P rc₀ ω)) ρ₀ c (r ω2 (Pool.P0210.extR P rc₀ ω)) (Pool.P0210.extR P rc₀ ω)
            then 0 else 1) :=
  badTermP_avg P hL ℓ rc₀ hps hq0 hq1 L ρ₀ c v r _
    (Pool.P0257.sum_not_fitAll_le P hlay hL hN ℓ rc₀ hps hq0 hq1 hE hB hLv hlev hxmin hx hBm hR hT M0 kk hM0 hk hp
      hlevLt s0 δs hs S' hM0S hρS hsl)


end Ovf

section Twin

variable {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι]
  (P : ParD n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (S KM : ℕ)

local notation "QG" => Pool.P0236.PG P η ε L N G γ wE
local notation "TW" => Pool.P0236.withTwin P η ε L N G γ wE S KM

open Classical in
/-- **ALG's interval guarantees for the finite twin, averaged over the arrays** (P0253's `prob_not_algOK_twin_alg`
with P0243's budgets): if `B` bounds P0257's averaged `P(¬FitAll)` for the self-rounding process `QG` (the twin has the
same round-coin weights), then `E_arr[P(¬AlgOK_twin)] ≤ (|ι|+2)(T+1)²e^{−Lc} + B`. Both `hη : 0 ≤ η` and `hη' : 0 < η`
are P0253's hypotheses (the first is implied by the second and kept only to pass P0253's argument list). -/
theorem algOK_twin_avg (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (hG : 1 ≤ G)
    (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 ≤ η)
    (hS : (∑ j : Fin P.D, (P.sl j : ℝ)) + 1 ≤ S) (hL : (QG).IsLaw) (hN : 0 < (QG).N)
    (hη' : 0 < η) (hwE' : P.wE = wE) {T Lt : ℕ} (hTL : T ≤ 2 ^ L) (hTK : T ≤ KM) (ℓ : LossSeq n)
    (rc₀ : RC (TW)) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (Lc : ℝ) {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) (B : ℝ)
    (hB : ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QG).D) (Lt := Lt) (K := (QG).K) ps q) ω2 *
      ∑ rc : Fin T → RC (QG), Pool.P0202.pw (wR (QG)) rc *
        (if Pool.P0257.FitAll (QG) T ℓ rc₀ (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2)
            (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc then 0 else 1) ≤ B) :
    ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QG).D) (Lt := Lt) (K := (QG).K) ps q) ω2 *
      ∑ ω : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) ω *
        (if Pool.P0228.AlgOK (TW) ℓ (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2)
            (Pool.P0082.φC T (QG).D Lt (QG).K ω2) T
            (Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ
              (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2) (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc₀ T κ
              (Pool.P0210.extR (TW) rc₀ ω))
            (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
            (Pool.P0243.rOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ
              (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2) (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc₀ T ε κ Lc
              (Pool.P0210.extR (TW) rc₀ ω))
            (Pool.P0210.extR (TW) rc₀ ω) then 0 else 1) ≤
      ((Fintype.card ι : ℝ) + 2) * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + B := by
  have hw0 : ∀ ω2 : Pool.P0082.SlotC T (QG).D Lt (QG).K × ι → Bool,
      0 ≤ Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QG).D) (Lt := Lt) (K := (QG).K) ps q) ω2 :=
    wtv_nonneg' (QG) hps hq0 hq1
  have hw1 : ∑ ω2 : Pool.P0082.SlotC T (QG).D Lt (QG).K × ι → Bool,
      Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QG).D) (Lt := Lt) (K := (QG).K) ps q) ω2 = 1 :=
    Pool.P0048.sum_wtv _
  have hpt := fun (ω2 : Pool.P0082.SlotC T (QG).D Lt (QG).K × ι → Bool) => (Pool.P0253.prob_not_algOK_twin_alg P η ε L N G γ wE S KM ℓ
    (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2) (Pool.P0082.φC T (QG).D Lt (QG).K ω2) hD hLv hlev hG hγ hwE hε hη
    hS hL hN hη' hwE' T hTL hTK rc₀ hκ0 hκ1 Lc).trans
    ((add_le_add_right (prob_le_fitAll (T := T) (QG) hL ℓ rc₀ (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2)
      (Pool.P0082.φC T (QG).D Lt (QG).K ω2) _ (fun rc h => h.1)) _).trans (le_of_eq (add_comm _ _)))
  have h := avg_le _ _ _ _ hw0 hw1 hpt
  exact (h.trans (add_le_add hB le_rfl)).trans_eq (add_comm _ _)

open Classical in
/-- **The averaged probing failure term of the finite twin, fully bounded** (the composition of `badTermP_avg` at
`P := TW` with P0243's budgets `vOK`, `ρOK`, `c = 0`, `rOK`, and `algOK_twin_avg`): with `B₁` a bound on the averaged
`P(¬FitAll)` of the twin `TW` and `B₂` one for the self-rounding process `QG` (both from P0257's `sum_not_fitAll_le`
under its hypotheses),
`E_arr[badTermP_TW] ≤ B₁ + (|ι|·2(T+1)²e^{−L} + 2(T+1)²e^{−L}) + ((|ι|+2)(T+1)²e^{−Lc} + B₂)`. -/
theorem badTermP_twin_avg (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (hG : 1 ≤ G)
    (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 ≤ η)
    (hS : (∑ j : Fin P.D, (P.sl j : ℝ)) + 1 ≤ S) (hL : (QG).IsLaw) (hN : 0 < (QG).N)
    (hη' : 0 < η) (hwE' : P.wE = wE) {T Lt : ℕ} (hTL : T ≤ 2 ^ L) (hTK : T ≤ KM) (ℓ : LossSeq n)
    (rc₀ : RC (TW)) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (Lp Lc : ℝ) {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (B₁ B₂ : ℝ)
    (hB₁ : ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QG).D) (Lt := Lt) (K := (QG).K) ps q) ω2 *
      ∑ rc : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) rc *
        (if Pool.P0257.FitAll (TW) T ℓ rc₀ (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2)
            (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc then 0 else 1) ≤ B₁)
    (hB₂ : ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QG).D) (Lt := Lt) (K := (QG).K) ps q) ω2 *
      ∑ rc : Fin T → RC (QG), Pool.P0202.pw (wR (QG)) rc *
        (if Pool.P0257.FitAll (QG) T ℓ rc₀ (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2)
            (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc then 0 else 1) ≤ B₂) :
    ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QG).D) (Lt := Lt) (K := (QG).K) ps q) ω2 *
      Pool.P0246.badTermP (TW) ℓ (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2)
        (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc₀ T Lp
        (Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ
          (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2) (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc₀ T κ)
        (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
        (Pool.P0243.rOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ
          (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2) (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc₀ T ε κ Lc) ≤
      B₁ + (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lp)) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lp)) +
        (((Fintype.card ι : ℝ) + 2) * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + B₂) := by
  have h1 := badTermP_avg (TW) (T := T) (Lt := Lt) hL ℓ rc₀ hps hq0 hq1 Lp
    (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
    (fun ω2 => Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ
          (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2) (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc₀ T κ)
    (fun ω2 => Pool.P0243.rOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ
          (Pool.P0082.ωsC (QG).E T (QG).D Lt (QG).K ω2) (Pool.P0082.φC T (QG).D Lt (QG).K ω2) rc₀ T ε κ Lc)
    B₁ hB₁
  have h2 := algOK_twin_avg P η ε L N G γ wE S KM hD hLv hlev hG hγ hwE hε hη hS hL hN hη' hwE' (Lt := Lt) hTL hTK
    ℓ rc₀ hκ0 hκ1 Lc hps hq0 hq1 B₂ hB₂
  exact h1.trans (add_le_add le_rfl h2)

end Twin

end Pool.P0276
