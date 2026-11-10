import Pool.P0253.Twin
import Pool.P0246.AbsorbP
import Pool.P0251.Fits
import Pool.P0245.Glue

/-!
# The bad-event term of P0246's machine bound for the finite-twin ALG, with the self-rounding ALG's budgets
-/

namespace Pool.P0277

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0212 Pool.P0236

section Twin

variable {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι]
  (P : ParD n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (S KM : ℕ)

local notation "QG" => Pool.P0236.PG P η ε L N G γ wE
local notation "TW" => Pool.P0236.withTwin P η ε L N G γ wE S KM

variable (ℓ : LossSeq n) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (Pool.P0236.PG P η ε L N G γ wE).K → ι → Bool)

open Classical in
/-- The fit-failure probability on the twin's coin paths is the self-rounding ALG's (same weights, same pools). -/
theorem notFits_twin_eq (T : ℕ) (rc₀ : RC (TW)) :
    ∑ ω : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) ω *
      (if ∀ t < T, Pool.P0176.Fits (TW).Lv (TW).sl (sp (TW) ℓ (Pool.P0210.extR (TW) rc₀ ω) ωs φ t) then 0 else 1) =
    ∑ ω : Fin T → RC (QG), Pool.P0202.pw (wR (QG)) ω *
      (if ∀ t < T, Pool.P0176.Fits (QG).Lv (QG).sl (sp (QG) ℓ (Pool.P0210.extR (QG) rc₀ ω) ωs φ t) then 0 else 1) := by
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Pool.P0253.pw_twin P η ε L N G γ wE S KM ω]
  have hsp : ∀ t, sp (TW) ℓ (Pool.P0210.extR (TW) rc₀ ω) ωs φ t = sp (QG) ℓ (Pool.P0210.extR (QG) rc₀ ω) ωs φ t :=
    fun t => Pool.P0253.sp_twin P η ε L N G γ wE S KM ℓ ωs φ _ t
  simp only [hsp]
  rfl

variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
  (hG : 0 < G) (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 ≤ η)
include hD hLv hlev hG hγ hwE hε hη

open Classical in
/-- **P0246's bad term for the finite twin with the self-rounding ALG's budgets** (P0243's `vOK`, `ρOK`, `rOK` with
`δ = ε`, `c = 0`): at most twice the fit-failure probability plus the concentration tails,
`badTermP ≤ 2·P(¬fits) + |ι|·2(T+1)²e^{−Ls} + 2(T+1)²e^{−Ls} + (|ι|+2)(T+1)²e^{−Lc}` (P0253's
`prob_not_algOK_twin_alg`), for `Σ_j sl_j + 1 ≤ S`. -/
theorem badTermP_twin_le (hS : (∑ j : Fin P.D, (P.sl j : ℝ)) + 1 ≤ S) (hL : (QG).IsLaw) (hN : 0 < (QG).N)
    (hη' : 0 < η) (hwE' : P.wE = wE) (T : ℕ) (hTL : T ≤ 2 ^ L) (hTK : T ≤ KM) (rc₀ : RC (TW)) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (Ls Lc : ℝ) :
    Pool.P0246.badTermP (TW) ℓ ωs φ rc₀ T Ls
        (Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T κ)
        (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
        (Pool.P0243.rOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T ε κ Lc) ≤
      2 * ∑ ω : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) ω *
        (if ∀ t < T, Pool.P0176.Fits (TW).Lv (TW).sl (sp (TW) ℓ (Pool.P0210.extR (TW) rc₀ ω) ωs φ t) then 0 else 1)
      + Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls)) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls)
      + ((Fintype.card ι : ℝ) + 2) * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) := by
  have h := Pool.P0253.prob_not_algOK_twin_alg P η ε L N G γ wE S KM ℓ ωs φ hD hLv hlev hG hγ hwE hε hη hS hL hN
    hη' hwE' T hTL hTK rc₀ hκ0 hκ1 Lc
  rw [← notFits_twin_eq P η ε L N G γ wE S KM ℓ ωs φ T rc₀] at h
  unfold Pool.P0246.badTermP
  linarith

end Twin

section Arr

open Pool.P0201 Pool.P0206 Pool.P0245

attribute [local instance] Pool.P0082.coinFintype

variable {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι]
  (M0 : MPar n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (KM : ℕ) [NeZero N]

local notation "MT" => mTwin M0 η ε L N G γ wE KM


open Classical in
/-- **The array average of P0246's bad term for P0245's finite-twin machine** `mTwin`, with the self-rounding ALG's
budgets read with the array's sampling/filter bits: at most `2·(T·D·δs + T·D·(Lf+1)·K·delta)` (P0251, the fit
failure counted twice: once in `badTermP`, once through P0253's `AlgOK` transfer) plus the concentration tails
`|ι|·2(T+1)²e^{−Ls} + 2(T+1)²e^{−Ls} + (|ι|+2)(T+1)²e^{−Lc}`. Hypotheses: P0253's (with `S = Ns + 1`, i.e.
`Σ_j sl_j ≤ Ns`) and P0251's (entry-order layout, P0185's slot condition `hsl`). -/
theorem exp_badTermP_twin (hD : 0 < M0.P.D) (hLv : 0 < M0.P.Lv) (hlev : ∀ r a, M0.P.lev r a + 1 < M0.P.Lv)
    (hG : 0 < G) (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 < η) (hwE' : M0.P.wE = wE)
    (hS : (∑ j : Fin M0.P.D, (M0.P.sl j : ℝ)) ≤ M0.Ns) (hL : (MT).P.IsLaw) {T : ℕ} (hTL : T ≤ 2 ^ L)
    (hTK : T ≤ KM) (ℓ : LossSeq n) (rc₀ : RC (MT).P) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (Ls Lc : ℝ)
    (hlay : (MT).P.lay = Pool.P0176.sortLay (MT).P.sl) (hE : Monotone (MT).P.E) (hB : Pool.P0065.BtHyp (MT).P.D (MT).P.Bt)
    {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ (MT).P.xr j) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hR : 1 ≤ (MT).P.R) (hT : 1 / xmin * T ≤ 2 ^ ((MT).P.R - 1) * (MT).P.θ) (M00 : ℝ) (kk : ℕ)
    (hM0 : 16 * (MT).P.R ≤ M00) (hk : 4 * (MT).P.R * kk ≤ M00) (hp : (MT).q * (Real.exp 1 - 1) ≤ 1 / (32 * (MT).P.R))
    (hlevLt : ∀ a < T, ∀ r < (MT).P.D, (MT).P.lev r a ≤ (MT).Lf) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < T → r < (MT).P.D →
      ∑ F ∈ (Finset.univ.filter fun c => (MT).P.E c = a ∧ (MT).P.thr0 c = r).powerset,
        (MT).ps ^ F.card * (1 - (MT).ps) ^ ((Finset.univ.filter fun c => (MT).P.E c = a ∧ (MT).P.thr0 c = r).card -
          F.card) * (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M00 ≤ S')
    (hρS : (1 - 1 / (4 * (MT).P.R : ℝ)) ^ (MT).P.K * ((S' : ℝ) + (s0 + (MT).P.D * (MT).P.Lv * S')) ≤ S')
    (hsl : ∀ j, ((MT).P.D : ℝ) * ((s0 + (MT).P.D * (MT).P.Lv * S') + ((MT).P.Lv - 1 : ℕ) * S') + (MT).P.D * s0 + 1 ≤
      (MT).P.sl j) :
    ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr *
        Pool.P0246.badTermP (MT).P (sh ℓ) (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr)
          (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr) rc₀ T Ls
          (Pool.P0243.vOK M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) (sh ℓ)
            (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr)
            rc₀ T κ)
          (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
          (Pool.P0243.rOK M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) (sh ℓ)
            (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr)
            rc₀ T ε κ Lc) ≤
      2 * (T * (MT).P.D * δs + T * (MT).P.D * ((MT).Lf + 1) * (MT).P.K *
          Pool.P0042.delta (Fintype.card ι) (MT).q (MT).P.R kk M00)
      + Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls)) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls)
      + ((Fintype.card ι : ℝ) + 2) * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNQ : 0 < (Pool.P0236.PG M0.P η ε L N G γ wE).N := hN
  have hLQ : (Pool.P0236.PG M0.P η ε L N G γ wE).IsLaw := hL
  have hS' : (∑ j : Fin M0.P.D, (M0.P.sl j : ℝ)) + 1 ≤ ((M0.Ns + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hw0 : ∀ arr : Pool.P0116.Arr (pp (MT)) T → Bool, 0 ≤ Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr := by
    intro arr
    refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) arr
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [(MT).hps.1, (MT).hq.1]
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [(MT).hps.2, (MT).hq.2]
  have hw1 : ∑ arr : Pool.P0116.Arr (pp (MT)) T → Bool, Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr = 1 :=
    Pool.P0048.sum_wtv _
  have hF := Pool.P0251.sum_notFits_le (m := MT) hlay ℓ rc₀ hL hN hE hB hLv hlev hxmin hx hBm hR hT M00 kk hM0 hk hp
    hlevLt s0 δs hs S' hM0S hρS hsl
  set C := Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls)) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls)
      + ((Fintype.card ι : ℝ) + 2) * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc))
  have hpt : ∀ arr : Pool.P0116.Arr (pp (MT)) T → Bool,
      Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr *
        Pool.P0246.badTermP (MT).P (sh ℓ) (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr)
          (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr) rc₀ T Ls
          (Pool.P0243.vOK M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) (sh ℓ)
            (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr)
            rc₀ T κ)
          (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
          (Pool.P0243.rOK M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) (sh ℓ)
            (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr)
            rc₀ T ε κ Lc) ≤
      2 * (Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr *
        ∑ ω : Fin T → RC (MT).P, Pool.P0202.pw (wR (MT).P) ω *
          (if ∀ t < T, Pool.P0176.Fits (MT).P.Lv (MT).P.sl (sp (MT).P (sh ℓ) (Pool.P0210.extR (MT).P rc₀ ω)
              (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr) t)
            then 0 else 1))
      + Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr * C := by
    intro arr
    have h : Pool.P0246.badTermP (MT).P (sh ℓ) (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr)
          (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr) rc₀ T Ls
          (Pool.P0243.vOK M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) (sh ℓ)
            (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr)
            rc₀ T κ)
          (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
          (Pool.P0243.rOK M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) (sh ℓ)
            (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr)
            rc₀ T ε κ Lc) ≤
        2 * ∑ ω : Fin T → RC (MT).P, Pool.P0202.pw (wR (MT).P) ω *
          (if ∀ t < T, Pool.P0176.Fits (MT).P.Lv (MT).P.sl (sp (MT).P (sh ℓ) (Pool.P0210.extR (MT).P rc₀ ω)
              (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr) t)
            then 0 else 1) + C := by
      have h0 := badTermP_twin_le M0.P η ε L N G γ wE (M0.Ns + 1) KM (sh ℓ)
        (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr)
        hD hLv hlev hG hγ hwE hε hη.le hS' hLQ hNQ hη hwE' T hTL hTK rc₀ hκ0 hκ1 Ls Lc
      refine le_trans h0 (le_of_eq ?_)
      simp only [C, add_assoc]
      rfl
    have := mul_le_mul_of_nonneg_left h (hw0 arr)
    linarith
  have hsum := Finset.sum_le_sum fun arr (_ : arr ∈ Finset.univ) => hpt arr
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hw1, one_mul] at hsum
  simp only [C] at hsum
  have hF' : ∑ arr : Pool.P0116.Arr (pp (MT)) T → Bool, Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr *
        ∑ ω : Fin T → RC (MT).P, Pool.P0202.pw (wR (MT).P) ω *
          (if ∀ t < T, Pool.P0176.Fits (MT).P.Lv (MT).P.sl (sp (MT).P (sh ℓ) (Pool.P0210.extR (MT).P rc₀ ω)
              (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr) t)
            then 0 else 1) ≤
      T * (MT).P.D * δs + T * (MT).P.D * ((MT).Lf + 1) * (MT).P.K *
          Pool.P0042.delta (Fintype.card ι) (MT).q (MT).P.R kk M00 := hF
  set Bd := ∑ arr : Pool.P0116.Arr (pp (MT)) T → Bool, Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr *
        ∑ ω : Fin T → RC (MT).P, Pool.P0202.pw (wR (MT).P) ω *
          (if ∀ t < T, Pool.P0176.Fits (MT).P.Lv (MT).P.sl (sp (MT).P (sh ℓ) (Pool.P0210.extR (MT).P rc₀ ω)
              (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr) t)
            then 0 else 1) with hBd
  refine le_trans hsum ?_
  linarith

end Arr

end Pool.P0277
