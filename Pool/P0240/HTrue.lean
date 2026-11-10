import Pool.P0231.IXD
import Pool.P0227.HTrue
import Pool.P0023.Concentration

/-!
# P0186's `htrue` for P0225's generalized ALG `withAlgG` on P0194's round coins (variance-adaptive, constant `Ψ = Lc/κ`,
horizon `T`)

This is P0227 with P0212's `withAlg` replaced by P0225's `withAlgG` (perturbation `ρG σ V ch bit` reading the round's
draw and loss bit, e.g. P0225's self-rounding `ρ⋆` of the finite-state twin), and P0220's objects by P0231's. With a
draw-blind rule it is P0227 (`Tests.lean`: `DT` agrees by `rfl`).

ALG's IX-data loss `ARc` (P0225's `AR` in the coin model) has conditional mean `mA` and second moment `vA`. The
lower-tail increment `DT = mA − ARc − κ·vA` has `E[exp(κ·DT)] ≤ 1` (`DT_step`, `0 < κ ≤ 1`), so P0149's one-sided
interval event fails w.p. `≤ (T+1)²e^{−Lc}` (`prob_not_goodHT`). On it, on every `[a, b) ⊆ [0, T)`:
`Σ aPol ≤ Σ (Pool.P0225.AR + slack) + Lc/κ` (`htrue_run`), with the predictable `slack = (aPol − mA) + κ·vA`, bounded by
`s·(γ + 2/N) + wE/G + κ·s·(1/wE + 1/(4N·wE·γ))` (`slack_le`), `s` = support size of ALG's marginal (`supp_le`).
-/

open Finset Real Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0212 Pool.P0092 Pool.P0139 Pool.P0149 Pool.P0231
open Pool.P0227 (sum_mul_ixA ixA_nonneg ixA_le_den supp pmarg_le_one supp_le)

namespace Pool.P0240

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (Pool.P0225.withAlgG P η L N G γ wE ρG).K → ι → Bool)
  (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

local notation "PA" => Pool.P0225.withAlgG P η L N G γ wE ρG

/-- ALG's state on a coin prefix. -/
noncomputable abbrev σs (s : ℕ) (ω' : Fin s → RC PA) : AState ι :=
  sAA P η L N G γ wE ρG ℓ ωs φ (Pool.P0203.extD PA rc0 ω') s

/-- The active set on a coin prefix. -/
noncomputable abbrev Vs (s : ℕ) (ω' : Fin s → RC PA) : Finset ι :=
  active PA ℓ (Pool.P0203.extD PA rc0 ω') ωs φ s

/-- The loss bit of choice `ch` in round `s` with BASE's action coin `y` (a copy's arm, or BASE's action). -/
noncomputable def bitc (s : ℕ) (ω' : Fin s → RC PA) (ch : Option ι) (y : (PA).AB.Y) : Bool :=
  ℓ s (match ch with
    | some x => P.arm x
    | none => (PA).AB.act 0 (sB PA ℓ (Pool.P0203.extD PA rc0 ω') s) y)

/-- ALG's IX-data loss in round `s` with coin `z`: on an exploitation round, its Hedge marginal against the round's IX
estimates (P0225's `AR`), else `0`. -/
noncomputable def ARc (s : ℕ) (ω' : Fin s → RC PA) (z : RC PA) : ℝ :=
  if isE PA z.1 = true then
    ∑ f, pmarg η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
      ixA η L N G γ wE (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
        (drawQ P η L N G γ wE ρG (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') z.2.1)
        (bitc P η L N G γ wE ρG ℓ rc0 s ω'
          (drawQ P η L N G γ wE ρG (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
            z.2.1) z.2.2.1) f
  else 0

/-- Its conditional mean. -/
noncomputable def mA (s : ℕ) (ω' : Fin s → RC PA) : ℝ :=
  ∑ z, wR PA z * ARc P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z

/-- Its conditional second moment. -/
noncomputable def vA (s : ℕ) (ω' : Fin s → RC PA) : ℝ :=
  ∑ z, wR PA z * ARc P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z ^ 2

/-- The increment of the lower-tail exponential supermartingale: `mean − value − κ·second moment`, before learner time
`2^L` (`0` after). -/
noncomputable def DT (κ : ℝ) (s : ℕ) (ω : Fin (s + 1) → RC PA) : ℝ :=
  if s < 2 ^ L then
    mA P η L N G γ wE ρG ℓ ωs φ rc0 s (Fin.init ω) - ARc P η L N G γ wE ρG ℓ ωs φ rc0 s (Fin.init ω) (ω (Fin.last s)) -
      κ * vA P η L N G γ wE ρG ℓ ωs φ rc0 s (Fin.init ω)
  else 0


/-! ### Elementary facts -/

theorem σs_k_le (s : ℕ) (ω' : Fin s → RC PA) : (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω').k ≤ s := by
  unfold σs sAA
  rw [Pool.P0225.sA_k P η L N G γ wE ρG ℓ (Pool.P0203.extD PA rc0 ω') ωs φ s]
  unfold Pool.P0225.kE
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- **The draw law** (before learner time `2^L`): averaging over the draw coin is integrating against `p̃`. -/
theorem sum_draw (hN : 0 < (PA).N) (σ : AState ι) (V : Finset ι) (hk : σ.k < 2 ^ L) (F : Option ι → ℝ) :
    ∑ d : Fin (PA).N, (1 / ((PA).N : ℝ)) * F (drawQ P η L N G γ wE ρG σ V d) =
      ∑ f, ptA η L N σ V f * F f := by
  classical
  have hN0 : 0 < N := hN
  have e : ∀ d : Fin (PA).N, (1 / ((PA).N : ℝ)) * F (drawQ P η L N G γ wE ρG σ V d) =
      ∑ f, (1 / ((PA).N : ℝ)) * (if drawQ P η L N G γ wE ρG σ V d = f then F f else 0) := by
    intro d
    rw [Finset.sum_eq_single (drawQ P η L N G γ wE ρG σ V d)]
    · rw [if_pos rfl]
    · intro f _ hf; rw [if_neg (Ne.symm hf), mul_zero]
    · simp
  rw [Finset.sum_congr rfl fun d _ => e d, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hdraw := Pool.P0179.prob_draw (N := N) (b := (none : Option ι)) hN0 (pmarg_nonneg η L σ V)
    (pmarg_sum η L σ V hk) f
  have h1 : ∑ d : Fin (PA).N, (1 / ((PA).N : ℝ)) * (if drawQ P η L N G γ wE ρG σ V d = f then F f else 0) =
      (((univ.filter fun d : Fin N => drawA η L N σ V d = f).card : ℝ) / N) * F f := by
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    show (1 / (N : ℝ)) * (if drawA η L N σ V d = f then F f else 0) = _
    split_ifs <;> simp [div_eq_mul_inv]
  rw [h1]
  unfold ptA
  rw [← hdraw]
  have hfil : (univ.filter fun d : Fin N => drawA η L N σ V d = f) =
      (univ.filter fun d : Fin N => Pool.P0179.draw (N := N) (b := (none : Option ι)) (pmarg_nonneg η L σ V)
        (pmarg_sum η L σ V hk) d = f) := by
    ext d; simp only [Finset.mem_filter, Finset.mem_univ, true_and, drawA_eq η L N σ V hk]
  rw [hfil]

/-- The expected loss of choice `f` over BASE's action coin. -/
noncomputable def lbar (s : ℕ) (ω' : Fin s → RC PA) (f : Option ι) : ℝ :=
  ∑ y, ((PA).AB.μ y).toReal * ((bitc P η L N G γ wE ρG ℓ rc0 s ω' f y).toNat : ℝ)

theorem lbar_mem (s : ℕ) (ω' : Fin s → RC PA) (f : Option ι) :
    0 ≤ lbar P η L N G γ wE ρG ℓ rc0 s ω' f ∧ lbar P η L N G γ wE ρG ℓ rc0 s ω' f ≤ 1 := by
  have hμ : ∑ y, ((PA).AB.μ y).toReal = 1 := Pool.P0092.sum_toReal_one _
  have hb : ∀ y, ((bitc P η L N G γ wE ρG ℓ rc0 s ω' f y).toNat : ℝ) ≤ 1 := fun y => by
    cases bitc P η L N G γ wE ρG ℓ rc0 s ω' f y <;> simp
  constructor
  · exact Finset.sum_nonneg fun y _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  · calc lbar P η L N G γ wE ρG ℓ rc0 s ω' f ≤ ∑ y, ((PA).AB.μ y).toReal * 1 :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hb y) ENNReal.toReal_nonneg
      _ = 1 := by simp only [mul_one]; exact hμ

/-- **ALG's policy loss is `Σ p̃·ℓ̄`** (before learner time `2^L`). -/
theorem aPol_eq (hN : 0 < (PA).N) (s : ℕ) (ω' : Fin s → RC PA)
    (hk : (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    aPol PA ℓ ωs φ (Pool.P0203.extD PA rc0 ω') s =
      ∑ f, ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
        lbar P η L N G γ wE ρG ℓ rc0 s ω' f := by
  rw [← sum_draw P η L N G γ wE ρG hN _ _ hk]
  unfold aPol
  refine Finset.sum_congr rfl fun d _ => ?_
  congr 1
  norm_num


/-! ### Closed forms of the conditional mean and second moment -/

/-- The IX-data loss as a sum over experts with the exploitation and draw indicators. -/
theorem ARc_eq (s : ℕ) (ω' : Fin s → RC PA) (z : RC PA) :
    ARc P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z =
      ∑ f, (if isE PA z.1 = true then 1 else 0) *
        (if drawQ P η L N G γ wE ρG (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
          z.2.1 = f then 1 else 0) *
        (pmarg η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
          ixA η L N G γ wE (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f
            (bitc P η L N G γ wE ρG ℓ rc0 s ω' f z.2.2.1) f) := by
  unfold ARc
  split_ifs with hE
  · rw [sum_mul_ixA]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with hf
    · subst hf; ring
    · ring
  · simp

theorem ARc_sq (s : ℕ) (ω' : Fin s → RC PA) (z : RC PA) :
    ARc P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z ^ 2 =
      ∑ f, (if isE PA z.1 = true then 1 else 0) *
        (if drawQ P η L N G γ wE ρG (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
          z.2.1 = f then 1 else 0) *
        (pmarg η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
          ixA η L N G γ wE (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f
            (bitc P η L N G γ wE ρG ℓ rc0 s ω' f z.2.2.1) f) ^ 2 := by
  rw [ARc_eq]
  set ch := drawQ P η L N G γ wE ρG (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') z.2.1
  by_cases hE : isE PA z.1 = true
  · simp only [hE, if_true, one_mul, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp
  · simp [hE]

/-- **Conditional mean** (before learner time `2^L`): `E[ARc] = Σ_f p_f·wE·p̃_f·E_y[ixA_f]`. -/
theorem mA_eq (hN : 0 < (PA).N) (s : ℕ) (ω' : Fin s → RC PA)
    (hk : (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    mA P η L N G γ wE ρG ℓ ωs φ rc0 s ω' =
      ∑ f, (PA).wE * ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
        ∑ y, ((PA).AB.μ y).toReal *
          (pmarg η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
            ixA η L N G γ wE (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f
              (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f) := by
  unfold mA
  simp only [ARc_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h := Pool.P0220.sum_wR_exploit_factor PA
    (fun d => if drawQ P η L N G γ wE ρG (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
      d = f then (1 : ℝ) else 0)
    (fun y => pmarg η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
      ixA η L N G γ wE (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f
        (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f)
  rw [h]
  have hd := sum_draw P η L N G γ wE ρG hN (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
    (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') hk
    (fun g => if g = f then (1 : ℝ) else 0)
  have hpt : ∑ g, ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') g *
      (if g = f then (1 : ℝ) else 0) =
      ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f := by
    simp [mul_ite]
  rw [hpt] at hd
  rw [hd, Finset.mul_sum]

/-- **Conditional second moment** (before learner time `2^L`). -/
theorem vA_eq (hN : 0 < (PA).N) (s : ℕ) (ω' : Fin s → RC PA)
    (hk : (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    vA P η L N G γ wE ρG ℓ ωs φ rc0 s ω' =
      ∑ f, (PA).wE * ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
        ∑ y, ((PA).AB.μ y).toReal *
          (pmarg η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
            ixA η L N G γ wE (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f
              (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f) ^ 2 := by
  unfold vA
  simp only [ARc_sq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h := Pool.P0220.sum_wR_exploit_factor PA
    (fun d => if drawQ P η L N G γ wE ρG (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
      d = f then (1 : ℝ) else 0)
    (fun y => (pmarg η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
      ixA η L N G γ wE (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f
        (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f) ^ 2)
  rw [h]
  have hd := sum_draw P η L N G γ wE ρG hN (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
    (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') hk
    (fun g => if g = f then (1 : ℝ) else 0)
  have hpt : ∑ g, ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') g *
      (if g = f then (1 : ℝ) else 0) =
      ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f := by
    simp [mul_ite]
  rw [hpt] at hd
  rw [hd, Finset.mul_sum]


/-! ### Deterministic bounds (before learner time `2^L`, with `wE` = P0194's exploitation weight) -/

section Bounds

variable {P η L N G γ wE ρG ℓ ωs φ rc0}

/-- `E_y[ixA_f] ≤ ℓ̄_f/(wE·(p̃_f + γ))`. -/
theorem Ey_le (hwE0 : 0 < wE) (hγ : 0 < γ) (s : ℕ) (ω' : Fin s → RC PA) (f : Option ι) :
    ∑ y, ((PA).AB.μ y).toReal *
        ixA η L N G γ wE (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f
          (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f ≤
      lbar P η L N G γ wE ρG ℓ rc0 s ω' f /
        (wE * (ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f + γ)) := by
  unfold lbar
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (ixA_le_den η L N G γ wE hwE0 hγ _ _ f _) ENNReal.toReal_nonneg

/-- `E_y[ixA_f] ≥ ℓ̄_f/(wE·(p̃_f + γ)) − 1/G` for `G ≥ 1`. -/
theorem Ey_ge (hG : 1 ≤ G) (hwE0 : 0 < wE) (hγ : 0 < γ) (s : ℕ) (ω' : Fin s → RC PA) (f : Option ι) :
    lbar P η L N G γ wE ρG ℓ rc0 s ω' f /
        (wE * (ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f + γ)) -
      1 / G ≤
    ∑ y, ((PA).AB.μ y).toReal *
        ixA η L N G γ wE (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f
          (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f := by
  have hμ : ∑ y, ((PA).AB.μ y).toReal = 1 := Pool.P0092.sum_toReal_one _
  have hpt := Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι))
    (p := pmarg η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω')) f
  have hden : 0 < wE * (ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f + γ) :=
    mul_pos hwE0 (by unfold ptA; linarith)
  have e : lbar P η L N G γ wE ρG ℓ rc0 s ω' f /
        (wE * (ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f + γ)) -
      1 / G = ∑ y, ((PA).AB.μ y).toReal * (((bitc P η L N G γ wE ρG ℓ rc0 s ω' f y).toNat : ℝ) /
        (wE * (ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f + γ)) -
        1 / G) := by
    unfold lbar
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ, one_mul, Finset.sum_div, mul_div_assoc]
  rw [e]
  refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  exact (ixA_grid η L N G γ wE hG _ _ f _ hden).1


/-- `E[ARc] = Σ_f p_f·(wE·p̃_f·E_y[ixA_f])`. -/
theorem mA_eq' (hN : 0 < (PA).N) (hwE : P.wE = wE) (s : ℕ) (ω' : Fin s → RC PA)
    (hk : (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    mA P η L N G γ wE ρG ℓ ωs φ rc0 s ω' =
      ∑ f, pmarg η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
        (wE * ptA η L N (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f *
          ∑ y, ((PA).AB.μ y).toReal *
            ixA η L N G γ wE (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f
              (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f) := by
  rw [mA_eq P η L N G γ wE ρG ℓ ωs φ rc0 hN s ω' hk]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hw : (PA).wE = wE := hwE
  rw [hw]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

/-- **The conditional mean of ALG's IX-data loss is at most `1`.** -/
theorem mA_le_one (hN : 0 < (PA).N) (hwE : P.wE = wE) (hwE0 : 0 < wE) (hγ : 0 < γ) (s : ℕ) (ω' : Fin s → RC PA)
    (hk : (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    mA P η L N G γ wE ρG ℓ ωs φ rc0 s ω' ≤ 1 := by
  rw [mA_eq' hN hwE s ω' hk]
  set σ := σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω'
  set V := Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω'
  calc _ ≤ ∑ f, pmarg η L σ V f * 1 := by
        refine Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left ?_ (pmarg_nonneg η L σ V f)
        have hpt := Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι)) (p := pmarg η L σ V) f
        have hptA : 0 ≤ ptA η L N σ V f := hpt
        have hl := lbar_mem P η L N G γ wE ρG ℓ rc0 s ω' f
        have hE := Ey_le (P := P) (ℓ := ℓ) (ωs := ωs) (φ := φ) (rc0 := rc0) hwE0 hγ s ω' f
        have hden : 0 < ptA η L N σ V f + γ := by linarith
        calc wE * ptA η L N σ V f * _ ≤ wE * ptA η L N σ V f *
              (lbar P η L N G γ wE ρG ℓ rc0 s ω' f / (wE * (ptA η L N σ V f + γ))) :=
              mul_le_mul_of_nonneg_left hE (by positivity)
          _ = ptA η L N σ V f / (ptA η L N σ V f + γ) * lbar P η L N G γ wE ρG ℓ rc0 s ω' f := by
              field_simp
          _ ≤ 1 * 1 := by
              refine mul_le_mul ?_ hl.2 hl.1 zero_le_one
              rw [div_le_one hden]; linarith
          _ = 1 := by ring
    _ = 1 := by simp only [mul_one]; exact pmarg_sum η L σ V hk


/-- **IX bias and rounding of ALG**: `aPol − E[ARc] ≤ s·(γ + 2/N) + wE/G` with `s` = support size of ALG's marginal
(played-loss rounding `s/N`, IX bias `s(γ + 1/N)`, grid rounding `wE/G`). -/
theorem aPol_sub_mA_le (hN : 0 < (PA).N) (hwE : P.wE = wE) (hwE0 : 0 < wE) (hγ : 0 < γ) (hG : 1 ≤ G) (s : ℕ)
    (ω' : Fin s → RC PA) (hk : (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    aPol PA ℓ ωs φ (Pool.P0203.extD PA rc0 ω') s - mA P η L N G γ wE ρG ℓ ωs φ rc0 s ω' ≤
      supp η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') * (γ + 2 / N) +
        wE / G := by
  rw [aPol_eq P η L N G γ wE ρG ℓ ωs φ rc0 hN s ω' hk, mA_eq' hN hwE s ω' hk]
  set σ := σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω'
  set V := Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω'
  set lb := lbar P η L N G γ wE ρG ℓ rc0 s ω'
  have hN0 : 0 < N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hp0 := pmarg_nonneg η L σ V
  have hp1 := pmarg_sum η L σ V hk
  have hlb0 : ∀ f, 0 ≤ lb f := fun f => (lbar_mem P η L N G γ wE ρG ℓ rc0 s ω' f).1
  have hlb1 : ∀ f, lb f ≤ 1 := fun f => (lbar_mem P η L N G γ wE ρG ℓ rc0 s ω' f).2
  -- per-expert lower bound of the mean term
  have hterm : ∀ f, pmarg η L σ V f * (ptA η L N σ V f * lb f / (ptA η L N σ V f + γ)) -
      pmarg η L σ V f * (wE * ptA η L N σ V f / G) ≤
      pmarg η L σ V f * (wE * ptA η L N σ V f * ∑ y, ((PA).AB.μ y).toReal *
        ixA η L N G γ wE σ V f (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f) := by
    intro f
    have hpt : 0 ≤ ptA η L N σ V f := Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι)) (p := pmarg η L σ V) f
    have hE := Ey_ge (P := P) (ℓ := ℓ) (ωs := ωs) (φ := φ) (rc0 := rc0) hG hwE0 hγ s ω' f
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (hp0 f)
    have hden : 0 < ptA η L N σ V f + γ := by linarith
    have : wE * ptA η L N σ V f * (lb f / (wE * (ptA η L N σ V f + γ)) - 1 / G) =
        ptA η L N σ V f * lb f / (ptA η L N σ V f + γ) - wE * ptA η L N σ V f / G := by
      field_simp
    rw [← this]
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  have hmean := Finset.sum_le_sum fun f (_ : f ∈ univ) => hterm f
  rw [Finset.sum_sub_distrib] at hmean
  -- the three error terms
  have h1 := Pool.P0179.played_loss_le_supp (N := N) (b := (none : Option ι)) hN0 hp0 hp1 lb hlb0 hlb1
  have h2 := Pool.P0179.ix_bias_le_scaled (N := N) (b := (none : Option ι)) hN0 hp0 hp1 lb hlb0 hlb1 hγ
    (ρ := 1) one_pos
  have h3 : ∑ f, pmarg η L σ V f * (wE * ptA η L N σ V f / G) ≤ wE / G := by
    have hs := Pool.P0179.sum_pt (N := N) (b := (none : Option ι)) hN0 hp0 hp1
    calc ∑ f, pmarg η L σ V f * (wE * ptA η L N σ V f / G) ≤ ∑ f, 1 * (wE * ptA η L N σ V f / G) := by
          refine Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (pmarg_le_one σ V hk f) ?_
          have hpt : 0 ≤ ptA η L N σ V f :=
            Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι)) (p := pmarg η L σ V) f
          positivity
      _ = wE / G * ∑ f, ptA η L N σ V f := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun f _ => ?_; ring
      _ = wE / G := by unfold ptA; rw [hs, mul_one]
  have hsupp1 : ((((univ : Finset (Option ι)).erase none).filter fun i => pmarg η L σ V i ≠ 0).card : ℝ) ≤
      supp η L σ V := by
    unfold supp
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
  -- identity: Σ p ℓ − Σ p p̃ℓ/(p̃+γ) = Σ p ℓ γ/(p̃+γ)
  have hid : ∑ f, pmarg η L σ V f * lb f - ∑ f, pmarg η L σ V f * (ptA η L N σ V f * lb f / (ptA η L N σ V f + γ)) =
      ∑ f, pmarg η L σ V f * lb f * (γ / (1 * ptA η L N σ V f + γ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hpt : 0 ≤ ptA η L N σ V f := Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι)) (p := pmarg η L σ V) f
    have hden : 0 < ptA η L N σ V f + γ := by linarith
    rw [one_mul]
    field_simp
    ring
  have habs := (abs_le.1 h1).2
  have hs0 : (0 : ℝ) ≤ supp η L σ V := Nat.cast_nonneg _
  have e1 : ((((univ : Finset (Option ι)).erase none).filter fun i => pmarg η L σ V i ≠ 0).card : ℝ) / N ≤
      supp η L σ V / N := div_le_div_of_nonneg_right hsupp1 hNr.le
  have e2 : (supp η L σ V : ℝ) * (γ / 1 + 1 / N) = supp η L σ V * (γ + 1 / N) := by rw [div_one]
  unfold ptA at *
  unfold supp at *
  rw [e2] at h2
  have : (supp η L σ V : ℝ) * (γ + 2 / N) = supp η L σ V / N + supp η L σ V * (γ + 1 / N) := by
    field_simp; ring
  unfold supp at this
  rw [this]
  linarith


/-- **Second moment of ALG's IX-data loss**: `E[ARc²] ≤ s·(1/wE + 1/(4N·wE·γ))`. -/
theorem vA_le (hN : 0 < (PA).N) (hwE : P.wE = wE) (hwE0 : 0 < wE) (hγ : 0 < γ) (s : ℕ) (ω' : Fin s → RC PA)
    (hk : (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    vA P η L N G γ wE ρG ℓ ωs φ rc0 s ω' ≤
      supp η L (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω') *
        (1 / wE + 1 / (4 * N * (wE * γ))) := by
  rw [vA_eq P η L N G γ wE ρG ℓ ωs φ rc0 hN s ω' hk]
  set σ := σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω'
  set V := Vs P η L N G γ wE ρG ℓ ωs φ rc0 s ω'
  have hN0 : 0 < N := hN
  have hp0 := pmarg_nonneg η L σ V
  have hp1 := pmarg_sum η L σ V hk
  have hw : (PA).wE = wE := hwE
  have hμ : ∑ y, ((PA).AB.μ y).toReal = 1 := Pool.P0092.sum_toReal_one _
  have hsm := Pool.P0179.second_moment_le_scaled (N := N) (b := (none : Option ι)) hN0 hp0 hp1 (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) (fun _ => le_rfl) (mul_pos hwE0 hγ) hwE0
  refine le_trans ?_ hsm
  rw [hw]
  refine Finset.sum_le_sum fun f _ => ?_
  have hpt : 0 ≤ ptA η L N σ V f := Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι)) (p := pmarg η L σ V) f
  have hden : 0 < wE * (ptA η L N σ V f + γ) := mul_pos hwE0 (by linarith)
  have hpf1 : pmarg η L σ V f ≤ 1 := pmarg_le_one σ V hk f
  -- each squared estimate is at most `(p_f / (wE(p̃+γ)))²`
  have hy : ∀ y, (pmarg η L σ V f * ixA η L N G γ wE σ V f (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f) ^ 2 ≤
      (pmarg η L σ V f / (wE * (ptA η L N σ V f + γ))) ^ 2 := by
    intro y
    have h0 := ixA_nonneg η L N G γ wE σ V f (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f
    have h1 := ixA_le_den η L N G γ wE hwE0 hγ σ V f (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y)
    have hb : ((bitc P η L N G γ wE ρG ℓ rc0 s ω' f y).toNat : ℝ) ≤ 1 := by
      cases bitc P η L N G γ wE ρG ℓ rc0 s ω' f y <;> simp
    have h2 : ixA η L N G γ wE σ V f (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f ≤ 1 / (wE * (ptA η L N σ V f + γ)) :=
      h1.trans (div_le_div_of_nonneg_right hb hden.le)
    have h3 : pmarg η L σ V f * ixA η L N G γ wE σ V f (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f ≤
        pmarg η L σ V f / (wE * (ptA η L N σ V f + γ)) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left h2 (hp0 f)
    exact pow_le_pow_left₀ (mul_nonneg (hp0 f) h0) h3 2
  calc wE * ptA η L N σ V f * ∑ y, ((PA).AB.μ y).toReal *
        (pmarg η L σ V f * ixA η L N G γ wE σ V f (bitc P η L N G γ wE ρG ℓ rc0 s ω' f y) f) ^ 2
      ≤ wE * ptA η L N σ V f * ∑ y, ((PA).AB.μ y).toReal * (pmarg η L σ V f / (wE * (ptA η L N σ V f + γ))) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (hy y) ENNReal.toReal_nonneg) (by positivity)
    _ = pmarg η L σ V f ^ 2 * (wE * ptA η L N σ V f / (wE * ptA η L N σ V f + wE * γ) ^ 2) := by
        rw [← Finset.sum_mul, hμ, one_mul]
        field_simp
    _ ≤ pmarg η L σ V f * (fun _ => (1 : ℝ)) f ^ 2 *
          (wE * Pool.P0179.pt N none (pmarg η L σ V) f / (wE * Pool.P0179.pt N none (pmarg η L σ V) f + wE * γ) ^ 2) := by
        simp only [one_pow, mul_one]
        refine mul_le_mul_of_nonneg_right ?_ (by unfold ptA at hpt ⊢; positivity)
        nlinarith [hp0 f]


theorem ARc_nonneg (s : ℕ) (ω' : Fin s → RC PA) (z : RC PA) : 0 ≤ ARc P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z := by
  unfold ARc
  split_ifs
  · exact Finset.sum_nonneg fun f _ => mul_nonneg (pmarg_nonneg η L _ _ f) (ixA_nonneg η L N G γ wE _ _ _ _ f)
  · exact le_rfl

/-- **One-step exponential moment** of the lower-tail increment (`0 < κ ≤ 1`). -/
theorem DT_step (hL : (PA).IsLaw) (hN : 0 < (PA).N) (hwE : P.wE = wE) (hwE0 : 0 < wE) (hγ : 0 < γ) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (s : ℕ) (ω' : Fin s → RC PA) :
    ∑ z, (Pool.P0203.nuD PA hL hN z).toReal * exp (κ * DT P η L N G γ wE ρG ℓ ωs φ rc0 κ s (Fin.snoc ω' z)) ≤ 1 := by
  by_cases hs : s < 2 ^ L
  swap
  · simp only [DT, if_neg hs, mul_zero, exp_zero, mul_one]
    exact le_of_eq (Pool.P0092.sum_toReal_one _)
  have hk : (σs P η L N G γ wE ρG ℓ ωs φ rc0 s ω').k < 2 ^ L :=
    lt_of_le_of_lt (σs_k_le P η L N G γ wE ρG ℓ ωs φ rc0 s ω') hs
  set m := mA P η L N G γ wE ρG ℓ ωs φ rc0 s ω' with hm
  set v := vA P η L N G γ wE ρG ℓ ωs φ rc0 s ω' with hv
  set X : RC PA → ℝ := fun z => m - ARc P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z with hX
  have hp : ∀ z, 0 ≤ (Pool.P0203.nuD PA hL hN z).toReal := fun z => ENNReal.toReal_nonneg
  have hp1 : ∑ z, (Pool.P0203.nuD PA hL hN z).toReal = 1 := Pool.P0092.sum_toReal_one _
  have hm1 : m ≤ 1 := mA_le_one hN hwE hwE0 hγ s ω' hk
  have hbd : ∀ z, (Pool.P0203.nuD PA hL hN z).toReal ≠ 0 → κ * X z ≤ 1 := by
    intro z _
    have h0 := ARc_nonneg (P := P) (η := η) (L := L) (N := N) (G := G) (γ := γ) (wE := wE) (ρG := ρG) (ℓ := ℓ) (ωs := ωs) (φ := φ) (rc0 := rc0) s ω' z
    simp only [hX]
    nlinarith
  have hexp := Pool.P0023.sum_exp_le (fun z => (Pool.P0203.nuD PA hL hN z).toReal) hp hp1 X hbd
  have hEA : ∑ z, (Pool.P0203.nuD PA hL hN z).toReal * ARc P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z = m := by
    simp only [Pool.P0203.nuD_toReal, hm, mA]
  have hEA2 : ∑ z, (Pool.P0203.nuD PA hL hN z).toReal * ARc P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z ^ 2 = v := by
    simp only [Pool.P0203.nuD_toReal, hv, vA]
  have hEX : ∑ z, (Pool.P0203.nuD PA hL hN z).toReal * X z = 0 := by
    simp only [hX, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul, hEA, sub_self]
  have hEX2 : ∑ z, (Pool.P0203.nuD PA hL hN z).toReal * X z ^ 2 = v - m ^ 2 := by
    have e : ∀ z, (Pool.P0203.nuD PA hL hN z).toReal * X z ^ 2 =
        m ^ 2 * (Pool.P0203.nuD PA hL hN z).toReal -
          2 * m * ((Pool.P0203.nuD PA hL hN z).toReal * ARc P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z) +
          (Pool.P0203.nuD PA hL hN z).toReal * ARc P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z ^ 2 := by
      intro z; simp only [hX]; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1, hEA, hEA2]
    ring
  have hDT : ∀ z, DT P η L N G γ wE ρG ℓ ωs φ rc0 κ s (Fin.snoc ω' z) = X z - κ * v := by
    intro z
    simp only [DT, if_pos hs, Fin.init_snoc, Fin.snoc_last, hX, hm, hv]
  simp only [hDT]
  have e2 : ∀ z, (Pool.P0203.nuD PA hL hN z).toReal * exp (κ * (X z - κ * v)) =
      exp (-(κ ^ 2 * v)) * ((Pool.P0203.nuD PA hL hN z).toReal * exp (κ * X z)) := by
    intro z; rw [← mul_assoc, mul_comm (exp _), mul_assoc, ← exp_add]; congr 2; ring
  simp only [e2, ← Finset.mul_sum]
  rw [hEX, hEX2] at hexp
  calc exp (-(κ ^ 2 * v)) * ∑ z, (Pool.P0203.nuD PA hL hN z).toReal * exp (κ * X z)
      ≤ exp (-(κ ^ 2 * v)) * exp (κ * 0 + κ ^ 2 * (v - m ^ 2)) :=
        mul_le_mul_of_nonneg_left hexp (exp_pos _).le
    _ = exp (-(κ ^ 2 * m ^ 2)) := by rw [← exp_add]; congr 1; ring
    _ ≤ 1 := exp_le_one_iff.2 (by nlinarith [sq_nonneg (κ * m)])

open Classical in
/-- **The lower-tail good event fails with probability `≤ (T+1)²e^{−Lc}`**: outside it, on some interval
`[a, b) ⊆ [0, T)`, `Σ (E[ARc] − ARc − κ·E[ARc²]) ≥ Lc/κ`. -/
theorem prob_not_goodHT (hL : (PA).IsLaw) (hN : 0 < (PA).N) (hwE : P.wE = wE) (hwE0 : 0 < wE) (hγ : 0 < γ)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (Lc : ℝ) (T : ℕ) :
    (∑ ω : Fin T → RC PA, wgt (Pool.P0203.nuD PA hL hN) ω *
      if StepGood (DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lc / κ) T ω then (0 : ℝ) else 1) ≤
      ((T : ℝ) + 1) ^ 2 * exp (-Lc) :=
  prob_not_stepGood (Pool.P0203.nuD PA hL hN) (DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) hκ0
    (DT_step (ℓ := ℓ) (ωs := ωs) (φ := φ) (rc0 := rc0) hL hN hwE hwE0 hγ hκ0 hκ1) (fun _ _ => true) Lc T

end Bounds

/-! ### Transport to the run on a full coin sequence -/

/-- On the prefix of a full sequence, the coin-model IX-data loss of round `u < T` is P0225's real-time `AR`. -/
theorem ARc_pre {T : ℕ} (ω : ℕ → RC PA) {u : ℕ} (hu : u < T) :
    ARc P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u) (ω u) = Pool.P0225.AR P η L N G γ wE ρG ℓ ω ωs φ T u := by
  have hag := Pool.P0203.extD_pre_agree PA rc0 ω u
  have hσ : σs P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u) = sA PA ℓ ω ωs φ u := by
    unfold σs sAA; exact sA_congr ωs φ u hag
  have hV : Vs P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u) = active PA ℓ ω ωs φ u := by
    unfold Vs; exact active_congr ωs φ u hag
  have hsB : sB PA ℓ (Pool.P0203.extD PA rc0 (Pool.P0203.pre PA ω u)) u = sB PA ℓ ω u := sB_congr u hag
  by_cases hg : Pool.P0225.gE P η L N G γ wE ρG ω u = true
  · rw [Pool.P0225.AR_eq P η L N G γ wE ρG ℓ ω ωs φ T hu hg]
    have hE : isE PA (ω u).1 = true := hg
    unfold ARc
    rw [if_pos hE, hσ, hV]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Pool.P0225.cuR_eq P η L N G γ wE ρG ℓ ω ωs φ T hu hg f]
    congr 2
    have hch : drawQ P η L N G γ wE ρG (sA PA ℓ ω ωs φ u) (active PA ℓ ω ωs φ u) (ω u).2.1 =
        algCh PA ℓ ω ωs φ u := rfl
    rw [hch]
    unfold bitc
    rcases algCh PA ℓ ω ωs φ u with _ | x
    · simp only [armOf, bAct]; rw [hsB]
    · rfl
  · have h0 : Pool.P0225.AR P η L N G γ wE ρG ℓ ω ωs φ T u = 0 := by unfold Pool.P0225.AR; rw [if_neg hg]
    rw [h0]
    have hE : ¬ isE PA (ω u).1 = true := hg
    unfold ARc
    rw [if_neg hE]

theorem aPol_pre (ω : ℕ → RC PA) (u : ℕ) :
    aPol PA ℓ ωs φ (Pool.P0203.extD PA rc0 (Pool.P0203.pre PA ω u)) u = aPol PA ℓ ωs φ ω u := by
  have hag := Pool.P0203.extD_pre_agree PA rc0 ω u
  unfold aPol
  rw [sA_congr ωs φ u hag, active_congr ωs φ u hag, sB_congr u hag]

/-- The per-round slack of `htrue`: ALG's rounding/IX bias `aPol − E[ARc]` plus `κ·E[ARc²]` (both predictable). -/
noncomputable def slack (κ : ℝ) (ω : ℕ → RC PA) (u : ℕ) : ℝ :=
  (aPol PA ℓ ωs φ ω u - mA P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u)) +
    κ * vA P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u)

/-- **P0186's `htrue` for P0225's `withAlgG`, horizon-`T` form.** On the good event of `prob_not_goodHT` (length-`T` prefix of
`ω`), with `T ≤ 2^L`: for every interval `[a, b) ⊆ [0, T)`, ALG's true policy loss is at most its IX-data loss plus
the per-round slack plus `Lc/κ`. This is the inequality of P0186's `htrue` with `A := Pool.P0225.AR + slack` and the constant
`Ψ = Lc/κ`, **on intervals inside `[0, T]` only**: P0186's `ActHyp.htrue` field quantifies over all intervals, and its
extension past `T` (e.g. truncating `aPol`, `Pool.P0225.AR`, `slack` after `T`) is open, as for P0208/P0212. -/
theorem htrue_run {κ : ℝ} {Lc : ℝ} {T : ℕ} (hT : T ≤ 2 ^ L) (ω : ℕ → RC PA)
    (hgood : StepGood (DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lc / κ) T (Pool.P0203.pre PA ω T))
    {a b : ℕ} (hab : a ≤ b) (hbT : b ≤ T) :
    ∑ u ∈ Finset.Ico a b, aPol PA ℓ ωs φ ω u ≤
      ∑ u ∈ Finset.Ico a b, (Pool.P0225.AR P η L N G γ wE ρG ℓ ω ωs φ T u + slack P η L N G γ wE ρG ℓ ωs φ rc0 κ ω u) +
        Lc / κ := by
  have h := hgood a b hab hbT
  rw [Pool.P0220.runSum_pre_gen PA _ _ ω a b T] at h
  have hsum : (∑ u ∈ Finset.range T, if a ≤ u ∧ u < b ∧ (fun (_ : ℕ) (_ : Fin _ → RC PA) => true) u
        (Pool.P0203.pre PA ω u) = true then
        DT P η L N G γ wE ρG ℓ ωs φ rc0 κ u (Pool.P0203.pre PA ω (u + 1)) else 0) =
      ∑ u ∈ Finset.Ico a b, DT P η L N G γ wE ρG ℓ ωs φ rc0 κ u (Pool.P0203.pre PA ω (u + 1)) := by
    rw [← Finset.sum_filter]
    congr 1
    ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, and_true]; omega
  rw [hsum] at h
  have hDT : ∀ u ∈ Finset.Ico a b, DT P η L N G γ wE ρG ℓ ωs φ rc0 κ u (Pool.P0203.pre PA ω (u + 1)) =
      mA P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u) - Pool.P0225.AR P η L N G γ wE ρG ℓ ω ωs φ T u -
        κ * vA P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u) := by
    intro u hu
    simp only [Finset.mem_Ico] at hu
    have hu2 : u < 2 ^ L := by omega
    unfold DT
    rw [if_pos hu2, Pool.P0203.init_pre]
    rw [show Pool.P0203.pre PA ω (u + 1) (Fin.last u) = ω u from rfl, ARc_pre P η L N G γ wE ρG ℓ ωs φ rc0 ω
      (show u < T by omega)]
  rw [Finset.sum_congr rfl hDT] at h
  have e : ∑ u ∈ Finset.Ico a b, aPol PA ℓ ωs φ ω u =
      ∑ u ∈ Finset.Ico a b, (Pool.P0225.AR P η L N G γ wE ρG ℓ ω ωs φ T u + slack P η L N G γ wE ρG ℓ ωs φ rc0 κ ω u) +
      ∑ u ∈ Finset.Ico a b, (mA P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u) -
        Pool.P0225.AR P η L N G γ wE ρG ℓ ω ωs φ T u - κ * vA P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    unfold slack; ring
  rw [e]
  linarith

/-- **The slack, bounded** (with `wE` = P0194's exploitation weight, `G ≥ 1`, `0 ≤ κ`): at every round `u < 2^L`,
`slack ≤ s_u·(γ + 2/N) + wE/G + κ·s_u·(1/wE + 1/(4N·wE·γ))`, where `s_u` is the support size of ALG's marginal at
`u`. -/
theorem slack_le (hN : 0 < (PA).N) (hwE : P.wE = wE) (hwE0 : 0 < wE) (hγ : 0 < γ) (hG : 1 ≤ G) {κ : ℝ}
    (hκ : 0 ≤ κ) (ω : ℕ → RC PA) {u : ℕ} (hu : u < 2 ^ L) :
    slack P η L N G γ wE ρG ℓ ωs φ rc0 κ ω u ≤
      supp η L (sA PA ℓ ω ωs φ u) (active PA ℓ ω ωs φ u) * (γ + 2 / N) + wE / G +
        κ * (supp η L (sA PA ℓ ω ωs φ u) (active PA ℓ ω ωs φ u) * (1 / wE + 1 / (4 * N * (wE * γ)))) := by
  have hag := Pool.P0203.extD_pre_agree PA rc0 ω u
  have hσ : σs P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u) = sA PA ℓ ω ωs φ u := by
    unfold σs sAA; exact sA_congr ωs φ u hag
  have hV : Vs P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u) = active PA ℓ ω ωs φ u := by
    unfold Vs; exact active_congr ωs φ u hag
  have hk : (σs P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre PA ω u)).k < 2 ^ L :=
    lt_of_le_of_lt (σs_k_le P η L N G γ wE ρG ℓ ωs φ rc0 u _) hu
  have h1 := aPol_sub_mA_le (ℓ := ℓ) (ωs := ωs) (φ := φ) (rc0 := rc0) hN hwE hwE0 hγ hG u (Pool.P0203.pre PA ω u) hk
  have h2 := vA_le (ℓ := ℓ) (ωs := ωs) (φ := φ) (rc0 := rc0) hN hwE hwE0 hγ u (Pool.P0203.pre PA ω u) hk
  rw [aPol_pre, hσ, hV] at h1
  rw [hσ, hV] at h2
  unfold slack
  have := mul_le_mul_of_nonneg_left h2 hκ
  linarith

end Pool.P0240
