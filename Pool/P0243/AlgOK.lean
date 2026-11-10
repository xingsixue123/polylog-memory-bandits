import Pool.P0240.HTrue
import Pool.P0226.Act
import Pool.P0228.ExpD

/-!
# P0228's `AlgOK` for P0225's withAlgG ALG, with a path-dependent variance budget

P0228's `slot_expect` leaves `P(¬AlgOK)` open: ALG's two interval guarantees (P0223's `hint`, vs BASE, and `hA`,
vs every copy over its active window). For P0225's withAlgG ALG they follow from P0212's learner inequality, P0231's IX bounds
(copies and meta-arm) and P0227's `htrue`, with the constant `ρOK = Lc/κ + αT + Lc/(2wEγ)` and the per-round budget
`vOK = (η/2)·Pool.P0225.VR + (P0227's slack)⁺`. The budget is a random (path-dependent) sequence, so `AlgOK` is used with
`v := vOK ω`; `slot_expect_path` is P0228's `slot_expect` for such path-dependent `v`, `r`.
-/

namespace Pool.P0243

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0231 Pool.P0240
open Pool.P0227 (supp supp_le)

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (Pool.P0225.withAlgG P η L N G γ wE ρG).K → ι → Bool)
  (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (T : ℕ)

local notation "PA" => Pool.P0225.withAlgG P η L N G γ wE ρG

theorem VR_nonneg (ω : ℕ → RC PA) (u : ℕ) : 0 ≤ Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u := by
  unfold Pool.P0225.VR Pool.P0225.Vp; split_ifs
  · exact Pool.P0138.palgVar_nonneg (fun _ => one_pos) _ _ _ _ _
  · exact le_rfl
  · exact le_rfl

/-- P0225's learner inequality on `[a, b) ⊆ [0, T]` with the horizon constant `αT` (P0226) in place of the learner
time at `T`. -/
theorem learner_int (ω : ℕ → RC PA) (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) (hρr : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ)
    (hTL : T ≤ 2 ^ L) (f : Option ι) (a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T)
    (hpres : ∀ u, a ≤ u → u < b → Pool.P0225.gE P η L N G γ wE ρG ω u = true →
      presOf (active PA ℓ ω ωs φ u) f = true) :
    ∑ u ∈ Ico a b, Pool.P0225.AR P η L N G γ wE ρG ℓ ω ωs φ T u ≤
      ∑ u ∈ Ico a b, Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u f + Pool.P0226.αT (ι := ι) η L T δ +
        ∑ u ∈ Ico a b, η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u := by
  have h := Pool.P0225.learner_hyp P η L N G γ wE ρG ℓ ω ωs φ T hη hδ hρr hTL f a b hab hbT hpres
  have hk : ((Pool.P0225.SF P η L N G γ wE ρG ℓ ω ωs φ T).k : ℝ) ≤ T := by
    have : (Pool.P0225.SF P η L N G γ wE ρG ℓ ω ωs φ T).k ≤ T := by
      rw [Pool.P0225.sA_k]; unfold Pool.P0225.kE; exact (Finset.card_filter_le _ _).trans (by simp)
    exact_mod_cast this
  have hαle : (2 * L + 1) * (Real.log (Fintype.card (Spec (Option ι) L)) +
      2 * δ * (Pool.P0225.SF P η L N G γ wE ρG ℓ ω ωs φ T).k) / η ≤ Pool.P0226.αT (ι := ι) η L T δ := by
    unfold Pool.P0226.αT
    apply div_le_div_of_nonneg_right _ hη.le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  rw [← Finset.mul_sum]
  linarith

/-- ALG's per-round variance budget on the path `ω`: P0212's second-moment term `(η/2)·Pool.P0225.VR` plus the positive part of
P0227's slack (IX/rounding bias and `κ·E[AR²|past]`). -/
noncomputable def vOK (κ : ℝ) (ω : ℕ → RC PA) (u : ℕ) : ℝ :=
  η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u + max 0 (slack P η L N G γ wE ρG ℓ ωs φ rc0 κ ω u)

/-- ALG's interval constant: `Lc/κ` (P0227's `htrue`) `+ αT` (P0212's learner constant at horizon `T`, P0226)
`+ Lc/(2wEγ)` (P0220's IX bound). `αT` contains the horizon-scale term `(2L+1)·2δT/η`, so `ρOK ≥ T` (and `AlgOK`
holds trivially, since `Σ_{[a,b)}(aPol − bPol) ≤ b − a ≤ T`) unless `δ ≲ η/T`; for `ρ⋆` the rounding `ε = δ` must
be chosen that small for `AlgOK` to be informative. -/
noncomputable def ρOK (δ κ Lc : ℝ) : ℝ := Lc / κ + Pool.P0226.αT (ι := ι) η L T δ + Lc / (2 * (wE * γ))

theorem vOK_nonneg (hη : 0 ≤ η) (κ : ℝ) (ω : ℕ → RC PA) (u : ℕ) :
    0 ≤ vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ ω u := by
  unfold vOK
  have := VR_nonneg P η L N G γ wE ρG ℓ ωs φ T ω u
  have : 0 ≤ max 0 (slack P η L N G γ wE ρG ℓ ωs φ rc0 κ ω u) := le_max_left _ _
  positivity

theorem ρOK_nonneg (hη : 0 < η) {δ κ Lc : ℝ} (hδ : 0 ≤ δ) (hκ : 0 < κ) (hLc : 0 ≤ Lc) (hγ : 0 < γ)
    (hwE : 0 < wE) : 0 ≤ ρOK η L γ wE (ι := ι) T δ κ Lc := by
  unfold ρOK
  have := Pool.P0226.αT_nonneg (ι := ι) η L T hη hδ
  have : 0 ≤ Lc / κ := div_nonneg hLc hκ.le
  have : 0 ≤ Lc / (2 * (wE * γ)) := div_nonneg hLc (by positivity)
  linarith

/-- **Core chain.** On P0227's `htrue` good event, for an expert `f` present at the exploitation rounds of
`[a, b) ⊆ [0, T)` whose IX data are within `Lc/(2wEγ)` of a loss sequence `lf`: ALG's policy loss is at most `lf` plus
`ρOK` plus the budget `vOK` on `[a, b)`. -/
theorem alg_le_expert (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) (hρr : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ)
    (hwE0 : 0 < wE) (hTL : T ≤ 2 ^ L) {κ Lc : ℝ} (ω : ℕ → RC PA)
    (hHT : Pool.P0149.StepGood (DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lc / κ) T
      (Pool.P0203.pre PA ω T))
    (f : Option ι) (lf : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    (hpres : ∀ u, a ≤ u → u < b → Pool.P0225.gE P η L N G γ wE ρG ω u = true →
      presOf (active PA ℓ ω ωs φ u) f = true)
    (hix : ∑ u ∈ Ico a b, Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u f ≤ ∑ u ∈ Ico a b, lf u + Lc / (2 * (wE * γ))) :
    ∑ u ∈ Ico a b, aPol PA ℓ ωs φ ω u ≤
      ∑ u ∈ Ico a b, lf u + ρOK η L γ wE (ι := ι) T δ κ Lc +
        ∑ u ∈ Ico a b, vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ ω u := by
  have h1 := htrue_run P η L N G γ wE ρG ℓ ωs φ rc0 hTL ω hHT hab hbT
  have h2 := learner_int P η L N G γ wE ρG ℓ ωs φ T ω hη hδ hρr hTL f a b hab hbT hpres
  have h3 : ∑ u ∈ Ico a b, slack P η L N G γ wE ρG ℓ ωs φ rc0 κ ω u ≤
      ∑ u ∈ Ico a b, max 0 (slack P η L N G γ wE ρG ℓ ωs φ rc0 κ ω u) :=
    Finset.sum_le_sum fun u _ => le_max_right _ _
  rw [Finset.sum_add_distrib] at h1
  unfold ρOK vOK
  rw [Finset.sum_add_distrib]
  linarith

/-- **ALG vs BASE (P0223's `hint`, `c = 0`).** On P0220's meta-arm good event and P0227's good event (length-`T`
prefix of `ω`), on every `[a, b) ⊆ [0, T)`: `Σ (aPol − bPol) ≤ ρOK + Σ vOK`. -/
theorem alg_vs_base (hL : (PA).IsLaw) (hN : 0 < (PA).N) (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ)
    (hρr : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hTL : T ≤ 2 ^ L) {κ Lc : ℝ}
    (ω : ℕ → RC PA)
    (hM : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD PA hL hN)
      (YB P η L N G γ wE ρG ℓ rc0) (bPolX P η L N G γ wE ρG ℓ rc0) (obsX P η L N G γ wE ρG ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (hHT : Pool.P0149.StepGood (DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lc / κ) T
      (Pool.P0203.pre PA ω T))
    (a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T) :
    -Pool.P0154.isum (fun u => bPol PA ℓ ω u - aPol PA ℓ ωs φ ω u) a b ≤
      ρOK η L γ wE (ι := ι) T δ κ Lc + Pool.P0154.isum (vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ ω) a b +
        0 * Real.sqrt ((b : ℝ) - a) := by
  have hix := (ix_run_meta P η L N G γ wE ρG ℓ ωs φ rc0 hL hN hγ hwE0 hwE T hTL ω hM a b hab hbT).le
  have h := alg_le_expert P η L N G γ wE ρG ℓ ωs φ rc0 T hη hδ hρr hγ hwE0 hTL ω hHT none
    (fun u => bPol PA ℓ ω u) hab hbT (fun _ _ _ _ => rfl) hix
  unfold Pool.P0154.isum
  rw [Finset.sum_sub_distrib]
  linarith

/-- **ALG vs a copy (P0223's `hA`).** On P0220's good event of copy `x` and P0227's good event: if `x` is active on
`[a, t) ⊆ [0, T)`, then `Σ_{[a,t)} aPol ≤ Σ_{[a,t)} ℓr x + ρOK + Σ_{[a,t)} vOK`. -/
theorem alg_vs_copy (hL : (PA).IsLaw) (hN : 0 < (PA).N) (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ)
    (hρr : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hTL : T ≤ 2 ^ L) {κ Lc : ℝ}
    (ω : ℕ → RC PA) (x : ι)
    (hX : Pool.P0146.IXGood (Pool.P0203.nuD PA hL hN) (lossX P η L N G γ wE ρG ℓ x)
      (obsX P η L N G γ wE ρG ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρG ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (hHT : Pool.P0149.StepGood (DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lc / κ) T
      (Pool.P0203.pre PA ω T))
    (a t : ℕ) (hat : a ≤ t) (htT : t ≤ T) (hact : ∀ u, a ≤ u → u < t → x ∈ active PA ℓ ω ωs φ u) :
    Pool.P0154.isum (fun u => aPol PA ℓ ωs φ ω u) a t ≤
      Pool.P0154.isum (fun u => ℓr PA ℓ u x) a t +
        (ρOK η L γ wE (ι := ι) T δ κ Lc + Pool.P0154.isum (vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ ω) a t) := by
  have h := ix_run P η L N G γ wE ρG ℓ ωs φ rc0 hL hN hγ hwE0 hwE T hTL ω x hX a t hat htT
  have e1 : ∑ u ∈ Ico a t, (if x ∈ active PA ℓ ω ωs φ u then Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u (some x) else 0) =
      ∑ u ∈ Ico a t, Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u (some x) :=
    Finset.sum_congr rfl fun u hu => by
      simp only [Finset.mem_Ico] at hu; rw [if_pos (hact u hu.1 hu.2)]
  have e2 : ∑ u ∈ Ico a t, (if x ∈ active PA ℓ ω ωs φ u then ℓr PA ℓ u x else 0) = ∑ u ∈ Ico a t, ℓr PA ℓ u x :=
    Finset.sum_congr rfl fun u hu => by
      simp only [Finset.mem_Ico] at hu; rw [if_pos (hact u hu.1 hu.2)]
  rw [e1, e2] at h
  have hpres : ∀ u, a ≤ u → u < t → Pool.P0225.gE P η L N G γ wE ρG ω u = true →
      presOf (active PA ℓ ω ωs φ u) (some x) = true := by
    intro u h1 h2 _
    simp [presOf, hact u h1 h2]
  have h' := alg_le_expert P η L N G γ wE ρG ℓ ωs φ rc0 T hη hδ hρr hγ hwE0 hTL ω hHT (some x)
    (fun u => ℓr PA ℓ u x) hat htT hpres h.le
  unfold Pool.P0154.isum
  linarith

/-- The copy budget `r x t = ρOK + Σ_{[E x, t)} vOK` of `hA`. -/
noncomputable def rOK (δ κ Lc : ℝ) (ω : ℕ → RC PA) (x : ι) (t : ℕ) : ℝ :=
  ρOK η L γ wE (ι := ι) T δ κ Lc + Pool.P0154.isum (vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ ω) (P.E x) t

/-- **`AlgOK` on the good events.** On P0220's good events (all copies and the meta-arm) and P0227's good event of the
length-`T` prefix of `ω`, P0228's `AlgOK` holds for `ω` with `v = vOK ω`, `ρ₀ = ρOK`, `c = 0`, `r = rOK ω`. -/
theorem algOK_of_good (hL : (PA).IsLaw) (hN : 0 < (PA).N) (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ)
    (hρr : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hTL : T ≤ 2 ^ L) {κ Lc : ℝ}
    (ω : ℕ → RC PA)
    (hX : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD PA hL hN) (lossX P η L N G γ wE ρG ℓ x)
      (obsX P η L N G γ wE ρG ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρG ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (hM : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD PA hL hN)
      (YB P η L N G γ wE ρG ℓ rc0) (bPolX P η L N G γ wE ρG ℓ rc0) (obsX P η L N G γ wE ρG ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (hHT : Pool.P0149.StepGood (DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lc / κ) T
      (Pool.P0203.pre PA ω T)) :
    Pool.P0228.AlgOK PA ℓ ωs φ T (vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ ω) (ρOK η L γ wE (ι := ι) T δ κ Lc) 0
      (rOK P η L N G γ wE ρG ℓ ωs φ rc0 T δ κ Lc ω) ω :=
  ⟨fun a b hab hbT => alg_vs_base P η L N G γ wE ρG ℓ ωs φ rc0 T hL hN hη hδ hρr hγ hwE0 hwE hTL ω hM hHT a b
      hab hbT,
    fun x t htT hEt hact => alg_vs_copy P η L N G γ wE ρG ℓ ωs φ rc0 T hL hN hη hδ hρr hγ hwE0 hwE hTL ω x
      (hX x) hHT (P.E x) t hEt.le htT hact⟩

open Classical in
/-- **`P(¬AlgOK) ≤ (|ι| + 2)(T+1)²e^{−Lc}`** over P0194's round coins (prefixes of length `T`, extended by `rc0`),
for P0225's withAlgG ALG with `v = vOK`, `ρ₀ = ρOK`, `c = 0`, `r = rOK` (union of P0231's two failure bounds and P0240's). -/
theorem prob_not_algOK (hL : (PA).IsLaw) (hN : 0 < (PA).N) (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ)
    (hρr : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hTL : T ≤ 2 ^ L) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (Lc : ℝ) :
    ∑ ω : Fin T → RC PA, Pool.P0202.pw (wR PA) ω *
      (if Pool.P0228.AlgOK PA ℓ ωs φ T (vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ (Pool.P0210.extR PA rc0 ω))
          (ρOK η L γ wE (ι := ι) T δ κ Lc) 0
          (rOK P η L N G γ wE ρG ℓ ωs φ rc0 T δ κ Lc (Pool.P0210.extR PA rc0 ω)) (Pool.P0210.extR PA rc0 ω)
        then 0 else 1) ≤ ((Fintype.card ι : ℝ) + 2) * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) := by
  set GX : (Fin T → RC PA) → Prop := fun ω' => ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD PA hL hN)
    (lossX P η L N G γ wE ρG ℓ x) (obsX P η L N G γ wE ρG ℓ ωs φ rc0 (some x)) (wE * γ)
    (gateX P η L N G γ wE ρG ℓ ωs φ rc0 x) Lc T ω'
  set GM : (Fin T → RC PA) → Prop := fun ω' => Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD PA hL hN)
      (YB P η L N G γ wE ρG ℓ rc0) (bPolX P η L N G γ wE ρG ℓ rc0) (obsX P η L N G γ wE ρG ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T ω'
  set GH : (Fin T → RC PA) → Prop := fun ω' =>
    Pool.P0149.StepGood (DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lc / κ) T ω'
  have hX := prob_not_ixGood_all P η L N G γ wE ρG ℓ ωs φ rc0 hL hN hγ hwE0 Lc T
  have hM := prob_not_ixGood_meta P η L N G γ wE ρG ℓ ωs φ rc0 hL hN hγ hwE0 Lc T
  have hH := prob_not_goodHT (P := P) (η := η) (L := L) (N := N) (G := G) (γ := γ) (wE := wE) (ρG := ρG) (ℓ := ℓ)
    (ωs := ωs) (φ := φ) (rc0 := rc0) hL hN hwE hwE0 hγ hκ0 hκ1 Lc T
  simp_rw [Pool.P0228.wgt_eq_pw PA hL hN] at hX hM hH
  have hpt : ∀ ω : Fin T → RC PA, Pool.P0202.pw (wR PA) ω *
      (if Pool.P0228.AlgOK PA ℓ ωs φ T (vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ (Pool.P0210.extR PA rc0 ω))
          (ρOK η L γ wE (ι := ι) T δ κ Lc) 0
          (rOK P η L N G γ wE ρG ℓ ωs φ rc0 T δ κ Lc (Pool.P0210.extR PA rc0 ω)) (Pool.P0210.extR PA rc0 ω)
        then (0 : ℝ) else 1) ≤
      Pool.P0202.pw (wR PA) ω * (if GX ω then 0 else 1) + Pool.P0202.pw (wR PA) ω * (if GM ω then 0 else 1) +
        Pool.P0202.pw (wR PA) ω * (if GH ω then 0 else 1) := by
    intro ω
    have hp := Pool.P0228.pw_nonneg PA hL ω
    rw [← mul_add, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hp
    have hpre := Pool.P0228.pre_extR PA rc0 ω
    by_cases h1 : GX ω
    · by_cases h2 : GM ω
      · by_cases h3 : GH ω
        · have hok := algOK_of_good P η L N G γ wE ρG ℓ ωs φ rc0 T hL hN hη hδ hρr hγ hwE0 hwE hTL
            (Pool.P0210.extR PA rc0 ω) (by rw [hpre]; exact h1) (by rw [hpre]; exact h2) (by rw [hpre]; exact h3)
          rw [if_pos hok]; split_ifs <;> norm_num
        · rw [if_neg h3]; split_ifs <;> norm_num
      · rw [if_neg h2]; split_ifs <;> norm_num
    · rw [if_neg h1]; split_ifs <;> norm_num
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin T → RC PA))) fun ω _ => hpt ω
  simp only [Finset.sum_add_distrib] at hsum
  have e : ((Fintype.card ι : ℝ) + 2) * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) =
      Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) +
        ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) := by ring
  rw [e]
  linarith

/-- **The budget, bounded pathwise** (from P0227's `slack_le` and `supp_le`): for `u < T ≤ 2^L`, `G ≥ 1`,
`0 ≤ κ`, `vOK u ≤ (η/2)·Pool.P0225.VR u + (|active u| + 1)·(γ + 2/N + κ·(1/wE + 1/(4N·wE·γ))) + wE/G`. -/
theorem vOK_le (hN : 0 < (PA).N) (hwE : P.wE = wE) (hwE0 : 0 < wE) (hγ : 0 < γ) (hG : 1 ≤ G) {κ : ℝ}
    (hκ : 0 ≤ κ) (ω : ℕ → RC PA) {u : ℕ} (hu : u < 2 ^ L) :
    vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ ω u ≤
      η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u +
        ((active PA ℓ ω ωs φ u).card + 1) * (γ + 2 / N + κ * (1 / wE + 1 / (4 * N * (wE * γ)))) + wE / G := by
  have h := slack_le (P := P) (η := η) (L := L) (N := N) (G := G) (γ := γ) (wE := wE) (ρG := ρG) (ℓ := ℓ) (ωs := ωs) (φ := φ) (rc0 := rc0) hN hwE hwE0 hγ hG hκ ω hu
  have hs : (supp η L (sA PA ℓ ω ωs φ u) (active PA ℓ ω ωs φ u) : ℝ) ≤ (active PA ℓ ω ωs φ u).card + 1 := by
    exact_mod_cast supp_le (η := η) (L := L) _ _
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 ≤ γ + 2 / N + κ * (1 / wE + 1 / (4 * N * (wE * γ))) := by positivity
  have hG0 : (0 : ℝ) ≤ wE / G := by positivity
  have hs0 : (0 : ℝ) ≤ supp η L (sA PA ℓ ω ωs φ u) (active PA ℓ ω ωs φ u) := Nat.cast_nonneg _
  have key : slack P η L N G γ wE ρG ℓ ωs φ rc0 κ ω u ≤
      ((active PA ℓ ω ωs φ u).card + 1) * (γ + 2 / N + κ * (1 / wE + 1 / (4 * N * (wE * γ)))) + wE / G := by
    have := mul_le_mul_of_nonneg_right hs hc
    nlinarith
  unfold vOK
  have : max 0 (slack P η L N G γ wE ρG ℓ ωs φ rc0 κ ω u) ≤
      ((active PA ℓ ω ωs φ u).card + 1) * (γ + 2 / N + κ * (1 / wE + 1 / (4 * N * (wE * γ)))) + wE / G :=
    max_le (by positivity) key
  linarith

end Pool.P0243
