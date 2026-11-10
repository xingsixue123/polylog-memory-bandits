import Pool.P0220.IXD
import Pool.P0158.FreedV

/-!
# `htrue` for P0212's ALG: the learner's estimated loss tracks its true policy loss
-/

namespace Pool.P0224

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0220

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (withAlg P η L N G γ wE ρr).K → ι → Bool)
  (rc0 : RC (withAlg P η L N G γ wE ρr))

/-- The learner's state and active set after a prefix. -/
noncomputable abbrev σX (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) : AState ι :=
  sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 ω') s
noncomputable abbrev VX (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) : Finset ι :=
  active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s

/-- The chosen expert with round coin `z`. -/
noncomputable def chX (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) (z : RC (withAlg P η L N G γ wE ρr)) :
    Option ι :=
  drawQ P η L N G γ wE ρr (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') z.2.1

/-- The loss of expert `f` with BASE's action coin `yB` (the meta-arm plays BASE's action). -/
noncomputable def lossF (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) (f : Option ι)
    (yB : (withAlg P η L N G γ wE ρr).AB.Y) : Bool :=
  ℓ s (match f with
    | some x => (withAlg P η L N G γ wE ρr).arm x
    | none => (withAlg P η L N G γ wE ρr).AB.act 0
        (sB (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') s) yB)

/-- The learner's estimated loss in round `s` with coin `z` (its marginal on the chosen expert times its IX
estimate; zero off exploitation rounds). -/
noncomputable def ARp (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) (z : RC (withAlg P η L N G γ wE ρr)) :
    ℝ :=
  if isE (withAlg P η L N G γ wE ρr) z.1 = true then
    pmarg η L (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω')
        (chX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z) *
      ixA η L N G γ wE (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω')
        (chX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z)
        (lossF P η L N G γ wE ρr ℓ rc0 s ω' (chX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z) z.2.2.1)
        (chX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z)
  else 0
theorem ARp_nonneg (hγ : 0 < γ) (hwE : 0 < wE) (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr))
    (z : RC (withAlg P η L N G γ wE ρr)) : 0 ≤ ARp P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z := by
  unfold ARp; split_ifs
  · refine mul_nonneg (pmarg_nonneg _ _ _ _ _) ?_
    unfold ixA; rw [if_pos rfl]
    have := Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι))
      (p := pmarg η L (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω'))
      (chX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z)
    unfold ptA; positivity
  · exact le_rfl

/-- **Range of the estimated loss** before learner time `2^L`: `ARp ≤ (1 + 1/(Nγ))/wE`. -/
theorem ARp_le (hγ : 0 < γ) (hwE : 0 < wE) (hN : 0 < N) (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr))
    (hk : (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω').k < 2 ^ L) (z : RC (withAlg P η L N G γ wE ρr)) :
    ARp P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z ≤ (1 + 1 / (N * γ)) / wE := by
  have hR0 : 0 ≤ (1 + 1 / (N * γ)) / wE := by positivity
  unfold ARp; split_ifs
  · set σ := σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω'
    set V := VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω'
    set f := chX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z
    have hp1 := pmarg_sum η L σ V hk
    have hpf : pmarg η L σ V f ≤ ptA η L N σ V f + 1 / N :=
      Pool.P0179.p_le_pt_add hN (pmarg_nonneg η L σ V) hp1 f
    have hpt : 0 ≤ ptA η L N σ V f := Pool.P0179.pt_nonneg _
    have hden : 0 < wE * (ptA η L N σ V f + γ) := by positivity
    unfold ixA; rw [if_pos rfl]
    have hbit : ((lossF P η L N G γ wE ρr ℓ rc0 s ω' f z.2.2.1).toNat : ℝ) ≤ 1 := by
      cases lossF P η L N G γ wE ρr ℓ rc0 s ω' f z.2.2.1 <;> simp
    have h1 := floor_div_le G (v := ((lossF P η L N G γ wE ρr ℓ rc0 s ω' f z.2.2.1).toNat : ℝ) /
      (wE * (ptA η L N σ V f + γ))) (by positivity)
    have h2 : ((lossF P η L N G γ wE ρr ℓ rc0 s ω' f z.2.2.1).toNat : ℝ) / (wE * (ptA η L N σ V f + γ)) ≤
        1 / (wE * (ptA η L N σ V f + γ)) := div_le_div_of_nonneg_right hbit hden.le
    have h3 : pmarg η L σ V f * (1 / (wE * (ptA η L N σ V f + γ))) ≤ (1 + 1 / (N * γ)) / wE := by
      rw [mul_one_div, div_le_div_iff₀ hden hwE]
      have hNγ : (0 : ℝ) < N * γ := by positivity
      have key : pmarg η L σ V f ≤ (1 + 1 / (N * γ)) * (ptA η L N σ V f + γ) := by
        have hN' : (0 : ℝ) < N := by exact_mod_cast hN
        have e : 1 / (N * γ) * (ptA η L N σ V f + γ) = ptA η L N σ V f / (N * γ) + 1 / N := by
          field_simp
        rw [add_mul, one_mul, e]
        have : 0 ≤ ptA η L N σ V f / (N * γ) := by positivity
        linarith
      nlinarith
    calc pmarg η L σ V f * (((⌊(G : ℝ) * (((lossF P η L N G γ wE ρr ℓ rc0 s ω' f z.2.2.1).toNat : ℝ) /
          (wE * (ptA η L N σ V f + γ)))⌋₊ : ℕ) : ℝ) / G)
        ≤ pmarg η L σ V f * (1 / (wE * (ptA η L N σ V f + γ))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (pmarg_nonneg _ _ _ _ _)
      _ ≤ _ := h3
  · exact hR0

omit [LinearOrder ι] in
/-- Marginalization of P0194's weights to exploitation rounds, keeping the draw coin and BASE's action coin. -/
theorem sum_wR_exploit2 [LinearOrder ι] (Q : ParD n ι) (H : Fin Q.N → Q.AB.Y → ℝ) :
    ∑ rc : RC Q, wR Q rc * (if isE Q rc.1 = true then H rc.2.1 rc.2.2.1 else 0) =
      Q.wE * ∑ d, (1 / (Q.N : ℝ)) * ∑ yB, (Q.AB.μ yB).toReal * H d yB := by
  have hν : ∑ zB : Q.AB.Z, (Q.AB.ν zB).toReal = 1 := Pool.P0092.sum_toReal_one Q.AB.ν
  simp only [Fintype.sum_prod_type, wR]
  have hinner : ∀ (κ : Kd Q) (d : Fin Q.N) (yB : Q.AB.Y),
      ∑ zB : Q.AB.Z, wK Q κ * (1 / (Q.N : ℝ)) * (Q.AB.μ yB).toReal * (Q.AB.ν zB).toReal *
        (if isE Q κ = true then H d yB else 0) =
      (wK Q κ * (if isE Q κ = true then 1 else 0)) * ((1 / (Q.N : ℝ)) * ((Q.AB.μ yB).toReal * H d yB)) := by
    intro κ d yB
    have e : ∀ zB, wK Q κ * (1 / (Q.N : ℝ)) * (Q.AB.μ yB).toReal * (Q.AB.ν zB).toReal *
        (if isE Q κ = true then H d yB else 0) =
        ((wK Q κ * (if isE Q κ = true then 1 else 0)) * ((1 / (Q.N : ℝ)) * ((Q.AB.μ yB).toReal * H d yB))) *
          (Q.AB.ν zB).toReal := fun _ => by split_ifs <;> ring
    simp only [e, ← Finset.mul_sum, hν, mul_one]
  simp only [hinner, ← Finset.mul_sum, ← Finset.sum_mul]
  congr 1
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [isE, wK]
  rw [Finset.sum_eq_zero (fun r _ => by simp)]
  simp

/-- Averaging over the draw coin is averaging over the rounded law (before learner time `2^L`). -/
theorem sum_draw (σ : AState ι) (V : Finset ι) (hN : 0 < N) (hk : σ.k < 2 ^ L) (F : Option ι → ℝ) :
    ∑ d : Fin N, (1 / (N : ℝ)) * F (drawA η L N σ V d) = ∑ f, ptA η L N σ V f * F f := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Finset.sum_fiberwise (s := univ) (g := fun d => drawA η L N σ V d)
    (f := fun d => (1 / (N : ℝ)) * F (drawA η L N σ V d))]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hc : ∀ d ∈ univ.filter (fun d : Fin N => drawA η L N σ V d = f),
      (1 / (N : ℝ)) * F (drawA η L N σ V d) = (1 / (N : ℝ)) * F f := by
    intro d hd; simp only [Finset.mem_filter] at hd; rw [hd.2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  have hfib := Pool.P0179.prob_draw (N := N) (b := (none : Option ι)) hN (pmarg_nonneg η L σ V)
    (pmarg_sum η L σ V hk) f
  have hcard : (univ.filter fun d : Fin N => drawA η L N σ V d = f) =
      (univ.filter fun d : Fin N => Pool.P0179.draw (N := N) (b := (none : Option ι)) (pmarg_nonneg η L σ V)
        (pmarg_sum η L σ V hk) d = f) := by
    ext d; simp only [Finset.mem_filter, Finset.mem_univ, true_and, drawA_eq η L N σ V hk]
  rw [hcard, ← mul_assoc, mul_comm _ (1 / (N : ℝ))]
  unfold ptA
  rw [← hfib]
  ring

/-- Expert `f`'s expected loss over BASE's action coin. -/
noncomputable def ℓbar (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) (f : Option ι) : ℝ :=
  ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal * ((lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB).toNat : ℝ)
theorem ℓbar_mem (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) (f : Option ι) :
    0 ≤ ℓbar P η L N G γ wE ρr ℓ rc0 s ω' f ∧ ℓbar P η L N G γ wE ρr ℓ rc0 s ω' f ≤ 1 := by
  have hμ := Pool.P0092.sum_toReal_one (withAlg P η L N G γ wE ρr).AB.μ
  constructor
  · exact Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (by positivity)
  · calc ℓbar P η L N G γ wE ρr ℓ rc0 s ω' f ≤ ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal * 1 :=
          Finset.sum_le_sum fun yB _ => mul_le_mul_of_nonneg_left (by
            cases lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB <;> simp) ENNReal.toReal_nonneg
      _ = 1 := by simp only [mul_one]; exact hμ

/-- The learner's true policy loss read from a prefix (P0194's `aPol`). -/
noncomputable def aPolX (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) : ℝ :=
  ∑ d : Fin (withAlg P η L N G γ wE ρr).N, (1 / ((withAlg P η L N G γ wE ρr).N : ℝ)) *
    ℓbar P η L N G γ wE ρr ℓ rc0 s ω'
      (drawQ P η L N G γ wE ρr (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') d)

/-- The policy loss is the rounded law against the experts' expected losses. -/
theorem aPolX_eq (hN : 0 < N) (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr))
    (hk : (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    aPolX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' =
      ∑ f, ptA η L N (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') f *
        ℓbar P η L N G γ wE ρr ℓ rc0 s ω' f :=
  sum_draw η L N _ _ hN hk _

/-- The conditional mean of the learner's estimated loss. -/
noncomputable def meanA (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) : ℝ :=
  ∑ z, (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal * ARp P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z
theorem meanA_eq (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr))
    (hk : (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    meanA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN s ω' =
      (withAlg P η L N G γ wE ρr).wE * ∑ f,
        ptA η L N (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') f *
        ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
          (pmarg η L (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') f *
            ixA η L N G γ wE (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') f
              (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f) := by
  have hN0 : 0 < N := hN
  unfold meanA
  simp only [Pool.P0203.nuD_toReal]
  have key := sum_wR_exploit2 (withAlg P η L N G γ wE ρr) (fun d yB =>
    pmarg η L (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω')
        (drawQ P η L N G γ wE ρr (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') d) *
      ixA η L N G γ wE (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω')
        (drawQ P η L N G γ wE ρr (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') d)
        (lossF P η L N G γ wE ρr ℓ rc0 s ω'
          (drawQ P η L N G γ wE ρr (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') d) yB)
        (drawQ P η L N G γ wE ρr (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') d))
  unfold ARp chX
  refine (Eq.trans (by convert key using 1) ?_)
  congr 1
  convert sum_draw η L N _ (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') hN0 hk (fun f => ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
    (pmarg η L (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') f *
      ixA η L N G γ wE (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') f
        (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f)) using 1
  rfl
theorem floor_div_ge (G : ℕ) (hG : 1 ≤ G) (v : ℝ) (hv : 0 ≤ v) : v - 1 / G ≤ ((⌊(G : ℝ) * v⌋₊ : ℕ) : ℝ) / G := by
  have hG' : (0 : ℝ) < G := by exact_mod_cast hG
  have h := Nat.lt_floor_add_one ((G : ℝ) * v)
  have h2 : (G : ℝ) * v - 1 ≤ ((⌊(G : ℝ) * v⌋₊ : ℕ) : ℝ) := by linarith
  calc v - 1 / G = ((G : ℝ) * v - 1) / G := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right h2 hG'.le

/-- **The conditional mean is at most `1`** (before learner time `2^L`). -/
theorem meanA_le_one (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr))
    (hk : (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    meanA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN s ω' ≤ 1 := by
  rw [meanA_eq P η L N G γ wE ρr ℓ ωs φ rc0 hL hN s ω' hk]
  have h1 : (withAlg P η L N G γ wE ρr).wE = wE := hwE
  rw [h1]
  set σ := σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω'
  set V := VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω'
  have hμ := Pool.P0092.sum_toReal_one (withAlg P η L N G γ wE ρr).AB.μ
  have hterm : ∀ f, ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
      (pmarg η L σ V f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f) ≤
      pmarg η L σ V f / wE := by
    intro f
    have hpt : 0 ≤ ptA η L N σ V f := Pool.P0179.pt_nonneg _
    have hpm : 0 ≤ pmarg η L σ V f := pmarg_nonneg _ _ _ _ _
    have hden : 0 < wE * (ptA η L N σ V f + γ) := by positivity
    have hix : ∀ yB, ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f ≤
        1 / (wE * (ptA η L N σ V f + γ)) := by
      intro yB
      unfold ixA; rw [if_pos rfl]
      have hb : ((lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB).toNat : ℝ) ≤ 1 := by
        cases lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB <;> simp
      exact (floor_div_le G (by positivity)).trans (div_le_div_of_nonneg_right hb hden.le)
    calc ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
          (pmarg η L σ V f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f)
        ≤ ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
          (pmarg η L σ V f * (1 / (wE * (ptA η L N σ V f + γ)))) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun yB _ => mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hix yB) hpm) ENNReal.toReal_nonneg) hpt
      _ = pmarg η L σ V f / wE * (ptA η L N σ V f / (ptA η L N σ V f + γ)) := by
          rw [← Finset.sum_mul, hμ]; field_simp
      _ ≤ pmarg η L σ V f / wE * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = _ := mul_one _
  calc wE * ∑ f, ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
        (pmarg η L σ V f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f)
      ≤ wE * ∑ f, pmarg η L σ V f / wE :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun f _ => hterm f) hwE0.le
    _ = 1 := by rw [← Finset.sum_div, pmarg_sum η L σ V hk]; field_simp

/-- **The conditional mean misses the true policy loss by at most the rounding and IX biases.** -/
theorem aPolX_le_meanA (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hG : 1 ≤ G) (s : ℕ)
    (ω' : Fin s → RC (withAlg P η L N G γ wE ρr))
    (hk : (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    aPolX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' ≤ meanA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN s ω' +
      (((univ.erase none).filter fun f => pmarg η L (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω')
          (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') f ≠ 0).card / N +
        (univ.filter fun f => pmarg η L (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω')
          (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') f ≠ 0).card * (γ + 1 / N) + wE / G) := by
  have hN0 : 0 < N := hN
  rw [aPolX_eq P η L N G γ wE ρr ℓ ωs φ rc0 hN0 s ω' hk, meanA_eq P η L N G γ wE ρr ℓ ωs φ rc0 hL hN s ω' hk]
  have h1 : (withAlg P η L N G γ wE ρr).wE = wE := hwE
  rw [h1]
  set σ := σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω'
  set V := VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω'
  set p := pmarg η L σ V
  set lb := ℓbar P η L N G γ wE ρr ℓ rc0 s ω'
  have hμ := Pool.P0092.sum_toReal_one (withAlg P η L N G γ wE ρr).AB.μ
  have hp0 : ∀ f, 0 ≤ p f := pmarg_nonneg η L σ V
  have hp1 : ∑ f, p f = 1 := pmarg_sum η L σ V hk
  have hlb := ℓbar_mem P η L N G γ wE ρr ℓ rc0 s ω'
  have hterm : ∀ f, ptA η L N σ V f * p f * (lb f / (ptA η L N σ V f + γ)) - wE / G * (ptA η L N σ V f * p f) ≤
      wE * (ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
        (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f)) := by
    intro f
    have hpt : 0 ≤ ptA η L N σ V f := Pool.P0179.pt_nonneg _
    have hden : 0 < wE * (ptA η L N σ V f + γ) := by positivity
    have hix : ∀ yB, ((lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB).toNat : ℝ) / (wE * (ptA η L N σ V f + γ)) - 1 / G ≤
        ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f := by
      intro yB
      unfold ixA; rw [if_pos rfl]
      exact floor_div_ge G hG _ (by positivity)
    have hsum : ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
        (((lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB).toNat : ℝ) / (wE * (ptA η L N σ V f + γ)) - 1 / G) =
        lb f / (wE * (ptA η L N σ V f + γ)) - 1 / G := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hμ, one_mul]
      unfold lb ℓbar
      rw [Finset.sum_div]
      exact congrArg₂ _ (Finset.sum_congr rfl fun yB _ => by ring) rfl
    have hle : lb f / (wE * (ptA η L N σ V f + γ)) - 1 / G ≤ ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
        ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f := by
      rw [← hsum]
      exact Finset.sum_le_sum fun yB _ => mul_le_mul_of_nonneg_left (hix yB) ENNReal.toReal_nonneg
    have e : ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
        (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f) =
        p f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
          ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun yB _ => by ring
    rw [e]
    have hmul := mul_le_mul_of_nonneg_left hle (mul_nonneg hwE0.le (mul_nonneg hpt (hp0 f)))
    have e2 : wE * (ptA η L N σ V f * p f) * (lb f / (wE * (ptA η L N σ V f + γ)) - 1 / G) =
        ptA η L N σ V f * p f * (lb f / (ptA η L N σ V f + γ)) - wE / G * (ptA η L N σ V f * p f) := by
      field_simp
    rw [e2] at hmul
    calc _ ≤ _ := hmul
      _ = _ := by ring
  have hmean : ∑ f, ptA η L N σ V f * p f * (lb f / (ptA η L N σ V f + γ)) - wE / G ≤
      wE * ∑ f, ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
        (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f) := by
    have hptp : ∑ f, ptA η L N σ V f * p f ≤ 1 := by
      calc ∑ f, ptA η L N σ V f * p f ≤ ∑ f, 1 * p f := Finset.sum_le_sum fun f _ =>
            mul_le_mul_of_nonneg_right (by
              have hs := Pool.P0179.sum_pt (N := N) (b := (none : Option ι)) hN0 hp0 hp1
              have := Finset.single_le_sum (f := Pool.P0179.pt N none p) (fun g _ => Pool.P0179.pt_nonneg g)
                (Finset.mem_univ f)
              unfold ptA; linarith) (hp0 f)
        _ = 1 := by simp [hp1]
    have hwG : 0 ≤ wE / G := by positivity
    calc ∑ f, ptA η L N σ V f * p f * (lb f / (ptA η L N σ V f + γ)) - wE / G
        ≤ ∑ f, ptA η L N σ V f * p f * (lb f / (ptA η L N σ V f + γ)) - wE / G * ∑ f, ptA η L N σ V f * p f := by
          nlinarith
      _ = ∑ f, (ptA η L N σ V f * p f * (lb f / (ptA η L N σ V f + γ)) - wE / G * (ptA η L N σ V f * p f)) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ ≤ _ := by rw [Finset.mul_sum]; exact Finset.sum_le_sum fun f _ => hterm f
  have hpl := Pool.P0179.played_loss_le_supp (N := N) (b := (none : Option ι)) hN0 hp0 hp1 lb (fun f => (hlb f).1)
    (fun f => (hlb f).2)
  have hix := Pool.P0179.ix_bias_le_scaled (N := N) (b := (none : Option ι)) hN0 hp0 hp1 lb (fun f => (hlb f).1)
    (fun f => (hlb f).2) hγ one_pos
  have hsplit : ∑ f, ptA η L N σ V f * lb f - ∑ f, ptA η L N σ V f * p f * (lb f / (ptA η L N σ V f + γ)) =
      (∑ f, Pool.P0179.pt N none p f * lb f - ∑ f, p f * lb f) +
        ∑ f, p f * lb f * (γ / (1 * Pool.P0179.pt N none p f + γ)) := by
    have hpe : (fun f => ptA η L N σ V f) = Pool.P0179.pt N none p := rfl
    simp only [hpe]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    have hpt : 0 ≤ Pool.P0179.pt N none p f := Pool.P0179.pt_nonneg _
    have hd : 0 < Pool.P0179.pt N none p f + γ := by linarith
    rw [one_mul]
    field_simp
    ring
  have habs := (abs_le.mp hpl).2
  linarith

/-! ### Identification with the run -/
theorem σX_pre (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (u : ℕ) :
    σX P η L N G γ wE ρr ℓ ωs φ rc0 u (Pool.P0203.pre _ ω u) = sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u :=
  sA_congr ωs φ u (Pool.P0203.extD_pre_agree (withAlg P η L N G γ wE ρr) rc0 ω u)
theorem VX_pre (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (u : ℕ) :
    VX P η L N G γ wE ρr ℓ ωs φ rc0 u (Pool.P0203.pre _ ω u) = active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u :=
  active_congr ωs φ u (Pool.P0203.extD_pre_agree (withAlg P η L N G γ wE ρr) rc0 ω u)
theorem lossF_pre (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (u : ℕ) (f : Option ι)
    (yB : (withAlg P η L N G γ wE ρr).AB.Y) :
    lossF P η L N G γ wE ρr ℓ rc0 u (Pool.P0203.pre _ ω u) f yB =
      ℓ u (match f with
        | some x => (withAlg P η L N G γ wE ρr).arm x
        | none => (withAlg P η L N G γ wE ρr).AB.act 0 (sB (withAlg P η L N G γ wE ρr) ℓ ω u) yB) := by
  unfold lossF
  rw [sB_congr u (Pool.P0203.extD_pre_agree (withAlg P η L N G γ wE ρr) rc0 ω u)]

/-- **P0194's policy loss of this ALG is `aPolX` on the prefix.** -/
theorem aPol_eq_aPolX (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (u : ℕ) :
    aPol (withAlg P η L N G γ wE ρr) ℓ ωs φ ω u = aPolX P η L N G γ wE ρr ℓ ωs φ rc0 u (Pool.P0203.pre _ ω u) := by
  unfold aPolX ℓbar
  simp only [lossF_pre P η L N G γ wE ρr ℓ rc0 ω u]
  rw [σX_pre P η L N G γ wE ρr ℓ ωs φ rc0 ω u, VX_pre P η L N G γ wE ρr ℓ ωs φ rc0 ω u]
  unfold aPol drawQ
  simp only [Nat.cast_one]
  rfl

/-- **P0212's real-time learner loss is `ARp` on the prefix and the round's coin.** -/
theorem AR_eq_ARp (T : ℕ) (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) {u : ℕ} (hu : u < T) :
    AR P η L N G γ wE ρr ℓ ω ωs φ T u = ARp P η L N G γ wE ρr ℓ ωs φ rc0 u (Pool.P0203.pre _ ω u) (ω u) := by
  by_cases hg : gE P η L N G γ wE ρr ω u = true
  · rw [AR_eq P η L N G γ wE ρr ℓ ω ωs φ T hu hg]
    simp only [cuR_eq P η L N G γ wE ρr ℓ ω ωs φ T hu hg]
    have hgE : isE (withAlg P η L N G γ wE ρr) (ω u).1 = true := hg
    unfold ARp chX
    rw [if_pos hgE, σX_pre P η L N G γ wE ρr ℓ ωs φ rc0 ω u, VX_pre P η L N G γ wE ρr ℓ ωs φ rc0 ω u]
    rw [Finset.sum_eq_single (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)]
    · have hch : drawQ P η L N G γ wE ρr (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
          (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) (ω u).2.1 =
          algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u := rfl
      rw [hch, lossF_pre P η L N G γ wE ρr ℓ rc0 ω u]
      congr 2
    · intro f _ hf
      unfold ixA; rw [if_neg hf, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h1 : AR P η L N G γ wE ρr ℓ ω ωs φ T u = 0 := by unfold AR; rw [if_neg hg]
    have hgE : isE (withAlg P η L N G γ wE ρr) (ω u).1 = false := by unfold gE at hg; simpa using hg
    rw [h1]; unfold ARp; rw [if_neg (by simp [hgE])]

/-! ### The martingale `meanA − ARp` -/

/-- The centred increment (zero from learner time `2^L` on). -/
noncomputable def DA (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (s : ℕ) (ω : Fin (s + 1) → RC (withAlg P η L N G γ wE ρr)) : ℝ :=
  if (σX P η L N G γ wE ρr ℓ ωs φ rc0 s (Fin.init ω)).k < 2 ^ L then
    meanA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN s (Fin.init ω) -
      ARp P η L N G γ wE ρr ℓ ωs φ rc0 s (Fin.init ω) (ω (Fin.last s))
  else 0
theorem meanA_nonneg (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) :
    0 ≤ meanA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN s ω' :=
  Finset.sum_nonneg fun z _ => mul_nonneg ENNReal.toReal_nonneg
    (ARp_nonneg P η L N G γ wE ρr ℓ ωs φ rc0 hγ hwE0 s ω' z)

/-- **`DA` is a centred increment with range and variance proxy `Rm = (1 + 1/(Nγ))/wE`** (P0158's `IncrV`), and
`DA ≥ −Rm`. -/
theorem incrV_DA (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE1 : wE ≤ 1) (hwE : P.wE = wE) :
    Pool.P0158.IncrV (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
        (DA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN) (fun _ => (1 + 1 / (N * γ)) / wE)
        (fun _ => (1 + 1 / (N * γ)) / wE) ∧
      ∀ s (ω : Fin s → RC (withAlg P η L N G γ wE ρr)) z,
        -((1 + 1 / (N * γ)) / wE) ≤ DA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN s (Fin.snoc ω z) := by
  have hN0 : 0 < N := hN
  set Rm := (1 + 1 / (N * γ)) / wE with hRm
  have hRm1 : 1 ≤ Rm := by
    rw [hRm, le_div_iff₀ hwE0]
    have : 0 ≤ 1 / ((N : ℝ) * γ) := by positivity
    linarith
  have hν := Pool.P0092.sum_toReal_one (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
  refine ⟨⟨fun s ω z => ?_, fun s ω => ?_, fun s ω => ?_⟩, fun s ω z => ?_⟩
  · unfold DA
    simp only [Fin.init_snoc, Fin.snoc_last]
    split_ifs with hk
    · have h1 := meanA_le_one P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 hwE s ω hk
      have h2 := ARp_nonneg P η L N G γ wE ρr ℓ ωs φ rc0 hγ hwE0 s ω z
      linarith
    · linarith
  · unfold DA
    simp only [Fin.init_snoc, Fin.snoc_last]
    split_ifs with hk
    · rw [Finset.sum_congr rfl fun z _ => mul_sub _ _ _, Finset.sum_sub_distrib, ← Finset.sum_mul, hν, one_mul]
      unfold meanA; ring
    · simp
  · unfold DA
    simp only [Fin.init_snoc, Fin.snoc_last]
    split_ifs with hk
    · set m := meanA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN s ω
      have hm1 := meanA_le_one P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 hwE s ω hk
      have hm0 := meanA_nonneg P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 s ω
      have hA0 := ARp_nonneg P η L N G γ wE ρr ℓ ωs φ rc0 hγ hwE0 s ω
      have hA1 := ARp_le P η L N G γ wE ρr ℓ ωs φ rc0 hγ hwE0 hN0 s ω hk
      have e : ∑ z, (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
          (m - ARp P η L N G γ wE ρr ℓ ωs φ rc0 s ω z) ^ 2 =
          ∑ z, (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
            ARp P η L N G γ wE ρr ℓ ωs φ rc0 s ω z ^ 2 - m ^ 2 := by
        have e1 : ∀ z, (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
            (m - ARp P η L N G γ wE ρr ℓ ωs φ rc0 s ω z) ^ 2 =
            (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal * m ^ 2 -
              2 * m * ((Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
                ARp P η L N G γ wE ρr ℓ ωs φ rc0 s ω z) +
              (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
                ARp P η L N G γ wE ρr ℓ ωs φ rc0 s ω z ^ 2 := fun z => by ring
        rw [Finset.sum_congr rfl fun z _ => e1 z, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_mul, hν, ← Finset.mul_sum]
        show 1 * m ^ 2 - 2 * m * m + _ = _
        ring
      rw [e]
      have hsq : ∑ z, (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
          ARp P η L N G γ wE ρr ℓ ωs φ rc0 s ω z ^ 2 ≤ Rm * m := by
        rw [show Rm * m = ∑ z, (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
            (Rm * ARp P η L N G γ wE ρr ℓ ωs φ rc0 s ω z) by
          unfold m meanA; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring]
        exact Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (by nlinarith [hA0 z, hA1 z])
          ENNReal.toReal_nonneg
      nlinarith
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
      linarith
  · unfold DA
    simp only [Fin.init_snoc, Fin.snoc_last]
    split_ifs with hk
    · have h1 := meanA_nonneg P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 s ω
      have h2 := ARp_le P η L N G γ wE ρr ℓ ωs φ rc0 hγ hwE0 hN0 s ω hk z
      linarith
    · linarith

open Classical in
/-- **The good event of `DA` fails with probability `≤ 2(T+1)²e^{−Lc}`.** -/
theorem prob_not_goodDA (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE1 : wE ≤ 1) (hwE : P.wE = wE) {Lc : ℝ} (hLc : 0 < Lc) (T : ℕ) :
    (∑ ω' : Fin T → RC (withAlg P η L N G γ wE ρr), Pool.P0092.wgt (Pool.P0203.nuD _ hL hN) ω' *
      if Pool.P0158.GoodV (DA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN) (fun _ _ => true)
        (fun _ => (1 + 1 / (N * γ)) / wE) (fun _ _ => (1 + 1 / (N * γ)) / wE) Lc T ω' then (0 : ℝ) else 1) ≤
      2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) := by
  have hN0 : 0 < N := hN
  obtain ⟨hD, hlow⟩ := incrV_DA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 hwE1 hwE
  have hRm : 0 < (1 + 1 / ((N : ℝ) * γ)) / wE := by positivity
  exact Pool.P0158.prob_not_goodV _ _ _ hD hlow (fun _ => hRm.le) _ (fun _ _ => hRm) (fun _ _ _ _ _ => le_rfl) hLc T

/-- The bias of round `u` (rounding of the draw, IX bias, grid rounding), on the support of the learner's marginal. -/
noncomputable def biasR (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (u : ℕ) : ℝ :=
  (((univ.erase none).filter fun f => pmarg η L (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
      (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) f ≠ 0).card / N +
    (univ.filter fun f => pmarg η L (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
      (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) f ≠ 0).card * (γ + 1 / N) + wE / G)

/-- **`htrue` on the actual run, interval form** (not P0186's field; see `htrue_const`): on `DA`'s good event, for
`[a, b) ⊆ [0, T)`, `T ≤ 2^L`: `Σ aPol ≤ Σ AR + widV((b−a)·Rm, Rm, Lc) + Σ biasR`, `Rm = (1 + 1/(Nγ))/wE`. -/
theorem htrue_run (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hG : 1 ≤ G) {Lc : ℝ} (T : ℕ) (hTL : T ≤ 2 ^ L)
    (ω : ℕ → RC (withAlg P η L N G γ wE ρr))
    (hgood : Pool.P0158.GoodV (DA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN) (fun _ _ => true)
      (fun _ => (1 + 1 / (N * γ)) / wE) (fun _ _ => (1 + 1 / (N * γ)) / wE) Lc T (Pool.P0203.pre _ ω T))
    (a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T) :
    ∑ u ∈ Finset.Ico a b, aPol (withAlg P η L N G γ wE ρr) ℓ ωs φ ω u ≤
      ∑ u ∈ Finset.Ico a b, AR P η L N G γ wE ρr ℓ ω ωs φ T u +
        Pool.P0158.widV (∑ _s ∈ Finset.Ico a b, (1 + 1 / (N * γ)) / wE) ((1 + 1 / (N * γ)) / wE) Lc +
        ∑ u ∈ Finset.Ico a b, biasR P η L N G γ wE ρr ℓ ωs φ ω u := by
  classical
  have hk : ∀ u, u < T → (σX P η L N G γ wE ρr ℓ ωs φ rc0 u (Pool.P0203.pre _ ω u)).k < 2 ^ L := by
    intro u hu
    rw [σX_pre P η L N G γ wE ρr ℓ ωs φ rc0 ω u, sA_k]
    have : kE P η L N G γ wE ρr ω u ≤ u := by
      unfold kE; exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  have h := hgood a b hab hbT
  rw [runSum_pre_gen] at h
  have hconv : (∑ u ∈ Finset.range T, if a ≤ u ∧ u < b ∧
      (fun (_ : ℕ) (_ : Fin _ → RC (withAlg P η L N G γ wE ρr)) => true) u (Pool.P0203.pre _ ω u) = true then
        DA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN u (Pool.P0203.pre _ ω (u + 1)) else 0) =
      ∑ u ∈ Finset.Ico a b, (meanA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN u (Pool.P0203.pre _ ω u) -
        AR P η L N G γ wE ρr ℓ ω ωs φ T u) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le a) (show a ≤ T by omega),
      ← Finset.sum_Ico_consecutive _ hab hbT]
    rw [Finset.sum_eq_zero (fun u hu => by simp at hu; simp [show ¬ a ≤ u by omega]),
      Finset.sum_eq_zero (s := Finset.Ico b T) (fun u hu => by simp at hu; simp [show ¬ u < b by omega])]
    simp only [zero_add, add_zero]
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Finset.mem_Ico] at hu
    have huT : u < T := by omega
    simp only [hu.1, hu.2, and_self, if_true]
    unfold DA
    rw [Pool.P0203.init_pre, if_pos (hk u huT), AR_eq_ARp P η L N G γ wE ρr ℓ ωs φ rc0 T ω huT]
    rfl
  rw [hconv] at h
  have hD := (abs_lt.mp h).2
  have hpt : ∀ u ∈ Finset.Ico a b, aPol (withAlg P η L N G γ wE ρr) ℓ ωs φ ω u ≤
      meanA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN u (Pool.P0203.pre _ ω u) +
        biasR P η L N G γ wE ρr ℓ ωs φ ω u := by
    intro u hu
    simp only [Finset.mem_Ico] at hu
    rw [aPol_eq_aPolX P η L N G γ wE ρr ℓ ωs φ rc0 ω u]
    have := aPolX_le_meanA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 hwE hG u (Pool.P0203.pre _ ω u)
      (hk u (by omega))
    unfold biasR
    rw [σX_pre P η L N G γ wE ρr ℓ ωs φ rc0 ω u, VX_pre P η L N G γ wE ρr ℓ ωs φ rc0 ω u] at this
    exact this
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_sub_distrib] at hD
  linarith

/-- `widV` is monotone in the total variance (for `L ≥ 0`). -/
theorem widV_mono {V V' ρ L : ℝ} (hV : V ≤ V') (hL : 0 ≤ L) : Pool.P0158.widV V ρ L ≤ Pool.P0158.widV V' ρ L := by
  unfold Pool.P0158.widV
  have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hV hL)
  linarith

/-- **`htrue` with one constant slack on `[0, T]`** (the shape of P0186's `ActHyp.htrue`, restricted to intervals inside
the horizon): on `DA`'s good event, for every `[a, b) ⊆ [0, T)`,
`Σ_{[a,b)} aPol ≤ Σ_{[a,b)} AR + Ψ` with `Ψ = widV(T·Rm, Rm, Lc) + Σ_{u<T} biasR u` (independent of `a`, `b`). -/
theorem htrue_const (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hG : 1 ≤ G) {Lc : ℝ} (hLc : 0 ≤ Lc) (T : ℕ) (hTL : T ≤ 2 ^ L)
    (ω : ℕ → RC (withAlg P η L N G γ wE ρr))
    (hgood : Pool.P0158.GoodV (DA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN) (fun _ _ => true)
      (fun _ => (1 + 1 / (N * γ)) / wE) (fun _ _ => (1 + 1 / (N * γ)) / wE) Lc T (Pool.P0203.pre _ ω T))
    (a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T) :
    ∑ u ∈ Finset.Ico a b, aPol (withAlg P η L N G γ wE ρr) ℓ ωs φ ω u ≤
      ∑ u ∈ Finset.Ico a b, AR P η L N G γ wE ρr ℓ ω ωs φ T u +
        (Pool.P0158.widV (T * ((1 + 1 / (N * γ)) / wE)) ((1 + 1 / (N * γ)) / wE) Lc +
          ∑ u ∈ Finset.range T, biasR P η L N G γ wE ρr ℓ ωs φ ω u) := by
  have h := htrue_run P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 hwE hG T hTL ω hgood a b hab hbT
  have hRm : 0 ≤ (1 + 1 / ((N : ℝ) * γ)) / wE := by positivity
  have hW : Pool.P0158.widV (∑ _s ∈ Finset.Ico a b, (1 + 1 / (N * γ)) / wE) ((1 + 1 / (N * γ)) / wE) Lc ≤
      Pool.P0158.widV (T * ((1 + 1 / (N * γ)) / wE)) ((1 + 1 / (N * γ)) / wE) Lc := by
    refine widV_mono ?_ hLc
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have : ((b - a : ℕ) : ℝ) ≤ T := by exact_mod_cast (show b - a ≤ T by omega)
    nlinarith
  have hB : ∑ u ∈ Finset.Ico a b, biasR P η L N G γ wE ρr ℓ ωs φ ω u ≤
      ∑ u ∈ Finset.range T, biasR P η L N G γ wE ρr ℓ ωs φ ω u := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) (fun u _ _ => ?_)
    · simp only [Finset.mem_Ico, Finset.mem_range] at hu ⊢; omega
    · unfold biasR; positivity
  linarith

/-! ### The learner's second moment (the `Σ V` budget) -/

/-- The learner's estimated second moment in round `s` with coin `z`. -/
noncomputable def VRp (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) (z : RC (withAlg P η L N G γ wE ρr)) :
    ℝ :=
  if isE (withAlg P η L N G γ wE ρr) z.1 = true then
    pmarg η L (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω')
        (chX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z) *
      ixA η L N G γ wE (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω')
        (chX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z)
        (lossF P η L N G γ wE ρr ℓ rc0 s ω' (chX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z) z.2.2.1)
        (chX P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z) ^ 2
  else 0

/-- **P0212's real-time second moment is `VRp` on the prefix and the round's coin.** -/
theorem VR_eq_VRp (T : ℕ) (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) {u : ℕ} (hu : u < T) :
    VR P η L N G γ wE ρr ℓ ω ωs φ T u = VRp P η L N G γ wE ρr ℓ ωs φ rc0 u (Pool.P0203.pre _ ω u) (ω u) := by
  by_cases hg : gE P η L N G γ wE ρr ω u = true
  · rw [VR_eq P η L N G γ wE ρr ℓ ω ωs φ T hu hg]
    simp only [cuR_eq P η L N G γ wE ρr ℓ ω ωs φ T hu hg]
    have hgE : isE (withAlg P η L N G γ wE ρr) (ω u).1 = true := hg
    unfold VRp chX
    rw [if_pos hgE, σX_pre P η L N G γ wE ρr ℓ ωs φ rc0 ω u, VX_pre P η L N G γ wE ρr ℓ ωs φ rc0 ω u]
    rw [Finset.sum_eq_single (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)]
    · have hch : drawQ P η L N G γ wE ρr (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
          (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) (ω u).2.1 =
          algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u := rfl
      rw [hch, lossF_pre P η L N G γ wE ρr ℓ rc0 ω u]
      congr 3
    · intro f _ hf
      unfold ixA; rw [if_neg hf]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h1 : VR P η L N G γ wE ρr ℓ ω ωs φ T u = 0 := by unfold VR; rw [if_neg hg]
    have hgE : isE (withAlg P η L N G γ wE ρr) (ω u).1 = false := by unfold gE at hg; simpa using hg
    rw [h1]; unfold VRp; rw [if_neg (by simp [hgE])]

/-- **Conditional mean of the second moment**: `E[VRp] ≤ #supp·(1 + 1/(4Nγ))/wE` before learner time `2^L`. -/
theorem meanV_le (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr))
    (hk : (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    ∑ z, (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal * VRp P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z ≤
      (univ.filter fun f => pmarg η L (σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω')
        (VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω') f ≠ 0).card * (1 + 1 / (4 * N * γ)) / wE := by
  have hN0 : 0 < N := hN
  have h1 : (withAlg P η L N G γ wE ρr).wE = wE := hwE
  set σ := σX P η L N G γ wE ρr ℓ ωs φ rc0 s ω'
  set V := VX P η L N G γ wE ρr ℓ ωs φ rc0 s ω'
  set p := pmarg η L σ V
  have hp0 : ∀ f, 0 ≤ p f := pmarg_nonneg η L σ V
  have hp1 : ∑ f, p f = 1 := pmarg_sum η L σ V hk
  have hμ := Pool.P0092.sum_toReal_one (withAlg P η L N G γ wE ρr).AB.μ
  have key := sum_wR_exploit2 (withAlg P η L N G γ wE ρr) (fun d yB =>
    p (drawQ P η L N G γ wE ρr σ V d) *
      ixA η L N G γ wE σ V (drawQ P η L N G γ wE ρr σ V d)
        (lossF P η L N G γ wE ρr ℓ rc0 s ω' (drawQ P η L N G γ wE ρr σ V d) yB)
        (drawQ P η L N G γ wE ρr σ V d) ^ 2)
  have hmean : ∑ z, (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
      VRp P η L N G γ wE ρr ℓ ωs φ rc0 s ω' z =
      wE * ∑ f, ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
        (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f ^ 2) := by
    simp only [Pool.P0203.nuD_toReal]
    unfold VRp chX
    refine (Eq.trans (by convert key using 1) ?_)
    rw [h1]
    congr 1
    convert sum_draw η L N σ V hN0 hk (fun f => ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
      (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f ^ 2)) using 1
    rfl
  rw [hmean]
  have hsm := Pool.P0179.second_moment_le_scaled (N := N) (b := (none : Option ι)) hN0 hp0 hp1 (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_rfl) hγ one_pos
  have hterm : ∀ f, wE * (ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
      (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f ^ 2)) ≤
      (p f * (1 : ℝ) ^ 2 * (1 * Pool.P0179.pt N none p f / (1 * Pool.P0179.pt N none p f + γ) ^ 2)) / wE := by
    intro f
    have hpt : 0 ≤ ptA η L N σ V f := Pool.P0179.pt_nonneg _
    have hden : 0 < wE * (ptA η L N σ V f + γ) := by positivity
    have hix : ∀ yB, ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f ^ 2 ≤
        (1 / (wE * (ptA η L N σ V f + γ))) ^ 2 := by
      intro yB
      have h0 : 0 ≤ ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f := by
        unfold ixA; rw [if_pos rfl]; positivity
      have hle : ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f ≤
          1 / (wE * (ptA η L N σ V f + γ)) := by
        unfold ixA; rw [if_pos rfl]
        have hb : ((lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB).toNat : ℝ) ≤ 1 := by
          cases lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB <;> simp
        exact (floor_div_le G (by positivity)).trans (div_le_div_of_nonneg_right hb hden.le)
      exact pow_le_pow_left₀ h0 hle 2
    calc wE * (ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
          (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f ^ 2))
        ≤ wE * (ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
          (p f * (1 / (wE * (ptA η L N σ V f + γ))) ^ 2)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun yB _ =>
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hix yB) (hp0 f)) ENNReal.toReal_nonneg) hpt)
            hwE0.le
      _ = _ := by
          rw [← Finset.sum_mul, hμ]
          unfold ptA
          have hpe : Pool.P0179.pt N none (pmarg η L σ V) = Pool.P0179.pt N none p := rfl
          rw [hpe]
          field_simp
  calc wE * ∑ f, ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
        (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f ^ 2)
      = ∑ f, wE * (ptA η L N σ V f * ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
        (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρr ℓ rc0 s ω' f yB) f ^ 2)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ f, (p f * (1 : ℝ) ^ 2 * (1 * Pool.P0179.pt N none p f / (1 * Pool.P0179.pt N none p f + γ) ^ 2)) / wE :=
        Finset.sum_le_sum fun f _ => hterm f
    _ = (∑ f, p f * (fun _ => (1 : ℝ)) f ^ 2 * (1 * Pool.P0179.pt N none p f /
          (1 * Pool.P0179.pt N none p f + γ) ^ 2)) / wE := by rw [Finset.sum_div]
    _ ≤ _ := by
        rw [div_le_div_iff_of_pos_right hwE0]
        convert hsm using 2
        ring

end Pool.P0224
