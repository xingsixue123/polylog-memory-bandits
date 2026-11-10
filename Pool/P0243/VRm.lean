import Pool.P0231.IXD
import Pool.P0224.True

/-!
# The learner's second moment `VR` of P0225's `withAlgG`: coin-model form and conditional mean
-/

namespace Pool.P0243

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0231

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (Pool.P0225.withAlgG P η L N G γ wE ρG).K → ι → Bool)
  (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

/-- The learner's state and active set after a prefix. -/
noncomputable abbrev σX (s : ℕ) (ω' : Fin s → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) : AState ι :=
  sAA P η L N G γ wE ρG ℓ ωs φ (Pool.P0203.extD _ rc0 ω') s
noncomputable abbrev VX (s : ℕ) (ω' : Fin s → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) : Finset ι :=
  active (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s

/-- The chosen expert with round coin `z`. -/
noncomputable def chX (s : ℕ) (ω' : Fin s → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (z : RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) :
    Option ι :=
  drawQ P η L N G γ wE ρG (σX P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρG ℓ ωs φ rc0 s ω') z.2.1

/-- The loss of expert `f` with BASE's action coin `yB` (the meta-arm plays BASE's action). -/
noncomputable def lossF (s : ℕ) (ω' : Fin s → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (f : Option ι)
    (yB : (Pool.P0225.withAlgG P η L N G γ wE ρG).AB.Y) : Bool :=
  ℓ s (match f with
    | some x => (Pool.P0225.withAlgG P η L N G γ wE ρG).arm x
    | none => (Pool.P0225.withAlgG P η L N G γ wE ρG).AB.act 0
        (sB (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ (Pool.P0203.extD _ rc0 ω') s) yB)

theorem σX_pre (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (u : ℕ) :
    σX P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre _ ω u) = sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u :=
  sA_congr ωs φ u (Pool.P0203.extD_pre_agree (Pool.P0225.withAlgG P η L N G γ wE ρG) rc0 ω u)
theorem VX_pre (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (u : ℕ) :
    VX P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre _ ω u) = active (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u :=
  active_congr ωs φ u (Pool.P0203.extD_pre_agree (Pool.P0225.withAlgG P η L N G γ wE ρG) rc0 ω u)
theorem lossF_pre (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (u : ℕ) (f : Option ι)
    (yB : (Pool.P0225.withAlgG P η L N G γ wE ρG).AB.Y) :
    lossF P η L N G γ wE ρG ℓ rc0 u (Pool.P0203.pre _ ω u) f yB =
      ℓ u (match f with
        | some x => (Pool.P0225.withAlgG P η L N G γ wE ρG).arm x
        | none => (Pool.P0225.withAlgG P η L N G γ wE ρG).AB.act 0 (sB (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u) yB) := by
  unfold lossF
  rw [sB_congr u (Pool.P0203.extD_pre_agree (Pool.P0225.withAlgG P η L N G γ wE ρG) rc0 ω u)]

/-- **P0194's policy loss of this ALG is `aPolX` on the prefix.** -/
noncomputable def VRp (s : ℕ) (ω' : Fin s → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (z : RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) :
    ℝ :=
  if isE (Pool.P0225.withAlgG P η L N G γ wE ρG) z.1 = true then
    pmarg η L (σX P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
        (chX P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z) *
      ixA η L N G γ wE (σX P η L N G γ wE ρG ℓ ωs φ rc0 s ω') (VX P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
        (chX P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z)
        (lossF P η L N G γ wE ρG ℓ rc0 s ω' (chX P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z) z.2.2.1)
        (chX P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z) ^ 2
  else 0

/-- **P0212's real-time second moment is `VRp` on the prefix and the round's coin.** -/
theorem VR_eq_VRp (T : ℕ) (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) {u : ℕ} (hu : u < T) :
    Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u = VRp P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre _ ω u) (ω u) := by
  by_cases hg : Pool.P0225.gE P η L N G γ wE ρG ω u = true
  · rw [Pool.P0225.VR_eq P η L N G γ wE ρG ℓ ω ωs φ T hu hg]
    simp only [Pool.P0225.cuR_eq P η L N G γ wE ρG ℓ ω ωs φ T hu hg]
    have hgE : isE (Pool.P0225.withAlgG P η L N G γ wE ρG) (ω u).1 = true := hg
    unfold VRp chX
    rw [if_pos hgE, σX_pre P η L N G γ wE ρG ℓ ωs φ rc0 ω u, VX_pre P η L N G γ wE ρG ℓ ωs φ rc0 ω u]
    rw [Finset.sum_eq_single (algCh (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)]
    · have hch : drawQ P η L N G γ wE ρG (sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
          (active (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u) (ω u).2.1 =
          algCh (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u := rfl
      rw [hch, lossF_pre P η L N G γ wE ρG ℓ rc0 ω u]
      congr 3
    · intro f _ hf
      unfold ixA; rw [if_neg hf]; ring
    · intro h; exact absurd (Finset.mem_univ _) h
  · have h1 : Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u = 0 := by unfold Pool.P0225.VR; rw [if_neg hg]
    have hgE : isE (Pool.P0225.withAlgG P η L N G γ wE ρG) (ω u).1 = false := by unfold Pool.P0225.gE at hg; simpa using hg
    rw [h1]; unfold VRp; rw [if_neg (by simp [hgE])]

/-- **Conditional mean of the second moment**: `E[VRp] ≤ #supp·(1 + 1/(4Nγ))/wE` before learner time `2^L`. -/
theorem meanV_le (hL : (Pool.P0225.withAlgG P η L N G γ wE ρG).IsLaw) (hN : 0 < (Pool.P0225.withAlgG P η L N G γ wE ρG).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (s : ℕ) (ω' : Fin s → RC (Pool.P0225.withAlgG P η L N G γ wE ρG))
    (hk : (σX P η L N G γ wE ρG ℓ ωs φ rc0 s ω').k < 2 ^ L) :
    ∑ z, (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN z).toReal * VRp P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z ≤
      (univ.filter fun f => pmarg η L (σX P η L N G γ wE ρG ℓ ωs φ rc0 s ω')
        (VX P η L N G γ wE ρG ℓ ωs φ rc0 s ω') f ≠ 0).card * (1 + 1 / (4 * N * γ)) / wE := by
  have hN0 : 0 < N := hN
  have h1 : (Pool.P0225.withAlgG P η L N G γ wE ρG).wE = wE := hwE
  set σ := σX P η L N G γ wE ρG ℓ ωs φ rc0 s ω'
  set V := VX P η L N G γ wE ρG ℓ ωs φ rc0 s ω'
  set p := pmarg η L σ V
  have hp0 : ∀ f, 0 ≤ p f := pmarg_nonneg η L σ V
  have hp1 : ∑ f, p f = 1 := pmarg_sum η L σ V hk
  have hμ := Pool.P0092.sum_toReal_one (Pool.P0225.withAlgG P η L N G γ wE ρG).AB.μ
  have key := Pool.P0224.sum_wR_exploit2 (Pool.P0225.withAlgG P η L N G γ wE ρG) (fun d yB =>
    p (drawQ P η L N G γ wE ρG σ V d) *
      ixA η L N G γ wE σ V (drawQ P η L N G γ wE ρG σ V d)
        (lossF P η L N G γ wE ρG ℓ rc0 s ω' (drawQ P η L N G γ wE ρG σ V d) yB)
        (drawQ P η L N G γ wE ρG σ V d) ^ 2)
  have hmean : ∑ z, (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN z).toReal *
      VRp P η L N G γ wE ρG ℓ ωs φ rc0 s ω' z =
      wE * ∑ f, ptA η L N σ V f * ∑ yB, ((Pool.P0225.withAlgG P η L N G γ wE ρG).AB.μ yB).toReal *
        (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB) f ^ 2) := by
    simp only [Pool.P0203.nuD_toReal]
    unfold VRp chX
    refine (Eq.trans (by convert key using 1) ?_)
    rw [h1]
    congr 1
    convert Pool.P0224.sum_draw η L N σ V hN0 hk (fun f => ∑ yB, ((Pool.P0225.withAlgG P η L N G γ wE ρG).AB.μ yB).toReal *
      (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB) f ^ 2)) using 1
    rfl
  rw [hmean]
  have hsm := Pool.P0179.second_moment_le_scaled (N := N) (b := (none : Option ι)) hN0 hp0 hp1 (fun _ => 1)
    (fun _ => zero_le_one) (fun _ => le_rfl) hγ one_pos
  have hterm : ∀ f, wE * (ptA η L N σ V f * ∑ yB, ((Pool.P0225.withAlgG P η L N G γ wE ρG).AB.μ yB).toReal *
      (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB) f ^ 2)) ≤
      (p f * (1 : ℝ) ^ 2 * (1 * Pool.P0179.pt N none p f / (1 * Pool.P0179.pt N none p f + γ) ^ 2)) / wE := by
    intro f
    have hpt : 0 ≤ ptA η L N σ V f := Pool.P0179.pt_nonneg _
    have hden : 0 < wE * (ptA η L N σ V f + γ) := by positivity
    have hix : ∀ yB, ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB) f ^ 2 ≤
        (1 / (wE * (ptA η L N σ V f + γ))) ^ 2 := by
      intro yB
      have h0 : 0 ≤ ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB) f := by
        unfold ixA; rw [if_pos rfl]; positivity
      have hle : ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB) f ≤
          1 / (wE * (ptA η L N σ V f + γ)) := by
        unfold ixA; rw [if_pos rfl]
        have hb : ((lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB).toNat : ℝ) ≤ 1 := by
          cases lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB <;> simp
        exact (Pool.P0220.floor_div_le G (by positivity)).trans (div_le_div_of_nonneg_right hb hden.le)
      exact pow_le_pow_left₀ h0 hle 2
    calc wE * (ptA η L N σ V f * ∑ yB, ((Pool.P0225.withAlgG P η L N G γ wE ρG).AB.μ yB).toReal *
          (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB) f ^ 2))
        ≤ wE * (ptA η L N σ V f * ∑ yB, ((Pool.P0225.withAlgG P η L N G γ wE ρG).AB.μ yB).toReal *
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
  calc wE * ∑ f, ptA η L N σ V f * ∑ yB, ((Pool.P0225.withAlgG P η L N G γ wE ρG).AB.μ yB).toReal *
        (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB) f ^ 2)
      = ∑ f, wE * (ptA η L N σ V f * ∑ yB, ((Pool.P0225.withAlgG P η L N G γ wE ρG).AB.μ yB).toReal *
        (p f * ixA η L N G γ wE σ V f (lossF P η L N G γ wE ρG ℓ rc0 s ω' f yB) f ^ 2)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ f, (p f * (1 : ℝ) ^ 2 * (1 * Pool.P0179.pt N none p f / (1 * Pool.P0179.pt N none p f + γ) ^ 2)) / wE :=
        Finset.sum_le_sum fun f _ => hterm f
    _ = (∑ f, p f * (fun _ => (1 : ℝ)) f ^ 2 * (1 * Pool.P0179.pt N none p f /
          (1 * Pool.P0179.pt N none p f + γ) ^ 2)) / wE := by rw [Finset.sum_div]
    _ ≤ _ := by
        rw [div_le_div_iff_of_pos_right hwE0]
        convert hsm using 2
        ring

end Pool.P0243
