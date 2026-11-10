import Pool.P0231.IXD
import Pool.P0225.Learner
import Pool.P0226.Run
import Pool.P0228.ExpD
import Pool.P0208.Tails
import Pool.P0216.BConc
import Pool.P0215.Interval
import Pool.P0218.RecUp

/-!
# P0186's per-run hypotheses `ActHyp` for P0194's process with P0225's generalized ALG `withAlgG`, on the good events

P0226's run lemmas, ported from P0212's `withAlg` to P0225's `withAlgG` (P0225's learner, P0231's IX events). The
ALG-independent helpers (`sum_trunc`, `αT`, `widV_mono2`, `widV_nonneg`, `gT`) are P0226's, not redefined. P0226's
`htrue_all` (horizon-scale Ψ) is not ported: `ActOcc.lean` uses P0240's constant `Ψ = Lt/κ` instead.
-/

namespace Pool.P0242

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0231
open Pool.P0226 (sum_trunc αT αT_nonneg widV_mono2 widV_nonneg gT)

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (Pool.P0225.withAlgG P η L N G γ wE ρG).K → ι → Bool) (T : ℕ)

/-- Learner data written by a state are zero after its learner time. -/
theorem sA_c_zero : ∀ u t, (sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k ≤ t →
    (sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).c t = fun _ => 0 := by
  intro u
  induction u with
  | zero => intro t _; rfl
  | succ u ih =>
    intro t ht
    rw [Pool.P0225.sA_k, Pool.P0225.kE_succ] at ht
    have hku := Pool.P0225.sA_k P η L N G γ wE ρG ℓ ω ωs φ u
    by_cases hE : isE (Pool.P0225.withAlgG P η L N G γ wE ρG) (ω u).1 = true
    · rw [if_pos hE] at ht
      have hw := Pool.P0225.sA_frozen P η L N G γ wE ρG ℓ ω ωs φ (u + 1) (u + 1) le_rfl
      have hc : (sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ (u + 1)).c =
          Function.update (sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).c
            (sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k
            (ixA η L N G γ wE (sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
              (active (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u) (algCh (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
              (ℓ u (armOf (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u (algCh (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)))) := by
        conv_lhs => rw [show sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ (u + 1) =
          Pool.P0225.updAG η L N G γ wE ρG (sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
            (active (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u) (ω u).2.1
            (algCh (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
            (ℓ u (armOf (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u (algCh (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u))) from by
          show (if isE (Pool.P0225.withAlgG P η L N G γ wE ρG) (ω u).1 then _ else _) = _
          rw [if_pos hE]; rfl]
        rfl
      rw [hc, Function.update_of_ne (by omega)]
      exact ih t (by omega)
    · rw [if_neg hE] at ht
      have hs : sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ (u + 1) = sA (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u := by
        show (if isE (Pool.P0225.withAlgG P η L N G γ wE ρG) (ω u).1 then _ else _) = _
        rw [if_neg hE]
      rw [hs]
      exact ih t (by omega)

theorem kE_le_of_le {u v : ℕ} (h : u ≤ v) : Pool.P0225.kE P η L N G γ wE ρG ω u ≤ Pool.P0225.kE P η L N G γ wE ρG ω v :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

theorem cuR_zero_ge {u : ℕ} (hu : T ≤ u) (f : Option ι) : Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u f = 0 := by
  unfold Pool.P0225.cuR; split_ifs
  · rw [sA_c_zero P η L N G γ wE ρG ℓ ω ωs φ T _ (by rw [Pool.P0225.sA_k]; exact kE_le_of_le P η L N G γ wE ρG ω hu)]
  · rfl

theorem AR_zero_ge {u : ℕ} (hu : T ≤ u) : Pool.P0225.AR P η L N G γ wE ρG ℓ ω ωs φ T u = 0 := by
  unfold Pool.P0225.AR Pool.P0225.Ap; split_ifs with h1 h2
  · exfalso
    have : (Pool.P0225.SF P η L N G γ wE ρG ℓ ω ωs φ T).k ≤ Pool.P0225.kE P η L N G γ wE ρG ω u := by
      rw [Pool.P0225.sA_k]; exact kE_le_of_le P η L N G γ wE ρG ω hu
    omega
  · rfl
  · rfl

theorem VR_zero_ge {u : ℕ} (hu : T ≤ u) : Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u = 0 := by
  unfold Pool.P0225.VR Pool.P0225.Vp; split_ifs with h1 h2
  · exfalso
    have : (Pool.P0225.SF P η L N G γ wE ρG ℓ ω ωs φ T).k ≤ Pool.P0225.kE P η L N G γ wE ρG ω u := by
      rw [Pool.P0225.sA_k]; exact kE_le_of_le P η L N G γ wE ρG ω hu
    omega
  · rfl
  · rfl

theorem cuR_nonneg (hγ : 0 < γ) (hwE : 0 < wE) (u : ℕ) (f : Option ι) :
    0 ≤ Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u f := by
  unfold Pool.P0225.cuR; split_ifs
  · exact Pool.P0225.sA_c_nonneg P η L N G γ wE ρG ℓ ω ωs φ T _ f
  · exact le_rfl

theorem VR_nonneg (u : ℕ) : 0 ≤ Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u := by
  unfold Pool.P0225.VR Pool.P0225.Vp; split_ifs
  · exact Pool.P0138.palgVar_nonneg (fun _ => one_pos) _ _ _ _ _
  · exact le_rfl
  · exact le_rfl







/-- **Learner hypothesis on every interval** (P0186's `hL`/`hLB` shape, any `s ≤ s'`), for an expert present at the
exploitation rounds of `[s, s') ∩ [0, T)`. -/
theorem learner_all (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) (hρG : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ) (hwE : 0 < wE)
    (hTL : T ≤ 2 ^ L) (f : Option ι) (s s' : ℕ) (hss : s ≤ s')
    (hpres : ∀ u, s ≤ u → u < s' → u < T → Pool.P0225.gE P η L N G γ wE ρG ω u = true →
      presOf (active (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u) f = true) :
    ∑ u ∈ Ico s s', Pool.P0225.AR P η L N G γ wE ρG ℓ ω ωs φ T u ≤
      ∑ u ∈ Ico s s', Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u f + αT (ι := ι) η L T δ +
        ∑ u ∈ Ico s s', η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u := by
  rw [sum_trunc T _ (fun u hu => AR_zero_ge P η L N G γ wE ρG ℓ ω ωs φ T hu) s s',
    sum_trunc T _ (fun u hu => cuR_zero_ge P η L N G γ wE ρG ℓ ω ωs φ T hu f) s s',
    sum_trunc T _ (fun u hu => by rw [VR_zero_ge P η L N G γ wE ρG ℓ ω ωs φ T hu, mul_zero]) s s']
  have hα := αT_nonneg (ι := ι) η L T hη hδ
  by_cases hsm : s ≤ min s' T
  · have h := Pool.P0225.learner_hyp P η L N G γ wE ρG ℓ ω ωs φ T hη hδ hρG hTL f s (min s' T) hsm (min_le_right _ _)
      (fun u h1 h2 hg => hpres u h1 (by omega) (by omega) hg)
    have hk : ((Pool.P0225.SF P η L N G γ wE ρG ℓ ω ωs φ T).k : ℝ) ≤ T := by
      have : (Pool.P0225.SF P η L N G γ wE ρG ℓ ω ωs φ T).k ≤ T := by
        rw [Pool.P0225.sA_k]; unfold Pool.P0225.kE; exact (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have hαle : (2 * L + 1) * (Real.log (Fintype.card (Spec (Option ι) L)) +
        2 * δ * (Pool.P0225.SF P η L N G γ wE ρG ℓ ω ωs φ T).k) / η ≤ αT (ι := ι) η L T δ := by
      unfold αT
      apply div_le_div_of_nonneg_right _ hη.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    rw [← Finset.mul_sum]
    linarith
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp only [Finset.sum_empty, zero_add, add_zero]
    exact hα


/-- Truncated copy losses. -/
noncomputable def ℓt (u : ℕ) (x : ι) : ℝ := if u < T then ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ u x else 0

/-- Truncated BASE policy losses. -/
noncomputable def bPt (u : ℕ) : ℝ := if u < T then bPol (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u else 0

/-- Truncated ALG policy losses. -/
noncomputable def aPt (u : ℕ) : ℝ := if u < T then aPol (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ ω u else 0

theorem ℓt_nonneg (u : ℕ) (x : ι) : 0 ≤ ℓt P η L N G γ wE ρG ℓ T u x := by
  unfold ℓt ℓr; split_ifs <;> positivity

variable (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

/-- **IX one-sided bound on every interval** (P0186's `hIX`), for a copy active on `[s, s')`. -/
theorem ix_all (hL : (Pool.P0225.withAlgG P η L N G γ wE ρG).IsLaw) (hN : 0 < (Pool.P0225.withAlgG P η L N G γ wE ρG).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hTL : T ≤ 2 ^ L) {Lc : ℝ} (hLc : 0 ≤ Lc)
    (hgood : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN) (lossX P η L N G γ wE ρG ℓ x)
      (obsX P η L N G γ wE ρG ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρG ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (f : ι) (s s' : ℕ) (hss : s ≤ s')
    (hact : ∀ u, s ≤ u → u < s' → f ∈ active (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u) :
    ∑ u ∈ Ico s s', Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u (some f) ≤
      ∑ u ∈ Ico s s', ℓt P η L N G γ wE ρG ℓ T u f + Lc / (2 * (wE * γ)) := by
  rw [sum_trunc T _ (fun u hu => cuR_zero_ge P η L N G γ wE ρG ℓ ω ωs φ T hu (some f)) s s',
    sum_trunc T _ (fun u hu => by unfold ℓt; rw [if_neg (by omega)]) s s']
  by_cases hsm : s ≤ min s' T
  · have h := ix_run P η L N G γ wE ρG ℓ ωs φ rc0 hL hN hγ hwE0 hwE T hTL ω f (hgood f) s (min s' T) hsm
      (min_le_right _ _)
    have e1 : ∑ u ∈ Ico s (min s' T), (if f ∈ active (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u then
        Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u (some f) else 0) =
        ∑ u ∈ Ico s (min s' T), Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u (some f) :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; rw [if_pos (hact u hu.1 (by omega))]
    have e2 : ∑ u ∈ Ico s (min s' T), (if f ∈ active (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u then
        ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ u f else 0) =
        ∑ u ∈ Ico s (min s' T), ℓt P η L N G γ wE ρG ℓ T u f :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; rw [if_pos (hact u hu.1 (by omega))]; unfold ℓt; rw [if_pos (by omega)]
    rw [e1, e2] at h
    exact h.le
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp only [Finset.sum_empty, zero_add]
    exact div_nonneg hLc (by positivity)

/-- **IX bound of the meta-arm on every interval** (P0186's `hIXB` with `drawn = bPt`). -/
theorem ixm_all (hL : (Pool.P0225.withAlgG P η L N G γ wE ρG).IsLaw) (hN : 0 < (Pool.P0225.withAlgG P η L N G γ wE ρG).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hTL : T ≤ 2 ^ L) {Lc : ℝ} (hLc : 0 ≤ Lc)
    (hgood : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN)
      (YB P η L N G γ wE ρG ℓ rc0) (bPolX P η L N G γ wE ρG ℓ rc0) (obsX P η L N G γ wE ρG ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (s s' : ℕ) (hss : s ≤ s') :
    ∑ u ∈ Ico s s', Pool.P0225.cuR P η L N G γ wE ρG ℓ ω ωs φ T u none ≤
      ∑ u ∈ Ico s s', bPt P η L N G γ wE ρG ℓ ω T u + Lc / (2 * (wE * γ)) := by
  rw [sum_trunc T _ (fun u hu => cuR_zero_ge P η L N G γ wE ρG ℓ ω ωs φ T hu none) s s',
    sum_trunc T _ (fun u hu => by unfold bPt; rw [if_neg (by omega)]) s s']
  by_cases hsm : s ≤ min s' T
  · have h := ix_run_meta P η L N G γ wE ρG ℓ ωs φ rc0 hL hN hγ hwE0 hwE T hTL ω hgood s (min s' T) hsm
      (min_le_right _ _)
    have e2 : ∑ u ∈ Ico s (min s' T), bPol (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u =
        ∑ u ∈ Ico s (min s' T), bPt P η L N G γ wE ρG ℓ ω T u :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold bPt; rw [if_pos (by omega)]
    rw [e2] at h
    exact h.le
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp only [Finset.sum_empty, zero_add]
    exact div_nonneg hLc (by positivity)






/-- **B̂ tail on every interval** (P0186's `hBh` with `bpol = bPt`, `Bhat = incBD`). -/
theorem bh_all (hcB0 : 0 ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) {Lb : ℝ} (hLb : 0 ≤ Lb)
    (hgood : Pool.P0158.GoodV (Pool.P0216.DB (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ rc0) (fun _ _ => true)
      (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) (Pool.P0158.rmax1 (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)) Lb T
      (Pool.P0203.pre _ ω T))
    (s s' : ℕ) (hss : s ≤ s') :
    ∑ u ∈ Ico s s', bPt P η L N G γ wE ρG ℓ ω T u ≤
      ∑ u ∈ Ico s s', Pool.P0216.incBD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u +
        Pool.P0158.widV ((s' - s : ℕ) * (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)
          (max 1 (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) Lb := by
  have hinc0 : ∀ u, 0 ≤ Pool.P0216.incBD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u := by
    intro u; unfold Pool.P0216.incBD; split_ifs <;> positivity
  rw [sum_trunc T _ (fun u hu => by unfold bPt; rw [if_neg (by omega)]) s s']
  have hW0 : 0 ≤ Pool.P0158.widV ((s' - s : ℕ) * (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)
      (max 1 (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) Lb := widV_nonneg (by positivity) hLb
  have hmono : ∑ u ∈ Ico s (min s' T), Pool.P0216.incBD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u ≤
      ∑ u ∈ Ico s s', Pool.P0216.incBD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (min_le_left _ _)) fun u _ _ => hinc0 u
  by_cases hsm : s ≤ min s' T
  · have h := Pool.P0216.goodB_run (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ rc0 ω T hgood s (min s' T) hsm (min_le_right _ _)
    have e1 : ∑ u ∈ Ico s (min s' T), bPt P η L N G γ wE ρG ℓ ω T u =
        ∑ u ∈ Ico s (min s' T), bPol (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω u :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold bPt; rw [if_pos (by omega)]
    have hrm : Pool.P0158.rmax1 (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) s (min s' T) ≤
        max 1 (Pool.P0225.withAlgG P η L N G γ wE ρG).cB := by
      unfold Pool.P0158.rmax1
      refine max_le_max le_rfl ?_
      have : ((Finset.Ico s (min s' T)).sup (fun _ => Real.toNNReal (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) : NNReal) ≤
          Real.toNNReal (Pool.P0225.withAlgG P η L N G γ wE ρG).cB := Finset.sup_le fun _ _ => le_rfl
      calc (((Finset.Ico s (min s' T)).sup (fun _ => Real.toNNReal (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) : NNReal) : ℝ)
          ≤ (Real.toNNReal (Pool.P0225.withAlgG P η L N G γ wE ρG).cB : ℝ) := by exact_mod_cast this
        _ = _ := Real.coe_toNNReal _ hcB0
    have hw : Pool.P0158.widV (∑ _s ∈ Ico s (min s' T), (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)
        (Pool.P0158.rmax1 (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) s (min s' T)) Lb ≤
        Pool.P0158.widV ((s' - s : ℕ) * (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) (max 1 (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) Lb := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      refine widV_mono2 (by positivity) (mul_le_mul_of_nonneg_right ?_ hcB0) hrm hLb
      have : min s' T - s ≤ s' - s := by omega
      exact_mod_cast this
    rw [e1]
    have h2 := (abs_lt.mp h).1
    rw [Finset.sum_sub_distrib] at h2
    linarith
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp only [Finset.sum_empty]
    exact add_nonneg (Finset.sum_nonneg fun u _ => hinc0 u) hW0


/-- The pool data of a unit grow by a nonnegative increment. -/
theorem incr_nonneg {xmin : ℝ} (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).xr j)
    (u : ℕ) (f : ι) : 0 ≤ Pool.P0105.incrOf (Pool.P0208.dat (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ) u f := by
  unfold Pool.P0105.incrOf Pool.P0208.dat
  rw [Pool.P0156.gChat_succ]
  have hB : ((1 : ℕ) : ℝ) / xmin ≥ 1 := by rw [Nat.cast_one, ge_iff_le, le_div_iff₀ hxm]; linarith
  have hall : ∀ ret o, 0 ≤ Pool.P0176.dzIncO (Pool.P0225.withAlgG P η L N G γ wE ρG).D 1 1 (Pool.P0225.withAlgG P η L N G γ wE ρG).xr
      (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ) u ret o f := fun ret o =>
    (Pool.P0176.dzInc_bounds 1 1 (Pool.P0225.withAlgG P η L N G γ wE ρG).xr (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ) hxm hxr
      (fun u x => by unfold ℓr; positivity) (fun u x => by unfold ℓr; cases ℓ u _ <;> simp) zero_le_one
      (by linarith) u ret o f).1
  have h : 0 ≤ Pool.P0156.gInc (Pool.P0225.withAlgG P η L N G γ wE ρG).E (Pool.P0225.withAlgG P η L N G γ wE ρG).thr0
      (Pool.P0225.withAlgG P η L N G γ wE ρG).θ
      (Pool.P0225.withAlgG P η L N G γ wE ρG).R (Pool.P0225.withAlgG P η L N G γ wE ρG).K (Pool.P0225.withAlgG P η L N G γ wE ρG).D
      (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).Bt (Pool.P0225.withAlgG P η L N G γ wE ρG).lev
      (Pool.P0176.dzUpd (Pool.P0225.withAlgG P η L N G γ wE ρG).D (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl 1 1
        (Pool.P0225.withAlgG P η L N G γ wE ρG).xr (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ) (rhD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω)
        (Pool.P0225.withAlgG P η L N G γ wE ρG).lay (zc (Pool.P0225.withAlgG P η L N G γ wE ρG) ω)) ∅ ωs φ u f := hall _ _
  linarith

/-- **Slot lower tail on every interval** (P0186's `hlo`), for a copy present-and-active on `[s, s')`, on P0203's good
event and with every thread fitting before `T`. -/
theorem lo_all (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) {Ls xmin : ℝ} (hLs : 0 ≤ Ls)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).xr j)
    (hgood : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ rc0 f)
      (Pool.P0203.gateS (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ rc0 f) (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) f)
      (Pool.P0158.rmax1 (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl
      (sp (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u))
    (f : ι) (s s' : ℕ) (hss : s ≤ s')
    (hP : Pool.P0186.PresAct (Pool.P0225.withAlgG P η L N G γ wE ρG).E (Pool.P0225.withAlgG P η L N G γ wE ρG).thr0
      (Pool.P0225.withAlgG P η L N G γ wE ρG).θ (Pool.P0225.withAlgG P η L N G γ wE ρG).R (Pool.P0225.withAlgG P η L N G γ wE ρG).K
      (Pool.P0225.withAlgG P η L N G γ wE ρG).D (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).Bt
      (Pool.P0225.withAlgG P η L N G γ wE ρG).lev
      (Pool.P0176.dzUpd (Pool.P0225.withAlgG P η L N G γ wE ρG).D (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl 1 1
        (Pool.P0225.withAlgG P η L N G γ wE ρG).xr (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ) (rhD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω)
        (Pool.P0225.withAlgG P η L N G γ wE ρG).lay (zc (Pool.P0225.withAlgG P η L N G γ wE ρG) ω)) ∅ ωs φ f s s') :
    ∑ u ∈ Ico s s', ℓt P η L N G γ wE ρG ℓ T u f ≤
      ∑ u ∈ Ico s s', Pool.P0105.incrOf (Pool.P0208.dat (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ) u f +
        (fun m : ℕ => 2 * √(Ls * ((m : ℝ) / xmin)) + 2 * Ls / xmin) (s' - s) := by
  obtain ⟨hWm, hW0⟩ := Pool.P0218.Wlen_mono_nonneg hLs hxm
  have hinc := incr_nonneg P η L N G γ wE ρG ℓ ω ωs φ hxm hxm1 hxr
  rw [sum_trunc T _ (fun u hu => by unfold ℓt; rw [if_neg (by omega)]) s s']
  have hmono : ∑ u ∈ Ico s (min s' T), Pool.P0105.incrOf (Pool.P0208.dat (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ) u f ≤
      ∑ u ∈ Ico s s', Pool.P0105.incrOf (Pool.P0208.dat (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ) u f :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (min_le_left _ _)) fun u _ _ => hinc u f
  by_cases hsm : s ≤ min s' T
  · have hP' : Pool.P0186.PresAct (Pool.P0225.withAlgG P η L N G γ wE ρG).E (Pool.P0225.withAlgG P η L N G γ wE ρG).thr0
        (Pool.P0225.withAlgG P η L N G γ wE ρG).θ (Pool.P0225.withAlgG P η L N G γ wE ρG).R (Pool.P0225.withAlgG P η L N G γ wE ρG).K
        (Pool.P0225.withAlgG P η L N G γ wE ρG).D (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).Bt
        (Pool.P0225.withAlgG P η L N G γ wE ρG).lev
        (Pool.P0176.dzUpd (Pool.P0225.withAlgG P η L N G γ wE ρG).D (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl 1 1
          (Pool.P0225.withAlgG P η L N G γ wE ρG).xr (ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ) (rhD (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω)
          (Pool.P0225.withAlgG P η L N G γ wE ρG).lay (zc (Pool.P0225.withAlgG P η L N G γ wE ρG) ω)) ∅ ωs φ f s (min s' T) :=
      ⟨fun u h1 h2 => hP.1 u h1 (by omega), fun u h1 h2 => hP.2 u h1 (by omega)⟩
    have h := Pool.P0208.hlo_len (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ hD hLv hlev rc0 hLs hxm hxm1 hxr T hgood hfit f
      hsm (min_le_right _ _) hP'
    have e1 : ∑ u ∈ Ico s (min s' T), ℓt P η L N G γ wE ρG ℓ T u f =
        ∑ u ∈ Ico s (min s' T), ℓr (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ u f :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold ℓt; rw [if_pos (by omega)]
    have hW : (fun m : ℕ => 2 * √(Ls * ((m : ℝ) / xmin)) + 2 * Ls / xmin) (min s' T - s) ≤
        (fun m : ℕ => 2 * √(Ls * ((m : ℝ) / xmin)) + 2 * Ls / xmin) (s' - s) := hWm (by omega)
    rw [e1]
    simp only at hW h ⊢
    linarith
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp only [Finset.sum_empty]
    exact add_nonneg (Finset.sum_nonneg fun u _ => hinc u f) (hW0 _)


end Pool.P0242
