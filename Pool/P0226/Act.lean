import Pool.P0224.True
import Pool.P0208.Tails
import Pool.P0216.BConc
import Pool.P0215.Interval
import Pool.P0218.RecUp

/-!
# P0186's per-run hypotheses `ActHyp` for P0194's process with P0212's ALG, on the good events
-/

namespace Pool.P0226

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0220 Pool.P0224

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (withAlg P η L N G γ wE ρr).K → ι → Bool) (T : ℕ)

/-- Learner data written by a state are zero after its learner time. -/
theorem sA_c_zero : ∀ u t, (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k ≤ t →
    (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).c t = fun _ => 0 := by
  intro u
  induction u with
  | zero => intro t _; rfl
  | succ u ih =>
    intro t ht
    rw [sA_k, kE_succ] at ht
    have hku := sA_k P η L N G γ wE ρr ℓ ω ωs φ u
    by_cases hE : isE (withAlg P η L N G γ wE ρr) (ω u).1 = true
    · rw [if_pos hE] at ht
      have hw := sA_frozen P η L N G γ wE ρr ℓ ω ωs φ (u + 1) (u + 1) le_rfl
      have hc : (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ (u + 1)).c =
          Function.update (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).c
            (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k
            (ixA η L N G γ wE (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
              (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
              (ℓ u (armOf (withAlg P η L N G γ wE ρr) ℓ ω u (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)))) := by
        conv_lhs => rw [show sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ (u + 1) =
          updA η L N G γ wE ρr (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
            (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) (ω u).2.1
            (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
            (ℓ u (armOf (withAlg P η L N G γ wE ρr) ℓ ω u (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u))) from by
          show (if isE (withAlg P η L N G γ wE ρr) (ω u).1 then _ else _) = _
          rw [if_pos hE]; rfl]
        rfl
      rw [hc, Function.update_of_ne (by omega)]
      exact ih t (by omega)
    · rw [if_neg hE] at ht
      have hs : sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ (u + 1) = sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u := by
        show (if isE (withAlg P η L N G γ wE ρr) (ω u).1 then _ else _) = _
        rw [if_neg hE]
      rw [hs]
      exact ih t (by omega)

theorem kE_le_of_le {u v : ℕ} (h : u ≤ v) : kE P η L N G γ wE ρr ω u ≤ kE P η L N G γ wE ρr ω v :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 h))

theorem cuR_zero_ge {u : ℕ} (hu : T ≤ u) (f : Option ι) : cuR P η L N G γ wE ρr ℓ ω ωs φ T u f = 0 := by
  unfold cuR; split_ifs
  · rw [sA_c_zero P η L N G γ wE ρr ℓ ω ωs φ T _ (by rw [sA_k]; exact kE_le_of_le P η L N G γ wE ρr ω hu)]
  · rfl

theorem AR_zero_ge {u : ℕ} (hu : T ≤ u) : AR P η L N G γ wE ρr ℓ ω ωs φ T u = 0 := by
  unfold AR Ap; split_ifs with h1 h2
  · exfalso
    have : (SF P η L N G γ wE ρr ℓ ω ωs φ T).k ≤ kE P η L N G γ wE ρr ω u := by
      rw [sA_k]; exact kE_le_of_le P η L N G γ wE ρr ω hu
    omega
  · rfl
  · rfl

theorem VR_zero_ge {u : ℕ} (hu : T ≤ u) : VR P η L N G γ wE ρr ℓ ω ωs φ T u = 0 := by
  unfold VR Vp; split_ifs with h1 h2
  · exfalso
    have : (SF P η L N G γ wE ρr ℓ ω ωs φ T).k ≤ kE P η L N G γ wE ρr ω u := by
      rw [sA_k]; exact kE_le_of_le P η L N G γ wE ρr ω hu
    omega
  · rfl
  · rfl

theorem cuR_nonneg (hγ : 0 < γ) (hwE : 0 < wE) (u : ℕ) (f : Option ι) :
    0 ≤ cuR P η L N G γ wE ρr ℓ ω ωs φ T u f := by
  unfold cuR; split_ifs
  · exact sA_c_nonneg P η L N G γ wE ρr ℓ ω ωs φ hγ hwE T _ f
  · exact le_rfl

theorem VR_nonneg (u : ℕ) : 0 ≤ VR P η L N G γ wE ρr ℓ ω ωs φ T u := by
  unfold VR Vp; split_ifs
  · exact Pool.P0138.palgVar_nonneg (fun _ => one_pos) _ _ _ _ _
  · exact le_rfl
  · exact le_rfl

/-- Sums of a sequence vanishing from `T` on stop at `T`. -/
theorem sum_trunc (F : ℕ → ℝ) (hF : ∀ u, T ≤ u → F u = 0) (s s' : ℕ) :
    ∑ u ∈ Ico s s', F u = ∑ u ∈ Ico s (min s' T), F u := by
  rcases le_total s' T with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    rcases le_total s T with hs | hs
    · rw [← Finset.sum_Ico_consecutive _ hs h, Finset.sum_eq_zero (s := Ico T s') (fun u hu => hF u
        (Finset.mem_Ico.mp hu).1), add_zero]
    · rw [Finset.Ico_eq_empty_of_le (show T ≤ s by omega), Finset.sum_empty]
      exact Finset.sum_eq_zero fun u hu => hF u (by simp at hu; omega)


/-- The constant of the learner hypothesis at horizon `T`. -/
noncomputable def αT (δ : ℝ) : ℝ := (2 * L + 1) * (Real.log (Fintype.card (Spec (Option ι) L)) + 2 * δ * T) / η

theorem αT_nonneg (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) : 0 ≤ αT (ι := ι) η L T δ := by
  unfold αT
  have : (0 : ℝ) ≤ Real.log (Fintype.card (Spec (Option ι) L)) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  positivity

/-- **Learner hypothesis on every interval** (P0186's `hL`/`hLB` shape, any `s ≤ s'`), for an expert present at the
exploitation rounds of `[s, s') ∩ [0, T)`. -/
theorem learner_all (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) (hρr : ∀ σ V, |ρr σ V| ≤ δ) (hγ : 0 < γ) (hwE : 0 < wE)
    (hTL : T ≤ 2 ^ L) (f : Option ι) (s s' : ℕ) (hss : s ≤ s')
    (hpres : ∀ u, s ≤ u → u < s' → u < T → gE P η L N G γ wE ρr ω u = true →
      presOf (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) f = true) :
    ∑ u ∈ Ico s s', AR P η L N G γ wE ρr ℓ ω ωs φ T u ≤
      ∑ u ∈ Ico s s', cuR P η L N G γ wE ρr ℓ ω ωs φ T u f + αT (ι := ι) η L T δ +
        ∑ u ∈ Ico s s', η / 2 * VR P η L N G γ wE ρr ℓ ω ωs φ T u := by
  rw [sum_trunc T _ (fun u hu => AR_zero_ge P η L N G γ wE ρr ℓ ω ωs φ T hu) s s',
    sum_trunc T _ (fun u hu => cuR_zero_ge P η L N G γ wE ρr ℓ ω ωs φ T hu f) s s',
    sum_trunc T _ (fun u hu => by rw [VR_zero_ge P η L N G γ wE ρr ℓ ω ωs φ T hu, mul_zero]) s s']
  have hα := αT_nonneg (ι := ι) η L T hη hδ
  by_cases hsm : s ≤ min s' T
  · have h := learner_hyp P η L N G γ wE ρr ℓ ω ωs φ T hη hδ hρr hγ hwE hTL f s (min s' T) hsm (min_le_right _ _)
      (fun u h1 h2 hg => hpres u h1 (by omega) (by omega) hg)
    have hk : ((SF P η L N G γ wE ρr ℓ ω ωs φ T).k : ℝ) ≤ T := by
      have : (SF P η L N G γ wE ρr ℓ ω ωs φ T).k ≤ T := by
        rw [sA_k]; unfold kE; exact (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast this
    have hαle : (2 * L + 1) * (Real.log (Fintype.card (Spec (Option ι) L)) +
        2 * δ * (SF P η L N G γ wE ρr ℓ ω ωs φ T).k) / η ≤ αT (ι := ι) η L T δ := by
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
noncomputable def ℓt (u : ℕ) (x : ι) : ℝ := if u < T then ℓr (withAlg P η L N G γ wE ρr) ℓ u x else 0

/-- Truncated BASE policy losses. -/
noncomputable def bPt (u : ℕ) : ℝ := if u < T then bPol (withAlg P η L N G γ wE ρr) ℓ ω u else 0

/-- Truncated ALG policy losses. -/
noncomputable def aPt (u : ℕ) : ℝ := if u < T then aPol (withAlg P η L N G γ wE ρr) ℓ ωs φ ω u else 0

theorem ℓt_nonneg (u : ℕ) (x : ι) : 0 ≤ ℓt P η L N G γ wE ρr ℓ T u x := by
  unfold ℓt ℓr; split_ifs <;> positivity

variable (rc0 : RC (withAlg P η L N G γ wE ρr))

/-- **IX one-sided bound on every interval** (P0186's `hIX`), for a copy active on `[s, s')`. -/
theorem ix_all (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hTL : T ≤ 2 ^ L) {Lc : ℝ} (hLc : 0 ≤ Lc)
    (hgood : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (lossX P η L N G γ wE ρr ℓ x)
      (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (f : ι) (s s' : ℕ) (hss : s ≤ s')
    (hact : ∀ u, s ≤ u → u < s' → f ∈ active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) :
    ∑ u ∈ Ico s s', cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some f) ≤
      ∑ u ∈ Ico s s', ℓt P η L N G γ wE ρr ℓ T u f + Lc / (2 * (wE * γ)) := by
  rw [sum_trunc T _ (fun u hu => cuR_zero_ge P η L N G γ wE ρr ℓ ω ωs φ T hu (some f)) s s',
    sum_trunc T _ (fun u hu => by unfold ℓt; rw [if_neg (by omega)]) s s']
  by_cases hsm : s ≤ min s' T
  · have h := ix_run P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 hwE T hTL ω f (hgood f) s (min s' T) hsm
      (min_le_right _ _)
    have e1 : ∑ u ∈ Ico s (min s' T), (if f ∈ active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u then
        cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some f) else 0) =
        ∑ u ∈ Ico s (min s' T), cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some f) :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; rw [if_pos (hact u hu.1 (by omega))]
    have e2 : ∑ u ∈ Ico s (min s' T), (if f ∈ active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u then
        ℓr (withAlg P η L N G γ wE ρr) ℓ u f else 0) =
        ∑ u ∈ Ico s (min s' T), ℓt P η L N G γ wE ρr ℓ T u f :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; rw [if_pos (hact u hu.1 (by omega))]; unfold ℓt; rw [if_pos (by omega)]
    rw [e1, e2] at h
    exact h.le
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp only [Finset.sum_empty, zero_add]
    exact div_nonneg hLc (by positivity)

/-- **IX bound of the meta-arm on every interval** (P0186's `hIXB` with `drawn = bPt`). -/
theorem ixm_all (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hTL : T ≤ 2 ^ L) {Lc : ℝ} (hLc : 0 ≤ Lc)
    (hgood : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
      (YB P η L N G γ wE ρr ℓ rc0) (bPolX P η L N G γ wE ρr ℓ rc0) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (s s' : ℕ) (hss : s ≤ s') :
    ∑ u ∈ Ico s s', cuR P η L N G γ wE ρr ℓ ω ωs φ T u none ≤
      ∑ u ∈ Ico s s', bPt P η L N G γ wE ρr ℓ ω T u + Lc / (2 * (wE * γ)) := by
  rw [sum_trunc T _ (fun u hu => cuR_zero_ge P η L N G γ wE ρr ℓ ω ωs φ T hu none) s s',
    sum_trunc T _ (fun u hu => by unfold bPt; rw [if_neg (by omega)]) s s']
  by_cases hsm : s ≤ min s' T
  · have h := ix_run_meta P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 hwE T hTL ω hgood s (min s' T) hsm
      (min_le_right _ _)
    have e2 : ∑ u ∈ Ico s (min s' T), bPol (withAlg P η L N G γ wE ρr) ℓ ω u =
        ∑ u ∈ Ico s (min s' T), bPt P η L N G γ wE ρr ℓ ω T u :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold bPt; rw [if_pos (by omega)]
    rw [e2] at h
    exact h.le
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp only [Finset.sum_empty, zero_add]
    exact div_nonneg hLc (by positivity)


theorem widV_mono2 {V V' ρ ρ' Lc : ℝ} (hV : 0 ≤ V) (hVV : V ≤ V') (hρ : ρ ≤ ρ') (hL : 0 ≤ Lc) :
    Pool.P0158.widV V ρ Lc ≤ Pool.P0158.widV V' ρ' Lc := by
  unfold Pool.P0158.widV
  have h1 : Real.sqrt (V * Lc) ≤ Real.sqrt (V' * Lc) := Real.sqrt_le_sqrt (by nlinarith)
  nlinarith

theorem widV_nonneg {V ρ Lc : ℝ} (hρ : 0 ≤ ρ) (hL : 0 ≤ Lc) : 0 ≤ Pool.P0158.widV V ρ Lc := by
  unfold Pool.P0158.widV; positivity

/-- **`htrue` on every interval** (P0186's `htrue`), with `Ψ = widV(T·Rm, Rm, Lc) + T·bmax`. -/
theorem htrue_all (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hG : 1 ≤ G) (hTL : T ≤ 2 ^ L) {Lc : ℝ} (hLc : 0 ≤ Lc)
    (hgood : Pool.P0158.GoodV (DA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN) (fun _ _ => true)
      (fun _ => (1 + 1 / (N * γ)) / wE) (fun _ _ => (1 + 1 / (N * γ)) / wE) Lc T (Pool.P0203.pre _ ω T))
    (bmax : ℝ) (hb0 : 0 ≤ bmax) (hbmax : ∀ u, u < T → biasR P η L N G γ wE ρr ℓ ωs φ ω u ≤ bmax)
    (s s' : ℕ) (hss : s ≤ s') :
    ∑ u ∈ Ico s s', aPt P η L N G γ wE ρr ℓ ω ωs φ T u ≤ ∑ u ∈ Ico s s', AR P η L N G γ wE ρr ℓ ω ωs φ T u +
      (Pool.P0158.widV (T * ((1 + 1 / (N * γ)) / wE)) ((1 + 1 / (N * γ)) / wE) Lc + T * bmax) := by
  have hN0 : 0 < N := hN
  have hRm : 0 ≤ (1 + 1 / ((N : ℝ) * γ)) / wE := by positivity
  rw [sum_trunc T _ (fun u hu => by unfold aPt; rw [if_neg (by omega)]) s s',
    sum_trunc T _ (fun u hu => AR_zero_ge P η L N G γ wE ρr ℓ ω ωs φ T hu) s s']
  have hΨ0 : 0 ≤ Pool.P0158.widV (T * ((1 + 1 / (N * γ)) / wE)) ((1 + 1 / (N * γ)) / wE) Lc + T * bmax :=
    add_nonneg (widV_nonneg hRm hLc) (by positivity)
  by_cases hsm : s ≤ min s' T
  · have h := htrue_run P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 hwE hG T hTL ω hgood s (min s' T) hsm
      (min_le_right _ _)
    have e1 : ∑ u ∈ Ico s (min s' T), aPt P η L N G γ wE ρr ℓ ω ωs φ T u =
        ∑ u ∈ Ico s (min s' T), aPol (withAlg P η L N G γ wE ρr) ℓ ωs φ ω u :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold aPt; rw [if_pos (by omega)]
    have hlen : ((min s' T - s : ℕ) : ℝ) ≤ T := by
      have : min s' T - s ≤ T := by omega
      exact_mod_cast this
    have hw : Pool.P0158.widV (∑ _s ∈ Ico s (min s' T), (1 + 1 / (N * γ)) / wE) ((1 + 1 / (N * γ)) / wE) Lc ≤
        Pool.P0158.widV (T * ((1 + 1 / (N * γ)) / wE)) ((1 + 1 / (N * γ)) / wE) Lc := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      exact widV_mono2 (by positivity) (mul_le_mul_of_nonneg_right hlen hRm) le_rfl hLc
    have hb : ∑ u ∈ Ico s (min s' T), biasR P η L N G γ wE ρr ℓ ωs φ ω u ≤ T * bmax := by
      calc ∑ u ∈ Ico s (min s' T), biasR P η L N G γ wE ρr ℓ ωs φ ω u ≤ ∑ _u ∈ Ico s (min s' T), bmax :=
            Finset.sum_le_sum fun u hu => hbmax u (by simp at hu; omega)
        _ = ((min s' T - s : ℕ) : ℝ) * bmax := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ T * bmax := mul_le_mul_of_nonneg_right hlen hb0
    rw [e1]
    linarith
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp only [Finset.sum_empty, zero_add]
    exact hΨ0

/-- **B̂ tail on every interval** (P0186's `hBh` with `bpol = bPt`, `Bhat = incBD`). -/
theorem bh_all (hcB0 : 0 ≤ (withAlg P η L N G γ wE ρr).cB) {Lb : ℝ} (hLb : 0 ≤ Lb)
    (hgood : Pool.P0158.GoodV (Pool.P0216.DB (withAlg P η L N G γ wE ρr) ℓ rc0) (fun _ _ => true)
      (fun _ => (withAlg P η L N G γ wE ρr).cB) (Pool.P0158.rmax1 (fun _ => (withAlg P η L N G γ wE ρr).cB)) Lb T
      (Pool.P0203.pre _ ω T))
    (s s' : ℕ) (hss : s ≤ s') :
    ∑ u ∈ Ico s s', bPt P η L N G γ wE ρr ℓ ω T u ≤
      ∑ u ∈ Ico s s', Pool.P0216.incBD (withAlg P η L N G γ wE ρr) ℓ ω u +
        Pool.P0158.widV ((s' - s : ℕ) * (withAlg P η L N G γ wE ρr).cB)
          (max 1 (withAlg P η L N G γ wE ρr).cB) Lb := by
  have hinc0 : ∀ u, 0 ≤ Pool.P0216.incBD (withAlg P η L N G γ wE ρr) ℓ ω u := by
    intro u; unfold Pool.P0216.incBD; split_ifs <;> positivity
  rw [sum_trunc T _ (fun u hu => by unfold bPt; rw [if_neg (by omega)]) s s']
  have hW0 : 0 ≤ Pool.P0158.widV ((s' - s : ℕ) * (withAlg P η L N G γ wE ρr).cB)
      (max 1 (withAlg P η L N G γ wE ρr).cB) Lb := widV_nonneg (by positivity) hLb
  have hmono : ∑ u ∈ Ico s (min s' T), Pool.P0216.incBD (withAlg P η L N G γ wE ρr) ℓ ω u ≤
      ∑ u ∈ Ico s s', Pool.P0216.incBD (withAlg P η L N G γ wE ρr) ℓ ω u :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (min_le_left _ _)) fun u _ _ => hinc0 u
  by_cases hsm : s ≤ min s' T
  · have h := Pool.P0216.goodB_run (withAlg P η L N G γ wE ρr) ℓ rc0 ω T hgood s (min s' T) hsm (min_le_right _ _)
    have e1 : ∑ u ∈ Ico s (min s' T), bPt P η L N G γ wE ρr ℓ ω T u =
        ∑ u ∈ Ico s (min s' T), bPol (withAlg P η L N G γ wE ρr) ℓ ω u :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold bPt; rw [if_pos (by omega)]
    have hrm : Pool.P0158.rmax1 (fun _ => (withAlg P η L N G γ wE ρr).cB) s (min s' T) ≤
        max 1 (withAlg P η L N G γ wE ρr).cB := by
      unfold Pool.P0158.rmax1
      refine max_le_max le_rfl ?_
      have : ((Finset.Ico s (min s' T)).sup (fun _ => Real.toNNReal (withAlg P η L N G γ wE ρr).cB) : NNReal) ≤
          Real.toNNReal (withAlg P η L N G γ wE ρr).cB := Finset.sup_le fun _ _ => le_rfl
      calc (((Finset.Ico s (min s' T)).sup (fun _ => Real.toNNReal (withAlg P η L N G γ wE ρr).cB) : NNReal) : ℝ)
          ≤ (Real.toNNReal (withAlg P η L N G γ wE ρr).cB : ℝ) := by exact_mod_cast this
        _ = _ := Real.coe_toNNReal _ hcB0
    have hw : Pool.P0158.widV (∑ _s ∈ Ico s (min s' T), (withAlg P η L N G γ wE ρr).cB)
        (Pool.P0158.rmax1 (fun _ => (withAlg P η L N G γ wE ρr).cB) s (min s' T)) Lb ≤
        Pool.P0158.widV ((s' - s : ℕ) * (withAlg P η L N G γ wE ρr).cB) (max 1 (withAlg P η L N G γ wE ρr).cB) Lb := by
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
theorem incr_nonneg {xmin : ℝ} (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (withAlg P η L N G γ wE ρr).xr j)
    (u : ℕ) (f : ι) : 0 ≤ Pool.P0105.incrOf (Pool.P0208.dat (withAlg P η L N G γ wE ρr) ℓ ω ωs φ) u f := by
  unfold Pool.P0105.incrOf Pool.P0208.dat
  rw [Pool.P0156.gChat_succ]
  have hB : ((1 : ℕ) : ℝ) / xmin ≥ 1 := by rw [Nat.cast_one, ge_iff_le, le_div_iff₀ hxm]; linarith
  have hall : ∀ ret o, 0 ≤ Pool.P0176.dzIncO (withAlg P η L N G γ wE ρr).D 1 1 (withAlg P η L N G γ wE ρr).xr
      (ℓr (withAlg P η L N G γ wE ρr) ℓ) u ret o f := fun ret o =>
    (Pool.P0176.dzInc_bounds 1 1 (withAlg P η L N G γ wE ρr).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ) hxm hxr
      (fun u x => by unfold ℓr; positivity) (fun u x => by unfold ℓr; cases ℓ u _ <;> simp) zero_le_one
      (by linarith) u ret o f).1
  have h : 0 ≤ Pool.P0156.gInc (withAlg P η L N G γ wE ρr).E (withAlg P η L N G γ wE ρr).thr0
      (withAlg P η L N G γ wE ρr).θ
      (withAlg P η L N G γ wE ρr).R (withAlg P η L N G γ wE ρr).K (withAlg P η L N G γ wE ρr).D
      (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).Bt (withAlg P η L N G γ wE ρr).lev
      (Pool.P0176.dzUpd (withAlg P η L N G γ wE ρr).D (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl 1 1
        (withAlg P η L N G γ wE ρr).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ) (rhD (withAlg P η L N G γ wE ρr) ℓ ω)
        (withAlg P η L N G γ wE ρr).lay (zc (withAlg P η L N G γ wE ρr) ω)) ∅ ωs φ u f := hall _ _
  linarith

/-- **Slot lower tail on every interval** (P0186's `hlo`), for a copy present-and-active on `[s, s')`, on P0203's good
event and with every thread fitting before `T`. -/
theorem lo_all (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) {Ls xmin : ℝ} (hLs : 0 ≤ Ls)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (withAlg P η L N G γ wE ρr).xr j)
    (hgood : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (withAlg P η L N G γ wE ρr) ℓ ωs φ rc0 f)
      (Pool.P0203.gateS (withAlg P η L N G γ wE ρr) ℓ ωs φ rc0 f) (Pool.P0203.rS (withAlg P η L N G γ wE ρr) f)
      (Pool.P0158.rmax1 (Pool.P0203.rS (withAlg P η L N G γ wE ρr) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl
      (sp (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u))
    (f : ι) (s s' : ℕ) (hss : s ≤ s')
    (hP : Pool.P0186.PresAct (withAlg P η L N G γ wE ρr).E (withAlg P η L N G γ wE ρr).thr0
      (withAlg P η L N G γ wE ρr).θ (withAlg P η L N G γ wE ρr).R (withAlg P η L N G γ wE ρr).K
      (withAlg P η L N G γ wE ρr).D (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).Bt
      (withAlg P η L N G γ wE ρr).lev
      (Pool.P0176.dzUpd (withAlg P η L N G γ wE ρr).D (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl 1 1
        (withAlg P η L N G γ wE ρr).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ) (rhD (withAlg P η L N G γ wE ρr) ℓ ω)
        (withAlg P η L N G γ wE ρr).lay (zc (withAlg P η L N G γ wE ρr) ω)) ∅ ωs φ f s s') :
    ∑ u ∈ Ico s s', ℓt P η L N G γ wE ρr ℓ T u f ≤
      ∑ u ∈ Ico s s', Pool.P0105.incrOf (Pool.P0208.dat (withAlg P η L N G γ wE ρr) ℓ ω ωs φ) u f +
        (fun m : ℕ => 2 * √(Ls * ((m : ℝ) / xmin)) + 2 * Ls / xmin) (s' - s) := by
  obtain ⟨hWm, hW0⟩ := Pool.P0218.Wlen_mono_nonneg hLs hxm
  have hinc := incr_nonneg P η L N G γ wE ρr ℓ ω ωs φ hxm hxm1 hxr
  rw [sum_trunc T _ (fun u hu => by unfold ℓt; rw [if_neg (by omega)]) s s']
  have hmono : ∑ u ∈ Ico s (min s' T), Pool.P0105.incrOf (Pool.P0208.dat (withAlg P η L N G γ wE ρr) ℓ ω ωs φ) u f ≤
      ∑ u ∈ Ico s s', Pool.P0105.incrOf (Pool.P0208.dat (withAlg P η L N G γ wE ρr) ℓ ω ωs φ) u f :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (min_le_left _ _)) fun u _ _ => hinc u f
  by_cases hsm : s ≤ min s' T
  · have hP' : Pool.P0186.PresAct (withAlg P η L N G γ wE ρr).E (withAlg P η L N G γ wE ρr).thr0
        (withAlg P η L N G γ wE ρr).θ (withAlg P η L N G γ wE ρr).R (withAlg P η L N G γ wE ρr).K
        (withAlg P η L N G γ wE ρr).D (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).Bt
        (withAlg P η L N G γ wE ρr).lev
        (Pool.P0176.dzUpd (withAlg P η L N G γ wE ρr).D (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl 1 1
          (withAlg P η L N G γ wE ρr).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ) (rhD (withAlg P η L N G γ wE ρr) ℓ ω)
          (withAlg P η L N G γ wE ρr).lay (zc (withAlg P η L N G γ wE ρr) ω)) ∅ ωs φ f s (min s' T) :=
      ⟨fun u h1 h2 => hP.1 u h1 (by omega), fun u h1 h2 => hP.2 u h1 (by omega)⟩
    have h := Pool.P0208.hlo_len (withAlg P η L N G γ wE ρr) ℓ ω ωs φ hD hLv hlev rc0 hLs hxm hxm1 hxr T hgood hfit f
      hsm (min_le_right _ _) hP'
    have e1 : ∑ u ∈ Ico s (min s' T), ℓt P η L N G γ wE ρr ℓ T u f =
        ∑ u ∈ Ico s (min s' T), ℓr (withAlg P η L N G γ wE ρr) ℓ u f :=
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


/-- **P0186's per-run hypotheses `ActHyp` for P0194's process with P0212's ALG**, on the good events: P0203's slot
event with every thread fitting before `T`, P0216's B̂ event, P0220's IX events (copies and meta-arm) and P0224's
`DA` event, with the per-round bias of P0224 at most `bmax`. Sequences after `T` are truncated (`ℓt`, `aPt`, `bPt`;
the learner's `AR`, `cuR`, `VR` vanish there). Constants: `α = αT`, `Γ = Lc/(2wEγ)`,
`Ψ = widV(T·Rm, Rm, Lc) + T·bmax`, `W(m) = 2√(Ls·m/xmin) + 2Ls/xmin`, `WD = 0`, `WB(m) = widV(m·cB, max 1 cB, Lb)`. -/
theorem actHyp_alg (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N) (hη : 0 < η) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρr : ∀ σ V, |ρr σ V| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hG : 1 ≤ G)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (withAlg P η L N G γ wE ρr).cB)
    {Ls Lb Lc xmin : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ (withAlg P η L N G γ wE ρr).xr j)
    (hS : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (withAlg P η L N G γ wE ρr) ℓ ωs φ rc0 f)
      (Pool.P0203.gateS (withAlg P η L N G γ wE ρr) ℓ ωs φ rc0 f) (Pool.P0203.rS (withAlg P η L N G γ wE ρr) f)
      (Pool.P0158.rmax1 (Pool.P0203.rS (withAlg P η L N G γ wE ρr) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl
      (sp (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u))
    (hB : Pool.P0158.GoodV (Pool.P0216.DB (withAlg P η L N G γ wE ρr) ℓ rc0) (fun _ _ => true)
      (fun _ => (withAlg P η L N G γ wE ρr).cB) (Pool.P0158.rmax1 (fun _ => (withAlg P η L N G γ wE ρr).cB)) Lb T
      (Pool.P0203.pre _ ω T))
    (hX : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (lossX P η L N G γ wE ρr ℓ x)
      (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (hXm : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
      (YB P η L N G γ wE ρr ℓ rc0) (bPolX P η L N G γ wE ρr ℓ rc0) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (hA : Pool.P0158.GoodV (DA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN) (fun _ _ => true)
      (fun _ => (1 + 1 / (N * γ)) / wE) (fun _ _ => (1 + 1 / (N * γ)) / wE) Lc T (Pool.P0203.pre _ ω T))
    (bmax : ℝ) (hb0 : 0 ≤ bmax) (hbmax : ∀ u, u < T → biasR P η L N G γ wE ρr ℓ ωs φ ω u ≤ bmax) :
    Pool.P0186.ActHyp (withAlg P η L N G γ wE ρr).E (withAlg P η L N G γ wE ρr).thr0 (withAlg P η L N G γ wE ρr).θ
      (withAlg P η L N G γ wE ρr).R (withAlg P η L N G γ wE ρr).K (withAlg P η L N G γ wE ρr).D
      (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).Bt (withAlg P η L N G γ wE ρr).lev
      (Pool.P0176.dzUpd (withAlg P η L N G γ wE ρr).D (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl 1 1
        (withAlg P η L N G γ wE ρr).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ) (rhD (withAlg P η L N G γ wE ρr) ℓ ω)
        (withAlg P η L N G γ wE ρr).lay (zc (withAlg P η L N G γ wE ρr) ω)) ∅ ωs φ
      (ℓt P η L N G γ wE ρr ℓ T) (fun u x => cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some x))
      (AR P η L N G γ wE ρr ℓ ω ωs φ T) (aPt P η L N G γ wE ρr ℓ ω ωs φ T)
      (fun u => η / 2 * VR P η L N G γ wE ρr ℓ ω ωs φ T u) (fun u => cuR P η L N G γ wE ρr ℓ ω ωs φ T u none)
      (bPt P η L N G γ wE ρr ℓ ω T) (bPt P η L N G γ wE ρr ℓ ω T) (Pool.P0216.incBD (withAlg P η L N G γ wE ρr) ℓ ω)
      (αT (ι := ι) η L T δ) (Lc / (2 * (wE * γ)))
      (Pool.P0158.widV (T * ((1 + 1 / (N * γ)) / wE)) ((1 + 1 / (N * γ)) / wE) Lc + T * bmax)
      (fun m : ℕ => 2 * √(Ls * ((m : ℝ) / xmin)) + 2 * Ls / xmin) (fun _ => 0)
      (fun m : ℕ => Pool.P0158.widV (m * (withAlg P η L N G γ wE ρr).cB) (max 1 (withAlg P η L N G γ wE ρr).cB) Lb) where
  hL := fun f s s' hss hP => by
    have hact := (Pool.P0208.presAct_iff (withAlg P η L N G γ wE ρr) ℓ ω ωs φ hD hLv hlev f s s').1 hP
    exact learner_all P η L N G γ wE ρr ℓ ω ωs φ T hη hδ hρr hγ hwE0 hTL (some f) s s' hss
      (fun u h1 h2 _ _ => by simp [presOf, hact u h1 h2])
  hIX := fun f s s' hss hP => by
    have hact := (Pool.P0208.presAct_iff (withAlg P η L N G γ wE ρr) ℓ ω ωs φ hD hLv hlev f s s').1 hP
    exact ix_all P η L N G γ wE ρr ℓ ω ωs φ T rc0 hL hN hγ hwE0 hwE hTL hLc hX f s s' hss hact
  hlo := fun f s s' hss hP =>
    lo_all P η L N G γ wE ρr ℓ ω ωs φ T rc0 hD hLv hlev hLs hxm hxm1 hxr hS hfit f s s' hss hP
  hLB := fun s s' hss =>
    learner_all P η L N G γ wE ρr ℓ ω ωs φ T hη hδ hρr hγ hwE0 hTL none s s' hss (fun _ _ _ _ _ => rfl)
  hIXB := fun s s' hss => ixm_all P η L N G γ wE ρr ℓ ω ωs φ T rc0 hL hN hγ hwE0 hwE hTL hLc hXm s s' hss
  hDr := fun s s' _ => by simp
  hBh := fun s s' hss => bh_all P η L N G γ wE ρr ℓ ω T rc0 hcB0 hLb hB s s' hss
  htrue := fun s s' hss => htrue_all P η L N G γ wE ρr ℓ ω ωs φ T rc0 hL hN hγ hwE0 hwE hG hTL hLc hA bmax hb0 hbmax
    s s' hss
  hfake := fun f u hf => by
    rw [Pool.P0207.dz_incr_retired (hf := hf)]
    unfold bPt; split_ifs
    · exact (Pool.P0216.bPol_mem (withAlg P η L N G γ wE ρr) ℓ ω u).2
    · exact zero_le_one
  haux := fun u => Pool.P0215.aux_succ (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u

end Pool.P0226
