import Pool.P0228.ExpD

/-!
# P0228's `slot_expect` with a path-dependent ALG budget

P0228's `AlgOK` takes the variance budget `v` and the copy budgets `r` as fixed sequences. A learner's budget is
random (for P0212's ALG it is `(η/2)·VR + slack`, read from the path; see `Pool.P0233.vOK`). Here `v` and `r` are
functions of the coin path; the statement and the proof are P0228's.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065 Pool.P0228 Pool.P0210

namespace Pool.P0233

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
variable (rc₀ : RC P)

open Classical in
/-- **P0228's `slot_expect` with path-dependent `v` and `r`** (P0194's probing term in expectation, P0217's `slotT`
form, fixed sampling/filter bits). With
`κ = (Σ_j sl_j)(Σ_j x_j)` and `X₁ = Σ_s x_s`:
`slotT ≤ κ·Σ_u E[bPol_u − aPol_u] + E[[G]·restD] + (X₁ + κ)·T·(P(overflow) + |ι|·2(T+1)²e^{−L} + 2(T+1)²e^{−L}
+ P(¬AlgOK))`, where `G` = no overflow ∧ P0203's slot good event (all copies) ∧ P0216's `B̂` good event ∧ `AlgOK`. -/
theorem slot_expect_path (hL : P.IsLaw) (hN : 0 < P.N) (T : ℕ) (hT : 1 ≤ T) {L : ℝ} (hLp : 0 < L)
    (hB : 0 < P.Bmin) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j) (hxr1 : ∀ j, P.xr j ≤ 1)
    (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i) (hcw : P.cB * P.wB = 1) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (v : (ℕ → RC P) → ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ ω u, 0 ≤ v ω u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c)
    (r : (ℕ → RC P) → ι → ℕ → ℝ) :
    ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' * probeU P ℓ ωs φ (extR P rc₀ ω') u ≤
      ((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
            (bPol P ℓ (extR P rc₀ ω') u - aPol P ℓ ωs φ (extR P rc₀ ω') u)
        + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
            (if (∀ t < T, Fits P.Lv P.sl (sp P ℓ (extR P rc₀ ω) ωs φ t)) ∧
                (∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc₀ x) (Pool.P0203.gateS P ℓ ωs φ rc₀ x)
                  (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T ω) ∧
                Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc₀) (fun _ _ => true) (fun _ => P.cB)
                  (Pool.P0158.rmax1 (fun _ => P.cB)) L T ω ∧
                AlgOK P ℓ ωs φ T (v (extR P rc₀ ω)) ρ₀ c (r (extR P rc₀ ω))
                  (extR P rc₀ ω)
              then restD P ℓ ωs φ hD hLv hlev T L (v (extR P rc₀ ω)) ρ₀ c (r (extR P rc₀ ω))
                  (extR P rc₀ ω) else 0)
        + ((∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + (∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j)
            * T * ((∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
                (if ∀ t < T, Fits P.Lv P.sl (sp P ℓ (extR P rc₀ ω) ωs φ t) then 0 else 1))
              + Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L))
              + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)
              + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
                (if AlgOK P ℓ ωs φ T (v (extR P rc₀ ω)) ρ₀ c (r (extR P rc₀ ω))
                  (extR P rc₀ ω) then 0 else 1)) := by
  set κ := (∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j with hκdef
  have hκ : 0 ≤ κ := mul_nonneg (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _)
    (Finset.sum_nonneg fun j _ => (hxr j).le)
  have hcB : 0 ≤ P.cB := by linarith [(Pool.P0216.cB_ge_one P hL hcw).1]
  set Fit : (Fin T → RC P) → Prop := fun ω => ∀ t < T, Fits P.Lv P.sl (sp P ℓ (extR P rc₀ ω) ωs φ t)
  set GS : (Fin T → RC P) → Prop := fun ω => ∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc₀ x)
    (Pool.P0203.gateS P ℓ ωs φ rc₀ x) (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T ω
  set GB : (Fin T → RC P) → Prop := fun ω => Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc₀) (fun _ _ => true)
    (fun _ => P.cB) (Pool.P0158.rmax1 (fun _ => P.cB)) L T ω
  set GA : (Fin T → RC P) → Prop := fun ω => AlgOK P ℓ ωs φ T (v (extR P rc₀ ω)) ρ₀ c (r (extR P rc₀ ω))
                  (extR P rc₀ ω)
  have hstep := slot_expect_of P ℓ ωs φ rc₀ hL hN T κ hκ (fun ω => Fit ω ∧ GS ω ∧ GB ω ∧ GA ω)
    (fun ω => restD P ℓ ωs φ hD hLv hlev T L (v (extR P rc₀ ω)) ρ₀ c (r (extR P rc₀ ω))
                  (extR P rc₀ ω)) ?_
  · refine hstep.trans ?_
    have hX : 0 ≤ (∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + κ :=
      add_nonneg (Finset.sum_nonneg fun s _ => (hxr s.1).le) hκ
    have hcoef : 0 ≤ ((∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + κ) * T := mul_nonneg hX (Nat.cast_nonneg _)
    -- union bound for the bad event
    have hunion : ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if Fit ω ∧ GS ω ∧ GB ω ∧ GA ω then 0 else 1) ≤
        (∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if Fit ω then 0 else 1))
          + Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L))
          + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)
          + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if GA ω then 0 else 1) := by
      have hS : ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if GS ω then 0 else 1) ≤
          Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) := by
        have h := Pool.P0203.prob_not_goodDS_all P ℓ ωs φ rc₀ hL hN hD hLv hlev hlay hxr hxr1 hLp T
        simp_rw [wgt_eq_pw P hL hN] at h
        exact h
      have hBd : ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if GB ω then 0 else 1) ≤
          2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
        have h := Pool.P0216.prob_not_goodB P ℓ rc₀ hL hN hcw hLp T
        simp_rw [wgt_eq_pw P hL hN] at h
        exact h
      have hpt : ∀ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if Fit ω ∧ GS ω ∧ GB ω ∧ GA ω then 0 else 1) ≤
          Pool.P0202.pw (wR P) ω * (if Fit ω then 0 else 1) + Pool.P0202.pw (wR P) ω * (if GS ω then 0 else 1)
            + Pool.P0202.pw (wR P) ω * (if GB ω then 0 else 1) + Pool.P0202.pw (wR P) ω * (if GA ω then 0 else 1) := by
        intro ω
        have hp := pw_nonneg P hL ω
        rw [← mul_add, ← mul_add, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hp
        by_cases h1 : Fit ω <;> by_cases h2 : GS ω <;> by_cases h3 : GB ω <;> by_cases h4 : GA ω <;>
          simp only [h1, h2, h3, h4, and_self, and_true, and_false, ite_true, ite_false] <;>
          norm_num
      have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin T → RC P))) fun ω _ => hpt ω
      simp only [Finset.sum_add_distrib] at hsum
      linarith
    have := mul_le_mul_of_nonneg_left hunion hcoef
    linarith
  · -- the pathwise bound on the good event
    rintro ω ⟨hfit, hgS, hgB, hint, hA⟩
    have hpre := pre_extR P rc₀ ω
    have h := Pool.P0223.probe_credit_pathD P ℓ ωs φ hD hLv hlev rc₀ (extR P rc₀ ω) T hT hLp hB hlay
      hxr hanti hcB hΛ0 hfit (by rw [hpre]; exact hgS) (by rw [hpre]; exact hgB) (v (extR P rc₀ ω)) ρ₀ c (hv _) hρ₀ hc hint (r (extR P rc₀ ω)) hA
    unfold probeU restD
    unfold Pool.P0154.isum at h ⊢
    beta_reduce at h
    rw [Finset.range_eq_Ico] at h ⊢
    rw [hκdef]
    linarith

end Pool.P0233
