import Pool.P0228.ExpD
import Pool.P0255.Probe2
import Pool.P0246.AbsorbP

/-!
# The expectation step and the machine-level bound with the refined remainder `restD2`

P0228's `AlgOK` takes the variance budget `v` and the copy budgets `r` as fixed sequences. A learner's budget is
random (for P0212's ALG it is `(η/2)·VR + slack`, read from the path; see `Pool.P0233.vOK`). Here `v` and `r` are
functions of the coin path (as in P0233/P0246), and the good-event remainder is P0255's refined `restD2` (with rate
floor `xf`) instead of P0228's `restD`. The proofs follow P0233's and P0246's, with P0255's `restD2` bound.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065 Pool.P0228 Pool.P0210

namespace Pool.P0258


variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
variable (rc₀ : RC P)

open Classical in
/-- **P0228's `slot_expect` with path-dependent `v` and `r`** (P0194's probing term in expectation, P0217's `slotT`
form, fixed sampling/filter bits). With
`κ = (Σ_j sl_j)(Σ_j x_j)` and `X₁ = Σ_s x_s`:
`slotT ≤ κ·Σ_u E[bPol_u − aPol_u] + E[[G]·restD2] + (X₁ + κ)·T·(P(overflow) + |ι|·2(T+1)²e^{−L} + 2(T+1)²e^{−L}
+ P(¬AlgOK))`, where `G` = no overflow ∧ P0203's slot good event (all copies) ∧ P0216's `B̂` good event ∧ `AlgOK`. -/
theorem slot_expect_path2 (hL : P.IsLaw) (hN : 0 < P.N) (T : ℕ) (hT : 1 ≤ T) {L : ℝ} (hLp : 0 < L)
    (hB : 0 < P.Bmin) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j) (hxr1 : ∀ j, P.xr j ≤ 1)
    (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i) (hcw : P.cB * P.wB = 1) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (v : (ℕ → RC P) → ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ ω u, 0 ≤ v ω u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c)
    (r : (ℕ → RC P) → ι → ℕ → ℝ) {xf : ℝ} (hfl : ∀ j, xf ≤ P.xr j) :
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
              then Pool.P0255.restD2 P ℓ ωs φ hD hLv hlev T L (v (extR P rc₀ ω)) ρ₀ c (r (extR P rc₀ ω)) xf
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
    (fun ω => Pool.P0255.restD2 P ℓ ωs φ hD hLv hlev T L (v (extR P rc₀ ω)) ρ₀ c (r (extR P rc₀ ω)) xf
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
    exact Pool.P0255.probe_le_restD2 P ℓ ωs φ hD hLv hlev rc₀ (extR P rc₀ ω) T hT hLp hB hlay hxr hanti hcB hΛ0
      hfit (by rw [hpre]; exact hgS) (by rw [hpre]; exact hgB) (v (extR P rc₀ ω)) ρ₀ c (hv _) hρ₀ hc hfl hint
      (r (extR P rc₀ ω)) hA

end Pool.P0258

namespace Pool.P0258

attribute [local instance] Pool.P0082.coinFintype

section Terms

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (hD : 0 < P.D) (hLv : 0 < P.Lv)
  (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (rc₀ : RC P) (T : ℕ) (L : ℝ) (v : (ℕ → RC P) → ℕ → ℝ) (ρ₀ c : ℝ)
  (r : (ℕ → RC P) → ι → ℕ → ℝ)

open Classical in
/-- The good-event part of `slot_expect_path2`: `E_T[[G]·restD2]` (P0255's refined remainder with rate floor `xf`). -/
noncomputable def goodTermP2 (xf : ℝ) : ℝ :=
  ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
    (if (∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t)) ∧
        (∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc₀ x) (Pool.P0203.gateS P ℓ ωs φ rc₀ x)
          (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T ω) ∧
        Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc₀) (fun _ _ => true) (fun _ => P.cB)
          (Pool.P0158.rmax1 (fun _ => P.cB)) L T ω ∧
        Pool.P0228.AlgOK P ℓ ωs φ T (v (Pool.P0210.extR P rc₀ ω)) ρ₀ c (r (Pool.P0210.extR P rc₀ ω))
          (Pool.P0210.extR P rc₀ ω)
      then Pool.P0255.restD2 P ℓ ωs φ hD hLv hlev T L (v (Pool.P0210.extR P rc₀ ω)) ρ₀ c
        (r (Pool.P0210.extR P rc₀ ω)) xf (Pool.P0210.extR P rc₀ ω) else 0)

/-- `slot_expect_path2` with its right-hand side named (`goodTermP2`, P0246's `badTermP`). -/
theorem slot_expectP2 (hL : P.IsLaw) (hN : 0 < P.N) (hT : 1 ≤ T) (hLp : 0 < L)
    (hB : 0 < P.Bmin) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j) (hxr1 : ∀ j, P.xr j ≤ 1)
    (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i) (hcw : P.cB * P.wB = 1) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (hv : ∀ ω u, 0 ≤ v ω u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) {xf : ℝ} (hfl : ∀ j, xf ≤ P.xr j) :
    ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
        Pool.P0228.probeU P ℓ ωs φ (Pool.P0210.extR P rc₀ ω') u ≤
      ((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
            (bPol P ℓ (Pool.P0210.extR P rc₀ ω') u - aPol P ℓ ωs φ (Pool.P0210.extR P rc₀ ω') u)
        + goodTermP2 P ℓ ωs φ hD hLv hlev rc₀ T L v ρ₀ c r xf
        + ((∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + (∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j)
            * T * Pool.P0246.badTermP P ℓ ωs φ rc₀ T L v ρ₀ c r :=
  slot_expect_path2 P ℓ ωs φ hD hLv hlev rc₀ hL hN T hT hLp hB hlay hxr hxr1 hanti hcw hΛ0 v ρ₀ c hv hρ₀ hc r hfl

end Terms

open Pool.P0201

/-- **P0194's machine regret with the probing term bounded and the rate-increase multiplier absorbed, with
PATH-DEPENDENT ALG budgets and P0255's refined remainder `restD2`.** Combining P0217's `regret_le_base`,
`slot_expectP2` (for every
sampling/filter array; the variance budget `v` and the copy budgets `r` of P0228's `AlgOK` may depend on the array and
are read on the coin path `extR rc₀ ω`) and `absorb_le`, with `κ = (Σ_j sl_j)(Σ_j x_j)`, `X₁ = Σ_s x_s` and a best
arm `i` in hindsight:
`regret ≤ 1 + T·E_arr[ovf] + (wB + X₁ + κ)·regret(Sub(BASE, wB), ℓ(·+1), T)
 + E_arr[(1 − κ/wE)·algT_i + goodTermP2 + (X₁ + κ)·T·badTermP]`. This is P0246's `regret_le_absorbedP` with
`goodTermP` replaced by `goodTermP2 ≤ goodTermP` (`goodTermP2_le`). -/
theorem regret_le_absorbedP2 {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {m : MPar n ι}
    [NeZero n] {T : ℕ} (hI : m.Intended T) (hL : m.P.IsLaw) (hN : 0 < m.P.N) (ℓ : LossSeq n)
    (ω₀ : Yc m × Zc m) (rc₀ : RC m.P)
    (hD : 0 < m.P.D) (hLv : 0 < m.P.Lv) (hlev : ∀ r a, m.P.lev r a + 1 < m.P.Lv)
    (hT : 1 ≤ T) {L : ℝ} (hLp : 0 < L) (hB : 0 < m.P.Bmin) (hlay : Pool.P0191.LayOK m.P.sl m.P.lay)
    (hxr : ∀ j, 0 < m.P.xr j) (hxr1 : ∀ j, m.P.xr j ≤ 1) (hanti : ∀ i j : Fin m.P.D, i ≤ j → m.P.xr j ≤ m.P.xr i)
    (hcw : m.P.cB * m.P.wB = 1) (hΛ0 : ∀ x c, 0 ≤ m.P.Λ x c) (hwE : 0 < m.P.wE)
    (v : (Pool.P0116.Arr (pp m) T → Bool) → (ℕ → RC m.P) → ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ arr ω u, 0 ≤ v arr ω u)
    (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (r : (Pool.P0116.Arr (pp m) T → Bool) → (ℕ → RC m.P) → ι → ℕ → ℝ)
    {xf : ℝ} (hfl : ∀ j, xf ≤ m.P.xr j) :
    ∃ i : Fin n, bestLoss ℓ (T + 1) = cumLoss ℓ (T + 1) i ∧ regret (mach m).toMachine ℓ (T + 1) ≤
      1 + T * ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * Pool.P0217.ovf m T ℓ rc₀ arr +
        (m.P.wB + ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1
            + (∑ j : Fin m.P.D, (m.P.sl j : ℝ)) * ∑ j : Fin m.P.D, m.P.xr j) *
          regret (Pool.P0055.Sub m.P.AB.toMachine m.P.wB hL.1 (Pool.P0202.wB_le_one m.P hL)) (Pool.P0206.sh ℓ) T +
        ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
          ((1 - (∑ j : Fin m.P.D, (m.P.sl j : ℝ)) * (∑ j : Fin m.P.D, m.P.xr j) / m.P.wE) *
              Pool.P0217.algT m T ℓ rc₀ i arr
            + goodTermP2 m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
                (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) hD hLv hlev rc₀ T L (v arr) ρ₀ c (r arr) xf
            + ((∑ s : (Σ j : Fin m.P.D, Fin (m.P.sl j)), m.P.xr s.1)
                + (∑ j : Fin m.P.D, (m.P.sl j : ℝ)) * ∑ j : Fin m.P.D, m.P.xr j) * T *
              Pool.P0246.badTermP m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
                (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) rc₀ T L (v arr) ρ₀ c (r arr)) := by
  obtain ⟨i, hbest, hi⟩ := Pool.P0217.regret_le_base hI hL hN ℓ ω₀ rc₀
  refine ⟨i, hbest, hi.trans ?_⟩
  set κ := (∑ j : Fin m.P.D, (m.P.sl j : ℝ)) * ∑ j : Fin m.P.D, m.P.xr j with hκdef
  have hκ : 0 ≤ κ := mul_nonneg (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _)
    (Finset.sum_nonneg fun j _ => (hxr j).le)
  set RS := regret (Pool.P0055.Sub m.P.AB.toMachine m.P.wB hL.1 (Pool.P0202.wB_le_one m.P hL)) (Pool.P0206.sh ℓ) T
  have hw0 : ∀ arr : Pool.P0116.Arr (pp m) T → Bool, 0 ≤ Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr := by
    intro arr
    refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) arr
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [m.hps.1, m.hq.1]
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [m.hps.2, m.hq.2]
  have hw1 : ∑ arr : Pool.P0116.Arr (pp m) T → Bool, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr = 1 :=
    Pool.P0048.sum_wtv _
  have harr : ∀ arr : Pool.P0116.Arr (pp m) T → Bool,
      Pool.P0217.algT m T ℓ rc₀ i arr + Pool.P0217.slotT m T ℓ rc₀ arr ≤
        (1 - κ / m.P.wE) * Pool.P0217.algT m T ℓ rc₀ i arr
          + goodTermP2 m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
              (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) hD hLv hlev rc₀ T L (v arr) ρ₀ c (r arr) xf
          + ((∑ s : (Σ j : Fin m.P.D, Fin (m.P.sl j)), m.P.xr s.1) + κ) * T *
            Pool.P0246.badTermP m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
              (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) rc₀ T L (v arr) ρ₀ c (r arr)
          + κ * RS := by
    intro arr
    have hs := slot_expectP2 m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
      (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) hD hLv hlev rc₀ T L (v arr) ρ₀ c (r arr) hL hN hT hLp hB hlay hxr hxr1 hanti hcw
      hΛ0 (hv arr) hρ₀ hc hfl
    have ha := Pool.P0234.absorb_le m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
      (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) rc₀ hL hN hwE T i κ hκ
    rw [Pool.P0228.slotT_eq]
    have e : Pool.P0217.algT m T ℓ rc₀ i arr = Pool.P0234.algTerm m.P (Pool.P0206.sh ℓ)
        (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) rc₀ T i := rfl
    rw [e]
    linarith
  have hsum := Finset.sum_le_sum fun arr (_ : arr ∈ Finset.univ) => mul_le_mul_of_nonneg_left (harr arr) (hw0 arr)
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul] at hsum
  have hkey : ∑ arr : Pool.P0116.Arr (pp m) T → Bool, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * (κ * RS) = κ * RS := by
    rw [← Finset.sum_mul, hw1, one_mul]
  simp only [mul_add, Finset.sum_add_distrib]
  nlinarith [hsum, hkey]


open Classical in
/-- **Never worse than P0246's `goodTermP`** (`restD2 ≤ restDcap ≤ restD` pointwise, P0255/P0239), for nonnegative
rates, margins, `ρ₀`, `c` and a law of round kinds. -/
theorem goodTermP2_le {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (hD : 0 < P.D) (hLv : 0 < P.Lv)
    (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (rc₀ : RC P) (T : ℕ) (L : ℝ) (v : (ℕ → RC P) → ℕ → ℝ) (ρ₀ c : ℝ)
    (r : (ℕ → RC P) → ι → ℕ → ℝ) (xf : ℝ) (hL : P.IsLaw) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) :
    goodTermP2 P ℓ ωs φ hD hLv hlev rc₀ T L v ρ₀ c r xf ≤ Pool.P0246.goodTermP P ℓ ωs φ hD hLv hlev rc₀ T L v ρ₀ c r := by
  unfold goodTermP2 Pool.P0246.goodTermP
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (Pool.P0228.pw_nonneg P hL ω)
  split_ifs
  · exact (Pool.P0255.restD2_le_restDcap P ℓ ωs φ hD hLv hlev hL.2.2.1 hΛ0 T L _ ρ₀ c hρ₀ hc _ xf _).trans
      (Pool.P0239.restDcap_le_restD P ℓ ωs φ hD hLv hlev hL.2.2.1 T L _ ρ₀ c _ _)
  · exact le_rfl

end Pool.P0258
