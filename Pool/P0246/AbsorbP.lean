import Pool.P0234.Absorb
import Pool.P0233.Path

/-!
# P0234's absorbed machine regret with PATH-DEPENDENT ALG budgets

P0234's `regret_le_absorbed` uses P0228's `slot_expect`, whose `AlgOK` takes a fixed variance budget `v` and fixed copy
budgets `r`. Here `v` and `r` may depend on the sampling/filter array and on the coin path (as P0212/P0225's ALG budget
`(η/2)·VR + slack⁺` does), via P0233's `slot_expect_path`.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065

namespace Pool.P0246

attribute [local instance] Pool.P0082.coinFintype

section Terms

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (hD : 0 < P.D) (hLv : 0 < P.Lv)
  (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (rc₀ : RC P) (T : ℕ) (L : ℝ) (v : (ℕ → RC P) → ℕ → ℝ) (ρ₀ c : ℝ)
  (r : (ℕ → RC P) → ι → ℕ → ℝ)

open Classical in
/-- The good-event part of P0228's `slot_expect`: `E_T[[G]·restD]`. -/
noncomputable def goodTermP : ℝ :=
  ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
    (if (∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t)) ∧
        (∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc₀ x) (Pool.P0203.gateS P ℓ ωs φ rc₀ x)
          (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T ω) ∧
        Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc₀) (fun _ _ => true) (fun _ => P.cB)
          (Pool.P0158.rmax1 (fun _ => P.cB)) L T ω ∧
        Pool.P0228.AlgOK P ℓ ωs φ T (v (Pool.P0210.extR P rc₀ ω)) ρ₀ c (r (Pool.P0210.extR P rc₀ ω))
          (Pool.P0210.extR P rc₀ ω)
      then Pool.P0228.restD P ℓ ωs φ hD hLv hlev T L (v (Pool.P0210.extR P rc₀ ω)) ρ₀ c
        (r (Pool.P0210.extR P rc₀ ω)) (Pool.P0210.extR P rc₀ ω) else 0)

open Classical in
/-- The failure part of P0228's `slot_expect`: `P(¬Fits) + |ι|·2(T+1)²e^{−L} + 2(T+1)²e^{−L} + P(¬AlgOK)`. -/
noncomputable def badTermP : ℝ :=
  (∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
      (if ∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t) then 0 else 1))
    + Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L))
    + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)
    + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
      (if Pool.P0228.AlgOK P ℓ ωs φ T (v (Pool.P0210.extR P rc₀ ω)) ρ₀ c (r (Pool.P0210.extR P rc₀ ω))
          (Pool.P0210.extR P rc₀ ω) then 0 else 1)

/-- P0233's `slot_expect_path` (P0228's `slot_expect` with path-dependent budgets `v`, `r`) with its right-hand side
named (`goodTermP`, `badTermP`). -/
theorem slot_expectP' (hL : P.IsLaw) (hN : 0 < P.N) (hT : 1 ≤ T) (hLp : 0 < L)
    (hB : 0 < P.Bmin) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j) (hxr1 : ∀ j, P.xr j ≤ 1)
    (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i) (hcw : P.cB * P.wB = 1) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (hv : ∀ ω u, 0 ≤ v ω u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) :
    ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
        Pool.P0228.probeU P ℓ ωs φ (Pool.P0210.extR P rc₀ ω') u ≤
      ((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
            (bPol P ℓ (Pool.P0210.extR P rc₀ ω') u - aPol P ℓ ωs φ (Pool.P0210.extR P rc₀ ω') u)
        + goodTermP P ℓ ωs φ hD hLv hlev rc₀ T L v ρ₀ c r
        + ((∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + (∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j)
            * T * badTermP P ℓ ωs φ rc₀ T L v ρ₀ c r :=
  Pool.P0233.slot_expect_path P ℓ ωs φ hD hLv hlev rc₀ hL hN T hT hLp hB hlay hxr hxr1 hanti hcw hΛ0 v ρ₀ c hv hρ₀ hc r

end Terms

open Pool.P0201

/-- **P0194's machine regret with the probing term bounded and the rate-increase multiplier absorbed, with
PATH-DEPENDENT ALG budgets.** Combining P0217's `regret_le_base`, P0233's `slot_expect_path` (for every
sampling/filter array; the variance budget `v` and the copy budgets `r` of P0228's `AlgOK` may depend on the array and
are read on the coin path `extR rc₀ ω`) and `absorb_le`, with `κ = (Σ_j sl_j)(Σ_j x_j)`, `X₁ = Σ_s x_s` and a best
arm `i` in hindsight:
`regret ≤ 1 + T·E_arr[ovf] + (wB + X₁ + κ)·regret(Sub(BASE, wB), ℓ(·+1), T)
 + E_arr[(1 − κ/wE)·algT_i + goodTermP + (X₁ + κ)·T·badTermP]`. With constant budgets this is P0234's
`regret_le_absorbed`. -/
theorem regret_le_absorbedP {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {m : MPar n ι}
    [NeZero n] {T : ℕ} (hI : m.Intended T) (hL : m.P.IsLaw) (hN : 0 < m.P.N) (ℓ : LossSeq n)
    (ω₀ : Yc m × Zc m) (rc₀ : RC m.P)
    (hD : 0 < m.P.D) (hLv : 0 < m.P.Lv) (hlev : ∀ r a, m.P.lev r a + 1 < m.P.Lv)
    (hT : 1 ≤ T) {L : ℝ} (hLp : 0 < L) (hB : 0 < m.P.Bmin) (hlay : Pool.P0191.LayOK m.P.sl m.P.lay)
    (hxr : ∀ j, 0 < m.P.xr j) (hxr1 : ∀ j, m.P.xr j ≤ 1) (hanti : ∀ i j : Fin m.P.D, i ≤ j → m.P.xr j ≤ m.P.xr i)
    (hcw : m.P.cB * m.P.wB = 1) (hΛ0 : ∀ x c, 0 ≤ m.P.Λ x c) (hwE : 0 < m.P.wE)
    (v : (Pool.P0116.Arr (pp m) T → Bool) → (ℕ → RC m.P) → ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ arr ω u, 0 ≤ v arr ω u)
    (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (r : (Pool.P0116.Arr (pp m) T → Bool) → (ℕ → RC m.P) → ι → ℕ → ℝ) :
    ∃ i : Fin n, bestLoss ℓ (T + 1) = cumLoss ℓ (T + 1) i ∧ regret (mach m).toMachine ℓ (T + 1) ≤
      1 + T * ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * Pool.P0217.ovf m T ℓ rc₀ arr +
        (m.P.wB + ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1
            + (∑ j : Fin m.P.D, (m.P.sl j : ℝ)) * ∑ j : Fin m.P.D, m.P.xr j) *
          regret (Pool.P0055.Sub m.P.AB.toMachine m.P.wB hL.1 (Pool.P0202.wB_le_one m.P hL)) (Pool.P0206.sh ℓ) T +
        ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
          ((1 - (∑ j : Fin m.P.D, (m.P.sl j : ℝ)) * (∑ j : Fin m.P.D, m.P.xr j) / m.P.wE) *
              Pool.P0217.algT m T ℓ rc₀ i arr
            + goodTermP m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
                (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) hD hLv hlev rc₀ T L (v arr) ρ₀ c (r arr)
            + ((∑ s : (Σ j : Fin m.P.D, Fin (m.P.sl j)), m.P.xr s.1)
                + (∑ j : Fin m.P.D, (m.P.sl j : ℝ)) * ∑ j : Fin m.P.D, m.P.xr j) * T *
              badTermP m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
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
          + goodTermP m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
              (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) hD hLv hlev rc₀ T L (v arr) ρ₀ c (r arr)
          + ((∑ s : (Σ j : Fin m.P.D, Fin (m.P.sl j)), m.P.xr s.1) + κ) * T *
            badTermP m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
              (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) rc₀ T L (v arr) ρ₀ c (r arr)
          + κ * RS := by
    intro arr
    have hs := slot_expectP' m.P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
      (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) hD hLv hlev rc₀ T L (v arr) ρ₀ c (r arr) hL hN hT hLp hB hlay hxr hxr1 hanti hcw
      hΛ0 (hv arr) hρ₀ hc
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

end Pool.P0246
