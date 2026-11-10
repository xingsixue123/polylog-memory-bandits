import Pool.P0092.Azuma
import Pool.P0016.Machine

/-!
# Freedman (variance-adaptive) bound for adapted sums of i.i.d. coins (P0064 / P0092 coin representation)

P0092 gives Azuma–Hoeffding for adapted sums of i.i.d. coins `ω : Fin t → Z` (weights `wgt ν ω = Π ν(ω j)`, which
is P0064's `QCoinAlg.W`). Its bound depends on the range `b` of the increments. For importance-weighted estimates
the range is `1/r` (probe rate `r`) while the conditional variance is only about `1/r`, so a range-based bound
loses a factor `√(1/r)`. This file gives the variance-adaptive (Freedman) version, the coin analogue of P0039.

* `runV vD t ω`: running sum of predictable variance budgets `vD s (ω restricted to rounds < s)`.
* `expSum_freedman_le`: `Σ_ω wgt ω · exp(κ·runSum − κ²·runV) ≤ 1`.
* **`freedman_coins`**: if, on every positive-weight prefix of length `s < T`, the increment satisfies `κ·D ≤ 1`
  (upper bound only) for every coin value of positive mass, has conditional mean `≤ 0` and conditional second
  moment `≤ vD s ω`, then `P(runSum − κ·runV ≥ x/κ) ≤ exp(−x)`.
  The hypotheses are required only on positive-weight prefixes and rounds `s < T` (no extension of `D` needed).
* `freedman_coins_delta`: `P(runSum − κ·runV ≥ log(1/δ)/κ) ≤ δ`.
* Importance-weighted instance (`ν = Pool.P0016.bern r`, estimate `ĉ_s = c_s·1[coin]/r`, `c_s ∈ [0,1]`):
  `iw_under` (truth − estimate, `0 < κ ≤ 1`), `iw_over` (estimate − truth, `0 < κ ≤ r`): with weight `≥ 1 − δ`,
  the error is `≤ κT/r + log(1/δ)/κ`; `iw_under_tuned`: underestimation `≤ 2√(T log(1/δ)/r)` when
  `r log(1/δ) ≤ T`; `iw_over_tuned`: overestimation `≤ 2√(T log(1/δ)/r)` when `log(1/δ) ≤ r T` (stronger).
  The range-based bound (P0092 with `b = 1/r`) gives `√(4T log(1/δ))/r`, a factor `√(1/r)` larger.
-/


open Finset Real
open scoped ENNReal

namespace Pool.P0100

open Pool.P0092

variable {Z : Type} [Fintype Z] (ν : PMF Z)

/-- Running sum of predictable variance budgets: `vD s` reads only the coins of rounds `< s`. -/
def runV (vD : (s : ℕ) → (Fin s → Z) → ℝ) : (t : ℕ) → (Fin t → Z) → ℝ
  | 0, _ => 0
  | t + 1, ω => runV vD t (Fin.init ω) + vD t (Fin.init ω)

/-- **Exponential supermartingale** `exp(κ·runSum − κ²·runV)`. -/
theorem expSum_freedman_le (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (vD : (s : ℕ) → (Fin s → Z) → ℝ)
    {κ : ℝ} {T : ℕ}
    (hbd : ∀ s < T, ∀ (ω : Fin s → Z) z, wgt ν ω ≠ 0 → ν z ≠ 0 → κ * D s (Fin.snoc ω z) ≤ 1)
    (hmean : ∀ s < T, ∀ ω : Fin s → Z, wgt ν ω ≠ 0 →
      κ * ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ≤ 0)
    (hvar : ∀ s < T, ∀ ω : Fin s → Z, wgt ν ω ≠ 0 →
      ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ^ 2 ≤ vD s ω) :
    ∀ t ≤ T, ∑ ω : Fin t → Z, wgt ν ω * exp (κ * runSum D t ω - κ ^ 2 * runV vD t ω) ≤ 1 := by
  intro t
  induction t with
  | zero => intro _; simp [wgt, runSum, runV]
  | succ t ih =>
    intro htT
    rw [Pool.P0064.sum_split, Finset.sum_comm]
    calc ∑ ω' : Fin t → Z, ∑ z, wgt ν (Fin.snoc ω' z) *
          exp (κ * runSum D (t + 1) (Fin.snoc ω' z) - κ ^ 2 * runV vD (t + 1) (Fin.snoc ω' z))
        = ∑ ω' : Fin t → Z, wgt ν ω' * exp (κ * runSum D t ω' - κ ^ 2 * runV vD t ω') *
            ∑ z, (ν z).toReal * exp (κ * D t (Fin.snoc ω' z) - κ ^ 2 * vD t ω') := by
          refine Finset.sum_congr rfl fun ω' _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [runSum, runV, Fin.init_snoc, wgt_snoc]
          rw [show κ * (runSum D t ω' + D t (Fin.snoc ω' z)) - κ ^ 2 * (runV vD t ω' + vD t ω') =
              (κ * runSum D t ω' - κ ^ 2 * runV vD t ω') + (κ * D t (Fin.snoc ω' z) - κ ^ 2 * vD t ω')
              by ring, exp_add]
          ring
      _ ≤ ∑ ω' : Fin t → Z, wgt ν ω' * exp (κ * runSum D t ω' - κ ^ 2 * runV vD t ω') * 1 := by
          refine Finset.sum_le_sum fun ω' _ => ?_
          by_cases hw : wgt ν ω' = 0
          · simp [hw]
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (wgt_nonneg ν ω') (exp_pos _).le)
          have hp : ∀ z, 0 ≤ (ν z).toReal := fun z => ENNReal.toReal_nonneg
          have hstep := Pool.P0023.sum_exp_le (fun z => (ν z).toReal) hp (sum_toReal_one ν)
            (fun z => D t (Fin.snoc ω' z)) (κ := κ) (fun z hz => by
              refine hbd t (by omega) ω' z hw ?_
              intro h; apply hz; simp [h])
          have hm := hmean t (by omega) ω' hw
          have hv := mul_le_mul_of_nonneg_left (hvar t (by omega) ω' hw) (sq_nonneg κ)
          calc ∑ z, (ν z).toReal * exp (κ * D t (Fin.snoc ω' z) - κ ^ 2 * vD t ω')
              = exp (-(κ ^ 2 * vD t ω')) * ∑ z, (ν z).toReal * exp (κ * D t (Fin.snoc ω' z)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun z _ => ?_
                rw [sub_eq_add_neg, exp_add]; ring
            _ ≤ exp (-(κ ^ 2 * vD t ω')) * exp (κ * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) +
                  κ ^ 2 * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) ^ 2) :=
                mul_le_mul_of_nonneg_left hstep (exp_pos _).le
            _ = exp (-(κ ^ 2 * vD t ω') + (κ * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) +
                  κ ^ 2 * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) ^ 2)) := by rw [← exp_add]
            _ ≤ exp 0 := by apply exp_le_exp.mpr; linarith
            _ = 1 := exp_zero
      _ ≤ 1 := by simpa using ih (by omega)

/-- **Freedman for coin sequences.** If every increment satisfies `κ·D ≤ 1` (an upper bound only), has
conditional mean `≤ 0` and conditional second moment `≤ vD` (predictable), on positive-weight prefixes of length
`< T`, then the weight of `{runSum − κ·runV ≥ x/κ}` is at most `exp (−x)`. -/
theorem freedman_coins (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (vD : (s : ℕ) → (Fin s → Z) → ℝ)
    {κ : ℝ} (hκ : 0 < κ) {T : ℕ}
    (hbd : ∀ s < T, ∀ (ω : Fin s → Z) z, wgt ν ω ≠ 0 → ν z ≠ 0 → κ * D s (Fin.snoc ω z) ≤ 1)
    (hmean : ∀ s < T, ∀ ω : Fin s → Z, wgt ν ω ≠ 0 → ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ≤ 0)
    (hvar : ∀ s < T, ∀ ω : Fin s → Z, wgt ν ω ≠ 0 →
      ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ^ 2 ≤ vD s ω) (x : ℝ) :
    probGe ν T (fun ω => runSum D T ω - κ * runV vD T ω) (x / κ) ≤ exp (-x) := by
  have hsup := expSum_freedman_le ν D vD hbd
    (fun s hs ω hw => mul_nonpos_of_nonneg_of_nonpos hκ.le (hmean s hs ω hw)) hvar T le_rfl
  calc probGe ν T (fun ω => runSum D T ω - κ * runV vD T ω) (x / κ)
      ≤ ∑ ω : Fin T → Z, wgt ν ω * exp (κ * (runSum D T ω - κ * runV vD T ω) - x) := by
        unfold probGe
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
        split_ifs with h
        · apply one_le_exp
          have : x ≤ κ * (runSum D T ω - κ * runV vD T ω) := by
            rw [div_le_iff₀ hκ] at h; linarith
          linarith
        · exact (exp_pos _).le
    _ = exp (-x) * ∑ ω : Fin T → Z, wgt ν ω * exp (κ * runSum D T ω - κ ^ 2 * runV vD T ω) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [mul_left_comm, ← exp_add]
        congr 2; ring
    _ ≤ exp (-x) * 1 := mul_le_mul_of_nonneg_left hsup (exp_pos _).le
    _ = exp (-x) := mul_one _

/-- The `δ` form: with weight at least `1 − δ`, `runSum ≤ κ·runV + log(1/δ)/κ`. -/
theorem freedman_coins_delta (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (vD : (s : ℕ) → (Fin s → Z) → ℝ)
    {κ : ℝ} (hκ : 0 < κ) {T : ℕ}
    (hbd : ∀ s < T, ∀ (ω : Fin s → Z) z, wgt ν ω ≠ 0 → ν z ≠ 0 → κ * D s (Fin.snoc ω z) ≤ 1)
    (hmean : ∀ s < T, ∀ ω : Fin s → Z, wgt ν ω ≠ 0 → ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ≤ 0)
    (hvar : ∀ s < T, ∀ ω : Fin s → Z, wgt ν ω ≠ 0 →
      ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ^ 2 ≤ vD s ω) {δ : ℝ} (hδ : 0 < δ) :
    probGe ν T (fun ω => runSum D T ω - κ * runV vD T ω) (Real.log (1 / δ) / κ) ≤ δ := by
  have h := freedman_coins ν D vD hκ hbd hmean hvar (Real.log (1 / δ))
  rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv] at h
  rwa [one_div]


omit [Fintype Z] in
lemma runV_const (v : ℝ) : ∀ t (ω : Fin t → Z), runV (fun _ _ => v) t ω = t * v := by
  intro t
  induction t with
  | zero => intro ω; simp [runV]
  | succ t ih => intro ω; simp only [runV, ih]; push_cast; ring

/-! ### Importance-weighted estimates (the motivating instance) -/

section IW

variable {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (c : ℕ → ℝ)

/-- Error (truth minus estimate) of the importance-weighted estimate `ĉ_s = c_s·1[probed]/r` of a loss `c_s`,
where round `s` is probed when its coin is `true` (probability `r`). -/
noncomputable def iwErr (r : ℝ) (c : ℕ → ℝ) (s : ℕ) (ω : Fin (s + 1) → Bool) : ℝ :=
  c s - (if ω (Fin.last s) then c s / r else 0)

include hr0 hr1 in
lemma iwErr_mean (s : ℕ) (ω : Fin s → Bool) :
    ∑ z, (Pool.P0016.bern r hr0.le hr1 z).toReal * iwErr r c s (Fin.snoc ω z) = 0 := by
  simp only [Fintype.sum_bool, Pool.P0016.bern_toReal, iwErr, Fin.snoc_last, ite_true,
    Bool.false_eq_true, ite_false]
  field_simp; ring

include hr0 hr1 in
lemma iwErr_sq (s : ℕ) (ω : Fin s → Bool) (hc : 0 ≤ c s ∧ c s ≤ 1) :
    ∑ z, (Pool.P0016.bern r hr0.le hr1 z).toReal * iwErr r c s (Fin.snoc ω z) ^ 2 ≤ 1 / r := by
  simp only [Fintype.sum_bool, Pool.P0016.bern_toReal, iwErr, Fin.snoc_last, ite_true,
    Bool.false_eq_true, ite_false]
  have e : r * (c s - c s / r) ^ 2 + (1 - r) * (c s - 0) ^ 2 = c s ^ 2 * (1 - r) / r := by
    field_simp; ring
  rw [e, div_le_div_iff_of_pos_right hr0]
  have : c s ^ 2 ≤ 1 := by nlinarith [hc.1, hc.2]
  nlinarith [hc.1]

include hr0 hr1 in
/-- **Underestimation** (truth − estimate) of an importance-weighted sum, for `0 < κ ≤ 1`: with weight at least
`1 − δ`, `Σ_s (c_s − ĉ_s) ≤ κ·T/r + log(1/δ)/κ`. -/
theorem iw_under {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hc : ∀ s, 0 ≤ c s ∧ c s ≤ 1) (T : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    probGe (Pool.P0016.bern r hr0.le hr1) T (runSum (iwErr r c) T)
      (κ * T / r + Real.log (1 / δ) / κ) ≤ δ := by
  have h := freedman_coins_delta (Pool.P0016.bern r hr0.le hr1) (iwErr r c) (fun _ _ => 1 / r) hκ0
    (T := T) (fun s _ ω z _ _ => by
      simp only [iwErr]
      have := hc s
      split_ifs
      · have : 0 ≤ c s / r := div_nonneg this.1 hr0.le
        nlinarith
      · nlinarith)
    (fun s _ ω _ => (iwErr_mean hr0 hr1 c s ω).le)
    (fun s _ ω _ => iwErr_sq hr0 hr1 c s ω (hc s)) hδ
  refine le_trans (probGe_mono _ fun ω hω => ?_) h
  simp only [runV_const] at *
  have : κ * (T * (1 / r)) = κ * T / r := by ring
  linarith

include hr0 hr1 in
/-- **Overestimation** (estimate − truth), for `0 < κ ≤ r`: with weight at least `1 − δ`,
`Σ_s (ĉ_s − c_s) ≤ κ·T/r + log(1/δ)/κ`. -/
theorem iw_over {κ : ℝ} (hκ0 : 0 < κ) (hκr : κ ≤ r) (hc : ∀ s, 0 ≤ c s ∧ c s ≤ 1) (T : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    probGe (Pool.P0016.bern r hr0.le hr1) T (runSum (fun s ω => -iwErr r c s ω) T)
      (κ * T / r + Real.log (1 / δ) / κ) ≤ δ := by
  have h := freedman_coins_delta (Pool.P0016.bern r hr0.le hr1) (fun s ω => -iwErr r c s ω)
    (fun _ _ => 1 / r) hκ0 (T := T) (fun s _ ω z _ _ => by
      simp only [iwErr]
      have := hc s
      split_ifs
      · have h1 : κ * (c s / r) ≤ 1 := by
          rw [mul_div_assoc']
          rw [div_le_one hr0]; nlinarith
        nlinarith
      · nlinarith)
    (fun s _ ω _ => by
      have := iwErr_mean hr0 hr1 c s ω
      simp only [mul_neg, Finset.sum_neg_distrib, this, neg_zero, le_refl])
    (fun s _ ω _ => by simpa only [neg_sq] using iwErr_sq hr0 hr1 c s ω (hc s)) hδ
  refine le_trans (probGe_mono _ fun ω hω => ?_) h
  simp only [runV_const] at *
  have : κ * (T * (1 / r)) = κ * T / r := by ring
  linarith

include hr0 hr1 in
/-- Tuned underestimation bound: if `r·log(1/δ) ≤ T` (and `δ ≤ 1`), with weight at least `1 − δ`,
`Σ_s (c_s − ĉ_s) ≤ 2 √(T log(1/δ) / r)`. -/
theorem iw_under_tuned (hc : ∀ s, 0 ≤ c s ∧ c s ≤ 1) (T : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hT : r * Real.log (1 / δ) ≤ T) :
    probGe (Pool.P0016.bern r hr0.le hr1) T (runSum (iwErr r c) T)
      (2 * Real.sqrt (T * Real.log (1 / δ) / r)) ≤ δ := by
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hδ, hδ1⟩)
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (mul_pos hr0 hL) hT
  set κ := Real.sqrt (r * Real.log (1 / δ) / T) with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.2 (by positivity)
  have hκ1 : κ ≤ 1 := by
    rw [hκ, Real.sqrt_le_one, div_le_one hTpos]; exact hT
  have h := iw_under hr0 hr1 c hκ0 hκ1 hc T hδ
  have key : κ * T / r + Real.log (1 / δ) / κ = 2 * Real.sqrt (T * Real.log (1 / δ) / r) := by
    have hs : κ * Real.sqrt (T * Real.log (1 / δ) / r) = Real.log (1 / δ) := by
      rw [hκ, ← Real.sqrt_mul (by positivity)]
      rw [show r * Real.log (1 / δ) / T * (T * Real.log (1 / δ) / r) = Real.log (1 / δ) ^ 2 by
        field_simp]
      exact Real.sqrt_sq hL.le
    have hs2 : κ * T / r = Real.sqrt (T * Real.log (1 / δ) / r) := by
      set S := Real.sqrt (T * Real.log (1 / δ) / r) with hSdef
      have hsq : S ^ 2 = T * Real.log (1 / δ) / r := Real.sq_sqrt (by positivity)
      have hTr : (T : ℝ) / r = S ^ 2 / Real.log (1 / δ) := by
        rw [hsq]; field_simp
      calc κ * T / r = κ * ((T : ℝ) / r) := by ring
        _ = κ * (S ^ 2 / Real.log (1 / δ)) := by rw [hTr]
        _ = (κ * S) * S / Real.log (1 / δ) := by ring
        _ = S := by rw [hs]; field_simp
    have h3 : Real.log (1 / δ) / κ = Real.sqrt (T * Real.log (1 / δ) / r) := by
      rw [div_eq_iff hκ0.ne', mul_comm]; exact hs.symm
    rw [hs2, h3]; ring
  rwa [key] at h

include hr0 hr1 in
/-- Tuned overestimation bound: if `log(1/δ) ≤ r·T` (and `δ < 1`), with weight at least `1 − δ`,
`Σ_s (ĉ_s − c_s) ≤ 2 √(T log(1/δ) / r)`. (The over side needs `κ ≤ r`, hence the stronger condition on `T`.) -/
theorem iw_over_tuned (hc : ∀ s, 0 ≤ c s ∧ c s ≤ 1) (T : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hT : Real.log (1 / δ) ≤ r * T) :
    probGe (Pool.P0016.bern r hr0.le hr1) T (runSum (fun s ω => -iwErr r c s ω) T)
      (2 * Real.sqrt (T * Real.log (1 / δ) / r)) ≤ δ := by
  have hL : 0 < Real.log (1 / δ) := Real.log_pos (by rw [one_div]; exact one_lt_inv_iff₀.2 ⟨hδ, hδ1⟩)
  have hTpos : (0 : ℝ) < T := by
    by_contra h; push_neg at h; nlinarith
  set κ := Real.sqrt (r * Real.log (1 / δ) / T) with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.2 (by positivity)
  have hκr : κ ≤ r := by
    rw [hκ, Real.sqrt_le_left hr0.le, div_le_iff₀ hTpos]; nlinarith
  have h := iw_over hr0 hr1 c hκ0 hκr hc T hδ
  have key : κ * T / r + Real.log (1 / δ) / κ = 2 * Real.sqrt (T * Real.log (1 / δ) / r) := by
    have hs : κ * Real.sqrt (T * Real.log (1 / δ) / r) = Real.log (1 / δ) := by
      rw [hκ, ← Real.sqrt_mul (by positivity)]
      rw [show r * Real.log (1 / δ) / T * (T * Real.log (1 / δ) / r) = Real.log (1 / δ) ^ 2 by
        field_simp]
      exact Real.sqrt_sq hL.le
    have hs2 : κ * T / r = Real.sqrt (T * Real.log (1 / δ) / r) := by
      set S := Real.sqrt (T * Real.log (1 / δ) / r) with hSdef
      have hsq : S ^ 2 = T * Real.log (1 / δ) / r := Real.sq_sqrt (by positivity)
      have hTr : (T : ℝ) / r = S ^ 2 / Real.log (1 / δ) := by
        rw [hsq]; field_simp
      calc κ * T / r = κ * ((T : ℝ) / r) := by ring
        _ = κ * (S ^ 2 / Real.log (1 / δ)) := by rw [hTr]
        _ = (κ * S) * S / Real.log (1 / δ) := by ring
        _ = S := by rw [hs]; field_simp
    have h3 : Real.log (1 / δ) / κ = Real.sqrt (T * Real.log (1 / δ) / r) := by
      rw [div_eq_iff hκ0.ne', mul_comm]; exact hs.symm
    rw [hs2, h3]; ring
  rwa [key] at h

end IW

end Pool.P0100
