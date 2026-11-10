import Pool.Prelude
import Pool.P0023.Concentration
import Pool.P0070.Relabel

/-!
# Exponential moments and tails of adapted sums over an explicit product coin law

Coins `ω : Fin T → Y`, independent with law `μ` each (P0070's weight `wR μ ω = ∏ μ(ω u)`). The increment of round
`u` is `X u p y`, a function of the earlier coins `p` and the current coin `y`. `adSum X T ω` is the partial sum.

* `sum_exp_adSum`: conditional mean `≤ 0`, conditional second moment `≤ b u`, `κ·X ≤ 1` give
  `E[exp(κ · adSum)] ≤ exp(κ² Σ b)` (via P0023's `sum_exp_le`).
* `tail_adSum` (`0 ≤ x ≤ 2V/c`): `P(adSum ≥ x) ≤ exp(−x²/(4V))`; `tail_adSum_all` (all `x ≥ 0`):
  `≤ exp(−min(x²/(4V), x/(2c)))`; two-sided version `tail_abs_adSum_all` (mean exactly `0`).
* `adSum_eq_sum`: the recursive sum is the sum over rounds of the increments on prefixes.
-/

open Real Finset

namespace Pool.P0097

variable {Y : Type} [Fintype Y]

/-- Partial sums of adapted increments: the increment of round `u` is `X u p y`, where `p` are the coins of the
earlier rounds and `y` the coin of round `u`. -/
def adSum (X : (u : ℕ) → (Fin u → Y) → Y → ℝ) : (T : ℕ) → (Fin T → Y) → ℝ
  | 0, _ => 0
  | T + 1, ω => adSum X T (Fin.init ω) + X T (Fin.init ω) (ω (Fin.last T))

theorem wR_nonneg (μ : Y → ℝ) (hμ0 : ∀ y, 0 ≤ μ y) {T : ℕ} (ω : Fin T → Y) : 0 ≤ Pool.P0070.wR μ ω :=
  Finset.prod_nonneg fun u _ => hμ0 (ω u)

theorem sum_wR (μ : Y → ℝ) (hμ1 : ∑ y, μ y = 1) : ∀ T, ∑ ω : Fin T → Y, Pool.P0070.wR μ ω = 1
  | 0 => by simp [Pool.P0070.wR]
  | T + 1 => by
    rw [Pool.P0070.sum_snoc]
    simp only [Pool.P0070.wR_snoc, ← Finset.mul_sum, hμ1, mul_one]
    exact sum_wR μ hμ1 T

/-- **Exponential moment of adapted sums.** If each increment has conditional mean `≤ 0`, conditional second moment
`≤ b u`, and `κ · increment ≤ 1`, then `E[exp(κ · Σ increments)] ≤ exp(κ² · Σ_u b u)`. -/
theorem sum_exp_adSum (μ : Y → ℝ) (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (X : (u : ℕ) → (Fin u → Y) → Y → ℝ) (b : ℕ → ℝ)
    (hmean : ∀ u p, ∑ y, μ y * X u p y ≤ 0) (hsq : ∀ u p, ∑ y, μ y * X u p y ^ 2 ≤ b u)
    (hone : ∀ u p y, μ y ≠ 0 → κ * X u p y ≤ 1) :
    ∀ T, ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * exp (κ * adSum X T ω) ≤
      exp (κ ^ 2 * ∑ u ∈ range T, b u)
  | 0 => by simp [adSum, Pool.P0070.wR]
  | T + 1 => by
    rw [Pool.P0070.sum_snoc]
    simp only [adSum, Fin.init_snoc, Fin.snoc_last, Pool.P0070.wR_snoc]
    have hstep : ∀ ω' : Fin T → Y, ∑ y, Pool.P0070.wR μ ω' * μ y * exp (κ * (adSum X T ω' + X T ω' y)) ≤
        Pool.P0070.wR μ ω' * exp (κ * adSum X T ω') * exp (κ ^ 2 * b T) := by
      intro ω'
      have h1 : ∑ y, Pool.P0070.wR μ ω' * μ y * exp (κ * (adSum X T ω' + X T ω' y)) =
          Pool.P0070.wR μ ω' * exp (κ * adSum X T ω') * ∑ y, μ y * exp (κ * X T ω' y) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [mul_add, exp_add]; ring
      rw [h1]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (wR_nonneg μ hμ0 ω') (exp_pos _).le)
      refine (Pool.P0023.sum_exp_le μ hμ0 hμ1 (X T ω') (fun y hy => hone T ω' y hy)).trans ?_
      apply exp_le_exp.2
      have hm := mul_le_mul_of_nonneg_left (hmean T ω') hκ
      have hs := mul_le_mul_of_nonneg_left (hsq T ω') (sq_nonneg κ)
      linarith
    calc ∑ ω' : Fin T → Y, ∑ y, Pool.P0070.wR μ ω' * μ y * exp (κ * (adSum X T ω' + X T ω' y))
        ≤ ∑ ω' : Fin T → Y, Pool.P0070.wR μ ω' * exp (κ * adSum X T ω') * exp (κ ^ 2 * b T) :=
          Finset.sum_le_sum fun ω' _ => hstep ω'
      _ = (∑ ω' : Fin T → Y, Pool.P0070.wR μ ω' * exp (κ * adSum X T ω')) * exp (κ ^ 2 * b T) := by
          rw [Finset.sum_mul]
      _ ≤ exp (κ ^ 2 * ∑ u ∈ range T, b u) * exp (κ ^ 2 * b T) :=
          mul_le_mul_of_nonneg_right (sum_exp_adSum μ hμ0 hμ1 hκ X b hmean hsq hone T) (exp_pos _).le
      _ = exp (κ ^ 2 * ∑ u ∈ range (T + 1), b u) := by
          rw [← exp_add, Finset.sum_range_succ]; ring_nf


/-- **Freedman-type tail for adapted sums.** Increments with conditional mean `≤ 0`, values `≤ c` and conditional
second moments `≤ b u`, with `Σ_{u<T} b u ≤ V`: for `0 ≤ x ≤ 2V/c`,
`P(Σ increments ≥ x) ≤ exp(−x²/(4V))`. -/
theorem tail_adSum (μ : Y → ℝ) (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1)
    (X : (u : ℕ) → (Fin u → Y) → Y → ℝ) (b : ℕ → ℝ) {c V x : ℝ} (hc : 0 < c) (hV : 0 < V)
    (hmean : ∀ u p, ∑ y, μ y * X u p y ≤ 0) (hsq : ∀ u p, ∑ y, μ y * X u p y ^ 2 ≤ b u)
    (hbd : ∀ u p y, X u p y ≤ c) (T : ℕ) (hbV : ∑ u ∈ range T, b u ≤ V) (hx0 : 0 ≤ x) (hxV : x ≤ 2 * V / c) :
    ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * (if x ≤ adSum X T ω then 1 else 0) ≤ exp (-(x ^ 2 / (4 * V))) := by
  set κ := x / (2 * V) with hκdef
  have hκ : 0 ≤ κ := div_nonneg hx0 (by linarith)
  have hκc : κ * c ≤ 1 := by
    rw [hκdef, div_mul_eq_mul_div, div_le_one (by linarith)]
    have := (le_div_iff₀ hc).1 hxV
    linarith
  have hone : ∀ u p y, μ y ≠ 0 → κ * X u p y ≤ 1 := fun u p y _ =>
    (mul_le_mul_of_nonneg_left (hbd u p y) hκ).trans hκc
  have hmom := sum_exp_adSum μ hμ0 hμ1 hκ X b hmean hsq hone T
  calc ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * (if x ≤ adSum X T ω then 1 else 0)
      ≤ ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * (exp (-(κ * x)) * exp (κ * adSum X T ω)) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wR_nonneg μ hμ0 ω)
        split_ifs with h
        · rw [← exp_add]; exact one_le_exp (by nlinarith)
        · positivity
    _ = exp (-(κ * x)) * ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * exp (κ * adSum X T ω) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ exp (-(κ * x)) * exp (κ ^ 2 * V) := by
        refine mul_le_mul_of_nonneg_left (hmom.trans (exp_le_exp.2 ?_)) (exp_pos _).le
        exact mul_le_mul_of_nonneg_left hbV (sq_nonneg κ)
    _ = exp (-(x ^ 2 / (4 * V))) := by
        rw [← exp_add]; congr 1; rw [hκdef]; field_simp; ring


/-- **Bernstein-type tail, all deviations.** Under the hypotheses of `tail_adSum` but for every `x ≥ 0`:
`P(Σ increments ≥ x) ≤ exp(−min(x²/(4V), x/(2c)))`. -/
theorem tail_adSum_all (μ : Y → ℝ) (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1)
    (X : (u : ℕ) → (Fin u → Y) → Y → ℝ) (b : ℕ → ℝ) {c V x : ℝ} (hc : 0 < c) (hV : 0 < V)
    (hmean : ∀ u p, ∑ y, μ y * X u p y ≤ 0) (hsq : ∀ u p, ∑ y, μ y * X u p y ^ 2 ≤ b u)
    (hbd : ∀ u p y, X u p y ≤ c) (T : ℕ) (hbV : ∑ u ∈ range T, b u ≤ V) (hx0 : 0 ≤ x) :
    ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * (if x ≤ adSum X T ω then 1 else 0) ≤
      exp (-(min (x ^ 2 / (4 * V)) (x / (2 * c)))) := by
  by_cases hxV : x ≤ 2 * V / c
  · exact (tail_adSum μ hμ0 hμ1 X b hc hV hmean hsq hbd T hbV hx0 hxV).trans
      (exp_le_exp.2 (neg_le_neg (min_le_left _ _)))
  · push_neg at hxV
    have hxc : 2 * V < x * c := by rwa [div_lt_iff₀ hc] at hxV
    set κ := 1 / c with hκdef
    have hκ : 0 ≤ κ := by positivity
    have hone : ∀ u p y, μ y ≠ 0 → κ * X u p y ≤ 1 := by
      intro u p y _
      have := mul_le_mul_of_nonneg_left (hbd u p y) hκ
      rw [hκdef, one_div_mul_cancel hc.ne'] at this; exact this
    have hmom := sum_exp_adSum μ hμ0 hμ1 hκ X b hmean hsq hone T
    calc ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * (if x ≤ adSum X T ω then 1 else 0)
        ≤ ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * (exp (-(κ * x)) * exp (κ * adSum X T ω)) := by
          refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wR_nonneg μ hμ0 ω)
          split_ifs with h
          · rw [← exp_add]; exact one_le_exp (by nlinarith)
          · positivity
      _ = exp (-(κ * x)) * ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * exp (κ * adSum X T ω) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ exp (-(κ * x)) * exp (κ ^ 2 * V) := by
          refine mul_le_mul_of_nonneg_left (hmom.trans (exp_le_exp.2 ?_)) (exp_pos _).le
          exact mul_le_mul_of_nonneg_left hbV (sq_nonneg κ)
      _ = exp (-(κ * x) + κ ^ 2 * V) := by rw [← exp_add]
      _ ≤ exp (-(min (x ^ 2 / (4 * V)) (x / (2 * c)))) := by
          apply exp_le_exp.2
          have h1 : -(κ * x) + κ ^ 2 * V ≤ -(x / (2 * c)) := by
            rw [hκdef]
            have : V / c ^ 2 < x / (2 * c) := by
              rw [div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
            have e1 : -(1 / c * x) + (1 / c) ^ 2 * V = -(x / c) + V / c ^ 2 := by ring
            have e2 : x / c = 2 * (x / (2 * c)) := by field_simp
            rw [e1, e2]; linarith
          exact h1.trans (neg_le_neg (min_le_right _ _))

/-- Prefix of a coin vector: the coins of the rounds before `u`. -/
def pre {T : ℕ} (ω : Fin T → Y) (u : ℕ) (hu : u ≤ T) : Fin u → Y :=
  fun v => ω ⟨v, lt_of_lt_of_le v.2 hu⟩

/-- The recursive partial sum is the sum over rounds of the increments evaluated on prefixes. -/
theorem adSum_eq_sum (X : (u : ℕ) → (Fin u → Y) → Y → ℝ) :
    ∀ (T : ℕ) (ω : Fin T → Y), adSum X T ω = ∑ u : Fin T, X u (pre ω u u.2.le) (ω u)
  | 0, _ => by simp [adSum]
  | T + 1, ω => by
    rw [adSum, adSum_eq_sum X T, Fin.sum_univ_castSucc]
    congr 1

/-- **Two-sided Bernstein-type tail, all deviations.** -/
theorem tail_abs_adSum_all (μ : Y → ℝ) (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1)
    (X : (u : ℕ) → (Fin u → Y) → Y → ℝ) (b : ℕ → ℝ) {c V x : ℝ} (hc : 0 < c) (hV : 0 < V)
    (hmean : ∀ u p, ∑ y, μ y * X u p y = 0) (hsq : ∀ u p, ∑ y, μ y * X u p y ^ 2 ≤ b u)
    (hbd : ∀ u p y, |X u p y| ≤ c) (T : ℕ) (hbV : ∑ u ∈ range T, b u ≤ V) (hx0 : 0 ≤ x) :
    ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * (if x ≤ |adSum X T ω| then 1 else 0) ≤
      2 * exp (-(min (x ^ 2 / (4 * V)) (x / (2 * c)))) := by
  have hneg : ∀ T (ω : Fin T → Y), adSum (fun u p y => -X u p y) T ω = -adSum X T ω := by
    intro T
    induction T with
    | zero => intro ω; simp [adSum]
    | succ T ih => intro ω; simp only [adSum, ih]; ring
  have h1 := tail_adSum_all μ hμ0 hμ1 X b hc hV (fun u p => (hmean u p).le) hsq
    (fun u p y => (le_abs_self _).trans (hbd u p y)) T hbV hx0
  have h2 := tail_adSum_all μ hμ0 hμ1 (fun u p y => -X u p y) b hc hV
    (fun u p => by simp only [mul_neg, Finset.sum_neg_distrib, hmean u p, neg_zero, le_refl])
    (fun u p => by simpa only [neg_sq] using hsq u p)
    (fun u p y => (neg_le_abs _).trans (hbd u p y)) T hbV hx0
  simp only [hneg] at h2
  calc ∑ ω : Fin T → Y, Pool.P0070.wR μ ω * (if x ≤ |adSum X T ω| then 1 else 0)
      ≤ ∑ ω : Fin T → Y, (Pool.P0070.wR μ ω * (if x ≤ adSum X T ω then 1 else 0) +
          Pool.P0070.wR μ ω * (if x ≤ -adSum X T ω then 1 else 0)) := by
        refine Finset.sum_le_sum fun ω _ => ?_
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ (wR_nonneg μ hμ0 ω)
        by_cases h : x ≤ |adSum X T ω|
        · rw [if_pos h]
          rcases le_abs.1 h with h3 | h3
          · rw [if_pos h3]; split_ifs <;> norm_num
          · rw [if_pos h3]; split_ifs <;> norm_num
        · rw [if_neg h]; split_ifs <;> norm_num
    _ ≤ 2 * exp (-(min (x ^ 2 / (4 * V)) (x / (2 * c)))) := by rw [Finset.sum_add_distrib]; linarith

end Pool.P0097
