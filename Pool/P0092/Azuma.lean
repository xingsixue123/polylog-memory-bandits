import Pool.P0064.QCoin
import Pool.P0023.Concentration

/-!
# Azuma–Hoeffding for adapted sums of i.i.d. coin sequences (the coin law of P0064's `QCoinAlg`)

P0064 writes the state law of a `QCoinAlg` (a pool learner whose update reads only its queried bits and a fresh
update coin `z ∼ ν`) as the coin-weighted realized run: `E f = Σ_ω W ω · f (runFin ℓ t ω)` with
`W ω = Π_j ν(ω j)`. P0023's `azuma` is stated for the state law of a P0001 machine, not for this representation.
This file gives the analogue for coin sequences.

* `Pool.P0092.wgt ν ω = Π_j ν(ω j)`, the weight of a coin sequence `ω : Fin t → Z`.
  `Pool.P0092.wgt_eq_W`: it is P0064's `QCoinAlg.W` (with `ν := A.ν`). `Pool.P0092.sum_wgt`: total mass `1`.
* `Pool.P0092.runSum D t ω`: the sum of increments `D s (ω restricted to rounds ≤ s)` over `s < t`. The increment of
  round `s` may read the coins of rounds `0..s` (it is adapted).
* `Pool.P0092.probGe ν T f x`: the weight of the sequences `ω : Fin T → Z` with `x ≤ f ω`.
* **`Pool.P0092.azuma_coins`**: if every increment is in `[-1, 1]` and has conditional mean `≤ 0` given the coins of
  the earlier rounds (`Σ_z ν(z)·D s (snoc ω z) ≤ 0` for every `ω : Fin s → Z`), then
  `probGe ν T (runSum D T) x ≤ exp (-x²/(4T))` for `0 ≤ x ≤ 2T`.
* `Pool.P0092.azuma_coins_scaled`: increments in `[-b, b]`, `0 ≤ x ≤ 2bT`: `≤ exp (-x²/(4b²T))`.
* `Pool.P0092.azuma_coins_abs`: conditional mean exactly `0`: `P(|runSum| ≥ x) ≤ 2 exp (-x²/(4b²T))`.
* `Pool.P0092.probGe_exists_le`: union bound over a finite family of functions.

**Hypotheses and constants.**
- The bound and conditional-mean hypotheses quantify over **every** prefix `ω : Fin s → Z` and **every** round `s`.
  This includes prefixes of weight `0`, if `ν` has atoms of mass `0`, and rounds `s ≥ T`.
- That is stronger than the martingale condition, which is needed only on positive-weight prefixes and rounds
  `s < T`.
- It costs nothing when `ν` has full support. Otherwise, for example for P0064 coin laws with zero-mass values, set
  the increment `D s := 0` on weight-0 prefixes and on rounds `s ≥ T` before applying the lemmas. The new `D` has the
  same `runSum D T` on every positive-weight sequence, so the conclusions are unchanged.
- The tail bound `exp (-x²/(4T))` (resp. `exp (-x²/(4b²T))`) is a factor `2` weaker in the exponent than the
  standard Azuma–Hoeffding `exp (-x²/(2T))` for increments in `[-1, 1]`, because of the crude one-step inequality
  `exp y ≤ 1 + y + y²`.

Intended use (CLAIMED, not done here): importance-weighted estimates of pool losses from a uniformly drawn slot
(a free observation, P0022 §2) have errors that are such sums, with `b` = the number of slots.
-/

open Finset Real
open scoped ENNReal

namespace Pool.P0092

variable {Z : Type} [Fintype Z] (ν : PMF Z)

/-- Weight of a coin sequence: `Π_j ν(ω j)`. -/
noncomputable def wgt {t : ℕ} (ω : Fin t → Z) : ℝ := ∏ j, (ν (ω j)).toReal

/-- `wgt` is P0064's `QCoinAlg.W`. -/
theorem wgt_eq_W {n K : ℕ} (A : Pool.P0064.QCoinAlg n K) {t : ℕ} (ω : Fin t → A.Z) :
    wgt A.ν ω = A.W ω := rfl

omit [Fintype Z] in
theorem wgt_nonneg {t : ℕ} (ω : Fin t → Z) : 0 ≤ wgt ν ω :=
  Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg

omit [Fintype Z] in
theorem wgt_snoc {t : ℕ} (ω : Fin t → Z) (z : Z) :
    wgt ν (Fin.snoc ω z) = wgt ν ω * (ν z).toReal := by
  unfold wgt; rw [Fin.prod_univ_castSucc]; simp

theorem sum_toReal_one : ∑ z, (ν z).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun z _ => PMF.apply_ne_top _ z),
    ← tsum_fintype (L := .unconditional _) (fun z => ν z), PMF.tsum_coe, ENNReal.toReal_one]

theorem sum_wgt (t : ℕ) : ∑ ω : Fin t → Z, wgt ν ω = 1 := by
  induction t with
  | zero => simp [wgt]
  | succ t ih =>
    rw [Pool.P0064.sum_split]
    simp only [wgt_snoc, ← Finset.sum_mul, ih, one_mul]
    exact sum_toReal_one ν

/-- Running sum of adapted increments: the increment of round `s` reads the coins of rounds `0..s`. -/
def runSum (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) : (t : ℕ) → (Fin t → Z) → ℝ
  | 0, _ => 0
  | t + 1, ω => runSum D t (Fin.init ω) + D t ω

/-- Weight of the coin sequences of length `T` on which `x ≤ f`. -/
noncomputable def probGe (T : ℕ) (f : (Fin T → Z) → ℝ) (x : ℝ) : ℝ :=
  ∑ ω : Fin T → Z, wgt ν ω * if x ≤ f ω then 1 else 0

theorem probGe_nonneg (T : ℕ) (f : (Fin T → Z) → ℝ) (x : ℝ) : 0 ≤ probGe ν T f x :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (wgt_nonneg ν ω) (by split_ifs <;> norm_num)

theorem probGe_mono {T : ℕ} {f g : (Fin T → Z) → ℝ} {x y : ℝ} (h : ∀ ω, x ≤ f ω → y ≤ g ω) :
    probGe ν T f x ≤ probGe ν T g y := by
  unfold probGe
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
  split_ifs with h1 h2 h2
  · norm_num
  · exact absurd (h ω h1) h2
  · norm_num
  · norm_num

/-- **Exponential supermartingale.** (Hypotheses on every prefix and every round; see the module docstring.) -/
theorem expSum_le (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1)
    (hbd : ∀ s ω, |D s ω| ≤ 1)
    (hmean : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ≤ 0) :
    ∀ t, ∑ ω : Fin t → Z, wgt ν ω * exp (κ * runSum D t ω - κ ^ 2 * t) ≤ 1 := by
  intro t
  induction t with
  | zero => simp [wgt, runSum]
  | succ t ih =>
    rw [Pool.P0064.sum_split, Finset.sum_comm]
    calc ∑ ω' : Fin t → Z, ∑ z, wgt ν (Fin.snoc ω' z) *
          exp (κ * runSum D (t + 1) (Fin.snoc ω' z) - κ ^ 2 * ((t + 1 : ℕ) : ℝ))
        = ∑ ω' : Fin t → Z, wgt ν ω' * exp (κ * runSum D t ω' - κ ^ 2 * t) *
            ∑ z, (ν z).toReal * exp (κ * D t (Fin.snoc ω' z) - κ ^ 2) := by
          refine Finset.sum_congr rfl fun ω' _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [runSum, Fin.init_snoc, wgt_snoc]
          rw [show κ * (runSum D t ω' + D t (Fin.snoc ω' z)) - κ ^ 2 * ((t + 1 : ℕ) : ℝ) =
              (κ * runSum D t ω' - κ ^ 2 * t) + (κ * D t (Fin.snoc ω' z) - κ ^ 2) by push_cast; ring,
            exp_add]
          ring
      _ ≤ ∑ ω' : Fin t → Z, wgt ν ω' * exp (κ * runSum D t ω' - κ ^ 2 * t) * 1 := by
          refine Finset.sum_le_sum fun ω' _ => mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (wgt_nonneg ν ω') (exp_pos _).le)
          have hp : ∀ z, 0 ≤ (ν z).toReal := fun z => ENNReal.toReal_nonneg
          have hstep := Pool.P0023.sum_exp_le (fun z => (ν z).toReal) hp (sum_toReal_one ν)
            (fun z => D t (Fin.snoc ω' z)) (κ := κ) (fun z _ => by
              have := (abs_le.mp (hbd t (Fin.snoc ω' z))).2
              nlinarith)
          have hv : ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) ^ 2 ≤ 1 := by
            calc ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) ^ 2 ≤ ∑ z, (ν z).toReal * 1 := by
                  refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (hp z)
                  rw [sq_le_one_iff_abs_le_one]; exact hbd t _
              _ = 1 := by simp [sum_toReal_one ν]
          have hm := hmean t ω'
          calc ∑ z, (ν z).toReal * exp (κ * D t (Fin.snoc ω' z) - κ ^ 2)
              = exp (-κ ^ 2) * ∑ z, (ν z).toReal * exp (κ * D t (Fin.snoc ω' z)) := by
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun z _ => ?_
                rw [sub_eq_add_neg, exp_add]; ring
            _ ≤ exp (-κ ^ 2) * exp (κ * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) +
                  κ ^ 2 * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) ^ 2) :=
                mul_le_mul_of_nonneg_left hstep (exp_pos _).le
            _ = exp (-κ ^ 2 + (κ * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) +
                  κ ^ 2 * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) ^ 2)) := by rw [← exp_add]
            _ ≤ exp 0 := by
                apply exp_le_exp.mpr
                have h1 : κ * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) ≤ 0 :=
                  mul_nonpos_of_nonneg_of_nonpos hκ0 hm
                have h2 := mul_le_mul_of_nonneg_left hv (sq_nonneg κ)
                linarith
            _ = 1 := exp_zero
      _ ≤ 1 := by simpa using ih

/-- **Azuma–Hoeffding for adapted sums of i.i.d. coins.** Increments in `[-1, 1]` with conditional mean `≤ 0`:
for `0 ≤ x ≤ 2T`, the weight of `{runSum ≥ x}` is at most `exp (-x²/(4T))`.
Note: `hbd` and `hmean` are required on every prefix (including weight-0 ones) and every round `s`, not only `s < T`;
set `D := 0` outside the relevant range if needed. The exponent is a factor `2` weaker than the standard
`exp (-x²/(2T))`. -/
theorem azuma_coins (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (hbd : ∀ s ω, |D s ω| ≤ 1)
    (hmean : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ≤ 0)
    {T : ℕ} (hT : 0 < T) {x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ 2 * T) :
    probGe ν T (runSum D T) x ≤ exp (-(x ^ 2) / (4 * T)) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set κ := x / (2 * T) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ ≤ 1 := by rw [hκ, div_le_one (by positivity)]; exact hxT
  have hsup := expSum_le ν D hκ0 hκ1 hbd hmean T
  calc probGe ν T (runSum D T) x
      ≤ ∑ ω : Fin T → Z, wgt ν ω * exp (κ * (runSum D T ω - x)) := by
        unfold probGe
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
        split_ifs with h
        · exact one_le_exp (mul_nonneg hκ0 (by linarith))
        · exact (exp_pos _).le
    _ = exp (κ ^ 2 * T - κ * x) * ∑ ω : Fin T → Z, wgt ν ω * exp (κ * runSum D T ω - κ ^ 2 * T) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [mul_left_comm, ← exp_add]
        congr 2; ring
    _ ≤ exp (κ ^ 2 * T - κ * x) * 1 := mul_le_mul_of_nonneg_left hsup (exp_pos _).le
    _ = exp (-(x ^ 2) / (4 * T)) := by
        rw [mul_one]; congr 1; rw [hκ]; field_simp; ring

omit [Fintype Z] in
/-- `runSum` of a scaled increment. -/
theorem runSum_smul (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (c : ℝ) :
    ∀ t (ω : Fin t → Z), runSum (fun s ω => c * D s ω) t ω = c * runSum D t ω
  | 0, _ => by simp [runSum]
  | t + 1, ω => by simp only [runSum, runSum_smul D c t]; ring

/-- **Scaled version.** Increments in `[-b, b]` (`b > 0`) with conditional mean `≤ 0`: for `0 ≤ x ≤ 2bT`,
`P(runSum ≥ x) ≤ exp (-x²/(4b²T))`.
Note: `hbd` and `hmean` are required on every prefix (including weight-0 ones) and every round `s`, not only `s < T`;
set `D := 0` outside the relevant range if needed. The exponent is a factor `2` weaker than the standard
`exp (-x²/(2b²T))`. -/
theorem azuma_coins_scaled (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) {b : ℝ} (hb : 0 < b)
    (hbd : ∀ s ω, |D s ω| ≤ b)
    (hmean : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ≤ 0)
    {T : ℕ} (hT : 0 < T) {x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ 2 * b * T) :
    probGe ν T (runSum D T) x ≤ exp (-(x ^ 2) / (4 * b ^ 2 * T)) := by
  set D' : (s : ℕ) → (Fin (s + 1) → Z) → ℝ := fun s ω => b⁻¹ * D s ω
  have hbd' : ∀ s ω, |D' s ω| ≤ 1 := by
    intro s ω
    simp only [D', abs_mul, abs_inv, abs_of_pos hb]
    rw [inv_mul_le_iff₀ hb, mul_one]; exact hbd s ω
  have hmean' : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * D' s (Fin.snoc ω z) ≤ 0 := by
    intro s ω
    have : ∑ z, (ν z).toReal * D' s (Fin.snoc ω z) = b⁻¹ * ∑ z, (ν z).toReal * D s (Fin.snoc ω z) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => ?_; simp only [D']; ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hb.le) (hmean s ω)
  have h := azuma_coins ν D' hbd' hmean' hT (x := x / b) (div_nonneg hx0 hb.le)
    (by rw [div_le_iff₀ hb]; linarith)
  calc probGe ν T (runSum D T) x = probGe ν T (runSum D' T) (x / b) := by
        unfold probGe
        refine Finset.sum_congr rfl fun ω _ => ?_
        have hc : (x / b ≤ runSum D' T ω) ↔ (x ≤ runSum D T ω) := by
          rw [show runSum D' T ω = b⁻¹ * runSum D T ω from runSum_smul D b⁻¹ T ω, inv_mul_eq_div]
          exact div_le_div_iff_of_pos_right hb
        by_cases h : x ≤ runSum D T ω
        · simp only [h, hc.mpr h, ite_true]
        · have h' : ¬ (x / b ≤ runSum D' T ω) := fun h' => h (hc.mp h')
          simp only [h, h', ite_false]
    _ ≤ exp (-((x / b) ^ 2) / (4 * T)) := h
    _ = exp (-(x ^ 2) / (4 * b ^ 2 * T)) := by
        congr 1; field_simp

omit [Fintype Z] in
theorem runSum_neg (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) :
    ∀ t (ω : Fin t → Z), runSum (fun s ω => -D s ω) t ω = -runSum D t ω
  | 0, _ => by simp [runSum]
  | t + 1, ω => by simp only [runSum, runSum_neg D t]; ring

/-- Weight of the sequences with `x ≤ |f|`. -/
noncomputable def probAbsGe (T : ℕ) (f : (Fin T → Z) → ℝ) (x : ℝ) : ℝ :=
  ∑ ω : Fin T → Z, wgt ν ω * if x ≤ |f ω| then 1 else 0

/-- **Two-sided version.** Increments in `[-b, b]` with conditional mean exactly `0`: for `0 ≤ x ≤ 2bT`,
`P(|runSum| ≥ x) ≤ 2 exp (-x²/(4b²T))`.
Note: `hbd` and `hmean` are required on every prefix (including weight-0 ones) and every round `s`, not only `s < T`;
set `D := 0` outside the relevant range if needed. The exponent is a factor `2` weaker than the standard
`exp (-x²/(2b²T))`. -/
theorem azuma_coins_abs (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) {b : ℝ} (hb : 0 < b)
    (hbd : ∀ s ω, |D s ω| ≤ b)
    (hmean : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * D s (Fin.snoc ω z) = 0)
    {T : ℕ} (hT : 0 < T) {x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ 2 * b * T) :
    probAbsGe ν T (runSum D T) x ≤ 2 * exp (-(x ^ 2) / (4 * b ^ 2 * T)) := by
  have h1 := azuma_coins_scaled ν D hb hbd (fun s ω => (hmean s ω).le) hT hx0 hxT
  have h2 := azuma_coins_scaled ν (fun s ω => -D s ω) hb (fun s ω => by rw [abs_neg]; exact hbd s ω)
    (fun s ω => by
      have : ∑ z, (ν z).toReal * -D s (Fin.snoc ω z) = -∑ z, (ν z).toReal * D s (Fin.snoc ω z) := by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun z _ => by ring
      rw [this, hmean s ω, neg_zero]) hT hx0 hxT
  have hsplit : probAbsGe ν T (runSum D T) x ≤
      probGe ν T (runSum D T) x + probGe ν T (runSum (fun s ω => -D s ω) T) x := by
    unfold probAbsGe probGe
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    rw [runSum_neg D T ω, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
    split_ifs with h h1 h2 h2 <;> norm_num
    · rcases le_abs'.mp h with h' | h'
      · exact absurd (by linarith) h2
      · exact absurd h' h1
  linarith

/-- **Union bound** over a finite family of functions. -/
theorem probGe_exists_le {ι' : Type} (I : Finset ι') {T : ℕ} (f : ι' → (Fin T → Z) → ℝ) (x : ℝ) :
    (∑ ω : Fin T → Z, wgt ν ω * if ∃ i ∈ I, x ≤ f i ω then 1 else 0) ≤ ∑ i ∈ I, probGe ν T (f i) x := by
  classical
  unfold probGe
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ω _ => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
  split_ifs with h
  · obtain ⟨i, hi, hx⟩ := h
    calc (1 : ℝ) = if x ≤ f i ω then 1 else 0 := by simp only [hx, ite_true]
      _ ≤ ∑ j ∈ I, if x ≤ f j ω then 1 else 0 :=
          Finset.single_le_sum (f := fun j => if x ≤ f j ω then (1 : ℝ) else 0)
            (fun j _ => by split_ifs <;> norm_num) hi
  · exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

end Pool.P0092

namespace Pool.P0092.Tests

open Pool.P0092

/-- A fair coin on `Bool`. -/
noncomputable def fair : PMF Bool := PMF.bernoulli (1 / 2) (by norm_num)

/-- `±1` increments driven by the round's own coin: conditional mean `0`. -/
def pm : (s : ℕ) → (Fin (s + 1) → Bool) → ℝ := fun s ω => if ω (Fin.last s) then 1 else -1

theorem pm_bd (s : ℕ) (ω : Fin (s + 1) → Bool) : |pm s ω| ≤ 1 := by
  unfold pm; split_ifs <;> norm_num

theorem pm_mean (s : ℕ) (ω : Fin s → Bool) : ∑ z, (fair z).toReal * pm s (Fin.snoc ω z) = 0 := by
  simp only [pm, fair, Fin.snoc_last, Fintype.sum_bool, PMF.bernoulli_apply, cond_true, cond_false,
    if_true, Bool.false_eq_true, if_false]
  have h : (1 : NNReal) - 1 / 2 = 1 / 2 := by
    rw [show (1 : NNReal) = 1 / 2 + 1 / 2 by rw [add_halves]]
    simp
  rw [h]
  ring

/-- The hypotheses of `azuma_coins_abs` are met by a genuinely random walk. -/
example (T : ℕ) (hT : 0 < T) (x : ℝ) (hx0 : 0 ≤ x) (hxT : x ≤ 2 * 1 * T) :
    probAbsGe fair T (runSum pm T) x ≤ 2 * exp (-(x ^ 2) / (4 * 1 ^ 2 * T)) :=
  azuma_coins_abs fair pm one_pos pm_bd pm_mean hT hx0 hxT

/-- Negative control: the walk really moves (after one round it is `±1`, never `0`). -/
theorem runSum_pm_one (ω : Fin 1 → Bool) : |runSum pm 1 ω| = 1 := by
  simp only [runSum, pm, zero_add]
  split_ifs <;> norm_num

end Pool.P0092.Tests
