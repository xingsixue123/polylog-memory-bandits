import Pool.P0001.Model

/-!
# Memory budgets and the two target statements

* `MemoryBound F C k`: the family `F` (one machine for each pair `n T`) uses at most
  `C (log (n T))^k` bits whenever `1 ≤ n ≤ T`.
* `RegretBound F R`: for all `1 ≤ n ≤ T` and every oblivious loss sequence, the machine `F n T`
  has expected regret at most `R n T` over the rounds `0, …, T - 1`.
* `MinimaxPolylogAchievable`: the positive resolution of the open problem: a family of
  homogeneous machines (no free clock) with polylogarithmic memory and regret
  `C' √(n T) (log (n T))^k'` for all `1 ≤ n ≤ T`.
* `PolylogPenaltyAt α`: a negative statement for the family `n = ⌊T^α⌋` (it includes `0 < α ≤ 1`):
  for every fixed memory
  budget `C (log (n T))^k` (every `C` and every `k`) there is `δ > 0` such that for all large `T`
  every machine within the budget (clocked or not) has regret at least `T^δ √(n T)` on some loss
  sequence.
* `not_minimaxPolylogAchievable_of_polylogPenaltyAt`: the negative statement refutes the
  positive one.
-/

namespace Pool.P0001

/-- A family of machines, one for each number of arms `n ≥ 1` and each horizon `T`.
(There is no machine on `0` arms: `PMF (Fin 0)` is empty.) -/
abbrev Family := (n T : ℕ) → 1 ≤ n → Machine n

/-- The machines `F n T` with `1 ≤ n ≤ T` use at most `C (log (n T))^k` bits of memory. -/
def MemoryBound (F : Family) (C : ℝ) (k : ℕ) : Prop :=
  ∀ (n T : ℕ) (hn : 1 ≤ n), n ≤ T → (F n T hn).memBits ≤ C * Real.log (n * T) ^ k

/-- For all `1 ≤ n ≤ T` and every loss sequence, `F n T` has regret at most `R n T` over the
rounds `0, …, T - 1`. -/
def RegretBound (F : Family) (R : ℕ → ℕ → ℝ) : Prop :=
  ∀ (n T : ℕ) (hn : 1 ≤ n), n ≤ T → ∀ ℓ : LossSeq n, regret (F n T hn) ℓ T ≤ R n T

/-- Positive resolution: homogeneous machines with polylogarithmic memory and regret
`Õ(√(n T))`, for all `1 ≤ n ≤ T`. -/
def MinimaxPolylogAchievable : Prop :=
  ∃ F : Family, (∀ n T hn, (F n T hn).IsHomogeneous) ∧
    (∃ (C : ℝ) (k : ℕ), MemoryBound F C k) ∧
    ∃ (C' : ℝ) (k' : ℕ), RegretBound F fun n T => C' * Real.sqrt (n * T) * Real.log (n * T) ^ k'

/-- Negative statement for the family `n = ⌊T ^ α⌋` with `0 < α ≤ 1`: whatever the
polylogarithmic budget `C (log (n T))^k`, some `δ > 0` works for all large `T`: every machine on
`⌊T ^ α⌋` arms within the budget has regret at least `T ^ δ √(n T)` on some oblivious loss sequence.
The range `0 < α ≤ 1` is part of the statement: for `α < 0`, `⌊T ^ α⌋ = 0` for `T ≥ 2` and there is
no machine on `0` arms, so the rest would hold vacuously. -/
def PolylogPenaltyAt (α : ℝ) : Prop :=
  0 < α ∧ α ≤ 1 ∧ ∀ (C : ℝ) (k : ℕ), ∃ δ : ℝ, 0 < δ ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
    ∀ M : Machine ⌊(T : ℝ) ^ α⌋₊,
      M.memBits ≤ C * Real.log (⌊(T : ℝ) ^ α⌋₊ * T) ^ k →
      ∃ ℓ : LossSeq ⌊(T : ℝ) ^ α⌋₊,
        (T : ℝ) ^ δ * Real.sqrt (⌊(T : ℝ) ^ α⌋₊ * T) ≤ regret M ℓ T

lemma one_le_floor_rpow {α : ℝ} (hα : 0 < α) {T : ℕ} (hT : 1 ≤ T) :
    1 ≤ ⌊(T : ℝ) ^ α⌋₊ := by
  rw [Nat.one_le_floor_iff]
  exact Real.one_le_rpow (by exact_mod_cast hT) hα.le

lemma floor_rpow_le {α : ℝ} (hα : α ≤ 1) {T : ℕ} (hT : 1 ≤ T) :
    ⌊(T : ℝ) ^ α⌋₊ ≤ T := by
  apply Nat.floor_le_of_le
  calc (T : ℝ) ^ α ≤ (T : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hT) hα
    _ = T := Real.rpow_one _

/-- The negative statement for `n = ⌊T ^ α⌋` (with its built-in `0 < α ≤ 1`) refutes the positive
resolution. -/
theorem not_minimaxPolylogAchievable_of_polylogPenaltyAt {α : ℝ}
    (h : PolylogPenaltyAt α) : ¬ MinimaxPolylogAchievable := by
  rintro ⟨F, -, ⟨C, k, hmem⟩, C', k', hreg⟩
  obtain ⟨hα0, hα1, h⟩ := h
  obtain ⟨δ, hδ, T₀, hT₀⟩ := h C k
  -- eventually `|C'| 2^k' (log x)^k' < x^δ`
  have hlo := (isLittleO_log_rpow_rpow_atTop (k' : ℝ) hδ)
  have hε : (0 : ℝ) < 1 / (2 * (|C'| * 2 ^ k' + 1)) := by positivity
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 (hlo.def hε)
  set T : ℕ := max (max T₀ ⌈x₀⌉₊) 2 with hTdef
  have hT1 : 1 ≤ T := le_trans (by norm_num) (le_max_right _ _)
  have hTx : x₀ ≤ T := by
    have : ⌈x₀⌉₊ ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
    exact (Nat.le_ceil x₀).trans (by exact_mod_cast this)
  set n := ⌊(T : ℝ) ^ α⌋₊
  have hn1 : 1 ≤ n := one_le_floor_rpow hα0 hT1
  have hnT : n ≤ T := floor_rpow_le hα1 hT1
  obtain ⟨ℓ, hℓ⟩ := hT₀ T (le_trans (le_max_left _ _) (le_max_left _ _)) (F n T hn1)
    (hmem n T hn1 hnT)
  have hup : regret (F n T hn1) ℓ T ≤ C' * Real.sqrt (n * T) * Real.log (n * T) ^ k' :=
    hreg n T hn1 hnT ℓ
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  have hsq : 0 < Real.sqrt (n * T) := Real.sqrt_pos.2 (by positivity)
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by exact_mod_cast hT1)
  have hlog_nT : 0 ≤ Real.log (n * T) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    nlinarith)
  have hlog_le : Real.log (n * T) ≤ 2 * Real.log T := by
    rw [two_mul, ← Real.log_mul hTpos.ne' hTpos.ne']
    apply Real.log_le_log (by positivity)
    have : (n : ℝ) ≤ T := by exact_mod_cast hnT
    nlinarith
  have hpow_le : Real.log (n * T) ^ k' ≤ 2 ^ k' * Real.log T ^ k' := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hlog_nT hlog_le k'
  -- `T^δ ≤ C' log(nT)^k'`
  have h1 : (T : ℝ) ^ δ ≤ C' * Real.log (n * T) ^ k' := by
    have := hℓ.trans hup
    have h' : (T : ℝ) ^ δ * Real.sqrt (n * T) ≤ (C' * Real.log (n * T) ^ k') * Real.sqrt (n * T) := by
      linarith
    exact le_of_mul_le_mul_right h' hsq
  have h2 : C' * Real.log (n * T) ^ k' ≤ |C'| * 2 ^ k' * Real.log T ^ k' := by
    calc C' * Real.log (n * T) ^ k' ≤ |C'| * Real.log (n * T) ^ k' :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hlog_nT _)
      _ ≤ |C'| * (2 ^ k' * Real.log T ^ k') := mul_le_mul_of_nonneg_left hpow_le (abs_nonneg _)
      _ = _ := by ring
  have h3 := hx₀ T hTx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlogT _),
    abs_of_nonneg (Real.rpow_nonneg hTpos.le _), Real.rpow_natCast] at h3
  have hTδ : 0 < (T : ℝ) ^ δ := Real.rpow_pos_of_pos hTpos δ
  have h4 : |C'| * 2 ^ k' * Real.log T ^ k' ≤ (|C'| * 2 ^ k' + 1) * Real.log T ^ k' := by
    nlinarith [pow_nonneg hlogT k']
  have h5 : (|C'| * 2 ^ k' + 1) * Real.log T ^ k' ≤ (T : ℝ) ^ δ / 2 := by
    have hpos : (0 : ℝ) < |C'| * 2 ^ k' + 1 := by positivity
    calc (|C'| * 2 ^ k' + 1) * Real.log T ^ k'
        ≤ (|C'| * 2 ^ k' + 1) * (1 / (2 * (|C'| * 2 ^ k' + 1)) * (T : ℝ) ^ δ) :=
          mul_le_mul_of_nonneg_left h3 hpos.le
      _ = (T : ℝ) ^ δ / 2 := by field_simp
  linarith

end Pool.P0001
