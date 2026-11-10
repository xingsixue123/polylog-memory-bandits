import Pool.P0023.Concentration

/-!
# The implicit-exploration (IX) one-step exponential bound (Neu 2015, Lemma 1, one round)

For a loss `ℓ ∈ [0,1]`, sampling probability `p ∈ (0,1]` and IX parameter `γ > 0`, the IX estimate is
`ℓ̂ = ℓ·1[sampled]/(p + γ)`. Then `E exp(2γ ℓ̂) ≤ exp(2γ ℓ)`:

  `p · exp(2γ ℓ/(p+γ)) + (1 - p) ≤ exp(2γ ℓ)`   (`ix_step`).
-/

open Real

namespace Pool.P0047

/-- `exp(2γℓ/(p+γ)) ≤ 1 + 2γℓ/p` for `ℓ ∈ [0,1]`, `p > 0`, `γ > 0`. -/
lemma exp_ix_le {ℓ p γ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hp : 0 < p) (hγ : 0 < γ) :
    exp (2 * γ * ℓ / (p + γ)) ≤ 1 + 2 * γ * ℓ / p := by
  set z := 2 * γ * ℓ / p with hz
  have hz0 : 0 ≤ z := by positivity
  -- 2γℓ/(p+γ) ≤ 2γℓ/(p+γℓ) = 2z/(z+2)
  have h1 : 2 * γ * ℓ / (p + γ) ≤ 2 * z / (z + 2) := by
    have hpz : 2 * z / (z + 2) = 2 * γ * ℓ / (p + γ * ℓ) := by
      rw [hz]; field_simp; ring
    rw [hpz]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    nlinarith
  have h2 := Real.le_log_one_add_of_nonneg hz0
  calc exp (2 * γ * ℓ / (p + γ)) ≤ exp (log (1 + z)) := exp_le_exp.mpr (h1.trans h2)
    _ = 1 + z := exp_log (by linarith)

/-- **IX one-step bound.** -/
theorem ix_step {ℓ p γ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ 1) (hp : 0 < p) (hp1 : p ≤ 1) (hγ : 0 < γ) :
    p * exp (2 * γ * ℓ / (p + γ)) + (1 - p) ≤ exp (2 * γ * ℓ) := by
  have h := exp_ix_le hℓ0 hℓ1 hp hγ
  have h2 : p * exp (2 * γ * ℓ / (p + γ)) ≤ p + 2 * γ * ℓ := by
    calc p * exp (2 * γ * ℓ / (p + γ)) ≤ p * (1 + 2 * γ * ℓ / p) := mul_le_mul_of_nonneg_left h hp.le
      _ = p + 2 * γ * ℓ := by field_simp
  have h3 := add_one_le_exp (2 * γ * ℓ)
  linarith

end Pool.P0047

namespace Pool.P0047

open Finset Pool.P0001 Pool.P0012 Pool.P0023
open scoped ENNReal

variable {n : ℕ}

/-- The IX increment `2γ(ℓ̂ - ℓ)` for arm `i` when arm `a` is pulled with probability vector `act t s`. -/
noncomputable def ixIncr (M : Machine n) (ℓ : LossSeq n) (γ : ℝ) (i : Fin n) (t : ℕ) (s : M.State) (a : Fin n) : ℝ :=
  2 * γ * ((if a = i then ((ℓ t i).toNat : ℝ) / ((M.act t s i).toReal + γ) else 0) - ((ℓ t i).toNat : ℝ))

lemma sum_act_toReal (M : Machine n) (t : ℕ) (s : M.State) : ∑ a, (M.act t s a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ a),
    ← tsum_fintype (L := .unconditional _) (fun a => M.act t s a), PMF.tsum_coe, ENNReal.toReal_one]

lemma sum_next_toReal (M : Machine n) (t : ℕ) (s : M.State) (a : Fin n) (b : Bool) :
    ∑ s', (M.next t s a b s').toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun s' _ => PMF.apply_ne_top _ s'),
    ← tsum_fintype (L := .unconditional _) (fun s' => M.next t s a b s'), PMF.tsum_coe, ENNReal.toReal_one]

/-- The IX exponential moment along one round: `Σ_a act(a) exp(ixIncr a) ≤ 1`. -/
lemma sum_act_exp_ixIncr_le (M : Machine n) (ℓ : LossSeq n) {γ : ℝ} (hγ : 0 < γ) (i : Fin n) (t : ℕ)
    (s : M.State) : ∑ a, (M.act t s a).toReal * exp (ixIncr M ℓ γ i t s a) ≤ 1 := by
  set p := (M.act t s i).toReal with hp
  set L := ((ℓ t i).toNat : ℝ) with hL
  have hL0 : 0 ≤ L := by positivity
  have hL1 : L ≤ 1 := by rw [hL]; cases ℓ t i <;> simp
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hsplit : ∑ a, (M.act t s a).toReal * exp (ixIncr M ℓ γ i t s a) =
      p * exp (2 * γ * (L / (p + γ) - L)) + (1 - p) * exp (-(2 * γ * L)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : ∑ a ∈ Finset.univ.erase i, (M.act t s a).toReal * exp (ixIncr M ℓ γ i t s a) =
        (∑ a ∈ Finset.univ.erase i, (M.act t s a).toReal) * exp (-(2 * γ * L)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a ha => ?_
      have hai : a ≠ i := Finset.ne_of_mem_erase ha
      simp [ixIncr, hai, hL]
    have hsum : ∑ a ∈ Finset.univ.erase i, (M.act t s a).toReal = 1 - p := by
      have := sum_act_toReal M t s
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at this
      linarith
    rw [hrest, hsum]
    simp [ixIncr, hp, hL]
  rw [hsplit]
  rcases eq_or_lt_of_le hp0 with h0 | hpos
  · rw [← h0]
    simp only [zero_mul, zero_add, sub_zero, one_mul]
    have : 0 ≤ 2 * γ * L := mul_nonneg (mul_nonneg (by norm_num) hγ.le) hL0
    exact exp_le_one_iff.mpr (by linarith)
  · have hp1 : p ≤ 1 := by
      have := sum_act_toReal M t s
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at this
      have : 0 ≤ ∑ a ∈ Finset.univ.erase i, (M.act t s a).toReal :=
        Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
      linarith
    have hstep := ix_step hL0 hL1 hpos hp1 hγ
    have e1 : p * exp (2 * γ * (L / (p + γ) - L)) = exp (-(2 * γ * L)) * (p * exp (2 * γ * L / (p + γ))) := by
      rw [show 2 * γ * (L / (p + γ) - L) = -(2 * γ * L) + 2 * γ * L / (p + γ) by ring, exp_add]; ring
    rw [e1]
    have hpos' : 0 < exp (-(2 * γ * L)) := exp_pos _
    calc exp (-(2 * γ * L)) * (p * exp (2 * γ * L / (p + γ))) + (1 - p) * exp (-(2 * γ * L))
        = exp (-(2 * γ * L)) * (p * exp (2 * γ * L / (p + γ)) + (1 - p)) := by ring
      _ ≤ exp (-(2 * γ * L)) * exp (2 * γ * L) := mul_le_mul_of_nonneg_left hstep hpos'.le
      _ = 1 := by rw [← exp_add]; simp

/-- **IX concentration on the state law.** Let `Z` be a (ghost-tracked) process that starts at `0` and whose increment
along every transition of positive probability from a reachable state is the IX increment `2γ(ℓ̂_t(i) - ℓ_t(i))` of
arm `i`. Then for `0 < δ`, `P(Z_T ≥ log(1/δ)) ≤ δ`: the IX estimate of arm `i` exceeds its true cumulative loss by more
than `log(1/δ)/(2γ)` with probability at most `δ`, whatever the (adaptive) sampling probabilities. -/
theorem ix_concentration (M : Machine n) (ℓ : LossSeq n) {γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) (i : Fin n)
    (Z : ℕ → M.State → ℝ) {T : ℕ}
    (h0 : ∀ s, M.init s ≠ 0 → Z 0 s ≤ 0)
    (hZ : ∀ t, t < T → ∀ s, M.stateDist ℓ t s ≠ 0 → ∀ a s', M.act t s a ≠ 0 →
      M.next t s a (ℓ t a) s' ≠ 0 → Z (t + 1) s' = Z t s + ixIncr M ℓ γ i t s a) :
    probGe M ℓ T (Z T) (log (1 / δ)) ≤ δ := by
  have hsup : ∀ t, t < T → ∀ s, M.stateDist ℓ t s ≠ 0 →
      stepExp M ℓ t s (fun s' => exp (1 * Z (t + 1) s')) ≤ exp (1 * Z t s) := by
    intro t ht s hs
    unfold stepExp
    have hterm : ∀ a, (M.act t s a).toReal * ∑ s', (M.next t s a (ℓ t a) s').toReal * exp (1 * Z (t + 1) s') =
        (M.act t s a).toReal * (exp (Z t s) * exp (ixIncr M ℓ γ i t s a)) := by
      intro a
      by_cases ha : M.act t s a = 0
      · simp [ha]
      congr 1
      have : ∀ s', (M.next t s a (ℓ t a) s').toReal * exp (1 * Z (t + 1) s') =
          (M.next t s a (ℓ t a) s').toReal * (exp (Z t s) * exp (ixIncr M ℓ γ i t s a)) := by
        intro s'
        by_cases hn : M.next t s a (ℓ t a) s' = 0
        · simp [hn]
        rw [hZ t ht s hs a s' ha hn, one_mul, exp_add]
      rw [Finset.sum_congr rfl fun s' _ => this s', ← Finset.sum_mul, sum_next_toReal, one_mul]
    rw [Finset.sum_congr rfl fun a _ => hterm a]
    have : ∑ a, (M.act t s a).toReal * (exp (Z t s) * exp (ixIncr M ℓ γ i t s a)) =
        exp (Z t s) * ∑ a, (M.act t s a).toReal * exp (ixIncr M ℓ γ i t s a) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
    rw [this, one_mul]
    calc exp (Z t s) * ∑ a, (M.act t s a).toReal * exp (ixIncr M ℓ γ i t s a)
        ≤ exp (Z t s) * 1 := mul_le_mul_of_nonneg_left (sum_act_exp_ixIncr_le M ℓ hγ i t s) (exp_pos _).le
      _ = exp (Z t s) := mul_one _
  have hE := expect_exp_le M ℓ Z 1 T hsup
  have hE0 : expect M ℓ 0 (fun s => exp (1 * Z 0 s)) ≤ 1 := by
    unfold Pool.P0012.expect
    calc ∑ s, (M.stateDist ℓ 0 s).toReal * exp (1 * Z 0 s)
        ≤ ∑ s, (M.stateDist ℓ 0 s).toReal * 1 := by
          refine Finset.sum_le_sum fun s _ => ?_
          by_cases hs : M.init s = 0
          · have : M.stateDist ℓ 0 s = 0 := hs
            simp [this]
          refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          rw [one_mul]; exact exp_le_one_iff.mpr (h0 s hs)
      _ = 1 := by
          simp only [mul_one]
          rw [← ENNReal.toReal_sum (fun s _ => PMF.apply_ne_top _ s),
            ← tsum_fintype (L := .unconditional _) (fun s => M.stateDist ℓ 0 s), PMF.tsum_coe,
            ENNReal.toReal_one]
  have hM := probGe_le_expect_exp M ℓ T (Z T) (log (1 / δ)) (κ := 1) zero_le_one
  have hrel : expect M ℓ T (fun s => exp (1 * (Z T s - log (1 / δ)))) =
      δ * expect M ℓ T (fun s => exp (1 * Z T s)) := by
    unfold Pool.P0012.expect
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [one_mul]
    rw [exp_sub, exp_log (by positivity)]
    field_simp
  rw [hrel] at hM
  calc probGe M ℓ T (Z T) (log (1 / δ)) ≤ δ * expect M ℓ T (fun s => exp (1 * Z T s)) := hM
    _ ≤ δ * 1 := mul_le_mul_of_nonneg_left (hE.trans hE0) hδ.le
    _ = δ := mul_one δ

end Pool.P0047
