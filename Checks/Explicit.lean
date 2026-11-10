import Pool.P0294.Statement

/-!
# Explicit constants behind `Pool.P0294.main`

`Pool.P0294.main : MinimaxPolylogAchievable` is existential in `C, k, C', k'`. Here the witness of
P0173's `minimax_of_StepAtIn` is re-run (its proof copied, unchanged except that the existentials are
replaced by explicit values) on the step obtained from the library:

  `Pool.P0294.goodBound` (Cg = 10^17 * 5^30, kg = 30)
  → `Pool.P0292.famHyp_of_good`   : FamHyp (CF Cg) (max 28 30)
  → `Pool.P0278.stepAtIn_of_famHyp`: StepAtIn CoinCls (max (CF Cg) 0 + 6) 30
  → P0173's horizon recursion (`exists_machineIn`).

Result (`explicit_numeric`): one homogeneous family with
  memory  ≤ 3·10^47 · log(nT)^31 bits, and
  regret  ≤ 2·10^95 · √(nT) · log(nT)^60,
for all 1 ≤ n ≤ T.  So k = 31 and k' = 60.
-/

open Pool.P0001 Pool.P0161 Pool.P0173

namespace Audit

/-- The step constant `c = max (CF Cg) 0 + 6` with `Cg = 10^17 · 5^30`. -/
noncomputable def cS : ℝ := max (Pool.P0292.CF (100000000000000000 * 5 ^ 30)) 0 + 6

/-- The step exponent is `max 28 30 = 30`. -/
theorem step30 : StepAtIn (fun {n} M => CoinCls (n := n) M) cS 30 := by
  have h := Pool.P0278.stepAtIn_of_famHyp (Pool.P0292.famHyp_of_good Pool.P0294.goodBound)
  have e : max 28 30 = (30 : ℕ) := by decide
  rw [e] at h
  exact h

/-- The step constant in closed form. -/
theorem cS_eq : cS = 12 + 5000000000000000 * 5 ^ 28 + 100000000000000000 * 5 ^ 30 + 160 * 600001 ^ 2 * 5 ^ 26 := by
  unfold cS Pool.P0292.CF
  have h1 : max ((100000000000000000 : ℝ) * 5 ^ 30) 0 = 100000000000000000 * 5 ^ 30 :=
    max_eq_left (by positivity)
  rw [h1]
  have h2 : max ((6 : ℝ) + 5000000000000000 * 5 ^ 28 + 100000000000000000 * 5 ^ 30 + 160 * 600001 ^ 2 * 5 ^ 26) 0
      = 6 + 5000000000000000 * 5 ^ 28 + 100000000000000000 * 5 ^ 30 + 160 * 600001 ^ 2 * 5 ^ 26 :=
    max_eq_left (by positivity)
  rw [h2]; ring

theorem one_le_cS : 1 ≤ cS := by rw [cS_eq]; norm_num

theorem cS_le : cS ≤ 10 ^ 38 := by rw [cS_eq]; norm_num

/-- **Explicit witness** (P0173's `minimax_of_StepAtIn`, copied with the existentials made explicit):
memory `≤ 2·c₁·2^30·log(nT)^31`, regret `≤ 12·c₁²·4^30·√(nT)·log(nT)^60`, `c₁ = max cS 1`. -/
theorem explicit_raw :
    ∃ F : Family, (∀ n T hn, (F n T hn).IsHomogeneous) ∧
      MemoryBound F (2 * max cS 1 * 2 ^ 30) (30 + 1) ∧
      RegretBound F (fun n T => 12 * max cS 1 ^ 2 * 4 ^ 30 * Real.sqrt (n * T) * Real.log (n * T) ^ (2 * 30)) := by
  classical
  have hstep := step30
  have hzero := coinCls_zero
  set c := cS
  set k := 30
  let F : Family := fun n T hn =>
    if h : n ≤ T ∧ 2 ≤ n then Classical.choose (exists_machineIn hstep hzero hn T (le_trans hn h.1))
    else triv n hn
  have hspec : ∀ n T (hn : 1 ≤ n) (h : n ≤ T ∧ 2 ≤ n), F n T hn =
      Classical.choose (exists_machineIn hstep hzero hn T (le_trans hn h.1)) := by
    intro n T hn h; simp only [F, dif_pos h]
  have htriv : ∀ n T (hn : 1 ≤ n) (h : ¬ (n ≤ T ∧ 2 ≤ n)), F n T hn = triv n hn := by
    intro n T hn h; simp only [F, dif_neg h]
  set c₁ := max c 1 with hc₁
  have hc₁1 : 1 ≤ c₁ := le_max_right _ _
  have hLam : ∀ n T, 2 ≤ n → n ≤ T →
      Lam c k n T ≤ c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ k := by
    intro n T h2 hnT
    have hl := one_le_log h2 hnT
    unfold Lam Lg
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) k)
      (by linarith)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro n T hn
    by_cases h : n ≤ T ∧ 2 ≤ n
    · rw [hspec n T hn h]
      exact (Classical.choose_spec (exists_machineIn hstep hzero hn T (le_trans hn h.1))).2.1
    · rw [htriv n T hn h]; exact triv_isHomogeneous n hn
  · intro n T hn hnT
    have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := Lg_nonneg hn (le_trans hn hnT)
    by_cases h : n ≤ T ∧ 2 ≤ n
    · rw [hspec n T hn h]
      have hm := (Classical.choose_spec (exists_machineIn hstep hzero hn T (le_trans hn h.1))).2.2.1
      have hΛ0 : 0 ≤ Lam c k n T := le_trans zero_le_one (one_le_Lam hn (le_trans hn hnT))
      calc _ ≤ (Nat.log 2 T : ℝ) * Lam c k n T := hm
        _ ≤ (2 * Real.log ((n : ℝ) * T)) * (c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ k) :=
            mul_le_mul (natLog_le_two_log hn hnT) (hLam n T h.2 hnT) hΛ0 (by positivity)
        _ = 2 * c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ (k + 1) := by ring
    · rw [htriv n T hn h, triv_memBits]; positivity
  · intro n T hn hnT ℓ
    have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := Lg_nonneg hn (le_trans hn hnT)
    by_cases h : n ≤ T ∧ 2 ≤ n
    · rw [hspec n T hn h]
      have hr := (Classical.choose_spec (exists_machineIn hstep hzero hn T (le_trans hn h.1))).2.2.2 ℓ
      have hΛ1 := one_le_Lam (c := c) (k := k) hn (le_trans hn hnT)
      have hΛ2 : Lam c k n T ^ 2 ≤ c₁ ^ 2 * 4 ^ k * Real.log ((n : ℝ) * T) ^ (2 * k) := by
        calc Lam c k n T ^ 2 ≤ (c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ k) ^ 2 :=
              pow_le_pow_left₀ (by linarith) (hLam n T h.2 hnT) 2
          _ = c₁ ^ 2 * 4 ^ k * Real.log ((n : ℝ) * T) ^ (2 * k) := by
              rw [show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
                pow_mul]; ring
      calc _ ≤ 12 * Lam c k n T ^ 2 * Real.sqrt (n * T) := hr
        _ ≤ 12 * (c₁ ^ 2 * 4 ^ k * Real.log ((n : ℝ) * T) ^ (2 * k)) * Real.sqrt (n * T) := by
            gcongr
        _ = 12 * c₁ ^ 2 * 4 ^ k * Real.sqrt (n * T) * Real.log ((n : ℝ) * T) ^ (2 * k) := by ring
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [regret_one]; positivity

/-- **Explicit numeric version**: memory `≤ 3·10^47·log(nT)^31` bits, regret
`≤ 2·10^95·√(nT)·log(nT)^60`, for all `1 ≤ n ≤ T`, homogeneous machines. -/
theorem explicit_numeric :
    ∃ F : Family, (∀ n T hn, (F n T hn).IsHomogeneous) ∧
      MemoryBound F (3 * 10 ^ 47) 31 ∧
      RegretBound F (fun n T => 2 * 10 ^ 95 * Real.sqrt (n * T) * Real.log (n * T) ^ 60) := by
  obtain ⟨F, hH, hM, hR⟩ := explicit_raw
  have hc1 : max cS 1 = cS := max_eq_left one_le_cS
  have hcl : cS ≤ 10 ^ 38 := cS_le
  have hc0 : 0 ≤ cS := le_trans zero_le_one one_le_cS
  refine ⟨F, hH, fun n T hn hnT => ?_, fun n T hn hnT ℓ => ?_⟩
  · have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := Lg_nonneg hn (le_trans hn hnT)
    have h := hM n T hn hnT
    rw [hc1] at h
    have hC : 2 * cS * 2 ^ 30 ≤ (3 * 10 ^ 47 : ℝ) := by
      have : 2 * cS * 2 ^ 30 ≤ 2 * 10 ^ 38 * 2 ^ 30 := by
        have : (0 : ℝ) ≤ 2 ^ 30 := by positivity
        nlinarith
      linarith [show (2 : ℝ) * 10 ^ 38 * 2 ^ 30 ≤ 3 * 10 ^ 47 by norm_num]
    calc (F n T hn).memBits ≤ 2 * cS * 2 ^ 30 * Real.log (n * T) ^ (30 + 1) := h
      _ ≤ 3 * 10 ^ 47 * Real.log (n * T) ^ 31 :=
          mul_le_mul_of_nonneg_right hC (pow_nonneg hl0 _)
  · have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := Lg_nonneg hn (le_trans hn hnT)
    have h := hR n T hn hnT ℓ
    simp only at h
    rw [hc1] at h
    have hC : 12 * cS ^ 2 * 4 ^ 30 ≤ (2 * 10 ^ 95 : ℝ) := by
      have hsq : cS ^ 2 ≤ (10 ^ 38) ^ 2 := pow_le_pow_left₀ hc0 hcl 2
      have : 12 * cS ^ 2 * 4 ^ 30 ≤ 12 * (10 ^ 38) ^ 2 * 4 ^ 30 := by
        have : (0 : ℝ) ≤ 4 ^ 30 := by positivity
        nlinarith
      linarith [show (12 : ℝ) * (10 ^ 38) ^ 2 * 4 ^ 30 ≤ 2 * 10 ^ 95 by norm_num]
    have hs : 0 ≤ Real.sqrt ((n : ℝ) * T) := Real.sqrt_nonneg _
    calc regret (F n T hn) ℓ T ≤ 12 * cS ^ 2 * 4 ^ 30 * Real.sqrt (n * T) * Real.log (n * T) ^ (2 * 30) := h
      _ ≤ 2 * 10 ^ 95 * Real.sqrt (n * T) * Real.log (n * T) ^ 60 := by
          have := mul_le_mul_of_nonneg_right hC hs
          exact mul_le_mul_of_nonneg_right this (pow_nonneg hl0 _)

end Audit

#print axioms Audit.explicit_numeric
#print axioms Audit.explicit_raw
#check @Audit.explicit_numeric
