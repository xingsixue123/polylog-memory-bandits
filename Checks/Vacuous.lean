import Mathlib

/-!
# The explicit regret bound of `Audit.explicit_numeric` (`Checks/Explicit.lean`) is at least `T` for
`2 ≤ n ≤ T ≤ 4·10^190`

Every machine has regret `≤ T` (`Pool.P0001.regret_le`), so on this range the bound
`2·10^95·√(nT)·log(nT)^60` carries no information. (By hand: it stays `≥ T` up to `T ≈ 10^564` for `n = 2`.)
-/

namespace Audit

theorem bound_ge_T (n T : ℕ) (h2 : 2 ≤ n) (hnT : n ≤ T) (hT : (T : ℝ) ≤ 4 * 10 ^ 190) :
    (T : ℝ) ≤ 2 * 10 ^ 95 * Real.sqrt (n * T) * Real.log (n * T) ^ 60 := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast h2
  have hT2 : (2 : ℝ) ≤ T := by exact_mod_cast (le_trans h2 hnT)
  have hT0 : (0 : ℝ) ≤ T := by linarith
  -- log(nT) ≥ 1
  have hlog : 1 ≤ Real.log ((n : ℝ) * T) := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) * T := by nlinarith
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hpow : 1 ≤ Real.log ((n : ℝ) * T) ^ 60 := one_le_pow₀ hlog
  -- √(nT) ≥ √T
  have hs : Real.sqrt T ≤ Real.sqrt ((n : ℝ) * T) := Real.sqrt_le_sqrt (by nlinarith)
  -- √T ≤ 2·10^95
  have hsT : Real.sqrt T ≤ 2 * 10 ^ 95 := by
    rw [Real.sqrt_le_left (by norm_num)]
    calc (T : ℝ) ≤ 4 * 10 ^ 190 := hT
      _ = (2 * 10 ^ 95) ^ 2 := by norm_num
  have hTT : (T : ℝ) = Real.sqrt T * Real.sqrt T := (Real.mul_self_sqrt hT0).symm
  have hsq0 : 0 ≤ Real.sqrt (T : ℝ) := Real.sqrt_nonneg _
  calc (T : ℝ) = Real.sqrt T * Real.sqrt T := hTT
    _ ≤ (2 * 10 ^ 95) * Real.sqrt ((n : ℝ) * T) := mul_le_mul hsT hs hsq0 (by norm_num)
    _ = 2 * 10 ^ 95 * Real.sqrt ((n : ℝ) * T) * 1 := by ring
    _ ≤ 2 * 10 ^ 95 * Real.sqrt ((n : ℝ) * T) * Real.log ((n : ℝ) * T) ^ 60 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

end Audit

#print axioms Audit.bound_ge_T
