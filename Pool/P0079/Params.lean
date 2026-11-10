import Pool.P0042.MergeLemma

/-!
# Parameter arithmetic for the merge lemma

* `delta_le`: P0042's per-iteration failure term is `≤ 2 (N+1)^(-c)` once `p k ≥ (L+1+c) log(N+1) + log(2L)` and
  `M0 ≥ 32 L c log(N+1)` (both polylogarithmic in `N`).
* `one_sub_pow_le_exp`, `geom_le`, `one_sub_pow_ge_half` (`(1-p)^m ≥ 1/2` if `pm ≤ 1/2`), and `rho_half`
  (`(1 - 1/(4R))^(4R) · 2 ≤ 1`: `4R` iterations halve P0042's shrink factor).
-/

open Real Finset

namespace Pool.P0079

theorem one_sub_pow_le_exp {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) : (1 - p) ^ k ≤ exp (-(p * k)) := by
  have h : 1 - p ≤ exp (-p) := by linarith [add_one_le_exp (-p)]
  calc (1 - p) ^ k ≤ (exp (-p)) ^ k := pow_le_pow_left₀ (by linarith) h k
    _ = exp (-(p * k)) := by rw [← exp_nat_mul]; ring_nf

theorem geom_le (N L : ℕ) : ∑ m ∈ range L, (N : ℝ) ^ m ≤ L * ((N : ℝ) + 1) ^ L := by
  calc ∑ m ∈ range L, (N : ℝ) ^ m ≤ ∑ m ∈ range L, ((N : ℝ) + 1) ^ L := by
        apply sum_le_sum; intro m hm
        rw [mem_range] at hm
        calc (N : ℝ) ^ m ≤ ((N : ℝ) + 1) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ ≤ ((N : ℝ) + 1) ^ L := pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]) hm.le
    _ = L * ((N : ℝ) + 1) ^ L := by simp

/-- **P0042's failure term is small.** If `p k ≥ (L + 1 + c) log (N + 1) + log (2L)` and
`M0 ≥ 32 L c log (N + 1)`, then `delta N p L k M0 ≤ 2 (N + 1)^(-c)`. -/
theorem delta_le {N L k : ℕ} {p M0 c : ℝ} (hL : 1 ≤ L) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hk : (L + 1 + c) * log (N + 1) + log (2 * L) ≤ p * k) (hM : 32 * L * c * log (N + 1) ≤ M0) :
    Pool.P0042.delta N p L k M0 ≤ 2 * exp (-(c * log (N + 1))) := by
  unfold Pool.P0042.delta
  have hN1 : (1 : ℝ) ≤ N + 1 := by linarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]
  have hlogN : 0 ≤ log ((N : ℝ) + 1) := log_nonneg hN1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hpow := one_sub_pow_le_exp hp0 hp1 k
  have hcoef : (((N + 1) * L * N : ℕ) : ℝ) + ∑ m ∈ range L, (N : ℝ) ^ m ≤ 2 * L * ((N : ℝ) + 1) ^ (L + 1) := by
    have h1 : (((N + 1) * L * N : ℕ) : ℝ) ≤ L * ((N : ℝ) + 1) ^ (L + 1) := by
      push_cast
      have : (N : ℝ) ≤ ((N : ℝ) + 1) ^ L := by
        calc (N : ℝ) ≤ (N : ℝ) + 1 := by linarith
          _ = ((N : ℝ) + 1) ^ 1 := (pow_one _).symm
          _ ≤ ((N : ℝ) + 1) ^ L := pow_le_pow_right₀ hN1 hL
      rw [pow_succ]
      have h0 : (0 : ℝ) ≤ L * ((N : ℝ) + 1) := by positivity
      have := mul_le_mul_of_nonneg_left this h0
      linarith
    have h2 := geom_le N L
    have h3 : ((N : ℝ) + 1) ^ L ≤ ((N : ℝ) + 1) ^ (L + 1) := pow_le_pow_right₀ hN1 (Nat.le_succ L)
    nlinarith
  have hexp1 : 2 * L * ((N : ℝ) + 1) ^ (L + 1) * exp (-(p * k)) ≤ exp (-(c * log (N + 1))) := by
    have : 2 * L * ((N : ℝ) + 1) ^ (L + 1) = exp (log (2 * L) + (L + 1) * log (N + 1)) := by
      rw [exp_add, exp_log (by positivity), ← rpow_natCast, rpow_def_of_pos (by linarith)]
      push_cast; ring_nf
    rw [this, ← exp_add]
    apply exp_le_exp.2
    nlinarith
  have hexp2 : exp (-(M0 / (32 * L))) ≤ exp (-(c * log (N + 1))) := by
    apply exp_le_exp.2
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    nlinarith
  have hsum : ((((N + 1) * L * N : ℕ) : ℝ) * (1 - p) ^ k + (∑ m ∈ range L, (N : ℝ) ^ m) * (1 - p) ^ k) ≤
      2 * L * ((N : ℝ) + 1) ^ (L + 1) * exp (-(p * k)) := by
    have hq : 0 ≤ (1 - p) ^ k := pow_nonneg (by linarith) k
    have hS : 0 ≤ (((N + 1) * L * N : ℕ) : ℝ) + ∑ m ∈ range L, (N : ℝ) ^ m := by positivity
    calc _ = ((((N + 1) * L * N : ℕ) : ℝ) + ∑ m ∈ range L, (N : ℝ) ^ m) * (1 - p) ^ k := by ring
      _ ≤ (2 * L * ((N : ℝ) + 1) ^ (L + 1)) * exp (-(p * k)) :=
          mul_le_mul hcoef hpow hq (by positivity)
  linarith


/-- `(1 - p)^m ≥ 1/2` when `p m ≤ 1/2`. -/
theorem one_sub_pow_ge_half {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {m : ℕ} (h : p * m ≤ 1 / 2) :
    1 / 2 ≤ (1 - p) ^ m := by
  have := one_add_mul_le_pow (a := -p) (by linarith) m
  rw [← sub_eq_add_neg] at this
  nlinarith

/-- The shrink factor of `4R` merge iterations: `(1 - 1/(4R))^(4R) · 2 ≤ 1`. -/
theorem rho_half {R : ℕ} (hR : 1 ≤ R) : (1 - 1 / (4 * R : ℝ)) ^ (4 * R) * 2 ≤ 1 := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hx0 : 0 ≤ 1 / (4 * R : ℝ) := by positivity
  have hx1 : 1 / (4 * R : ℝ) ≤ 1 := by
    have : (1:ℝ) ≤ R := by exact_mod_cast hR
    rw [div_le_one (by positivity)]; linarith
  have h1 := one_sub_pow_le_exp hx0 hx1 (4 * R)
  have h2 : 1 / (4 * R : ℝ) * ((4 * R : ℕ) : ℝ) = 1 := by push_cast; field_simp
  rw [h2] at h1
  have h3 : exp (-1 : ℝ) * 2 ≤ 1 := by
    have := exp_one_gt_d9
    rw [exp_neg, inv_mul_eq_div, div_le_one (exp_pos 1)]
    linarith
  calc (1 - 1 / (4 * R : ℝ)) ^ (4 * R) * 2 ≤ exp (-1) * 2 := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        simpa using h1
    _ ≤ 1 := h3

end Pool.P0079
