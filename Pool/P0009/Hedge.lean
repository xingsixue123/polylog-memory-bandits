import Pool.Prelude

/-!
# Exponential weights (Hedge) with nonnegative losses: the local-norm regret inequality

A deterministic statement (no probability). Let `ι` be a finite nonempty set of arms, `q i > 0` prior
weights, `η > 0` a learning rate and `c t i ≥ 0` arbitrary losses (in applications: importance-weighted
loss estimates, possibly chosen adaptively; the inequality holds pathwise). The Hedge distribution is
`prob q η c t i ∝ q i · exp (-η · Σ_{s<t} c s i)`. Then for every arm `i` and horizon `T`

  Σ_{t<T} ⟨p t, c t⟩ - Σ_{t<T} c t i ≤ log ((Σ_j q j) / q i) / η + (η / 2) Σ_{t<T} ⟨p t, (c t)²⟩

(`hedge_regret`); with the uniform prior `q = 1` the first term is `log |ι| / η` (`hedge_regret_uniform`).
This is the inequality behind EXP3: feed importance-weighted estimates as `c`.

The proof is the standard potential argument, using `exp (-x) ≤ 1 - x + x²/2` for `x ≥ 0`
(`exp_neg_le_quadratic`).
-/

open Real Finset

namespace Pool.P0009

/-- `exp (-x) ≤ 1 - x + x²/2` for `x ≥ 0`. -/
theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) : exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have h1 : 1 + x + x ^ 2 / 2 ≤ exp x := quadratic_le_exp_of_nonneg hx
  rw [exp_neg, inv_eq_one_div, div_le_iff₀ (exp_pos x)]
  have h2 : 0 ≤ 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (x - 1)]
  calc (1 : ℝ) ≤ (1 - x + x ^ 2 / 2) * (1 + x + x ^ 2 / 2) := by
        nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]
    _ ≤ (1 - x + x ^ 2 / 2) * exp x := mul_le_mul_of_nonneg_left h1 h2

variable {ι : Type*} [Fintype ι]

/-- Cumulative loss of arm `i` over the rounds `0, …, t-1`. -/
def cum (c : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ := ∑ s ∈ range t, c s i

/-- Exponential weight of arm `i` at round `t`, with prior weight `q i`. -/
noncomputable def weight (q : ι → ℝ) (η : ℝ) (c : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  q i * exp (-η * cum c t i)

/-- The Hedge distribution at round `t` (prior `q`, learning rate `η`, losses `c`). -/
noncomputable def prob (q : ι → ℝ) (η : ℝ) (c : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  weight q η c t i / ∑ j, weight q η c t j

variable {q : ι → ℝ} {η : ℝ}

omit [Fintype ι] in
theorem weight_pos (hq : ∀ i, 0 < q i) (c : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    0 < weight q η c t i :=
  mul_pos (hq i) (exp_pos _)

theorem sum_weight_pos [Nonempty ι] (hq : ∀ i, 0 < q i) (c : ℕ → ι → ℝ) (t : ℕ) :
    0 < ∑ j, weight q η c t j :=
  Finset.sum_pos (fun j _ => weight_pos hq c t j) Finset.univ_nonempty

theorem prob_nonneg [Nonempty ι] (hq : ∀ i, 0 < q i) (c : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    0 ≤ prob q η c t i :=
  div_nonneg (weight_pos hq c t i).le (sum_weight_pos hq c t).le

theorem sum_prob [Nonempty ι] (hq : ∀ i, 0 < q i) (c : ℕ → ι → ℝ) (t : ℕ) :
    ∑ i, prob q η c t i = 1 := by
  simp only [prob, ← Finset.sum_div]
  exact div_self (sum_weight_pos hq c t).ne'

omit [Fintype ι] in
theorem weight_succ (c : ℕ → ι → ℝ) (t : ℕ) (i : ι) :
    weight q η c (t + 1) i = weight q η c t i * exp (-η * c t i) := by
  simp only [weight, cum, Finset.sum_range_succ, mul_assoc, ← exp_add]; ring_nf

/-- One step of the potential argument. -/
theorem log_sum_weight_succ_le [Nonempty ι] (hq : ∀ i, 0 < q i) (hη : 0 < η) (c : ℕ → ι → ℝ)
    (hc : ∀ t i, 0 ≤ c t i) (t : ℕ) :
    log (∑ j, weight q η c (t + 1) j) ≤ log (∑ j, weight q η c t j)
      - η * ∑ j, prob q η c t j * c t j + η ^ 2 / 2 * ∑ j, prob q η c t j * c t j ^ 2 := by
  set W := ∑ j, weight q η c t j with hW
  have hWpos : 0 < W := sum_weight_pos hq c t
  set a := ∑ j, prob q η c t j * c t j
  set b := ∑ j, prob q η c t j * c t j ^ 2
  have hstep : ∑ j, weight q η c (t + 1) j ≤ W * (1 - η * a + η ^ 2 / 2 * b) := by
    have : ∀ j, weight q η c (t + 1) j ≤
        W * (prob q η c t j * (1 - η * c t j + (η * c t j) ^ 2 / 2)) := by
      intro j
      rw [weight_succ]
      have hexp := exp_neg_le_quadratic (mul_nonneg hη.le (hc t j))
      have hp : W * prob q η c t j = weight q η c t j := by
        simp only [prob, ← hW]; field_simp
      calc weight q η c t j * exp (-η * c t j)
          = weight q η c t j * exp (-(η * c t j)) := by ring_nf
        _ ≤ weight q η c t j * (1 - η * c t j + (η * c t j) ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hexp (weight_pos hq c t j).le
        _ = W * (prob q η c t j * (1 - η * c t j + (η * c t j) ^ 2 / 2)) := by
            rw [← mul_assoc, hp]
    calc ∑ j, weight q η c (t + 1) j
        ≤ ∑ j, W * (prob q η c t j * (1 - η * c t j + (η * c t j) ^ 2 / 2)) :=
          Finset.sum_le_sum fun j _ => this j
      _ = W * (∑ j, prob q η c t j - η * a + η ^ 2 / 2 * b) := by
          rw [← Finset.mul_sum]; congr 1
          simp only [a, b, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ = W * (1 - η * a + η ^ 2 / 2 * b) := by rw [sum_prob hq]
  have hpos1 : 0 < ∑ j, weight q η c (t + 1) j := sum_weight_pos hq c (t + 1)
  have hfac : 0 < 1 - η * a + η ^ 2 / 2 * b := by
    by_contra hneg
    rw [not_lt] at hneg
    have : W * (1 - η * a + η ^ 2 / 2 * b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hWpos.le hneg
    linarith
  calc log (∑ j, weight q η c (t + 1) j) ≤ log (W * (1 - η * a + η ^ 2 / 2 * b)) :=
        log_le_log hpos1 hstep
    _ = log W + log (1 - η * a + η ^ 2 / 2 * b) := log_mul hWpos.ne' hfac.ne'
    _ ≤ log W + (-η * a + η ^ 2 / 2 * b) := by
        have := log_le_sub_one_of_pos hfac
        linarith
    _ = log W - η * a + η ^ 2 / 2 * b := by ring

/-- **Hedge local-norm regret inequality** for nonnegative losses and positive prior weights. -/
theorem hedge_regret [Nonempty ι] (hq : ∀ i, 0 < q i) (hη : 0 < η) (c : ℕ → ι → ℝ)
    (hc : ∀ t i, 0 ≤ c t i) (T : ℕ) (i : ι) :
    ∑ t ∈ range T, ∑ j, prob q η c t j * c t j - cum c T i ≤
      log ((∑ j, q j) / q i) / η + η / 2 * ∑ t ∈ range T, ∑ j, prob q η c t j * c t j ^ 2 := by
  have htel : ∀ T, log (∑ j, weight q η c T j) ≤ log (∑ j, q j)
      - η * ∑ t ∈ range T, ∑ j, prob q η c t j * c t j
      + η ^ 2 / 2 * ∑ t ∈ range T, ∑ j, prob q η c t j * c t j ^ 2 := by
    intro T
    induction T with
    | zero => simp [weight, cum]
    | succ T ih =>
      have := log_sum_weight_succ_le hq hη c hc T
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  have hlow : log (q i) - η * cum c T i ≤ log (∑ j, weight q η c T j) := by
    have : weight q η c T i ≤ ∑ j, weight q η c T j :=
      Finset.single_le_sum (fun j _ => (weight_pos hq c T j).le) (Finset.mem_univ i)
    have h := log_le_log (weight_pos hq c T i) this
    rw [weight, log_mul (hq i).ne' (exp_pos _).ne', log_exp] at h
    linarith
  have key := hlow.trans (htel T)
  have hsum : 0 < ∑ j, q j := Finset.sum_pos (fun j _ => hq j) Finset.univ_nonempty
  rw [log_div hsum.ne' (hq i).ne', div_add' _ _ _ hη.ne', le_div_iff₀ hη]
  nlinarith [key]

/-- Uniform prior: the regret against any arm is at most `log |ι| / η + (η/2) Σ_t ⟨p t, (c t)²⟩`. -/
theorem hedge_regret_uniform [Nonempty ι] (hη : 0 < η) (c : ℕ → ι → ℝ)
    (hc : ∀ t i, 0 ≤ c t i) (T : ℕ) (i : ι) :
    ∑ t ∈ range T, ∑ j, prob (fun _ => (1 : ℝ)) η c t j * c t j - cum c T i ≤
      log (Fintype.card ι) / η +
        η / 2 * ∑ t ∈ range T, ∑ j, prob (fun _ => (1 : ℝ)) η c t j * c t j ^ 2 := by
  have h := hedge_regret (q := fun _ => (1 : ℝ)) (fun _ => one_pos) hη c hc T i
  simpa using h

end Pool.P0009
