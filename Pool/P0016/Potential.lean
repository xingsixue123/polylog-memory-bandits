import Pool.Prelude
import Pool.P0009.Hedge

/-!
# The EXP3 potential on count vectors (pure real analysis)

For a count vector `c : Fin n → ℝ` and `η > 0`: `W η c = Σ_j exp(-η c_j)`, the Hedge distribution
`soft η c j = exp(-η c_j) / W η c`, and the potential for comparator `i`,
`phi η c i = c_i + log (W η c) / η` (`= (1/η) log Σ_j exp(-η (c_j - c_i))`).

* `phi_nonneg`, `phi_zero` (`= log n / η` at `c = 0`).
* `phi_step`: adding `X ≥ 0` to coordinate `a` changes the potential by at most
  `-soft_a X + [a = i] X + (η/2) soft_a X²`.
* `phi_sub_const`: shifting all counts by a constant does not change the potential.
* `phi_cap`: if all counts are `≥ 0` and one is `0`, capping them at `D ≥ 0` increases the potential by
  at most `n e^{-ηD} / η`.
-/

open Real Finset

namespace Pool.P0016

variable {n : ℕ}

/-- Total exponential weight of a count vector. -/
noncomputable def W (η : ℝ) (c : Fin n → ℝ) : ℝ := ∑ j, exp (-η * c j)

/-- Softmax (Hedge) distribution of a count vector. -/
noncomputable def soft (η : ℝ) (c : Fin n → ℝ) (j : Fin n) : ℝ := exp (-η * c j) / W η c

/-- Potential for comparator `i`: `c i + (1/η) log W`. -/
noncomputable def phi (η : ℝ) (c : Fin n → ℝ) (i : Fin n) : ℝ := c i + log (W η c) / η

theorem W_pos [NeZero n] (η : ℝ) (c : Fin n → ℝ) : 0 < W η c :=
  Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty

theorem soft_nonneg [NeZero n] (η : ℝ) (c : Fin n → ℝ) (j : Fin n) : 0 ≤ soft η c j :=
  div_nonneg (exp_pos _).le (W_pos η c).le

theorem sum_soft [NeZero n] (η : ℝ) (c : Fin n → ℝ) : ∑ j, soft η c j = 1 := by
  simp only [soft, ← Finset.sum_div]; exact div_self (W_pos η c).ne'

theorem soft_le_one [NeZero n] (η : ℝ) (c : Fin n → ℝ) (j : Fin n) : soft η c j ≤ 1 := by
  rw [← sum_soft η c]
  exact Finset.single_le_sum (fun k _ => soft_nonneg η c k) (Finset.mem_univ j)

/-- The potential is nonnegative. -/
theorem phi_nonneg [NeZero n] {η : ℝ} (hη : 0 < η) (c : Fin n → ℝ) (i : Fin n) : 0 ≤ phi η c i := by
  unfold phi
  have h : exp (-η * c i) ≤ W η c :=
    Finset.single_le_sum (f := fun j => exp (-η * c j)) (fun j _ => (exp_pos _).le) (Finset.mem_univ i)
  have h1 := log_le_log (exp_pos _) h
  rw [log_exp] at h1
  have h2 : c i + log (W η c) / η = (η * c i + log (W η c)) / η := by field_simp
  rw [h2]; apply div_nonneg _ hη.le; linarith

/-- The potential with all counts zero. -/
theorem phi_zero [NeZero n] (η : ℝ) (hη : 0 < η) (i : Fin n) :
    phi η (fun _ => 0) i = log n / η := by
  simp [phi, W]

/-- One step: adding `X ≥ 0` to the count of arm `a`. -/
theorem phi_step [NeZero n] {η : ℝ} (hη : 0 < η) (c : Fin n → ℝ) (a i : Fin n) {X : ℝ}
    (hX : 0 ≤ X) :
    phi η (fun j => c j + if j = a then X else 0) i ≤
      phi η c i - soft η c a * X + (if a = i then X else 0) + η / 2 * soft η c a * X ^ 2 := by
  set c' : Fin n → ℝ := fun j => c j + if j = a then X else 0
  have hW' : W η c' = W η c * (1 + soft η c a * (exp (-η * X) - 1)) := by
    have hsplit : ∀ j, exp (-η * c' j) = exp (-η * c j) +
        (if j = a then exp (-η * c j) * (exp (-η * X) - 1) else 0) := by
      intro j
      by_cases h : j = a
      · subst h; simp only [c', if_true]; rw [mul_add, exp_add]; ring
      · simp [c', h]
    have e1 : W η c' = W η c + exp (-η * c a) * (exp (-η * X) - 1) := by
      simp only [W, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [e1, soft, mul_add, mul_one, ← mul_assoc, mul_div_cancel₀ _ (W_pos η c).ne']
  have hq := Pool.P0009.exp_neg_le_quadratic (mul_nonneg hη.le hX)
  have hs0 := soft_nonneg η c a
  have hs1 := soft_le_one η c a
  have hfac_le : 1 + soft η c a * (exp (-η * X) - 1) ≤
      exp (-(η * soft η c a * X) + η ^ 2 / 2 * soft η c a * X ^ 2) := by
    have h1 : 1 + soft η c a * (exp (-η * X) - 1) ≤
        1 + soft η c a * (-(η * X) + (η * X) ^ 2 / 2) := by
      have : exp (-η * X) - 1 ≤ -(η * X) + (η * X) ^ 2 / 2 := by
        have := hq; rw [show -η * X = -(η * X) by ring]; linarith
      nlinarith
    have h2 := add_one_le_exp (-(η * soft η c a * X) + η ^ 2 / 2 * soft η c a * X ^ 2)
    nlinarith
  have hfac_pos : 0 < 1 + soft η c a * (exp (-η * X) - 1) := by
    have he : 0 < exp (-η * X) := exp_pos _
    rcases hs1.lt_or_eq with h | h
    · nlinarith
    · rw [h]; linarith
  have hlog : log (W η c') ≤ log (W η c) - η * soft η c a * X + η ^ 2 / 2 * soft η c a * X ^ 2 := by
    rw [hW', log_mul (W_pos η c).ne' hfac_pos.ne']
    have := log_le_log hfac_pos hfac_le
    rw [log_exp] at this
    linarith
  unfold phi
  have hci : c' i = c i + if a = i then X else 0 := by
    simp only [c']; by_cases h : i = a
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [hci]
  have : log (W η c') / η ≤ log (W η c) / η - soft η c a * X + η / 2 * soft η c a * X ^ 2 := by
    rw [div_le_iff₀ hη]
    have e : (log (W η c) / η - soft η c a * X + η / 2 * soft η c a * X ^ 2) * η =
        log (W η c) - η * soft η c a * X + η ^ 2 / 2 * soft η c a * X ^ 2 := by
      field_simp
    rw [e]; exact hlog
  linarith

/-- Subtracting a constant from all counts does not change the potential. -/
theorem phi_sub_const [NeZero n] {η : ℝ} (hη : 0 < η) (v : Fin n → ℝ) (m : ℝ) (i : Fin n) :
    phi η (fun j => v j - m) i = phi η v i := by
  have hW : W η (fun j => v j - m) = W η v * exp (η * m) := by
    simp only [W, Finset.sum_mul, ← exp_add]
    refine Finset.sum_congr rfl fun j _ => by ring_nf
  unfold phi
  rw [hW, log_mul (W_pos η v).ne' (exp_pos _).ne', log_exp]
  field_simp
  ring

/-- Capping the counts at `D ≥ 0` (when some count is `0` and all are `≥ 0`) increases the
potential by at most `n e^{-ηD} / η`. -/
theorem phi_cap [NeZero n] {η : ℝ} (hη : 0 < η) (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j)
    (j0 : Fin n) (hj0 : v j0 = 0) {D : ℝ} (hD : 0 ≤ D) (i : Fin n) :
    phi η (fun j => min (v j) D) i ≤ phi η v i + n * exp (-η * D) / η := by
  set x := (n : ℝ) * exp (-η * D)
  have hx : 0 ≤ x := by positivity
  set A := ∑ j, if v j ≤ D then exp (-η * v j) else 0 with hA
  have hpt : ∀ j, exp (-η * min (v j) D) ≤
      (if v j ≤ D then exp (-η * v j) else 0) + exp (-η * D) := by
    intro j
    by_cases h : v j ≤ D
    · simp [h, min_eq_left h, (exp_pos _).le]
    · push Not at h; simp [h.not_ge, min_eq_right h.le]
  have hWu : W η (fun j => min (v j) D) ≤ A + x := by
    calc W η (fun j => min (v j) D)
        ≤ ∑ j, ((if v j ≤ D then exp (-η * v j) else 0) + exp (-η * D)) :=
          Finset.sum_le_sum fun j _ => hpt j
      _ = A + x := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hA1 : 1 ≤ A := by
    have : (if v j0 ≤ D then exp (-η * v j0) else 0) = 1 := by simp [hj0, hD]
    calc (1 : ℝ) = (if v j0 ≤ D then exp (-η * v j0) else 0) := this.symm
      _ ≤ A := Finset.single_le_sum (f := fun j => if v j ≤ D then exp (-η * v j) else 0)
          (fun j _ => by split_ifs <;> simp [(exp_pos _).le]) (Finset.mem_univ j0)
  have hAW : A ≤ W η v :=
    Finset.sum_le_sum fun j _ => by split_ifs <;> simp [(exp_pos _).le]
  have hWv : 0 < W η v := W_pos η v
  have hWu_pos : 0 < W η (fun j => min (v j) D) := W_pos η _
  have hbound : W η (fun j => min (v j) D) ≤ W η v * (1 + x) := by
    calc W η (fun j => min (v j) D) ≤ A + x := hWu
      _ ≤ A + A * x := by nlinarith
      _ = A * (1 + x) := by ring
      _ ≤ W η v * (1 + x) := mul_le_mul_of_nonneg_right hAW (by linarith)
  have hlog : log (W η (fun j => min (v j) D)) ≤ log (W η v) + x := by
    calc log (W η (fun j => min (v j) D)) ≤ log (W η v * (1 + x)) := log_le_log hWu_pos hbound
      _ = log (W η v) + log (1 + x) := log_mul hWv.ne' (by linarith)
      _ ≤ log (W η v) + x := by
          have := log_le_sub_one_of_pos (show 0 < 1 + x by linarith); linarith
  unfold phi
  have hmin : min (v i) D ≤ v i := min_le_left _ _
  have : log (W η (fun j => min (v j) D)) / η ≤ log (W η v) / η + x / η := by
    rw [← add_div]; exact div_le_div_of_nonneg_right hlog hη.le
  simp only at this ⊢
  linarith

end Pool.P0016
