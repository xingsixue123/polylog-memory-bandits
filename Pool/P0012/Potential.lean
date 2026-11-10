import Pool.P0001.Model

/-!
# Potential (drift) arguments for the machines of `Pool.P0001`

Tools to bound the expected regret of a `Pool.P0001.Machine` from a one-step inequality on a
potential function of the state, the way EXP3/Hedge-type algorithms are analysed.

* `expect M ℓ t f = Σ_s P(state at round t = s) · f s`, `stepExp M ℓ t s f` = expected value of `f`
  at the next state, from state `s` at round `t` (arm drawn from `act`, next state from `next` with
  the observed loss bit `ℓ t a`).
* `expect_succ`: `expect (t+1) f = expect t (stepExp t · f)` (the Markov property of `stateDist`).
* `drift`: `E[Φ T] ≤ E_init[Φ 0] + Σ_{t<T} E[g t]` whenever `stepExp t s (Φ (t+1)) ≤ Φ t s + g t s`.
* `expLoss_eq_expect`: `expLoss t = expect t (stateLoss t)`.
* `loss_sub_cumLoss_le_of_potential`: if `Φ T ≥ 0` and, for `t < T`,
  `stepExp t s (Φ (t+1)) ≤ Φ t s − stateLoss t s + ℓ_t(i) + g t s`, then
  `Σ_{t<T} expLoss t − cumLoss T i ≤ E_init[Φ 0] + Σ_{t<T} E[g t]`.
* `regret_le_of_potential`: the same for every arm gives `regret M ℓ T ≤ B`.
-/

open scoped ENNReal
open Finset

namespace Pool.P0012

open Pool.P0001

variable {n : ℕ} (M : Machine n) (ℓ : LossSeq n)

/-- Expectation of `f` under the law of the state at round `t`. -/
noncomputable def expect (t : ℕ) (f : M.State → ℝ) : ℝ := ∑ s, (M.stateDist ℓ t s).toReal * f s

/-- One-step expectation: from state `s` at round `t`, the expected value of `f` at the next state. -/
noncomputable def stepExp (t : ℕ) (s : M.State) (f : M.State → ℝ) : ℝ :=
  ∑ a, (M.act t s a).toReal * ∑ s', (M.next t s a (ℓ t a) s').toReal * f s'

/-- Real-valued bind formula on finite types. -/
theorem bind_toReal {α β : Type} [Fintype α] (p : PMF α) (q : α → PMF β) (b : β) :
    ((p.bind q) b).toReal = ∑ a, (p a).toReal * (q a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp [ENNReal.toReal_mul]
  · intro a _; exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

theorem expect_succ (t : ℕ) (f : M.State → ℝ) :
    expect M ℓ (t + 1) f = expect M ℓ t (fun s => stepExp M ℓ t s f) := by
  simp only [expect, stepExp, Machine.stateDist, bind_toReal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun s' _ => ?_
  ring

theorem expect_add (t : ℕ) (f g : M.State → ℝ) :
    expect M ℓ t (fun s => f s + g s) = expect M ℓ t f + expect M ℓ t g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_mono (t : ℕ) {f g : M.State → ℝ} (h : ∀ s, f s ≤ g s) :
    expect M ℓ t f ≤ expect M ℓ t g :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) ENNReal.toReal_nonneg

/-- **Drift lemma.** If a potential `Φ` satisfies `E[Φ (t+1) (next state) | s] ≤ Φ t s + g t s`
for every round and state, then `E[Φ T] ≤ E_init[Φ 0] + Σ_{t<T} E[g t]`. -/
theorem drift (Φ g : ℕ → M.State → ℝ) (h : ∀ t s, stepExp M ℓ t s (Φ (t + 1)) ≤ Φ t s + g t s)
    (T : ℕ) :
    expect M ℓ T (Φ T) ≤ expect M ℓ 0 (Φ 0) + ∑ t ∈ range T, expect M ℓ t (g t) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [expect_succ, Finset.sum_range_succ]
    have := expect_mono M ℓ T (h T)
    rw [expect_add] at this
    linarith

/-- The expected loss at round `t`, through the state law. -/
theorem expLoss_eq_expect (t : ℕ) :
    M.expLoss ℓ t = expect M ℓ t (fun s => ∑ a, (M.act t s a).toReal * ((ℓ t a).toNat : ℝ)) := by
  simp only [Machine.expLoss, Machine.armDist, expect, bind_toReal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Expected one-round loss in state `s` at round `t`. -/
noncomputable def stateLoss (t : ℕ) (s : M.State) : ℝ := ∑ a, (M.act t s a).toReal * ((ℓ t a).toNat : ℝ)

/-- **Regret against a fixed arm from a potential.** If `Φ ≥ 0` at the horizon and every round's
expected potential change pays for the gap between the machine's expected loss and the loss of arm `i`,
up to an error `g`, then the expected regret against arm `i` is at most `E_init[Φ 0] + Σ_t E[g t]`. -/
theorem loss_sub_cumLoss_le_of_potential (i : Fin n) (Φ g : ℕ → M.State → ℝ) (T : ℕ)
    (hT : ∀ s, 0 ≤ Φ T s)
    (h : ∀ t, t < T → ∀ s, stepExp M ℓ t s (Φ (t + 1)) ≤
      Φ t s - stateLoss M ℓ t s + ((ℓ t i).toNat : ℝ) + g t s) :
    ∑ t ∈ range T, M.expLoss ℓ t - cumLoss ℓ T i ≤
      expect M ℓ 0 (Φ 0) + ∑ t ∈ range T, expect M ℓ t (g t) := by
  -- shifted potential absorbing the running regret
  have key : ∀ k, k ≤ T → expect M ℓ k (Φ k) + (∑ t ∈ range k, M.expLoss ℓ t - cumLoss ℓ k i) ≤
      expect M ℓ 0 (Φ 0) + ∑ t ∈ range k, expect M ℓ t (g t) := by
    intro k
    induction k with
    | zero => intro _; simp [cumLoss]
    | succ k ih =>
      intro hk
      have ih := ih (by omega)
      rw [expect_succ]
      have hstep : expect M ℓ k (fun s => stepExp M ℓ k s (Φ (k + 1))) ≤
          expect M ℓ k (fun s => Φ k s - stateLoss M ℓ k s + ((ℓ k i).toNat : ℝ) + g k s) :=
        expect_mono M ℓ k (h k (by omega))
      have hsplit : expect M ℓ k (fun s => Φ k s - stateLoss M ℓ k s + ((ℓ k i).toNat : ℝ) + g k s)
          = expect M ℓ k (Φ k) - M.expLoss ℓ k + ((ℓ k i).toNat : ℝ) *
              ∑ s, (M.stateDist ℓ k s).toReal + expect M ℓ k (g k) := by
        rw [expLoss_eq_expect]
        simp only [expect, stateLoss]
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => by ring
      have hone : ∑ s, (M.stateDist ℓ k s).toReal = 1 := by
        rw [← ENNReal.toReal_sum (fun s _ => PMF.apply_ne_top _ s)]
        rw [← tsum_fintype (L := .unconditional _) (fun s => M.stateDist ℓ k s), PMF.tsum_coe,
          ENNReal.toReal_one]
      rw [hsplit, hone, mul_one] at hstep
      have hcum : cumLoss ℓ (k + 1) i = cumLoss ℓ k i + ((ℓ k i).toNat : ℝ) := by
        simp [cumLoss, Finset.sum_range_succ]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, hcum]
      linarith
  have hfin := key T le_rfl
  have hnn : 0 ≤ expect M ℓ T (Φ T) :=
    Finset.sum_nonneg fun s _ => mul_nonneg ENNReal.toReal_nonneg (hT s)
  linarith

/-- **Regret from potentials**: if for every arm the hypotheses of
`loss_sub_cumLoss_le_of_potential` hold with total error at most `B`, the regret is at most `B`. -/
theorem regret_le_of_potential [NeZero n] (Φ g : Fin n → ℕ → M.State → ℝ) (T : ℕ) (B : ℝ)
    (hT : ∀ i s, 0 ≤ Φ i T s)
    (h : ∀ i t, t < T → ∀ s, stepExp M ℓ t s (Φ i (t + 1)) ≤
      Φ i t s - stateLoss M ℓ t s + ((ℓ t i).toNat : ℝ) + g i t s)
    (hB : ∀ i, expect M ℓ 0 (Φ i 0) + ∑ t ∈ range T, expect M ℓ t (g i t) ≤ B) :
    regret M ℓ T ≤ B := by
  obtain ⟨i, hi⟩ := exists_bestLoss_eq ℓ T
  rw [regret, hi]
  exact (loss_sub_cumLoss_le_of_potential M ℓ i (Φ i) (g i) T (hT i) (h i)).trans (hB i)

/-- Sanity check: with `Φ = 0` and `g = 1` the lemma gives the trivial bound `regret ≤ T`, so its
hypotheses are satisfiable by every machine. -/
theorem regret_le_T_via_potential [NeZero n] (T : ℕ) : regret M ℓ T ≤ T := by
  refine regret_le_of_potential M ℓ (fun _ _ _ => 0) (fun _ _ _ => 1) T T
    (fun _ _ => le_rfl) ?_ ?_
  · intro i t _ s
    have hl : 0 ≤ stateLoss M ℓ t s := Finset.sum_nonneg fun a _ =>
      mul_nonneg ENNReal.toReal_nonneg (by positivity)
    have hi : ((ℓ t i).toNat : ℝ) ≥ 0 := by positivity
    have hle : stateLoss M ℓ t s ≤ 1 := by
      calc stateLoss M ℓ t s ≤ ∑ a, (M.act t s a).toReal := Finset.sum_le_sum fun a _ =>
            mul_le_of_le_one_right ENNReal.toReal_nonneg (by cases ℓ t a <;> simp)
        _ = 1 := by
          rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ a),
            ← tsum_fintype (L := .unconditional _) (fun a => M.act t s a), PMF.tsum_coe,
            ENNReal.toReal_one]
    simp only [stepExp, mul_zero, Finset.sum_const_zero]
    linarith
  · intro i
    have hone : ∀ t, expect M ℓ t (fun _ => (1 : ℝ)) = 1 := by
      intro t
      simp only [expect, mul_one]
      rw [← ENNReal.toReal_sum (fun s _ => PMF.apply_ne_top _ s),
        ← tsum_fintype (L := .unconditional _) (fun s => M.stateDist ℓ t s), PMF.tsum_coe,
        ENNReal.toReal_one]
    simp only [hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    simp [expect]

end Pool.P0012
