import Pool.P0001.Model
import Pool.P0012.Potential

/-!
# Expectations under finite PMFs, and invariants of a machine's run

* `pexp μ f`: the expectation `∑ a, (μ a).toReal * f a` under a PMF on a finite type, with basic
  algebra (`pexp_bind`, `pexp_const`, `pexp_add`, `pexp_mono`, `pexp_congr`, …). For a machine,
  `Pool.P0012.stepExp M ℓ t s f` is definitionally `pexp (M.act t s) fun a => pexp (M.next t s a (ℓ t a)) f`,
  and `Pool.P0012.expect M ℓ t f` is `pexp (M.stateDist ℓ t) f`.
* Bridges to the pool API: `stepExp_eq_pexp`, `expect_eq_pexp` (both `rfl`), so `pexp` is the
  generic-PMF version of `Pool.P0012.expect`/`stepExp`, not a parallel notion; `pexp_bind` reuses
  `Pool.P0012.bind_toReal`.
* `stateDist_support_of_invariant`: an invariant preserved by every transition of positive
  probability holds on the support of `stateDist ℓ t` for every `t`.
-/

open scoped ENNReal Pool.P0001

namespace Pool.P0018

open Pool.P0001 Finset

/-- Expectation of `f` under a PMF on a finite type, as a finite real sum. -/
noncomputable def pexp {α : Type} [Fintype α] (μ : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (μ a).toReal * f a

section pexp

variable {α β : Type} [Fintype α] [Fintype β]

lemma pexp_bind (μ : PMF α) (κ : α → PMF β) (f : β → ℝ) :
    pexp (μ.bind κ) f = pexp μ (fun a => pexp (κ a) f) := by
  unfold pexp
  simp_rw [Pool.P0012.bind_toReal, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma pexp_toReal_sum (μ : PMF α) : ∑ a, (μ a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ a),
    ← tsum_fintype (L := .unconditional _) (fun a => μ a), PMF.tsum_coe, ENNReal.toReal_one]

lemma pexp_const (μ : PMF α) (c : ℝ) : pexp μ (fun _ => c) = c := by
  unfold pexp
  rw [← Finset.sum_mul, pexp_toReal_sum, one_mul]

lemma pexp_add (μ : PMF α) (f g : α → ℝ) :
    pexp μ (fun a => f a + g a) = pexp μ f + pexp μ g := by
  unfold pexp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma pexp_sub (μ : PMF α) (f g : α → ℝ) :
    pexp μ (fun a => f a - g a) = pexp μ f - pexp μ g := by
  unfold pexp
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma pexp_mul_left (μ : PMF α) (c : ℝ) (f : α → ℝ) :
    pexp μ (fun a => c * f a) = c * pexp μ f := by
  unfold pexp
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma pexp_mono (μ : PMF α) {f g : α → ℝ} (h : ∀ a, μ a ≠ 0 → f a ≤ g a) :
    pexp μ f ≤ pexp μ g := by
  unfold pexp
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : μ a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg

lemma pexp_congr (μ : PMF α) {f g : α → ℝ} (h : ∀ a, μ a ≠ 0 → f a = g a) :
    pexp μ f = pexp μ g :=
  le_antisymm (pexp_mono μ fun a ha => (h a ha).le) (pexp_mono μ fun a ha => (h a ha).ge)

end pexp

variable {n : ℕ}

/-- `Pool.P0012.stepExp` is a nested `pexp` (definitional). -/
lemma stepExp_eq_pexp (M : Machine n) (ℓ : LossSeq n) (t : ℕ) (s : M.State) (f : M.State → ℝ) :
    Pool.P0012.stepExp M ℓ t s f = pexp (M.act t s) fun a => pexp (M.next t s a (ℓ t a)) f := rfl

/-- `Pool.P0012.expect` is `pexp` under `stateDist` (definitional). -/
lemma expect_eq_pexp (M : Machine n) (ℓ : LossSeq n) (t : ℕ) (f : M.State → ℝ) :
    Pool.P0012.expect M ℓ t f = pexp (M.stateDist ℓ t) f := rfl

/-- An invariant `P` holds on the support of the state distribution at every round, if it holds
on the support of `init` and every transition from a state satisfying `P t` lands in `P (t + 1)`. -/
lemma stateDist_support_of_invariant (M : Machine n) (ℓ : LossSeq n) (P : ℕ → M.State → Prop)
    (h0 : ∀ s, M.init s ≠ 0 → P 0 s)
    (hstep : ∀ t s, P t s → ∀ a, M.act t s a ≠ 0 → ∀ s', M.next t s a (ℓ t a) s' ≠ 0 → P (t + 1) s') :
    ∀ t s, M.stateDist ℓ t s ≠ 0 → P t s := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    intro s' hs'
    rw [Machine.stateDist] at hs'
    rw [← PMF.mem_support_iff, PMF.mem_support_bind_iff] at hs'
    obtain ⟨s, hs, hs2⟩ := hs'
    rw [PMF.mem_support_bind_iff] at hs2
    obtain ⟨a, ha, ha2⟩ := hs2
    exact hstep t s (ih s hs) a ha s' ha2

end Pool.P0018
