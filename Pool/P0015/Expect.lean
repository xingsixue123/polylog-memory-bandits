import Pool.P0001.Model
/-!
# Expectations of real functions under PMFs on finite types

`E μ f = ∑ a, (μ a).toReal * f a` and its basic calculus (`E_bind`, `E_pure`, `E_map`, linearity,
monotonicity, Fubini `E_comm`), and two uniform distributions: `unif B` on `Fin B` and `unifT α`
on a nonempty finite type. For a P0001 machine, `Machine.expLoss M ℓ t` is by definition
`E (M.armDist ℓ t) (fun a => (ℓ t a).toNat)`.
-/

open scoped ENNReal

namespace Pool.P0015

open Pool.P0001

/-- Expectation of a real function under a PMF on a finite type. -/
noncomputable def E {α : Type} [Fintype α] (μ : PMF α) (f : α → ℝ) : ℝ :=
  ∑ a, (μ a).toReal * f a

section E

variable {α β : Type} [Fintype α] [Fintype β]

lemma toReal_bind_apply (μ : PMF α) (g : α → PMF β) (b : β) :
    ((μ.bind g) b).toReal = ∑ a, (μ a).toReal * (g a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro a _
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

lemma sum_toReal (μ : PMF α) : ∑ a, (μ a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top μ a)]
  rw [← tsum_fintype (L := .unconditional _) (fun a => μ a), PMF.tsum_coe, ENNReal.toReal_one]

lemma E_bind (μ : PMF α) (g : α → PMF β) (f : β → ℝ) :
    E (μ.bind g) f = E μ (fun a => E (g a) f) := by
  unfold E
  simp only [toReal_bind_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma E_pure [DecidableEq α] (a : α) (f : α → ℝ) : E (PMF.pure a) f = f a := by
  unfold E
  simp only [PMF.pure_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma E_map [DecidableEq β] (μ : PMF α) (g : α → β) (f : β → ℝ) :
    E (μ.map g) f = E μ (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, E_bind]
  simp only [Function.comp_apply, E_pure]

lemma E_const (μ : PMF α) (c : ℝ) : E μ (fun _ => c) = c := by
  unfold E
  rw [← Finset.sum_mul, sum_toReal, one_mul]

lemma E_add (μ : PMF α) (f g : α → ℝ) : E μ (fun a => f a + g a) = E μ f + E μ g := by
  unfold E
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma E_smul (μ : PMF α) (c : ℝ) (f : α → ℝ) : E μ (fun a => c * f a) = c * E μ f := by
  unfold E
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma E_sum {ι : Type} (s : Finset ι) (μ : PMF α) (f : ι → α → ℝ) :
    E μ (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, E μ (f i) := by
  unfold E
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma E_mono (μ : PMF α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : E μ f ≤ E μ g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg

lemma E_comm (μ : PMF α) (ν : PMF β) (h : α → β → ℝ) :
    E μ (fun a => E ν (fun b => h a b)) = E ν (fun b => E μ (fun a => h a b)) := by
  unfold E
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

end E

/-- The uniform distribution on `Fin B` (for `0 < B`). -/
noncomputable def unif (B : ℕ) (hB : 0 < B) : PMF (Fin B) :=
  PMF.ofFintype (fun _ => (B : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hB.ne') (ENNReal.natCast_ne_top B))

lemma E_unif (B : ℕ) (hB : 0 < B) (f : Fin B → ℝ) :
    E (unif B hB) f = (1 / (B : ℝ)) * ∑ u, f u := by
  unfold E unif
  simp only [PMF.ofFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun u _ => by ring

end Pool.P0015
