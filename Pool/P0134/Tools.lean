import Pool.P0096.State
import Pool.P0070.Relabel

set_option linter.unusedSectionVars false

/-!
# Tools: the finite-precision Hedge reads only the past, and averaging out one coordinate

* `pw_congr`, `pprob_congr`, `st_congr`, `ρM_congr`, **`pprobM_congr`**: P0089's weights and play distribution at
  round `t`, and P0096's integer state and perturbation, read the awake sets of rounds `≤ t` and the losses of
  rounds `< t` only.
* **`sum_wR_coord`**: if `H` does not read coordinate `a` and averaging `G` over coordinate `a` gives at most `H`,
  then `E[G] ≤ E[H]` under i.i.d. coordinates (P0070's `wR`).
-/

namespace Pool.P0134

open Finset

section Hedge

variable {ι : Type*} [Fintype ι]

/-- P0089's weights at round `t` read the awake sets, losses and perturbations of rounds `< t` only. -/
theorem pw_congr (q : ι → ℝ) (η : ℝ) {aw aw' : ℕ → ι → Bool} {c c' : ℕ → ι → ℝ} {ρ ρ' : ℕ → ℝ} :
    ∀ t, (∀ s < t, aw s = aw' s ∧ c s = c' s ∧ ρ s = ρ' s) →
      Pool.P0089.pw q η aw c ρ t = Pool.P0089.pw q η aw' c' ρ' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := h t (Nat.lt_succ_self t)
    have ih' := ih (fun s hs => h s (by omega))
    funext i
    simp only [Pool.P0089.pw, ih', h1, h2, h3]

/-- The play distribution at round `t` reads the awake sets of rounds `≤ t` and the losses and perturbations of
rounds `< t`. -/
theorem pprob_congr (q : ι → ℝ) (η : ℝ) {aw aw' : ℕ → ι → Bool} {c c' : ℕ → ι → ℝ} {ρ ρ' : ℕ → ℝ} (t : ℕ)
    (h : ∀ s < t, aw s = aw' s ∧ c s = c' s ∧ ρ s = ρ' s) (ht : aw t = aw' t) :
    Pool.P0089.pprob q η aw c ρ t = Pool.P0089.pprob q η aw' c' ρ' t := by
  funext i
  unfold Pool.P0089.pprob
  rw [pw_congr q η t h, ht]

/-- P0096's integer state at round `t` reads the awake sets and losses of rounds `< t` only. -/
theorem st_congr (q : ι → ℝ) (η δ : ℝ) {aw aw' : ℕ → ι → Bool} {b b' : ℕ → ι → ℕ} :
    ∀ t, (∀ s < t, aw s = aw' s ∧ b s = b' s) →
      Pool.P0096.st q η δ aw b t = Pool.P0096.st q η δ aw' b' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    obtain ⟨h1, h2⟩ := h t (Nat.lt_succ_self t)
    have ih' := ih (fun s hs => h s (by omega))
    funext i
    simp only [Pool.P0096.st, ih', h1, h2]

/-- P0096's perturbation at round `t` reads the awake sets and losses of rounds `≤ t` only. -/
theorem ρM_congr (q : ι → ℝ) (η δ : ℝ) {aw aw' : ℕ → ι → Bool} {b b' : ℕ → ι → ℕ} (t : ℕ)
    (h : ∀ s ≤ t, aw s = aw' s ∧ b s = b' s) :
    Pool.P0096.ρM q η δ aw b t = Pool.P0096.ρM q η δ aw' b' t := by
  unfold Pool.P0096.ρM
  rw [st_congr q η δ t (fun s hs => h s hs.le), (h t le_rfl).1, (h t le_rfl).2]

/-- **The finite-precision Hedge's play distribution at round `t` reads the awake sets of rounds `≤ t` and the
integer losses of rounds `< t` only.** -/
theorem pprobM_congr (q : ι → ℝ) (η δ : ℝ) {aw aw' : ℕ → ι → Bool} {b b' : ℕ → ι → ℕ} (t : ℕ)
    (h : ∀ s ≤ t, aw s = aw' s) (hb : ∀ s < t, b s = b' s) :
    Pool.P0089.pprob q η aw (fun s j => (b s j : ℝ)) (Pool.P0096.ρM q η δ aw b) t =
      Pool.P0089.pprob q η aw' (fun s j => (b' s j : ℝ)) (Pool.P0096.ρM q η δ aw' b') t := by
  refine pprob_congr q η t (fun s hs => ⟨h s hs.le, by rw [hb s hs], ?_⟩) (h t le_rfl)
  exact ρM_congr q η δ s (fun s' hs' => ⟨h s' (by omega), hb s' (by omega)⟩)

end Hedge

end Pool.P0134

namespace Pool.P0134

open Finset

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **Averaging out one coordinate.** If `H` does not read coordinate `a`, and averaging `G` over coordinate `a`
(law `μ`) gives at most `H`, then `E[G] ≤ E[H]` under i.i.d. coordinates with law `μ`. -/
theorem sum_wR_coord {T : ℕ} (μ : Y → ℝ) (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (a : Fin T)
    (G H : (Fin T → Y) → ℝ) (hH : ∀ yy z, H (Function.update yy a z) = H yy)
    (hG : ∀ yy, ∑ z, μ z * G (Function.update yy a z) ≤ H yy) :
    ∑ yy, Pool.P0070.wR μ yy * G yy ≤ ∑ yy, Pool.P0070.wR μ yy * H yy := by
  classical
  let e := Equiv.piSplitAt a (fun _ : Fin T => Y)
  let wr : ({j // j ≠ a} → Y) → ℝ := fun r => ∏ j, μ (r j)
  have hwr0 : ∀ r, 0 ≤ wr r := fun r => Finset.prod_nonneg fun j _ => hμ0 _
  have hw : ∀ z r, Pool.P0070.wR μ (e.symm (z, r)) = μ z * wr r := by
    intro z r
    unfold Pool.P0070.wR
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ a]
    congr 1
    · simp [e, Equiv.piSplitAt]
    · apply Fintype.prod_congr; intro j
      simp [e, Equiv.piSplitAt, j.2]
  have hupd : ∀ z z' r, e.symm (z, r) = Function.update (e.symm (z', r)) a z := by
    intro z z' r
    funext j
    by_cases hj : j = a
    · subst hj; simp [e, Equiv.piSplitAt]
    · simp [e, Equiv.piSplitAt, hj]
  have expand : ∀ F : (Fin T → Y) → ℝ, ∑ yy, Pool.P0070.wR μ yy * F yy =
      ∑ r, wr r * ∑ z, μ z * F (e.symm (z, r)) := by
    intro F
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hw]; ring
  rw [expand G, expand H]
  refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left ?_ (hwr0 r)
  obtain ⟨z0⟩ : Nonempty Y := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hμ1
  have hHc : ∀ z, H (e.symm (z, r)) = H (e.symm (z0, r)) := fun z => by
    rw [hupd z z0 r, hH]
  calc ∑ z, μ z * G (e.symm (z, r)) = ∑ z, μ z * G (Function.update (e.symm (z0, r)) a z) :=
        Finset.sum_congr rfl fun z _ => by rw [hupd z z0 r]
    _ ≤ H (e.symm (z0, r)) := hG _
    _ = ∑ z, μ z * H (e.symm (z, r)) := by
        simp only [hHc]; rw [← Finset.sum_mul, hμ1, one_mul]

end Pool.P0134
