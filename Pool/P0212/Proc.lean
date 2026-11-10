import Pool.P0212.Alg

/-!
# P0194's process with the concrete ALG: the learner's state along a run
-/

namespace Pool.P0212

open Finset Pool.P0089 Pool.P0194 Pool.P0001

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]

/-- P0194's parameters with the concrete ALG (`N` draw grid, learning rate `η`, depth `L`, IX parameter `γ`,
exploitation weight `wE` used in the IX estimates, perturbation rule `ρr`). **Intended:** `wE = P.wE` (the
estimates are then unbiased for the process's exploitation rounds), `G ≥ 1`, and `N` the draw grid of P0194's law;
`withAlg` does NOT enforce these: all statements of this module are pathwise and hold for any values. -/
noncomputable def withAlg (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) : ParD n ι :=
  { P with
    N := N
    σA := AState ι
    sA0 := s0A
    draw := drawA η L N
    updA := updA η L N G γ wE ρr
    draw_mem := fun σ V d x h => drawA_mem η L N σ V d x h }

variable (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (withAlg P η L N G γ wE ρr).K → ι → Bool)

/-- The number of exploitation rounds before `u` (the learner time at round `u`). -/
noncomputable def kE (u : ℕ) : ℕ := ((Finset.range u).filter fun v => isE (withAlg P η L N G γ wE ρr) (ω v).1 = true).card

theorem kE_succ (u : ℕ) : kE P η L N G γ wE ρr ω (u + 1) =
    kE P η L N G γ wE ρr ω u + if isE (withAlg P η L N G γ wE ρr) (ω u).1 = true then 1 else 0 := by
  unfold kE
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem sA_k (u : ℕ) : (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k = kE P η L N G γ wE ρr ω u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [kE_succ, ← ih]
    simp only [sA]
    split_ifs <;> rfl

/-- Learner data written at learner times `< k` are never changed. -/
theorem sA_frozen (u : ℕ) : ∀ u', u ≤ u' → ∀ t < (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k,
    (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u').c t = (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).c t ∧
    (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u').pr t = (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).pr t ∧
    (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u').ρ t = (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).ρ t := by
  intro u' hu
  induction u', hu using Nat.le_induction with
  | base => intro t _; exact ⟨rfl, rfl, rfl⟩
  | succ u' hu ih =>
    intro t ht
    have hk : (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k ≤ (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u').k := by
      rw [sA_k, sA_k]
      unfold kE
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 hu))
    obtain ⟨h1, h2, h3⟩ := ih t ht
    have htne : t ≠ (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u').k := by omega
    simp only [sA]
    split_ifs
    · refine ⟨?_, ?_, ?_⟩
      · show Function.update _ _ _ t = _; rw [Function.update_of_ne htne]; exact h1
      · show Function.update _ _ _ t = _; rw [Function.update_of_ne htne]; exact h2
      · show Function.update _ _ _ t = _; rw [Function.update_of_ne htne]; exact h3
    · exact ⟨h1, h2, h3⟩


/-- The learner data along the run are nonnegative and the perturbations bounded. -/
theorem sA_c_nonneg (hγ : 0 < γ) (hwE : 0 < wE) : ∀ u t f, 0 ≤ (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).c t f := by
  intro u
  induction u with
  | zero => intro t f; exact le_rfl
  | succ u ih =>
    intro t f
    simp only [sA]
    split_ifs
    · show 0 ≤ (Function.update (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).c
        (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k _ : ℕ → Option ι → ℝ) t f
      by_cases ht : t = (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k
      · subst ht; rw [Function.update_self]
        unfold ixA; split_ifs
        · have := Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι))
            (p := pmarg η L (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
              (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)) f
          unfold ptA; positivity
        · exact le_rfl
      · rw [Function.update_of_ne ht]; exact ih t f
    · exact ih t f

theorem sA_ρ_bound {δ : ℝ} (hδ : 0 ≤ δ) (hρr : ∀ σ V, |ρr σ V| ≤ δ) :
    ∀ u t, |(sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).ρ t| ≤ δ := by
  intro u
  induction u with
  | zero => intro t; simpa [sA, withAlg, s0A] using hδ
  | succ u ih =>
    intro t
    simp only [sA]
    split_ifs
    · show |(Function.update (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).ρ
        (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k _ : ℕ → ℝ) t| ≤ δ
      by_cases ht : t = (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k
      · subst ht; rw [Function.update_self]; exact hρr _ _
      · rw [Function.update_of_ne ht]; exact ih t
    · exact ih t

/-- What an exploitation round writes. -/
theorem sA_written {u : ℕ} (hE : isE (withAlg P η L N G γ wE ρr) (ω u).1 = true) :
    (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ (u + 1)).k = (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k + 1 ∧
    (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ (u + 1)).c (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k =
      ixA η L N G γ wE (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
        (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
        (ℓ u (armOf (withAlg P η L N G γ wE ρr) ℓ ω u (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u))) ∧
    (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ (u + 1)).pr (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k =
      presOf (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) ∧
    (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ (u + 1)).ρ (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k =
      ρr (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) := by
  simp only [sA, if_pos hE]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> exact Function.update_self _ _ _

end Pool.P0212
