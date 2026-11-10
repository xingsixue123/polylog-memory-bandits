import Pool.P0212.Learner

/-!
# P0212's ALG with a perturbation that reads the round's draw and loss bit

P0212's update writes the normaliser perturbation `ρ k := ρr σ V`, which cannot see the round's draw `ch` and loss
bit `bit`, hence not the round's losses `c k`. A finite-state twin with polylog memory has to round the round's
log-normaliser `log(mA/mA')`, which depends on `c k`. So here the perturbation rule reads `ch` and `bit` too:
`ρG σ V ch bit`. P0212's ALG is the special case `ρG σ V _ _ = ρr σ V` (`withAlg_eq`). All of P0212's run lemmas and
the learner inequality carry over unchanged in form.
-/

namespace Pool.P0225

open Finset Pool.P0089 Pool.P0212

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ)

/-- The update on an exploitation round, with a perturbation that may read the round's draw and loss bit. -/
noncomputable def updAG (σ : AState ι) (V : Finset ι) (_d : Fin N) (ch : Option ι) (bit : Bool) : AState ι :=
  { k := σ.k + 1
    c := Function.update σ.c σ.k (ixA η L N G γ wE σ V ch bit)
    pr := Function.update σ.pr σ.k (presOf V)
    ρ := Function.update σ.ρ σ.k (ρG σ V ch bit) }

/-- P0212's update is the special case of a perturbation that ignores the draw and the loss bit. -/
theorem updA_eq (ρr : AState ι → Finset ι → ℝ) :
    updA η L N G γ wE ρr = updAG η L N G γ wE (fun σ V _ _ => ρr σ V) := rfl

end Pool.P0225

namespace Pool.P0225

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0212

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]

/-- P0194's parameters with the generalized ALG. Intended as for P0212: `wE = P.wE`, `G ≥ 1`, `N` the draw grid. -/
noncomputable def withAlgG (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ)
    (ρG : AState ι → Finset ι → Option ι → Bool → ℝ) : ParD n ι :=
  { P with
    N := N
    σA := AState ι
    sA0 := s0A
    draw := drawA η L N
    updA := updAG η L N G γ wE ρG
    draw_mem := fun σ V d x h => drawA_mem η L N σ V d x h }

/-- **P0212's ALG is a special case.** -/
theorem withAlg_eq (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) :
    withAlg P η L N G γ wE ρr = withAlgG P η L N G γ wE (fun σ V _ _ => ρr σ V) := rfl

variable (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ)
  (ℓ : LossSeq n) (ω : ℕ → RC (withAlgG P η L N G γ wE ρG)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (withAlgG P η L N G γ wE ρG).K → ι → Bool)

/-- The number of exploitation rounds before `u` (the learner time at round `u`). -/
noncomputable def kE (u : ℕ) : ℕ :=
  ((Finset.range u).filter fun v => isE (withAlgG P η L N G γ wE ρG) (ω v).1 = true).card

theorem kE_succ (u : ℕ) : kE P η L N G γ wE ρG ω (u + 1) =
    kE P η L N G γ wE ρG ω u + if isE (withAlgG P η L N G γ wE ρG) (ω u).1 = true then 1 else 0 := by
  unfold kE
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem sA_k (u : ℕ) : (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k = kE P η L N G γ wE ρG ω u := by
  induction u with
  | zero => rfl
  | succ u ih =>
    rw [kE_succ, ← ih]
    simp only [sA]
    split_ifs <;> rfl

/-- Learner data written at learner times `< k` are never changed. -/
theorem sA_frozen (u : ℕ) : ∀ u', u ≤ u' → ∀ t < (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k,
    (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u').c t = (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).c t ∧
    (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u').pr t = (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).pr t ∧
    (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u').ρ t = (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).ρ t := by
  intro u' hu
  induction u', hu using Nat.le_induction with
  | base => intro t _; exact ⟨rfl, rfl, rfl⟩
  | succ u' hu ih =>
    intro t ht
    have hk : (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k ≤
        (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u').k := by
      rw [sA_k, sA_k]
      unfold kE
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_subset_range.2 hu))
    obtain ⟨h1, h2, h3⟩ := ih t ht
    have htne : t ≠ (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u').k := by omega
    simp only [sA]
    split_ifs
    · refine ⟨?_, ?_, ?_⟩
      · show Function.update _ _ _ t = _; rw [Function.update_of_ne htne]; exact h1
      · show Function.update _ _ _ t = _; rw [Function.update_of_ne htne]; exact h2
      · show Function.update _ _ _ t = _; rw [Function.update_of_ne htne]; exact h3
    · exact ⟨h1, h2, h3⟩

/-- The learner data along the run are nonnegative. -/
theorem sA_c_nonneg :
    ∀ u t f, 0 ≤ (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).c t f := by
  intro u
  induction u with
  | zero => intro t f; exact le_rfl
  | succ u ih =>
    intro t f
    simp only [sA]
    split_ifs
    · show 0 ≤ (Function.update (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).c
        (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k _ : ℕ → Option ι → ℝ) t f
      by_cases ht : t = (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k
      · subst ht; rw [Function.update_self]
        unfold ixA; split_ifs
        · have := Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι))
            (p := pmarg η L (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
              (active (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)) f
          unfold ptA; positivity
        · exact le_rfl
      · rw [Function.update_of_ne ht]; exact ih t f
    · exact ih t f

/-- The perturbations along the run are bounded when the rule is. -/
theorem sA_ρ_bound {δ : ℝ} (hδ : 0 ≤ δ) (hρG : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) :
    ∀ u t, |(sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).ρ t| ≤ δ := by
  intro u
  induction u with
  | zero => intro t; simpa [sA, withAlgG, s0A] using hδ
  | succ u ih =>
    intro t
    simp only [sA]
    split_ifs
    · show |(Function.update (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).ρ
        (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k _ : ℕ → ℝ) t| ≤ δ
      by_cases ht : t = (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k
      · subst ht; rw [Function.update_self]; exact hρG _ _ _ _
      · rw [Function.update_of_ne ht]; exact ih t
    · exact ih t

/-- What an exploitation round writes. -/
theorem sA_written {u : ℕ} (hE : isE (withAlgG P η L N G γ wE ρG) (ω u).1 = true) :
    (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ (u + 1)).k = (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k + 1 ∧
    (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ (u + 1)).c (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k =
      ixA η L N G γ wE (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
        (active (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
        (algCh (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
        (ℓ u (armOf (withAlgG P η L N G γ wE ρG) ℓ ω u (algCh (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u))) ∧
    (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ (u + 1)).pr (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k =
      presOf (active (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u) ∧
    (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ (u + 1)).ρ (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u).k =
      ρG (sA (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u) (active (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
        (algCh (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)
        (ℓ u (armOf (withAlgG P η L N G γ wE ρG) ℓ ω u (algCh (withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u))) := by
  simp only [sA, if_pos hE]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> exact Function.update_self _ _ _

end Pool.P0225
