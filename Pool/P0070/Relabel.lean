import Pool.Prelude

/-!
# Adapted relabeling of round coins, and the slot-order coupling

Processes driven by independent round coins: `run step s0 T ω` is the state after `T` rounds, where round `u` uses the
coin `ω u` (law `μ`, weight `wR μ ω = ∏_u μ (ω u)`).

* `sum_relabel`: replacing each round coin by `σ u p (ω u)`, a `μ`-preserving permutation that may depend on the
  earlier coins `p`, preserves the coin law: `E[f(relabel σ T ω)] = E[f ω]`.
* `run_relabel`, `sum_run_eq`: if two processes have steps that agree up to a state-dependent `μ`-preserving
  permutation of the round coin (`stepB u s y = stepA u s (τ u s y)`), then process `B` on `ω` is process `A` on
  relabeled coins, and the final states of the two processes have the same law.
* `Compat`, `exists_perm`, `sum_run_slots` (slot-order coupling): at each round a uniformly drawn slot's occupant is
  observed; two orderings of the occupants into slots that have the same occupants (both injective) give processes with
  the same law. This is an abstract form of the "transition law does not depend on the ordering rule" step of
  P0029 §2. Both processes contain the same occupants, so both are runs WITH the copy: occupants in entry order versus
  the copy in the last slot. The further comparison of the copy-last run with the copy-free run (removing a last-slot
  copy changes no other item's observation rounds) is a separate pathwise step that is not proved here.
-/

namespace Pool.P0070

open Finset

variable {Y : Type*} [Fintype Y]

/-- Weight of `T` independent round coins, each with law `μ`. -/
noncomputable def wR (μ : Y → ℝ) {T : ℕ} (ω : Fin T → Y) : ℝ := ∏ u, μ (ω u)

/-- Adapted relabeling: the coin of round `u` is replaced by `σ u p (ω u)`, where `p` is the prefix of the
original coins before round `u`. -/
def relabel (σ : (u : ℕ) → (Fin u → Y) → Equiv.Perm Y) : (T : ℕ) → (Fin T → Y) → (Fin T → Y)
  | 0, ω => ω
  | T + 1, ω => Fin.snoc (relabel σ T (Fin.init ω)) (σ T (Fin.init ω) (ω (Fin.last T)))

lemma sum_snoc {X : Type*} [Fintype X] {T : ℕ} (f : (Fin (T + 1) → X) → ℝ) :
    ∑ ω, f ω = ∑ ω' : Fin T → X, ∑ x : X, f (Fin.snoc ω' x) := by
  have h : ∑ ω, f ω = ∑ x : X, ∑ ω' : Fin T → X, f (Fin.snoc ω' x) := by
    rw [← Fintype.sum_prod_type' (fun x (ω' : Fin T → X) => f (Fin.snoc ω' x))]
    exact (Fintype.sum_equiv (Fin.snocEquiv fun _ => X) _ _ (fun q => rfl)).symm
  rw [h, sum_comm]

lemma wR_snoc (μ : Y → ℝ) {T : ℕ} (ω : Fin T → Y) (y : Y) :
    wR μ (Fin.snoc ω y : Fin (T + 1) → Y) = wR μ ω * μ y := by
  unfold wR; rw [Fin.prod_univ_castSucc]; simp

/-- **Adapted relabeling preserves the coin law.** If every relabeling `σ u p` preserves `μ`, then for every `f`,
`Σ_ω wR μ ω · f (relabel σ T ω) = Σ_ω wR μ ω · f ω`. -/
theorem sum_relabel (μ : Y → ℝ) (σ : (u : ℕ) → (Fin u → Y) → Equiv.Perm Y)
    (hσ : ∀ u p y, μ (σ u p y) = μ y) :
    ∀ (T : ℕ) (f : (Fin T → Y) → ℝ), ∑ ω, wR μ ω * f (relabel σ T ω) = ∑ ω, wR μ ω * f ω
  | 0, f => rfl
  | T + 1, f => by
    rw [sum_snoc, sum_snoc]
    simp only [relabel, Fin.init_snoc, Fin.snoc_last, wR_snoc]
    -- inner sum: reindex the last coin by the permutation
    have hin : ∀ ω' : Fin T → Y,
        ∑ y, wR μ ω' * μ y * f (Fin.snoc (relabel σ T ω') (σ T ω' y)) =
          wR μ ω' * ∑ z, μ z * f (Fin.snoc (relabel σ T ω') z) := by
      intro ω'
      rw [mul_sum]
      have := Equiv.sum_comp (σ T ω') (fun z => wR μ ω' * (μ z * f (Fin.snoc (relabel σ T ω') z)))
      rw [← this]
      apply sum_congr rfl; intro y _
      rw [hσ]; ring
    simp_rw [hin]
    have ih := sum_relabel μ σ hσ T (fun ρ => ∑ z, μ z * f (Fin.snoc ρ z))
    rw [ih]
    apply sum_congr rfl; intro ω' _
    rw [mul_sum]; apply sum_congr rfl; intro y _; ring

section Process

variable {S : Type*}

/-- A process driven by round coins: the state after `T` rounds. -/
def run (step : ℕ → S → Y → S) (s0 : S) : (T : ℕ) → (Fin T → Y) → S
  | 0, _ => s0
  | T + 1, ω => step T (run step s0 T (Fin.init ω)) (ω (Fin.last T))

/-- **Coupling by relabeling.** Suppose the steps of two processes agree up to a state-dependent permutation of the
round coin: `stepB u s y = stepA u s (τ u s y)`. Then process `B` on coins `ω` is process `A` on the relabeled coins. -/
theorem run_relabel (stepA stepB : ℕ → S → Y → S) (s0 : S) (τ : ℕ → S → Equiv.Perm Y)
    (hτ : ∀ u s y, stepB u s y = stepA u s (τ u s y)) :
    ∀ (T : ℕ) (ω : Fin T → Y),
      run stepB s0 T ω = run stepA s0 T (relabel (fun u p => τ u (run stepB s0 u p)) T ω)
  | 0, _ => rfl
  | T + 1, ω => by
    simp only [run, relabel, Fin.init_snoc, Fin.snoc_last]
    rw [← run_relabel stepA stepB s0 τ hτ T (Fin.init ω), hτ]

/-- **Same law.** Under the hypotheses of `run_relabel`, if every `τ u s` preserves `μ`, the final states of the two
processes have the same law: `E[f(run_B)] = E[f(run_A)]` for every `f`. -/
theorem sum_run_eq (μ : Y → ℝ) (stepA stepB : ℕ → S → Y → S) (s0 : S) (τ : ℕ → S → Equiv.Perm Y)
    (hτ : ∀ u s y, stepB u s y = stepA u s (τ u s y)) (hμ : ∀ u s y, μ (τ u s y) = μ y)
    (T : ℕ) (f : S → ℝ) :
    ∑ ω, wR μ ω * f (run stepB s0 T ω) = ∑ ω, wR μ ω * f (run stepA s0 T ω) := by
  simp_rw [run_relabel stepA stepB s0 τ hτ T]
  exact sum_relabel μ (fun u p => τ u (run stepB s0 u p)) (fun u p y => hμ u _ y) T
    (fun ω => f (run stepA s0 T ω))

end Process

section Slots

variable {I : Type*} {s : ℕ}

/-- Two occupancy maps (slot ↦ occupant) are compatible when both are injective on occupants and they have the same
occupants. -/
structure Compat (oA oB : Fin s → Option I) : Prop where
  injA : ∀ y y' x, oA y = some x → oA y' = some x → y = y'
  injB : ∀ y y' x, oB y = some x → oB y' = some x → y = y'
  same : ∀ x, (∃ y, oA y = some x) ↔ (∃ y, oB y = some x)

open Classical in
/-- Compatible occupancies differ by a permutation of the slots. -/
theorem exists_perm (oA oB : Fin s → Option I) (h : Compat oA oB) :
    ∃ τ : Equiv.Perm (Fin s), ∀ y, oA (τ y) = oB y := by
  let p : Fin s → Prop := fun y => (oB y).isSome
  let q : Fin s → Prop := fun y => (oA y).isSome
  have hfwd : ∀ y : {y // p y}, ∃ y' : Fin s, oA y' = oB y.1 := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hy
    obtain ⟨y', hy'⟩ := (h.same x).2 ⟨y, hx⟩
    exact ⟨y', by rw [hy', hx]⟩
  have hbwd : ∀ y : {y // q y}, ∃ y' : Fin s, oB y' = oA y.1 := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hy
    obtain ⟨y', hy'⟩ := (h.same x).1 ⟨y, hx⟩
    exact ⟨y', by rw [hy', hx]⟩
  let f : {y // p y} → {y // q y} := fun y =>
    ⟨Classical.choose (hfwd y), by
      show (oA _).isSome
      rw [Classical.choose_spec (hfwd y)]; exact y.2⟩
  let g : {y // q y} → {y // p y} := fun y =>
    ⟨Classical.choose (hbwd y), by
      show (oB _).isSome
      rw [Classical.choose_spec (hbwd y)]; exact y.2⟩
  have hf : ∀ y, oA (f y).1 = oB y.1 := fun y => Classical.choose_spec (hfwd y)
  have hg : ∀ y, oB (g y).1 = oA y.1 := fun y => Classical.choose_spec (hbwd y)
  let e : {y // p y} ≃ {y // q y} :=
    { toFun := f, invFun := g,
      left_inv := by
        intro y
        apply Subtype.ext
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 y.2
        have h1 : oB (g (f y)).1 = some x := by rw [hg, hf, hx]
        exact h.injB _ _ x h1 hx
      right_inv := by
        intro y
        apply Subtype.ext
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 y.2
        have h1 : oA (f (g y)).1 = some x := by rw [hf, hg, hx]
        exact h.injA _ _ x h1 hx }
  refine ⟨e.extendSubtype, fun y => ?_⟩
  by_cases hy : p y
  · rw [Equiv.extendSubtype_apply_of_mem e y hy]
    exact hf ⟨y, hy⟩
  · have hq := Equiv.extendSubtype_not_mem e y hy
    simp only [p, q, Option.not_isSome_iff_eq_none] at hy hq
    rw [hq, hy]

variable {S Z : Type*} [Fintype Z]

/-- **Slot-order coupling.** A process observes, at each round, the occupant of a uniformly drawn slot (and draws
another coin `z ∼ ν`); its next state depends only on the observed occupant (or `none`) and on `z`. Two orderings of the
occupants into slots (`oA`, `oB`), compatible at every state, give processes whose final states have the same law.
Both processes have the same occupants: in the passive-copy application both are runs with the copy (entry order vs.
copy last); the comparison with the copy-free run is not part of this statement. -/
theorem sum_run_slots (ν : Z → ℝ) (next : ℕ → S → Option I → Z → S) (oA oB : S → Fin s → Option I)
    (hc : ∀ st, Compat (oA st) (oB st)) (s0 : S) (T : ℕ) (f : S → ℝ) :
    ∑ ω, wR (fun yz : Fin s × Z => ν yz.2 / s) ω *
        f (run (fun u st yz => next u st (oB st yz.1) yz.2) s0 T ω) =
      ∑ ω, wR (fun yz : Fin s × Z => ν yz.2 / s) ω *
        f (run (fun u st yz => next u st (oA st yz.1) yz.2) s0 T ω) := by
  choose τ hτ using fun st => exists_perm (oA st) (oB st) (hc st)
  refine sum_run_eq (fun yz : Fin s × Z => ν yz.2 / s) _ _ s0
    (fun _ st => Equiv.prodCongr (τ st) (Equiv.refl Z)) ?_ ?_ T f
  · intro u st yz
    simp [hτ]
  · intro u st yz
    rfl

end Slots

end Pool.P0070
