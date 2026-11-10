import Pool.P0225.Learner

/-!
# The self-rounding perturbation

`selfRho ε w a η c'` is the perturbation that makes the round's normaliser factor a grid value:
`(A/A')·exp(selfRho) = exp(ε·⌊log(A/A')/ε⌋₊)`, where `A`, `A'` are the awake masses before and after the
exponential update. It lies in `(−ε, 0]`. `ρStar` applies it to the learner's own weights and the round's IX data.
-/

namespace Pool.P0225

open Finset Real Pool.P0019 Pool.P0089 Pool.P0212

section abstract

variable {κ : Type} [Fintype κ]

/-- The log of the round's normaliser factor. -/
noncomputable def logFac (w : κ → ℝ) (a : κ → Bool) (η : ℝ) (c' : κ → ℝ) : ℝ :=
  log (awakeMass w a / expMass w a η c')

/-- The self-rounding perturbation. -/
noncomputable def selfRho (ε : ℝ) (w : κ → ℝ) (a : κ → Bool) (η : ℝ) (c' : κ → ℝ) : ℝ :=
  ε * (⌊logFac w a η c' / ε⌋₊ : ℝ) - logFac w a η c'

theorem expMass_le_awakeMass {w : κ → ℝ} (hw : ∀ j, 0 < w j) {a : κ → Bool} {η : ℝ} (hη : 0 ≤ η) {c' : κ → ℝ}
    (hc : ∀ j, a j = true → 0 ≤ c' j) : expMass w a η c' ≤ awakeMass w a := by
  unfold expMass awakeMass
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with h
  · have : exp (-η * c' j) ≤ 1 := by
      rw [exp_le_one_iff]; have := hc j h; nlinarith
    have := hw j
    nlinarith
  · exact le_rfl

theorem logFac_nonneg {w : κ → ℝ} (hw : ∀ j, 0 < w j) {a : κ → Bool} {η : ℝ} (hη : 0 ≤ η) {c' : κ → ℝ}
    (hc : ∀ j, a j = true → 0 ≤ c' j) : 0 ≤ logFac w a η c' := by
  unfold logFac
  by_cases h : ∃ i, a i = true
  · obtain ⟨i, hi⟩ := h
    have hA := awakeMass_pos_of_awake hw hi
    have hA' := expMass_pos_of_awake (η := η) hw hi c'
    apply log_nonneg
    rw [le_div_iff₀ hA', one_mul]
    exact expMass_le_awakeMass hw hη hc
  · push_neg at h
    have h0 : awakeMass w a = 0 := by
      unfold awakeMass; refine Finset.sum_eq_zero fun j _ => ?_; simp [h j]
    rw [h0, zero_div, log_zero]

/-- **The self-rounding perturbation lies in `(−ε, 0]`.** -/
theorem selfRho_mem {ε : ℝ} (hε : 0 < ε) {w : κ → ℝ} (hw : ∀ j, 0 < w j) {a : κ → Bool} {η : ℝ} (hη : 0 ≤ η)
    {c' : κ → ℝ} (hc : ∀ j, a j = true → 0 ≤ c' j) :
    -ε < selfRho ε w a η c' ∧ selfRho ε w a η c' ≤ 0 := by
  unfold selfRho
  set r := logFac w a η c'
  have hr : 0 ≤ r := logFac_nonneg hw hη hc
  have h1 : (⌊r / ε⌋₊ : ℝ) ≤ r / ε := Nat.floor_le (div_nonneg hr hε.le)
  have h2 : r / ε < ⌊r / ε⌋₊ + 1 := Nat.lt_floor_add_one _
  have e1 : ε * (r / ε) = r := by field_simp
  constructor
  · have : ε * (r / ε) < ε * ((⌊r / ε⌋₊ : ℝ) + 1) := mul_lt_mul_of_pos_left h2 hε
    nlinarith
  · have : ε * (⌊r / ε⌋₊ : ℝ) ≤ ε * (r / ε) := mul_le_mul_of_nonneg_left h1 hε.le
    linarith

theorem abs_selfRho_le {ε : ℝ} (hε : 0 < ε) {w : κ → ℝ} (hw : ∀ j, 0 < w j) {a : κ → Bool} {η : ℝ}
    (hη : 0 ≤ η) {c' : κ → ℝ} (hc : ∀ j, a j = true → 0 ≤ c' j) : |selfRho ε w a η c'| ≤ ε := by
  obtain ⟨h1, h2⟩ := selfRho_mem hε hw hη hc
  rw [abs_le]; constructor <;> linarith

/-- **The perturbed normaliser factor is a grid value**: `(A/A')·exp(selfRho) = exp(ε·⌊log(A/A')/ε⌋₊)` when some
specialist is awake. -/
theorem fac_mul_exp_selfRho (ε : ℝ) {w : κ → ℝ} (hw : ∀ j, 0 < w j) {a : κ → Bool} {i : κ} (hi : a i = true)
    (η : ℝ) (c' : κ → ℝ) :
    awakeMass w a / expMass w a η c' * exp (selfRho ε w a η c') =
      exp (ε * (⌊logFac w a η c' / ε⌋₊ : ℝ)) := by
  have hA := awakeMass_pos_of_awake hw hi
  have hA' := expMass_pos_of_awake (η := η) hw hi c'
  have hq : 0 < awakeMass w a / expMass w a η c' := div_pos hA hA'
  unfold selfRho
  rw [exp_sub, ← exp_log hq]
  unfold logFac
  rw [exp_log hq]
  field_simp

end abstract

variable {ι : Type} [Fintype ι] [DecidableEq ι]

variable (η : ℝ) (L N G : ℕ) (γ wE ε : ℝ)

/-- The IX data are nonnegative. -/
theorem ixA_nonneg (σ : AState ι) (V : Finset ι) (ch : Option ι) (bit : Bool) (f : Option ι) :
    0 ≤ ixA η L N G γ wE σ V ch bit f := by
  unfold ixA; split_ifs <;> positivity

/-- The awake indicator of the learner at its current time. -/
noncomputable abbrev awS (σ : AState ι) (V : Finset ι) := specAw (L := L) (prAt σ V)

/-- The learner's data with the round's IX estimates written at the current learner time. -/
noncomputable abbrev ccS (σ : AState ι) (V : Finset ι) (ch : Option ι) (bit : Bool) :=
  specLoss (L := L) (Function.update σ.c σ.k (ixA η L N G γ wE σ V ch bit))

/-- The learner's current weights (P0089's `pw` at the current learner time, uniform prior). -/
noncomputable abbrev wS (σ : AState ι) (V : Finset ι) (ch : Option ι) (bit : Bool) :=
  pw (fun _ => (1 : ℝ)) η (awS L σ V) (ccS η L N G γ wE σ V ch bit) σ.ρ σ.k

/-- **The concrete perturbation rule**: self-rounding of the round's log-normaliser on the grid `ε`. -/
noncomputable def ρStar (σ : AState ι) (V : Finset ι) (ch : Option ι) (bit : Bool) : ℝ :=
  selfRho ε (wS η L N G γ wE σ V ch bit) (awS L σ V σ.k) η (ccS η L N G γ wE σ V ch bit σ.k)

theorem ρStar_mem (hε : 0 < ε) (hη : 0 ≤ η) (σ : AState ι) (V : Finset ι) (ch : Option ι) (bit : Bool) :
    -ε < ρStar η L N G γ wE ε σ V ch bit ∧ ρStar η L N G γ wE ε σ V ch bit ≤ 0 :=
  selfRho_mem hε (pw_pos (fun _ => one_pos) _) hη
    (fun s _ => by simp only [specLoss, Function.update_self]; exact ixA_nonneg η L N G γ wE σ V ch bit _)

/-- The rule's bound, in the form the learner inequality asks for. -/
theorem abs_ρStar_le (hε : 0 < ε) (hη : 0 ≤ η) (σ : AState ι) (V : Finset ι) (ch : Option ι) (bit : Bool) :
    |ρStar η L N G γ wE ε σ V ch bit| ≤ ε := by
  obtain ⟨h1, h2⟩ := ρStar_mem η L N G γ wE ε hε hη σ V ch bit
  rw [abs_le]; constructor <;> linarith

/-- **The grid identity for `ρ⋆` itself** (the instance of `fac_mul_exp_selfRho` at `ρ⋆`'s own arguments): when some
specialist is awake at the learner's current time, the normaliser factor computed from the learner's current weights
`wS`, awake set `awS … σ.k` and the round's written data `ccS … σ.k`, times `e^{ρ⋆}`, is `exp(ε·m)` for the natural
number `m = ⌊logFac/ε⌋₊`. The identification of these arguments with the run's P0089 weights at learner time `k`
(through `sA_frozen` and `sA_written`) is by definition and is NOT stated as a lemma here. -/
theorem ρStar_grid (σ : AState ι) (V : Finset ι) (ch : Option ι) (bit : Bool) {s : Spec (Option ι) L}
    (hs : awS L σ V σ.k s = true) :
    awakeMass (wS η L N G γ wE σ V ch bit) (awS L σ V σ.k) /
        expMass (wS η L N G γ wE σ V ch bit) (awS L σ V σ.k) η (ccS η L N G γ wE σ V ch bit σ.k) *
      Real.exp (ρStar η L N G γ wE ε σ V ch bit) =
      Real.exp (ε * (⌊logFac (wS η L N G γ wE σ V ch bit) (awS L σ V σ.k) η
        (ccS η L N G γ wE σ V ch bit σ.k) / ε⌋₊ : ℝ)) :=
  fac_mul_exp_selfRho ε (pw_pos (fun _ => one_pos) _) hs η _

end Pool.P0225
