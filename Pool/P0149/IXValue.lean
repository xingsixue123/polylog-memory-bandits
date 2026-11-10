import Pool.P0146.IX

/-!
# IX with a random observed value (e.g. Design Z's BASE meta-arm), and a union over items

Coins `ω : Fin t → Z` are i.i.d. with law `ν` (P0092). P0146 treats an item whose loss is predictable (fixed before
the round's coin). Here the **observed value** `Y s ω' z ∈ [0, 1]` may depend on the round's coin `z` too: for
P0136's BASE meta-arm, `z` both selects the meta-arm (`obs`) and draws the pulled arm from BASE's policy, and `Y` is
the drawn arm's loss. The comparator is any predictable `ℓ s ω' ≥ 0` with the one-sided mean condition
`Σ_z ν(z)·1[obs]·Y ≤ ℓ·P(obs)` (for the meta-arm: `ℓ` = BASE's policy loss, with equality when the draw is
independent of the selection).

* **Generic layer** (any increment `D` with one-step exponential moment `≤ 1` at scale `κ`):
  `expSum_le_of_step`, `tail_of_step`, the prefix-closed event `StepGood` and `prob_not_stepGood`
  (`≤ (T+1)²e^{−L}`), and `prob_not_stepGood_family` (union over a finite family of items: `≤ |I|·(T+1)²e^{−L}`).
* **`ixV_one_step`**: `E[exp(2γ·(Y·1[obs]/(p+γ) − ℓ))] ≤ 1` (Neu 2015, Lemma 1, with a random value).
* **`ixEstV_le_of_good`**: on the good event, on every interval, gated IX estimate `<` gated `ℓ` `+ L/(2γ)`.
* **`ixErrV_const`**: for a constant value `Y = ℓ` the increment is P0146's `ixErr` (bridge).
-/

open Finset Real

namespace Pool.P0149

open Pool.P0092 Pool.P0139 Pool.P0146

variable {Z : Type} [Fintype Z] (ν : PMF Z)

/-! ## Generic layer -/

/-- Gated exponential supermartingale for any increment whose one-step exponential moment is `≤ 1`. -/
theorem expSum_le_of_step (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) {κ : ℝ}
    (hstep : ∀ s (ω' : Fin s → Z), ∑ z, (ν z).toReal * exp (κ * D s (Fin.snoc ω' z)) ≤ 1)
    (gate : (s : ℕ) → (Fin s → Z) → Bool) (a b : ℕ) :
    ∀ t, ∑ ω : Fin t → Z, wgt ν ω * exp (κ * runSum (gD D gate a b) t ω) ≤ 1 := by
  intro t
  induction t with
  | zero => simp [wgt, runSum]
  | succ t ih =>
    rw [Pool.P0064.sum_split, Finset.sum_comm]
    calc ∑ ω' : Fin t → Z, ∑ z, wgt ν (Fin.snoc ω' z) * exp (κ * runSum (gD D gate a b) (t + 1) (Fin.snoc ω' z))
        = ∑ ω' : Fin t → Z, wgt ν ω' * exp (κ * runSum (gD D gate a b) t ω') *
            ∑ z, (ν z).toReal * exp (κ * gD D gate a b t (Fin.snoc ω' z)) := by
          refine Finset.sum_congr rfl fun ω' _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [runSum, Fin.init_snoc, wgt_snoc]
          rw [mul_add, exp_add]; ring
      _ ≤ ∑ ω' : Fin t → Z, wgt ν ω' * exp (κ * runSum (gD D gate a b) t ω') * 1 := by
          refine Finset.sum_le_sum fun ω' _ => mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (wgt_nonneg ν ω') (exp_pos _).le)
          simp only [gD_snoc]
          split_ifs
          · exact hstep t ω'
          · simp [sum_toReal_one ν]
      _ ≤ 1 := by simpa using ih

/-- **One interval** (Markov): the gated sum over `[a, b)` is `≥ L/κ` with probability `≤ e^{−L}`. -/
theorem tail_of_step (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hstep : ∀ s (ω' : Fin s → Z), ∑ z, (ν z).toReal * exp (κ * D s (Fin.snoc ω' z)) ≤ 1)
    (gate : (s : ℕ) → (Fin s → Z) → Bool) (a b T : ℕ) (L : ℝ) :
    probGe ν T (runSum (gD D gate a b) T) (L / κ) ≤ exp (-L) := by
  have hE := expSum_le_of_step ν D hstep gate a b T
  calc probGe ν T (runSum (gD D gate a b) T) (L / κ)
      ≤ ∑ ω : Fin T → Z, wgt ν ω * exp (κ * runSum (gD D gate a b) T ω - L) := by
        unfold probGe
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
        split_ifs with h
        · apply one_le_exp
          rw [div_le_iff₀ hκ] at h
          linarith
        · exact (exp_pos _).le
    _ = exp (-L) * ∑ ω : Fin T → Z, wgt ν ω * exp (κ * runSum (gD D gate a b) T ω) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [sub_eq_add_neg, exp_add]; ring
    _ ≤ exp (-L) * 1 := mul_le_mul_of_nonneg_left hE (exp_pos _).le
    _ = exp (-L) := mul_one _

/-- **The one-sided good event at time `t`**: on every interval `[a, b)` with `b ≤ t`, the gated sum is
`< thr`. -/
def StepGood (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) (thr : ℝ)
    (t : ℕ) (ω : Fin t → Z) : Prop :=
  ∀ a b, a ≤ b → b ≤ t → runSum (gD D gate a b) t ω < thr

omit [Fintype Z] in
/-- The one-sided good events are prefix-closed. -/
theorem stepGood_prefix (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) (thr : ℝ)
    (t : ℕ) (ω : Fin t → Z) (z : Z) (h : StepGood D gate thr (t + 1) (Fin.snoc ω z)) :
    StepGood D gate thr t ω := by
  intro a b hab hb
  have := h a b hab (by omega)
  rwa [runSum_gD_stable D gate hb] at this

open Classical in
/-- **Union over intervals**: the one-sided good event with threshold `L/κ` fails at the horizon with probability
`≤ (T+1)² e^{−L}`. -/
theorem prob_not_stepGood (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hstep : ∀ s (ω' : Fin s → Z), ∑ z, (ν z).toReal * exp (κ * D s (Fin.snoc ω' z)) ≤ 1)
    (gate : (s : ℕ) → (Fin s → Z) → Bool) (L : ℝ) (T : ℕ) :
    (∑ ω : Fin T → Z, wgt ν ω * if StepGood D gate (L / κ) T ω then (0 : ℝ) else 1) ≤
      ((T : ℝ) + 1) ^ 2 * exp (-L) := by
  set I : Finset (ℕ × ℕ) := ((Finset.range (T + 1)) ×ˢ (Finset.range (T + 1))).filter (fun p => p.1 ≤ p.2) with hI
  let f : ℕ × ℕ → (Fin T → Z) → ℝ := fun i ω => runSum (gD D gate i.1 i.2) T ω - L / κ
  have hstep' : (∑ ω : Fin T → Z, wgt ν ω * if StepGood D gate (L / κ) T ω then (0 : ℝ) else 1) ≤
      ∑ ω : Fin T → Z, wgt ν ω * if ∃ i ∈ I, (0 : ℝ) ≤ f i ω then 1 else 0 := by
    refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
    by_cases hg : StepGood D gate (L / κ) T ω
    · rw [if_pos hg]; split_ifs <;> norm_num
    by_cases hex : ∃ i ∈ I, (0 : ℝ) ≤ f i ω
    · rw [if_neg hg, if_pos hex]
    · exfalso; apply hex
      simp only [StepGood, not_forall, not_lt] at hg
      obtain ⟨a, b, hab, hbT, hw⟩ := hg
      refine ⟨(a, b), ?_, ?_⟩
      · simp only [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega
      · simp only [f]; linarith
  refine le_trans hstep' (le_trans (probGe_exists_le ν I f 0) ?_)
  have hone : ∀ i ∈ I, probGe ν T (f i) 0 ≤ exp (-L) := by
    intro i _
    refine le_trans (probGe_mono ν (fun ω h => ?_)) (tail_of_step ν D hκ hstep gate i.1 i.2 T L)
    simp only [f] at h; linarith
  calc ∑ i ∈ I, probGe ν T (f i) 0 ≤ ∑ _i ∈ I, exp (-L) := Finset.sum_le_sum hone
    _ = (I.card : ℝ) * exp (-L) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((T : ℝ) + 1) ^ 2 * exp (-L) := by
        refine mul_le_mul_of_nonneg_right ?_ (exp_pos _).le
        have h1 : I.card ≤ (T + 1) * (T + 1) := by
          rw [hI]; refine le_trans (Finset.card_filter_le _ _) ?_
          rw [Finset.card_product, Finset.card_range]
        have h2 : (I.card : ℝ) ≤ ((T + 1) * (T + 1) : ℕ) := by exact_mod_cast h1
        push_cast at h2; nlinarith

open Classical in
/-- **Union over a finite family of items** (each with its own increment and gate): some item's good event
fails at the horizon with probability `≤ |I|·(T+1)² e^{−L}`. -/
theorem prob_not_stepGood_family {ι : Type} (I : Finset ι) (D : ι → (s : ℕ) → (Fin (s + 1) → Z) → ℝ)
    (gate : ι → (s : ℕ) → (Fin s → Z) → Bool) {κ : ℝ} (hκ : 0 < κ)
    (hstep : ∀ i ∈ I, ∀ s (ω' : Fin s → Z), ∑ z, (ν z).toReal * exp (κ * D i s (Fin.snoc ω' z)) ≤ 1)
    (L : ℝ) (T : ℕ) :
    (∑ ω : Fin T → Z, wgt ν ω * if ∀ i ∈ I, StepGood (D i) (gate i) (L / κ) T ω then (0 : ℝ) else 1) ≤
      (I.card : ℝ) * (((T : ℝ) + 1) ^ 2 * exp (-L)) := by
  have hpt : ∀ ω : Fin T → Z, (if ∀ i ∈ I, StepGood (D i) (gate i) (L / κ) T ω then (0 : ℝ) else 1) ≤
      ∑ i ∈ I, (if StepGood (D i) (gate i) (L / κ) T ω then (0 : ℝ) else 1) := by
    intro ω
    by_cases h : ∀ i ∈ I, StepGood (D i) (gate i) (L / κ) T ω
    · rw [if_pos h]; exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num
    · rw [if_neg h]
      push_neg at h
      obtain ⟨i, hi, hni⟩ := h
      calc (1 : ℝ) = if StepGood (D i) (gate i) (L / κ) T ω then (0 : ℝ) else 1 := by rw [if_neg hni]
        _ ≤ ∑ j ∈ I, (if StepGood (D j) (gate j) (L / κ) T ω then (0 : ℝ) else 1) :=
          Finset.single_le_sum (f := fun j => if StepGood (D j) (gate j) (L / κ) T ω then (0 : ℝ) else 1)
            (fun j _ => by split_ifs <;> norm_num) hi
  calc (∑ ω : Fin T → Z, wgt ν ω * if ∀ i ∈ I, StepGood (D i) (gate i) (L / κ) T ω then (0 : ℝ) else 1)
      ≤ ∑ ω : Fin T → Z, wgt ν ω *
          ∑ i ∈ I, (if StepGood (D i) (gate i) (L / κ) T ω then (0 : ℝ) else 1) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (wgt_nonneg ν ω)
    _ = ∑ i ∈ I, ∑ ω : Fin T → Z, wgt ν ω * (if StepGood (D i) (gate i) (L / κ) T ω then (0 : ℝ) else 1) := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ _i ∈ I, ((T : ℝ) + 1) ^ 2 * exp (-L) :=
        Finset.sum_le_sum fun i hi => prob_not_stepGood ν (D i) hκ (hstep i hi) (gate i) L T
    _ = (I.card : ℝ) * (((T : ℝ) + 1) ^ 2 * exp (-L)) := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ## IX with a random observed value -/

/-- The IX estimate increment with observed value `Y`: `Y·1[obs]/(p + γ)`, `p` = the observation mass. -/
noncomputable def ixEstV (Y : (s : ℕ) → (Fin s → Z) → Z → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (γ : ℝ) :
    (s : ℕ) → (Fin (s + 1) → Z) → ℝ :=
  fun s ω => if obs s (Fin.init ω) (ω (Fin.last s)) then
    Y s (Fin.init ω) (ω (Fin.last s)) / (obsMass ν obs s (Fin.init ω) + γ) else 0

/-- The IX error against the predictable comparator `ℓ`: `Y·1[obs]/(p + γ) − ℓ`. -/
noncomputable def ixErrV (Y : (s : ℕ) → (Fin s → Z) → Z → ℝ) (ℓ : (s : ℕ) → (Fin s → Z) → ℝ)
    (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (γ : ℝ) : (s : ℕ) → (Fin (s + 1) → Z) → ℝ :=
  fun s ω => ixEstV ν Y obs γ s ω - ℓ s (Fin.init ω)

/-- **Bridge to P0146**: with the constant value `Y = ℓ`, the error is P0146's `ixErr`. -/
theorem ixErrV_const (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (γ : ℝ) :
    ixErrV ν (fun s ω' _ => ℓ s ω') ℓ obs γ = ixErr ν ℓ obs γ := by
  funext s ω
  simp only [ixErrV, ixEstV, ixErr]
  split_ifs <;> ring

/-- The one-sided mean condition holds with equality for a constant value. -/
theorem mean_const (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (s : ℕ)
    (ω' : Fin s → Z) :
    ∑ z, (ν z).toReal * (if obs s ω' z then ℓ s ω' else 0) = ℓ s ω' * obsMass ν obs s ω' := by
  simp only [obsMass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> ring

/-- **IX one-step bound with a random value** (Neu 2015, Lemma 1): if `Y ∈ [0,1]`, `ℓ ≥ 0` and
`Σ_z ν(z)·1[obs]·Y ≤ ℓ·p`, then `E[exp(2γ·(Y·1[obs]/(p+γ) − ℓ))] ≤ 1`. -/
theorem ixV_one_step (Y : (s : ℕ) → (Fin s → Z) → Z → ℝ) (ℓ : (s : ℕ) → (Fin s → Z) → ℝ)
    (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) {γ : ℝ} (hγ : 0 < γ)
    (hY0 : ∀ s ω' z, 0 ≤ Y s ω' z) (hY1 : ∀ s ω' z, Y s ω' z ≤ 1) (hℓ0 : ∀ s ω', 0 ≤ ℓ s ω')
    (hmean : ∀ s ω', ∑ z, (ν z).toReal * (if obs s ω' z then Y s ω' z else 0) ≤ ℓ s ω' * obsMass ν obs s ω')
    (s : ℕ) (ω' : Fin s → Z) :
    ∑ z, (ν z).toReal * exp (2 * γ * ixErrV ν Y ℓ obs γ s (Fin.snoc ω' z)) ≤ 1 := by
  obtain ⟨p, hp⟩ : ∃ p, p = obsMass ν obs s ω' := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = ℓ s ω' := ⟨_, rfl⟩
  have hp0 : 0 ≤ p := hp ▸ obsMass_nonneg ν obs s ω'
  have hl0 : 0 ≤ l := hl ▸ hℓ0 s ω'
  have hsplit : ∀ z, exp (2 * γ * ixErrV ν Y ℓ obs γ s (Fin.snoc ω' z)) =
      exp (-(2 * γ * l)) * (if obs s ω' z then exp (2 * γ * Y s ω' z / (p + γ)) else 1) := by
    intro z
    simp only [ixErrV, ixEstV, Fin.init_snoc, Fin.snoc_last, ← hp, ← hl]
    split_ifs
    · rw [← exp_add]; congr 1; ring
    · rw [mul_one]; congr 1; ring
  simp only [hsplit]
  have hfac : ∑ z, (ν z).toReal * (exp (-(2 * γ * l)) *
      (if obs s ω' z then exp (2 * γ * Y s ω' z / (p + γ)) else 1)) =
      exp (-(2 * γ * l)) * ∑ z, (ν z).toReal * (if obs s ω' z then exp (2 * γ * Y s ω' z / (p + γ)) else 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring
  rw [hfac]
  rcases hp0.lt_or_eq with hpos | hzero
  · -- p > 0: exp(2γY/(p+γ)) ≤ 1 + 2γY/p on observed coins
    have hbound : ∑ z, (ν z).toReal * (if obs s ω' z then exp (2 * γ * Y s ω' z / (p + γ)) else 1) ≤
        ∑ z, (ν z).toReal * (1 + (2 * γ / p) * (if obs s ω' z then Y s ω' z else 0)) := by
      refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      split_ifs
      · have := Pool.P0047.exp_ix_le (hY0 s ω' z) (hY1 s ω' z) hpos hγ
        calc exp (2 * γ * Y s ω' z / (p + γ)) ≤ 1 + 2 * γ * Y s ω' z / p := this
          _ = 1 + 2 * γ / p * Y s ω' z := by ring
      · simp
    have heq : ∑ z, (ν z).toReal * (1 + (2 * γ / p) * (if obs s ω' z then Y s ω' z else 0)) =
        1 + (2 * γ / p) * ∑ z, (ν z).toReal * (if obs s ω' z then Y s ω' z else 0) := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, sum_toReal_one ν, Finset.mul_sum]
      congr 1; exact Finset.sum_congr rfl fun z _ => by ring
    have hm : ∑ z, (ν z).toReal * (if obs s ω' z then Y s ω' z else 0) ≤ l * p := by
      have := hmean s ω'; rwa [← hp, ← hl] at this
    have hle : 1 + (2 * γ / p) * ∑ z, (ν z).toReal * (if obs s ω' z then Y s ω' z else 0) ≤ 1 + 2 * γ * l := by
      have h2 : (2 * γ / p) * ∑ z, (ν z).toReal * (if obs s ω' z then Y s ω' z else 0) ≤ (2 * γ / p) * (l * p) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      have h3 : (2 * γ / p) * (l * p) = 2 * γ * l := by field_simp
      linarith
    have hexp : exp (-(2 * γ * l)) * (1 + 2 * γ * l) ≤ 1 := by
      have h1 := add_one_le_exp (2 * γ * l)
      calc exp (-(2 * γ * l)) * (1 + 2 * γ * l) ≤ exp (-(2 * γ * l)) * exp (2 * γ * l) := by
            refine mul_le_mul_of_nonneg_left ?_ (exp_pos _).le; linarith
        _ = 1 := by rw [← exp_add]; simp
    calc exp (-(2 * γ * l)) * ∑ z, (ν z).toReal * (if obs s ω' z then exp (2 * γ * Y s ω' z / (p + γ)) else 1)
        ≤ exp (-(2 * γ * l)) * (1 + 2 * γ * l) :=
          mul_le_mul_of_nonneg_left (hbound.trans (heq ▸ hle)) (exp_pos _).le
      _ ≤ 1 := hexp
  · -- p = 0: observed coins have mass 0
    have hnull : ∀ z, obs s ω' z = true → (ν z).toReal = 0 := by
      intro z hz
      have hsum : ∑ z, (ν z).toReal * (if obs s ω' z then (1 : ℝ) else 0) = 0 := by
        have h0 : obsMass ν obs s ω' = 0 := by rw [← hp, hzero]
        unfold obsMass at h0; exact h0
      have hnn : ∀ z ∈ Finset.univ, 0 ≤ (ν z).toReal * (if obs s ω' z then (1 : ℝ) else 0) :=
        fun z _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum z (Finset.mem_univ z)
      simpa [hz] using this
    have hle : ∑ z, (ν z).toReal * (if obs s ω' z then exp (2 * γ * Y s ω' z / (p + γ)) else 1) ≤ 1 := by
      calc ∑ z, (ν z).toReal * (if obs s ω' z then exp (2 * γ * Y s ω' z / (p + γ)) else 1)
          ≤ ∑ z, (ν z).toReal := by
            refine Finset.sum_le_sum fun z _ => ?_
            by_cases hz : obs s ω' z = true
            · rw [hnull z hz]; simp
            · simp [hz]
        _ = 1 := sum_toReal_one ν
    calc exp (-(2 * γ * l)) * ∑ z, (ν z).toReal * (if obs s ω' z then exp (2 * γ * Y s ω' z / (p + γ)) else 1)
        ≤ 1 * 1 := mul_le_mul (exp_le_one_iff.mpr (by nlinarith)) hle
          (Finset.sum_nonneg fun z _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> positivity))
          zero_le_one
      _ = 1 := one_mul 1

open Classical in
/-- **IX good event with a random value** fails at the horizon with probability `≤ (T+1)² e^{−L}`. -/
theorem prob_not_ixGoodV (Y : (s : ℕ) → (Fin s → Z) → Z → ℝ) (ℓ : (s : ℕ) → (Fin s → Z) → ℝ)
    (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) {γ : ℝ} (hγ : 0 < γ)
    (hY0 : ∀ s ω' z, 0 ≤ Y s ω' z) (hY1 : ∀ s ω' z, Y s ω' z ≤ 1) (hℓ0 : ∀ s ω', 0 ≤ ℓ s ω')
    (hmean : ∀ s ω', ∑ z, (ν z).toReal * (if obs s ω' z then Y s ω' z else 0) ≤ ℓ s ω' * obsMass ν obs s ω')
    (gate : (s : ℕ) → (Fin s → Z) → Bool) (L : ℝ) (T : ℕ) :
    (∑ ω : Fin T → Z, wgt ν ω *
        if StepGood (ixErrV ν Y ℓ obs γ) gate (L / (2 * γ)) T ω then (0 : ℝ) else 1) ≤
      ((T : ℝ) + 1) ^ 2 * exp (-L) :=
  prob_not_stepGood ν (ixErrV ν Y ℓ obs γ) (by positivity)
    (ixV_one_step ν Y ℓ obs hγ hY0 hY1 hℓ0 hmean) gate L T

/-- **Certificate form.** On the good event, on every interval `[a, b)` with `b ≤ t`, the gated IX estimate
(observed values) is below the gated comparator `ℓ` plus `L/(2γ)`. -/
theorem ixEstV_le_of_good (Y : (s : ℕ) → (Fin s → Z) → Z → ℝ) (ℓ : (s : ℕ) → (Fin s → Z) → ℝ)
    (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (γ : ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) (L : ℝ)
    {t : ℕ} {ω : Fin t → Z} (hG : StepGood (ixErrV ν Y ℓ obs γ) gate (L / (2 * γ)) t ω)
    {a b : ℕ} (hab : a ≤ b) (hbt : b ≤ t) :
    runSum (gD (ixEstV ν Y obs γ) gate a b) t ω <
      runSum (gD (fun s ω => ℓ s (Fin.init ω)) gate a b) t ω + L / (2 * γ) := by
  have h := hG a b hab hbt
  have heq : gD (ixErrV ν Y ℓ obs γ) gate a b =
      fun s ω => gD (ixEstV ν Y obs γ) gate a b s ω - gD (fun s ω => ℓ s (Fin.init ω)) gate a b s ω := by
    funext s ω; unfold gD ixErrV; split_ifs <;> ring
  rw [heq, runSum_sub] at h
  linarith

end Pool.P0149
