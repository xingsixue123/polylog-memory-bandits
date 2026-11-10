import Pool.P0009.Hedge

/-!
# Sleeping experts (specialists) Hedge: regret against each specialist over its awake rounds

A deterministic statement (no probability, no model), complementing P0009 (Hedge with a fixed arm
set). `ι` is a finite set of *specialists* (in applications: pairs (arm, entry time) of a pool
algorithm, all potential ones), `q i > 0` prior weights, `aw t i : Bool` says whether `i` is awake
at round `t` (an arbitrary pattern: in applications it is chosen adaptively, and the inequality is
used pathwise), `c t i ≥ 0` arbitrary losses (e.g. importance-weighted estimates).

The update (`sw`): awake specialists get the exponential update `w ↦ w · exp (-η c)`, renormalised so
that the awake mass is unchanged; asleep specialists keep their weight. The distribution played at
round `t` (`sprob`) is proportional to the weights of the awake specialists.

* `sleeping_hedge_regret`: for every specialist `i`,
  `Σ_{t<T, i awake} (⟨p t, c t⟩ - c t i) ≤ log (Q / q i) / η + (η/2) Σ_{t<T, i awake} ⟨p t, (c t)²⟩`
  with `Q = Σ_j q j` the total prior mass (including specialists that are never awake).
* `sum_sw`: the total weight stays equal to `Q`.
* `sw_eq_prior`: a specialist that has not been awake yet still has its prior weight. So an algorithm
  running this update only has to store the weights of specialists that have been awake (for
  "monocarpic" specialists, awake on one interval, only of the currently awake ones).
* `sprob_eq_prob_of_always_awake`: if everybody is always awake, `sprob` is the Hedge distribution
  `Pool.P0009.prob` (a consistency check of the definitions).
-/

open Real Finset

namespace Pool.P0019

variable {ι : Type*} [Fintype ι]

/-- Mass of the awake specialists. -/
noncomputable def awakeMass (w : ι → ℝ) (aw : ι → Bool) : ℝ := ∑ j, if aw j then w j else 0

/-- Mass of the awake specialists after the exponential update with losses `c'`. -/
noncomputable def expMass (w : ι → ℝ) (aw : ι → Bool) (η : ℝ) (c' : ι → ℝ) : ℝ :=
  ∑ j, if aw j then w j * exp (-η * c' j) else 0

/-- Specialists (sleeping experts) weights: awake specialists get the exponential update,
renormalised so that their total mass is unchanged; asleep specialists keep their weight. -/
noncomputable def sw (q : ι → ℝ) (η : ℝ) (aw : ℕ → ι → Bool) (c : ℕ → ι → ℝ) : ℕ → ι → ℝ
  | 0 => q
  | t + 1 => fun i =>
      if aw t i then
        sw q η aw c t i * exp (-η * c t i) *
          (awakeMass (sw q η aw c t) (aw t) / expMass (sw q η aw c t) (aw t) η (c t))
      else sw q η aw c t i

/-- The distribution played at round `t`: proportional to the weights of the awake specialists. -/
noncomputable def sprob (q : ι → ℝ) (η : ℝ) (aw : ℕ → ι → Bool) (c : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  if aw t i then sw q η aw c t i / awakeMass (sw q η aw c t) (aw t) else 0

variable {q : ι → ℝ} {η : ℝ} {aw : ℕ → ι → Bool} {c : ℕ → ι → ℝ}

lemma expMass_pos_of_awake {w : ι → ℝ} (hw : ∀ j, 0 < w j) {a : ι → Bool} {i : ι} (hi : a i = true)
    (c' : ι → ℝ) : 0 < expMass w a η c' := by
  unfold expMass
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => if a j then w j * exp (-η * c' j) else 0)
    (fun j _ => by split_ifs; exacts [(mul_pos (hw j) (exp_pos _)).le, le_rfl]) (Finset.mem_univ i))
  simp only [hi, if_true]; exact mul_pos (hw i) (exp_pos _)

lemma awakeMass_pos_of_awake {w : ι → ℝ} (hw : ∀ j, 0 < w j) {a : ι → Bool} {i : ι}
    (hi : a i = true) : 0 < awakeMass w a := by
  unfold awakeMass
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun j => if a j then w j else 0)
    (fun j _ => by split_ifs; exacts [(hw j).le, le_rfl]) (Finset.mem_univ i))
  simp only [hi, if_true]; exact hw i

theorem sw_pos (hq : ∀ i, 0 < q i) (t : ℕ) (i : ι) : 0 < sw q η aw c t i := by
  induction t generalizing i with
  | zero => exact hq i
  | succ t ih =>
    simp only [sw]
    split_ifs with h
    · exact mul_pos (mul_pos (ih i) (exp_pos _))
        (div_pos (awakeMass_pos_of_awake ih h) (expMass_pos_of_awake ih h _))
    · exact ih i

/-- Total weight is conserved. -/
theorem sum_sw_succ (hq : ∀ i, 0 < q i) (t : ℕ) :
    ∑ j, sw q η aw c (t + 1) j = ∑ j, sw q η aw c t j := by
  set w := sw q η aw c t
  have hw : ∀ j, 0 < w j := sw_pos hq t
  set A := awakeMass w (aw t)
  set A' := expMass w (aw t) η (c t)
  have hsplit : ∀ f : ι → ℝ, ∑ j, f j = (∑ j, if aw t j then f j else 0) + ∑ j, if aw t j then 0 else f j := by
    intro f; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  rw [hsplit (sw q η aw c (t + 1)), hsplit w]
  congr 1
  · by_cases hne : ∃ i, aw t i = true
    · obtain ⟨i, hi⟩ := hne
      have hA' : 0 < A' := expMass_pos_of_awake hw hi _
      calc (∑ j, if aw t j then sw q η aw c (t + 1) j else 0)
          = (∑ j, if aw t j then w j * exp (-η * c t j) else 0) * (A / A') := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases hj : aw t j
            · simp only [hj, if_true, sw]; rfl
            · simp [hj]
        _ = A := by
            show A' * (A / A') = A
            field_simp
        _ = _ := rfl
    · push_neg at hne
      have h0 : ∀ f : ι → ℝ, (∑ j, if aw t j then f j else 0) = 0 :=
        fun f => Finset.sum_eq_zero fun j _ => by simp [hne j]
      rw [h0, h0]
  · refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : aw t j
    · simp [hj]
    · simp only [hj, sw]; simp; rfl

theorem sum_sw (hq : ∀ i, 0 < q i) (t : ℕ) : ∑ j, sw q η aw c t j = ∑ j, q j := by
  induction t with
  | zero => rfl
  | succ t ih => rw [sum_sw_succ hq, ih]

/-- Before its first awake round, a specialist still has its prior weight (so a machine only needs
to store the weights of specialists that have already been awake). -/
theorem sw_eq_prior (t : ℕ) (i : ι) (h : ∀ s < t, aw s i = false) : sw q η aw c t i = q i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [sw, h t (Nat.lt_succ_self t)]
    exact ih fun s hs => h s (Nat.lt_succ_of_lt hs)

theorem sprob_nonneg (hq : ∀ i, 0 < q i) (t : ℕ) (i : ι) : 0 ≤ sprob q η aw c t i := by
  unfold sprob
  split_ifs with h
  · exact div_nonneg (sw_pos hq t i).le (awakeMass_pos_of_awake (sw_pos hq t) h).le
  · exact le_rfl

theorem sum_sprob (hq : ∀ i, 0 < q i) (t : ℕ) {i : ι} (hi : aw t i = true) :
    ∑ j, sprob q η aw c t j = 1 := by
  have hA := awakeMass_pos_of_awake (sw_pos (η := η) (aw := aw) (c := c) hq t) hi
  unfold sprob
  calc ∑ j, (if aw t j then sw q η aw c t j / awakeMass (sw q η aw c t) (aw t) else 0)
      = (∑ j, if aw t j then sw q η aw c t j else 0) / awakeMass (sw q η aw c t) (aw t) := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    _ = 1 := div_self hA.ne'

/-- One step: the log-weight of an awake specialist moves by at least
`η ⟨p, c⟩ - η² ⟨p, c²⟩ / 2 - η c i`. -/
theorem log_sw_succ_ge (hq : ∀ i, 0 < q i) (hη : 0 < η) (hc : ∀ t i, 0 ≤ c t i) (t : ℕ) (i : ι)
    (hi : aw t i = true) :
    log (sw q η aw c t i) + η * ∑ j, sprob q η aw c t j * c t j
      - η ^ 2 / 2 * ∑ j, sprob q η aw c t j * c t j ^ 2 - η * c t i
      ≤ log (sw q η aw c (t + 1) i) := by
  set w := sw q η aw c t
  have hw : ∀ j, 0 < w j := sw_pos hq t
  set A := awakeMass w (aw t)
  set A' := expMass w (aw t) η (c t)
  have hA : 0 < A := awakeMass_pos_of_awake hw hi
  have hA' : 0 < A' := expMass_pos_of_awake hw hi _
  set a := ∑ j, sprob q η aw c t j * c t j
  set b := ∑ j, sprob q η aw c t j * c t j ^ 2
  -- A' ≤ A (1 - η a + η² b / 2)
  have hstep : A' ≤ A * (1 - η * a + η ^ 2 / 2 * b) := by
    have hp : ∀ j, aw t j = true → A * sprob q η aw c t j = w j := by
      intro j hj
      simp only [sprob, hj, if_true]
      show A * (w j / A) = w j
      field_simp
    calc A' = ∑ j, if aw t j then w j * exp (-η * c t j) else 0 := rfl
      _ ≤ ∑ j, A * (sprob q η aw c t j * (1 - η * c t j + (η * c t j) ^ 2 / 2)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases hj : aw t j
          · simp only [hj, if_true]
            rw [← mul_assoc, hp j hj]
            have := Pool.P0009.exp_neg_le_quadratic (mul_nonneg hη.le (hc t j))
            have he : exp (-η * c t j) = exp (-(η * c t j)) := by ring_nf
            rw [he]; exact mul_le_mul_of_nonneg_left this (hw j).le
          · simp [hj, sprob]
      _ = A * (∑ j, sprob q η aw c t j - η * a + η ^ 2 / 2 * b) := by
          rw [← Finset.mul_sum]; congr 1
          simp only [a, b, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ = A * (1 - η * a + η ^ 2 / 2 * b) := by rw [sum_sprob hq t hi]
  have hfac : 0 < 1 - η * a + η ^ 2 / 2 * b := by
    by_contra hneg; rw [not_lt] at hneg
    have : A * (1 - η * a + η ^ 2 / 2 * b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA.le hneg
    linarith
  have hlogA' : log A' ≤ log A - η * a + η ^ 2 / 2 * b := by
    calc log A' ≤ log (A * (1 - η * a + η ^ 2 / 2 * b)) := log_le_log hA' hstep
      _ = log A + log (1 - η * a + η ^ 2 / 2 * b) := log_mul hA.ne' hfac.ne'
      _ ≤ log A + (-η * a + η ^ 2 / 2 * b) := by
          have := log_le_sub_one_of_pos hfac; linarith
      _ = _ := by ring
  have hsucc : sw q η aw c (t + 1) i = w i * exp (-η * c t i) * (A / A') := by
    simp only [sw, hi, if_true]; rfl
  rw [hsucc, log_mul (mul_pos (hw i) (exp_pos _)).ne' (div_pos hA hA').ne',
    log_mul (hw i).ne' (exp_pos _).ne', log_exp, log_div hA.ne' hA'.ne']
  linarith

/-- **Sleeping-experts (specialists) Hedge regret.** For every specialist `i`, over the rounds in
which `i` is awake, the regret of the specialists distribution against `i` is at most
`log (Q / q i) / η + (η/2) Σ_{awake rounds} ⟨p t, (c t)²⟩`, where `Q = Σ_j q j` is the total prior
weight of all specialists (including those that are never awake). -/
theorem sleeping_hedge_regret (hq : ∀ i, 0 < q i) (hη : 0 < η) (hc : ∀ t i, 0 ≤ c t i)
    (T : ℕ) (i : ι) :
    ∑ t ∈ range T, (if aw t i then ∑ j, sprob q η aw c t j * c t j - c t i else 0) ≤
      log ((∑ j, q j) / q i) / η +
        η / 2 * ∑ t ∈ range T, (if aw t i then ∑ j, sprob q η aw c t j * c t j ^ 2 else 0) := by
  have htel : ∀ T, log (q i) + η * ∑ t ∈ range T,
      (if aw t i then ∑ j, sprob q η aw c t j * c t j - c t i else 0)
      - η ^ 2 / 2 * ∑ t ∈ range T, (if aw t i then ∑ j, sprob q η aw c t j * c t j ^ 2 else 0)
      ≤ log (sw q η aw c T i) := by
    intro T
    induction T with
    | zero => simp [sw]
    | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      by_cases hT : aw T i
      · have := log_sw_succ_ge hq hη hc T i hT
        simp only [hT, if_true]
        nlinarith [this, ih]
      · have hsame : sw q η aw c (T + 1) i = sw q η aw c T i := by simp [sw, hT]
        simp only [hT]
        rw [hsame]
        simpa using ih
  have hup : log (sw q η aw c T i) ≤ log (∑ j, q j) := by
    apply log_le_log (sw_pos hq T i)
    rw [← sum_sw (η := η) (aw := aw) (c := c) hq T]
    exact Finset.single_le_sum (fun j _ => (sw_pos hq T j).le) (Finset.mem_univ i)
  have key := (htel T).trans hup
  have hsum : 0 < ∑ j, q j := lt_of_lt_of_le (hq i)
    (Finset.single_le_sum (fun j _ => (hq j).le) (Finset.mem_univ i))
  rw [log_div hsum.ne' (hq i).ne', div_add' _ _ _ hη.ne', le_div_iff₀ hη]
  nlinarith [key]

/-- Consistency with ordinary Hedge (P0009): if every specialist is always awake, the weights are
the Hedge weights rescaled to total mass `Q`. -/
theorem sw_eq_weight_of_always_awake [Nonempty ι] (hq : ∀ i, 0 < q i) (haw : ∀ t i, aw t i = true)
    (t : ℕ) (i : ι) :
    sw q η aw c t i =
      Pool.P0009.weight q η c t i * ((∑ j, q j) / ∑ j, Pool.P0009.weight q η c t j) := by
  induction t generalizing i with
  | zero =>
    simp only [sw, Pool.P0009.weight, Pool.P0009.cum, Finset.range_zero, Finset.sum_empty, mul_zero,
      exp_zero, mul_one]
    have : 0 < ∑ j, q j := Finset.sum_pos (fun j _ => hq j) Finset.univ_nonempty
    field_simp
  | succ t ih =>
    have hW : 0 < ∑ j, Pool.P0009.weight q η c t j := Pool.P0009.sum_weight_pos hq c t
    have hW' : 0 < ∑ j, Pool.P0009.weight q η c (t + 1) j := Pool.P0009.sum_weight_pos hq c (t + 1)
    have hQ : 0 < ∑ j, q j := Finset.sum_pos (fun j _ => hq j) Finset.univ_nonempty
    have hA : awakeMass (sw q η aw c t) (aw t) = ∑ j, q j := by
      rw [← sum_sw (η := η) (aw := aw) (c := c) hq t]
      exact Finset.sum_congr rfl fun j _ => by simp [haw t j]
    have hA' : expMass (sw q η aw c t) (aw t) η (c t) =
        (∑ j, q j) / (∑ j, Pool.P0009.weight q η c t j) *
          ∑ j, Pool.P0009.weight q η c (t + 1) j := by
      unfold expMass
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [haw t j, if_true, ih j, Pool.P0009.weight_succ]
      ring
    simp only [sw, haw t i, if_true, hA, hA', ih i, Pool.P0009.weight_succ]
    field_simp

/-- If every specialist is always awake, `sprob` is the Hedge distribution of P0009. -/
theorem sprob_eq_prob_of_always_awake [Nonempty ι] (hq : ∀ i, 0 < q i) (haw : ∀ t i, aw t i = true)
    (t : ℕ) (i : ι) : sprob q η aw c t i = Pool.P0009.prob q η c t i := by
  have hW : 0 < ∑ j, Pool.P0009.weight q η c t j := Pool.P0009.sum_weight_pos hq c t
  have hQ : 0 < ∑ j, q j := Finset.sum_pos (fun j _ => hq j) Finset.univ_nonempty
  have hA : awakeMass (sw q η aw c t) (aw t) = ∑ j, q j := by
    rw [← sum_sw (η := η) (aw := aw) (c := c) hq t]
    exact Finset.sum_congr rfl fun j _ => by simp [haw t j]
  simp only [sprob, haw t i, if_true, hA, sw_eq_weight_of_always_awake hq haw t i, Pool.P0009.prob]
  field_simp

end Pool.P0019
