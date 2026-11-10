import Pool.P0054.Dyadic

/-!
# Sleeping-experts Hedge with perturbed normalisation (a finite-precision model), and the
# dyadic-specialist learner's interval regret against every copy present on an interval

* `pw`, `pprob`: P0019's specialists Hedge, except that the renormalisation of the awake specialists is
  multiplied at round `t` by `exp (ρ t)`, an arbitrary common factor (`pw_zero`: `ρ = 0` gives P0019's
  `sw`). CLAIMED (argued, not proved here; no machine is defined in this file): for integer (or
  grid-valued) losses, a machine that stores each awake specialist's loss and a rounded cumulative
  log-normaliser runs this algorithm with `ρ t = ε (t+1) - ε t`, where `ε` is the rounding error, so
  `|ρ t| ≤ 2 ε_max`. The theorems below hold for every real `c ≥ 0` and every sequence `ρ`.
* `pert_sleeping_hedge_regret`: the regret against every specialist over its awake rounds is at most
  `(log (Q / q i) + 2 δ T) / η + (η/2) Σ ⟨p, c²⟩` (`sum_pw_succ_le`: the total mass grows by at most
  `exp δ` per round).
* `pert_regret_interval_le`: the analogue of P0054's `regret_interval_le` (dyadic pieces).
* `Spec`, `specAw`, `specLoss`, **`hedge_interval_hyp`**: with specialists (copy, aligned dyadic block)
  awake exactly while the copy is present in the block (`card_awake_copy_le`: at most `L + 1` awake per
  copy and round), uniform prior and per-round losses in `[0,1]`, the learner (its loss counted as `0` at
  rounds `≥ T`, with `T ≤ 2^L`, and at rounds where no specialist is awake) is within
  `(2L+1)(log |Spec| + 2δT)/η + (η/2)·len` of every copy on every interval of its presence: the
  learner hypothesis `hA` of P0086 (threaded run bound) and of P0074's certificates.
-/

open Real Finset

namespace Pool.P0089

open Pool.P0019

variable {ι : Type*} [Fintype ι]

/-- Perturbed specialists weights. -/
noncomputable def pw (q : ι → ℝ) (η : ℝ) (aw : ℕ → ι → Bool) (c : ℕ → ι → ℝ) (ρ : ℕ → ℝ) : ℕ → ι → ℝ
  | 0 => q
  | t + 1 => fun i =>
      if aw t i then
        pw q η aw c ρ t i * exp (-η * c t i) *
          (awakeMass (pw q η aw c ρ t) (aw t) / expMass (pw q η aw c ρ t) (aw t) η (c t)) * exp (ρ t)
      else pw q η aw c ρ t i

/-- The distribution played: proportional to the perturbed weights of the awake specialists. -/
noncomputable def pprob (q : ι → ℝ) (η : ℝ) (aw : ℕ → ι → Bool) (c : ℕ → ι → ℝ) (ρ : ℕ → ℝ) (t : ℕ)
    (i : ι) : ℝ :=
  if aw t i then pw q η aw c ρ t i / awakeMass (pw q η aw c ρ t) (aw t) else 0

variable {q : ι → ℝ} {η : ℝ} {aw : ℕ → ι → Bool} {c : ℕ → ι → ℝ} {ρ : ℕ → ℝ}

theorem pw_pos (hq : ∀ i, 0 < q i) (t : ℕ) (i : ι) : 0 < pw q η aw c ρ t i := by
  induction t generalizing i with
  | zero => exact hq i
  | succ t ih =>
    simp only [pw]
    split_ifs with h
    · have hA := awakeMass_pos_of_awake ih h
      have hA' := expMass_pos_of_awake (η := η) ih h (c t)
      exact mul_pos (mul_pos (mul_pos (ih i) (exp_pos _)) (div_pos hA hA')) (exp_pos _)
    · exact ih i

theorem sum_pprob (hq : ∀ i, 0 < q i) (t : ℕ) {i : ι} (hi : aw t i = true) :
    ∑ j, pprob q η aw c ρ t j = 1 := by
  set w := pw q η aw c ρ t
  have hA : 0 < awakeMass w (aw t) := awakeMass_pos_of_awake (pw_pos hq t) hi
  calc ∑ j, pprob q η aw c ρ t j = (∑ j, if aw t j then w j else 0) / awakeMass w (aw t) := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => by
          by_cases hj : aw t j <;> simp [pprob, hj, w]
    _ = 1 := div_self hA.ne'

theorem pprob_nonneg (hq : ∀ i, 0 < q i) (t : ℕ) (i : ι) : 0 ≤ pprob q η aw c ρ t i := by
  unfold pprob
  split_ifs with h
  · exact div_nonneg (pw_pos hq t i).le (awakeMass_pos_of_awake (pw_pos hq t) h).le
  · exact le_rfl

/-- Consistency: with zero perturbation the weights are P0019's specialists weights. -/
theorem pw_zero (t : ℕ) : pw q η aw c (fun _ => 0) t = sw q η aw c t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext i
    simp only [pw, sw, ih, Real.exp_zero, mul_one]

/-- The total mass grows by at most the factor `exp δ` per round. -/
theorem sum_pw_succ_le (hq : ∀ i, 0 < q i) {δ : ℝ} (hρ : ∀ t, ρ t ≤ δ) (hδ : 0 ≤ δ) (t : ℕ) :
    ∑ j, pw q η aw c ρ (t + 1) j ≤ exp δ * ∑ j, pw q η aw c ρ t j := by
  set w := pw q η aw c ρ t
  have hw : ∀ j, 0 < w j := pw_pos hq t
  by_cases hex : ∃ i, aw t i = true
  · obtain ⟨i0, hi0⟩ := hex
    set A := awakeMass w (aw t)
    set A' := expMass w (aw t) η (c t)
    have hA : 0 < A := awakeMass_pos_of_awake hw hi0
    have hA' : 0 < A' := expMass_pos_of_awake (η := η) hw hi0 _
    -- awake mass after the update is `A · exp (ρ t)`
    have hsplit : ∀ v : ι → ℝ, ∑ j, v j = (∑ j, if aw t j then v j else 0) + ∑ j, if aw t j then 0 else v j := by
      intro v; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
    have hawk : (∑ j, if aw t j then pw q η aw c ρ (t + 1) j else 0) = A * exp (ρ t) := by
      have : ∀ j, (if aw t j then pw q η aw c ρ (t + 1) j else 0) =
          (if aw t j then w j * exp (-η * c t j) else 0) * (A / A' * exp (ρ t)) := by
        intro j
        by_cases hj : aw t j
        · simp only [hj, if_true, pw]; ring
        · simp [hj]
      rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.sum_mul]
      change A' * (A / A' * exp (ρ t)) = A * exp (ρ t)
      field_simp
    have hasl : (∑ j, if aw t j then 0 else pw q η aw c ρ (t + 1) j) = ∑ j, if aw t j then 0 else w j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : aw t j
      · simp [hj]
      · have hj' : aw t j = false := by simpa using hj
        simp [pw, hj', w]
    rw [hsplit (pw q η aw c ρ (t + 1)), hawk, hasl, hsplit w]
    have h1 : A * exp (ρ t) ≤ A * exp δ := mul_le_mul_of_nonneg_left (exp_le_exp.2 (hρ t)) hA.le
    have h2 : (∑ j, if aw t j then 0 else w j) ≤ exp δ * ∑ j, if aw t j then 0 else w j := by
      have : 0 ≤ ∑ j, if aw t j then 0 else w j :=
        Finset.sum_nonneg fun j _ => by split_ifs; exacts [le_rfl, (hw j).le]
      have : 1 ≤ exp δ := one_le_exp hδ
      nlinarith
    change A * exp (ρ t) + _ ≤ exp δ * (A + _)
    nlinarith
  · push Not at hex
    have : pw q η aw c ρ (t + 1) = w := by
      funext j
      have hj' : aw t j = false := by simpa using hex j
      simp [pw, hj', w]
    rw [this]
    have : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => (hw j).le
    have : 1 ≤ exp δ := one_le_exp hδ
    nlinarith


/-- One step: the log-weight of an awake specialist moves by at least
`η ⟨p, c⟩ - η² ⟨p, c²⟩ / 2 - η c i + ρ t`. -/
theorem log_pw_succ_ge (hq : ∀ i, 0 < q i) (hη : 0 < η) (hc : ∀ t i, 0 ≤ c t i) (t : ℕ) (i : ι)
    (hi : aw t i = true) :
    log (pw q η aw c ρ t i) + η * ∑ j, pprob q η aw c ρ t j * c t j
      - η ^ 2 / 2 * ∑ j, pprob q η aw c ρ t j * c t j ^ 2 - η * c t i + ρ t
      ≤ log (pw q η aw c ρ (t + 1) i) := by
  set w := pw q η aw c ρ t
  have hw : ∀ j, 0 < w j := pw_pos hq t
  set A := awakeMass w (aw t)
  set A' := expMass w (aw t) η (c t)
  have hA : 0 < A := awakeMass_pos_of_awake hw hi
  have hA' : 0 < A' := expMass_pos_of_awake hw hi _
  set a := ∑ j, pprob q η aw c ρ t j * c t j
  set b := ∑ j, pprob q η aw c ρ t j * c t j ^ 2
  have hstep : A' ≤ A * (1 - η * a + η ^ 2 / 2 * b) := by
    have hp : ∀ j, aw t j = true → A * pprob q η aw c ρ t j = w j := by
      intro j hj
      simp only [pprob, hj, if_true]
      show A * (w j / A) = w j
      field_simp
    calc A' = ∑ j, if aw t j then w j * exp (-η * c t j) else 0 := rfl
      _ ≤ ∑ j, A * (pprob q η aw c ρ t j * (1 - η * c t j + (η * c t j) ^ 2 / 2)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases hj : aw t j
          · simp only [hj, if_true]
            rw [← mul_assoc, hp j hj]
            have := Pool.P0009.exp_neg_le_quadratic (mul_nonneg hη.le (hc t j))
            have he : exp (-η * c t j) = exp (-(η * c t j)) := by ring_nf
            rw [he]; exact mul_le_mul_of_nonneg_left this (hw j).le
          · simp [hj, pprob]
      _ = A * (∑ j, pprob q η aw c ρ t j - η * a + η ^ 2 / 2 * b) := by
          rw [← Finset.mul_sum]; congr 1
          simp only [a, b, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_; ring
      _ = A * (1 - η * a + η ^ 2 / 2 * b) := by rw [sum_pprob hq t hi]
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
  have hsucc : pw q η aw c ρ (t + 1) i = w i * exp (-η * c t i) * (A / A') * exp (ρ t) := by
    simp only [pw, hi, if_true]; rfl
  rw [hsucc, log_mul (mul_pos (mul_pos (hw i) (exp_pos _)) (div_pos hA hA')).ne' (exp_pos _).ne',
    log_mul (mul_pos (hw i) (exp_pos _)).ne' (div_pos hA hA').ne',
    log_mul (hw i).ne' (exp_pos _).ne', log_exp, log_exp, log_div hA.ne' hA'.ne']
  linarith

/-- **Perturbed sleeping-experts regret.** With `ρ t ∈ [-δ, δ]` for all `t`, for every specialist
`i`, over its awake rounds, the regret is at most `(log (Q / q i) + 2 δ T) / η + (η/2) Σ ⟨p, c²⟩`. -/
theorem pert_sleeping_hedge_regret (hq : ∀ i, 0 < q i) (hη : 0 < η) (hc : ∀ t i, 0 ≤ c t i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hρ : ∀ t, |ρ t| ≤ δ) (T : ℕ) (i : ι) :
    ∑ t ∈ range T, (if aw t i then ∑ j, pprob q η aw c ρ t j * c t j - c t i else 0) ≤
      (log ((∑ j, q j) / q i) + 2 * δ * T) / η +
        η / 2 * ∑ t ∈ range T, (if aw t i then ∑ j, pprob q η aw c ρ t j * c t j ^ 2 else 0) := by
  have hρl : ∀ t, -δ ≤ ρ t := fun t => (abs_le.1 (hρ t)).1
  have hρu : ∀ t, ρ t ≤ δ := fun t => (abs_le.1 (hρ t)).2
  have htel : ∀ T, log (q i) + η * ∑ t ∈ range T,
      (if aw t i then ∑ j, pprob q η aw c ρ t j * c t j - c t i else 0)
      - η ^ 2 / 2 * ∑ t ∈ range T, (if aw t i then ∑ j, pprob q η aw c ρ t j * c t j ^ 2 else 0)
      - δ * T ≤ log (pw q η aw c ρ T i) := by
    intro T
    induction T with
    | zero => simp [pw]
    | succ T ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      push_cast
      by_cases hT : aw T i
      · have := log_pw_succ_ge (ρ := ρ) hq hη hc T i hT
        have := hρl T
        simp only [hT, if_true]
        nlinarith [this, ih]
      · have hsame : pw q η aw c ρ (T + 1) i = pw q η aw c ρ T i := by simp [pw, hT]
        simp only [hT]
        rw [hsame]
        simp only [Bool.false_eq_true, if_false, add_zero]
        nlinarith [ih]
  -- total mass
  have hmass : ∀ T, ∑ j, pw q η aw c ρ T j ≤ exp (δ * T) * ∑ j, q j := by
    intro T
    induction T with
    | zero => simp [pw]
    | succ T ih =>
      calc ∑ j, pw q η aw c ρ (T + 1) j ≤ exp δ * ∑ j, pw q η aw c ρ T j := sum_pw_succ_le hq hρu hδ T
        _ ≤ exp δ * (exp (δ * T) * ∑ j, q j) := mul_le_mul_of_nonneg_left ih (exp_pos _).le
        _ = exp (δ * ((T + 1 : ℕ) : ℝ)) * ∑ j, q j := by
            rw [← mul_assoc, ← exp_add]; push_cast; ring_nf
  have hsum : 0 < ∑ j, q j := lt_of_lt_of_le (hq i)
    (Finset.single_le_sum (fun j _ => (hq j).le) (Finset.mem_univ i))
  have hup : log (pw q η aw c ρ T i) ≤ δ * T + log (∑ j, q j) := by
    calc log (pw q η aw c ρ T i) ≤ log (exp (δ * T) * ∑ j, q j) := by
          apply log_le_log (pw_pos hq T i)
          exact (Finset.single_le_sum (fun j _ => (pw_pos hq T j).le) (Finset.mem_univ i)).trans (hmass T)
      _ = δ * T + log (∑ j, q j) := by rw [log_mul (exp_pos _).ne' hsum.ne', log_exp]
  have key := (htel T).trans hup
  rw [log_div hsum.ne' (hq i).ne', div_add' _ _ _ hη.ne', le_div_iff₀ hη]
  nlinarith [key]

end Pool.P0089

namespace Pool.P0089

open Pool.P0019 Pool.P0054

variable {ι : Type*} [Fintype ι] {q : ι → ℝ} {η : ℝ} {aw : ℕ → ι → Bool} {c : ℕ → ι → ℝ} {ρ : ℕ → ℝ}

/-- Expected loss of the perturbed specialists Hedge at round `t`. -/
noncomputable def palgLoss (q : ι → ℝ) (η : ℝ) (aw : ℕ → ι → Bool) (c : ℕ → ι → ℝ) (ρ : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j, pprob q η aw c ρ t j * c t j

/-- Its second moment at round `t`. -/
noncomputable def palgVar (q : ι → ℝ) (η : ℝ) (aw : ℕ → ι → Bool) (c : ℕ → ι → ℝ) (ρ : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j, pprob q η aw c ρ t j * c t j ^ 2

/-- **Interval regret of the perturbed specialists Hedge through dyadic specialists** (the analogue
of P0054's `regret_interval_le`, with `Λ` replaced by `Λ + 2 δ T`). -/
theorem pert_regret_interval_le (hq : ∀ i, 0 < q i) (hη : 0 < η) (hc : ∀ t i, 0 ≤ c t i)
    {δ : ℝ} (hδ : 0 ≤ δ) (hρ : ∀ t, |ρ t| ≤ δ)
    (T L u v : ℕ) (huv : u ≤ v) (hv : v ≤ 2^L) (hvT : v ≤ T)
    (spec : ℕ × ℕ → ι) (g : ℕ → ℝ)
    (haw : ∀ p ∈ dec L u v, ∀ t < T, aw t (spec p) = true ↔ p.1 ≤ t ∧ t < p.1 + 2^p.2)
    (hg : ∀ p ∈ dec L u v, ∀ t, p.1 ≤ t → t < p.1 + 2^p.2 → c t (spec p) = g t)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ p ∈ dec L u v, log ((∑ j, q j) / q (spec p)) ≤ Λ) :
    ∑ t ∈ Ico u v, (palgLoss q η aw c ρ t - g t) ≤
      (2 * L + 1) * (Λ + 2 * δ * T) / η + η / 2 * ∑ t ∈ Ico u v, palgVar q η aw c ρ t := by
  rw [dec_sum L u v huv hv, dec_sum L u v huv hv]
  have hΛ' : 0 ≤ Λ + 2 * δ * T := by positivity
  have hpiece : ∀ p ∈ dec L u v,
      ps (fun t => palgLoss q η aw c ρ t - g t) p ≤ (Λ + 2 * δ * T) / η + η / 2 * ps (palgVar q η aw c ρ) p := by
    intro p hp
    obtain ⟨-, -, hpv⟩ := dec_dy L u v hv p hp
    have hreg := pert_sleeping_hedge_regret (aw := aw) hq hη hc hδ hρ T (spec p)
    rw [sum_range_ite_eq T p.1 (p.1 + 2^p.2) (by omega) (fun t => aw t (spec p) = true)
        (haw p hp)] at hreg
    rw [sum_range_ite_eq T p.1 (p.1 + 2^p.2) (by omega) (fun t => aw t (spec p) = true)
        (haw p hp)] at hreg
    have hsame : ps (fun t => palgLoss q η aw c ρ t - g t) p =
        ∑ t ∈ Ico p.1 (p.1 + 2^p.2), (∑ j, pprob q η aw c ρ t j * c t j - c t (spec p)) := by
      unfold ps palgLoss
      apply Finset.sum_congr rfl
      intro t ht; rw [Finset.mem_Ico] at ht; rw [hg p hp t ht.1 ht.2]
    rw [hsame]
    have : (log ((∑ j, q j) / q (spec p)) + 2 * δ * T) / η ≤ (Λ + 2 * δ * T) / η :=
      div_le_div_of_nonneg_right (by linarith [hΛ p hp]) hη.le
    unfold ps palgVar
    linarith
  have hsum : ∀ P : List (ℕ × ℕ), (∀ p ∈ P, p ∈ dec L u v) →
      (P.map (ps (fun t => palgLoss q η aw c ρ t - g t))).sum ≤
        P.length * ((Λ + 2 * δ * T) / η) + η / 2 * (P.map (ps (palgVar q η aw c ρ))).sum := by
    intro P hP
    induction P with
    | nil => simp
    | cons p P ih =>
      have h1 := hpiece p (hP p List.mem_cons_self)
      have h2 := ih (fun x hx => hP x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      nlinarith
  refine (hsum _ (fun p hp => hp)).trans ?_
  have hlen : ((dec L u v).length : ℝ) ≤ 2 * L + 1 := by exact_mod_cast dec_len L u v
  have : ((dec L u v).length : ℝ) * ((Λ + 2 * δ * T) / η) ≤ (2 * L + 1) * ((Λ + 2 * δ * T) / η) :=
    mul_le_mul_of_nonneg_right hlen (div_nonneg hΛ' hη.le)
  rw [mul_div_assoc]
  linarith

end Pool.P0089

namespace Pool.P0089

open Pool.P0019 Pool.P0054

/-- Specialists: a copy and a block `(level, start)` of `[0, 2^L)`. Only aligned (dyadic) blocks,
`2^level ∣ start`, are ever awake (`specAw`). -/
abbrev Spec (ι₀ : Type*) (L : ℕ) := ι₀ × (Fin (L + 1) × Fin (2 ^ L))

variable {ι₀ : Type*} [Fintype ι₀] {L : ℕ}

/-- Awake predicate: the block `(l, a)` is dyadic (aligned: `2^l ∣ a`), contains `t`, and the copy is
present at `t`. Unaligned starts are never awake, so at each round at most `L + 1` specialists per present
copy are awake. -/
noncomputable def specAw (present : ℕ → ι₀ → Prop) (t : ℕ) (s : Spec ι₀ L) : Bool :=
  open Classical in
  decide (2 ^ (s.2.1 : ℕ) ∣ (s.2.2 : ℕ) ∧ (s.2.2 : ℕ) ≤ t ∧ t < s.2.2 + 2 ^ (s.2.1 : ℕ) ∧ present t s.1)

omit [Fintype ι₀] in
/-- Two awake specialists of the same copy at the same level have the same start (aligned blocks of
one level are disjoint). -/
lemma specAw_start_eq (present : ℕ → ι₀ → Prop) (t : ℕ) {s₁ s₂ : Spec ι₀ L}
    (h₁ : specAw present t s₁ = true) (h₂ : specAw present t s₂ = true) (hl : s₁.2.1 = s₂.2.1) :
    s₁.2.2 = s₂.2.2 := by
  simp only [specAw, decide_eq_true_eq] at h₁ h₂
  obtain ⟨⟨k₁, hk₁⟩, a₁, b₁, -⟩ := h₁
  obtain ⟨⟨k₂, hk₂⟩, a₂, b₂, -⟩ := h₂
  rw [hl] at hk₁ b₁
  have hpos : 0 < 2 ^ (s₂.2.1 : ℕ) := Nat.two_pow_pos _
  have e1 : k₁ = t / 2 ^ (s₂.2.1 : ℕ) :=
    (Nat.div_eq_of_lt_le (by rw [mul_comm, ← hk₁]; exact a₁)
      (by rw [add_mul, one_mul, mul_comm, ← hk₁]; exact b₁)).symm
  have e2 : k₂ = t / 2 ^ (s₂.2.1 : ℕ) :=
    (Nat.div_eq_of_lt_le (by rw [mul_comm, ← hk₂]; exact a₂)
      (by rw [add_mul, one_mul, mul_comm, ← hk₂]; exact b₂)).symm
  ext; rw [hk₁, hk₂, e1, e2]

/-- At each round at most `L + 1` specialists of a given copy are awake (one per level). -/
lemma card_awake_copy_le (present : ℕ → ι₀ → Prop) (t : ℕ) (f : ι₀) [DecidableEq ι₀] :
    ((Finset.univ : Finset (Spec ι₀ L)).filter
      (fun s => s.1 = f ∧ specAw present t s = true)).card ≤ L + 1 := by
  classical
  calc _ ≤ (Finset.univ : Finset (Fin (L + 1))).card := by
        refine Finset.card_le_card_of_injOn (fun s => s.2.1) (fun _ _ => Finset.mem_univ _) ?_
        intro s₁ h₁ s₂ h₂ hl
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at h₁ h₂
        have hst := specAw_start_eq present t h₁.2 h₂.2 hl
        exact Prod.ext (h₁.1.trans h₂.1.symm) (Prod.ext hl hst)
    _ = L + 1 := by simp

/-- Specialists' losses: their copy's loss. -/
def specLoss (cu : ℕ → ι₀ → ℝ) (t : ℕ) (s : Spec ι₀ L) : ℝ := cu t s.1

/-- **The normaliser-perturbed dyadic sleeping Hedge competes with every copy on every interval of
its presence.** With the uniform prior, per-round losses in `[0,1]`, and `T ≤ 2^L`, for every copy `f`
present on `[s, s')`:
`Σ_{[s,s')} A ≤ Σ_{[s,s')} cu f + (2L+1)(log |Spec| + 2δT)/η + (η/2)(s' - s)`.
Scope: `A u` is the learner's expected loss only at rounds `u < T` at which some specialist is awake;
it is `0` at rounds `u ≥ T` and at rounds with no present copy (`palgLoss` is `0` then). Downstream sums
of `A` over a horizon must not treat these zeros as real losses. Losses of another unit (e.g. per
epoch) must be rescaled into `[0,1]` before use. -/
theorem hedge_interval_hyp (present : ℕ → ι₀ → Prop) (cu : ℕ → ι₀ → ℝ) (hc0 : ∀ t f, 0 ≤ cu t f)
    (hc1 : ∀ t f, cu t f ≤ 1) {η : ℝ} (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) (ρ : ℕ → ℝ) (hρ : ∀ t, |ρ t| ≤ δ)
    (T : ℕ) (hTL : T ≤ 2 ^ L) [Nonempty (Spec ι₀ L)] (f : ι₀) (s s' : ℕ) (hss' : s ≤ s')
    (hpres : ∀ u, s ≤ u → u < s' → present u f) :
    let A : ℕ → ℝ := fun u => if u < T then
      palgLoss (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ u else 0
    ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f +
      (2 * L + 1) * (Real.log (Fintype.card (Spec ι₀ L)) + 2 * δ * T) / η +
        η / 2 * ((s' - s : ℕ) : ℝ) := by
  intro A
  classical
  set v := min s' T with hv
  have hvs : v ≤ s' := min_le_left _ _
  have hvT : v ≤ T := min_le_right _ _
  have hcS : ∀ t (j : Spec ι₀ L), 0 ≤ specLoss (L := L) cu t j := fun t j => hc0 t j.1
  -- split `[s, s')` at `v`
  by_cases hsv : s ≤ v
  · have hsplit : ∑ u ∈ Finset.Ico s s', A u = ∑ u ∈ Finset.Ico s v, A u := by
      rw [← Finset.sum_Ico_consecutive _ hsv hvs]
      have : ∑ u ∈ Finset.Ico v s', A u = 0 := Finset.sum_eq_zero fun u hu => by
        rw [Finset.mem_Ico] at hu
        have : ¬ u < T := by
          intro h; have : u < v := by rw [hv]; exact lt_min hu.2 h
          omega
        simp [A, this]
      rw [this, add_zero]
    rw [hsplit]
    have hAv : ∑ u ∈ Finset.Ico s v, A u =
        ∑ u ∈ Finset.Ico s v, palgLoss (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ u :=
      Finset.sum_congr rfl fun u hu => by
        rw [Finset.mem_Ico] at hu
        simp [A, show u < T by omega]
    rw [hAv]
    -- the specialist for each dyadic piece
    let spec : ℕ × ℕ → Spec ι₀ L := fun p =>
      (f, (⟨min p.2 L, by omega⟩, ⟨p.1 % 2 ^ L, Nat.mod_lt _ (Nat.two_pow_pos L)⟩))
    have hvL : v ≤ 2 ^ L := hvT.trans hTL
    have hpiece : ∀ p ∈ dec L s v, p.2 ≤ L ∧ p.1 < 2 ^ L := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := dec_dy L s v hvL p hp
      have : 2 ^ p.2 ≤ 2 ^ L := by
        have := Nat.one_le_two_pow (n := p.2)
        omega
      refine ⟨(Nat.pow_le_pow_iff_right (by norm_num)).1 this, ?_⟩
      have := Nat.one_le_two_pow (n := p.2); omega
    have hreg := pert_regret_interval_le (q := fun _ => (1 : ℝ)) (aw := specAw (L := L) present)
      (c := specLoss (L := L) cu) (ρ := ρ) (fun _ => one_pos) hη hcS hδ hρ T L s v hsv hvL hvT spec
      (fun t => cu t f)
      (by
        intro p hp t ht
        obtain ⟨hpL, hpa⟩ := hpiece p hp
        obtain ⟨hdy, h1, h2⟩ := dec_dy L s v hvL p hp
        simp only [specAw, spec, decide_eq_true_eq, Nat.mod_eq_of_lt hpa, min_eq_left hpL]
        constructor
        · rintro ⟨-, a1, a2, -⟩; exact ⟨a1, a2⟩
        · rintro ⟨a1, a2⟩; exact ⟨hdy, a1, a2, hpres t (by omega) (by omega)⟩)
      (fun p _ t _ _ => rfl)
      (Real.log_nonneg (show (1 : ℝ) ≤ Fintype.card (Spec ι₀ L) by exact_mod_cast Fintype.card_pos))
      (fun p _ => by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, div_one]
        exact le_rfl)
    -- the variance term
    have hvar : ∑ t ∈ Finset.Ico s v, palgVar (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ t ≤
        ((s' - s : ℕ) : ℝ) := by
      calc ∑ t ∈ Finset.Ico s v, palgVar (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ t
          ≤ ∑ _t ∈ Finset.Ico s v, (1 : ℝ) := Finset.sum_le_sum fun t _ => by
            unfold palgVar
            by_cases hex : ∃ i, specAw (L := L) present t i = true
            · obtain ⟨i, hi⟩ := hex
              have hs1 := sum_pprob (q := fun _ => (1 : ℝ)) (η := η) (c := specLoss (L := L) cu) (ρ := ρ)
                (fun _ => one_pos) t hi
              calc ∑ j, pprob (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ t j * specLoss (L := L) cu t j ^ 2
                  ≤ ∑ j, pprob (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ t j * 1 :=
                    Finset.sum_le_sum fun j _ => by
                      apply mul_le_mul_of_nonneg_left _ (pprob_nonneg (fun _ => one_pos) t j)
                      have h0 := hc0 t j.1; have h1 := hc1 t j.1
                      simp only [specLoss]; nlinarith
                _ = 1 := by simp [hs1]
            · push Not at hex
              have : ∀ j, pprob (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ t j = 0 := by
                intro j; simp [pprob, hex j]
              simp [this]
        _ = ((v - s : ℕ) : ℝ) := by rw [Finset.sum_const, Nat.card_Ico]; simp
        _ ≤ ((s' - s : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le_sub_right hvs s
    have hcf : ∑ u ∈ Finset.Ico s v, cu u f ≤ ∑ u ∈ Finset.Ico s s', cu u f :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hvs) fun u _ _ => hc0 u f
    have hη2 : 0 ≤ η / 2 := by positivity
    rw [Finset.sum_sub_distrib] at hreg
    nlinarith
  · -- the interval lies beyond `T`
    push Not at hsv
    have : ∑ u ∈ Finset.Ico s s', A u = 0 := Finset.sum_eq_zero fun u hu => by
      rw [Finset.mem_Ico] at hu
      have : ¬ u < T := by
        intro h; have : u < v := by rw [hv]; exact lt_min hu.2 h
        omega
      simp [A, this]
    rw [this]
    have h1 : 0 ≤ ∑ u ∈ Finset.Ico s s', cu u f := Finset.sum_nonneg fun u _ => hc0 u f
    have h2 : 0 ≤ (2 * L + 1) * (Real.log (Fintype.card (Spec ι₀ L)) + 2 * δ * T) / η := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ Fintype.card (Spec ι₀ L) by exact_mod_cast Fintype.card_pos)
      positivity
    have h3 : 0 ≤ η / 2 * ((s' - s : ℕ) : ℝ) := by positivity
    linarith

end Pool.P0089
