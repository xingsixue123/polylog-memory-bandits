import Pool.P0089.Hedge

/-!
# A finite-data machine runs P0089's perturbed sleeping Hedge exactly, with `|ρ t| ≤ δ/2`

Integer losses `b t i : ℕ`. Each specialist stores two integers over its awake rounds so far: its loss
`n i` and the sum `m i` of the grid increments of the normaliser. Its weight is
`wOf σ i = q i · exp (-η·n i + δ·m i)`. The grid increment at round `t` is
`kinc = round (log (awake mass / updated awake mass) / δ)`.

* `st`, `ρM`, **`pw_eq_wOf`**: the integer state's weights are exactly P0089's `pw` with perturbation
  `ρM t = δ·kinc t − log (ratio t)`. **`abs_ρM_le`**: `|ρM t| ≤ δ/2` (a rounding error). `pprob_eq`.
* Ranges: `ratio_bounds` (`1 ≤ ratio ≤ exp (η·bmax)`), `kinc_bounds` (`0 ≤ kinc ≤ η·bmax/δ + 1/2`),
  `st_bounds` (`n i ≤ t·bmax`, `0 ≤ m i ≤ t·(η·bmax/δ + 1/2)`).
* Only the awake specialists' data is needed: `NoRewake` (awake sets are intervals; `NoRewake.and`,
  `NoRewake.window`, `specAw_noRewake` for P0089's dyadic specialists when presence has no re-entry),
  `st_of_never`, `stR` (data of the awake specialists), `wR`, `stepR`, **`stR_succ`**: the stored data
  evolves by the explicit step `stepR`. `pprob_eq_stR`: the play distribution is a function of it.
* `machine_regret`: P0089's regret bound applies with `δ/2`.
-/

open Real Finset

namespace Pool.P0096

open Pool.P0019 Pool.P0089

variable {ι : Type*} [Fintype ι]

/-- Weights read off integer data: `q i · exp (-η·n i + δ·m i)`. -/
noncomputable def wOf (q : ι → ℝ) (η δ : ℝ) (σ : ι → ℕ × ℤ) (i : ι) : ℝ :=
  q i * exp (-η * (σ i).1 + δ * (σ i).2)

/-- The grid increment of the normaliser: `round (log (awake mass / updated awake mass) / δ)`. -/
noncomputable def kinc (η δ : ℝ) (w : ι → ℝ) (a : ι → Bool) (c : ι → ℝ) : ℤ :=
  round (Real.log (awakeMass w a / expMass w a η c) / δ)

/-- The integer state: for each specialist, its integer loss and its summed grid increments over
its awake rounds so far. -/
noncomputable def st (q : ι → ℝ) (η δ : ℝ) (aw : ℕ → ι → Bool) (b : ℕ → ι → ℕ) : ℕ → ι → ℕ × ℤ
  | 0 => fun _ => (0, 0)
  | t + 1 => fun i =>
      if aw t i then
        ((st q η δ aw b t i).1 + b t i,
          (st q η δ aw b t i).2 +
            kinc η δ (wOf q η δ (st q η δ aw b t)) (aw t) (fun j => (b t j : ℝ)))
      else st q η δ aw b t i

/-- The perturbation that the integer state realises. -/
noncomputable def ρM (q : ι → ℝ) (η δ : ℝ) (aw : ℕ → ι → Bool) (b : ℕ → ι → ℕ) (t : ℕ) : ℝ :=
  δ * kinc η δ (wOf q η δ (st q η δ aw b t)) (aw t) (fun j => (b t j : ℝ)) -
    Real.log (awakeMass (wOf q η δ (st q η δ aw b t)) (aw t) /
      expMass (wOf q η δ (st q η δ aw b t)) (aw t) η (fun j => (b t j : ℝ)))

variable {q : ι → ℝ} {η δ : ℝ} {aw : ℕ → ι → Bool} {b : ℕ → ι → ℕ} {b0 : ι → ℕ}

omit [Fintype ι] in
theorem wOf_pos (hq : ∀ i, 0 < q i) (σ : ι → ℕ × ℤ) (i : ι) : 0 < wOf q η δ σ i :=
  mul_pos (hq i) (exp_pos _)

/-- **The integer state runs P0089's perturbed Hedge exactly**, with perturbation `ρM`. -/
theorem pw_eq_wOf (hq : ∀ i, 0 < q i) (t : ℕ) :
    pw q η aw (fun s j => (b s j : ℝ)) (ρM q η δ aw b) t = wOf q η δ (st q η δ aw b t) := by
  induction t with
  | zero => funext i; simp [pw, st, wOf]
  | succ t ih =>
    funext i
    simp only [pw, ih]
    by_cases h : aw t i
    · simp only [h, if_true, st, wOf]
      set w := wOf q η δ (st q η δ aw b t)
      have hA : 0 < awakeMass w (aw t) := awakeMass_pos_of_awake (wOf_pos hq _) h
      have hA' : 0 < expMass w (aw t) η (fun j => (b t j : ℝ)) :=
        expMass_pos_of_awake (η := η) (wOf_pos hq _) h _
      have hr : 0 < awakeMass w (aw t) / expMass w (aw t) η (fun j => (b t j : ℝ)) := div_pos hA hA'
      unfold ρM
      rw [exp_sub, exp_log hr]
      simp only [w]
      have gen : ∀ Q X Y Z r : ℝ, r ≠ 0 → Q * exp X * exp Y * r * (exp Z / r) = Q * exp (X + Y + Z) :=
        fun Q X Y Z r hr0 => by rw [exp_add, exp_add]; field_simp
      rw [gen _ _ _ _ _ hr.ne']
      congr 2
      push_cast
      ring
    · simp [h, st, wOf]

/-- The realised perturbation is a rounding error: `|ρM t| ≤ δ/2`. -/
theorem abs_ρM_le (hδ : 0 < δ) (t : ℕ) : |ρM q η δ aw b t| ≤ δ / 2 := by
  unfold ρM kinc
  set x := Real.log (awakeMass (wOf q η δ (st q η δ aw b t)) (aw t) /
      expMass (wOf q η δ (st q η δ aw b t)) (aw t) η (fun j => (b t j : ℝ)))
  have h := abs_sub_round (x / δ)
  have : δ * (round (x / δ) : ℝ) - x = -(δ * (x / δ - round (x / δ))) := by
    field_simp; ring
  rw [this, abs_neg, abs_mul, abs_of_pos hδ]
  calc δ * |x / δ - round (x / δ)| ≤ δ * (1 / 2) := mul_le_mul_of_nonneg_left h hδ.le
    _ = δ / 2 := by ring

/-- The play distribution is a function of the integer data of the awake specialists. -/
theorem pprob_eq (hq : ∀ i, 0 < q i) (t : ℕ) (i : ι) :
    pprob q η aw (fun s j => (b s j : ℝ)) (ρM q η δ aw b) t i =
      if aw t i then wOf q η δ (st q η δ aw b t) i / awakeMass (wOf q η δ (st q η δ aw b t)) (aw t)
      else 0 := by
  unfold pprob
  rw [pw_eq_wOf hq]

/-! ### Ranges of the integer data -/

/-- The awake-mass ratio lies in `[1, exp (η·bmax)]` when someone is awake. -/
theorem ratio_bounds (hη : 0 ≤ η) {bmax : ℕ} (hb : ∀ j, b0 j ≤ bmax) (w : ι → ℝ) (hw : ∀ j, 0 < w j)
    (a : ι → Bool) {i : ι} (hi : a i = true) :
    1 ≤ awakeMass w a / expMass w a η (fun j => (b0 j : ℝ)) ∧
      awakeMass w a / expMass w a η (fun j => (b0 j : ℝ)) ≤ exp (η * bmax) := by
  have hA : 0 < awakeMass w a := awakeMass_pos_of_awake hw hi
  have hA' : 0 < expMass w a η (fun j => (b0 j : ℝ)) := expMass_pos_of_awake (η := η) hw hi _
  have hle : expMass w a η (fun j => (b0 j : ℝ)) ≤ awakeMass w a := by
    unfold expMass awakeMass
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · have : exp (-η * (b0 j : ℝ)) ≤ 1 := exp_le_one_iff.2 (by
        have : (0 : ℝ) ≤ b0 j := Nat.cast_nonneg _
        nlinarith)
      have := (hw j).le
      nlinarith
    · exact le_rfl
  have hge : exp (-(η * bmax)) * awakeMass w a ≤ expMass w a η (fun j => (b0 j : ℝ)) := by
    unfold expMass awakeMass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · have : exp (-(η * bmax)) ≤ exp (-η * (b0 j : ℝ)) := exp_le_exp.2 (by
        have : (b0 j : ℝ) ≤ bmax := by exact_mod_cast hb j
        nlinarith)
      have := (hw j).le
      nlinarith
    · simp
  constructor
  · rw [le_div_iff₀ hA']; linarith
  · rw [div_le_iff₀ hA']
    calc awakeMass w a = exp (η * bmax) * (exp (-(η * bmax)) * awakeMass w a) := by
          rw [← mul_assoc, ← exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hge (exp_pos _).le

/-- The grid increment is in `[0, η·bmax/δ + 1/2]`. -/
theorem kinc_bounds (hη : 0 ≤ η) (hδ : 0 < δ) {bmax : ℕ} (hb : ∀ j, b0 j ≤ bmax) (w : ι → ℝ)
    (hw : ∀ j, 0 < w j) (a : ι → Bool) :
    0 ≤ kinc η δ w a (fun j => (b0 j : ℝ)) ∧
      (kinc η δ w a (fun j => (b0 j : ℝ)) : ℝ) ≤ η * bmax / δ + 1 / 2 := by
  unfold kinc
  set x := Real.log (awakeMass w a / expMass w a η (fun j => (b0 j : ℝ)))
  have hx : 0 ≤ x ∧ x ≤ η * bmax := by
    by_cases hex : ∃ i, a i = true
    · obtain ⟨i, hi⟩ := hex
      obtain ⟨h1, h2⟩ := ratio_bounds hη hb w hw a hi
      exact ⟨Real.log_nonneg h1, by
        have := Real.log_le_log (by linarith) h2
        rwa [Real.log_exp] at this⟩
    · push Not at hex
      have h0 : awakeMass w a = 0 := Finset.sum_eq_zero fun j _ => by simp [hex j]
      have hb0 : (0 : ℝ) ≤ bmax := Nat.cast_nonneg _
      simp only [x, h0, zero_div, Real.log_zero]
      exact ⟨le_rfl, mul_nonneg hη hb0⟩
  have hr := abs_sub_round (x / δ)
  rw [abs_le] at hr
  have hxd : 0 ≤ x / δ := div_nonneg hx.1 hδ.le
  have hxd2 : x / δ ≤ η * bmax / δ := div_le_div_of_nonneg_right hx.2 hδ.le
  constructor
  · have : (-1 : ℝ) < round (x / δ) := by linarith
    have : (-1 : ℤ) < round (x / δ) := by exact_mod_cast this
    omega
  · linarith

/-- Ranges of the integer state: the loss part is at most `t·bmax`, the normaliser part is in
`[0, t·(η·bmax/δ + 1/2)]`. -/
theorem st_bounds (hq : ∀ i, 0 < q i) (hη : 0 ≤ η) (hδ : 0 < δ) {bmax : ℕ} (hb : ∀ t j, b t j ≤ bmax)
    (t : ℕ) (i : ι) :
    (st q η δ aw b t i).1 ≤ t * bmax ∧ 0 ≤ (st q η δ aw b t i).2 ∧
      ((st q η δ aw b t i).2 : ℝ) ≤ t * (η * bmax / δ + 1 / 2) := by
  induction t with
  | zero => simp [st]
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    obtain ⟨k1, k2⟩ := kinc_bounds hη hδ (hb t) (wOf q η δ (st q η δ aw b t)) (wOf_pos hq _) (aw t)
    have hK : (0 : ℝ) ≤ η * bmax / δ + 1 / 2 := by
      have : (0 : ℝ) ≤ bmax := Nat.cast_nonneg _
      positivity
    simp only [st]
    split_ifs
    · refine ⟨?_, by omega, ?_⟩
      · have := hb t i
        rw [Nat.succ_mul]; omega
      · push_cast
        nlinarith
    · refine ⟨?_, h2, ?_⟩
      · rw [Nat.succ_mul]; omega
      · push_cast; nlinarith

/-! ### Only the awake specialists' data is needed -/

/-- Awake sets are intervals: a specialist that falls asleep never wakes again. -/
def NoRewake (aw : ℕ → ι → Bool) : Prop :=
  ∀ i s u, s ≤ u → aw s i = true → aw u i = false → ∀ v, u ≤ v → aw v i = false

theorem st_of_never {t : ℕ} {i : ι} (h : ∀ s < t, aw s i = false) : st q η δ aw b t i = (0, 0) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [st, h t (Nat.lt_succ_self t), Bool.false_eq_true, if_false]
    exact ih fun s hs => h s (Nat.lt_succ_of_lt hs)

/-- The stored data: integer data of the awake specialists only. -/
noncomputable def stR (q : ι → ℝ) (η δ : ℝ) (aw : ℕ → ι → Bool) (b : ℕ → ι → ℕ) (t : ℕ) :
    ι → Option (ℕ × ℤ) :=
  fun i => if aw t i then some (st q η δ aw b t i) else none

/-- Weights read off the stored data (asleep specialists get the default data, which is never used). -/
noncomputable def wR (q : ι → ℝ) (η δ : ℝ) (σR : ι → Option (ℕ × ℤ)) : ι → ℝ :=
  wOf q η δ (fun i => (σR i).getD (0, 0))

/-- **One step of the finite-data machine**: awake-to-awake specialists add their loss and the grid
increment computed from the stored data; newly awake specialists start at `(0, 0)`; asleep ones are
forgotten. -/
noncomputable def stepR (q : ι → ℝ) (η δ : ℝ) (σR : ι → Option (ℕ × ℤ)) (a a' : ι → Bool) (c : ι → ℕ) :
    ι → Option (ℕ × ℤ) := fun i =>
  if a' i then
    (match σR i with
     | some d => some (d.1 + c i, d.2 + kinc η δ (wR q η δ σR) a (fun j => (c j : ℝ)))
     | none => some (0, 0))
  else none

theorem awakeMass_congr {w w' : ι → ℝ} {a : ι → Bool} (h : ∀ j, a j = true → w j = w' j) :
    awakeMass w a = awakeMass w' a :=
  Finset.sum_congr rfl fun j _ => by by_cases hj : a j <;> simp [hj, h j]

theorem expMass_congr {w w' : ι → ℝ} {a : ι → Bool} (c : ι → ℝ)
    (h : ∀ j, a j = true → w j = w' j) : expMass w a η c = expMass w' a η c :=
  Finset.sum_congr rfl fun j _ => by by_cases hj : a j <;> simp [hj, h j]

theorem wR_stR {t : ℕ} {j : ι} (hj : aw t j = true) :
    wR q η δ (stR q η δ aw b t) j = wOf q η δ (st q η δ aw b t) j := by
  simp [wR, stR, wOf, hj]

theorem kinc_stR (t : ℕ) (c : ι → ℝ) :
    kinc η δ (wR q η δ (stR q η δ aw b t)) (aw t) c = kinc η δ (wOf q η δ (st q η δ aw b t)) (aw t) c := by
  unfold kinc
  rw [awakeMass_congr fun j hj => wR_stR hj, expMass_congr c fun j hj => wR_stR hj]

/-- **The stored data evolves by `stepR`** when awake sets are intervals. -/
theorem stR_succ (hNR : NoRewake aw) (t : ℕ) :
    stR q η δ aw b (t + 1) = stepR q η δ (stR q η δ aw b t) (aw t) (aw (t + 1)) (b t) := by
  funext i
  unfold stepR
  by_cases h1 : aw (t + 1) i
  · simp only [stR, h1, if_true]
    by_cases h0 : aw t i
    · simp only [h0, if_true, st]
      rw [kinc_stR]
    · have h0' : aw t i = false := by simpa using h0
      simp only [h0', Bool.false_eq_true, if_false, st]
      congr 1
      refine st_of_never fun s hs => ?_
      by_contra hc
      have hc' : aw s i = true := by simpa using hc
      have := hNR i s t hs.le hc' h0' (t + 1) (Nat.le_succ t)
      rw [h1] at this
      exact Bool.noConfusion this
  · simp [stR, h1]

/-- The play distribution is a function of the stored data. -/
theorem pprob_eq_stR (hq : ∀ i, 0 < q i) (t : ℕ) (i : ι) :
    pprob q η aw (fun s j => (b s j : ℝ)) (ρM q η δ aw b) t i =
      if aw t i then wR q η δ (stR q η δ aw b t) i / awakeMass (wR q η δ (stR q η δ aw b t)) (aw t)
      else 0 := by
  rw [pprob_eq hq]
  by_cases h : aw t i
  · simp only [h, if_true]
    rw [wR_stR h, awakeMass_congr fun j hj => wR_stR hj]
  · simp [h]

/-- **P0089's regret bound for the finite-data machine**: the realised perturbation has `|ρM| ≤ δ/2`. -/
theorem machine_regret (hq : ∀ i, 0 < q i) (hη : 0 < η) (hδ : 0 < δ) (T : ℕ) (i : ι) :
    ∑ t ∈ Finset.range T, (if aw t i = true then
        ∑ j, pprob q η aw (fun s j => (b s j : ℝ)) (ρM q η δ aw b) t j * (b t j : ℝ) - (b t i : ℝ) else 0) ≤
      (Real.log ((∑ j, q j) / q i) + 2 * (δ / 2) * T) / η +
        η / 2 * ∑ t ∈ Finset.range T, (if aw t i = true then
          ∑ j, pprob q η aw (fun s j => (b s j : ℝ)) (ρM q η δ aw b) t j * (b t j : ℝ) ^ 2 else 0) :=
  pert_sleeping_hedge_regret hq hη (fun _ _ => Nat.cast_nonneg _) (by linarith) (abs_ρM_le hδ) T i

omit [Fintype ι] in
/-- Intersections of interval awake sets are interval awake sets. -/
theorem NoRewake.and {a a' : ℕ → ι → Bool} (ha : NoRewake a) (ha' : NoRewake a') :
    NoRewake (fun t i => a t i && a' t i) := by
  intro i s u hsu hs hu v huv
  simp only [Bool.and_eq_true] at hs
  simp only [Bool.and_eq_false_iff] at hu ⊢
  rcases hu with hu | hu
  · exact Or.inl (ha i s u hsu hs.1 hu v huv)
  · exact Or.inr (ha' i s u hsu hs.2 hu v huv)

omit [Fintype ι] in
/-- A fixed time window per specialist is an interval awake set. -/
theorem NoRewake.window (st0 len : ι → ℕ) :
    NoRewake (fun t i => decide (st0 i ≤ t ∧ t < st0 i + len i)) := by
  intro i s u hsu hs hu v huv
  simp only [decide_eq_true_eq, decide_eq_false_iff_not, not_and, not_lt] at hs hu ⊢
  intro hv
  have := hu (by omega)
  omega

/-- **P0089's dyadic specialists have interval awake sets** when every copy's presence is an interval
(no re-entry after removal). -/
theorem specAw_noRewake {ι₀ : Type*} {L : ℕ} (present : ℕ → ι₀ → Prop)
    (hP : ∀ f s u v, s ≤ u → u ≤ v → present s f → ¬ present u f → ¬ present v f) :
    NoRewake (specAw (L := L) present) := by
  intro i s u hsu hs hu v huv
  simp only [specAw, decide_eq_true_eq, decide_eq_false_iff_not] at hs hu ⊢
  rintro ⟨h1, h2, h3, h4⟩
  apply hu
  refine ⟨h1, by omega, by omega, ?_⟩
  by_contra hpu
  exact hP i.1 s u v hsu huv hs.2.2.2 hpu h4

end Pool.P0096
