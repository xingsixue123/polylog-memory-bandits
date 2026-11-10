import Pool.P0034.Coins

/-!
# Several rounds of fresh coins: a sequential union bound for iterated random filtering
-/

open Finset Real Pool.P0034

namespace Pool.P0042

variable {X : Type*} [Fintype X] [DecidableEq X] (p : ℝ)

/-- Weight of `K` rounds of independent coin vectors. -/
noncomputable def wtK (K : ℕ) (ω : Fin K → X → Bool) : ℝ := ∏ j, wt p (ω j)

/-- Indicator of an event on `K` rounds of coins. -/
noncomputable def indK {K : ℕ} (A : (Fin K → X → Bool) → Prop) (ω : Fin K → X → Bool) : ℝ :=
  Set.indicator {ω | A ω} (fun _ => (1 : ℝ)) ω

/-- Probability of an event on `K` rounds of coins. -/
noncomputable def probK (K : ℕ) (A : (Fin K → X → Bool) → Prop) : ℝ := ∑ ω, wtK p K ω * indK A ω

variable {p}

theorem indK_pos {K : ℕ} {A : (Fin K → X → Bool) → Prop} {ω} (h : A ω) : indK A ω = 1 := by
  simp [indK, Set.indicator_of_mem (show ω ∈ {ω | A ω} from h)]

theorem indK_neg {K : ℕ} {A : (Fin K → X → Bool) → Prop} {ω} (h : ¬ A ω) : indK A ω = 0 := by
  simp [indK, Set.indicator_of_notMem (show ω ∉ {ω | A ω} from h)]

theorem indK_nonneg {K : ℕ} (A : (Fin K → X → Bool) → Prop) (ω) : 0 ≤ indK A ω := by
  by_cases h : A ω
  · rw [indK_pos h]; norm_num
  · rw [indK_neg h]

theorem wtK_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (K : ℕ) (ω : Fin K → X → Bool) : 0 ≤ wtK p K ω :=
  Finset.prod_nonneg fun j _ => wt_nonneg hp0 hp1 (ω j)

/-- Splitting off the last round. -/
theorem sum_split {K : ℕ} (f : (Fin (K + 1) → X → Bool) → ℝ) :
    ∑ ω, f ω = ∑ y : X → Bool, ∑ ω' : Fin K → X → Bool, f (Fin.snoc ω' y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv fun _ => X → Bool) _ _ (fun q => rfl)).symm

theorem wtK_snoc {K : ℕ} (ω' : Fin K → X → Bool) (y : X → Bool) :
    wtK p (K + 1) (Fin.snoc ω' y) = wtK p K ω' * wt p y := by
  unfold wtK
  rw [Fin.prod_univ_castSucc]
  simp

theorem sum_wtK (K : ℕ) : ∑ ω : Fin K → X → Bool, wtK p K ω = 1 := by
  induction K with
  | zero => simp [wtK]
  | succ K ih =>
    rw [sum_split]
    simp only [wtK_snoc, ← Finset.sum_mul, ih, one_mul]
    exact sum_wt

/-- An event depending only on the first `K` rounds has the same probability. -/
theorem probK_init {K : ℕ} (A : (Fin K → X → Bool) → Prop) :
    probK p (K + 1) (fun ω => A (Fin.init ω)) = probK p K A := by
  unfold probK
  rw [sum_split]
  simp only [wtK_snoc]
  have : ∀ (y : X → Bool) (ω' : Fin K → X → Bool),
      indK (fun ω => A (Fin.init ω)) (Fin.snoc ω' y) = indK A ω' := by
    intro y ω'
    by_cases h : A ω'
    · rw [indK_pos h, indK_pos (A := fun ω => A (Fin.init ω)) (by simpa [Fin.init_snoc] using h)]
    · rw [indK_neg h, indK_neg (A := fun ω => A (Fin.init ω)) (by simpa [Fin.init_snoc] using h)]
  simp only [this]
  rw [Finset.sum_comm]
  simp only [mul_comm (wtK p K _) (wt p _), mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_wt, one_mul]

theorem probK_or_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {K : ℕ} (A B : (Fin K → X → Bool) → Prop) :
    probK p K (fun ω => A ω ∨ B ω) ≤ probK p K A + probK p K B := by
  unfold probK
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (wtK_nonneg hp0 hp1 K ω)
  by_cases hA : A ω
  · rw [indK_pos (A := fun ω => A ω ∨ B ω) (Or.inl hA), indK_pos hA]; linarith [indK_nonneg B ω]
  · by_cases hB : B ω
    · rw [indK_pos (A := fun ω => A ω ∨ B ω) (Or.inr hB), indK_pos hB]; linarith [indK_nonneg A ω]
    · rw [indK_neg (A := fun ω => A ω ∨ B ω) (by tauto), indK_neg hA, indK_neg hB]; norm_num

theorem probK_mono (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {K : ℕ} {A B : (Fin K → X → Bool) → Prop}
    (h : ∀ ω, A ω → B ω) : probK p K A ≤ probK p K B := by
  unfold probK
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wtK_nonneg hp0 hp1 K ω)
  by_cases hA : A ω
  · rw [indK_pos hA, indK_pos (h ω hA)]
  · rw [indK_neg hA]; exact indK_nonneg B ω

variable (step : Finset X → (X → Bool) → Finset X) (Q : Finset X)

/-- The pool after `K` rounds of a coin-driven update `step`. -/
def iter : (K : ℕ) → (Fin K → X → Bool) → Finset X
  | 0, _ => Q
  | K + 1, ω => step (iter K (Fin.init ω)) (ω (Fin.last K))

/-- "Some round among the first `K` was bad". -/
def anyBad (bad : Finset X → (X → Bool) → Prop) : (K : ℕ) → (Fin K → X → Bool) → Prop
  | 0, _ => False
  | K + 1, ω => anyBad bad K (Fin.init ω) ∨ bad (iter step Q K (Fin.init ω)) (ω (Fin.last K))

/-- **Sequential union bound.** If every round is bad with probability at most `δ`, whatever the current
pool, then some round among the first `K` is bad with probability at most `K δ`. -/
theorem probK_anyBad_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (bad : Finset X → (X → Bool) → Prop) (δ : ℝ)
    (hδ : ∀ Q', prob p (bad Q') ≤ δ) (K : ℕ) :
    probK p K (anyBad step Q bad K) ≤ K * δ := by
  induction K with
  | zero =>
    unfold probK
    simp only [CharP.cast_eq_zero, zero_mul]
    exact le_of_eq (Finset.sum_eq_zero fun ω _ => by rw [indK_neg (A := anyBad step Q bad 0) id]; ring)
  | succ K ih =>
    have h1 := probK_or_le hp0 hp1 (fun ω : Fin (K + 1) → X → Bool => anyBad step Q bad K (Fin.init ω))
      (fun ω => bad (iter step Q K (Fin.init ω)) (ω (Fin.last K)))
    rw [probK_init] at h1
    have h2 : probK p (K + 1) (fun ω => bad (iter step Q K (Fin.init ω)) (ω (Fin.last K))) ≤ δ := by
      unfold probK
      rw [sum_split]
      simp only [wtK_snoc, Fin.init_snoc, Fin.snoc_last]
      rw [Finset.sum_comm]
      calc ∑ ω' : Fin K → X → Bool, ∑ y : X → Bool, wtK p K ω' * wt p y *
            indK (fun ω => bad (iter step Q K (Fin.init ω)) (ω (Fin.last K))) (Fin.snoc ω' y)
          = ∑ ω' : Fin K → X → Bool, wtK p K ω' * prob p (bad (iter step Q K ω')) := by
            refine Finset.sum_congr rfl fun ω' _ => ?_
            unfold prob
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [mul_assoc]
            congr 2
            by_cases h : bad (iter step Q K ω') y
            · rw [ind_pos h, indK_pos (A := fun ω => bad (iter step Q K (Fin.init ω)) (ω (Fin.last K)))
                (by simpa [Fin.init_snoc, Fin.snoc_last] using h)]
            · rw [ind_neg h, indK_neg (A := fun ω => bad (iter step Q K (Fin.init ω)) (ω (Fin.last K)))
                (by simpa [Fin.init_snoc, Fin.snoc_last] using h)]
        _ ≤ ∑ ω' : Fin K → X → Bool, wtK p K ω' * δ :=
            Finset.sum_le_sum fun ω' _ => mul_le_mul_of_nonneg_left (hδ _) (wtK_nonneg hp0 hp1 K ω')
        _ = δ := by rw [← Finset.sum_mul, sum_wtK, one_mul]
    calc probK p (K + 1) (anyBad step Q bad (K + 1)) ≤ probK p K (anyBad step Q bad K) +
          probK p (K + 1) (fun ω => bad (iter step Q K (Fin.init ω)) (ω (Fin.last K))) := h1
      _ ≤ K * δ + δ := add_le_add ih h2
      _ = ((K + 1 : ℕ) : ℝ) * δ := by push_cast; ring

/-- Every iterated pool is a subset of the initial pool when `step` never adds experts. -/
theorem iter_sub (hstep : ∀ Q' y, step Q' y ⊆ Q') : ∀ K (ω : Fin K → X → Bool), iter step Q K ω ⊆ Q
  | 0, _ => le_rfl
  | K + 1, ω => (hstep _ _).trans (iter_sub hstep K (Fin.init ω))

/-- A bad round always happens at a pool contained in the initial pool. -/
theorem anyBad_sub (hstep : ∀ Q' y, step Q' y ⊆ Q') (bad : Finset X → (X → Bool) → Prop) :
    ∀ K (ω : Fin K → X → Bool), anyBad step Q bad K ω →
      anyBad step Q (fun Q' y => Q' ⊆ Q ∧ bad Q' y) K ω
  | 0, _, h => h
  | K + 1, ω, h => by
    rcases h with h | h
    · exact Or.inl (anyBad_sub hstep bad K (Fin.init ω) h)
    · exact Or.inr ⟨iter_sub step Q hstep K (Fin.init ω), h⟩

end Pool.P0042
