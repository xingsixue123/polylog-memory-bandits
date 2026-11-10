import Pool.Prelude

/-!
# Independent Bernoulli(p) coins on a finite type: miss probabilities, union bound, Chernoff

A minimal finite probability model for random subsets, as used by Peng–Rubinstein-style pool algorithms
(random filter sets, random entry of experts): a coin vector `ω : ι → Bool` has weight
`wt p ω = Π_x (p if ω x else 1 − p)`, and `prob p A = Σ_ω wt p ω · 1[A ω]`.

* `sum_wt` (total mass 1), `sum_prod_bool` (product–sum factorization), `prob_nonneg`, `prob_mono`,
  `prob_compl`, `prob_or_le`, `prob_exists_le` (union bound over a finite family).
* `prob_all_false`: all coins of a set `S` are `false` with probability exactly `(1 − p)^{|S|}`.
* `Fof Q ω`: the sampled subset of `Q`; `prob_card_ge` (Chernoff): for `κ ≥ 0`,
  `P(|Fof Q ω| ≥ c) ≤ exp(p |Q| (e^κ − 1) − κ c)`.
-/

open Finset Real

namespace Pool.P0034

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ)

/-- Probability weight of a coin vector: independent coins, `true` with probability `p`. -/
noncomputable def wt (ω : ι → Bool) : ℝ := ∏ x, if ω x then p else 1 - p

/-- Indicator of an event, as a real number. -/
noncomputable def ind (A : (ι → Bool) → Prop) (ω : ι → Bool) : ℝ :=
  Set.indicator {ω | A ω} (fun _ => (1 : ℝ)) ω

/-- Probability of an event. -/
noncomputable def prob (A : (ι → Bool) → Prop) : ℝ := ∑ ω, wt p ω * ind A ω

variable {p}

theorem ind_pos {A : (ι → Bool) → Prop} {ω : ι → Bool} (h : A ω) : ind A ω = 1 := by
  simp [ind, Set.indicator_of_mem (show ω ∈ {ω | A ω} from h)]

theorem ind_neg {A : (ι → Bool) → Prop} {ω : ι → Bool} (h : ¬ A ω) : ind A ω = 0 := by
  simp [ind, Set.indicator_of_notMem (show ω ∉ {ω | A ω} from h)]

theorem ind_nonneg (A : (ι → Bool) → Prop) (ω : ι → Bool) : 0 ≤ ind A ω := by
  by_cases h : A ω
  · rw [ind_pos h]; norm_num
  · rw [ind_neg h]

theorem ind_le_one (A : (ι → Bool) → Prop) (ω : ι → Bool) : ind A ω ≤ 1 := by
  by_cases h : A ω
  · rw [ind_pos h]
  · rw [ind_neg h]; norm_num

theorem wt_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : ι → Bool) : 0 ≤ wt p ω :=
  Finset.prod_nonneg fun x _ => by split_ifs <;> linarith

/-- Product–sum factorization over coin vectors. -/
theorem sum_prod_bool (f : ι → Bool → ℝ) :
    ∑ ω : ι → Bool, ∏ x, f x (ω x) = ∏ x, (f x true + f x false) := by
  rw [← Fintype.prod_sum]
  simp [Fintype.sum_bool]

theorem sum_wt : ∑ ω : ι → Bool, wt p ω = 1 := by
  unfold wt
  rw [sum_prod_bool (fun _ b => if b then p else 1 - p)]
  simp

theorem prob_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : (ι → Bool) → Prop) : 0 ≤ prob p A :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (wt_nonneg hp0 hp1 ω) (ind_nonneg A ω)

theorem prob_mono (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {A B : (ι → Bool) → Prop} (h : ∀ ω, A ω → B ω) :
    prob p A ≤ prob p B := by
  unfold prob
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wt_nonneg hp0 hp1 ω)
  by_cases hA : A ω
  · rw [ind_pos hA, ind_pos (h ω hA)]
  · rw [ind_neg hA]; exact ind_nonneg B ω

theorem prob_compl (A : (ι → Bool) → Prop) : prob p (fun ω => ¬ A ω) = 1 - prob p A := by
  unfold prob
  calc ∑ ω, wt p ω * ind (fun ω => ¬ A ω) ω = ∑ ω, (wt p ω - wt p ω * ind A ω) := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases h : A ω
        · rw [ind_pos h, ind_neg (A := fun ω => ¬ A ω) (by simpa using h)]; ring
        · rw [ind_neg h, ind_pos (A := fun ω => ¬ A ω) h]; ring
    _ = ∑ ω, wt p ω - ∑ ω, wt p ω * ind A ω := Finset.sum_sub_distrib _ _
    _ = 1 - ∑ ω, wt p ω * ind A ω := by rw [sum_wt]

/-- **Union bound** over a finite family. -/
theorem prob_exists_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {β : Type*} (s : Finset β)
    (A : β → (ι → Bool) → Prop) :
    prob p (fun ω => ∃ b ∈ s, A b ω) ≤ ∑ b ∈ s, prob p (A b) := by
  unfold prob
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ω _ => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (wt_nonneg hp0 hp1 ω)
  by_cases h : ∃ b ∈ s, A b ω
  · obtain ⟨b, hb, hAb⟩ := h
    rw [ind_pos (A := fun ω => ∃ b ∈ s, A b ω) ⟨b, hb, hAb⟩]
    calc (1 : ℝ) = ind (A b) ω := (ind_pos hAb).symm
      _ ≤ ∑ b ∈ s, ind (A b) ω :=
          Finset.single_le_sum (f := fun b => ind (A b) ω) (fun b _ => ind_nonneg _ _) hb
  · rw [ind_neg (A := fun ω => ∃ b ∈ s, A b ω) h]
    exact Finset.sum_nonneg fun b _ => ind_nonneg _ _

theorem prob_or_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A B : (ι → Bool) → Prop) :
    prob p (fun ω => A ω ∨ B ω) ≤ prob p A + prob p B := by
  unfold prob
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (wt_nonneg hp0 hp1 ω)
  by_cases hA : A ω
  · rw [ind_pos (A := fun ω => A ω ∨ B ω) (Or.inl hA), ind_pos hA]; linarith [ind_nonneg B ω]
  · by_cases hB : B ω
    · rw [ind_pos (A := fun ω => A ω ∨ B ω) (Or.inr hB), ind_pos hB]; linarith [ind_nonneg A ω]
    · rw [ind_neg (A := fun ω => A ω ∨ B ω) (by tauto), ind_neg hA, ind_neg hB]; norm_num

/-- **Miss probability**: all coins in `S` are `false` with probability `(1-p)^{|S|}`. -/
theorem prob_all_false (S : Finset ι) : prob p (fun ω => ∀ x ∈ S, ω x = false) = (1 - p) ^ S.card := by
  unfold prob wt
  have key : ∀ ω : ι → Bool, (∏ x, if ω x then p else 1 - p) * ind (fun ω => ∀ x ∈ S, ω x = false) ω =
      ∏ x, (if ω x then (if x ∈ S then 0 else p) else 1 - p) := by
    intro ω
    by_cases h : ∀ x ∈ S, ω x = false
    · rw [ind_pos (A := fun ω => ∀ x ∈ S, ω x = false) h, mul_one]
      refine Finset.prod_congr rfl fun x _ => ?_
      by_cases hx : x ∈ S
      · simp [h x hx]
      · simp [hx]
    · rw [ind_neg (A := fun ω => ∀ x ∈ S, ω x = false) h, mul_zero]
      push Not at h
      obtain ⟨x, hxS, hx⟩ := h
      have hxt : ω x = true := by simpa using hx
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ x)
      simp [hxt, hxS]
  rw [Finset.sum_congr rfl (fun ω _ => key ω)]
  rw [sum_prod_bool (fun x b => if b then (if x ∈ S then 0 else p) else 1 - p)]
  simp only [ite_true, Bool.false_eq_true, ite_false]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x => x ∈ S)]
  have h1 : ∏ x ∈ Finset.univ.filter (fun x => x ∈ S), ((if x ∈ S then (0 : ℝ) else p) + (1 - p)) =
      (1 - p) ^ S.card := by
    rw [Finset.prod_congr rfl (fun x hx => by
      rw [if_pos (Finset.mem_filter.mp hx).2, zero_add]), Finset.prod_const]
    congr 1
    simp
  have h2 : ∏ x ∈ Finset.univ.filter (fun x => x ∉ S),
      ((if x ∈ S then (0 : ℝ) else p) + (1 - p)) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    rw [if_neg (Finset.mem_filter.mp hx).2]; ring
  rw [h1, h2, mul_one]

/-- The sampled set: members of `Q` whose coin is `true`. -/
def Fof (Q : Finset ι) (ω : ι → Bool) : Finset ι := Q.filter fun x => ω x = true

theorem exp_card_Fof (κ : ℝ) (Q : Finset ι) (ω : ι → Bool) :
    exp (κ * (Fof Q ω).card) = ∏ x, (if x ∈ Q ∧ ω x = true then exp κ else 1) := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, ← exp_nat_mul]
  congr 1
  have : (Finset.univ.filter fun x => x ∈ Q ∧ ω x = true) = Fof Q ω := by
    ext x; simp [Fof]
  rw [this]; ring

/-- **Chernoff bound** for the size of the sampled set. -/
theorem prob_card_ge (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Q : Finset ι) {κ : ℝ} (hκ : 0 ≤ κ) (c : ℝ) :
    prob p (fun ω => c ≤ (Fof Q ω).card) ≤ exp (p * Q.card * (exp κ - 1) - κ * c) := by
  unfold prob
  -- indicator ≤ exp (κ (|F| - c))
  have hind : ∀ ω, ind (fun ω => c ≤ ((Fof Q ω).card : ℝ)) ω ≤ exp (-κ * c) * exp (κ * (Fof Q ω).card) := by
    intro ω
    rw [← exp_add]
    by_cases h : c ≤ ((Fof Q ω).card : ℝ)
    · rw [ind_pos (A := fun ω => c ≤ ((Fof Q ω).card : ℝ)) h]
      exact one_le_exp (by nlinarith)
    · rw [ind_neg (A := fun ω => c ≤ ((Fof Q ω).card : ℝ)) h]; exact (exp_pos _).le
  calc ∑ ω, wt p ω * ind (fun ω => c ≤ ((Fof Q ω).card : ℝ)) ω
      ≤ ∑ ω, wt p ω * (exp (-κ * c) * exp (κ * (Fof Q ω).card)) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hind ω) (wt_nonneg hp0 hp1 ω)
    _ = exp (-κ * c) * ∑ ω : ι → Bool, ∏ x, ((if ω x then p else 1 - p) *
          (if x ∈ Q ∧ ω x = true then exp κ else 1)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [exp_card_Fof, wt, Finset.prod_mul_distrib]; ring
    _ = exp (-κ * c) * ∏ x, (if x ∈ Q then p * exp κ + (1 - p) else 1) := by
        rw [sum_prod_bool (fun x b => (if b then p else 1 - p) * (if x ∈ Q ∧ b = true then exp κ else 1))]
        congr 1
        refine Finset.prod_congr rfl fun x _ => ?_
        by_cases hx : x ∈ Q <;> simp [hx]
    _ = exp (-κ * c) * (p * exp κ + (1 - p)) ^ Q.card := by
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        congr 2
        simp
    _ ≤ exp (-κ * c) * exp (p * (exp κ - 1)) ^ Q.card := by
        apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
        apply pow_le_pow_left₀ (by nlinarith [exp_pos κ])
        have := add_one_le_exp (p * (exp κ - 1)); linarith
    _ = exp (p * Q.card * (exp κ - 1) - κ * c) := by
        rw [← exp_nat_mul, ← exp_add]; congr 1; ring

end Pool.P0034
