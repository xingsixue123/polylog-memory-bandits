import Pool.P0012.Potential

/-!
# Ghost-augmented machines and exponential (Chernoff/Azuma) bounds on the state law

Tools to prove high-probability statements about `Pool.P0001` machines without building a path space.

* **Ghost augmentation** (`augment`): add to the state a component `G` (finite) updated deterministically
  from (old state, old ghost, pulled arm, observed loss, new state). The arm law ignores the ghost, so the
  projected state law, the arm law, the expected losses and the regret are unchanged
  (`augment_stateDist_fst`, `augment_armDist`, `augment_expLoss`, `augment_regret`). Use it to carry
  analysis-only quantities (running sums, counters) in the state. The augmented machine is an analysis
  device, not an algorithm, so its memory is irrelevant.
* `probGe M ℓ t f c`: the probability under the state law at round `t` that `f ≥ c`.
* `probGe_le_expect_exp` (Markov/Chernoff), `expect_exp_le` (exponential supermartingale, via P0012's
  `drift`), `exp_le_one_add_add_sq` and `sum_exp_le` (one-step exponential moment).
* `azuma`: if, at every round `t < T` and every reachable state, `Z` has increments in `[-1, 1]` along
  every transition of positive probability and conditional mean `≤ 0`, and `Z 0 ≤ c` on the support of the
  initial law, then `P(Z_T ≥ c + x) ≤ exp(-x²/(4T))` for `0 ≤ x ≤ 2T`. Hypotheses are only required on
  reachable states, so unreachable ghost values need no care.
-/

open Real Finset Pool.P0001 Pool.P0012
open scoped ENNReal

namespace Pool.P0023

variable {n : ℕ}

/-! ### Ghost augmentation -/

/-- Augment a machine with a ghost component `G`, updated deterministically from the old state, the old
ghost value, the pulled arm, the observed loss and the new state. The arm law ignores the ghost. -/
noncomputable def augment (M : Machine n) (G : Type) [Fintype G] (g0 : G)
    (gnext : ℕ → M.State → G → Fin n → Bool → M.State → G) : Machine n where
  State := M.State × G
  init := M.init.map fun s => (s, g0)
  act t p := M.act t p.1
  next t p a b := (M.next t p.1 a b).map fun s' => (s', gnext t p.1 p.2 a b s')

variable (M : Machine n) (G : Type) [Fintype G] (g0 : G)
  (gnext : ℕ → M.State → G → Fin n → Bool → M.State → G)

theorem map_fst_bind (μ : PMF (M.State × G)) (ℓ : LossSeq n) (t : ℕ)
    (h : M.State × G → Fin n → M.State → G) :
    PMF.map Prod.fst (μ.bind fun p => (M.act t p.1).bind fun a =>
        (M.next t p.1 a (ℓ t a)).map fun s' => (s', h p a s')) =
      (μ.map Prod.fst).bind fun s => (M.act t s).bind fun a => M.next t s a (ℓ t a) := by
  rw [PMF.map_bind, PMF.bind_map]
  congr 1
  funext p
  simp only [Function.comp_apply, PMF.map_bind]
  congr 1; funext a
  rw [PMF.map_comp]
  exact PMF.map_id _

theorem augment_stateDist_fst (ℓ : LossSeq n) (t : ℕ) :
    PMF.map Prod.fst ((augment M G g0 gnext).stateDist ℓ t : PMF (M.State × G)) =
      M.stateDist ℓ t := by
  induction t with
  | zero =>
    change PMF.map Prod.fst (M.init.map fun s => (s, g0)) = M.init
    rw [PMF.map_comp]; exact PMF.map_id M.init
  | succ t ih =>
    have key := map_fst_bind M G ((augment M G g0 gnext).stateDist ℓ t) ℓ t
      (fun p a s' => gnext t p.1 p.2 a (ℓ t a) s')
    rw [ih] at key
    exact key

theorem augment_armDist (ℓ : LossSeq n) (t : ℕ) :
    (augment M G g0 gnext).armDist ℓ t = M.armDist ℓ t := by
  have h := augment_stateDist_fst M G g0 gnext ℓ t
  have key : M.armDist ℓ t = (PMF.map Prod.fst
      ((augment M G g0 gnext).stateDist ℓ t : PMF (M.State × G))).bind (M.act t) := by
    rw [h]; rfl
  rw [key]
  exact (PMF.bind_map (p := ((augment M G g0 gnext).stateDist ℓ t : PMF (M.State × G)))
    Prod.fst (M.act t)).symm

theorem augment_expLoss (ℓ : LossSeq n) (t : ℕ) :
    (augment M G g0 gnext).expLoss ℓ t = M.expLoss ℓ t := by
  simp only [Machine.expLoss, augment_armDist]

/-- Augmentation does not change the regret. -/
theorem augment_regret (ℓ : LossSeq n) (T : ℕ) :
    regret (augment M G g0 gnext) ℓ T = regret M ℓ T := by
  simp only [regret, augment_expLoss]

/-! ### Probabilities under the state law, Markov and exponential supermartingales -/

/-- Probability, under the law of the state at round `t`, that `f ≥ c`. -/
noncomputable def probGe (M : Machine n) (ℓ : LossSeq n) (t : ℕ) (f : M.State → ℝ) (c : ℝ) : ℝ :=
  ∑ s, (M.stateDist ℓ t s).toReal * (if c ≤ f s then 1 else 0)

/-- Chernoff–Markov: `P(f ≥ c) ≤ E[exp(κ (f - c))]` for `κ ≥ 0`. -/
theorem probGe_le_expect_exp (M : Machine n) (ℓ : LossSeq n) (t : ℕ) (f : M.State → ℝ) (c : ℝ)
    {κ : ℝ} (hk : 0 ≤ κ) :
    probGe M ℓ t f c ≤ expect M ℓ t (fun s => exp (κ * (f s - c))) := by
  unfold probGe Pool.P0012.expect
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
  split_ifs with h
  · exact one_le_exp (mul_nonneg hk (by linarith))
  · exact (exp_pos _).le

/-- Monotonicity of `expect` needs the inequality only on the support of the state law. -/
theorem expect_mono_of_support (M : Machine n) (ℓ : LossSeq n) (t : ℕ) {f g : M.State → ℝ}
    (h : ∀ s, M.stateDist ℓ t s ≠ 0 → f s ≤ g s) :
    expect M ℓ t f ≤ expect M ℓ t g := by
  unfold Pool.P0012.expect
  refine Finset.sum_le_sum fun s _ => ?_
  by_cases hs : M.stateDist ℓ t s = 0
  · simp [hs]
  · exact mul_le_mul_of_nonneg_left (h s hs) ENNReal.toReal_nonneg

/-- **Exponential supermartingale.** If `E[exp(κ Z_{t+1}) | s] ≤ exp(κ Z_t(s))` for every round `t < T`
and every state `s` reachable at round `t` (`M.stateDist ℓ t s ≠ 0`), then
`E[exp(κ Z_T)] ≤ E_init[exp(κ Z_0)]`. Unreachable states are unconstrained. -/
theorem expect_exp_le (M : Machine n) (ℓ : LossSeq n) (Z : ℕ → M.State → ℝ) (κ : ℝ) (T : ℕ)
    (h : ∀ t, t < T → ∀ s, M.stateDist ℓ t s ≠ 0 →
      stepExp M ℓ t s (fun s' => exp (κ * Z (t + 1) s')) ≤ exp (κ * Z t s)) :
    expect M ℓ T (fun s => exp (κ * Z T s)) ≤ expect M ℓ 0 (fun s => exp (κ * Z 0 s)) := by
  have key : ∀ m, m ≤ T →
      expect M ℓ m (fun s => exp (κ * Z m s)) ≤ expect M ℓ 0 (fun s => exp (κ * Z 0 s)) := by
    intro m
    induction m with
    | zero => intro _; exact le_rfl
    | succ m ih =>
      intro hm
      rw [expect_succ]
      exact (expect_mono_of_support M ℓ m fun s hs => h m (by omega) s hs).trans (ih (by omega))
  exact key T le_rfl

/-- `exp x ≤ 1 + x + x²` for `x ≤ 1`. -/
theorem exp_le_one_add_add_sq {x : ℝ} (hx : x ≤ 1) : exp x ≤ 1 + x + x ^ 2 := by
  rcases le_or_gt (-1) x with h | h
  · have habs : |x| ≤ 1 := abs_le.mpr ⟨h, hx⟩
    have := abs_exp_sub_one_sub_id_le habs
    have := (abs_le.mp this).2
    linarith
  · have h1 : exp x ≤ 1 := exp_le_one_iff.mpr (by linarith)
    nlinarith

/-- **One-step exponential moment bound.** For a probability vector `p` on a finite type and values
`x` with `κ x ≤ 1`: `Σ p_a exp(κ x_a) ≤ exp(κ Σ p_a x_a + κ² Σ p_a x_a²)`. -/
theorem sum_exp_le {α : Type} [Fintype α] (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (x : α → ℝ) {κ : ℝ} (hx : ∀ a, p a ≠ 0 → κ * x a ≤ 1) :
    ∑ a, p a * exp (κ * x a) ≤ exp (κ * ∑ a, p a * x a + κ ^ 2 * ∑ a, p a * x a ^ 2) := by
  calc ∑ a, p a * exp (κ * x a) ≤ ∑ a, p a * (1 + κ * x a + (κ * x a) ^ 2) := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases h0 : p a = 0
        · simp [h0]
        · exact mul_le_mul_of_nonneg_left (exp_le_one_add_add_sq (hx a h0)) (hp a)
    _ = 1 + (κ * ∑ a, p a * x a + κ ^ 2 * ∑ a, p a * x a ^ 2) := by
        have e : ∀ a, p a * (1 + κ * x a + (κ * x a) ^ 2) =
            p a + (κ * (p a * x a) + κ ^ 2 * (p a * x a ^ 2)) := fun a => by ring
        simp only [e, Finset.sum_add_distrib, hp1, Finset.mul_sum]
    _ ≤ exp (κ * ∑ a, p a * x a + κ ^ 2 * ∑ a, p a * x a ^ 2) := by
        have := add_one_le_exp (κ * ∑ a, p a * x a + κ ^ 2 * ∑ a, p a * x a ^ 2); linarith

/-- `stepExp` as one expectation over (pulled arm, next state). -/
theorem stepExp_eq_sum_pair (M : Machine n) (ℓ : LossSeq n) (t : ℕ) (s : M.State)
    (f : M.State → ℝ) :
    stepExp M ℓ t s f = ∑ q : Fin n × M.State,
      ((M.act t s q.1).toReal * (M.next t s q.1 (ℓ t q.1) q.2).toReal) * f q.2 := by
  unfold stepExp
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => by ring

theorem sum_pair_prob (M : Machine n) (ℓ : LossSeq n) (t : ℕ) (s : M.State) :
    ∑ q : Fin n × M.State, (M.act t s q.1).toReal * (M.next t s q.1 (ℓ t q.1) q.2).toReal = 1 := by
  have h1 : ∀ {β : Type} [Fintype β] (μ : PMF β), ∑ b, (μ b).toReal = 1 := by
    intro β _ μ
    rw [← ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top _ b),
      ← tsum_fintype (L := .unconditional _) (fun b => μ b), PMF.tsum_coe, ENNReal.toReal_one]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, h1, mul_one]

/-- **Azuma–Hoeffding on the state law.** Let `Z t s` be a real function of round and state. Suppose that,
for every round `t < T` and every state `s` reachable at round `t` (`M.stateDist ℓ t s ≠ 0`), the
increments of `Z` along the transitions of positive probability from `s` are at most `1` in absolute value
and have conditional mean `≤ 0`, and that `Z 0 ≤ c` on the support of the initial law. Then for
`0 ≤ x ≤ 2T`, `P(Z_T ≥ c + x) ≤ exp(-x²/(4T))`. Unreachable states and rounds `≥ T` are unconstrained. -/
theorem azuma (M : Machine n) (ℓ : LossSeq n) (Z : ℕ → M.State → ℝ) (c : ℝ) {T : ℕ}
    (h0 : ∀ s, M.init s ≠ 0 → Z 0 s ≤ c)
    (hbd : ∀ t, t < T → ∀ s, M.stateDist ℓ t s ≠ 0 → ∀ a s', M.act t s a ≠ 0 →
      M.next t s a (ℓ t a) s' ≠ 0 → |Z (t + 1) s' - Z t s| ≤ 1)
    (hmean : ∀ t, t < T → ∀ s, M.stateDist ℓ t s ≠ 0 →
      stepExp M ℓ t s (fun s' => Z (t + 1) s' - Z t s) ≤ 0)
    (hT : 0 < T) {x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ 2 * T) :
    probGe M ℓ T (Z T) (c + x) ≤ exp (-(x ^ 2) / (4 * T)) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set κ := x / (2 * T) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκ1 : κ ≤ 1 := by rw [hκ, div_le_one (by positivity)]; exact hxT
  set W : ℕ → M.State → ℝ := fun t s => Z t s - κ * t
  -- exponential supermartingale for W
  have hsup : ∀ t, t < T → ∀ s, M.stateDist ℓ t s ≠ 0 →
      stepExp M ℓ t s (fun s' => exp (κ * W (t + 1) s')) ≤ exp (κ * W t s) := by
    intro t ht s hs
    set p : Fin n × M.State → ℝ := fun q => (M.act t s q.1).toReal * (M.next t s q.1 (ℓ t q.1) q.2).toReal
    set D : Fin n × M.State → ℝ := fun q => Z (t + 1) q.2 - Z t s
    have hp : ∀ q, 0 ≤ p q := fun q => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have hp1 : ∑ q, p q = 1 := sum_pair_prob M ℓ t s
    have hsupp : ∀ q, p q ≠ 0 → |D q| ≤ 1 := by
      intro q hq
      have ha : M.act t s q.1 ≠ 0 := by
        intro h; apply hq; simp [p, h]
      have hb : M.next t s q.1 (ℓ t q.1) q.2 ≠ 0 := by
        intro h; apply hq; simp [p, h]
      exact hbd t ht s hs q.1 q.2 ha hb
    have hm : ∑ q, p q * D q ≤ 0 := by
      have := hmean t ht s hs; rw [stepExp_eq_sum_pair] at this; simpa [p, D] using this
    have hv : ∑ q, p q * D q ^ 2 ≤ 1 := by
      calc ∑ q, p q * D q ^ 2 ≤ ∑ q, p q := by
            refine Finset.sum_le_sum fun q _ => ?_
            by_cases h : p q = 0
            · simp [h]
            · have := hsupp q h
              have : D q ^ 2 ≤ 1 := by
                rw [sq_le_one_iff_abs_le_one]; exact this
              nlinarith [hp q]
        _ = 1 := hp1
    have hstep := sum_exp_le p hp hp1 D (κ := κ) (fun q hq => by
      have := hsupp q hq
      calc κ * D q ≤ κ * 1 := mul_le_mul_of_nonneg_left (abs_le.mp this).2 hκ0
        _ ≤ 1 := by linarith)
    have e : ∀ q : Fin n × M.State, p q * exp (κ * W (t + 1) q.2) =
        exp (κ * W t s - κ ^ 2) * (p q * exp (κ * D q)) := by
      intro q
      rw [mul_left_comm, ← exp_add]
      congr 2
      simp only [W, D]; push_cast; ring
    calc stepExp M ℓ t s (fun s' => exp (κ * W (t + 1) s'))
        = ∑ q, p q * exp (κ * W (t + 1) q.2) := by rw [stepExp_eq_sum_pair]
      _ = exp (κ * W t s - κ ^ 2) * ∑ q, p q * exp (κ * D q) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => e q
      _ ≤ exp (κ * W t s - κ ^ 2) * exp (κ * ∑ q, p q * D q + κ ^ 2 * ∑ q, p q * D q ^ 2) :=
          mul_le_mul_of_nonneg_left hstep (exp_pos _).le
      _ = exp (κ * W t s - κ ^ 2 + (κ * ∑ q, p q * D q + κ ^ 2 * ∑ q, p q * D q ^ 2)) := by
          rw [← exp_add]
      _ ≤ exp (κ * W t s) := by
          apply exp_le_exp.mpr
          have h1 : κ * ∑ q, p q * D q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ0 hm
          have h2 : κ ^ 2 * ∑ q, p q * D q ^ 2 ≤ κ ^ 2 := by
            have := mul_le_mul_of_nonneg_left hv (sq_nonneg κ); linarith
          linarith
  have hE := expect_exp_le M ℓ W κ T hsup
  have hE0 : expect M ℓ 0 (fun s => exp (κ * W 0 s)) ≤ exp (κ * c) := by
    unfold Pool.P0012.expect
    calc ∑ s, (M.stateDist ℓ 0 s).toReal * exp (κ * W 0 s)
        ≤ ∑ s, (M.stateDist ℓ 0 s).toReal * exp (κ * c) := by
          refine Finset.sum_le_sum fun s _ => ?_
          by_cases hs : M.init s = 0
          · have : M.stateDist ℓ 0 s = 0 := hs
            simp [this]
          refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          apply exp_le_exp.mpr
          simp only [W, Nat.cast_zero, mul_zero, sub_zero]
          exact mul_le_mul_of_nonneg_left (h0 s hs) hκ0
      _ = exp (κ * c) := by
          rw [← Finset.sum_mul]
          rw [← ENNReal.toReal_sum (fun s _ => PMF.apply_ne_top _ s),
            ← tsum_fintype (L := .unconditional _) (fun s => M.stateDist ℓ 0 s), PMF.tsum_coe,
            ENNReal.toReal_one, one_mul]
  -- Markov
  have hM := probGe_le_expect_exp M ℓ T (Z T) (c + x) hκ0
  have hrel : expect M ℓ T (fun s => exp (κ * (Z T s - (c + x)))) =
      exp (κ * T * κ - κ * (c + x)) * expect M ℓ T (fun s => exp (κ * W T s)) := by
    unfold Pool.P0012.expect
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_left_comm, ← exp_add]
    congr 2
    simp only [W]; ring_nf
  rw [hrel] at hM
  calc probGe M ℓ T (Z T) (c + x)
      ≤ exp (κ * T * κ - κ * (c + x)) * expect M ℓ T (fun s => exp (κ * W T s)) := hM
    _ ≤ exp (κ * T * κ - κ * (c + x)) * exp (κ * c) :=
        mul_le_mul_of_nonneg_left (hE.trans hE0) (exp_pos _).le
    _ = exp (-(x ^ 2) / (4 * T)) := by
        rw [← exp_add]; congr 1; rw [hκ]; field_simp; ring


/-! ### Worked use: a saturating ghost counter -/

/-- Sum against the image of a PMF on finite types. -/
theorem sum_map_toReal {α β : Type} [Fintype α] [Fintype β] (μ : PMF α) (φ : α → β) (f : β → ℝ) :
    ∑ b, ((μ.map φ) b).toReal * f b = ∑ a, (μ a).toReal * f (φ a) := by
  rw [← PMF.bind_pure_comp]
  simp only [bind_toReal, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, PMF.pure_apply, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_eq_single (φ a) (fun b _ hb => by simp [hb]) (by simp)]
  simp

/-- Ghost update of a counter in `Fin (K + 1)`: add one (saturating at `K`) when `inc` holds. -/
def counterNext (M : Machine n) (K : ℕ) (inc : ℕ → M.State → Fin n → Bool → M.State → Bool) :
    ℕ → M.State → Fin (K + 1) → Fin n → Bool → M.State → Fin (K + 1) :=
  fun t s g a b s' => if inc t s a b s' then ⟨min (g.val + 1) K, by omega⟩ else g

theorem counterNext_sub (M : Machine n) (K : ℕ) (inc : ℕ → M.State → Fin n → Bool → M.State → Bool)
    (t : ℕ) (s : M.State) (g : Fin (K + 1)) (a : Fin n) (b : Bool) (s' : M.State) :
    0 ≤ ((counterNext M K inc t s g a b s').val : ℝ) - g.val ∧
      ((counterNext M K inc t s g a b s').val : ℝ) - g.val ≤ if inc t s a b s' then 1 else 0 := by
  have hg := g.isLt
  unfold counterNext
  split_ifs with h
  · have : min (g.val + 1) K = g.val ∨ min (g.val + 1) K = g.val + 1 := by omega
    rcases this with h2 | h2
    · refine ⟨?_, ?_⟩ <;> simp only [h2] <;> norm_num
    · refine ⟨?_, ?_⟩ <;> simp only [h2] <;> push_cast <;> linarith
  · simp

/-- **Worked example (counting events).** Augment `M` with a saturating ghost counter `g ∈ Fin (K + 1)`,
started at `0`, that counts the transitions on which `inc` holds. If, at every round `t < T` and every
state reachable in `M`, the conditional probability that `inc` holds is at most `q`, then
`P(g_T ≥ q T + x) ≤ exp(-x²/(4T))` for `0 ≤ x ≤ 2T`. Here `Z t (s, g) = g - q t` and `c = 0`;
the ghost values that are never reached play no role. -/
theorem azuma_counter (M : Machine n) (ℓ : LossSeq n) (K : ℕ)
    (inc : ℕ → M.State → Fin n → Bool → M.State → Bool) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    {T : ℕ} (hT : 0 < T)
    (hinc : ∀ t, t < T → ∀ s, M.stateDist ℓ t s ≠ 0 →
      ∑ a, (M.act t s a).toReal *
        ∑ s', (M.next t s a (ℓ t a) s').toReal * (if inc t s a (ℓ t a) s' then 1 else 0) ≤ q)
    {x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ 2 * T) :
    probGe (augment M (Fin (K + 1)) 0 (counterNext M K inc)) ℓ T
      (fun p => ((p.2 : ℕ) : ℝ)) (q * T + x) ≤ exp (-(x ^ 2) / (4 * T)) := by
  have hfst : ∀ t (p : M.State × Fin (K + 1)),
      ((augment M (Fin (K + 1)) 0 (counterNext M K inc)).stateDist ℓ t : PMF (M.State × Fin (K + 1))) p
        ≠ 0 → M.stateDist ℓ t p.1 ≠ 0 := by
    intro t p hp
    have hmem : p.1 ∈ (PMF.map Prod.fst
        ((augment M (Fin (K + 1)) 0 (counterNext M K inc)).stateDist ℓ t :
          PMF (M.State × Fin (K + 1)))).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨p, (PMF.mem_support_iff _ _).mpr hp, rfl⟩
    rw [augment_stateDist_fst] at hmem
    exact (PMF.mem_support_iff _ _).mp hmem
  have hsum1 : ∀ (t : ℕ) (s : M.State) (a : Fin n), ∑ s', (M.next t s a (ℓ t a) s').toReal = 1 := by
    intro t s a
    rw [← ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top _ b),
      ← tsum_fintype (L := .unconditional _) (fun b => M.next t s a (ℓ t a) b), PMF.tsum_coe,
      ENNReal.toReal_one]
  have hact1 : ∀ (t : ℕ) (s : M.State), ∑ a, (M.act t s a).toReal = 1 := by
    intro t s
    rw [← ENNReal.toReal_sum (fun b _ => PMF.apply_ne_top _ b),
      ← tsum_fintype (L := .unconditional _) (fun b => M.act t s b), PMF.tsum_coe, ENNReal.toReal_one]
  have key := azuma (augment M (Fin (K + 1)) 0 (counterNext M K inc)) ℓ (fun t p => ((p.2 : ℕ) : ℝ) - q * t) 0 (T := T) ?_ ?_ ?_ hT hx0 hxT
  · have e : (fun p : M.State × Fin (K + 1) => ((p.2 : ℕ) : ℝ) - q * T) =
        fun p => ((p.2 : ℕ) : ℝ) - q * T := rfl
    unfold probGe at key ⊢
    convert key using 3 with p
    congr 1
    apply propext
    constructor <;> intro h <;> linarith
  · intro p hp
    change M.init.map (fun s => (s, (0 : Fin (K + 1)))) p ≠ 0 at hp
    obtain ⟨s, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hp)
    simp
  · intro t _ p _ a p' _ hn
    change (M.next t p.1 a (ℓ t a)).map (fun s' => (s', counterNext M K inc t p.1 p.2 a (ℓ t a) s')) p'
      ≠ 0 at hn
    obtain ⟨s', _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_iff _ _).mpr hn)
    obtain ⟨h1, h2⟩ := counterNext_sub M K inc t p.1 p.2 a (ℓ t a) s'
    have h3 : ((counterNext M K inc t p.1 p.2 a (ℓ t a) s').val : ℝ) - p.2.val ≤ 1 :=
      h2.trans (by split_ifs <;> norm_num)
    rw [abs_le]
    push_cast
    constructor <;> nlinarith
  · intro t ht p hp
    have hs := hinc t ht p.1 (hfst t p hp)
    unfold stepExp
    change ∑ a, (M.act t p.1 a).toReal * ∑ p', (((M.next t p.1 a (ℓ t a)).map
      (fun s' => (s', counterNext M K inc t p.1 p.2 a (ℓ t a) s'))) p').toReal *
        ((((p'.2 : ℕ) : ℝ) - q * ((t + 1 : ℕ) : ℝ)) - (((p.2 : ℕ) : ℝ) - q * t)) ≤ 0
    simp only [sum_map_toReal]
    have hle : ∀ a, ∑ s', (M.next t p.1 a (ℓ t a) s').toReal *
        ((((counterNext M K inc t p.1 p.2 a (ℓ t a) s' : ℕ) : ℝ) - q * ((t + 1 : ℕ) : ℝ)) -
          (((p.2 : ℕ) : ℝ) - q * t)) ≤
        ∑ s', (M.next t p.1 a (ℓ t a) s').toReal * (if inc t p.1 a (ℓ t a) s' then 1 else 0) - q := by
      intro a
      calc _ ≤ ∑ s', (M.next t p.1 a (ℓ t a) s').toReal *
            ((if inc t p.1 a (ℓ t a) s' then 1 else 0) - q) := by
            refine Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            have := (counterNext_sub M K inc t p.1 p.2 a (ℓ t a) s').2
            push_cast; linarith
        _ = _ := by
            simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul]
    calc _ ≤ ∑ a, (M.act t p.1 a).toReal *
          (∑ s', (M.next t p.1 a (ℓ t a) s').toReal * (if inc t p.1 a (ℓ t a) s' then 1 else 0) - q) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hle a) ENNReal.toReal_nonneg
      _ = (∑ a, (M.act t p.1 a).toReal *
          ∑ s', (M.next t p.1 a (ℓ t a) s').toReal * (if inc t p.1 a (ℓ t a) s' then 1 else 0)) - q := by
          simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hact1, one_mul]
      _ ≤ 0 := by linarith

end Pool.P0023
