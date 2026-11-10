import Pool.P0018.Pexp
import Pool.P0001.Targets
import Pool.P0012.Potential
import Pool.P0009.Hedge

/-!
# EXP3 with finite-precision (randomized-rounding) counters, as a `Pool.P0001` machine

The classical EXP3 algorithm (Auer, Cesa-Bianchi, Freund, Schapire 2002), implemented with a
finite state: one integer counter per arm. With `γ = 1/(2T+2)` and
`η = √((1 + log n)/((2n+1)(T+1)))`:

* in state `c` the machine pulls arm `a` with probability `p_a = (1-γ) q_a + γ/n`, where
  `q ∝ exp(-η c)` (`actPMF`);
* on observing loss `1` it adds to `c_a` a random integer with mean exactly `1/p_a`
  (`⌊1/p_a⌋` or `⌊1/p_a⌋ + 1`, randomized rounding; `nextPMF`); on loss `0` nothing changes.
  The counters saturate at `Kcap n T = T (n(2T+2)+1)`, which is never reached before round `T`
  (`good_reachable`, `noSat_of_good`).

Main results (for every `n ≥ 1`, every `T` and every oblivious loss sequence `ℓ`):
* `exp3M_regret_le`: `regret ≤ (1/η) log n + T (γ + η(2n+1)/2)`;
* `exp3M_regret_le_sqrt`: `regret ≤ (3/2) √((1 + log n)(2n+1)(T+1)) + 1/2`;
* `exp3M_memBits`: `memBits = n · log₂ (Kcap n T + 1)`, i.e. `O(n log (nT))` bits;
* `exp3M_isHomogeneous`: the machine does not use the round number;
* `exp3Family_regretBound`, `exp3Family_memBits`: the same for the family `n T ↦ exp3M n T`.

The proof is the potential argument of `Pool.P0012.regret_le_of_potential` with
`Φ_i(c) = (1/η) log Σ_j exp(-η c_j) + c_i ≥ 0`. The one-step inequality (`step_le`) uses
`Pool.P0009.exp_neg_le_quadratic`; the unbiasedness of the counters is built into it.
On unreachable (saturating) states the error term is set to a large constant, which costs
nothing because those states have probability `0`.
-/

open scoped ENNReal NNReal Pool.P0001
open Pool.P0001 Finset Real

namespace Pool.P0018

/-! ### Small PMF expectation lemmas -/

section pmf
variable {α β : Type} [Fintype α] [Fintype β]

lemma pexp_pure [DecidableEq α] (a : α) (f : α → ℝ) : pexp (PMF.pure a) f = f a := by
  unfold pexp
  rw [Finset.sum_eq_single a]
  · simp [PMF.pure_apply]
  · intro b _ hb; simp [PMF.pure_apply, hb]
  · simp

lemma pexp_map [DecidableEq β] (μ : PMF α) (g : α → β) (f : β → ℝ) :
    pexp (μ.map g) f = pexp μ (fun a => f (g a)) := by
  rw [← PMF.bind_pure_comp, pexp_bind]
  congr 1; funext a
  exact pexp_pure (g a) f

lemma pexp_bernoulli (p : ℝ≥0) (h : p ≤ 1) (f : Bool → ℝ) :
    pexp (PMF.bernoulli p h) f = (p : ℝ) * f true + (1 - (p : ℝ)) * f false := by
  unfold pexp
  rw [Fintype.sum_bool]
  simp only [PMF.bernoulli_apply, cond_true, cond_false]
  rw [ENNReal.coe_toReal, ENNReal.coe_toReal, NNReal.coe_sub h, NNReal.coe_one]

lemma pexp_ofFintype (g : α → ℝ≥0∞) (hg : ∑ a, g a = 1) (f : α → ℝ) :
    pexp (PMF.ofFintype g hg) f = ∑ a, (g a).toReal * f a := rfl

end pmf

/-! ### The algorithm -/

variable {n : ℕ}

/-- States: one counter in `{0, …, K}` per arm. -/
abbrev St (n K : ℕ) := Fin n → Fin (K + 1)

/-- Exponential weight of arm `i`. -/
noncomputable def wt (η : ℝ) {K : ℕ} (s : St n K) (i : Fin n) : ℝ := exp (-η * ((s i : ℕ) : ℝ))

/-- Total weight. -/
noncomputable def W (η : ℝ) {K : ℕ} (s : St n K) : ℝ := ∑ i, wt η s i

/-- Hedge probabilities. -/
noncomputable def q (η : ℝ) {K : ℕ} (s : St n K) (i : Fin n) : ℝ := wt η s i / W η s

/-- Played probabilities: Hedge mixed with uniform exploration. -/
noncomputable def p (η γ : ℝ) {K : ℕ} (s : St n K) (i : Fin n) : ℝ :=
  (1 - γ) * q η s i + γ / n

lemma wt_pos (η : ℝ) {K : ℕ} (s : St n K) (i : Fin n) : 0 < wt η s i := exp_pos _

lemma W_pos [NeZero n] (η : ℝ) {K : ℕ} (s : St n K) : 0 < W η s :=
  Finset.sum_pos (fun i _ => wt_pos η s i) Finset.univ_nonempty

lemma q_nonneg [NeZero n] (η : ℝ) {K : ℕ} (s : St n K) (i : Fin n) : 0 ≤ q η s i :=
  div_nonneg (wt_pos η s i).le (W_pos η s).le

lemma sum_q [NeZero n] (η : ℝ) {K : ℕ} (s : St n K) : ∑ i, q η s i = 1 := by
  unfold q; rw [← Finset.sum_div]; exact div_self (W_pos η s).ne'

lemma p_pos [NeZero n] {η γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {K : ℕ} (s : St n K) (i : Fin n) :
    0 < p η γ s i := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold p
  have := q_nonneg η s i
  have : 0 ≤ (1 - γ) * q η s i := mul_nonneg (by linarith) this
  have : 0 < γ / n := div_pos hγ0 hn
  linarith

lemma sum_p [NeZero n] (η γ : ℝ) {K : ℕ} (s : St n K) : ∑ i, p η γ s i = 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  unfold p
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_q, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The law of the pulled arm. -/
noncomputable def actPMF [NeZero n] {η γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) {K : ℕ} (s : St n K) :
    PMF (Fin n) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (p η γ s i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (p_pos hγ0 hγ1 s i).le), sum_p, ENNReal.ofReal_one])

/-- Saturating counter value. -/
def sat (K m : ℕ) : Fin (K + 1) := ⟨min m K, by omega⟩

/-- The state after adding `k` to the counter of arm `a`. -/
def bump {K : ℕ} (s : St n K) (a : Fin n) (k : ℕ) : St n K :=
  Function.update s a (sat K ((s a : ℕ) + k))

/-- The importance weight `1/p` of the pulled arm. -/
noncomputable def iw (η γ : ℝ) {K : ℕ} (s : St n K) (a : Fin n) : ℝ := 1 / p η γ s a

lemma frac_le_one (y : ℝ) : (y - ⌊y⌋₊ : ℝ).toNNReal ≤ 1 := by
  rw [Real.toNNReal_le_one]
  rcases le_or_gt 0 y with hy | hy
  · linarith [Nat.lt_floor_add_one y]
  · rw [Nat.floor_eq_zero.2 (by linarith)]; simp; linarith

/-- Transition after observing loss bit `b` of arm `a`: on loss `1`, the counter of `a` grows by
`⌊1/p_a⌋` or `⌊1/p_a⌋ + 1`, with mean `1/p_a` (randomized rounding). -/
noncomputable def nextPMF (η γ : ℝ) {K : ℕ} (s : St n K) (a : Fin n) (b : Bool) : PMF (St n K) :=
  if b then
    (PMF.bernoulli (iw η γ s a - ⌊iw η γ s a⌋₊ : ℝ).toNNReal (frac_le_one _)).map fun c =>
      bump s a (⌊iw η γ s a⌋₊ + c.toNat)
  else PMF.pure s

/-- EXP3 with randomized-rounding counters saturating at `K`. -/
noncomputable def exp3 (n : ℕ) [NeZero n] (η γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (K : ℕ) :
    Machine n where
  State := St n K
  init := PMF.pure fun _ => 0
  act _ s := actPMF (η := η) hγ0 hγ1 s
  next _ s a b := nextPMF η γ s a b


/-! ### Analysis -/

section analysis

variable [NeZero n] {K : ℕ}

lemma n_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

/-- Counter value after a bump that does not saturate. -/
lemma bump_val_self {s : St n K} {a : Fin n} {k : ℕ} (hk : (s a : ℕ) + k ≤ K) :
    ((bump s a k a : Fin (K + 1)) : ℕ) = (s a : ℕ) + k := by
  simp [bump, sat, Nat.min_eq_left hk]

lemma bump_val_self_le (s : St n K) (a : Fin n) (k : ℕ) :
    ((bump s a k a : Fin (K + 1)) : ℕ) ≤ (s a : ℕ) + k := by
  simp [bump, sat]

lemma bump_val_ne (s : St n K) {a j : Fin n} (k : ℕ) (hj : j ≠ a) : bump s a k j = s j := by
  simp [bump, Function.update_of_ne hj]

lemma wt_bump_self (η : ℝ) {s : St n K} {a : Fin n} {k : ℕ} (hk : (s a : ℕ) + k ≤ K) :
    wt η (bump s a k) a = wt η s a * exp (-η * k) := by
  unfold wt
  rw [bump_val_self hk, ← exp_add]
  congr 1; push_cast; ring

lemma W_bump (η : ℝ) {s : St n K} {a : Fin n} {k : ℕ} (hk : (s a : ℕ) + k ≤ K) :
    W η (bump s a k) = W η s - wt η s a + wt η s a * exp (-η * k) := by
  unfold W
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
    wt_bump_self η hk]
  have : ∑ x ∈ Finset.univ.erase a, wt η (bump s a k) x = ∑ x ∈ Finset.univ.erase a, wt η s x :=
    Finset.sum_congr rfl fun j hj => by
      unfold wt; rw [bump_val_ne s k (Finset.ne_of_mem_erase hj)]
  rw [this]; ring

/-- The potential of arm `i`: `(1/η) log W + c_i = (1/η) log (W / w_i)`. -/
noncomputable def Φ (η : ℝ) (i : Fin n) (s : St n K) : ℝ := (1 / η) * Real.log (W η s) + ((s i : ℕ) : ℝ)

lemma Φ_nonneg {η : ℝ} (hη : 0 < η) (i : Fin n) (s : St n K) : 0 ≤ Φ η i s := by
  unfold Φ
  have h1 : wt η s i ≤ W η s :=
    Finset.single_le_sum (fun j _ => (wt_pos η s j).le) (Finset.mem_univ i)
  have h2 : Real.log (wt η s i) ≤ Real.log (W η s) := Real.log_le_log (wt_pos η s i) h1
  have h3 : Real.log (wt η s i) = -η * ((s i : ℕ) : ℝ) := by unfold wt; rw [Real.log_exp]
  rw [h3] at h2
  have h4 := mul_le_mul_of_nonneg_left h2 (one_div_pos.2 hη).le
  have h5 : (1 / η) * (-η * ((s i : ℕ) : ℝ)) = -((s i : ℕ) : ℝ) := by field_simp
  linarith

lemma W_le (η : ℝ) (hη : 0 ≤ η) (s : St n K) : W η s ≤ n := by
  unfold W
  calc ∑ i, wt η s i ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
        unfold wt; rw [Real.exp_le_one_iff, neg_mul, neg_nonpos]
        exact mul_nonneg hη (Nat.cast_nonneg _)
    _ = n := by simp

lemma Φ_le {η : ℝ} (hη : 0 < η) (i : Fin n) (s : St n K) : Φ η i s ≤ (1 / η) * Real.log n + K := by
  unfold Φ
  have h1 : Real.log (W η s) ≤ Real.log n := Real.log_le_log (W_pos η s) (W_le η hη.le s)
  have h2 : ((s i : ℕ) : ℝ) ≤ K := by exact_mod_cast Nat.lt_succ_iff.1 (s i).isLt
  have := mul_le_mul_of_nonneg_left h1 (le_of_lt (one_div_pos.2 hη))
  linarith

/-- The one-step potential inequality for a non-saturating bump by `k`. -/
lemma Φ_bump_le {η : ℝ} (hη : 0 < η) (i : Fin n) {s : St n K} {a : Fin n} {k : ℕ}
    (hk : (s a : ℕ) + k ≤ K) :
    Φ η i (bump s a k) ≤ Φ η i s - q η s a * k + η * q η s a * (k : ℝ) ^ 2 / 2 +
      (if i = a then (k : ℝ) else 0) := by
  have hW := W_pos η s
  have hq : q η s a = wt η s a / W η s := rfl
  have hWb : W η (bump s a k) = W η s * (1 - q η s a * (1 - exp (-η * k))) := by
    rw [W_bump η hk, hq]; field_simp; ring
  have hWb_pos : 0 < W η (bump s a k) := W_pos η _
  -- log step
  have hlog : Real.log (W η (bump s a k)) - Real.log (W η s) ≤ -(q η s a * (1 - exp (-η * k))) := by
    rw [← Real.log_div hWb_pos.ne' hW.ne']
    have hratio : W η (bump s a k) / W η s = 1 - q η s a * (1 - exp (-η * k)) := by
      rw [hWb]; field_simp
    have := Real.log_le_sub_one_of_pos (div_pos hWb_pos hW)
    rw [hratio] at this ⊢
    linarith
  have hexp : exp (-(η * k)) ≤ 1 - η * k + (η * k) ^ 2 / 2 :=
    Pool.P0009.exp_neg_le_quadratic (by positivity)
  have hq0 := q_nonneg η s a
  have hci : ((bump s a k i : Fin (K + 1)) : ℕ) = (s i : ℕ) + (if i = a then k else 0) := by
    by_cases h : i = a
    · subst h; simp [bump_val_self hk]
    · simp [bump_val_ne s k h, h]
  unfold Φ
  rw [hci]
  push_cast
  have key : (1 / η) * Real.log (W η (bump s a k)) ≤ (1 / η) * Real.log (W η s) -
      q η s a * k + η * q η s a * (k : ℝ) ^ 2 / 2 := by
    have h1 : Real.log (W η (bump s a k)) ≤ Real.log (W η s) - (q η s a * (η * k - (η * k) ^ 2 / 2)) := by
      have : q η s a * (η * k - (η * k) ^ 2 / 2) ≤ q η s a * (1 - exp (-η * k)) := by
        apply mul_le_mul_of_nonneg_left _ hq0
        rw [neg_mul] ; linarith
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (one_div_pos.2 hη))
    calc (1 / η) * Real.log (W η (bump s a k))
        ≤ (1 / η) * (Real.log (W η s) - q η s a * (η * k - (η * k) ^ 2 / 2)) := h2
      _ = (1 / η) * Real.log (W η s) - q η s a * k + η * q η s a * (k : ℝ) ^ 2 / 2 := by
          field_simp; ring
  split_ifs <;> push_cast <;> linarith

end analysis

section step

variable [NeZero n] {K : ℕ} {η γ : ℝ}

lemma toReal_act (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (s : St n K) (a : Fin n) :
    ((actPMF (η := η) hγ0 hγ1 s) a).toReal = p η γ s a := by
  simp only [actPMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (p_pos hγ0 hγ1 s a).le

lemma iw_pos (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (s : St n K) (a : Fin n) : 0 < iw η γ s a :=
  one_div_pos.2 (p_pos hγ0 hγ1 s a)

lemma p_mul_iw (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (s : St n K) (a : Fin n) :
    p η γ s a * iw η γ s a = 1 := by
  unfold iw; field_simp [(p_pos hγ0 hγ1 s a).ne']

lemma frac_coe {y : ℝ} (hy : 0 ≤ y) : (((y - ⌊y⌋₊ : ℝ).toNNReal : ℝ≥0) : ℝ) = y - ⌊y⌋₊ :=
  Real.coe_toNNReal _ (by linarith [Nat.floor_le hy])

/-- The extra term in the expected potential after a loss-`1` pull of arm `a`. -/
noncomputable def X (η γ : ℝ) (i : Fin n) (s : St n K) (a : Fin n) : ℝ :=
  -(q η s a * iw η γ s a) + η * q η s a * (iw η γ s a ^ 2 + 1) / 2 +
    (if i = a then iw η γ s a else 0)

lemma pexp_next_le (hη : 0 < η) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (i : Fin n) (s : St n K) (a : Fin n)
    (hK : (s a : ℕ) + ⌊iw η γ s a⌋₊ + 1 ≤ K) (b : Bool) :
    pexp (nextPMF η γ s a b) (Φ η i) ≤ Φ η i s + (b.toNat : ℝ) * X η γ i s a := by
  cases b with
  | false =>
    simp only [nextPMF, Bool.false_eq_true, if_false, Bool.toNat_false, Nat.cast_zero, zero_mul,
      add_zero]
    exact (pexp_pure s _).le
  | true =>
    simp only [nextPMF, if_true, Bool.toNat_true, Nat.cast_one, one_mul]
    rw [pexp_map, pexp_bernoulli]
    set y := iw η γ s a with hy
    have hy0 : 0 < y := iw_pos hγ0 hγ1 s a
    set k0 := ⌊y⌋₊ with hk0
    rw [frac_coe hy0.le]
    simp only [Bool.toNat_true, Bool.toNat_false, add_zero]
    have h1 := Φ_bump_le hη i (s := s) (a := a) (k := k0 + 1) (by omega)
    have h0 := Φ_bump_le hη i (s := s) (a := a) (k := k0) (by omega)
    have hfl : (k0 : ℝ) ≤ y := Nat.floor_le hy0.le
    have hfl2 : y < k0 + 1 := Nat.lt_floor_add_one y
    set fr := y - k0 with hfr
    have hfr0 : 0 ≤ fr := by linarith
    have hfr1 : fr ≤ 1 := by linarith
    have hq0 := q_nonneg η s a
    have e1 := mul_le_mul_of_nonneg_left h1 hfr0
    have e0 := mul_le_mul_of_nonneg_left h0 (by linarith : (0:ℝ) ≤ 1 - fr)
    unfold X
    push_cast at e1 e0
    have hyk : y = k0 + fr := by rw [hfr]; ring
    have hηq : 0 ≤ η * q η s a := mul_nonneg hη.le hq0
    have hsq : (k0 : ℝ) ^ 2 + fr * (2 * k0 + 1) ≤ y ^ 2 + 1 := by
      rw [hyk]; nlinarith
    split_ifs at e1 e0 ⊢ with hia
    · have : fr * (Φ η i s - q η s a * (↑k0 + 1) + η * q η s a * (↑k0 + 1) ^ 2 / 2 + (↑k0 + 1)) +
          (1 - fr) * (Φ η i s - q η s a * ↑k0 + η * q η s a * ↑k0 ^ 2 / 2 + ↑k0) =
          Φ η i s - q η s a * y + η * q η s a * (k0 ^ 2 + fr * (2 * k0 + 1)) / 2 + y := by
        rw [hyk]; ring
      nlinarith
    · have : fr * (Φ η i s - q η s a * (↑k0 + 1) + η * q η s a * (↑k0 + 1) ^ 2 / 2 + 0) +
          (1 - fr) * (Φ η i s - q η s a * ↑k0 + η * q η s a * ↑k0 ^ 2 / 2 + 0) =
          Φ η i s - q η s a * y + η * q η s a * (k0 ^ 2 + fr * (2 * k0 + 1)) / 2 := by
        rw [hyk]; ring
      nlinarith

lemma p_le_one (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (s : St n K) (a : Fin n) : p η γ s a ≤ 1 := by
  rw [← sum_p η γ s]
  exact Finset.single_le_sum (fun j _ => (p_pos hγ0 hγ1 s j).le) (Finset.mem_univ a)

/-- Per-arm bound on the drift term. -/
lemma arm_term_le (hη : 0 < η) (hγ0 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (i : Fin n) (s : St n K)
    (a : Fin n) (b : Bool) :
    p η γ s a * ((b.toNat : ℝ) * X η γ i s a) ≤
      -(p η γ s a * (b.toNat : ℝ)) + (if i = a then (b.toNat : ℝ) else 0) +
        (γ / n + η * (2 + q η s a) / 2) := by
  have hγ1 : γ ≤ 1 := by linarith
  have hp := p_pos (η := η) hγ0 hγ1 s a
  have hp1 := p_le_one (η := η) hγ0 hγ1 s a
  have hq0 := q_nonneg η s a
  have hn := n_pos (n := n)
  have hγn : 0 < γ / n := div_pos hγ0 hn
  have hpiw := p_mul_iw (η := η) hγ0 hγ1 s a
  have hiw : iw η γ s a = 1 / p η γ s a := rfl
  -- p ≥ q / 2
  have hpq : q η s a ≤ 2 * p η γ s a := by
    unfold p; nlinarith [div_pos hγ0 hn]
  have hqiw : q η s a * iw η γ s a ≤ 2 := by
    rw [hiw, mul_one_div, div_le_iff₀ hp]; linarith
  have hpXa : p η γ s a * X η γ i s a = -q η s a + η * q η s a * (iw η γ s a + p η γ s a) / 2 +
      (if i = a then 1 else 0) := by
    unfold X
    have h2 : p η γ s a * iw η γ s a ^ 2 = iw η γ s a := by
      rw [pow_two, ← mul_assoc, hpiw, one_mul]
    split_ifs
    · have : p η γ s a * (-(q η s a * iw η γ s a) + η * q η s a * (iw η γ s a ^ 2 + 1) / 2 +
          iw η γ s a) = -(q η s a) * (p η γ s a * iw η γ s a) + η * q η s a *
          (p η γ s a * iw η γ s a ^ 2 + p η γ s a) / 2 + p η γ s a * iw η γ s a := by ring
      rw [this, h2, hpiw]; ring
    · have : p η γ s a * (-(q η s a * iw η γ s a) + η * q η s a * (iw η γ s a ^ 2 + 1) / 2 +
          0) = -(q η s a) * (p η γ s a * iw η γ s a) + η * q η s a *
          (p η γ s a * iw η γ s a ^ 2 + p η γ s a) / 2 := by ring
      rw [this, h2, hpiw]; ring
  have hpmq : p η γ s a - q η s a ≤ γ / n := by
    unfold p; nlinarith
  have hqp : q η s a * p η γ s a ≤ q η s a := mul_le_of_le_one_right hq0 hp1
  cases b with
  | false =>
    simp only [Bool.toNat_false, Nat.cast_zero, zero_mul, mul_zero, neg_zero, zero_add]
    split_ifs <;> nlinarith
  | true =>
    simp only [Bool.toNat_true, Nat.cast_one, one_mul, mul_one]
    rw [hpXa]
    have : η * q η s a * (iw η γ s a + p η γ s a) / 2 ≤ η * (2 + q η s a) / 2 := by
      have : q η s a * (iw η γ s a + p η γ s a) ≤ 2 + q η s a := by nlinarith
      have := mul_le_mul_of_nonneg_left this hη.le
      nlinarith
    split_ifs <;> linarith

/-- The one-step EXP3 inequality, in the form required by `Pool.P0012`. -/
lemma step_le (hη : 0 < η) (hγ0 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (i : Fin n) (s : St n K)
    (b : Fin n → Bool) (hK : ∀ a, (s a : ℕ) + ⌊iw η γ s a⌋₊ + 1 ≤ K) :
    pexp (actPMF (η := η) hγ0 (by linarith) s) (fun a => pexp (nextPMF η γ s a (b a)) (Φ η i)) ≤
      Φ η i s - ∑ a, ((actPMF (η := η) hγ0 (by linarith) s) a).toReal * ((b a).toNat : ℝ) +
        ((b i).toNat : ℝ) + (γ + η * (2 * n + 1) / 2) := by
  have hγ1 : γ ≤ 1 := by linarith
  calc pexp (actPMF (η := η) hγ0 hγ1 s) (fun a => pexp (nextPMF η γ s a (b a)) (Φ η i))
      ≤ pexp (actPMF (η := η) hγ0 hγ1 s) (fun a => Φ η i s + ((b a).toNat : ℝ) * X η γ i s a) :=
        pexp_mono _ fun a _ => pexp_next_le hη hγ0 hγ1 i s a (hK a) (b a)
    _ = Φ η i s + ∑ a, p η γ s a * (((b a).toNat : ℝ) * X η γ i s a) := by
        rw [pexp_add, pexp_const]
        unfold pexp
        simp only [toReal_act]
    _ ≤ Φ η i s + ∑ a, (-(p η γ s a * ((b a).toNat : ℝ)) + (if i = a then ((b a).toNat : ℝ) else 0) +
          (γ / n + η * (2 + q η s a) / 2)) := by
        gcongr with a
        exact arm_term_le hη hγ0 hγ2 i s a (b a)
    _ = Φ η i s - ∑ a, ((actPMF (η := η) hγ0 hγ1 s) a).toReal * ((b a).toNat : ℝ) +
          ((b i).toNat : ℝ) + (γ + η * (2 * n + 1) / 2) := by
        simp only [toReal_act]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
          Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib, sum_q, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hn := (n_pos (n := n)).ne'
        field_simp
        ring

end step

/-! ### Parameters and the regret bound -/

section main

variable (n : ℕ) [NeZero n] (T : ℕ)

/-- Exploration rate `γ = 1/(2T+2) ≤ 1/2`. -/
noncomputable def gam : ℝ := 1 / (2 * T + 2)

/-- Learning rate. -/
noncomputable def eta : ℝ := Real.sqrt ((1 + Real.log n) / ((2 * n + 1) * (T + 1)))

/-- Bound on one counter increment. -/
def Dinc : ℕ := n * (2 * T + 2) + 1

/-- Counter capacity: never reached before round `T`. -/
def Kcap : ℕ := T * Dinc n T

lemma gam_pos : 0 < gam T := by unfold gam; positivity
lemma gam_le : gam T ≤ 1 / 2 := by
  unfold gam; rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [(T.cast_nonneg : (0:ℝ) ≤ T)]
lemma gam_le_one : gam T ≤ 1 := (gam_le T).trans (by norm_num)

lemma eta_pos : 0 < eta n T := by
  unfold eta
  have : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
  positivity

/-- **EXP3 with finite-precision counters** on `n` arms and horizon `T`. -/
noncomputable def exp3M : Machine n :=
  exp3 n (eta n T) (gam T) (gam_pos T) (gam_le_one T) (Kcap n T)

variable {n T}

lemma floor_iw_le (s : St n (Kcap n T)) (a : Fin n) :
    ⌊iw (eta n T) (gam T) s a⌋₊ ≤ n * (2 * T + 2) := by
  apply Nat.floor_le_of_le
  have hp := p_pos (η := eta n T) (gam_pos T) (gam_le_one T) s a
  have hpl : gam T / n ≤ p (eta n T) (gam T) s a := by
    unfold p; nlinarith [q_nonneg (eta n T) s a, gam_le_one T]
  have hn := n_pos (n := n)
  unfold iw
  rw [div_le_iff₀ hp]
  have : gam T / n * ((n * (2 * T + 2) : ℕ) : ℝ) = 1 := by
    unfold gam; push_cast; field_simp
  calc (1 : ℝ) = gam T / n * ((n * (2 * T + 2) : ℕ) : ℝ) := this.symm
    _ ≤ p (eta n T) (gam T) s a * ((n * (2 * T + 2) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hpl (Nat.cast_nonneg _)
    _ = _ := by push_cast; ring

/-- Counters stay below `t · Dinc` up to round `T`. -/
def Good (t : ℕ) (s : St n (Kcap n T)) : Prop := t ≤ T → ∀ j, (s j : ℕ) ≤ t * Dinc n T

lemma good_reachable (ℓ : LossSeq n) (t : ℕ) (s : (exp3M n T).State)
    (hs : (exp3M n T).stateDist ℓ t s ≠ 0) : Good (T := T) t s := by
  refine stateDist_support_of_invariant (exp3M n T) ℓ (fun t s => Good (T := T) t s)
    ?_ ?_ t s hs
  · intro s hs _ j
    have h1 : s ∈ (PMF.pure (fun _ => (0 : Fin (Kcap n T + 1))) : PMF (St n (Kcap n T))).support :=
      (PMF.mem_support_iff _ _).2 hs
    have h2 : s = fun _ => 0 := (PMF.mem_support_pure_iff _ _).1 h1
    subst h2; simp
  · intro t s hgood a _ s' hs' ht j
    have hgt := hgood (by omega)
    change nextPMF _ _ s a (ℓ t a) s' ≠ 0 at hs'
    unfold nextPMF at hs'
    split_ifs at hs'
    · have h1 := (PMF.mem_support_iff _ _).2 hs'
      obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 h1
      have hfl := floor_iw_le (n := n) (T := T) s a
      by_cases hja : j = a
      · subst hja
        have h1 := bump_val_self_le (K := Kcap n T) s j (⌊iw (eta n T) (gam T) s j⌋₊ + c.toNat)
        have := hgt j
        have hc : c.toNat ≤ 1 := by cases c <;> simp
        unfold Dinc at *
        calc _ ≤ (s j : ℕ) + (⌊iw (eta n T) (gam T) s j⌋₊ + c.toNat) := h1
          _ ≤ t * (n * (2 * T + 2) + 1) + (n * (2 * T + 2) + 1) := by omega
          _ = (t + 1) * (n * (2 * T + 2) + 1) := by ring
      · rw [bump_val_ne s _ hja]
        have := hgt j
        calc (s j : ℕ) ≤ t * Dinc n T := this
          _ ≤ (t + 1) * Dinc n T := Nat.mul_le_mul_right _ (by omega)
    · have h1 := (PMF.mem_support_iff _ _).2 hs'
      have h2 : s' = s := (PMF.mem_support_pure_iff _ _).1 h1
      rw [h2]
      calc (s j : ℕ) ≤ t * Dinc n T := hgt j
        _ ≤ (t + 1) * Dinc n T := Nat.mul_le_mul_right _ (by omega)

/-- On a good state before the horizon, no bump saturates. -/
lemma noSat_of_good {t : ℕ} (ht : t < T) {s : St n (Kcap n T)} (hg : Good (T := T) t s) (a : Fin n) :
    (s a : ℕ) + ⌊iw (eta n T) (gam T) s a⌋₊ + 1 ≤ Kcap n T := by
  have h1 := hg ht.le a
  have h2 := floor_iw_le (n := n) (T := T) s a
  unfold Kcap
  calc (s a : ℕ) + ⌊iw (eta n T) (gam T) s a⌋₊ + 1 ≤ t * Dinc n T + Dinc n T := by
        unfold Dinc at *; omega
    _ = (t + 1) * Dinc n T := by ring
    _ ≤ T * Dinc n T := Nat.mul_le_mul_right _ ht

end main

section theorems

variable {n : ℕ} [NeZero n] {T : ℕ}

/-- The drift constant `δ = γ + η (2n+1)/2`. -/
noncomputable def δc (n T : ℕ) : ℝ := gam T + eta n T * (2 * n + 1) / 2

lemma stateLoss_le_one (ℓ : LossSeq n) (t : ℕ) (s : (exp3M n T).State) :
    Pool.P0012.stateLoss (exp3M n T) ℓ t s ≤ 1 := by
  unfold Pool.P0012.stateLoss
  calc ∑ a, ((exp3M n T).act t s a).toReal * ((ℓ t a).toNat : ℝ) ≤ ∑ a, ((exp3M n T).act t s a).toReal :=
        Finset.sum_le_sum fun a _ => mul_le_of_le_one_right ENNReal.toReal_nonneg
          (by cases ℓ t a <;> simp)
    _ = 1 := pexp_toReal_sum _

theorem exp3M_regret_le (ℓ : LossSeq n) :
    regret (exp3M n T) ℓ T ≤ (1 / eta n T) * Real.log n + T * δc n T := by
  have hη := eta_pos n T
  set Gbig : ℝ := (1 / eta n T) * Real.log n + Kcap n T + 1
  let Cond : St n (Kcap n T) → Prop := fun s => ∀ a, (s a : ℕ) + ⌊iw (eta n T) (gam T) s a⌋₊ + 1 ≤ Kcap n T
  classical
  refine Pool.P0012.regret_le_of_potential (exp3M n T) ℓ (fun i _ s => Φ (eta n T) i s)
    (fun _ _ s => if Cond s then δc n T else Gbig) T _ (fun i s => Φ_nonneg hη i s) ?_ ?_
  · intro i t _ s
    by_cases hc : Cond s
    · simp only [hc, if_true]
      exact step_le hη (gam_pos T) (gam_le T) i s (ℓ t) hc
    · simp only [hc, if_false]
      have hup : Pool.P0012.stepExp (exp3M n T) ℓ t s (Φ (eta n T) i) ≤
          (1 / eta n T) * Real.log n + Kcap n T := by
        change pexp (actPMF (η := eta n T) (gam_pos T) (gam_le_one T) s)
          (fun a => pexp (nextPMF (eta n T) (gam T) s a (ℓ t a)) (Φ (eta n T) i)) ≤ _
        calc _ ≤ pexp (actPMF (η := eta n T) (gam_pos T) (gam_le_one T) s)
              (fun _ => (1 / eta n T) * Real.log n + Kcap n T) :=
              pexp_mono _ fun a _ => (pexp_mono _ fun s' _ => Φ_le hη i s').trans
                (pexp_const _ _).le
          _ = _ := pexp_const _ _
      have h1 := stateLoss_le_one (T := T) ℓ t s
      have h2 := Φ_nonneg hη i s
      have h3 : (0 : ℝ) ≤ ((ℓ t i).toNat : ℝ) := Nat.cast_nonneg _
      linarith
  · intro i
    have h0 : Pool.P0012.expect (exp3M n T) ℓ 0 (Φ (eta n T) i) = (1 / eta n T) * Real.log n := by
      change pexp (PMF.pure fun _ => (0 : Fin (Kcap n T + 1))) (Φ (eta n T) i) = _
      rw [pexp_pure]
      simp [Φ, W, wt]
    have ht : ∀ t ∈ Finset.range T, Pool.P0012.expect (exp3M n T) ℓ t
        (fun s => if Cond s then δc n T else Gbig) = δc n T := by
      intro t ht
      have ht' := Finset.mem_range.1 ht
      change pexp ((exp3M n T).stateDist ℓ t) _ = _
      rw [pexp_congr _ (g := fun _ => δc n T) fun s hs => by
        have hc : Cond s := fun a => noSat_of_good ht' (good_reachable ℓ t s hs) a
        simp only [hc, if_true]]
      exact pexp_const _ _
    rw [h0, Finset.sum_congr rfl ht, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Closed form: `regret ≤ (3/2) √((1 + log n)(2n+1)(T+1)) + 1/2`. -/
theorem exp3M_regret_le_sqrt (ℓ : LossSeq n) :
    regret (exp3M n T) ℓ T ≤
      3 / 2 * Real.sqrt ((1 + Real.log n) * ((2 * n + 1) * (T + 1))) + 1 / 2 := by
  refine (exp3M_regret_le ℓ).trans ?_
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
  set A : ℝ := 1 + Real.log n with hA
  set Bc : ℝ := (2 * n + 1) * (T + 1) with hBc
  have hA0 : 0 < A := by rw [hA]; linarith
  have hB0 : 0 < Bc := by rw [hBc]; positivity
  have hη := eta_pos n T
  set S : ℝ := Real.sqrt (A * Bc) with hS
  have hηdef : eta n T = Real.sqrt (A / Bc) := rfl
  have hη2 : eta n T ^ 2 = A / Bc := by rw [hηdef]; exact Real.sq_sqrt (div_nonneg hA0.le hB0.le)
  have hηB : eta n T * Bc = S := by
    rw [hS, ← Real.sqrt_sq (mul_nonneg hη.le hB0.le)]
    congr 1
    rw [mul_pow, hη2]; field_simp
  have hSpos : 0 < S := by rw [hS]; positivity
  have h1 : (1 / eta n T) * Real.log n ≤ S := by
    have : (1 / eta n T) * Real.log n ≤ A / eta n T := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right (by rw [hA]; linarith) hη.le
    have hAS : A = S * eta n T := by
      rw [← hηB]
      have : eta n T * Bc * eta n T = eta n T ^ 2 * Bc := by ring
      rw [this, hη2]; field_simp
    have h' : A / eta n T = S := by rw [hAS]; field_simp
    linarith
  have h2 : (T : ℝ) * (eta n T * (2 * n + 1) / 2) ≤ S / 2 := by
    have : (T : ℝ) * (eta n T * (2 * n + 1)) ≤ eta n T * Bc := by
      rw [hBc]; nlinarith [hη, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [hηB] at this; linarith
  have h3 : (T : ℝ) * gam T ≤ 1 / 2 := by
    unfold gam; rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  unfold δc
  nlinarith

/-- Memory of the EXP3 machine: `n · log₂ (Kcap + 1)` bits, `Kcap = T (n(2T+2)+1)`. -/
theorem exp3M_memBits : (exp3M n T).memBits = n * Real.logb 2 (Kcap n T + 1) := by
  unfold Machine.memBits
  change Real.logb 2 (Fintype.card (St n (Kcap n T))) = _
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  push_cast
  rw [Real.logb_pow]

theorem exp3M_isHomogeneous : (exp3M n T).IsHomogeneous := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- The EXP3 family: `exp3M n T` for every `n ≥ 1` and `T`. -/
noncomputable def exp3Family : Family := fun n T hn =>
  haveI : NeZero n := NeZero.of_pos hn
  exp3M n T

theorem exp3Family_regretBound : RegretBound exp3Family fun n T =>
    3 / 2 * Real.sqrt ((1 + Real.log n) * ((2 * n + 1) * (T + 1))) + 1 / 2 := by
  intro n T hn _ ℓ
  have : NeZero n := NeZero.of_pos hn
  exact exp3M_regret_le_sqrt ℓ

theorem exp3Family_memBits (n T : ℕ) (hn : 1 ≤ n) :
    (exp3Family n T hn).memBits = n * Real.logb 2 (T * (n * (2 * T + 2) + 1) + 1) := by
  have : NeZero n := NeZero.of_pos hn
  change (exp3M n T).memBits = _
  rw [exp3M_memBits]
  unfold Kcap Dinc
  push_cast
  ring_nf

theorem exp3Family_isHomogeneous (n T : ℕ) (hn : 1 ≤ n) : (exp3Family n T hn).IsHomogeneous :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

end theorems

end Pool.P0018
