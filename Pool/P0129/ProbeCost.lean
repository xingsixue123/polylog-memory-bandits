import Pool.P0092.Azuma

/-!
# Probing-cost identity (P0014 §3.1) and the stopped-gap bound behind P0117 §1, in the coin model of P0092

Coins `ω : Fin t → Z` are i.i.d. with law `ν` (weights `Pool.P0092.wgt`). A **probe** (`Pool.P0129.Probe`) has
* `alive s ω'`: whether it is alive in round `s`, read on the coins `ω'` of the rounds `< s` (predictable);
* `g s ω'`: its gap in round `s` against the algorithm's play (e.g. `ℓ_s(probe) − ⟨p_s, ℓ_s⟩`), also predictable;
* `hit s ω' z`: the coin event of round `s` on which the probe is played (its slot round). It may depend on the
  round and on the earlier coins `ω'` (a slot that moves with the state); `Pool.P0129.HasRate ν P x` asks that its
  `ν`-mass be `x` after every past (constant rate).

* `Pool.P0129.ag`: the gap on alive rounds; `Pool.P0129.pc`: the probing cost, the gap on alive rounds whose coin hits.
* **`Pool.P0129.probe_cost_identity`**: `E[Σ pc] = x · E[Σ ag]` (P0014 §3.1). The probe is charged `x` times its
  whole alive gap, not `x` per alive round.
* **`Pool.P0129.runSum_ag_le`**: on a prefix-closed good event, if the alive gap stays `≤ Ψ` while alive (`Ψ`
  nondecreasing along extensions, gaps `≤ 1`), the total alive gap is `≤ Ψ + 1`.
* **`Pool.P0129.probe_cost_le`**: `E[Σ pc] ≤ x · E[if good then Ψ_T + 1 else T]` (gaps `|g| ≤ 1`; the off-event
  term uses the horizon `T`, not the probe's lifetime).
* **`Pool.P0129.halive_of_rule`**: rule (b′) (P0117 §0: stay alive after round `t` only if the estimated gap is
  `< Λ`) plus an estimate within `W` of the true alive gap on the good event gives `runSum_ag_le`'s hypothesis with
  `Ψ ≥ Λ + W`.

Not done here: the good event's probability (concentration of the probe and ALG estimates, e.g. via P0100/P0115)
and any concrete design. Expectations are over all coins `Fin T → Z`; the probe's data may depend on every earlier
coin, so ALG's state and the probe's own history are allowed.
-/

open Finset Real
open scoped ENNReal

namespace Pool.P0129

open Pool.P0092

variable {Z : Type} [Fintype Z] (ν : PMF Z)

/-- Expectation over `t` i.i.d. coins with law `ν`. -/
noncomputable def expect (t : ℕ) (f : (Fin t → Z) → ℝ) : ℝ := ∑ ω : Fin t → Z, wgt ν ω * f ω

theorem expect_runSum_succ (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (t : ℕ) :
    expect ν (t + 1) (runSum D (t + 1)) =
      expect ν t (runSum D t) + ∑ ω' : Fin t → Z, wgt ν ω' * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) := by
  unfold expect
  rw [Pool.P0064.sum_split, Finset.sum_comm]
  have h1 : ∀ ω' : Fin t → Z, ∑ z, wgt ν (Fin.snoc ω' z) * runSum D (t + 1) (Fin.snoc ω' z) =
      wgt ν ω' * runSum D t ω' + wgt ν ω' * ∑ z, (ν z).toReal * D t (Fin.snoc ω' z) := by
    intro ω'
    simp only [runSum, Fin.init_snoc, wgt_snoc]
    rw [Finset.mul_sum]
    have : ∑ z, wgt ν ω' * (ν z).toReal * runSum D t ω' = wgt ν ω' * runSum D t ω' := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, sum_toReal_one ν, mul_one]
    rw [← this, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => by ring
  simp only [h1, Finset.sum_add_distrib]

/-- Increments of the form `A s (past) · h (current coin)` factor in expectation. -/
theorem expect_runSum_mul (A : (s : ℕ) → (Fin s → Z) → ℝ) (h : Z → ℝ) (t : ℕ) :
    expect ν t (runSum (fun s ω => A s (Fin.init ω) * h (ω (Fin.last s))) t) =
      (∑ z, (ν z).toReal * h z) * expect ν t (runSum (fun s ω => A s (Fin.init ω)) t) := by
  induction t with
  | zero => simp [expect, runSum]
  | succ t ih =>
    rw [expect_runSum_succ, expect_runSum_succ, ih, mul_add]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    simp only [Fin.init_snoc, Fin.snoc_last]
    rw [← Finset.sum_mul, sum_toReal_one ν]
    rw [Finset.sum_congr rfl (fun z _ => (mul_left_comm _ _ _ : (ν z).toReal * (A t ω' * h z) =
      A t ω' * ((ν z).toReal * h z))), ← Finset.mul_sum]
    ring

/-! ## The probe -/

/-- A probe: alive before round `s` (reads the coins of rounds `< s`), its per-round gap `g` against the
algorithm (also predictable), and the coin event `hit s ω' z` on which it is played in round `s`. The slot event may
depend on the round and on the earlier coins (e.g. a slot label that changes as items enter or leave); only the
current coin `z` must be fresh. -/
structure Probe (Z : Type) where
  alive : (s : ℕ) → (Fin s → Z) → Bool
  g : (s : ℕ) → (Fin s → Z) → ℝ
  hit : (s : ℕ) → (Fin s → Z) → Z → Bool

variable (P : Probe Z)

/-- Gap accrued on the alive rounds, round `s` read on the prefix of rounds `< s`. -/
noncomputable def ag (s : ℕ) (ω : Fin (s + 1) → Z) : ℝ :=
  if P.alive s (Fin.init ω) then P.g s (Fin.init ω) else 0

/-- Probing cost: the gap is paid only on alive rounds whose coin hits the probe's slot event. -/
noncomputable def pc (s : ℕ) (ω : Fin (s + 1) → Z) : ℝ :=
  ag P s ω * if P.hit s (Fin.init ω) (ω (Fin.last s)) then 1 else 0

/-- The slot event has `ν`-mass `x` in every round and after every past (constant rate `x`, with a slot event
that may move with the state). -/
def HasRate (x : ℝ) : Prop :=
  ∀ s (ω' : Fin s → Z), ∑ z, (ν z).toReal * (if P.hit s ω' z then 1 else 0) = x

theorem HasRate.nonneg {x : ℝ} (hx : HasRate ν P x) : 0 ≤ x := by
  rw [← hx 0 Fin.elim0]
  exact Finset.sum_nonneg fun z _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)

/-- **Probing-cost identity** (P0014 §3.1): `E[probing cost] = x · E[gap on alive rounds]`, for a slot event of
mass `x` after every past. -/
theorem probe_cost_identity {x : ℝ} (hx : HasRate ν P x) (T : ℕ) :
    expect ν T (runSum (pc P) T) = x * expect ν T (runSum (ag P) T) := by
  induction T with
  | zero => simp [expect, runSum]
  | succ t ih =>
    rw [expect_runSum_succ, expect_runSum_succ, ih, mul_add]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    have hag : ∀ z, ag P t (Fin.snoc ω' z) = if P.alive t ω' then P.g t ω' else 0 := by
      intro z; simp only [ag, Fin.init_snoc]
    simp only [pc, hag, Fin.init_snoc, Fin.snoc_last]
    rw [← Finset.sum_mul, sum_toReal_one ν, one_mul]
    have : ∑ z, (ν z).toReal * ((if P.alive t ω' then P.g t ω' else 0) * if P.hit t ω' z then 1 else 0) =
        (if P.alive t ω' then P.g t ω' else 0) * x := by
      rw [← hx t ω', Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [this]; ring

/-! ## The stopped-gap bound -/

omit [Fintype Z] in
/-- If, on a prefix-closed good event, the alive gap stays `≤ Ψ` while the probe is alive, with `Ψ`
nondecreasing along extensions and per-round gaps `≤ 1`, then the total alive gap is `≤ Ψ + 1` on the event. -/
theorem runSum_ag_le (G : (t : ℕ) → (Fin t → Z) → Prop) (Ψ : (t : ℕ) → (Fin t → Z) → ℝ)
    (hG : ∀ t (ω : Fin t → Z) z, G (t + 1) (Fin.snoc ω z) → G t ω)
    (hΨ : ∀ t (ω : Fin t → Z) z, Ψ t ω ≤ Ψ (t + 1) (Fin.snoc ω z))
    (hΨ0 : ∀ ω : Fin 0 → Z, 0 ≤ Ψ 0 ω + 1)
    (halive : ∀ t (ω : Fin t → Z), G t ω → P.alive t ω → runSum (ag P) t ω ≤ Ψ t ω)
    (hg : ∀ t (ω : Fin t → Z), P.g t ω ≤ 1) :
    ∀ t (ω : Fin t → Z), G t ω → runSum (ag P) t ω ≤ Ψ t ω + 1 := by
  intro t
  induction t with
  | zero => intro ω _; simpa [runSum] using hΨ0 ω
  | succ t ih =>
    intro ω hω
    rw [← Fin.snoc_init_self ω] at hω ⊢
    have hω' := hG t _ _ hω
    have hmono := hΨ t (Fin.init ω) (ω (Fin.last t))
    simp only [runSum, Fin.init_snoc, ag]
    split_ifs with ha
    · have := halive t _ hω' ha
      have := hg t (Fin.init ω)
      linarith
    · have := ih _ hω'
      linarith

omit [Fintype Z] in
theorem abs_runSum_ag_le (hg : ∀ t (ω : Fin t → Z), |P.g t ω| ≤ 1) :
    ∀ t (ω : Fin t → Z), |runSum (ag P) t ω| ≤ t := by
  intro t
  induction t with
  | zero => intro ω; simp [runSum]
  | succ t ih =>
    intro ω
    simp only [runSum]
    have h1 : |ag P t ω| ≤ 1 := by
      unfold ag; split_ifs
      · exact hg _ _
      · simp
    calc |runSum (ag P) t (Fin.init ω) + ag P t ω| ≤ |runSum (ag P) t (Fin.init ω)| + |ag P t ω| :=
          abs_add_le _ _
      _ ≤ t + 1 := add_le_add (ih _) h1
      _ = ((t + 1 : ℕ) : ℝ) := by push_cast; ring

/-- **Expected probing cost.** On the good event the alive gap is `≤ Ψ + 1`; off it, `≤ T`. -/
theorem probe_cost_le {x : ℝ} (hx : HasRate ν P x) (T : ℕ) (G : (t : ℕ) → (Fin t → Z) → Prop) [∀ t ω, Decidable (G t ω)]
    (Ψ : (t : ℕ) → (Fin t → Z) → ℝ)
    (hG : ∀ t (ω : Fin t → Z) z, G (t + 1) (Fin.snoc ω z) → G t ω)
    (hΨ : ∀ t (ω : Fin t → Z) z, Ψ t ω ≤ Ψ (t + 1) (Fin.snoc ω z))
    (hΨ0 : ∀ ω : Fin 0 → Z, 0 ≤ Ψ 0 ω + 1)
    (halive : ∀ t (ω : Fin t → Z), G t ω → P.alive t ω → runSum (ag P) t ω ≤ Ψ t ω)
    (hg : ∀ t (ω : Fin t → Z), |P.g t ω| ≤ 1) :
    expect ν T (runSum (pc P) T) ≤
      x * expect ν T (fun ω => if G T ω then Ψ T ω + 1 else (T : ℝ)) := by
  rw [probe_cost_identity ν P hx]
  refine mul_le_mul_of_nonneg_left ?_ (hx.nonneg ν P)
  unfold expect
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
  dsimp only
  split_ifs with h
  · exact runSum_ag_le P G Ψ hG hΨ hΨ0 halive (fun t ω => (abs_le.mp (hg t ω)).2) T ω h
  · exact (abs_le.mp (abs_runSum_ag_le P hg T ω)).2

omit [Fintype Z] in
/-- **Rule (b′) gives the alive-gap hypothesis.** If the probe stays alive after round `t` only when its
estimated gap `est t` is below the threshold `Λ t`, the estimate is within `W t` of the true alive gap on the
good event, a probe that enters is fresh (never alive before), and `Λ + W ≤ Ψ` with `Ψ ≥ 0`, then the alive gap
is `≤ Ψ` whenever the probe is alive on the good event. -/
theorem halive_of_rule (G : (t : ℕ) → (Fin t → Z) → Prop) (Ψ : (t : ℕ) → (Fin t → Z) → ℝ)
    (est : (t : ℕ) → (Fin (t + 1) → Z) → ℝ) (Λ W : (t : ℕ) → (Fin t → Z) → ℝ)
    (hrule : ∀ t (ω : Fin t → Z) z, P.alive (t + 1) (Fin.snoc ω z) → P.alive t ω →
      est t (Fin.snoc ω z) < Λ t ω)
    (hfresh : ∀ t (ω : Fin t → Z) z, P.alive (t + 1) (Fin.snoc ω z) → ¬ P.alive t ω →
      runSum (ag P) t ω = 0)
    (hest : ∀ t (ω : Fin t → Z) z, G (t + 1) (Fin.snoc ω z) →
      runSum (ag P) (t + 1) (Fin.snoc ω z) ≤ est t (Fin.snoc ω z) + W t ω)
    (hΛW : ∀ t (ω : Fin t → Z) z, Λ t ω + W t ω ≤ Ψ (t + 1) (Fin.snoc ω z))
    (hΨnn : ∀ t (ω : Fin t → Z), 0 ≤ Ψ t ω) :
    ∀ t (ω : Fin t → Z), G t ω → P.alive t ω → runSum (ag P) t ω ≤ Ψ t ω := by
  intro t
  cases t with
  | zero => intro ω _ _; simpa [runSum] using hΨnn 0 ω
  | succ t =>
    intro ω hG ha
    rw [← Fin.snoc_init_self ω] at hG ha ⊢
    by_cases hp : P.alive t (Fin.init ω)
    · have h1 := hrule t _ _ ha hp
      have h2 := hest t _ _ hG
      have h3 := hΛW t (Fin.init ω) (ω (Fin.last t))
      linarith
    · have h0 := hfresh t _ _ ha hp
      have : runSum (ag P) (t + 1) (Fin.snoc (Fin.init ω) (ω (Fin.last t))) = 0 := by
        simp only [runSum, Fin.init_snoc, ag, if_neg hp, h0, add_zero]
      rw [this]; exact hΨnn _ _

end Pool.P0129
