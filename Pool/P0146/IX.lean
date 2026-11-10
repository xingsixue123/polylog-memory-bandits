import Pool.P0139.IntervalFreedman
import Pool.P0047.IX

/-!
# Implicit-exploration (IX) one-sided concentration in P0092's coin model, uniformly over intervals

Coins `ω : Fin t → Z` are i.i.d. with law `ν` (P0092). One item has a predictable loss `ℓ s ω' ∈ [0, 1]` and an
observation event `obs s ω' z` (e.g. "the exploitation learner plays this item in round `s`", "a BASE round
selects the BASE meta-arm"). Its observation probability is the event's `ν`-mass, `obsMass ν obs s ω'`, computed
here (no rate hypothesis). The IX estimate increment is `ℓ·1[obs]/(p + γ)` (`ixEst`), and the estimation error is
`ixErr = ℓ·1[obs]/(p + γ) − ℓ`.

* **`ix_one_step`**: `E[exp(2γ·ixErr)] ≤ 1` after every past (P0047's `ix_step` for `p > 0`, direct for `p = 0`).
* **`ix_expSum_le`**: `exp(2γ·Σ gated errors)` is a supermartingale for every gating (P0139's `gD`: rounds in
  `[a, b)` on which a predictable gate is on).
* **`ix_interval_tail`**: the gated overestimate over `[a, b)` is `≥ L/(2γ)` with probability `≤ e^{−L}`.
* **`IXGood`**, **`ixGood_prefix`**, **`prob_not_ixGood`**: the one-sided good event "every interval with
  `b ≤ t` has gated overestimate `< L/(2γ)`" is prefix-closed and fails at the horizon with probability
  `≤ (T+1)² e^{−L}`.
* **`ixEst_le_of_good`**: on that event, on every interval the item's gated IX estimate is below its gated true loss
  plus `L/(2γ)`. This is the one-sided bound used in the cover and (b″) certificates of P0108 §1 and P0136 §3
  (Neu 2015, Lemma 1, uniformly over intervals).

The bound is one-sided: IX estimates may underestimate by any amount (see the tests). The union over several
items is not done here.
-/

open Finset Real

namespace Pool.P0146

open Pool.P0092 Pool.P0139

variable {Z : Type} [Fintype Z] (ν : PMF Z)

/-- The `ν`-mass of the observation event of round `s` after the past `ω'`. -/
noncomputable def obsMass (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (s : ℕ) (ω' : Fin s → Z) : ℝ :=
  ∑ z, (ν z).toReal * (if obs s ω' z then 1 else 0)

/-- The IX estimation error of one item in round `s`: `ℓ·1[obs]/(p + γ) − ℓ`, with `p` the observation mass. -/
noncomputable def ixErr (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (γ : ℝ) :
    (s : ℕ) → (Fin (s + 1) → Z) → ℝ :=
  fun s ω => ℓ s (Fin.init ω) *
    (if obs s (Fin.init ω) (ω (Fin.last s)) then 1 / (obsMass ν obs s (Fin.init ω) + γ) else 0) - ℓ s (Fin.init ω)

theorem obsMass_nonneg (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (s : ℕ) (ω' : Fin s → Z) :
    0 ≤ obsMass ν obs s ω' :=
  Finset.sum_nonneg fun z _ => mul_nonneg ENNReal.toReal_nonneg (by split_ifs <;> norm_num)

theorem obsMass_le_one (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (s : ℕ) (ω' : Fin s → Z) :
    obsMass ν obs s ω' ≤ 1 := by
  calc obsMass ν obs s ω' ≤ ∑ z, (ν z).toReal * 1 :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (by split_ifs <;> norm_num) ENNReal.toReal_nonneg
    _ = 1 := by simp [sum_toReal_one ν]

/-- **One-step IX bound in the coin model:** `E[exp(2γ·ixErr)] ≤ 1`. -/
theorem ix_one_step (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) {γ : ℝ}
    (hγ : 0 < γ) (hℓ0 : ∀ s ω', 0 ≤ ℓ s ω') (hℓ1 : ∀ s ω', ℓ s ω' ≤ 1) (s : ℕ) (ω' : Fin s → Z) :
    ∑ z, (ν z).toReal * exp (2 * γ * ixErr ν ℓ obs γ s (Fin.snoc ω' z)) ≤ 1 := by
  obtain ⟨p, hp⟩ : ∃ p, p = obsMass ν obs s ω' := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l, l = ℓ s ω' := ⟨_, rfl⟩
  have hsplit : ∀ z, exp (2 * γ * ixErr ν ℓ obs γ s (Fin.snoc ω' z)) =
      exp (-(2 * γ * l)) * ((if obs s ω' z then exp (2 * γ * l / (p + γ)) else 1)) := by
    intro z
    simp only [ixErr, Fin.init_snoc, Fin.snoc_last, ← hp, ← hl]
    split_ifs
    · rw [← exp_add]; congr 1; field_simp; ring
    · rw [mul_one]; congr 1; ring
  simp only [hsplit]
  have hA : ∑ z, (ν z).toReal * (if obs s ω' z then exp (2 * γ * l / (p + γ)) else 1) =
      p * exp (2 * γ * l / (p + γ)) + (1 - p) := by
    have hz : ∀ z, (if obs s ω' z then exp (2 * γ * l / (p + γ)) else 1) =
        exp (2 * γ * l / (p + γ)) * (if obs s ω' z then 1 else 0) + (1 - (if obs s ω' z then 1 else 0)) := by
      intro z; split_ifs <;> ring
    simp only [hz, mul_add, mul_sub, mul_one, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_toReal_one ν]
    have h1 : ∑ z, (ν z).toReal * (if obs s ω' z then (1 : ℝ) else 0) = p := hp.symm
    have h2 : ∑ z, (ν z).toReal * (exp (2 * γ * l / (p + γ)) * (if obs s ω' z then (1 : ℝ) else 0)) =
        exp (2 * γ * l / (p + γ)) * p := by
      rw [← h1, Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring
    rw [h2, h1]; ring
  have hsum : ∑ z, (ν z).toReal * (exp (-(2 * γ * l)) * (if obs s ω' z then exp (2 * γ * l / (p + γ)) else 1)) =
      exp (-(2 * γ * l)) * (p * exp (2 * γ * l / (p + γ)) + (1 - p)) := by
    rw [← hA, Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring
  rw [hsum]
  have hp0 : 0 ≤ p := hp ▸ obsMass_nonneg ν obs s ω'
  have hp1 : p ≤ 1 := hp ▸ obsMass_le_one ν obs s ω'
  have hl0 : 0 ≤ l := hl ▸ hℓ0 s ω'
  have hl1 : l ≤ 1 := hl ▸ hℓ1 s ω'
  rcases hp0.lt_or_eq with hpos | hzero
  · have := Pool.P0047.ix_step hl0 hl1 hpos hp1 hγ
    calc exp (-(2 * γ * l)) * (p * exp (2 * γ * l / (p + γ)) + (1 - p))
        ≤ exp (-(2 * γ * l)) * exp (2 * γ * l) := mul_le_mul_of_nonneg_left this (exp_pos _).le
      _ = 1 := by rw [← exp_add]; simp
  · rw [← hzero]
    simp only [zero_mul, sub_zero, zero_add, mul_one]
    exact exp_le_one_iff.mpr (by nlinarith)

/-- **Exponential supermartingale** for any gating of the IX errors (gated rounds contribute `ixErr`, others `0`). -/
theorem ix_expSum_le (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) {γ : ℝ}
    (hγ : 0 < γ) (hℓ0 : ∀ s ω', 0 ≤ ℓ s ω') (hℓ1 : ∀ s ω', ℓ s ω' ≤ 1)
    (gate : (s : ℕ) → (Fin s → Z) → Bool) (a b : ℕ) :
    ∀ t, ∑ ω : Fin t → Z, wgt ν ω * exp (2 * γ * runSum (gD (ixErr ν ℓ obs γ) gate a b) t ω) ≤ 1 := by
  intro t
  induction t with
  | zero => simp [wgt, runSum]
  | succ t ih =>
    rw [Pool.P0064.sum_split, Finset.sum_comm]
    calc ∑ ω' : Fin t → Z, ∑ z, wgt ν (Fin.snoc ω' z) *
          exp (2 * γ * runSum (gD (ixErr ν ℓ obs γ) gate a b) (t + 1) (Fin.snoc ω' z))
        = ∑ ω' : Fin t → Z, wgt ν ω' * exp (2 * γ * runSum (gD (ixErr ν ℓ obs γ) gate a b) t ω') *
            ∑ z, (ν z).toReal * exp (2 * γ * gD (ixErr ν ℓ obs γ) gate a b t (Fin.snoc ω' z)) := by
          refine Finset.sum_congr rfl fun ω' _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          simp only [runSum, Fin.init_snoc, wgt_snoc]
          rw [mul_add, exp_add]; ring
      _ ≤ ∑ ω' : Fin t → Z, wgt ν ω' * exp (2 * γ * runSum (gD (ixErr ν ℓ obs γ) gate a b) t ω') * 1 := by
          refine Finset.sum_le_sum fun ω' _ => mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (wgt_nonneg ν ω') (exp_pos _).le)
          simp only [gD_snoc]
          split_ifs
          · exact ix_one_step ν ℓ obs hγ hℓ0 hℓ1 t ω'
          · simp [sum_toReal_one ν]
      _ ≤ 1 := by simpa using ih

/-- **One interval.** The gated IX overestimate over `[a, b)` is `≥ L/(2γ)` with probability `≤ e^{−L}`. -/
theorem ix_interval_tail (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) {γ : ℝ}
    (hγ : 0 < γ) (hℓ0 : ∀ s ω', 0 ≤ ℓ s ω') (hℓ1 : ∀ s ω', ℓ s ω' ≤ 1)
    (gate : (s : ℕ) → (Fin s → Z) → Bool) (a b T : ℕ) (L : ℝ) :
    probGe ν T (runSum (gD (ixErr ν ℓ obs γ) gate a b) T) (L / (2 * γ)) ≤ exp (-L) := by
  have hE := ix_expSum_le ν ℓ obs hγ hℓ0 hℓ1 gate a b T
  calc probGe ν T (runSum (gD (ixErr ν ℓ obs γ) gate a b) T) (L / (2 * γ))
      ≤ ∑ ω : Fin T → Z, wgt ν ω * exp (2 * γ * runSum (gD (ixErr ν ℓ obs γ) gate a b) T ω - L) := by
        unfold probGe
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
        split_ifs with h
        · apply one_le_exp
          rw [div_le_iff₀ (by positivity)] at h
          linarith
        · exact (exp_pos _).le
    _ = exp (-L) * ∑ ω : Fin T → Z, wgt ν ω * exp (2 * γ * runSum (gD (ixErr ν ℓ obs γ) gate a b) T ω) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [sub_eq_add_neg, exp_add]; ring
    _ ≤ exp (-L) * 1 := mul_le_mul_of_nonneg_left hE (exp_pos _).le
    _ = exp (-L) := mul_one _

/-- **The one-sided IX good event at time `t`**: on every interval `[a, b)` with `b ≤ t`, the gated IX overestimate
is `< L/(2γ)`. -/
def IXGood (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (γ : ℝ)
    (gate : (s : ℕ) → (Fin s → Z) → Bool) (L : ℝ) (t : ℕ) (ω : Fin t → Z) : Prop :=
  ∀ a b, a ≤ b → b ≤ t → runSum (gD (ixErr ν ℓ obs γ) gate a b) t ω < L / (2 * γ)

theorem ixGood_prefix (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (γ : ℝ)
    (gate : (s : ℕ) → (Fin s → Z) → Bool) (L : ℝ) (t : ℕ) (ω : Fin t → Z) (z : Z)
    (h : IXGood ν ℓ obs γ gate L (t + 1) (Fin.snoc ω z)) : IXGood ν ℓ obs γ gate L t ω := by
  intro a b hab hb
  have := h a b hab (by omega)
  rwa [runSum_gD_stable (ixErr ν ℓ obs γ) gate hb] at this

open Classical in
/-- **Union bound**: the one-sided IX good event fails at the horizon with probability `≤ (T+1)² e^{−L}`. -/
theorem prob_not_ixGood (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) {γ : ℝ}
    (hγ : 0 < γ) (hℓ0 : ∀ s ω', 0 ≤ ℓ s ω') (hℓ1 : ∀ s ω', ℓ s ω' ≤ 1)
    (gate : (s : ℕ) → (Fin s → Z) → Bool) (L : ℝ) (T : ℕ) :
    (∑ ω : Fin T → Z, wgt ν ω * if IXGood ν ℓ obs γ gate L T ω then (0 : ℝ) else 1) ≤
      ((T : ℝ) + 1) ^ 2 * exp (-L) := by
  set I : Finset (ℕ × ℕ) := ((Finset.range (T + 1)) ×ˢ (Finset.range (T + 1))).filter (fun p => p.1 ≤ p.2) with hI
  let f : ℕ × ℕ → (Fin T → Z) → ℝ := fun i ω =>
    runSum (gD (ixErr ν ℓ obs γ) gate i.1 i.2) T ω - L / (2 * γ)
  have hstep : (∑ ω : Fin T → Z, wgt ν ω * if IXGood ν ℓ obs γ gate L T ω then (0 : ℝ) else 1) ≤
      ∑ ω : Fin T → Z, wgt ν ω * if ∃ i ∈ I, (0 : ℝ) ≤ f i ω then 1 else 0 := by
    refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
    by_cases hg : IXGood ν ℓ obs γ gate L T ω
    · rw [if_pos hg]; split_ifs <;> norm_num
    by_cases hex : ∃ i ∈ I, (0 : ℝ) ≤ f i ω
    · rw [if_neg hg, if_pos hex]
    · exfalso; apply hex
      simp only [IXGood, not_forall, not_lt] at hg
      obtain ⟨a, b, hab, hbT, hw⟩ := hg
      refine ⟨(a, b), ?_, ?_⟩
      · simp only [hI, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega
      · simp only [f]; linarith
  refine le_trans hstep (le_trans (probGe_exists_le ν I f 0) ?_)
  have hone : ∀ i ∈ I, probGe ν T (f i) 0 ≤ exp (-L) := by
    intro i _
    refine le_trans (probGe_mono ν (fun ω h => ?_)) (ix_interval_tail ν ℓ obs hγ hℓ0 hℓ1 gate i.1 i.2 T L)
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

/-- The IX estimate increment of the item: `ℓ·1[obs]/(p + γ)`. -/
noncomputable def ixEst (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (γ : ℝ) :
    (s : ℕ) → (Fin (s + 1) → Z) → ℝ :=
  fun s ω => ℓ s (Fin.init ω) *
    (if obs s (Fin.init ω) (ω (Fin.last s)) then 1 / (obsMass ν obs s (Fin.init ω) + γ) else 0)

omit [Fintype Z] in
theorem runSum_sub (f g : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) :
    ∀ t (ω : Fin t → Z), runSum (fun s ω => f s ω - g s ω) t ω = runSum f t ω - runSum g t ω := by
  intro t
  induction t with
  | zero => intro ω; simp [runSum]
  | succ t ih => intro ω; simp only [runSum, ih]; ring

/-- **Certificate form.** On the good event, for every interval `[a, b)` with `b ≤ t`, the item's gated IX estimate is
below its gated true loss plus `L/(2γ)`. -/
theorem ixEst_le_of_good (ℓ : (s : ℕ) → (Fin s → Z) → ℝ) (obs : (s : ℕ) → (Fin s → Z) → Z → Bool) (γ : ℝ)
    (gate : (s : ℕ) → (Fin s → Z) → Bool) (L : ℝ) {t : ℕ} {ω : Fin t → Z}
    (hG : IXGood ν ℓ obs γ gate L t ω) {a b : ℕ} (hab : a ≤ b) (hbt : b ≤ t) :
    runSum (gD (ixEst ν ℓ obs γ) gate a b) t ω <
      runSum (gD (fun s ω => ℓ s (Fin.init ω)) gate a b) t ω + L / (2 * γ) := by
  have h := hG a b hab hbt
  have heq : gD (ixErr ν ℓ obs γ) gate a b =
      fun s ω => gD (ixEst ν ℓ obs γ) gate a b s ω - gD (fun s ω => ℓ s (Fin.init ω)) gate a b s ω := by
    funext s ω; unfold gD ixErr ixEst; split_ifs <;> ring
  rw [heq, runSum_sub] at h
  linarith

end Pool.P0146
