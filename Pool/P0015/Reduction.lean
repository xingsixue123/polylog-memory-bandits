import Pool.P0015.BlockLoss
/-!
# The block reduction: from a `K`-query machine to a single-query machine

The virtual loss vectors `virt ℓ b u` depend only on `ℓ` and on the offsets, which are drawn
independently of `A`'s coins: for every fixed offset sequence `w : Fin T' → Fin B` they form an
oblivious loss sequence `ℓw ℓ w` for `A`, and every coordinate is unbiased:
the mean over `u` of `virt ℓ b u i` is the average loss of arm `i` over block `b`.

* `mix_state`, `mix_loss`, `mix_cum`: the law `avgA` is the average over `w` of the laws of `A`
  on the oblivious sequences `ℓw ℓ w` (exact identities, proved with `sum_indep`).
* `regret_blockMachine_le` (main result): if `A` has regret at most `R` over `T'` days on every
  loss sequence, then for every loss sequence the block machine has regret at most
  `B * R + K * T'` over `T' * B` rounds.
* `memBits_blockMachine`: the block machine uses
  `A.memBits + (K + 1) log₂ n + log₂ B + (K + 1)` bits.
* `regret_le_regret_add`: for any P0001 machine, the regret over `T ≥ T₀` rounds is at most the
  regret over `T₀` rounds plus `T - T₀`.
-/

open scoped ENNReal

namespace Pool.P0015

open Pool.P0001

variable {n K B : ℕ} (hB : n ≤ B) (hB0 : 0 < B) (A : QMachine n K)

/-- The virtual loss sequence of `A` for the offsets `w`. -/
def ℓw (ℓ : LossSeq n) {T' : ℕ} (w : Fin T' → Fin B) : LossSeq n :=
  fun t i => if h : t < T' then virt hB ℓ t (w ⟨t, h⟩) i else false

lemma ℓw_of_lt (ℓ : LossSeq n) {T' : ℕ} (w : Fin T' → Fin B) (t : ℕ) (h : t < T') :
    ℓw hB ℓ w t = virt hB ℓ t (w ⟨t, h⟩) := by
  funext i; simp [ℓw, h]

/-- Splitting one coordinate of a uniform function. -/
lemma sum_indep {T' : ℕ} (hB0 : 0 < B) (i : Fin T') (Φ : (Fin T' → Fin B) → Fin B → ℝ)
    (hΦ : ∀ w x y, Φ (Function.update w i x) y = Φ w y) :
    ∑ w, Φ w (w i) = (1 / (B : ℝ)) * ∑ w, ∑ y, Φ w y := by
  set e := Equiv.funSplitAt i (Fin B)
  have hsymm : ∀ (x y : Fin B) (r : {j // j ≠ i} → Fin B),
      e.symm (y, r) = Function.update (e.symm (x, r)) i y := by
    intro x y r
    funext j
    by_cases hj : j = i
    · subst hj; simp [e, Equiv.funSplitAt_symm_apply]
    · simp [e, Equiv.funSplitAt_symm_apply, hj]
  have hΦ' : ∀ (x y : Fin B) (r : {j // j ≠ i} → Fin B), Φ (e.symm (x, r)) y = Φ (e.symm (y, r)) y := by
    intro x y r; rw [hsymm x y r, hΦ]
  have hi : ∀ (x : Fin B) (r : {j // j ≠ i} → Fin B), (e.symm (x, r)) i = x := by
    intro x r; simp [e, Equiv.funSplitAt_symm_apply]
  rw [← Fintype.sum_equiv e.symm (fun p => Φ (e.symm p) ((e.symm p) i)) _ (fun _ => rfl)]
  rw [← Fintype.sum_equiv e.symm (fun p => ∑ y, Φ (e.symm p) y) _ (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, hi]
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB0.ne'
  set ψ : ({j // j ≠ i} → Fin B) → Fin B → ℝ := fun r y => Φ (e.symm (y, r)) y with hψ
  calc ∑ x, ∑ r, Φ (e.symm (x, r)) x = ∑ x, ∑ r, ψ r x := rfl
    _ = ∑ r, ∑ y, ψ r y := Finset.sum_comm
    _ = (1 / (B : ℝ)) * ∑ _x : Fin B, ∑ r, ∑ y, ψ r y := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
          one_div_mul_cancel hB', one_mul]
    _ = (1 / (B : ℝ)) * ∑ x, ∑ r, ∑ y, Φ (e.symm (x, r)) y := by
        congr 1
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun r _ =>
          Finset.sum_congr rfl fun y _ => ?_
        rw [hψ, hΦ' x y r]

/-- Average over all offset sequences `w : Fin T' → Fin B`. -/
noncomputable def avgW (B T' : ℕ) (F : (Fin T' → Fin B) → ℝ) : ℝ :=
  (1 / (B : ℝ) ^ T') * ∑ w, F w

section avgW

variable {T' : ℕ}

lemma avgW_const (hB0 : 0 < B) (c : ℝ) : avgW B T' (fun _ => c) = c := by
  have : (B : ℝ) ^ T' ≠ 0 := pow_ne_zero _ (by exact_mod_cast hB0.ne')
  simp only [avgW, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow]
  field_simp

lemma avgW_mono {F G : (Fin T' → Fin B) → ℝ} (h : ∀ w, F w ≤ G w) : avgW B T' F ≤ avgW B T' G :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => h w) (by positivity)

lemma avgW_add (F G : (Fin T' → Fin B) → ℝ) :
    avgW B T' (fun w => F w + G w) = avgW B T' F + avgW B T' G := by
  simp only [avgW, Finset.sum_add_distrib, mul_add]

lemma avgW_sum {ι : Type} (s : Finset ι) (F : ι → (Fin T' → Fin B) → ℝ) :
    avgW B T' (fun w => ∑ i ∈ s, F i w) = ∑ i ∈ s, avgW B T' (F i) := by
  simp only [avgW, Finset.mul_sum]; rw [Finset.sum_comm]

lemma avgW_indep (hB0 : 0 < B) (i : Fin T') (Φ : (Fin T' → Fin B) → Fin B → ℝ)
    (hΦ : ∀ w x y, Φ (Function.update w i x) y = Φ w y) :
    avgW B T' (fun w => Φ w (w i)) = avgW B T' (fun w => E (unif B hB0) (Φ w)) := by
  simp only [avgW, E_unif, sum_indep hB0 i Φ hΦ, Finset.mul_sum]

end avgW

lemma ℓw_update (ℓ : LossSeq n) {T' : ℕ} (w : Fin T' → Fin B) (b : ℕ) (hb : b < T') (x : Fin B) :
    ∀ t < b, ℓw hB ℓ (Function.update w ⟨b, hb⟩ x) t = ℓw hB ℓ w t := by
  intro t ht
  funext i
  have htT : t < T' := by omega
  have hne : (⟨t, htT⟩ : Fin T') ≠ ⟨b, hb⟩ := by intro h; simp at h; omega
  simp [ℓw, htT, Function.update_of_ne hne]

/-- One averaging step: inside the average over `w`, a fresh uniform offset on day `b` can be
replaced by the offset `w b`. -/
lemma avg_step (ℓ : LossSeq n) (T' b : ℕ) (hb : b < T') (h : A.State → QAct n K → Fin B → ℝ) :
    avgW B T' (fun w => E (A.stateDist (ℓw hB ℓ w) b) (fun s => E (A.act b s) (fun a =>
      E (unif B hB0) (fun u => h s a u)))) =
    avgW B T' (fun w => E (A.stateDist (ℓw hB ℓ w) b) (fun s => E (A.act b s) (fun a =>
      h s a (w ⟨b, hb⟩)))) := by
  let Φ : (Fin T' → Fin B) → Fin B → ℝ := fun w u =>
    E (A.stateDist (ℓw hB ℓ w) b) (fun s => E (A.act b s) (fun a => h s a u))
  have hΦ : ∀ w x y, Φ (Function.update w ⟨b, hb⟩ x) y = Φ w y := by
    intro w x y
    simp only [Φ]
    rw [QMachine.stateDist_congr A b (ℓw_update hB ℓ w b hb x)]
  have h1 := avgW_indep hB0 ⟨b, hb⟩ Φ hΦ
  simp only [Φ] at h1
  rw [h1]
  congr 1; funext w
  rw [← E_comm]
  refine congrArg _ (funext fun s => ?_)
  rw [← E_comm]

/-- Averaging over the offsets: the law `avgA` is the average of the laws of `A` on the
virtual sequences. -/
lemma mix_state (ℓ : LossSeq n) (T' : ℕ) :
    ∀ b ≤ T', ∀ g : A.State → ℝ,
      E (avgA hB hB0 A ℓ b) g = avgW B T' (fun w => E (A.stateDist (ℓw hB ℓ w) b) g) := by
  intro b
  induction b with
  | zero =>
    intro _ g
    simp only [avgA, QMachine.stateDist]
    exact (avgW_const hB0 _).symm
  | succ b ih =>
    intro hb g
    have hbT : b < T' := by omega
    simp only [avgA, E_bind]
    rw [ih (by omega), avg_step hB hB0 A ℓ T' b hbT]
    congr 1; funext w
    simp only [QMachine.stateDist, E_bind, ℓw_of_lt hB ℓ w b hbT]

lemma mix_loss (ℓ : LossSeq n) (T' b : ℕ) (hb : b < T') :
    E (avgA hB hB0 A ℓ b) (fun s => E (A.act b s) (fun a =>
      E (unif B hB0) (fun u => φ (virt hB ℓ b u a.1)))) =
      avgW B T' (fun w => A.expLoss (ℓw hB ℓ w) b) := by
  rw [mix_state hB hB0 A ℓ T' b hb.le, avg_step hB hB0 A ℓ T' b hb]
  congr 1; funext w
  simp only [QMachine.expLoss_eq, ℓw_of_lt hB ℓ w b hb]

lemma mix_cum (ℓ : LossSeq n) (T' b : ℕ) (hb : b < T') (j : Fin n) :
    E (unif B hB0) (fun u => φ (virt hB ℓ b u j)) = avgW B T' (fun w => φ (ℓw hB ℓ w b j)) := by
  set i : Fin T' := ⟨b, hb⟩
  have := avgW_indep hB0 i (fun _ u => φ (virt hB ℓ b u j)) (fun _ _ _ => rfl)
  rw [avgW_const hB0] at this
  rw [← this]
  congr 1; funext w
  simp [ℓw_of_lt hB ℓ w b hb]
  rfl

/-- **The block reduction.** If the `K`-query machine `A` has regret at most `R` over `T'` days
on every loss sequence, the block machine has regret at most `B * R + K * T'` over `T' * B`
rounds on every loss sequence. -/
theorem regret_blockMachine_le [NeZero n] (T' : ℕ) (R : ℝ) (hR : ∀ ℓ', A.regret ℓ' T' ≤ R)
    (ℓ : LossSeq n) : regret (blockMachine hB hB0 A) ℓ (T' * B) ≤ B * R + K * T' := by
  obtain ⟨j, hj⟩ := exists_bestLoss_eq ℓ (T' * B)
  have hsum := sum_expLoss_blockMachine_le hB hB0 A ℓ T'
  have hw : ∀ w : Fin T' → Fin B, ∑ q ∈ Finset.range T', A.expLoss (ℓw hB ℓ w) q ≤
      R + cumLoss (ℓw hB ℓ w) T' j := by
    intro w
    have h1 := hR (ℓw hB ℓ w)
    have h2 := bestLoss_le_cumLoss (ℓw hB ℓ w) T' j
    rw [QMachine.regret] at h1
    linarith
  have hcum : cumLoss ℓ (T' * B) j =
      B * ∑ q ∈ Finset.range T', E (unif B hB0) (fun u => φ (virt hB ℓ q u j)) := by
    rw [cumLoss, sum_range_mul_eq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => sum_block_eq hB hB0 ℓ q j
  have hcumw : avgW B T' (fun w => cumLoss (ℓw hB ℓ w) T' j) =
      ∑ q ∈ Finset.range T', E (unif B hB0) (fun u => φ (virt hB ℓ q u j)) := by
    simp only [cumLoss]
    rw [avgW_sum]
    exact Finset.sum_congr rfl fun q hq => (mix_cum hB hB0 ℓ T' q (Finset.mem_range.1 hq) j).symm
  have key : ∑ t ∈ Finset.range (T' * B), (blockMachine hB hB0 A).expLoss ℓ t ≤
      B * R + cumLoss ℓ (T' * B) j + K * T' := by
    calc ∑ t ∈ Finset.range (T' * B), (blockMachine hB hB0 A).expLoss ℓ t
        ≤ _ := hsum
      _ = ∑ q ∈ Finset.range T', (B * avgW B T' (fun w => A.expLoss (ℓw hB ℓ w) q) + K) :=
          Finset.sum_congr rfl fun q hq => by
            rw [mix_loss hB hB0 A ℓ T' q (Finset.mem_range.1 hq)]
      _ = B * avgW B T' (fun w => ∑ q ∈ Finset.range T', A.expLoss (ℓw hB ℓ w) q) + K * T' := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, avgW_sum]
          simp [mul_comm]
      _ ≤ B * avgW B T' (fun w => R + cumLoss (ℓw hB ℓ w) T' j) + K * T' := by
          gcongr
          exact avgW_mono hw
      _ = B * R + cumLoss ℓ (T' * B) j + K * T' := by
          rw [avgW_add, avgW_const hB0, hcumw, hcum]
          ring
  rw [regret, hj]
  linarith

lemma card_blockMachine :
    Fintype.card (blockMachine hB hB0 A).State =
      Fintype.card A.State * (n * n ^ K) * B * 2 ^ (K + 1) := by
  simp only [blockMachine, BState, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, QAct]
  ring

lemma QMachine.card_pos (A : QMachine n K) : 0 < Fintype.card A.State := by
  obtain ⟨s, -⟩ := A.init.support_nonempty
  exact Fintype.card_pos_iff.2 ⟨s⟩

lemma memBits_blockMachine (hn : 0 < n) :
    (blockMachine hB hB0 A).memBits =
      A.memBits + (K + 1) * Real.logb 2 n + Real.logb 2 B + (K + 1) := by
  have h1 : (0 : ℝ) < Fintype.card A.State := by exact_mod_cast A.card_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB0
  rw [Machine.memBits, card_blockMachine, QMachine.memBits]
  push_cast
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  push_cast
  ring

/-- Regret over a longer horizon: each extra round adds at most one. -/
lemma regret_le_regret_add {M : Machine n} (ℓ : LossSeq n) {T₀ T : ℕ} (h : T₀ ≤ T) :
    regret M ℓ T ≤ regret M ℓ T₀ + (T - T₀ : ℕ) := by
  have hsplit : ∑ t ∈ Finset.range T, M.expLoss ℓ t =
      ∑ t ∈ Finset.range T₀, M.expLoss ℓ t + ∑ t ∈ Finset.range (T - T₀), M.expLoss ℓ (T₀ + t) := by
    rw [← Finset.sum_range_add, Nat.add_sub_cancel' h]
  have hrest : ∑ t ∈ Finset.range (T - T₀), M.expLoss ℓ (T₀ + t) ≤ (T - T₀ : ℕ) := by
    calc _ ≤ ∑ _t ∈ Finset.range (T - T₀), (1 : ℝ) :=
          Finset.sum_le_sum fun t _ => M.expLoss_le_one ℓ _
      _ = _ := by simp
  have hbest : bestLoss ℓ T₀ ≤ bestLoss ℓ T := by
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · simp [bestLoss, Real.iInf_of_isEmpty]
    refine le_ciInf fun i => (bestLoss_le_cumLoss ℓ T₀ i).trans ?_
    unfold cumLoss
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun _ _ _ => by positivity
  rw [regret, regret, hsplit]
  linarith

/-- The same bound for the homogeneous version of the block machine (round number stored in the
state, P0001's `withClock`, which costs `log₂ (T' * B + 1)` more bits). -/
theorem regret_blockMachine_withClock_le [NeZero n] (T' : ℕ) (R : ℝ)
    (hR : ∀ ℓ', A.regret ℓ' T' ≤ R) (ℓ : LossSeq n) :
    regret ((blockMachine hB hB0 A).withClock (T' * B)) ℓ (T' * B) ≤ B * R + K * T' := by
  rw [regret_withClock]
  exact regret_blockMachine_le hB hB0 A T' R hR ℓ

end Pool.P0015
