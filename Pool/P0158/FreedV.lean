import Pool.P0139.IntervalFreedman

/-!
# Interval-uniform Freedman bounds with TIME-VARYING (clock-determined) ranges and variances

P0139's `Incr ν D c` has one constant `c` for both the range of the increments and their conditional second moment,
as for slot estimates at a constant rate `x` (`c = 1/x`). P0150 (thread-dependent probe rates `x_j`, its open step
N2) needs rates that vary with the round, but deterministically (they are fixed by the clock). Here:

* `IncrV ν D r v`: increments `≤ r s`, conditionally centred, conditional second moment `≤ v s`, with `r`, `v`
  deterministic functions of the round.
* `widV V ρ L = 2√(V·L) + 2ρL`: the width for total variance `V` and range `ρ` over an interval.
* `interval_tailV` / `interval_tail_negV`: for `b ≤ T`, the gated sum over `[a, b)` is `≥ widV(Σ_{[a,b)} v, ρ, L)`
  (resp. `≤ −widV`) with probability `≤ e^{−L}`, whenever `r ≤ ρ` on `[a, b)`.
* `GoodV`, `goodV_prefix`, `prob_not_goodV`: the two-sided good event over all intervals, with an interval-dependent
  range `ρ a b`, prefix-closed, failing with probability `≤ 2(T+1)²e^{−L}`.
* `rmax1`: the canonical range `max(1, max_{s∈[a,b)} r s)`, with `le_rmax1` and `rmax1_pos`.
* `incrV_of_unbiased`: an unbiased estimate `Y ∈ [0, c s]` of a predictable mean `μ ∈ [0, 1]` with `c s ≥ 1`, e.g. a
  slot estimate `ℓ·1[slot]/x_s` at a clock-determined rate `x_s`; its error satisfies `IncrV` with `r = v = c` and is
  `≥ −1`.
* `incrV_const`: P0139's `Incr ν D c` is `IncrV ν D (fun _ => c) (fun _ => c)` (bridge).
-/

open Finset Real

namespace Pool.P0158

open Pool.P0092 Pool.P0139

variable {Z : Type} [Fintype Z] (ν : PMF Z)

/-- Increments bounded above by `r s`, conditionally centred, with conditional second moment `≤ v s`. -/
structure IncrV (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (r v : ℕ → ℝ) : Prop where
  up : ∀ s (ω : Fin s → Z) z, D s (Fin.snoc ω z) ≤ r s
  mean : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * D s (Fin.snoc ω z) = 0
  var : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ^ 2 ≤ v s

/-- The width for total variance `V` and range `ρ`. -/
noncomputable def widV (V ρ L : ℝ) : ℝ := 2 * Real.sqrt (V * L) + 2 * ρ * L

theorem widV_pos {V ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 < L) : 0 < widV V ρ L := by
  unfold widV; have := Real.sqrt_nonneg (V * L); positivity

/-- P0139's constant-parameter hypothesis is the constant case. -/
theorem incrV_const (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) {c : ℝ} (h : Incr ν D c) :
    IncrV ν D (fun _ => c) (fun _ => c) := ⟨h.up, h.mean, h.var⟩

/-- Tuning: for `V ≥ 0`, `ρ > 0`, `L > 0` some `κ > 0` has `κρ ≤ 1` and `κV + L/κ ≤ widV V ρ L`. -/
theorem tuneV {V ρ L : ℝ} (hV : 0 ≤ V) (hρ : 0 < ρ) (hL : 0 < L) :
    ∃ κ, 0 < κ ∧ κ * ρ ≤ 1 ∧ κ * V + L / κ ≤ widV V ρ L := by
  have hs := Real.sqrt_nonneg (V * L)
  by_cases hcase : V ≤ ρ ^ 2 * L
  · refine ⟨1 / ρ, by positivity, by field_simp; rfl, ?_⟩
    have h1 : 1 / ρ * V ≤ ρ * L := by
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hρ]; nlinarith
    have h2 : L / (1 / ρ) = ρ * L := by field_simp
    unfold widV; rw [h2]; linarith
  · push_neg at hcase
    have hVpos : 0 < V := lt_of_le_of_lt (by positivity) hcase
    set q := Real.sqrt (L / V) with hq
    have hq0 : 0 < q := Real.sqrt_pos.mpr (by positivity)
    have hq2 : q ^ 2 = L / V := Real.sq_sqrt (by positivity)
    refine ⟨q, hq0, ?_, ?_⟩
    · -- q² ρ² = Lρ²/V < 1
      have : (q * ρ) ^ 2 < 1 := by
        rw [mul_pow, hq2, div_mul_eq_mul_div, div_lt_one hVpos]; nlinarith
      nlinarith [sq_nonneg (q * ρ), mul_pos hq0 hρ]
    · -- qV = √(VL) and L/q = √(VL)
      have hsq : Real.sqrt (V * L) ^ 2 = V * L := Real.sq_sqrt (by positivity)
      have e1 : q * V = Real.sqrt (V * L) := by
        have : (q * V) ^ 2 = Real.sqrt (V * L) ^ 2 := by
          rw [mul_pow, hq2, hsq]; field_simp
        have h0 : 0 ≤ q * V := by positivity
        nlinarith [sq_nonneg (q * V - Real.sqrt (V * L)), sq_nonneg (q * V + Real.sqrt (V * L))]
      have e2 : L / q = Real.sqrt (V * L) := by
        rw [div_eq_iff hq0.ne', ← e1]
        have : q ^ 2 * V = L := by rw [hq2]; field_simp
        nlinarith
      unfold widV; rw [e1, e2]; nlinarith [hρ, hL]

/-- **Freedman on one interval, time-varying parameters.** -/
theorem interval_tailV (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool)
    {r v : ℕ → ℝ} (hD : IncrV ν D r v) (hv : ∀ s, 0 ≤ v s) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 < L)
    {a b T : ℕ} (hbT : b ≤ T) (hr : ∀ s, a ≤ s → s < b → r s ≤ ρ) :
    probGe ν T (runSum (gD D gate a b) T) (widV (∑ s ∈ Ico a b, v s) ρ L) ≤ Real.exp (-L) := by
  have hV0 : 0 ≤ ∑ s ∈ Ico a b, v s := Finset.sum_nonneg fun s _ => hv s
  obtain ⟨κ, hκ0, hκρ, hκw⟩ := tuneV hV0 hρ hL
  have hF := Pool.P0100.freedman_coins ν (gD D gate a b)
    (fun s _ => if a ≤ s ∧ s < b then v s else 0) hκ0 (T := T)
    (fun s _ ω z _ _ => by
      rw [gD_snoc]
      split_ifs with h
      · calc κ * D s (Fin.snoc ω z) ≤ κ * ρ :=
              mul_le_mul_of_nonneg_left ((hD.up s ω z).trans (hr s h.1 h.2.1)) hκ0.le
          _ ≤ 1 := hκρ
      · simp)
    (fun s _ ω _ => by
      simp only [gD_snoc]
      split_ifs
      · rw [hD.mean s ω]
      · simp)
    (fun s _ ω _ => by
      simp only [gD_snoc]
      split_ifs with h1 h2
      · exact hD.var s ω
      · exact absurd ⟨h1.1, h1.2.1⟩ h2
      · simp; exact hv s
      · simp) L
  have hV : ∀ ω : Fin T → Z, Pool.P0100.runV (fun s _ => if a ≤ s ∧ s < b then v s else 0) T ω =
      ∑ s ∈ Ico a b, v s := by
    intro ω
    rw [Pool.P0115.runV_det (fun s => if a ≤ s ∧ s < b then v s else 0) T ω, ← Finset.sum_filter]
    congr 1
    ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  refine le_trans (probGe_mono ν (fun ω h => ?_)) hF
  rw [hV ω]
  linarith

omit [Fintype Z] in
theorem gD_negV (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) (a b : ℕ) :
    gD (fun s ω => -D s ω) gate a b = fun s ω => -gD D gate a b s ω := by
  funext s ω; unfold gD; split_ifs <;> simp

/-- The lower tail, given increments `≥ −r s`. -/
theorem interval_tail_negV (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool)
    {r v : ℕ → ℝ} (hD : IncrV ν D r v) (hlow : ∀ s (ω : Fin s → Z) z, -r s ≤ D s (Fin.snoc ω z))
    (hv : ∀ s, 0 ≤ v s) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 < L)
    {a b T : ℕ} (hbT : b ≤ T) (hr : ∀ s, a ≤ s → s < b → r s ≤ ρ) :
    probGe ν T (fun ω => -runSum (gD D gate a b) T ω) (widV (∑ s ∈ Ico a b, v s) ρ L) ≤ Real.exp (-L) := by
  have hD' : IncrV ν (fun s ω => -D s ω) r v :=
    { up := fun s ω z => by have := hlow s ω z; linarith
      mean := fun s ω => by
        simp only [mul_neg, Finset.sum_neg_distrib, hD.mean s ω, neg_zero]
      var := fun s ω => by simpa only [neg_sq] using hD.var s ω }
  have h := interval_tailV ν (fun s ω => -D s ω) gate hD' hv hρ hL hbT hr
  rw [gD_negV] at h
  refine le_trans (le_of_eq ?_) h
  unfold probGe
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Pool.P0115.runSum_neg]

/-- **The good event** with variance budget `v` and interval ranges `ρ a b`. -/
def GoodV (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) (v : ℕ → ℝ)
    (ρ : ℕ → ℕ → ℝ) (L : ℝ) (t : ℕ) (ω : Fin t → Z) : Prop :=
  ∀ a b, a ≤ b → b ≤ t → |runSum (gD D gate a b) t ω| < widV (∑ s ∈ Ico a b, v s) (ρ a b) L

omit [Fintype Z] in
theorem goodV_prefix (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) (v : ℕ → ℝ)
    (ρ : ℕ → ℕ → ℝ) (L : ℝ) (t : ℕ) (ω : Fin t → Z) (z : Z) (h : GoodV D gate v ρ L (t + 1) (Fin.snoc ω z)) :
    GoodV D gate v ρ L t ω := by
  intro a b hab hb
  have := h a b hab (by omega)
  rwa [runSum_gD_stable D gate hb] at this

open Classical in
/-- **Union bound**: the two-sided good event fails at the horizon with probability `≤ 2(T+1)²e^{−L}`. -/
theorem prob_not_goodV (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool)
    {r v : ℕ → ℝ} (hD : IncrV ν D r v) (hlow : ∀ s (ω : Fin s → Z) z, -r s ≤ D s (Fin.snoc ω z))
    (hv : ∀ s, 0 ≤ v s) (ρ : ℕ → ℕ → ℝ) (hρ : ∀ a b, 0 < ρ a b) (hr : ∀ a b s, a ≤ s → s < b → r s ≤ ρ a b)
    {L : ℝ} (hL : 0 < L) (T : ℕ) :
    (∑ ω : Fin T → Z, wgt ν ω * if GoodV D gate v ρ L T ω then (0 : ℝ) else 1) ≤
      2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
  set I : Finset ((ℕ × ℕ) × Bool) :=
    (((Finset.range (T + 1)) ×ˢ (Finset.range (T + 1))).filter (fun p => p.1 ≤ p.2)) ×ˢ Finset.univ with hI
  let f : (ℕ × ℕ) × Bool → (Fin T → Z) → ℝ := fun i ω =>
    (if i.2 then runSum (gD D gate i.1.1 i.1.2) T ω else -runSum (gD D gate i.1.1 i.1.2) T ω) -
      widV (∑ s ∈ Ico i.1.1 i.1.2, v s) (ρ i.1.1 i.1.2) L
  have hstep : (∑ ω : Fin T → Z, wgt ν ω * if GoodV D gate v ρ L T ω then (0 : ℝ) else 1) ≤
      ∑ ω : Fin T → Z, wgt ν ω * if ∃ i ∈ I, (0 : ℝ) ≤ f i ω then 1 else 0 := by
    refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
    by_cases hg : GoodV D gate v ρ L T ω
    · rw [if_pos hg]; split_ifs <;> norm_num
    by_cases hex : ∃ i ∈ I, (0 : ℝ) ≤ f i ω
    · rw [if_neg hg, if_pos hex]
    · exfalso
      apply hex
      simp only [GoodV, not_forall, not_lt] at hg
      obtain ⟨a, b, hab, hbT, hw⟩ := hg
      rcases le_abs'.mp hw with h1 | h1
      · refine ⟨((a, b), false), ?_, ?_⟩
        · simp only [hI, Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, and_true]
          omega
        · simp only [f, Bool.false_eq_true, ↓reduceIte]; linarith
      · refine ⟨((a, b), true), ?_, ?_⟩
        · simp only [hI, Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, and_true]
          omega
        · simp only [f, ↓reduceIte]; linarith
  refine le_trans hstep (le_trans (probGe_exists_le ν I f 0) ?_)
  have hone : ∀ i ∈ I, probGe ν T (f i) 0 ≤ Real.exp (-L) := by
    intro i hi
    simp only [hI, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hi
    rcases i with ⟨⟨a, b⟩, sgn⟩
    have hbT : b ≤ T := by simp only at hi; omega
    cases sgn
    · refine le_trans (probGe_mono ν (fun ω h => ?_))
        (interval_tail_negV ν D gate hD hlow hv (hρ a b) hL hbT (fun s h1 h2 => hr a b s h1 h2))
      simp only [f, Bool.false_eq_true, ↓reduceIte] at h; linarith
    · refine le_trans (probGe_mono ν (fun ω h => ?_))
        (interval_tailV ν D gate hD hv (hρ a b) hL hbT (fun s h1 h2 => hr a b s h1 h2))
      simp only [f, ↓reduceIte] at h; linarith
  calc ∑ i ∈ I, probGe ν T (f i) 0 ≤ ∑ _i ∈ I, Real.exp (-L) := Finset.sum_le_sum hone
    _ = (I.card : ℝ) * Real.exp (-L) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have h1 : I.card ≤ (T + 1) * (T + 1) * 2 := by
          rw [hI, Finset.card_product]
          refine Nat.mul_le_mul ?_ (by simp)
          refine le_trans (Finset.card_filter_le _ _) ?_
          rw [Finset.card_product, Finset.card_range]
        have h2 : (I.card : ℝ) ≤ ((T + 1) * (T + 1) * 2 : ℕ) := by exact_mod_cast h1
        push_cast at h2; nlinarith

/-! ## The canonical interval range and unbiased estimates at clock-determined rates -/

/-- `max(1, max_{s ∈ [a,b)} r s)`. -/
noncomputable def rmax1 (r : ℕ → ℝ) (a b : ℕ) : ℝ :=
  max 1 (((Finset.Ico a b).sup (fun s => Real.toNNReal (r s)) : NNReal) : ℝ)

theorem rmax1_pos (r : ℕ → ℝ) (a b : ℕ) : 0 < rmax1 r a b :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

theorem le_rmax1 (r : ℕ → ℝ) {a b s : ℕ} (h1 : a ≤ s) (h2 : s < b) : r s ≤ rmax1 r a b := by
  have hs : s ∈ Finset.Ico a b := Finset.mem_Ico.2 ⟨h1, h2⟩
  have h := Finset.le_sup (f := fun s => Real.toNNReal (r s)) hs
  have h' : (Real.toNNReal (r s) : ℝ) ≤ (((Finset.Ico a b).sup (fun s => Real.toNNReal (r s)) : NNReal) : ℝ) :=
    by exact_mod_cast h
  exact (Real.le_coe_toNNReal (r s)).trans (h'.trans (le_max_right _ _))

/-- An unbiased estimate `Y ∈ [0, c s]` of a predictable mean `μ ∈ [0, 1]`, with `c s ≥ 1` deterministic (e.g. a slot
estimate `ℓ·1[slot]/x_s` at a clock-determined rate `x_s`): its error satisfies `IncrV` with `r = v = c`, and is
`≥ −1`. -/
theorem incrV_of_unbiased (Y : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (μ : (s : ℕ) → (Fin s → Z) → ℝ) {c : ℕ → ℝ}
    (hc : ∀ s, 1 ≤ c s) (hY0 : ∀ s (ω : Fin s → Z) z, 0 ≤ Y s (Fin.snoc ω z))
    (hYc : ∀ s (ω : Fin s → Z) z, Y s (Fin.snoc ω z) ≤ c s)
    (hmean : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * Y s (Fin.snoc ω z) = μ s ω)
    (hμ0 : ∀ s (ω : Fin s → Z), 0 ≤ μ s ω) (hμ1 : ∀ s (ω : Fin s → Z), μ s ω ≤ 1) :
    IncrV ν (fun s ω => Y s ω - μ s (Fin.init ω)) c c ∧
      ∀ s (ω : Fin s → Z) z, -1 ≤ Y s (Fin.snoc ω z) - μ s ω := by
  have h1 := sum_toReal_one ν
  refine ⟨{ up := fun s ω z => ?_, mean := fun s ω => ?_, var := fun s ω => ?_ }, fun s ω z => ?_⟩
  · simp only [Fin.init_snoc]; linarith [hYc s ω z, hμ0 s ω]
  · simp only [Fin.init_snoc, mul_sub, Finset.sum_sub_distrib, hmean s ω, ← Finset.sum_mul, h1, one_mul,
      sub_self]
  · simp only [Fin.init_snoc]
    have hsq : ∀ z, (Y s (Fin.snoc ω z) - μ s ω) ^ 2 ≤ c s * Y s (Fin.snoc ω z) - 2 * μ s ω * Y s (Fin.snoc ω z) +
        μ s ω ^ 2 := by
      intro z
      have := hY0 s ω z; have := hYc s ω z
      nlinarith
    calc ∑ z, (ν z).toReal * (Y s (Fin.snoc ω z) - μ s ω) ^ 2
        ≤ ∑ z, (ν z).toReal * (c s * Y s (Fin.snoc ω z) - 2 * μ s ω * Y s (Fin.snoc ω z) + μ s ω ^ 2) :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hsq z) ENNReal.toReal_nonneg
      _ = c s * μ s ω - 2 * μ s ω * μ s ω + μ s ω ^ 2 := by
          simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [← Finset.sum_mul, h1]
          have e1 : ∑ z, (ν z).toReal * (c s * Y s (Fin.snoc ω z)) = c s * μ s ω := by
            rw [show ∑ z, (ν z).toReal * (c s * Y s (Fin.snoc ω z)) =
                c s * ∑ z, (ν z).toReal * Y s (Fin.snoc ω z) by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring, hmean s ω]
          have e2 : ∑ z, (ν z).toReal * (2 * μ s ω * Y s (Fin.snoc ω z)) = 2 * μ s ω * μ s ω := by
            rw [show ∑ z, (ν z).toReal * (2 * μ s ω * Y s (Fin.snoc ω z)) =
                2 * μ s ω * ∑ z, (ν z).toReal * Y s (Fin.snoc ω z) by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring, hmean s ω]
          rw [e1, e2]; ring
      _ ≤ c s := by have := hμ0 s ω; have := hμ1 s ω; have := hc s; nlinarith
  · linarith [hY0 s ω z, hμ1 s ω]

/-- The difference of two error processes (e.g. a member's slot-estimate error minus BASE's estimate error, as in
rule (b″)) satisfies `IncrV` with `r = r₁ + l₂`, `v = 2(v₁ + v₂)`, and the matching lower bound `−(l₁ + r₂)`, given
lower bounds `−l₁ ≤ D₁`, `−l₂ ≤ D₂`. -/
theorem incrV_sub (D₁ D₂ : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) {r₁ r₂ v₁ v₂ l₁ l₂ : ℕ → ℝ}
    (h₁ : IncrV ν D₁ r₁ v₁) (h₂ : IncrV ν D₂ r₂ v₂)
    (hl₁ : ∀ s (ω : Fin s → Z) z, -l₁ s ≤ D₁ s (Fin.snoc ω z)) (hl₂ : ∀ s (ω : Fin s → Z) z, -l₂ s ≤ D₂ s (Fin.snoc ω z)) :
    IncrV ν (fun s ω => D₁ s ω - D₂ s ω) (fun s => r₁ s + l₂ s) (fun s => 2 * (v₁ s + v₂ s)) ∧
      ∀ s (ω : Fin s → Z) z, -(l₁ s + r₂ s) ≤ D₁ s (Fin.snoc ω z) - D₂ s (Fin.snoc ω z) := by
  refine ⟨{ up := fun s ω z => ?_, mean := fun s ω => ?_, var := fun s ω => ?_ }, fun s ω z => ?_⟩
  · linarith [h₁.up s ω z, hl₂ s ω z]
  · simp only [mul_sub, Finset.sum_sub_distrib, h₁.mean s ω, h₂.mean s ω, sub_self]
  · calc ∑ z, (ν z).toReal * (D₁ s (Fin.snoc ω z) - D₂ s (Fin.snoc ω z)) ^ 2
        ≤ ∑ z, (ν z).toReal * (2 * D₁ s (Fin.snoc ω z) ^ 2 + 2 * D₂ s (Fin.snoc ω z) ^ 2) :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
            (by nlinarith [sq_nonneg (D₁ s (Fin.snoc ω z) + D₂ s (Fin.snoc ω z))]) ENNReal.toReal_nonneg
      _ = 2 * ∑ z, (ν z).toReal * D₁ s (Fin.snoc ω z) ^ 2 + 2 * ∑ z, (ν z).toReal * D₂ s (Fin.snoc ω z) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ 2 * (v₁ s + v₂ s) := by linarith [h₁.var s ω, h₂.var s ω]
  · linarith [hl₁ s ω z, h₂.up s ω z]

end Pool.P0158
