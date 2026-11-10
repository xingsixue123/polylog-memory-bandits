import Pool.P0105.FOConc
import Pool.P0100.FreedmanCoins

/-!
# Length-dependent (Freedman) concentration of slot-IW estimates, and forced-run overflow

P0105's concentration is range-based (P0092's Azuma, width `(s+1)√(T log)` at horizon scale). Here the
variance-adaptive bound (P0100's `freedman_coins`) gives widths that scale with the interval length:

* `errIncr_split`, `obs_part`: the increment is the observed part minus its conditional mean.
* `errIncr_sq`: conditional second moment `≤ s·Σₓ (w u x)²` (for `|L| ≤ 1`).
* `errIncr_le`: the increment is `≤ s` for weights and losses in `[0, 1]`.
* `runV_det`: P0100's `runV` of a coin-free budget is a plain sum.
* `errIncr_freedman`: `P(Σ errIncr − κ·s·Σ_u Σₓ w² ≥ x/κ) ≤ e^{−x}` for `0 < κ ≤ 1/s`.
* `sum_wIv_sq`, `sum_range_ind`, `tune_le`: the single-copy interval weighting, and the choice
  `κ = min (1/s) √(x/(s·len))`.
* **`fo_interval_freedman`**: for P0095's FO process, a copy `c` and `[a, b)` with `a < b ≤ T`: without overflow,
  `c`'s realized estimate over `[a, b)` exceeds its true loss over the slotted units by `≥ 2√(s·(b−a)·x) + 2s·x`
  with probability `≤ e^{−x}`.
* **Lower tail:** `neg_errIncr_le`, `runSum_neg`, `errIncr_freedman_lower` (`0 < κ ≤ 1`, `Σₓ w ≤ 1`), `tune_le_one`
  and `fo_interval_freedman_lower`: the true loss exceeds the estimate by `≥ 2√(s·(b−a)·x) + 2x` with probability
  `≤ e^{−x}`.
* **`Vat_forced_card_le`**: the forced copy-last run's start-pool members are the actual run's plus at most the
  copy. So `s − 1` members in the actual run means no overflow in any forced run.
-/

namespace Pool.P0115

open Finset Pool.P0105

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (L : ℕ → ι → ℝ)
  (Vf : (u : ℕ) → (Fin u → Fin s) → Finset ι) (ocf : (u : ℕ) → (Fin u → Fin s) → Fin s → Option ι)

/-- The observed part of the increment: `s · w · L` of the observed copy. -/
theorem errIncr_split (w : ℕ → ι → ℝ) (u : ℕ) (h : Fin u → Fin s) (z : Fin s) (hc : (Vf u h).card ≤ s) :
    errIncr s L Vf ocf w u (Fin.snoc h z) =
      (∑ x, w u x * (if ocf u h z = some x then (s : ℝ) * L u x else 0)) -
        ∑ x, w u x * (if x ∈ Vf u h then L u x else 0) := by
  unfold errIncr
  simp only [Fin.init_snoc, Fin.snoc_last, if_pos hc]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The observed part, as a function of the slot content. -/
theorem obs_part (w : ℕ → ι → ℝ) (u : ℕ) (o : Option ι) :
    ∑ x, w u x * (if o = some x then (s : ℝ) * L u x else 0) =
      match o with
      | none => 0
      | some x' => w u x' * ((s : ℝ) * L u x') := by
  cases o with
  | none => simp
  | some x' =>
    simp only [Option.some.injEq]
    rw [Finset.sum_eq_single x']
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp

/-- **Conditional second moment** of the increment under uniform slots: at most `s · Σₓ (w u x)²` when `|L| ≤ 1`. -/
theorem errIncr_sq [NeZero s] (hocc : SlotLayout s Vf ocf) (hL : ∀ u x, |L u x| ≤ 1) (w : ℕ → ι → ℝ) (u : ℕ)
    (h : Fin u → Fin s) :
    ∑ z : Fin s, (1 / (s : ℝ)) * errIncr s L Vf ocf w u (Fin.snoc h z) ^ 2 ≤ s * ∑ x, (w u x) ^ 2 := by
  have hs : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne s))
  by_cases hc : (Vf u h).card ≤ s
  · set m := ∑ x, w u x * (if x ∈ Vf u h then L u x else 0) with hm
    set g : Option ι → ℝ := fun o => ∑ x, w u x * (if o = some x then (s : ℝ) * L u x else 0) with hg
    have hg0 : g none = 0 := by simp [hg]
    have hA : ∀ z, errIncr s L Vf ocf w u (Fin.snoc h z) = g (ocf u h z) - m := fun z =>
      errIncr_split s L Vf ocf w u h z hc
    -- the mean of the observed part is `m`
    have hmean : ∑ z : Fin s, (1 / (s : ℝ)) * g (ocf u h z) = m := by
      rw [← Finset.mul_sum, hocc u h hc g hg0]
      simp only [hg, hm]
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.mul_sum]
      simp only [Option.some.injEq, Finset.sum_ite_eq', mul_ite, mul_zero]
      split_ifs <;> field_simp
    -- the second moment of the observed part
    have hsq : ∑ z : Fin s, (1 / (s : ℝ)) * g (ocf u h z) ^ 2 = s * ∑ x ∈ Vf u h, (w u x * L u x) ^ 2 := by
      have hg2 : (fun o => g o ^ 2) none = 0 := by simp [hg0]
      rw [← Finset.mul_sum, hocc u h hc (fun o => g o ^ 2) hg2]
      have : ∀ x', g (some x') = w u x' * ((s : ℝ) * L u x') := fun x' => by
        simp only [hg]; rw [obs_part s L w u (some x')]
      simp only [this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      field_simp
    calc ∑ z : Fin s, (1 / (s : ℝ)) * errIncr s L Vf ocf w u (Fin.snoc h z) ^ 2
        = ∑ z : Fin s, (1 / (s : ℝ)) * g (ocf u h z) ^ 2 - 2 * m * ∑ z : Fin s, (1 / (s : ℝ)) * g (ocf u h z) +
            m ^ 2 * ∑ _z : Fin s, (1 / (s : ℝ)) := by
          simp only [hA, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ = s * ∑ x ∈ Vf u h, (w u x * L u x) ^ 2 - m ^ 2 := by
          rw [hsq, hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
          ring
      _ ≤ s * ∑ x, (w u x) ^ 2 := by
          have h1 : ∑ x ∈ Vf u h, (w u x * L u x) ^ 2 ≤ ∑ x, (w u x) ^ 2 := by
            refine (Finset.sum_le_sum fun x _ => ?_).trans
              (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => sq_nonneg _)
            rw [mul_pow]
            have : L u x ^ 2 ≤ 1 := by
              have := hL u x
              rw [sq_le_one_iff_abs_le_one]; exact this
            nlinarith [sq_nonneg (w u x)]
          nlinarith [sq_nonneg m]
  · have : ∀ z, errIncr s L Vf ocf w u (Fin.snoc h z) = 0 := fun z => by
      unfold errIncr; simp only [Fin.init_snoc, if_neg hc]
    simp only [this]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
    exact mul_nonneg hs.le (Finset.sum_nonneg fun x _ => sq_nonneg _)

end Generic

section GenericFreedman

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (L : ℕ → ι → ℝ)
  (Vf : (u : ℕ) → (Fin u → Fin s) → Finset ι) (ocf : (u : ℕ) → (Fin u → Fin s) → Fin s → Option ι)

/-- With nonnegative weights `≤ 1` and losses in `[0, 1]`, the increment is at most `s`. -/
theorem errIncr_le (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1) (w : ℕ → ι → ℝ) (hw0 : ∀ u x, 0 ≤ w u x)
    (hw1 : ∀ u x, w u x ≤ 1) (u : ℕ) (ω : Fin (u + 1) → Fin s) : errIncr s L Vf ocf w u ω ≤ s := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  unfold errIncr
  split_ifs with hc
  · simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
    have hm : 0 ≤ ∑ x, w u x * (if x ∈ Vf u (Fin.init ω) then L u x else 0) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hw0 u x) (by split_ifs <;> simp [hL0 u x])
    have hA := obs_part s L w u (ocf u (Fin.init ω) (ω (Fin.last u)))
    have hA' : ∑ x, w u x * (if ocf u (Fin.init ω) (ω (Fin.last u)) = some x then (s : ℝ) * L u x else 0) ≤ s := by
      rw [hA]
      split
      · exact hs
      · rename_i x' _
        calc w u x' * ((s : ℝ) * L u x') ≤ 1 * ((s : ℝ) * 1) := by
              apply mul_le_mul (hw1 u x') (mul_le_mul_of_nonneg_left (hL1 u x') hs)
                (mul_nonneg hs (hL0 u x')) zero_le_one
          _ = s := by ring
    linarith
  · exact hs

/-- `runV` of a budget that does not read the coins. -/
theorem runV_det {Z : Type} (v : ℕ → ℝ) : ∀ (T : ℕ) (ω : Fin T → Z),
    Pool.P0100.runV (fun u _ => v u) T ω = ∑ u ∈ Finset.range T, v u
  | 0, _ => by simp [Pool.P0100.runV]
  | T + 1, ω => by
    simp only [Pool.P0100.runV]
    rw [runV_det v T (Fin.init ω), Finset.sum_range_succ]

/-- **Freedman bound for slot-IW estimation errors.** Under i.i.d. uniform slots, for weights in `[0, 1]`, losses in
`[0, 1]` and `0 < κ ≤ 1/s`: `P(Σ errIncr − κ·s·Σ_{u<T} Σₓ (w u x)² ≥ x/κ) ≤ e^{−x}`. -/
theorem errIncr_freedman [NeZero s] (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s) (hocc : SlotLayout s Vf ocf)
    (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1) (w : ℕ → ι → ℝ) (hw0 : ∀ u x, 0 ≤ w u x)
    (hw1 : ∀ u x, w u x ≤ 1) {κ : ℝ} (hκ : 0 < κ) (hκs : κ * s ≤ 1) (T : ℕ) (x : ℝ) :
    Pool.P0092.probGe ν T (fun ω => Pool.P0092.runSum (errIncr s L Vf ocf w) T ω -
      κ * ∑ u ∈ Finset.range T, (s : ℝ) * ∑ x', (w u x') ^ 2) (x / κ) ≤ Real.exp (-x) := by
  have hL : ∀ u x, |L u x| ≤ 1 := fun u x => abs_le.mpr ⟨by linarith [hL0 u x], hL1 u x⟩
  have h := Pool.P0100.freedman_coins ν (errIncr s L Vf ocf w) (fun u _ => (s : ℝ) * ∑ x', (w u x') ^ 2) hκ
    (T := T)
    (fun u _ ω z _ _ => by
      have := errIncr_le s L Vf ocf hL0 hL1 w hw0 hw1 u (Fin.snoc ω z)
      nlinarith)
    (fun u _ ω _ => by
      simp only [hν]
      exact (errIncr_mean s L Vf ocf hocc w u ω).le)
    (fun u _ ω _ => by
      simp only [hν]
      exact errIncr_sq s L Vf ocf hocc hL w u ω) x
  simpa only [runV_det] using h

/-- With nonnegative weights and losses in `[0, 1]`, minus the increment is at most `Σₓ w u x`. -/
theorem neg_errIncr_le (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1) (w : ℕ → ι → ℝ) (hw0 : ∀ u x, 0 ≤ w u x)
    (u : ℕ) (ω : Fin (u + 1) → Fin s) : -errIncr s L Vf ocf w u ω ≤ ∑ x, w u x := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  unfold errIncr
  split_ifs with hc
  · simp only [mul_sub]
    rw [Finset.sum_sub_distrib]
    have hm : ∑ x, w u x * (if x ∈ Vf u (Fin.init ω) then L u x else 0) ≤ ∑ x, w u x :=
      Finset.sum_le_sum fun x _ => by
        split_ifs
        · nlinarith [hw0 u x, hL1 u x]
        · simp [hw0 u x]
    have hg : 0 ≤ ∑ x, w u x * (if ocf u (Fin.init ω) (ω (Fin.last u)) = some x then (s : ℝ) * L u x else 0) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hw0 u x) (by split_ifs <;> [exact mul_nonneg hs (hL0 u x); exact le_rfl])
    linarith
  · simp only [neg_zero]
    exact Finset.sum_nonneg fun x _ => hw0 u x

/-- `runSum` of the negated increments. -/
theorem runSum_neg {Z : Type} (D : (u : ℕ) → (Fin (u + 1) → Z) → ℝ) : ∀ (T : ℕ) (ω : Fin T → Z),
    Pool.P0092.runSum (fun u ω => -D u ω) T ω = -Pool.P0092.runSum D T ω
  | 0, _ => by simp [Pool.P0092.runSum]
  | T + 1, ω => by
    simp only [Pool.P0092.runSum]
    rw [runSum_neg D T (Fin.init ω)]
    ring

/-- **Freedman bound for the lower tail.** Under i.i.d. uniform slots, for nonnegative weights with `Σₓ w u x ≤ 1`,
losses in `[0, 1]` and `0 < κ ≤ 1`: `P(−Σ errIncr − κ·s·Σ_{u<T} Σₓ (w u x)² ≥ x/κ) ≤ e^{−x}`. -/
theorem errIncr_freedman_lower [NeZero s] (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s)
    (hocc : SlotLayout s Vf ocf) (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1) (w : ℕ → ι → ℝ)
    (hw0 : ∀ u x, 0 ≤ w u x) (hwsum : ∀ u, ∑ x, w u x ≤ 1) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (T : ℕ) (x : ℝ) :
    Pool.P0092.probGe ν T (fun ω => -Pool.P0092.runSum (errIncr s L Vf ocf w) T ω -
      κ * ∑ u ∈ Finset.range T, (s : ℝ) * ∑ x', (w u x') ^ 2) (x / κ) ≤ Real.exp (-x) := by
  have hL : ∀ u x, |L u x| ≤ 1 := fun u x => abs_le.mpr ⟨by linarith [hL0 u x], hL1 u x⟩
  have h := Pool.P0100.freedman_coins ν (fun u ω => -errIncr s L Vf ocf w u ω)
    (fun u _ => (s : ℝ) * ∑ x', (w u x') ^ 2) hκ (T := T)
    (fun u _ ω z _ _ => by
      have h1 := neg_errIncr_le s L Vf ocf hL0 hL1 w hw0 u (Fin.snoc ω z)
      have h2 := hwsum u
      nlinarith)
    (fun u _ ω _ => by
      simp only [hν]
      have := errIncr_mean s L Vf ocf hocc w u ω
      have h' : ∑ z : Fin s, 1 / (s : ℝ) * -errIncr s L Vf ocf w u (Fin.snoc ω z) =
          -∑ z : Fin s, 1 / (s : ℝ) * errIncr s L Vf ocf w u (Fin.snoc ω z) := by
        rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun z _ => by ring
      rw [h', this]; simp)
    (fun u _ ω _ => by
      simp only [hν, neg_sq]
      exact errIncr_sq s L Vf ocf hocc hL w u ω) x
  simpa only [runV_det, runSum_neg] using h

end GenericFreedman

section FOFreedman

open Pool.P0095

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ)
  (occ : Finset ι → Fin s → Option ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

theorem sum_wIv_sq (c : ι) (a b u : ℕ) : ∑ x, (wIv c a b u x) ^ 2 = if a ≤ u ∧ u < b then 1 else 0 := by
  unfold wIv
  have : ∀ x, (if x = c ∧ a ≤ u ∧ u < b then (1 : ℝ) else 0) ^ 2 =
      if x = c then (if a ≤ u ∧ u < b then 1 else 0) else 0 := by
    intro x; by_cases hx : x = c <;> by_cases hu : a ≤ u ∧ u < b <;> simp [hx, hu]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sum_range_ind {a b T : ℕ} (hbT : b ≤ T) :
    ∑ u ∈ Finset.range T, (if a ≤ u ∧ u < b then (1 : ℝ) else 0) = ((b - a : ℕ) : ℝ) := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have : (Finset.range T).filter (fun u => a ≤ u ∧ u < b) = Finset.Ico a b := by
    ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]

/-- The tuning arithmetic: with `q = √(x/(s·len))` and `κ = min (1/s) q`,
`κ·s·len + x/κ ≤ 2√(s·len·x) + 2·s·x`. -/
theorem tune_le {sR len x : ℝ} (hs : 0 < sR) (hl : 0 < len) (hx : 0 < x) :
    let κ := min (1 / sR) (Real.sqrt (x / (sR * len)))
    0 < κ ∧ κ * sR ≤ 1 ∧ κ * (sR * len) + x / κ ≤ 2 * Real.sqrt (sR * len * x) + 2 * sR * x := by
  intro κ
  set q := Real.sqrt (x / (sR * len)) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : q ^ 2 = x / (sR * len) := Real.sq_sqrt (by positivity)
  have hsq : Real.sqrt (sR * len * x) = q * (sR * len) := by
    rw [show sR * len * x = (q * (sR * len)) ^ 2 by rw [mul_pow, hq2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hκ0 : 0 < κ := lt_min (by positivity) hq0
  refine ⟨hκ0, ?_, ?_⟩
  · calc κ * sR ≤ (1 / sR) * sR := mul_le_mul_of_nonneg_right (min_le_left _ _) hs.le
      _ = 1 := by field_simp
  · rw [hsq]
    rcases le_total q (1 / sR) with h | h
    · have hk : κ = q := min_eq_right h
      rw [hk]
      have hxq : x / q = q * (sR * len) := by
        rw [div_eq_iff hq0.ne']
        have : x = q ^ 2 * (sR * len) := by rw [hq2]; field_simp
        rw [this]; ring
      rw [hxq]
      have : 0 ≤ 2 * sR * x := by positivity
      linarith
    · have hk : κ = 1 / sR := min_eq_left h
      rw [hk]
      have hlen : len ≤ sR * x := by
        have h2 : (1 / sR) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by positivity) h 2
        rw [hq2, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)] at h2
        nlinarith
      have h3 : 1 / sR * (sR * len) = len := by field_simp
      have h4 : x / (1 / sR) = sR * x := by field_simp
      rw [h3, h4]
      have : 0 ≤ q * (sR * len) := by positivity
      linarith

/-- **Length-dependent concentration for one copy** (Freedman). For a copy `c` and units `[a, b)` with
`a < b ≤ T` and `x > 0`: the weight of the slot sequences without overflow before `T` on which `c`'s realized
estimate over `[a, b)` exceeds its true loss over the units of `[a, b)` in which it is present by at least
`2√(s·(b−a)·x) + 2s·x` is at most `e^{−x}`. Losses in `[0, 1]`. -/
theorem fo_interval_freedman [NeZero s] (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s) (hocc : SlotSum s occ)
    (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1) (c : ι) {a b T : ℕ} (hab : a < b) (hbT : b ≤ T)
    {x : ℝ} (hx : 0 < x) :
    ∑ ω : Fin T → Fin s, Pool.P0092.wgt ν ω *
      (if (∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) u).card ≤ s) ∧
          2 * Real.sqrt (s * ((b - a : ℕ) : ℝ) * x) + 2 * s * x ≤
            (Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) c b -
              Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) c a) -
            ∑ u ∈ Ico a b, (if c ∈ Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) u then L u c else 0)
        then 1 else 0) ≤ Real.exp (-x) := by
  have hs : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne s))
  have hl : (0 : ℝ) < ((b - a : ℕ) : ℝ) := by exact_mod_cast (show 0 < b - a by omega)
  obtain ⟨hκ0, hκs, hκ⟩ := tune_le hs hl hx
  set κ := min (1 / (s : ℝ)) (Real.sqrt (x / (s * ((b - a : ℕ) : ℝ)))) with hκdef
  have hF := errIncr_freedman s L (foV E thr0 θ R K D Lv Bt lev s L occ ωs φ)
    (fun u h => occ (foV E thr0 θ R K D Lv Bt lev s L occ ωs φ u h)) ν hν
    (slotLayout_fo E thr0 θ R K D Lv Bt lev s L occ ωs φ hocc) hL0 hL1 (wIv c a b)
    (fun u x => by unfold wIv; split_ifs <;> norm_num) (fun u x => by unfold wIv; split_ifs <;> norm_num)
    hκ0 hκs T x
  have hV : ∑ u ∈ Finset.range T, (s : ℝ) * ∑ x', (wIv c a b u x') ^ 2 = s * ((b - a : ℕ) : ℝ) := by
    simp only [sum_wIv_sq]
    rw [← Finset.mul_sum, sum_range_ind hbT]
  rw [hV] at hF
  refine le_trans ?_ hF
  unfold Pool.P0092.probGe
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (Pool.P0092.wgt_nonneg ν ω)
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; apply h2
    have hrs := runSum_foErr_eq E thr0 θ R K D Lv Bt lev s L occ ωs φ (wIv c a b) T ω h1.1
    rw [sum_wIv c hbT, Finset.sum_sub_distrib, Finset.sum_Ico_sub _ hab.le] at hrs
    simp only [foErr] at hrs
    dsimp only
    rw [hrs]
    have := h1.2
    linarith
  · norm_num
  · exact le_rfl

/-- The tuning arithmetic for the lower tail: with `q = √(x/(s·len))` and `κ = min 1 q`,
`κ·s·len + x/κ ≤ 2√(s·len·x) + 2·x`. -/
theorem tune_le_one {sR len x : ℝ} (hs : 0 < sR) (hl : 0 < len) (hx : 0 < x) :
    let κ := min 1 (Real.sqrt (x / (sR * len)))
    0 < κ ∧ κ ≤ 1 ∧ κ * (sR * len) + x / κ ≤ 2 * Real.sqrt (sR * len * x) + 2 * x := by
  intro κ
  set q := Real.sqrt (x / (sR * len)) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : q ^ 2 = x / (sR * len) := Real.sq_sqrt (by positivity)
  have hsq : Real.sqrt (sR * len * x) = q * (sR * len) := by
    rw [show sR * len * x = (q * (sR * len)) ^ 2 by rw [mul_pow, hq2]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have hκ0 : 0 < κ := lt_min (by norm_num) hq0
  refine ⟨hκ0, min_le_left _ _, ?_⟩
  rw [hsq]
  rcases le_total q 1 with h | h
  · have hk : κ = q := min_eq_right h
    rw [hk]
    have hxq : x / q = q * (sR * len) := by
      rw [div_eq_iff hq0.ne']
      have : x = q ^ 2 * (sR * len) := by rw [hq2]; field_simp
      rw [this]; ring
    rw [hxq]
    linarith
  · have hk : κ = 1 := min_eq_left h
    rw [hk]
    have hlen : sR * len ≤ x := by
      have h2 : (1 : ℝ) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
      rw [hq2, one_pow, le_div_iff₀ (by positivity)] at h2
      linarith
    have : 0 ≤ q * (sR * len) := by positivity
    simp only [one_mul, div_one]
    linarith

/-- **Length-dependent concentration for one copy, lower tail.** For a copy `c` and units `[a, b)` with
`a < b ≤ T` and `x > 0`: the weight of the slot sequences without overflow before `T` on which `c`'s true loss over
the units of `[a, b)` in which it is present exceeds its realized estimate over `[a, b)` by at least
`2√(s·(b−a)·x) + 2x` is at most `e^{−x}`. Losses in `[0, 1]`. -/
theorem fo_interval_freedman_lower [NeZero s] (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s)
    (hocc : SlotSum s occ) (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1) (c : ι) {a b T : ℕ} (hab : a < b)
    (hbT : b ≤ T) {x : ℝ} (hx : 0 < x) :
    ∑ ω : Fin T → Fin s, Pool.P0092.wgt ν ω *
      (if (∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) u).card ≤ s) ∧
          2 * Real.sqrt (s * ((b - a : ℕ) : ℝ) * x) + 2 * x ≤
            ∑ u ∈ Ico a b, (if c ∈ Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) u then L u c else 0) -
            (Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) c b -
              Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) c a)
        then 1 else 0) ≤ Real.exp (-x) := by
  have hs : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne s))
  have hl : (0 : ℝ) < ((b - a : ℕ) : ℝ) := by exact_mod_cast (show 0 < b - a by omega)
  obtain ⟨hκ0, hκ1, hκ⟩ := tune_le_one hs hl hx
  set κ := min 1 (Real.sqrt (x / (s * ((b - a : ℕ) : ℝ)))) with hκdef
  have hF := errIncr_freedman_lower s L (foV E thr0 θ R K D Lv Bt lev s L occ ωs φ)
    (fun u h => occ (foV E thr0 θ R K D Lv Bt lev s L occ ωs φ u h)) ν hν
    (slotLayout_fo E thr0 θ R K D Lv Bt lev s L occ ωs φ hocc) hL0 hL1 (wIv c a b)
    (fun u x => by unfold wIv; split_ifs <;> norm_num)
    (fun u => le_trans (Finset.sum_le_sum fun x _ => le_abs_self _) (wIv_abs c a b u))
    hκ0 hκ1 T x
  have hV : ∑ u ∈ Finset.range T, (s : ℝ) * ∑ x', (wIv c a b u x') ^ 2 = s * ((b - a : ℕ) : ℝ) := by
    simp only [sum_wIv_sq]
    rw [← Finset.mul_sum, sum_range_ind hbT]
  rw [hV] at hF
  refine le_trans ?_ hF
  unfold Pool.P0092.probGe
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (Pool.P0092.wgt_nonneg ν ω)
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; apply h2
    have hrs := runSum_foErr_eq E thr0 θ R K D Lv Bt lev s L occ ωs φ (wIv c a b) T ω h1.1
    rw [sum_wIv c hbT, Finset.sum_sub_distrib, Finset.sum_Ico_sub _ hab.le] at hrs
    simp only [foErr] at hrs
    dsimp only
    rw [hrs]
    have := h1.2
    linarith
  · norm_num
  · exact le_rfl

end FOFreedman

section Forced

open Pool.P0095 Pool.P0065 Pool.P0052

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ)

/-- **Forced runs overflow at most one slot later than the actual run.** The start-pool members of the forced
copy-last run of a never-sampled copy `c` are the actual (entry-order) run's members plus at most `c`. -/
theorem Vat_forced_card_le {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (y : ℕ → Fin s) (u : ℕ) :
    (Vat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y u).card ≤
      (Vat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u).card + 1 := by
  classical
  have hs : AgreeOff c (forceS ωs c) ωs := fun x hx => by simp [forceS, Function.update_of_ne hx]
  have hP : (fun r ℓ => ((foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y
      u).pools r ℓ).erase c) = (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u).pools := by
    funext r ℓ
    rw [(fo_forced_erase E thr0 θ R K D Lv Bt lev s L hc φ y u).1 r ℓ,
      foRun_free_eq E thr0 θ R K D Lv Bt lev s L hc φ y u]
  have hV : (Vat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y u).erase c =
      Vat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u := by
    unfold Vat
    rw [members_erase]
    congr 1
    funext r ℓ
    rw [startPools_erase c (forceS ωs c) ωs hs hc, hP]
  have := Finset.pred_card_le_card_erase (s := Vat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c)
    (forceF K φ c) y u) (a := c)
  rw [hV] at this
  omega

end Forced

end Pool.P0115
