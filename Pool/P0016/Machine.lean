import Pool.P0016.Potential
import Pool.P0012.Potential

open Real Finset Pool.P0001 Pool.P0012
open scoped ENNReal NNReal

/-!
# EXP3 as a `Pool.P0001.Machine` with finitely many states, and its regret

State: a vector of `n` integer counts in `{0, …, D}` (`St n D = Fin n → Fin (D+1)`), so the state set has
`(D+1)^n` elements and the memory is `n log₂ (D+1)` bits (`memBits_machine`).

* Arm law (`actPMF`): Hedge on the counts, `p(j) = soft η (counts) j ∝ exp(-η · count_j)`.
* Transition (`nextPMF`): if the pulled arm `a` has loss `0`, the state does not change. If it has loss
  `1`, then `X` is added to `count_a`, where `X` is the unbiased randomized rounding of `1/p(a)`
  (`⌊1/p(a)⌋` or `⌊1/p(a)⌋ + 1`, with mean `1/p(a)`, `round_moments`). Then all counts are shifted so the
  minimum is `0` and capped at `D` (`normalize`). Hedge is invariant under the shift. The cap costs at most
  `n e^{-ηD}/η` per round in the potential (`phi_cap`).
* `stepExp_le`: the one-step drift of the potential `phi η counts i` (P0012 notation).
* `regret_le`: for every oblivious loss sequence and every horizon `T`,
  `regret ≤ log n / η + T (5 η n / 8 + n e^{-ηD} / η)` (P0001 regret).
* `regret_tuned`: with `η = etaOf n T = √((1 + log n)/(n T))` and `D = capOf n T`,
  `regret ≤ 2 √(n T (1 + log n)) + 1`; `memBits_tuned`: memory `≤ n log₂ ((nT)² + 2)` bits.
-/

namespace Pool.P0016

variable {n : ℕ} [NeZero n] (D : ℕ) (η : ℝ)

/-- States: capped, shifted counts. -/
abbrev St (n D : ℕ) := Fin n → Fin (D + 1)

/-- Counts as reals. -/
def cnt (s : St n D) : Fin n → ℝ := fun j => ((s j : ℕ) : ℝ)

/-- The arm law: Hedge on the counts. -/
noncomputable def actPMF (s : St n D) : PMF (Fin n) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (soft η (cnt D s) j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => soft_nonneg η _ j), sum_soft]; simp)

theorem actPMF_toReal (s : St n D) (j : Fin n) :
    (actPMF D η s j).toReal = soft η (cnt D s) j := by
  simp [actPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (soft_nonneg η _ j)]

/-- Normalization: add `X` to arm `a`, shift so the minimum is `0`, cap at `D`. -/
noncomputable def normalize (s : St n D) (a : Fin n) (X : ℕ) : St n D := fun j =>
  let v : Fin n → ℕ := fun k => (s k : ℕ) + if k = a then X else 0
  let m : ℕ := Finset.univ.inf' Finset.univ_nonempty v
  ⟨min (v j - m) D, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Expectation under a pushforward PMF, on finite types. -/
theorem sum_map_toReal {α β : Type} [Fintype α] [Fintype β] (p : PMF α) (φ : α → β) (F : β → ℝ) :
    ∑ b, ((p.map φ) b).toReal * F b = ∑ a, (p a).toReal * F (φ a) := by
  classical
  have : ∀ b, ((p.map φ) b).toReal = ∑ a, (p a).toReal * (if b = φ a then 1 else 0) := by
    intro b
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    · intro a _; split_ifs <;> simp [PMF.apply_ne_top]
  simp only [this, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Finset.sum_ite_eq']

/-- A Bernoulli law on `Bool` with real parameter `r ∈ [0,1]` (`true` with probability `r`). -/
noncomputable def bern (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : PMF Bool :=
  PMF.ofFintype (fun z => ENNReal.ofReal (if z then r else 1 - r)) (by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ite_true, ite_false]
    rw [← ENNReal.ofReal_add h0 (by linarith)]; simp)

theorem bern_toReal (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) (z : Bool) :
    (bern r h0 h1 z).toReal = if z then r else 1 - r := by
  simp only [bern, PMF.ofFintype_apply]
  rw [ENNReal.toReal_ofReal]; cases z <;> simp <;> linarith

/-- Fractional part of `y ≥ 0`. -/
noncomputable def frac (y : ℝ) : ℝ := y - ⌊y⌋₊

theorem frac_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ frac y := by
  unfold frac; linarith [Nat.floor_le hy]

theorem frac_le_one (y : ℝ) : frac y ≤ 1 := by
  unfold frac; linarith [Nat.lt_floor_add_one y]

/-- The rounded increment: `⌊y⌋` or `⌊y⌋ + 1`. -/
noncomputable def incr (y : ℝ) (z : Bool) : ℕ := ⌊y⌋₊ + if z then 1 else 0

/-- Mean and second moment of the randomized rounding. -/
theorem round_moments {y : ℝ} (hy : 0 ≤ y) :
    ∑ z, (bern (frac y) (frac_nonneg hy) (frac_le_one y) z).toReal * (incr y z : ℝ) = y ∧
    ∑ z, (bern (frac y) (frac_nonneg hy) (frac_le_one y) z).toReal * (incr y z : ℝ) ^ 2
      ≤ y ^ 2 + 1 / 4 := by
  simp only [Fintype.sum_bool, bern_toReal, incr, Bool.false_eq_true, ite_true, ite_false]
  push_cast
  have hf0 := frac_nonneg hy
  have hf1 := frac_le_one y
  set f := frac y
  have hy' : y = (⌊y⌋₊ : ℝ) + f := by simp only [f, frac]; ring
  set k := ((⌊y⌋₊ : ℕ) : ℝ)
  constructor
  · rw [hy']; ring
  · rw [hy']; nlinarith [sq_nonneg (f - 1/2)]

/-- Next-state law: after a loss on arm `a`, add a randomized rounding of `1/p(a)` to its count. -/
noncomputable def nextPMF (s : St n D) (a : Fin n) (b : Bool) : PMF (St n D) :=
  if b then
    let y := 1 / soft η (cnt D s) a
    (bern (frac y) (frac_nonneg (by have := soft_nonneg η (cnt D s) a; positivity))
      (frac_le_one y)).map fun z => normalize D s a (incr y z)
  else PMF.pure s

/-- The EXP3 machine with capped shifted counts. -/
noncomputable def machine : Machine n where
  State := St n D
  init := PMF.pure fun _ => 0
  act _ s := actPMF D η s
  next _ s a b := nextPMF D η s a b

theorem cnt_normalize (s : St n D) (a : Fin n) (X : ℕ) :
    ∃ m : ℝ, (∃ j0, cnt D s j0 + (if j0 = a then (X : ℝ) else 0) = m) ∧
      (∀ j, m ≤ cnt D s j + if j = a then (X : ℝ) else 0) ∧
      cnt D (normalize D s a X) = fun j => min (cnt D s j + (if j = a then (X : ℝ) else 0) - m) D := by
  set v : Fin n → ℕ := fun k => (s k : ℕ) + if k = a then X else 0 with hv
  set m : ℕ := Finset.univ.inf' Finset.univ_nonempty v with hm
  have hle : ∀ j, m ≤ v j := fun j => Finset.inf'_le _ (Finset.mem_univ j)
  obtain ⟨j0, -, hj0⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty v
  have hcast : ∀ j, ((v j : ℕ) : ℝ) = cnt D s j + if j = a then (X : ℝ) else 0 := by
    intro j; simp only [v, cnt]; push_cast; split_ifs <;> simp
  refine ⟨(m : ℝ), ⟨j0, by rw [← hcast, ← hj0]⟩, fun j => by rw [← hcast]; exact_mod_cast hle j, ?_⟩
  funext j
  have hvj : (s j : ℕ) + (if j = a then X else 0) = v j := rfl
  simp only [cnt, normalize]
  rw [← hm, hvj, Nat.cast_min, Nat.cast_sub (hle j), hcast]
  rfl

/-- Potential after one update, pathwise. -/
theorem phi_normalize_le {η : ℝ} (hη : 0 < η) (s : St n D) (a i : Fin n) (X : ℕ) :
    phi η (cnt D (normalize D s a X)) i ≤
      phi η (cnt D s) i - soft η (cnt D s) a * X + (if a = i then (X : ℝ) else 0) +
        η / 2 * soft η (cnt D s) a * (X : ℝ) ^ 2 + n * exp (-η * D) / η := by
  obtain ⟨m, ⟨j0, hj0⟩, hmle, heq⟩ := cnt_normalize D s a X
  rw [heq]
  set vr : Fin n → ℝ := fun j => cnt D s j + if j = a then (X : ℝ) else 0
  have h1 := phi_cap hη (fun j => vr j - m) (fun j => by simp only [vr]; linarith [hmle j]) j0
    (by simp only [vr]; linarith) (Nat.cast_nonneg D) i
  have h2 := phi_sub_const hη vr m i
  have h3 := phi_step hη (cnt D s) a i (Nat.cast_nonneg X)
  simp only [vr] at h1 h2
  linarith

theorem soft_pos (c : Fin n → ℝ) (j : Fin n) : 0 < soft η c j :=
  div_pos (exp_pos _) (W_pos η c)

/-- Inner expectation after pulling arm `a` in state `s`. -/
theorem inner_le {η : ℝ} (hη : 0 < η) (s : St n D) (a i : Fin n) (b : Bool) :
    ∑ s', (nextPMF D η s a b s').toReal * phi η (cnt D s') i ≤
      phi η (cnt D s) i + if b then
        (-1 + (if a = i then 1 / soft η (cnt D s) a else 0) +
          η / 2 * (1 / soft η (cnt D s) a + soft η (cnt D s) a / 4) + n * exp (-η * D) / η)
      else 0 := by
  classical
  cases b with
  | false =>
    simp only [nextPMF, Bool.false_eq_true, ite_false, add_zero]
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [PMF.pure_apply, hb]
    · simp
  | true =>
    simp only [nextPMF, ite_true]
    rw [sum_map_toReal]
    set q := soft η (cnt D s) a with hq
    have hqpos : 0 < q := soft_pos η (cnt D s) a
    set y := 1 / q with hy
    have hy0 : 0 ≤ y := by positivity
    obtain ⟨hm1, hm2⟩ := round_moments hy0
    set B := bern (frac y) (frac_nonneg hy0) (frac_le_one y)
    have hpt : ∀ z, (B z).toReal * phi η (cnt D (normalize D s a (incr y z))) i ≤
        (B z).toReal * (phi η (cnt D s) i - q * (incr y z : ℝ) +
          (if a = i then (incr y z : ℝ) else 0) + η / 2 * q * (incr y z : ℝ) ^ 2 +
          n * exp (-η * D) / η) :=
      fun z => mul_le_mul_of_nonneg_left (phi_normalize_le D hη s a i _) ENNReal.toReal_nonneg
    refine (Finset.sum_le_sum fun z _ => hpt z).trans ?_
    have hB1 : ∑ z, (B z).toReal = 1 := by
      simp only [B, Fintype.sum_bool, bern_toReal, ite_true, Bool.false_eq_true, ite_false]; ring
    have hsplit : ∑ z, (B z).toReal * (phi η (cnt D s) i - q * (incr y z : ℝ) +
          (if a = i then (incr y z : ℝ) else 0) + η / 2 * q * (incr y z : ℝ) ^ 2 +
          n * exp (-η * D) / η) =
        phi η (cnt D s) i * ∑ z, (B z).toReal - q * ∑ z, (B z).toReal * (incr y z : ℝ) +
          (if a = i then ∑ z, (B z).toReal * (incr y z : ℝ) else 0) +
          η / 2 * q * ∑ z, (B z).toReal * (incr y z : ℝ) ^ 2 +
          n * exp (-η * D) / η * ∑ z, (B z).toReal := by
      simp only [Fintype.sum_bool]; split_ifs <;> ring
    rw [hsplit, hB1, hm1]
    have hqy : q * y = 1 := by rw [hy]; field_simp
    have hsq : η / 2 * q * ∑ z, (B z).toReal * (incr y z : ℝ) ^ 2 ≤ η / 2 * q * (y ^ 2 + 1 / 4) :=
      mul_le_mul_of_nonneg_left hm2 (by positivity)
    have hqy2 : η / 2 * q * (y ^ 2 + 1 / 4) = η / 2 * (y + q / 4) := by
      rw [hy]; field_simp
    split_ifs <;> nlinarith [hqy]

theorem ite_bool_eq (b : Bool) (x : ℝ) : (if b then x else 0) = (b.toNat : ℝ) * x := by
  cases b <;> simp

/-- **One-step drift** of the EXP3 potential for comparator `i`. -/
theorem stepExp_le {η : ℝ} (hη : 0 < η) (ℓ : LossSeq n) (t : ℕ) (s : St n D) (i : Fin n) :
    stepExp (machine D η) ℓ t s (fun s' => phi η (cnt D s') i) ≤
      phi η (cnt D s) i - stateLoss (machine D η) ℓ t s + ((ℓ t i).toNat : ℝ) +
        (5 * η * n / 8 + n * exp (-η * D) / η) := by
  set q := soft η (cnt D s) with hq
  set Φ := phi η (cnt D s) i
  set err := (n : ℝ) * exp (-η * D) / η
  have herr : 0 ≤ err := by positivity
  set bb : Fin n → ℝ := fun a => ((ℓ t a).toNat : ℝ)
  have hb0 : ∀ a, 0 ≤ bb a := fun a => by positivity
  have hb1 : ∀ a, bb a ≤ 1 := fun a => by simp only [bb]; cases ℓ t a <;> simp
  have hq0 : ∀ a, 0 < q a := fun a => soft_pos η (cnt D s) a
  have hq1 : ∀ a, q a ≤ 1 := fun a => soft_le_one η (cnt D s) a
  have hstep : stepExp (machine D η) ℓ t s (fun s' => phi η (cnt D s') i) ≤
      ∑ a, q a * (Φ + bb a * (-1 + (if a = i then 1 / q a else 0) +
        η / 2 * (1 / q a + q a / 4) + err)) := by
    unfold stepExp
    refine Finset.sum_le_sum fun a _ => ?_
    have h := inner_le D hη s a i (ℓ t a)
    rw [ite_bool_eq] at h
    simp only [machine, actPMF_toReal]
    exact mul_le_mul_of_nonneg_left h (hq0 a).le
  have hstate : stateLoss (machine D η) ℓ t s = ∑ a, q a * bb a := by
    simp [stateLoss, machine, actPMF_toReal, q, bb]
  have hsumq : ∑ a, q a = 1 := sum_soft η _
  have hexpand : ∑ a, q a * (Φ + bb a * (-1 + (if a = i then 1 / q a else 0) +
        η / 2 * (1 / q a + q a / 4) + err)) =
      Φ - ∑ a, q a * bb a + bb i + η / 2 * ∑ a, bb a * (1 + q a ^ 2 / 4) + err * ∑ a, q a * bb a := by
    have e1 : ∀ a, q a * (Φ + bb a * (-1 + (if a = i then 1 / q a else 0) +
        η / 2 * (1 / q a + q a / 4) + err)) =
        q a * Φ - q a * bb a + (if a = i then bb a else 0) + η / 2 * (bb a * (1 + q a ^ 2 / 4)) +
          err * (q a * bb a) := by
      intro a
      have := (hq0 a).ne'
      split_ifs <;> field_simp <;> ring
    simp only [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hsumq, one_mul]
  have hvar : ∑ a, bb a * (1 + q a ^ 2 / 4) ≤ 5 * (n : ℝ) / 4 := by
    calc ∑ a, bb a * (1 + q a ^ 2 / 4) ≤ ∑ _a : Fin n, (5 / 4 : ℝ) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have : q a ^ 2 ≤ 1 := by nlinarith [hq0 a, hq1 a]
          nlinarith [hb0 a, hb1 a]
      _ = 5 * (n : ℝ) / 4 := by simp; ring
  have hloss : ∑ a, q a * bb a ≤ 1 := by
    calc ∑ a, q a * bb a ≤ ∑ a, q a := Finset.sum_le_sum fun a _ => by nlinarith [hq0 a, hb1 a]
      _ = 1 := hsumq
  rw [hstate]
  refine hstep.trans ?_
  rw [hexpand]
  have : err * ∑ a, q a * bb a ≤ err := by nlinarith
  have : η / 2 * ∑ a, bb a * (1 + q a ^ 2 / 4) ≤ 5 * η * n / 8 := by nlinarith
  simp only [bb] at *
  linarith

theorem expect_const {n : ℕ} (M : Machine n) (ℓ : LossSeq n) (t : ℕ) (c : ℝ) :
    expect M ℓ t (fun _ => c) = c := by
  unfold Pool.P0012.expect
  rw [← Finset.sum_mul, ← ENNReal.toReal_sum (fun s _ => PMF.apply_ne_top _ s),
    ← tsum_fintype (L := .unconditional _) (fun s => M.stateDist ℓ t s), PMF.tsum_coe,
    ENNReal.toReal_one, one_mul]

theorem sum_pure_toReal {α : Type} [Fintype α] (x : α) (f : α → ℝ) :
    ∑ s, ((PMF.pure x) s).toReal * f s = f x := by
  classical
  rw [Finset.sum_eq_single x]
  · simp
  · intro b _ hb; simp [PMF.pure_apply, hb]
  · simp

/-- The EXP3 machine does not use the round number. -/
theorem machine_isHomogeneous : (machine D η : Machine n).IsHomogeneous :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- **Regret of the EXP3 machine**: for every loss sequence and horizon `T`,
`regret ≤ log n / η + T (5 η n / 8 + n e^{-η D} / η)`. -/
theorem regret_le {η : ℝ} (hη : 0 < η) (ℓ : LossSeq n) (T : ℕ) :
    regret (machine D η) ℓ T ≤
      log n / η + T * (5 * η * n / 8 + n * exp (-η * D) / η) := by
  refine regret_le_of_potential (machine D η) ℓ (fun i _ s => phi η (cnt D s) i)
    (fun _ _ _ => 5 * η * n / 8 + n * exp (-η * D) / η) T _
    (fun i s => phi_nonneg hη _ i) (fun i t _ s => stepExp_le D hη ℓ t s i) ?_
  intro i
  rw [Finset.sum_congr rfl fun t _ => expect_const (machine D η) ℓ t _]
  have h0 : expect (machine D η) ℓ 0 (fun s => phi η (cnt D s) i) = log n / η := by
    have hz : cnt D (fun _ : Fin n => (0 : Fin (D + 1))) = fun _ => 0 := by funext j; simp [cnt]
    rw [← phi_zero η hη i, ← hz]
    exact sum_pure_toReal (fun _ : Fin n => (0 : Fin (D + 1))) _
  rw [h0]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact le_rfl

/-- Memory of the EXP3 machine: `n log₂ (D + 1)` bits. -/
theorem memBits_machine : (machine D η : Machine n).memBits = n * Real.logb 2 (D + 1) := by
  have hc : Fintype.card (machine D η : Machine n).State = (D + 1) ^ n := by
    show Fintype.card (Fin n → Fin (D + 1)) = (D + 1) ^ n
    simp
  rw [Machine.memBits, hc]
  push_cast
  rw [Real.logb_pow]

/-- Tuned learning rate. -/
noncomputable def etaOf (n T : ℕ) : ℝ := Real.sqrt ((1 + Real.log n) / (n * T))

/-- Tuned cap. -/
noncomputable def capOf (n T : ℕ) : ℕ := ⌈Real.log (n * T / etaOf n T) / etaOf n T⌉₊

theorem etaOf_pos {T : ℕ} (hT : 1 ≤ T) : 0 < etaOf n T := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  unfold etaOf
  apply Real.sqrt_pos.mpr
  apply div_pos (by linarith) (by positivity)

/-- **Tuned EXP3**: regret at most `2 √(n T (1 + log n)) + 1`. -/
theorem regret_tuned {T : ℕ} (hT : 1 ≤ T) (ℓ : LossSeq n) :
    regret (machine (capOf n T) (etaOf n T)) ℓ T ≤ 2 * Real.sqrt (n * T * (1 + Real.log n)) + 1 := by
  set η := etaOf n T with hηdef
  have hη : 0 < η := etaOf_pos hT
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  have hnT : 0 < (n : ℝ) * T := by positivity
  set L := 1 + Real.log n
  have hL : 0 < L := by positivity
  -- η² = L / (nT)
  have hη2 : η ^ 2 = L / (n * T) := by
    rw [hηdef, etaOf, Real.sq_sqrt (by positivity)]
  -- the cap makes the truncation term at most 1
  have hcap : (T : ℝ) * (n * exp (-η * (capOf n T : ℕ)) / η) ≤ 1 := by
    have hD : Real.log (n * T / η) / η ≤ (capOf n T : ℝ) := Nat.le_ceil _
    have h1 : Real.log (n * T / η) ≤ η * (capOf n T : ℝ) := by
      rw [div_le_iff₀ hη] at hD; linarith
    have h2 : n * T / η ≤ exp (η * (capOf n T : ℝ)) := by
      calc n * T / η = exp (Real.log (n * T / η)) := (exp_log (by positivity)).symm
        _ ≤ exp (η * (capOf n T : ℝ)) := exp_le_exp.mpr h1
    have h3 : exp (-η * (capOf n T : ℕ)) = 1 / exp (η * (capOf n T : ℝ)) := by
      rw [neg_mul, exp_neg, one_div]
    rw [h3]
    have hpos : 0 < exp (η * (capOf n T : ℝ)) := exp_pos _
    rw [show (T : ℝ) * (n * (1 / exp (η * (capOf n T : ℝ))) / η) =
      (n * T / η) / exp (η * (capOf n T : ℝ)) by field_simp]
    rw [div_le_one hpos]; exact h2
  have hmain := regret_le (capOf n T) hη ℓ T
  -- log n / η + 5 η n T / 8 ≤ L/η + η n T = 2 √(nT L)
  have hsq : Real.sqrt (n * T * L) = η * (n * T) := by
    have : (n : ℝ) * T * L = (η * (n * T)) ^ 2 := by
      rw [mul_pow, hη2]; field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  have hLη : L / η = η * (n * T) := by
    field_simp; rw [hη2]; field_simp
  have hA : Real.log n / η ≤ L / η := div_le_div_of_nonneg_right (by linarith) hη.le
  have hB : (T : ℝ) * (5 * η * n / 8) ≤ η * (n * T) := by nlinarith
  calc regret (machine (capOf n T) η) ℓ T
      ≤ Real.log n / η + T * (5 * η * n / 8 + n * exp (-η * (capOf n T : ℕ)) / η) := hmain
    _ = Real.log n / η + T * (5 * η * n / 8) + T * (n * exp (-η * (capOf n T : ℕ)) / η) := by ring
    _ ≤ L / η + η * (n * T) + 1 := by linarith
    _ = 2 * Real.sqrt (n * T * L) + 1 := by rw [hLη, hsq]; ring

theorem capOf_le {T : ℕ} (hT : 1 ≤ T) : (capOf n T : ℝ) ≤ ((n : ℝ) * T) ^ 2 + 1 := by
  set η := etaOf n T with hηdef
  have hη : 0 < η := etaOf_pos hT
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hnT : 0 < (n : ℝ) * T := by positivity
  have hη2 : η ^ 2 = (1 + Real.log n) / (n * T) := by
    rw [hηdef, etaOf, Real.sq_sqrt (by have := Real.log_nonneg hn; positivity)]
  set x := Real.log (n * T / η) / η
  have hx : x ≤ ((n : ℝ) * T) ^ 2 := by
    have h1 : Real.log (n * T / η) ≤ n * T / η := by
      have := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) * T / η by positivity); linarith
    have h2 : x ≤ n * T / η ^ 2 := by
      simp only [x]; rw [div_le_iff₀ hη]
      calc Real.log (n * T / η) ≤ n * T / η := h1
        _ = n * T / η ^ 2 * η := by field_simp
    have h3 : (n : ℝ) * T / η ^ 2 ≤ ((n : ℝ) * T) ^ 2 := by
      rw [hη2, div_div_eq_mul_div, div_le_iff₀ (by have := Real.log_nonneg hn; positivity)]
      have := Real.log_nonneg hn
      nlinarith [sq_nonneg ((n : ℝ) * T)]
    linarith
  have hceil : (capOf n T : ℝ) ≤ max x 0 + 1 := by
    have h := Nat.ceil_lt_add_one (le_max_right x 0)
    have hm : ⌈x⌉₊ ≤ ⌈max x 0⌉₊ := Nat.ceil_mono (le_max_left x 0)
    have : (capOf n T : ℝ) ≤ (⌈max x 0⌉₊ : ℝ) := by exact_mod_cast hm
    linarith
  have : max x 0 ≤ ((n : ℝ) * T) ^ 2 := max_le hx (by positivity)
  linarith

/-- Memory of the tuned EXP3 machine: at most `n log₂ ((nT)² + 2)` bits. -/
theorem memBits_tuned {T : ℕ} (hT : 1 ≤ T) :
    (machine (capOf n T) (etaOf n T) : Machine n).memBits ≤ n * Real.logb 2 (((n : ℝ) * T) ^ 2 + 2) := by
  rw [memBits_machine]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
  apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
  linarith [capOf_le (n := n) hT]

end Pool.P0016
