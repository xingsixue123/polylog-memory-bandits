import Pool.P0089.Hedge

/-!
# A finite-state implementation of P0089's dyadic-specialist learner

P0089 analyses a sleeping Hedge over specialists `(copy, level, aligned block)` whose renormalisation is
perturbed by `exp (ρ t)`, and CLAIMS that a machine storing integer losses and a rounded log-normaliser runs it.
This file proves that claim, abstractly (no pools, no machine type).

Data, for presence sets `pr u` (copies present at round `u`) and integer losses `b u f`:
* a global grid index `kL u` (the cumulative log-normaliser is `ε · kL u`);
* per copy and level `ℓ`: `lw u f ℓ = (C, k)`, the copy's integer loss since the level-`ℓ` specialist woke, and
  the grid index at its wake.
The machine weight is `mw u f ℓ = exp (-η C + ε (kL u - k))`. The recursion `Rec` (the machine's update) is:
`kL (u+1) = kL u + ⌊log (mA u / mA' u) / ε⌋₊` (masses before/after the exponential update) when some copy is
present, and per present copy and level: keep accumulating if the copy was present and no new level-`ℓ` block
starts at `u+1`, else restart at `(0, kL (u+1))`.

**`pw_eq_mw`**: if copies never come back (`hent`) and `u < 2^L`, then P0089's perturbed weights with prior `1`,
specialists `specAw (· ∈ pr ·)`, losses `b` and the perturbation `ρ = rho` (the rounding error) equal the
machine weights on the awake specialists. **`rho_mem`**: `-ε < ρ u ≤ 0` (so `|ρ u| ≤ ε`, `rho_abs_le`), for any
natural losses. **`pprob_eq`**, **`palgLoss_eq`**: the played distribution and its loss are those of the machine
weights. **`inc_le`**, **`kL_le`**: the grid index grows by at most `⌊η/ε⌋₊` per round (losses `≤ 1`), so
`kL u ≤ u ⌊η/ε⌋₊`; **`lw_le`**: the stored loss since wake is `≤ u` and the stored wake index is `≤ kL u`.
**`rec_stS`**: `Rec` is satisfiable (an explicit run `stS`). **`machine_interval`**: the composition with P0089's
`hedge_interval_hyp` (`δ = ε`), stated for the machine's weighted losses. No finite state type or machine is defined here; the
bounds above are what a downstream memory count uses.
-/

open Real Finset Pool.P0019 Pool.P0089

namespace Pool.P0102

variable {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] (L : ℕ)

/-- Start of the aligned level-`ℓ` block containing `u`. -/
def blk (ℓ u : ℕ) : ℕ := u / 2 ^ ℓ * 2 ^ ℓ

theorem blk_le (ℓ u : ℕ) : blk ℓ u ≤ u := Nat.div_mul_le_self u _

theorem lt_blk_add (ℓ u : ℕ) : u < blk ℓ u + 2 ^ ℓ := by
  unfold blk
  have h1 := Nat.div_add_mod u (2 ^ ℓ)
  have h2 := Nat.mod_lt u (Nat.two_pow_pos ℓ)
  rw [Nat.mul_comm] at h1
  omega

theorem dvd_blk (ℓ u : ℕ) : 2 ^ ℓ ∣ blk ℓ u := Nat.dvd_mul_left _ _

/-- Aligned blocks containing `u` start at `blk ℓ u`. -/
theorem aligned_iff (ℓ u s : ℕ) : (2 ^ ℓ ∣ s ∧ s ≤ u ∧ u < s + 2 ^ ℓ) ↔ s = blk ℓ u := by
  constructor
  · rintro ⟨⟨k, rfl⟩, h1, h2⟩
    unfold blk
    have hpos := Nat.two_pow_pos ℓ
    have : u / 2 ^ ℓ = k := by
      apply Nat.div_eq_of_lt_le
      · rw [Nat.mul_comm]; exact h1
      · rw [Nat.add_mul, one_mul, Nat.mul_comm]; exact h2
    rw [this, Nat.mul_comm]
  · rintro rfl
    exact ⟨dvd_blk ℓ u, blk_le ℓ u, lt_blk_add ℓ u⟩

theorem blk_succ (ℓ u : ℕ) (h : ¬ 2 ^ ℓ ∣ u + 1) : blk ℓ (u + 1) = blk ℓ u := by
  have h1 := (aligned_iff ℓ (u + 1) (blk ℓ u)).1
  refine (h1 ⟨dvd_blk ℓ u, (blk_le ℓ u).trans (Nat.le_succ u), ?_⟩).symm
  have h2 := lt_blk_add ℓ u
  rcases Nat.lt_or_ge (u + 1) (blk ℓ u + 2 ^ ℓ) with h3 | h3
  · exact h3
  · exfalso; apply h
    have : u + 1 = blk ℓ u + 2 ^ ℓ := by omega
    rw [this]; exact Nat.dvd_add (dvd_blk ℓ u) dvd_rfl

theorem blk_succ_of_dvd (ℓ u : ℕ) (h : 2 ^ ℓ ∣ u + 1) : blk ℓ (u + 1) = u + 1 :=
  ((aligned_iff ℓ (u + 1) (u + 1)).1 ⟨h, le_rfl, by have := Nat.two_pow_pos ℓ; omega⟩).symm

variable (pr : ℕ → Finset ι₀) (b : ℕ → ι₀ → ℕ) (η ε : ℝ) (kL : ℕ → ℕ) (lw : ℕ → ι₀ → ℕ → ℕ × ℕ)

/-- Machine weight of the level-`ℓ` specialist of copy `f` at round `u`. -/
noncomputable def mw (u : ℕ) (f : ι₀) (ℓ : ℕ) : ℝ :=
  exp (-η * ((lw u f ℓ).1 : ℝ) + ε * ((kL u : ℝ) - ((lw u f ℓ).2 : ℝ)))

/-- Awake mass of the machine weights. -/
noncomputable def mA (u : ℕ) : ℝ := ∑ f ∈ pr u, ∑ ℓ : Fin (L + 1), mw η ε kL lw u f ℓ

/-- Awake mass after the exponential update with the losses of round `u`. -/
noncomputable def mA' (u : ℕ) : ℝ :=
  ∑ f ∈ pr u, ∑ ℓ : Fin (L + 1), mw η ε kL lw u f ℓ * exp (-η * (b u f : ℝ))

/-- Grid increment of the log-normaliser. -/
noncomputable def inc (u : ℕ) : ℕ :=
  if (pr u).Nonempty then ⌊log (mA L pr η ε kL lw u / mA' L pr b η ε kL lw u) / ε⌋₊ else 0

/-- The perturbation: the rounding error of the log-normaliser. -/
noncomputable def rho (u : ℕ) : ℝ :=
  if (pr u).Nonempty then ε * (inc L pr b η ε kL lw u : ℝ) -
    log (mA L pr η ε kL lw u / mA' L pr b η ε kL lw u) else 0

/-- The machine's recursion. -/
structure Rec : Prop where
  k0 : kL 0 = 0
  kS : ∀ u, kL (u + 1) = kL u + inc L pr b η ε kL lw u
  w0 : ∀ f ∈ pr 0, ∀ ℓ, lw 0 f ℓ = (0, 0)
  wS : ∀ u, ∀ f ∈ pr (u + 1), ∀ ℓ, lw (u + 1) f ℓ =
    if f ∈ pr u ∧ ¬ 2 ^ ℓ ∣ u + 1 then ((lw u f ℓ).1 + b u f, (lw u f ℓ).2) else (0, kL (u + 1))

/-- The specialists' awake indicator (presence `f ∈ pr u`). -/
noncomputable abbrev aw : ℕ → Spec ι₀ L → Bool := specAw (L := L) (fun u f => f ∈ pr u)

/-- The specialists' losses. -/
noncomputable abbrev cs : ℕ → Spec ι₀ L → ℝ := specLoss (L := L) (fun u f => (b u f : ℝ))

variable {L pr b η ε kL lw}

theorem mw_pos (u : ℕ) (f : ι₀) (ℓ : ℕ) : 0 < mw η ε kL lw u f ℓ := exp_pos _

theorem aw_iff {u : ℕ} {i : Spec ι₀ L} : aw L pr u i = true ↔ (i.2.2 : ℕ) = blk i.2.1 u ∧ i.1 ∈ pr u := by
  simp only [aw, specAw, decide_eq_true_eq]
  rw [← aligned_iff]
  tauto

/-- The awake specialist of copy `f` at level `ℓ` and round `u < 2^L`. -/
def spc {u : ℕ} (hu : u < 2 ^ L) (f : ι₀) (ℓ : Fin (L + 1)) : Spec ι₀ L :=
  (f, ℓ, ⟨blk ℓ u, lt_of_le_of_lt (blk_le _ _) hu⟩)

/-- Sums over the awake specialists, as sums over present copies and levels. -/
theorem sum_awake {u : ℕ} (hu : u < 2 ^ L) (F : Spec ι₀ L → ℝ) :
    ∑ j, (if aw L pr u j then F j else 0) = ∑ f ∈ pr u, ∑ ℓ : Fin (L + 1), F (spc hu f ℓ) := by
  rw [Fintype.sum_prod_type, ← Finset.sum_filter_add_sum_filter_not univ (fun f => f ∈ pr u)]
  have h0 : ∑ f ∈ univ.filter (fun f => f ∉ pr u), ∑ y : Fin (L + 1) × Fin (2 ^ L),
      (if aw L pr u (f, y) then F (f, y) else 0) = 0 := by
    refine Finset.sum_eq_zero fun f hf => Finset.sum_eq_zero fun y _ => ?_
    rw [Finset.mem_filter] at hf
    rw [if_neg]; rw [aw_iff]; exact fun h => hf.2 h.2
  rw [h0, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [Finset.sum_eq_single ⟨blk ℓ u, lt_of_le_of_lt (blk_le _ _) hu⟩]
  · rw [if_pos (aw_iff.2 ⟨rfl, hf⟩)]; rfl
  · intro s _ hs
    rw [if_neg]; rw [aw_iff]; intro h; exact hs (Fin.ext h.1)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- A specialist never awake before `t` keeps its prior weight. -/
theorem pw_of_never {q : Spec ι₀ L → ℝ} {c : ℕ → Spec ι₀ L → ℝ} {ρ : ℕ → ℝ} {aw' : ℕ → Spec ι₀ L → Bool}
    (i : Spec ι₀ L) : ∀ t, (∀ s < t, aw' s i = false) → pw q η aw' c ρ t i = q i
  | 0, _ => rfl
  | t + 1, h => by
    simp only [pw]
    rw [if_neg (by rw [h t (Nat.lt_succ_self t)]; simp)]
    exact pw_of_never i t fun s hs => h s (Nat.lt_succ_of_lt hs)

theorem mA_pos {u : ℕ} (hne : (pr u).Nonempty) : 0 < mA L pr η ε kL lw u := by
  obtain ⟨f, hf⟩ := hne
  refine Finset.sum_pos (fun f _ => Finset.sum_pos (fun ℓ _ => mw_pos _ _ _) Finset.univ_nonempty) ⟨f, hf⟩

theorem mA'_pos {u : ℕ} (hne : (pr u).Nonempty) : 0 < mA' L pr b η ε kL lw u := by
  obtain ⟨f, hf⟩ := hne
  refine Finset.sum_pos (fun f _ => Finset.sum_pos (fun ℓ _ => mul_pos (mw_pos _ _ _) (exp_pos _))
    Finset.univ_nonempty) ⟨f, hf⟩

theorem mA'_le (hη : 0 ≤ η) (u : ℕ) : mA' L pr b η ε kL lw u ≤ mA L pr η ε kL lw u := by
  unfold mA' mA
  refine Finset.sum_le_sum fun f _ => Finset.sum_le_sum fun ℓ _ => ?_
  have : exp (-η * (b u f : ℝ)) ≤ 1 := by
    rw [exp_le_one_iff]; have : (0 : ℝ) ≤ b u f := Nat.cast_nonneg _; nlinarith
  have := mw_pos (η := η) (ε := ε) (kL := kL) (lw := lw) u f ℓ
  nlinarith

theorem le_mA' (hb : ∀ u f, b u f ≤ 1) (hη : 0 ≤ η) (u : ℕ) :
    exp (-η) * mA L pr η ε kL lw u ≤ mA' L pr b η ε kL lw u := by
  unfold mA' mA
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  have : exp (-η) ≤ exp (-η * (b u f : ℝ)) := by
    rw [exp_le_exp]
    have : (b u f : ℝ) ≤ 1 := by exact_mod_cast hb u f
    nlinarith
  have := mw_pos (η := η) (ε := ε) (kL := kL) (lw := lw) u f ℓ
  nlinarith

/-- The logarithmic mass ratio lies in `[0, η]`. -/
theorem logRatio_mem (hb : ∀ u f, b u f ≤ 1) (hη : 0 ≤ η) {u : ℕ} (hne : (pr u).Nonempty) :
    0 ≤ log (mA L pr η ε kL lw u / mA' L pr b η ε kL lw u) ∧
      log (mA L pr η ε kL lw u / mA' L pr b η ε kL lw u) ≤ η := by
  have hA := mA_pos (η := η) (ε := ε) (kL := kL) (lw := lw) (L := L) hne
  have hA' := mA'_pos (b := b) (η := η) (ε := ε) (kL := kL) (lw := lw) (L := L) hne
  constructor
  · apply log_nonneg
    rw [le_div_iff₀ hA', one_mul]; exact mA'_le hη u
  · rw [log_le_iff_le_exp (div_pos hA hA'), div_le_iff₀ hA']
    have h := le_mA' (pr := pr) (ε := ε) (kL := kL) (lw := lw) (L := L) hb hη u
    have : exp η * exp (-η) = 1 := by rw [← exp_add]; simp
    nlinarith [exp_pos η]

/-- **The perturbation lies in `(-ε, 0]`** (floor rounding of a nonnegative log-ratio). Only `η ≥ 0` and `ε > 0`
are needed; the losses may be any natural numbers. -/
theorem rho_mem (hη : 0 ≤ η) (hε : 0 < ε) (u : ℕ) :
    -ε < rho L pr b η ε kL lw u ∧ rho L pr b η ε kL lw u ≤ 0 := by
  unfold rho
  split_ifs with hne
  · have hA := mA_pos (η := η) (ε := ε) (kL := kL) (lw := lw) (L := L) hne
    have hA' := mA'_pos (b := b) (η := η) (ε := ε) (kL := kL) (lw := lw) (L := L) hne
    have hy0 : 0 ≤ log (mA L pr η ε kL lw u / mA' L pr b η ε kL lw u) := by
      apply log_nonneg
      rw [le_div_iff₀ hA', one_mul]; exact mA'_le hη u
    set y := log (mA L pr η ε kL lw u / mA' L pr b η ε kL lw u)
    have hinc : (inc L pr b η ε kL lw u : ℝ) = ⌊y / ε⌋₊ := by simp [inc, hne, y]
    rw [hinc]
    have h1 : (⌊y / ε⌋₊ : ℝ) ≤ y / ε := Nat.floor_le (div_nonneg hy0 hε.le)
    have h2 : y / ε < ⌊y / ε⌋₊ + 1 := Nat.lt_floor_add_one _
    have h1' : ε * (⌊y / ε⌋₊ : ℝ) ≤ y := by rwa [le_div_iff₀ hε, mul_comm] at h1
    have h2' : y < ε * ((⌊y / ε⌋₊ : ℝ) + 1) := by rwa [div_lt_iff₀ hε, mul_comm] at h2
    constructor <;> nlinarith
  · exact ⟨by linarith, le_rfl⟩

/-- **The perturbation is at most `ε`** in absolute value (any natural losses). -/
theorem rho_abs_le (hη : 0 ≤ η) (hε : 0 < ε) (u : ℕ) : |rho L pr b η ε kL lw u| ≤ ε := by
  obtain ⟨h1, h2⟩ := rho_mem (L := L) (pr := pr) (b := b) (kL := kL) (lw := lw) hη hε u
  rw [abs_le]; constructor <;> linarith

/-- The grid index grows by at most `⌊η/ε⌋₊` per round. -/
theorem inc_le (hb : ∀ u f, b u f ≤ 1) (hη : 0 ≤ η) (hε : 0 < ε) (u : ℕ) :
    inc L pr b η ε kL lw u ≤ ⌊η / ε⌋₊ := by
  unfold inc
  split_ifs with hne
  · apply Nat.floor_le_floor
    exact div_le_div_of_nonneg_right (logRatio_mem (ε := ε) (kL := kL) (lw := lw) (L := L) hb hη hne).2 hε.le
  · exact Nat.zero_le _

/-- The grid index after `u` rounds is at most `u ⌊η/ε⌋₊`. -/
theorem kL_le (hrec : Rec L pr b η ε kL lw) (hb : ∀ u f, b u f ≤ 1) (hη : 0 ≤ η) (hε : 0 < ε) :
    ∀ u, kL u ≤ u * ⌊η / ε⌋₊
  | 0 => by rw [hrec.k0]; exact Nat.zero_le _
  | u + 1 => by
    rw [hrec.kS u, Nat.succ_mul]
    exact Nat.add_le_add (kL_le hrec hb hη hε u) (inc_le hb hη hε u)

/-- The exponential update factor of the perturbed Hedge is `exp (ε · inc)`. -/
theorem factor_eq {u : ℕ} (hne : (pr u).Nonempty) :
    mA L pr η ε kL lw u / mA' L pr b η ε kL lw u * exp (rho L pr b η ε kL lw u) =
      exp (ε * (inc L pr b η ε kL lw u : ℝ)) := by
  have hA := mA_pos (η := η) (ε := ε) (kL := kL) (lw := lw) (L := L) hne
  have hA' := mA'_pos (b := b) (η := η) (ε := ε) (kL := kL) (lw := lw) (L := L) hne
  unfold rho
  rw [if_pos hne, exp_sub, exp_log (div_pos hA hA')]
  field_simp

/-- **P0089's perturbed weights are the machine weights** on the awake specialists, at every round `u < 2^L`. -/
theorem pw_eq_mw (hrec : Rec L pr b η ε kL lw)
    (hent : ∀ u, ∀ f ∈ pr (u + 1), f ∉ pr u → ∀ u' ≤ u, f ∉ pr u') :
    ∀ u (hu : u < 2 ^ L), ∀ f ∈ pr u, ∀ ℓ : Fin (L + 1),
      pw (fun _ => 1) η (aw L pr) (cs L b) (rho L pr b η ε kL lw) u (spc hu f ℓ) = mw η ε kL lw u f ℓ := by
  intro u
  induction u with
  | zero =>
    intro hu f hf ℓ
    simp only [pw, mw, hrec.w0 f hf ℓ, hrec.k0]
    simp
  | succ u ih =>
    intro hu f hf ℓ
    have hu' : u < 2 ^ L := by omega
    by_cases hcase : f ∈ pr u ∧ ¬ 2 ^ (ℓ : ℕ) ∣ u + 1
    · -- awake at `u` too
      have hspc : spc hu f ℓ = spc hu' f ℓ := by
        simp only [spc, blk_succ ℓ u hcase.2]
      have hne : (pr u).Nonempty := ⟨f, hcase.1⟩
      have hawu : aw L pr u (spc hu' f ℓ) = true := aw_iff.2 ⟨rfl, hcase.1⟩
      have hmass : awakeMass (pw (fun _ => 1) η (aw L pr) (cs L b) (rho L pr b η ε kL lw) u) (aw L pr u) =
          mA L pr η ε kL lw u := by
        unfold awakeMass mA
        rw [sum_awake hu']
        exact Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun ℓ' _ => ih hu' g hg ℓ'
      have hexp : expMass (pw (fun _ => 1) η (aw L pr) (cs L b) (rho L pr b η ε kL lw) u) (aw L pr u) η
          (cs L b u) = mA' L pr b η ε kL lw u := by
        unfold expMass mA'
        rw [sum_awake hu']
        exact Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun ℓ' _ => by
          rw [ih hu' g hg ℓ']; rfl
      rw [hspc]
      simp only [pw]
      rw [if_pos hawu, hmass, hexp, ih hu' f hcase.1 ℓ, mul_assoc, factor_eq hne]
      unfold mw
      rw [hrec.wS u f hf ℓ, if_pos hcase, hrec.kS u]
      simp only [cs, specLoss, spc]
      rw [← exp_add, ← exp_add]
      congr 1
      push_cast
      ring
    · -- woke at `u + 1`
      have hnever : ∀ s < u + 1, aw L pr s (spc hu f ℓ) = false := by
        intro s hs
        rw [Bool.eq_false_iff]
        intro haw
        obtain ⟨h1, h2⟩ := aw_iff.1 haw
        rw [not_and_or] at hcase
        rcases hcase with hc | hc
        · exact hent u f hf hc s (by omega) h2
        · push Not at hc
          have : blk ℓ (u + 1) = u + 1 := blk_succ_of_dvd ℓ u hc
          simp only [spc, this] at h1
          have := blk_le (ℓ : ℕ) s
          omega
      rw [pw_of_never _ (u + 1) hnever]
      unfold mw
      rw [hrec.wS u f hf ℓ, if_neg hcase]
      simp

/-- The played distribution is the normalised machine weight. -/
theorem pprob_eq (hrec : Rec L pr b η ε kL lw)
    (hent : ∀ u, ∀ f ∈ pr (u + 1), f ∉ pr u → ∀ u' ≤ u, f ∉ pr u')
    {u : ℕ} (hu : u < 2 ^ L) (j : Spec ι₀ L) :
    pprob (fun _ => 1) η (aw L pr) (cs L b) (rho L pr b η ε kL lw) u j =
      if aw L pr u j then
        pw (fun _ => 1) η (aw L pr) (cs L b) (rho L pr b η ε kL lw) u j / mA L pr η ε kL lw u else 0 := by
  unfold pprob
  split_ifs with h
  · congr 1
    unfold awakeMass mA
    rw [sum_awake hu]
    exact Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun ℓ _ => pw_eq_mw hrec hent u hu g hg ℓ
  · rfl

/-- **The learner's expected loss** at a round `u < 2^L` is the machine-weighted average loss of the present
copies. -/
theorem palgLoss_eq (hrec : Rec L pr b η ε kL lw)
    (hent : ∀ u, ∀ f ∈ pr (u + 1), f ∉ pr u → ∀ u' ≤ u, f ∉ pr u') {u : ℕ} (hu : u < 2 ^ L) :
    palgLoss (fun _ => 1) η (aw L pr) (cs L b) (rho L pr b η ε kL lw) u =
      (∑ f ∈ pr u, (∑ ℓ : Fin (L + 1), mw η ε kL lw u f ℓ) * (b u f : ℝ)) / mA L pr η ε kL lw u := by
  unfold palgLoss
  have : ∀ j, pprob (fun _ => 1) η (aw L pr) (cs L b) (rho L pr b η ε kL lw) u j * cs L b u j =
      if aw L pr u j then
        pw (fun _ => 1) η (aw L pr) (cs L b) (rho L pr b η ε kL lw) u j * cs L b u j / mA L pr η ε kL lw u
      else 0 := by
    intro j
    rw [pprob_eq hrec hent hu j]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => this j, sum_awake hu, Finset.sum_div]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [pw_eq_mw hrec hent u hu f hf ℓ]
  rfl

/-- **Composed guarantee** (P0089's `hedge_interval_hyp` with `δ = ε`, transported by `palgLoss_eq` and
`rho_abs_le`): on every interval `[s, s')` with `s' ≤ T ≤ 2^L` during which copy `f` is present, the machine's
weighted losses are within `(2L+1)(log|Spec| + 2εT)/η + (η/2)(s' − s)` of `f`'s losses. -/
theorem machine_interval (hrec : Rec L pr b η ε kL lw)
    (hent : ∀ u, ∀ f ∈ pr (u + 1), f ∉ pr u → ∀ u' ≤ u, f ∉ pr u')
    (hb : ∀ u f, b u f ≤ 1) (hη : 0 < η) (hε : 0 < ε) (T : ℕ) (hTL : T ≤ 2 ^ L)
    [Nonempty (Spec ι₀ L)] (f : ι₀) (s s' : ℕ) (hss' : s ≤ s') (hs'T : s' ≤ T)
    (hpres : ∀ u, s ≤ u → u < s' → f ∈ pr u) :
    ∑ u ∈ Finset.Ico s s',
        (∑ g ∈ pr u, (∑ ℓ : Fin (L + 1), mw η ε kL lw u g ℓ) * (b u g : ℝ)) / mA L pr η ε kL lw u ≤
      ∑ u ∈ Finset.Ico s s', (b u f : ℝ) +
        (2 * L + 1) * (Real.log (Fintype.card (Spec ι₀ L)) + 2 * ε * T) / η +
          η / 2 * ((s' - s : ℕ) : ℝ) := by
  have h := hedge_interval_hyp (L := L) (fun u f => f ∈ pr u) (fun u f => (b u f : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (fun u f => by exact_mod_cast hb u f) hη hε.le
    (rho L pr b η ε kL lw) (rho_abs_le hη.le hε) T hTL f s s' hss' hpres
  simp only at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun u hu => ?_
  have hus : u < s' := (Finset.mem_Ico.mp hu).2
  rw [if_pos (by omega), palgLoss_eq hrec hent (by omega)]

/-- **Bounds on the stored per-copy integers**: for a present copy, the loss since wake is at most `u` (losses
`≤ 1`) and the wake grid index is at most `kL u`. Together with `kL_le`, every stored number is bounded. -/
theorem lw_le (hrec : Rec L pr b η ε kL lw) (hb : ∀ u f, b u f ≤ 1) :
    ∀ u, ∀ f ∈ pr u, ∀ ℓ, (lw u f ℓ).1 ≤ u ∧ (lw u f ℓ).2 ≤ kL u
  | 0 => by
    intro f hf ℓ
    rw [hrec.w0 f hf ℓ, hrec.k0]; exact ⟨le_rfl, le_rfl⟩
  | u + 1 => by
    intro f hf ℓ
    rw [hrec.wS u f hf ℓ]
    split_ifs with hc
    · have ih := lw_le hrec hb u f hc.1 ℓ
      have := hb u f
      rw [hrec.kS u]
      exact ⟨by simp only; omega, by simp only; omega⟩
    · exact ⟨by simp, le_rfl⟩

/-- One step of the machine's state `(kL, lw)` (used to show that `Rec` is satisfiable). -/
noncomputable def stepS (u : ℕ) (s : ℕ × (ι₀ → ℕ → ℕ × ℕ)) : ℕ × (ι₀ → ℕ → ℕ × ℕ) :=
  (s.1 + inc L pr b η ε (fun _ => s.1) (fun _ => s.2) u, fun f ℓ =>
    if f ∈ pr u ∧ ¬ 2 ^ ℓ ∣ u + 1 then ((s.2 f ℓ).1 + b u f, (s.2 f ℓ).2)
    else (0, s.1 + inc L pr b η ε (fun _ => s.1) (fun _ => s.2) u))

variable (L pr b η ε) in
/-- The machine's state run from `(0, (0,0))`. -/
noncomputable def stS : ℕ → ℕ × (ι₀ → ℕ → ℕ × ℕ)
  | 0 => (0, fun _ _ => (0, 0))
  | u + 1 => stepS (L := L) (pr := pr) (b := b) (η := η) (ε := ε) u (stS u)

/-- **`Rec` is satisfiable**: the explicitly run state satisfies it, for all inputs. -/
theorem rec_stS : Rec L pr b η ε (fun u => (stS L pr b η ε u).1) (fun u => (stS L pr b η ε u).2) where
  k0 := rfl
  kS u := rfl
  w0 f _ ℓ := rfl
  wS u f _ ℓ := rfl

end Pool.P0102
