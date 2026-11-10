import Pool.P0112.FOAsm
import Pool.P0115.FOFreed

/-!
# The record errors of the one-free-observation walk hold with high probability

P0112's per-run bound `run_bound_FO` assumes `hz`: every covered record's data overestimate the comparator's true
loss by at most `z(len)`. Here `z = zW s x`, `zW s x n = 2√(s·n·x) + 2s·x`.

* `DevEv`, `devEv_le`: the deviation event of one record in its own run (actual entry-order run if the copy is
  sampled, its forced copy-last run otherwise) has probability `≤ e^{−x}` (P0115's `fo_interval_freedman`).
* `HzProp`: the hypothesis `hz` of P0112.
* `devEv_of_not_hz`: if the actual run never uses more than `s − 1` slots, a violated record is a deviation event
  (P0115's `Vat_forced_card_le` handles the forced runs; P0112's `hyp_evWF` gives `τ < e ≤ T`).
* **`prob_not_hz`**: for fixed sampling/filter bits, `P(at most s − 1 slots used ∧ ¬ hz) ≤ D·T·(T+1)·e^{−x}`.
-/

namespace Pool.P0120

open Finset Pool.P0095 Pool.P0065 Pool.P0105 Pool.P0112 Pool.P0115

section Hz

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ)

/-- The record width: `2√(s·len·x) + 2s·x`. -/
noncomputable def zW (x : ℝ) (n : ℕ) : ℝ := 2 * Real.sqrt (s * (n : ℝ) * x) + 2 * s * x

/-- The deviation event of one record `[τ, e)` of copy `c`, in the run that the record's data come from. -/
def DevEv (cstar : ℕ → ℕ → ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (T : ℕ) (x : ℝ) (r τ e : ℕ)
    (y : ℕ → Fin s) : Prop :=
  if ωs (cstar r τ) = true then
    (∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u).card ≤ s) ∧
      zW s x (e - τ) ≤ (Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y (cstar r τ) e -
        Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y (cstar r τ) τ) -
        ∑ u ∈ Ico τ e, (if cstar r τ ∈ Vat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u
          then L u (cstar r τ) else 0)
  else
    (∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ)) (forceS ωs (cstar r τ))
        (forceF K φ (cstar r τ)) y u).card ≤ s) ∧
      zW s x (e - τ) ≤ (Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ)) (forceS ωs (cstar r τ))
          (forceF K φ (cstar r τ)) y (cstar r τ) e -
        Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ)) (forceS ωs (cstar r τ))
          (forceF K φ (cstar r τ)) y (cstar r τ) τ) -
        ∑ u ∈ Ico τ e, (if cstar r τ ∈ Vat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ))
          (forceS ωs (cstar r τ)) (forceF K φ (cstar r τ)) y u then L u (cstar r τ) else 0)

open Classical in
/-- Each record's deviation event has probability at most `e^{−x}`. -/
theorem devEv_le [NeZero s] (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s)
    (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1) (cstar : ℕ → ℕ → ι) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) {T : ℕ} {x : ℝ} (hx : 0 < x) {r τ e : ℕ} (hτe : τ < e) (heT : e ≤ T) :
    ∑ yy : Fin T → Fin s, Pool.P0092.wgt ν yy *
      (if DevEv E thr0 θ R K D Lv Bt lev s L cstar ωs φ T x r τ e (extY s yy) then 1 else 0) ≤ Real.exp (-x) := by
  unfold DevEv zW
  by_cases hc : ωs (cstar r τ) = true
  · simp only [ite_eq_left hc]
    exact fo_interval_freedman E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ ν hν (slotSum_occSort s) hL0 hL1
      (cstar r τ) hτe heT hx
  · simp only [ite_eq_right hc]
    exact fo_interval_freedman E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ)) (forceS ωs (cstar r τ))
      (forceF K φ (cstar r τ)) ν hν (slotSum_occLast s (cstar r τ)) hL0 hL1 (cstar r τ) hτe heT hx

end Hz

section HzProb

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ)

/-- The record-error hypothesis `hz` of P0112's `run_bound_FO`, with the width `zW`. -/
def HzProp (cstar : ℕ → ℕ → ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (T : ℕ) (g : ℕ → ℝ) (x : ℝ)
    (y : ℕ → Fin s) : Prop :=
  ∀ τ r e, Bt r ∣ τ → τ < T → r < D → evFO E thr0 θ R K D Lv Bt lev s L T cstar ωs φ y τ r = some e →
    recData E thr0 θ R K D Lv Bt lev s L cstar ωs φ y r τ e -
      recData E thr0 θ R K D Lv Bt lev s L cstar ωs φ y r τ τ - ∑ u ∈ Finset.Ico τ e, g u ≤ zW s x (e - τ)

/-- **A violated record is a deviation event.** If the actual run never uses more than `s − 1` slots and the
comparator's copies have true losses `g`, a covered record whose data exceed `Σ g` by more than `zW` is a
deviation event of its run (P0115's `Vat_forced_card_le` handles the forced runs). -/
theorem devEv_of_not_hz (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s) (g : ℕ → ℝ)
    (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < T → L u (cstar j a) = g u) (hL0 : ∀ u x, 0 ≤ L u x) (x : ℝ)
    (hgood : ∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u).card + 1 ≤ s)
    (hnot : ¬ HzProp E thr0 θ R K D Lv Bt lev s L cstar ωs φ T g x y) :
    ∃ r < D, ∃ τ < T, ∃ e < T + 1, τ < e ∧ DevEv E thr0 θ R K D Lv Bt lev s L cstar ωs φ T x r τ e y := by
  unfold HzProp at hnot
  push Not at hnot
  obtain ⟨τ, r, e, hd, hτ, hr, he, hbig⟩ := hnot
  have hH := hyp_evWF (θ := θ) (R := R) (lev := lev) hB hLv hlev hT
    (Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y)
    (fun r τ => Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ)) (forceS ωs (cstar r τ))
      (forceF K φ (cstar r τ)) y) cstar hE hthr ωs φ
  have hlb := hH.lb τ r e hd hτ hr he
  have hub := hH.ub τ r e hd hτ hr he
  have hpos := hB.pos r
  refine ⟨r, hr, τ, hτ, e, by omega, by omega, ?_⟩
  have hsum : ∀ (V : ℕ → Finset ι), ∑ u ∈ Ico τ e, (if cstar r τ ∈ V u then L u (cstar r τ) else 0) ≤
      ∑ u ∈ Ico τ e, g u := by
    intro V
    refine Finset.sum_le_sum fun u _ => ?_
    rw [← hg r τ u (by omega) hd hτ]
    split_ifs
    · exact le_rfl
    · exact hL0 u _
  unfold DevEv
  unfold recData at hbig
  split_ifs with hc
  · rw [ite_eq_left hc] at hbig
    refine ⟨fun u hu => by have := hgood u hu; omega, ?_⟩
    have := hsum (fun u => Vat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u)
    linarith
  · rw [ite_eq_right hc] at hbig
    have hc' : ωs (cstar r τ) = false := by simpa using hc
    refine ⟨fun u hu => ?_, ?_⟩
    · have h1 := Vat_forced_card_le E thr0 θ R K D Lv Bt lev s L hc' φ y u
      have h2 := hgood u hu
      omega
    · have := hsum (fun u => Vat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar r τ)) (forceS ωs (cstar r τ))
        (forceF K φ (cstar r τ)) y u)
      linarith

open Classical in
/-- **The record errors of P0112 hold with high probability.** For fixed sampling and filter bits and i.i.d.
uniform slots, the weight of the slot sequences on which the actual run never uses more than `s − 1` slots but some
covered record of the FO walk violates `hz` with width `zW s x` is at most `D·T·(T+1)·e^{−x}`. -/
theorem prob_not_hz [NeZero s] (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (g : ℕ → ℝ)
    (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < T → L u (cstar j a) = g u)
    (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1)
    (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s) {x : ℝ} (hx : 0 < x) :
    ∑ yy : Fin T → Fin s, Pool.P0092.wgt ν yy *
      (if (∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ (extY s yy) u).card + 1 ≤ s) ∧
          ¬ HzProp E thr0 θ R K D Lv Bt lev s L cstar ωs φ T g x (extY s yy) then 1 else 0) ≤
        D * T * (T + 1) * Real.exp (-x) := by
  have hw : ∀ yy : Fin T → Fin s, 0 ≤ Pool.P0092.wgt ν yy := fun yy => Pool.P0092.wgt_nonneg ν yy
  set Ev : ℕ → ℕ → ℕ → (Fin T → Fin s) → ℝ := fun r τ e yy =>
    if τ < e ∧ DevEv E thr0 θ R K D Lv Bt lev s L cstar ωs φ T x r τ e (extY s yy) then 1 else 0 with hEv
  have hpt : ∀ yy : Fin T → Fin s,
      (if (∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ (extY s yy) u).card + 1 ≤ s) ∧
          ¬ HzProp E thr0 θ R K D Lv Bt lev s L cstar ωs φ T g x (extY s yy) then (1 : ℝ) else 0) ≤
        ∑ r ∈ range D, ∑ τ ∈ range T, ∑ e ∈ range (T + 1), Ev r τ e yy := by
    intro yy
    have hnn : ∀ r τ e, 0 ≤ Ev r τ e yy := fun r τ e => by simp only [hEv]; split_ifs <;> norm_num
    split_ifs with h
    · obtain ⟨r, hr, τ, hτ, e, he, hτe, hdev⟩ := devEv_of_not_hz E thr0 θ R K D Lv Bt lev s L hB hLv hlev hT
        cstar hE hthr ωs φ (extY s yy) g hg hL0 x h.1 h.2
      have h1 : Ev r τ e yy = 1 := by simp only [hEv]; rw [ite_eq_left ⟨hτe, hdev⟩]
      calc (1 : ℝ) = Ev r τ e yy := h1.symm
        _ ≤ ∑ e' ∈ range (T + 1), Ev r τ e' yy :=
            Finset.single_le_sum (fun e' _ => hnn r τ e') (Finset.mem_range.2 he)
        _ ≤ ∑ τ' ∈ range T, ∑ e' ∈ range (T + 1), Ev r τ' e' yy :=
            Finset.single_le_sum (f := fun τ' => ∑ e' ∈ range (T + 1), Ev r τ' e' yy)
              (fun τ' _ => Finset.sum_nonneg fun e' _ => hnn r τ' e') (Finset.mem_range.2 hτ)
        _ ≤ _ := Finset.single_le_sum (f := fun r' => ∑ τ' ∈ range T, ∑ e' ∈ range (T + 1), Ev r' τ' e' yy)
              (fun r' _ => Finset.sum_nonneg fun τ' _ => Finset.sum_nonneg fun e' _ => hnn r' τ' e')
              (Finset.mem_range.2 hr)
    · exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun e _ => hnn r τ e
  have hone : ∀ r τ e, e < T + 1 → ∑ yy : Fin T → Fin s, Pool.P0092.wgt ν yy * Ev r τ e yy ≤ Real.exp (-x) := by
    intro r τ e heT
    by_cases hτe : τ < e
    · refine le_trans (le_of_eq (Finset.sum_congr rfl fun yy _ => ?_))
        (devEv_le E thr0 θ R K D Lv Bt lev s L ν hν hL0 hL1 cstar ωs φ hx (r := r) hτe (by omega))
      simp only [hEv]
      congr 1
      exact if_congr (by simp [hτe]) rfl rfl
    · simp only [hEv, hτe, false_and, ite_false, mul_zero, Finset.sum_const_zero]
      exact (Real.exp_pos _).le
  calc _ ≤ ∑ yy : Fin T → Fin s, Pool.P0092.wgt ν yy *
          ∑ r ∈ range D, ∑ τ ∈ range T, ∑ e ∈ range (T + 1), Ev r τ e yy :=
        Finset.sum_le_sum fun yy _ => mul_le_mul_of_nonneg_left (hpt yy) (hw yy)
    _ = ∑ r ∈ range D, ∑ τ ∈ range T, ∑ e ∈ range (T + 1),
          ∑ yy : Fin T → Fin s, Pool.P0092.wgt ν yy * Ev r τ e yy := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ _r ∈ range D, ∑ _τ ∈ range T, ∑ _e ∈ range (T + 1), Real.exp (-x) :=
        Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun e he =>
          hone r τ e (Finset.mem_range.1 he)
    _ = D * T * (T + 1) * Real.exp (-x) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring

/-- **Bridge to the closed form.** `HzProp` with width `zW s x` gives P0112's `run_bound_FO_closed` hypothesis `hz`
with `za = 2√(s·x)` and `zb = 2s·x` (using `√(s·len·x) = √(s·x)·√len`). -/
theorem hz_closed_of_hzProp (cstar : ℕ → ℕ → ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (T : ℕ)
    (g : ℕ → ℝ) {x : ℝ} (hx : 0 ≤ x) (y : ℕ → Fin s)
    (h : HzProp E thr0 θ R K D Lv Bt lev s L cstar ωs φ T g x y) :
    ∀ τ r e, Bt r ∣ τ → τ < T → r < D → evFO E thr0 θ R K D Lv Bt lev s L T cstar ωs φ y τ r = some e →
      recData E thr0 θ R K D Lv Bt lev s L cstar ωs φ y r τ e -
        recData E thr0 θ R K D Lv Bt lev s L cstar ωs φ y r τ τ - ∑ u ∈ Finset.Ico τ e, g u ≤
          (2 * Real.sqrt (s * x)) * Real.sqrt ((e - τ : ℕ) : ℝ) + 2 * s * x := by
  intro τ r e hd hτ hr he
  have h1 := h τ r e hd hτ hr he
  unfold zW at h1
  have h2 : Real.sqrt (s * ((e - τ : ℕ) : ℝ) * x) = Real.sqrt (s * x) * Real.sqrt ((e - τ : ℕ) : ℝ) := by
    rw [show (s : ℝ) * ((e - τ : ℕ) : ℝ) * x = (s * x) * ((e - τ : ℕ) : ℝ) by ring]
    exact Real.sqrt_mul (by positivity) _
  rw [h2] at h1
  linarith

end HzProb

end Pool.P0120
