import Pool.P0065.Threads

/-!
# Occupancy of a thread by a migrating copy, and the variance proxy of P0150 §1.1

In P0065's threaded process a copy's current thread `curT c x` is its entry thread, lowered to `canonT m` at every
restart `m`. P0150 §1.1 (and P0166's design, where rates follow the current thread) needs: a copy is in thread
`i ≥ 1` for at most `Bt (i-1)` units, so the inverse-rate sum `Σ_u 1/x(curT u)` (the variance proxy of its slot
estimate, meaningful for positive rates `x i > 0`; the Lean statements do not require positivity, and a zero
rate would contribute `1/0 = 0`) is `≤ |I|/x_max + (#threads)·ρ·T/n` on every window `I` after its entry,
whatever its entry thread.

* `Pool.P0171.sub_lt_of_curT_eq`: two units of thread `i ≥ 1` (after entry) are less than `Bt (i-1)` apart.
* **`Pool.P0171.card_curT_eq_le`**: in any window `[a, b)` with `E c ≤ a`, at most `Bt (i-1)` units have `curT = i`.
* **`Pool.P0171.sum_w_curT_le`**: for any weight `w` and `M ≥ w 0`,
  `Σ_{x∈[a,b)} w(curT x) ≤ (b-a)·M + Σ_{1≤i≤thr0 c} Bt(i-1)·(w i - M)⁺`.
* **`Pool.P0171.sum_inv_rate_le`**: with `1/x i ≤ max M (T/(n·Bt i))`, `1/x 0 ≤ M`, `Bt (i-1) ≤ ρ·Bt i`:
  `Σ_{u∈[a,b)} 1/x(curT u) ≤ (b-a)·M + thr0 c·ρ·T/n`.

Only `canonT_le_of_dvd` and `curT_le_canonT` of P0065 are used: no divisibility chain between epoch lengths is
needed. Deterministic; no probability, no process beyond `curT`.
-/

namespace Pool.P0171

open Pool.P0065

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E : ι → ℕ} {thr0 : ι → ℕ} {D : ℕ} {Bt : ℕ → ℕ}

/-- A copy spends fewer than `Bt (i-1)` units in thread `i ≥ 1` after its entry: two units of thread `i`
cannot be separated by a multiple of `Bt (i-1)`. -/
lemma sub_lt_of_curT_eq (c : ι) {i x y : ℕ} (hi : 1 ≤ i) (hB : 0 < Bt (i - 1)) (hx : E c ≤ x) (hxy : x ≤ y)
    (hcx : curT E thr0 D Bt c x = i) (hcy : curT E thr0 D Bt c y = i) : y - x < Bt (i - 1) := by
  by_contra hcon
  push_neg at hcon
  -- the first multiple of `Bt (i-1)` after `x`
  set m := (x / Bt (i - 1) + 1) * Bt (i - 1) with hm
  have hxm : x < m := by
    have := Nat.lt_div_mul_add hB (a := x)
    rw [hm, add_mul, one_mul]; exact this
  have hmy : m ≤ y := by
    have : m ≤ x + Bt (i - 1) := by
      rw [hm, add_mul, one_mul]; have := Nat.div_mul_le_self x (Bt (i - 1)); omega
    omega
  have hdvd : Bt (i - 1) ∣ m := ⟨x / Bt (i - 1) + 1, by rw [hm, mul_comm]⟩
  have h1 := curT_le_canonT (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c (lt_of_le_of_lt hx hxm) hmy
  have h2 := canonT_le_of_dvd (D := D) hdvd
  omega

/-- **Occupancy of a thread.** After its entry, a copy is in thread `i ≥ 1` during at most `Bt (i-1)` units of
any window. -/
theorem card_curT_eq_le (c : ι) {i : ℕ} (hi : 1 ≤ i) (hB : 0 < Bt (i - 1)) (a b : ℕ) (ha : E c ≤ a) :
    ((Finset.Ico a b).filter fun x => curT E thr0 D Bt c x = i).card ≤ Bt (i - 1) := by
  set S := (Finset.Ico a b).filter fun x => curT E thr0 D Bt c x = i
  rcases S.eq_empty_or_nonempty with h | h
  · rw [h]; simp
  set x0 := S.min' h
  have hx0 : x0 ∈ S := S.min'_mem h
  have hsub : S ⊆ Finset.Ico x0 (x0 + Bt (i - 1)) := by
    intro y hy
    have hle : x0 ≤ y := S.min'_le y hy
    simp only [S, Finset.mem_filter, Finset.mem_Ico] at hy hx0
    have := sub_lt_of_curT_eq (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c hi hB (by omega) hle hx0.2 hy.2
    simp only [Finset.mem_Ico]; omega
  refine (Finset.card_le_card hsub).trans ?_
  simp

/-- **Variance proxy of a migrating copy.** For any per-thread weight `w` (e.g. `w i = 1/x_i`, the inverse probe
rate of thread `i`) and any level `M ≥ w 0`, over a window `[a, b)` after the copy's entry,
`Σ_x w(curT x) ≤ (b - a)·M + Σ_{1 ≤ i ≤ thr0 c} Bt (i-1)·(w i - M)⁺`. -/
theorem sum_w_curT_le (c : ι) (w : ℕ → ℝ) (M : ℝ) (hw0 : w 0 ≤ M) (hB : ∀ i, 0 < Bt i)
    (a b : ℕ) (ha : E c ≤ a) :
    ∑ x ∈ Finset.Ico a b, w (curT E thr0 D Bt c x) ≤
      (b - a : ℕ) * M + ∑ i ∈ Finset.Ico 1 (thr0 c + 1), (Bt (i - 1) : ℝ) * max (w i - M) 0 := by
  have hsplit : ∑ x ∈ Finset.Ico a b, w (curT E thr0 D Bt c x) ≤
      ∑ x ∈ Finset.Ico a b, (M + max (w (curT E thr0 D Bt c x) - M) 0) :=
    Finset.sum_le_sum fun x _ => by have := le_max_left (w (curT E thr0 D Bt c x) - M) 0; linarith
  refine hsplit.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  refine add_le_add le_rfl ?_
  -- group by the value of the thread
  have hmaps : ∀ x ∈ Finset.Ico a b, curT E thr0 D Bt c x ∈ Finset.range (thr0 c + 1) := by
    intro x _
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (curT_le_thr0 c x))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos _)]
  have h0 : ∑ x ∈ (Finset.Ico a b).filter (fun x => curT E thr0 D Bt c x = 0),
      max (w (curT E thr0 D Bt c x) - M) 0 = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]; simp [hw0]
  rw [h0, zero_add]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
  have hfib : ∑ x ∈ (Finset.Ico a b).filter (fun x => curT E thr0 D Bt c x = i),
      max (w (curT E thr0 D Bt c x) - M) 0 =
      ((Finset.Ico a b).filter (fun x => curT E thr0 D Bt c x = i)).card * max (w i - M) 0 := by
    rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const, nsmul_eq_mul]
  rw [hfib]
  refine mul_le_mul_of_nonneg_right ?_ (le_max_right _ _)
  exact_mod_cast card_curT_eq_le c hi1 (hB _) a b ha

/-- **P0150 §1.1's bound.** With thread rates `x i` such that `1/x i ≤ max M (T/(n·Bt i))` (e.g.
`x i = min x_max (n·Bt i/T)`, `M = 1/x_max`), `1/x 0 ≤ M`, and ratio `Bt (i-1) ≤ ρ·Bt i`:
`Σ_{x ∈ [a,b)} 1/x(curT x) ≤ (b - a)·M + thr0 c·ρ·T/n`.
Scope: the theorem does not require `0 < x i`. Since `1/0 = 0` in Lean, a zero rate satisfies the hypotheses
vacuously and contributes `0`. The reading of the sum as the variance proxy of an importance-weighted slot
estimate is only meaningful for positive rates `x i > 0` (as for `x i = min x_max (n·Bt i/T)` with positive
parameters). -/
theorem sum_inv_rate_le (c : ι) (x : ℕ → ℝ) (M ρ : ℝ) (n T : ℝ) (hn : 0 < n) (hT : 0 ≤ T) (hM : 0 ≤ M)
    (hB : ∀ i, 0 < Bt i) (hρ : ∀ i, 1 ≤ i → (Bt (i - 1) : ℝ) ≤ ρ * Bt i)
    (hx0 : 1 / x 0 ≤ M) (hx : ∀ i, 1 ≤ i → 1 / x i ≤ max M (T / (n * Bt i)))
    (a b : ℕ) (ha : E c ≤ a) :
    ∑ u ∈ Finset.Ico a b, 1 / x (curT E thr0 D Bt c u) ≤ (b - a : ℕ) * M + thr0 c * (ρ * T / n) := by
  refine (sum_w_curT_le c (fun i => 1 / x i) M hx0 hB a b ha).trans (add_le_add le_rfl ?_)
  have hterm : ∀ i ∈ Finset.Ico 1 (thr0 c + 1), (Bt (i - 1) : ℝ) * max (1 / x i - M) 0 ≤ ρ * T / n := by
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Ico.1 hi).1
    have hb : (0 : ℝ) < Bt i := by exact_mod_cast hB i
    have hmax : max (1 / x i - M) 0 ≤ T / (n * Bt i) := by
      refine max_le ?_ (by positivity)
      have := hx i hi1
      rcases le_total M (T / (n * Bt i)) with h | h
      · rw [max_eq_right h] at this
        linarith
      · rw [max_eq_left h] at this
        linarith [show (0 : ℝ) ≤ T / (n * Bt i) by positivity]
    have hBi1 : (0 : ℝ) ≤ Bt (i - 1) := by positivity
    calc (Bt (i - 1) : ℝ) * max (1 / x i - M) 0 ≤ (ρ * Bt i) * (T / (n * Bt i)) :=
          mul_le_mul (hρ i hi1) hmax (le_max_right _ _) (le_trans hBi1 (hρ i hi1))
      _ = ρ * T / n := by field_simp
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  simp

end Pool.P0171
