import Pool.P0119.FOCount
import Pool.P0120.FOHz
import Pool.P0109.GoodFO
import Pool.P0091.Exp

/-!
# Expected regret of the one-free-observation threaded pool process (FO analogue of P0091)

Assembles P0112's per-run walk bound, P0120's record errors, P0119's bad-point count, P0109's pool sizes with
adapted data and P0091's opportunity probability into one expectation bound, over the sampling/filter coins
(P0082's array, law `pC ps q`) and i.i.d. uniform slots, for an abstract learner.

* `nBad_evFO`, `sum_nBad_evFO`: the bad points of P0112's walk data `evFO` are P0119's bad opportunities.
* `run_bound_FO_count`: on runs satisfying P0120's `HzProp`, with epoch ratios `≤ ρ`,
  `Σ (A − g) ≤ C₀ + W·#bad`.
* `sum_wR_one`, **`expected_bound_FO`**: `E[Σ (A − g)] ≤ C₀ + W·(D·Lv·S/π + D·NE·Pna) + NE·Bep·(Pna + D·NE·(NE+1)·e^{−x})`,
  `Pna` = probability that the actual run is not `GoodA`.
* `goodA_of_goodRunT`, `prob_notGoodA_le`: `Pna ≤ P0073's bad-run probability` (P0109, bridged to the uncurried
  coin array by P0091's `wtv_uncurryT`).
* **`expected_regret_FO`**: everything combined in closed form, under P0085's schedule `levTh`.

Scope: the learner is abstract (within `α + β·len` of the actual run's REALIZED ESTIMATES of every present copy, and
within `Bep` of the comparator per unit; `A` may depend on all coins). No machine, no parameter choice.

**Reading of `A` (important).** `hA` compares `A` with the REALIZED slot estimates `Chat` pathwise (for every coin
vector and slot sequence), while the conclusion subtracts the TRUE comparator loss `g`. A learner's true expected
loss `⟨p_u, L_u⟩` does not satisfy `hA` pathwise in general. The usable reading is `A u := ⟨p_u, ℓ̂_u⟩`, the learner's
ESTIMATED loss (then `hBep` needs `Bep ≥ s`). So the bounded quantity is `E[Σ (A − g)]` for this abstract `A`, which
may depend on all coins, including future ones; it is NOT yet the expected regret of a machine. Turning it into one
needs an unbiasedness step `E[estimated learner loss] = E[true learner loss]` under the actual law (valid on
overflow-free runs), which is not proved here.
-/

namespace Pool.P0126

open Finset Pool.P0095 Pool.P0065 Pool.P0081 Pool.P0082 Pool.P0048 Pool.P0105 Pool.P0112 Pool.P0111
  Pool.P0119 Pool.P0120

attribute [local instance] coinFintype

section Pointwise

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ} {NE : ℕ} {s : ℕ} {L : ℕ → ι → ℝ}

/-- The walk's bad points of thread `j < D` are the bad opportunities `(j, a)` of `count_bad_FO`. -/
theorem nBad_evFO (cstar : ℕ → ℕ → ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s)
    {j : ℕ} (hj : j < D) :
    Pool.P0057.nBad NE Bt (evFO E thr0 θ R K D Lv Bt lev s L NE cstar ωs φ y) j =
      #{a : Fin NE | Bt j ∣ a ∧ ωs (cstar j a) = false ∧
        evict E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar j a)) (forceS ωs (cstar j a))
          (forceF K φ (cstar j a)) y) θ R K D Lv Bt lev NE cstar ωs φ j a = none} := by
  unfold Pool.P0057.nBad
  rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  congr 1
  ext s'
  simp only [mem_filter, mem_range, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hs, hd, hn⟩
    refine ⟨⟨s', hs⟩, ⟨hd, ?_⟩, rfl⟩
    unfold evFO evWF at hn
    rw [if_pos ⟨hj, hd, hs⟩] at hn
    split_ifs at hn with h
    · exact ⟨by simpa using h, hn⟩
  · rintro ⟨a, ⟨hd, hs, hn⟩, rfl⟩
    refine ⟨a.2, hd, ?_⟩
    unfold evFO evWF
    rw [if_pos ⟨hj, hd, a.2⟩, if_neg (by simp [hs])]
    exact hn

open Classical in
theorem sum_nBad_evFO (cstar : ℕ → ℕ → ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s) :
    ∑ j ∈ range D, (Pool.P0057.nBad NE Bt (evFO E thr0 θ R K D Lv Bt lev s L NE cstar ωs φ y) j : ℝ) =
      #{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωs (cstar ja.1 ja.2) = false ∧
        evict E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar ja.1 ja.2)) (forceS ωs (cstar ja.1 ja.2))
          (forceF K φ (cstar ja.1 ja.2)) y) θ R K D Lv Bt lev NE cstar ωs φ ja.1 ja.2 = none} := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => (Pool.P0057.nBad NE Bt
    (evFO E thr0 θ R K D Lv Bt lev s L NE cstar ωs φ y) j : ℝ))]
  simp only [fun j : Fin D => nBad_evFO (E := E) (thr0 := thr0) (θ := θ) (R := R) (Lv := Lv) (lev := lev)
    (NE := NE) (Bt := Bt) (s := s) (L := L) cstar ωs φ y j.2]
  rw [Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.card_filter]
  push_cast
  rfl

end Pointwise

section RunCount

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ} {NE : ℕ} {s : ℕ} {L : ℕ → ι → ℝ}

open Classical in
/-- **Per-run FO bound with the bad points counted as in `count_bad_FO`**, on runs where the record errors are
at most `zW s x`. With epoch ratios at most `ρ`:
`Σ (A − g) ≤ (θ + Rα + 2s·x)·NE/B₀ + β·NE + 2√(s·x)·NE/√B₀ + W·#bad`,
`W = (θ + Rα + 2s·x)·ρ + 2√(s·x)·ρ·√B₀ + Bep`. -/
theorem run_bound_FO_count (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hT : Bt 0 ∣ NE) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s)
    (A : ℕ → ℝ) (α β Bep : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R) (hBep0 : 0 ≤ Bep)
    (hA : ∀ f a b, a ≤ b → (∀ u, a ≤ u → u < b → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u).pools r ℓ) →
      ∑ u ∈ Finset.Ico a b, A u ≤ Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y f b -
        Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y f a + α + β * ((b - a : ℕ) : ℝ))
    (g : ℕ → ℝ) (hBep : ∀ u, A u - g u ≤ Bep) {x : ℝ} (hx : 0 ≤ x)
    (hz : HzProp E thr0 θ R K D Lv Bt lev s L cstar ωs φ NE g x y)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ∀ j, j + 1 < D → (Bt j : ℝ) ≤ ρ * Bt (j + 1)) :
    ∑ u ∈ Finset.range NE, (A u - g u) ≤
      (θ + R * α + 2 * s * x) * (NE / Bt 0) + β * NE + 2 * Real.sqrt (s * x) * (NE / Real.sqrt (Bt 0)) +
        ((θ + R * α + 2 * s * x) * ρ + 2 * Real.sqrt (s * x) * ρ * Real.sqrt (Bt 0) + Bep) *
          #{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωs (cstar ja.1 ja.2) = false ∧
            evict E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar ja.1 ja.2))
              (forceS ωs (cstar ja.1 ja.2)) (forceF K φ (cstar ja.1 ja.2)) y)
              θ R K D Lv Bt lev NE cstar ωs φ ja.1 ja.2 = none} := by
  have hsx : (0 : ℝ) ≤ s * x := mul_nonneg (Nat.cast_nonneg s) hx
  have za0 : (0 : ℝ) ≤ 2 * Real.sqrt (s * x) := by positivity
  have zb0 : (0 : ℝ) ≤ 2 * s * x := by positivity
  have h1 := run_bound_FO_closed (θ := θ) hB hLv hlev hT s L cstar hE hthr ωs φ y A α β Bep hα hβ hθ hR1 hBep0 hA
    g hBep (2 * Real.sqrt (s * x)) (2 * s * x) za0 zb0 (fun τ r e hd hτ hr he => by
      have := hz τ r e hd hτ hr he
      unfold zW at this
      have hsq : Real.sqrt (s * ((e - τ : ℕ) : ℝ) * x) = Real.sqrt (s * x) * Real.sqrt ((e - τ : ℕ) : ℝ) := by
        rw [show (s : ℝ) * ((e - τ : ℕ) : ℝ) * x = (s * x) * ((e - τ : ℕ) : ℝ) by ring]
        exact Real.sqrt_mul hsx _
      rw [hsq] at this
      linarith)
  simp only at h1
  rw [← sum_nBad_evFO cstar ωs φ y]
  set H := Pool.P0057.nBad NE Bt (evFO E thr0 θ R K D Lv Bt lev s L NE cstar ωs φ y)
  have hc0 : (0 : ℝ) ≤ θ + R * α + 2 * s * x := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    positivity
  have hD : D = (D - 1) + 1 := by have := hB.hD; omega
  have hsplit : ∑ j ∈ range D, (H j : ℝ) = ∑ j ∈ range (D - 1), (H j : ℝ) + H (D - 1) := by
    conv_lhs => rw [hD]
    rw [Finset.sum_range_succ]
  have hratio : ∑ j ∈ range (D - 1), (Bt j : ℝ) * H j / Bt (j + 1) ≤ ρ * ∑ j ∈ range (D - 1), (H j : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' : j + 1 < D := by rw [Finset.mem_range] at hj; omega
    have hpos : (0 : ℝ) < Bt (j + 1) := by exact_mod_cast hB.pos (j + 1)
    rw [div_le_iff₀ hpos]
    have := hρ j hj'
    have hH : (0 : ℝ) ≤ H j := Nat.cast_nonneg _
    nlinarith
  have hB0 : ∀ j, j < D → (Bt j : ℝ) ≤ Bt 0 := fun j hj => by
    exact_mod_cast Nat.le_of_dvd (hB.pos 0) (hB.dvd_of_le (Nat.zero_le j) hj)
  have hsqrt : ∑ j ∈ Finset.Ico 1 D, (Bt (j - 1) : ℝ) * H (j - 1) / Real.sqrt (Bt j) ≤
      ρ * Real.sqrt (Bt 0) * ∑ j ∈ range (D - 1), (H j : ℝ) := by
    rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
    rw [show D - 1 = D - 1 from rfl]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_range] at hj
    simp only [show 1 + j = j + 1 by omega]
    have hpos : (0 : ℝ) < Bt (j + 1) := by exact_mod_cast hB.pos (j + 1)
    have hsp : 0 < Real.sqrt (Bt (j + 1)) := Real.sqrt_pos.mpr hpos
    rw [div_le_iff₀ hsp]
    have hH : (0 : ℝ) ≤ H j := Nat.cast_nonneg _
    have h2 := hρ j (by omega)
    have h3 : Real.sqrt (Bt (j + 1)) ≤ Real.sqrt (Bt 0) := Real.sqrt_le_sqrt (hB0 (j + 1) (by omega))
    have h4 : (Bt (j + 1) : ℝ) = Real.sqrt (Bt (j + 1)) * Real.sqrt (Bt (j + 1)) :=
      (Real.mul_self_sqrt hpos.le).symm
    have h5 : (Bt j : ℝ) ≤ ρ * Real.sqrt (Bt (j + 1)) * Real.sqrt (Bt (j + 1)) := by rw [mul_assoc, ← h4]; exact h2
    have h7 : ρ * Real.sqrt (Bt (j + 1)) * Real.sqrt (Bt (j + 1)) ≤ ρ * Real.sqrt (Bt 0) * Real.sqrt (Bt (j + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hρ0) hsp.le
    have h8 := mul_le_mul_of_nonneg_right (h5.trans h7) hH
    calc (Bt j : ℝ) * H j ≤ ρ * Real.sqrt (Bt 0) * Real.sqrt (Bt (j + 1)) * H j := h8
      _ = ρ * Real.sqrt (Bt 0) * H j * Real.sqrt (Bt (j + 1)) := by ring
  have hlast : ((Bt (D - 1) * H (D - 1) : ℕ) : ℝ) = H (D - 1) := by rw [hB.last, one_mul]
  rw [hlast] at h1
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ range (D - 1), (H j : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hHl : (0 : ℝ) ≤ H (D - 1) := Nat.cast_nonneg _
  rw [hsplit]
  have e1 : (θ + R * α + 2 * s * x) * (NE / Bt 0 + ∑ j ∈ range (D - 1), (Bt j : ℝ) * H j / Bt (j + 1)) ≤
      (θ + R * α + 2 * s * x) * (NE / Bt 0) + (θ + R * α + 2 * s * x) * ρ * ∑ j ∈ range (D - 1), (H j : ℝ) := by
    have := mul_le_mul_of_nonneg_left hratio hc0
    calc (θ + R * α + 2 * s * x) * (NE / Bt 0 + ∑ j ∈ range (D - 1), (Bt j : ℝ) * H j / Bt (j + 1))
        = (θ + R * α + 2 * s * x) * (NE / Bt 0) +
            (θ + R * α + 2 * s * x) * ∑ j ∈ range (D - 1), (Bt j : ℝ) * H j / Bt (j + 1) := by ring
      _ ≤ (θ + R * α + 2 * s * x) * (NE / Bt 0) +
            (θ + R * α + 2 * s * x) * (ρ * ∑ j ∈ range (D - 1), (H j : ℝ)) := by linarith
      _ = _ := by ring
  have e2 : 2 * Real.sqrt (s * x) * (NE / Real.sqrt (Bt 0) +
        ∑ j ∈ Finset.Ico 1 D, (Bt (j - 1) : ℝ) * H (j - 1) / Real.sqrt (Bt j)) ≤
      2 * Real.sqrt (s * x) * (NE / Real.sqrt (Bt 0)) +
        2 * Real.sqrt (s * x) * ρ * Real.sqrt (Bt 0) * ∑ j ∈ range (D - 1), (H j : ℝ) := by
    rw [mul_add]
    have := mul_le_mul_of_nonneg_left hsqrt za0
    nlinarith
  have hsq0 : 0 ≤ 2 * Real.sqrt (s * x) * ρ * Real.sqrt (Bt 0) := by positivity
  nlinarith [mul_nonneg hBep0 hS0, mul_nonneg (mul_nonneg hc0 hρ0) hHl, mul_nonneg hsq0 hHl]

end RunCount

section Expected

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ} {NE Lt : ℕ} {s : ℕ} {L : ℕ → ι → ℝ}

theorem sum_wR_one [NeZero s] (T : ℕ) : ∑ yy : Fin T → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy = 1 :=
  Pool.P0097.sum_wR _ (by simp [Finset.sum_const, Finset.card_univ]) T

open Classical in
/-- **Expected regret of the one-free-observation threaded process** (any product law `p` on P0082's coins,
i.i.d. uniform slots, abstract learner). With `Pna` the probability that the actual run is not `GoodA`:
`E[Σ (A − g)] ≤ C₀ + W·(D·Lv·S/π + D·NE·Pna) + NE·Bep·(Pna + D·NE·(NE+1)·e^{−x})`, where
`C₀ = (θ + Rα + 2s·x)·NE/B₀ + β·NE + 2√(s·x)·NE/√B₀` and `W = (θ + Rα + 2s·x)·ρ + 2√(s·x)·ρ·√B₀ + Bep`.
The left side is `E[Σ (A − g)]` for the abstract `A` of `hA` (compared with REALIZED estimates pathwise; the usable
reading is the learner's ESTIMATED loss, see the module docstring); it is not yet a true expected regret. -/
theorem expected_bound_FO [NeZero s] (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hT : Bt 0 ∣ NE) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1)
    (g : ℕ → ℝ) (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < NE → L u (cstar j a) = g u)
    (A : (SlotC NE D Lt K × ι → Bool) → (Fin NE → Fin s) → ℕ → ℝ) (α β Bep : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hθ : 0 ≤ θ) (hR1 : 1 ≤ R) (hBep0 : 0 ≤ Bep)
    (hA : ∀ ω yy f a b, a ≤ b → (∀ u, a ≤ u → u < b → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt (ωsC E NE D Lt K ω) u
      (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) u).pools
        r ℓ) →
      ∑ u ∈ Finset.Ico a b, A ω yy u ≤
        Chat E thr0 θ R K D Lv Bt lev s L (occSort s) (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) f b -
        Chat E thr0 θ R K D Lv Bt lev s L (occSort s) (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) f a +
          α + β * ((b - a : ℕ) : ℝ))
    (hBep : ∀ ω yy u, A ω yy u - g u ≤ Bep) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ j, j + 1 < D → (Bt j : ℝ) ≤ ρ * Bt (j + 1))
    (p : SlotC NE D Lt K × ι → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (π : ℝ) (hπ : 0 < π)
    (hπ1 : π ≤ 1)
    (hpi : ∀ (j : Fin D) (a : Fin NE) (h : Bt j ∣ a),
      π ≤ piS p (oppSet E thr0 D Bt lev NE Lt K (cstar j a)
        (by rw [hE j a (by omega) h a.2]; exact a.2)) oppVal)
    (S : ℕ) (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s) {x : ℝ} (hx : 0 < x) :
    ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        ∑ u ∈ Finset.range NE, (A ω yy u - g u) ≤
      ((θ + R * α + 2 * s * x) * (NE / Bt 0) + β * NE + 2 * Real.sqrt (s * x) * (NE / Real.sqrt (Bt 0))) +
        ((θ + R * α + 2 * s * x) * ρ + 2 * Real.sqrt (s * x) * ρ * Real.sqrt (Bt 0) + Bep) *
          ((D * Lv * S : ℝ) / π + D * NE * ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s,
            Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
            (if GoodA E thr0 θ R K D Lv Bt lev s L NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy)
              then 0 else 1)) +
        NE * Bep * (∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
            (if GoodA E thr0 θ R K D Lv Bt lev s L NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy)
              then 0 else 1) + D * NE * (NE + 1) * Real.exp (-x)) := by
  have hw : ∀ ω, 0 ≤ wtv p ω := wtv_nonneg hp0 hp1
  have hwR : ∀ yy : Fin NE → Fin s, 0 ≤ Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy := wR_nonneg_s s
  set C0 := (θ + R * α + 2 * s * x) * (NE / Bt 0) + β * NE + 2 * Real.sqrt (s * x) * (NE / Real.sqrt (Bt 0))
    with hC0
  set W := (θ + R * α + 2 * s * x) * ρ + 2 * Real.sqrt (s * x) * ρ * Real.sqrt (Bt 0) + Bep with hW
  have hC00 : 0 ≤ C0 := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    positivity
  have hW0 : 0 ≤ W := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    positivity
  set Nb : (SlotC NE D Lt K × ι → Bool) → (Fin NE → Fin s) → ℝ := fun ω yy =>
    (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar ja.1 ja.2))
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (extY s yy))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ) with hNb
  set Ina : (SlotC NE D Lt K × ι → Bool) → (Fin NE → Fin s) → ℝ := fun ω yy =>
    if GoodA E thr0 θ R K D Lv Bt lev s L NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) then 0 else 1
    with hIna
  set Ihz : (SlotC NE D Lt K × ι → Bool) → (Fin NE → Fin s) → ℝ := fun ω yy =>
    if (∀ u < NE, (Vat E thr0 θ R K D Lv Bt lev s L (occSort s) (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
          (extY s yy) u).card + 1 ≤ s) ∧
        ¬ HzProp E thr0 θ R K D Lv Bt lev s L cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) NE g x (extY s yy)
      then 1 else 0 with hIhz
  -- pointwise
  have hpt : ∀ ω yy, ∑ u ∈ Finset.range NE, (A ω yy u - g u) ≤ C0 + W * Nb ω yy + NE * Bep * (Ina ω yy + Ihz ω yy) := by
    intro ω yy
    have hN0 : 0 ≤ Nb ω yy := Nat.cast_nonneg _
    have hI0 : 0 ≤ Ina ω yy := by simp only [hIna]; split_ifs <;> norm_num
    have hJ0 : 0 ≤ Ihz ω yy := by simp only [hIhz]; split_ifs <;> norm_num
    have hNEB : 0 ≤ (NE : ℝ) * Bep := mul_nonneg (Nat.cast_nonneg _) hBep0
    have hall : ∑ u ∈ Finset.range NE, (A ω yy u - g u) ≤ NE * Bep := by
      calc ∑ u ∈ Finset.range NE, (A ω yy u - g u) ≤ ∑ _u ∈ Finset.range NE, Bep :=
            Finset.sum_le_sum fun u _ => hBep ω yy u
        _ = NE * Bep := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    by_cases hga : GoodA E thr0 θ R K D Lv Bt lev s L NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy)
    · by_cases hz : HzProp E thr0 θ R K D Lv Bt lev s L cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) NE g x (extY s yy)
      · have := run_bound_FO_count hB hLv hlev hT cstar hE hthr (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy)
          (A ω yy) α β Bep hα hβ hθ hR1 hBep0 (hA ω yy) g (hBep ω yy) hx.le hz ρ hρ0 hρ
        have : ∑ u ∈ Finset.range NE, (A ω yy u - g u) ≤ C0 + W * Nb ω yy := by
          simp only [hC0, hW, hNb]; convert this using 3
        nlinarith [mul_nonneg hNEB (add_nonneg hI0 hJ0)]
      · have h1 : Ihz ω yy = 1 := by
          simp only [hIhz]; rw [if_pos ⟨fun u hu => hga.1 u hu, hz⟩]
        rw [h1]
        nlinarith [mul_nonneg hW0 hN0, mul_nonneg hNEB hI0]
    · have h1 : Ina ω yy = 1 := by simp only [hIna]; rw [if_neg hga]
      rw [h1]
      nlinarith [mul_nonneg hW0 hN0, mul_nonneg hNEB hJ0]
  -- expectations
  have hcnt := count_bad_FO E thr0 θ R K D Lv Bt lev s L hB hLv hlev cstar hE hthr p hp0 hp1 π hπ hπ1 hpi S
  have hhz : ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * Ihz ω yy ≤
      D * NE * (NE + 1) * Real.exp (-x) := by
    calc ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * Ihz ω yy
        ≤ ∑ ω, wtv p ω * (D * NE * (NE + 1) * Real.exp (-x)) := by
          refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hw ω)
          have := prob_not_hz E thr0 θ R K D Lv Bt lev s L hB hLv hlev hT cstar hE hthr (ωsC E NE D Lt K ω)
            (φC NE D Lt K ω) g hg hL0 hL1 ν hν hx
          simp only [Pool.P0111.wgt_eq_wR ν hν] at this
          simpa only [hIhz] using this
      _ = D * NE * (NE + 1) * Real.exp (-x) := by
          rw [← Finset.sum_mul, show ∑ ω, wtv p ω = 1 by convert sum_wtv p, one_mul]
  have hsw : ∑ ω, wtv p ω = 1 := by convert sum_wtv p
  have hsR := sum_wR_one (s := s) NE
  have hlin : ∀ (F G H' : (SlotC NE D Lt K × ι → Bool) → (Fin NE → Fin s) → ℝ),
      ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        (C0 + W * F ω yy + NE * Bep * (G ω yy + H' ω yy)) =
      C0 + W * (∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * F ω yy) +
        NE * Bep * (∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * G ω yy +
          ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * H' ω yy) := by
    intro F G H'
    have e1 : ∀ ω, ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        (C0 + W * F ω yy + NE * Bep * (G ω yy + H' ω yy)) =
        C0 * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy +
          W * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * F ω yy +
          NE * Bep * (∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * G ω yy +
            ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * H' ω yy) := by
      intro ω
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun yy _ => by ring
    simp only [e1, hsR, mul_one]
    have e2 : ∀ ω, wtv p ω * (C0 + W * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * F ω yy +
          NE * Bep * (∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * G ω yy +
            ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * H' ω yy)) =
        C0 * wtv p ω + W * (wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * F ω yy) +
          NE * Bep * (wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * G ω yy) +
          NE * Bep * (wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * H' ω yy) := by
      intro ω; ring
    rw [Finset.sum_congr rfl fun ω _ => e2 ω]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsw]
    ring
  calc _ ≤ ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
          (C0 + W * Nb ω yy + NE * Bep * (Ina ω yy + Ihz ω yy)) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun yy _ =>
          mul_le_mul_of_nonneg_left (hpt ω yy) (hwR yy)) (hw ω)
    _ = _ := hlin Nb Ina Ihz
    _ ≤ _ := by
        have hNEB : 0 ≤ (NE : ℝ) * Bep := mul_nonneg (Nat.cast_nonneg _) hBep0
        gcongr

end Expected

section GoodA

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ} {NE Lt : ℕ} {s : ℕ} {L : ℕ → ι → ℝ}

/-- **On a good run (P0073's `GoodRunT` for the realized estimates), the actual FO run is `GoodA`**, with
`S = s0 + D·Lv·S' + 1` and at least `D·((s0 + D·Lv·S') + (Lv−1)·S') + D·s0 + 1` slots. -/
theorem goodA_of_goodRunT (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (ω2 : Pool.P0073.SlotT NE D Lt K → ι → Bool) (y : ℕ → Fin s) (s0 : ℕ) (M0 ρ : ℝ) (S' : ℕ) (hρ : 0 ≤ ρ)
    (hg : Pool.P0073.GoodRunT E thr0
      (Chat E thr0 θ R K D Lv Bt lev s L (occSort s) (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) y)
      θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) NE s0 M0 ρ)
    (hM0S : M0 ≤ S') (hρS : ρ * ((S' : ℝ) + (s0 + D * Lv * S')) ≤ S')
    (hs : (D : ℝ) * ((s0 + D * Lv * S') + (Lv - 1 : ℕ) * S') + D * s0 + 1 ≤ s) :
    GoodA E thr0 θ R K D Lv Bt lev s L NE (s0 + D * Lv * S' + 1) (Pool.P0073.ωsOfT E K D ω2)
      (Pool.P0073.φOfT K D ω2) y := by
  have hcard := fun a ha => Pool.P0073.tpools_card_le hB hLv hlev _ _ NE s0 M0 ρ S' hρ hg hM0S (Nat.cast_nonneg _) hρS a ha
  refine ⟨fun u hu => ?_, fun r hr ℓ hℓ => ?_⟩
  · have hpe := foRun_pools_eq E thr0 θ R K D Lv Bt lev s L (occSort s) (Pool.P0073.ωsOfT E K D ω2)
      (Pool.P0073.φOfT K D ω2) y u
    have h := Pool.P0109.members_startPools_card_le E thr0 D Lv Bt (Pool.P0073.ωsOfT E K D ω2) u _ s0 S'
      (s0 + D * Lv * S') (hcard u hu.le).1 (hcard u hu.le).2.1 (fun r hr hd => hg.1 u hu r hr hd)
    rw [← hpe] at h
    have : ((Vst E thr0 D Lv Bt (Pool.P0073.ωsOfT E K D ω2) u
        (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) y u)).card
        : ℝ) + 1 ≤ s := by
      unfold Vst; linarith
    exact_mod_cast this
  · have hpe := foRun_pools_eq E thr0 θ R K D Lv Bt lev s L (occSort s) (Pool.P0073.ωsOfT E K D ω2)
      (Pool.P0073.φOfT K D ω2) y NE
    rw [hpe]
    obtain ⟨h1, h2, -⟩ := hcard NE le_rfl
    have hDLv : (S' : ℝ) ≤ D * Lv * S' := by
      have : (1 : ℝ) ≤ D * Lv := by
        have : (1 : ℕ) ≤ D * Lv := Nat.one_le_iff_ne_zero.2 (by have := hB.hD; positivity)
        exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) S']
    rcases Nat.eq_zero_or_pos ℓ with hl | hl
    · subst hl
      have := h2 r
      have : ((tpools E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occSort s) (Pool.P0073.ωsOfT E K D ω2)
          (Pool.P0073.φOfT K D ω2) y) θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) NE r 0).card
          : ℝ) + 1 ≤ ((s0 + D * Lv * S' + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have := h1 r ℓ (by omega)
      have : ((tpools E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occSort s) (Pool.P0073.ωsOfT E K D ω2)
          (Pool.P0073.φOfT K D ω2) y) θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) NE r ℓ).card
          : ℝ) + 1 ≤ ((s0 + D * Lv * S' + 1 : ℕ) : ℝ) := by
        push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) s0]
      exact_mod_cast this

end GoodA

section NotGood

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ} {NE Lt : ℕ} {s : ℕ} {L : ℕ → ι → ℝ}

open Classical in
/-- **The actual FO run is `GoodA` except with P0073's probability**, for every fixed slot sequence (P0109). -/
theorem prob_notGoodA_le {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hE : Monotone E) (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1)
    (hR : 1 ≤ R) (hT : (s : ℝ) * NE ≤ 2 ^ (R - 1) * θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * R ≤ M0)
    (hk : 4 * R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * R))
    (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S') (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * ((S' : ℝ) + (s0 + D * Lv * S')) ≤ S')
    (hsl : (D : ℝ) * ((s0 + D * Lv * S') + (Lv - 1 : ℕ) * S') + D * s0 + 1 ≤ s) (y : ℕ → Fin s) :
    ∑ ω, wtv (Pool.P0091.pC (NE := NE) (D := D) (Lt := Lt) (K := K) ps q) ω *
      (if GoodA E thr0 θ R K D Lv Bt lev s L NE (s0 + D * Lv * S' + 1) (ωsC E NE D Lt K ω) (φC NE D Lt K ω) y
        then 0 else 1) ≤
      NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0 := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hρ0 : 0 ≤ (1 - 1 / (4 * R : ℝ)) ^ K := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  rw [← (Equiv.curry (Pool.P0073.SlotT NE D Lt K) ι Bool).symm.sum_comp]
  refine le_trans (Finset.sum_le_sum fun ω2 _ => ?_) (Pool.P0109.prob_not_goodRunT_FO E thr0 θ R K D Lv Bt lev s L
    (occSort s) y M0 kk hps hq0 hq1 hE hB.hD hLv hlev hL0 hL1 hR hT hM0 hk hp hlevLt s0 δs hs)
  simp only [Equiv.curry_symm_apply]
  rw [Pool.P0091.wtv_uncurryT ω2]
  have hw0 : 0 ≤ Pool.P0046.bw2 (Pool.P0073.qOfT K D ps q) ω2 :=
    Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
      cases s <;> split_ifs <;> simp [Pool.P0073.qOfT] <;> linarith [hps.1, hps.2]
  refine mul_le_mul_of_nonneg_left ?_ hw0
  have hωs : ωsC E NE D Lt K (Function.uncurry ω2) = Pool.P0073.ωsOfT E K D ω2 := rfl
  have hφ : φC NE D Lt K (Function.uncurry ω2) = Pool.P0073.φOfT K D ω2 := rfl
  rw [hωs, hφ]
  by_cases hg : Pool.P0073.GoodRunT E thr0 (Pool.P0109.Cof E thr0 θ R K D Lv Bt lev s L (occSort s) y ω2) θ R K D Lv
      Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
  · rw [if_pos (goodA_of_goodRunT hB hLv hlev ω2 y s0 M0 _ S' hρ0 hg hM0S hρS hsl)]
    split_ifs; norm_num
  · rw [if_neg hg]; split_ifs <;> norm_num

end NotGood

section Final

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {NE Lt : ℕ} {s : ℕ} {L : ℕ → ι → ℝ}

open Classical in
/-- **Expected regret of the one-free-observation threaded pool process, closed form** (P0085's schedule
`levTh Ld Bt`, coin law `pC ps q`, i.i.d. uniform slots, abstract learner within `α + β·len` of the actual run's
realized estimates of every present copy, and within `Bep` of the comparator per unit):
`E[Σ_{u<NE} (A − g)] ≤ C₀ + W·(D·Lv·(s0 + D·Lv·S' + 1)/π + D·NE·P_bad) + NE·Bep·(P_bad + D·NE·(NE+1)·e^{−x})`,
with `π = ps(1−q)^{K·D(2Ld + NE/2^Ld + 1)}`, `P_bad = NE·D·δs + NE·D·(Lt+1)·K·delta` (P0073/P0109),
`C₀ = (θ + Rα + 2s·x)·NE/B₀ + β·NE + 2√(s·x)·NE/√B₀`, `W = (θ + Rα + 2s·x)·ρ + 2√(s·x)·ρ·√B₀ + Bep`.
Despite the name, the left side is `E[Σ (A − g)]` for the abstract `A` of `hA` (compared with REALIZED estimates
pathwise, so `A` should be read as the learner's ESTIMATED loss, with `Bep ≥ s`); the estimated-to-true step needed
for a machine's expected regret is not done here (module docstring). -/
theorem expected_regret_FO {Ld : ℕ} [NeZero s] (hB : BtHyp D Bt) (hLv2 : Ld + 2 ≤ Lv) (hLt : Ld ≤ Lt)
    (hT : Bt 0 ∣ NE) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1)
    (g : ℕ → ℝ) (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < NE → L u (cstar j a) = g u)
    (A : (SlotC NE D Lt K × ι → Bool) → (Fin NE → Fin s) → ℕ → ℝ) (α β Bep : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hθ : 0 ≤ θ) (hR1 : 1 ≤ R) (hBep0 : 0 ≤ Bep)
    (hA : ∀ ω yy f a b, a ≤ b → (∀ u, a ≤ u → u < b → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt (ωsC E NE D Lt K ω) u
      (foRun E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L (occSort s) (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
        (extY s yy) u).pools r ℓ) →
      ∑ u ∈ Finset.Ico a b, A ω yy u ≤
        Chat E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L (occSort s) (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
          (extY s yy) f b -
        Chat E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L (occSort s) (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
          (extY s yy) f a + α + β * ((b - a : ℕ) : ℝ))
    (hBep : ∀ ω yy u, A ω yy u - g u ≤ Bep) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ j, j + 1 < D → (Bt j : ℝ) ≤ ρ * Bt (j + 1))
    {ps q : ℝ} (hps0 : 0 < ps) (hps1 : ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (hEm : Monotone E)
    (hTθ : (s : ℝ) * NE ≤ 2 ^ (R - 1) * θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S') (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * ((S' : ℝ) + (s0 + D * Lv * S')) ≤ S')
    (hsl : (D : ℝ) * ((s0 + D * Lv * S') + (Lv - 1 : ℕ) * S') + D * s0 + 1 ≤ s)
    (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s) {x : ℝ} (hx : 0 < x) :
    ∑ ω, wtv (Pool.P0091.pC ps q) ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        ∑ u ∈ Finset.range NE, (A ω yy u - g u) ≤
      ((θ + R * α + 2 * s * x) * (NE / Bt 0) + β * NE + 2 * Real.sqrt (s * x) * (NE / Real.sqrt (Bt 0))) +
        ((θ + R * α + 2 * s * x) * ρ + 2 * Real.sqrt (s * x) * ρ * Real.sqrt (Bt 0) + Bep) *
          ((D * Lv * (s0 + D * Lv * S' + 1) : ℝ) / (ps * (1 - q) ^ (K * (D * (2 * Ld + NE / 2 ^ Ld + 1)))) +
            D * NE * (NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0)) +
        NE * Bep * ((NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0) +
          D * NE * (NE + 1) * Real.exp (-x)) := by
  have hD := hB.hD
  have hLv : 0 < Lv := by omega
  have hlev : ∀ r a, Pool.P0085.levTh Ld Bt r a + 1 < Lv := fun r a => by
    have := Pool.P0062.levPR_le Ld ((a + 1) / Bt r - 1)
    unfold Pool.P0085.levTh; omega
  have hlevLt : ∀ a < NE, ∀ r < D, Pool.P0085.levTh Ld Bt r a ≤ Lt := fun a _ r _ => by
    have := Pool.P0062.levPR_le Ld ((a + 1) / Bt r - 1)
    unfold Pool.P0085.levTh; omega
  have hp0 : ∀ x : SlotC NE D Lt K × ι, 0 ≤ Pool.P0091.pC ps q x := fun x => by
    rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith
  have hp1 : ∀ x : SlotC NE D Lt K × ι, Pool.P0091.pC ps q x ≤ 1 := fun x => by
    rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith
  set π := ps * (1 - q) ^ (K * (D * (2 * Ld + NE / 2 ^ Ld + 1))) with hπdef
  have hπ : 0 < π := mul_pos hps0 (pow_pos (by linarith) _)
  have hπ1 : π ≤ 1 := by
    have : (1 - q) ^ (K * (D * (2 * Ld + NE / 2 ^ Ld + 1))) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    calc π ≤ 1 * 1 := mul_le_mul hps1 this (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hpi : ∀ (j : Fin D) (a : Fin NE) (h : Bt j ∣ a),
      π ≤ piS (Pool.P0091.pC ps q) (oppSet E thr0 D Bt (Pool.P0085.levTh Ld Bt) NE Lt K (cstar j a)
        (by rw [hE j a (by omega) h a.2]; exact a.2)) oppVal := by
    intro j a h
    have he := hE j a (by omega) h a.2
    have ht := hthr j a (by omega) h a.2
    exact Pool.P0091.piS_geT hB hps0.le hq0 hq1.le (cstar j a) _ (by rw [he, ht]; exact h) (by rw [ht]; exact j.2)
  have h1 := expected_bound_FO (θ := θ) (L := L) hB hLv hlev hT cstar hE hthr hL0 hL1 g hg A α β Bep hα hβ hθ hR1
    hBep0 hA hBep ρ hρ0 hρ (Pool.P0091.pC ps q) hp0 hp1 π hπ hπ1 hpi (s0 + D * Lv * S' + 1) ν hν hx
  set Pbad := (NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0 : ℝ) with hPbad
  have hPna : ∑ ω, wtv (Pool.P0091.pC ps q) ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      (if GoodA E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L NE (s0 + D * Lv * S' + 1) (ωsC E NE D Lt K ω)
        (φC NE D Lt K ω) (extY s yy) then 0 else 1) ≤ Pbad := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ yy : Fin NE → Fin s, ∑ ω, wtv (Pool.P0091.pC ps q) ω * (Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
          (if GoodA E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L NE (s0 + D * Lv * S' + 1) (ωsC E NE D Lt K ω)
            (φC NE D Lt K ω) (extY s yy) then 0 else 1))
        = ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * ∑ ω, wtv (Pool.P0091.pC ps q) ω *
          (if GoodA E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L NE (s0 + D * Lv * S' + 1) (ωsC E NE D Lt K ω)
            (φC NE D Lt K ω) (extY s yy) then 0 else 1) := by
          refine Finset.sum_congr rfl fun yy _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * Pbad :=
          Finset.sum_le_sum fun yy _ => mul_le_mul_of_nonneg_left
            (prob_notGoodA_le ⟨hps0.le, hps1⟩ hq0 hq1.le hEm hB hLv hlev hL0 hL1 hR1 hTθ M0 kk hM0 hk hp hlevLt
              s0 δs hs S' hM0S hρS hsl (extY s yy)) (wR_nonneg_s s yy)
      _ = Pbad := by rw [← Finset.sum_mul, sum_wR_one, one_mul]
  have hW0 : 0 ≤ (θ + R * α + 2 * s * x) * ρ + 2 * Real.sqrt (s * x) * ρ * Real.sqrt (Bt 0) + Bep := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    positivity
  have hNB : (0 : ℝ) ≤ NE * Bep := mul_nonneg (Nat.cast_nonneg _) hBep0
  refine h1.trans ?_
  have hcast : ((D * Lv * (s0 + D * Lv * S' + 1) : ℕ) : ℝ) = (D * Lv * (s0 + D * Lv * S' + 1) : ℝ) := by push_cast; ring
  rw [hcast] at *
  gcongr
  push_cast; rfl

end Final

end Pool.P0126
