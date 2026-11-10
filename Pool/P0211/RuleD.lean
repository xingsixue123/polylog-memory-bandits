import Pool.P0194.Proc

open Finset Pool.P0001 Pool.P0050 Pool.P0194

/-!
# Rule (b″) did not fire, for P0194's per-thread process (P0196's `estGap_lt` for `dzRun`)

* `Pool.P0211.mem_aux_succ`: one round of retirement in P0194's pool (P0156's `mem_aux_succ` for `dzRun`).
* `Pool.P0211.estGapD`: the estimated gap since entry against B̂, as read by rule (b″) (`rhD`).
* **`Pool.P0211.estGapD_lt`**: a copy active at `c` and `c + 1` with `E x ≤ c`, `Bmin ∣ c + 1` has estimated gap
  `< Λ x c` at `c + 1`.
* **`Pool.P0211.check_le`**: with concentration (true gap ≤ estimated gap + `W` at the check), a copy active on
  `[E x, b)` has true gap `< Λ x (m − 1) + W` at every check boundary `m ∈ (E x, b)` — the check hypothesis of
  P0196/P0209-type probing bounds.

Deterministic and pathwise; concentration is a hypothesis (P0203 for the slot data, B̂'s width separately).
-/

namespace Pool.P0211

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- Retirement in P0194's pool, one round: a copy is retired at `u + 1` iff it was retired at `u`, or it is a
start-pool member at `u` and rule (b″) fires on its updated data. -/
theorem mem_aux_succ (ω : ℕ → RC P) (u : ℕ) (x : ι) :
    x ∈ (pool P ℓ ω ωs φ (u + 1)).aux ↔
      x ∈ (pool P ℓ ω ωs φ u).aux ∨
        (x ∈ Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u) ∧
          rhD P ℓ ω u x ((pool P ℓ ω ωs φ (u + 1)).est x) = true) := by
  show x ∈ (Pool.P0176.dzUpdO P.D P.Lv 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) u _ _ _ _).2 ↔ _
  simp only [Pool.P0176.dzUpdO, Finset.mem_union, Finset.mem_filter]
  rfl

/-- The estimated gap of copy `x` against BASE at boundary `m`, as read by rule (b″). -/
noncomputable def estGapD (ω : ℕ → RC P) (x : ι) (m : ℕ) : ℝ :=
  (pool P ℓ ω ωs φ m).est x m - (pool P ℓ ω ωs φ m).est x (P.E x) - (Bh P ℓ ω m - Bh P ℓ ω (P.E x))

/-- **Rule (b″) did not fire** (P0196's `estGap_lt` for P0194's per-thread process): if `x` is active at rounds
`c` and `c + 1`, `E x ≤ c` and `Bmin ∣ c + 1`, its estimated gap at `c + 1` is below the margin `Λ x c`. -/
theorem estGapD_lt (ω : ℕ → RC P) (x : ι) (c : ℕ) (hc : x ∈ active P ℓ ω ωs φ c)
    (hc1 : x ∈ active P ℓ ω ωs φ (c + 1)) (hE : P.E x ≤ c) (hB : P.Bmin ∣ c + 1) :
    estGapD P ℓ ωs φ ω x (c + 1) < P.Λ x c := by
  unfold active at hc hc1
  rw [Finset.mem_sdiff] at hc hc1
  have hnot := hc1.2
  rw [mem_aux_succ] at hnot
  push_neg at hnot
  have hrule := hnot.2 hc.1
  by_contra hge
  push_neg at hge
  apply hrule
  unfold rhD
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hE, hB⟩, hge⟩

/-- **Check bound from the rule** (the hypothesis `hcheck` of P0209-type probing bounds): if `x` is active on
`[E x, b)` and, at a check boundary `m` inside, the true gap since entry is at most the estimated gap plus `W`
(concentration, e.g. P0203 with B̂'s width), then the true gap at `m` is `< Λ x (m − 1) + W`. -/
theorem check_le (ω : ℕ → RC P) (x : ι) (b : ℕ)
    (hint : ∀ t, P.E x ≤ t → t < b → x ∈ active P ℓ ω ωs φ t) (W : ℝ) (m : ℕ) (hm1 : P.E x < m) (hm2 : m < b)
    (hdvd : P.Bmin ∣ m)
    (hconc : ∑ t ∈ Ico (P.E x) m, (ℓr P ℓ t x - bPol P ℓ ω t) ≤ estGapD P ℓ ωs φ ω x m + W) :
    ∑ t ∈ Ico (P.E x) m, (ℓr P ℓ t x - bPol P ℓ ω t) < P.Λ x (m - 1) + W := by
  have hlt := estGapD_lt P ℓ ωs φ ω x (m - 1) (hint (m - 1) (by omega) (by omega))
    (by rw [show m - 1 + 1 = m by omega]; exact hint m (by omega) hm2) (by omega)
    (by rw [show m - 1 + 1 = m by omega]; exact hdvd)
  rw [show m - 1 + 1 = m by omega] at hlt
  linarith

end Pool.P0211
