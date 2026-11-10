import Pool.P0086.Asm
import Pool.P0082.Count
import Pool.P0085.Count
import Pool.P0073.Prob

/-!
# Expected regret of the threaded (inheritance) K-query pool process

Assembles P0086's per-run walk bound, P0082's bad-opportunity count, P0085's thread slot count and
P0073's pool-size probability into one expectation bound (the threaded analogue of P0071's
`expected_bound`).

* `nBad_evW`, `sum_nBad_evW`: the walk's bad points (`nBad` of P0086's `evW`, summed over the threads)
  are exactly `count_bad`'s bad opportunities.
* `run_bound_count`: P0086's `run_bound_closed` with epoch ratios `≤ ρ`:
  `Σ (A - g) ≤ (θ + Rα)·NE/B 0 + β NE + ((θ + Rα) ρ + Bep)·#bad`.
* **`expected_boundT`**: for any product coin law, `E[Σ (A - g)] ≤ (θ + Rα)·NE/B 0 + β NE +
  ((θ + Rα) ρ + Bep)·(D·Lv·S/π + D·NE·P(not good))`.
* `pC` (P0073's law, uncurried), `piS_geT` (opportunity probability `≥ ps (1-q)^{K·D(2L+NE/2^L+1)}`
  under P0085's schedule `levTh L Bt`), `wtv_uncurryT`, `notGood_le` (the not-good term is at most
  P0073's bad-run probability).
* **`expected_regretT`**: everything combined, in closed form.

Scope: exact cumulative losses (`C = cumL cu`, the K-query setting); the learner is abstract (P0086's
hypothesis `hA`); no machine, no parameter choice.
-/

namespace Pool.P0091

open Finset Pool.P0065 Pool.P0081 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0048 Pool.P0082
  Pool.P0086

attribute [local instance] coinFintype

section Pointwise

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {C : ι → ℕ → ℝ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ} {NE : ℕ}

open Classical in
/-- The walk's bad points of thread `j < D` are the bad opportunities `(j, a)` of `count_bad`. -/
theorem nBad_evW (cstar : ℕ → ℕ → ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) {j : ℕ}
    (hj : j < D) :
    Pool.P0057.nBad NE Bt (evW E thr0 C θ R K D Lv Bt lev NE cstar ωs φ) j =
      #{a : Fin NE | Bt j ∣ a ∧ ωs (cstar j a) = false ∧
        evict E thr0 C θ R K D Lv Bt lev NE cstar ωs φ j a = none} := by
  unfold Pool.P0057.nBad
  rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  congr 1
  ext s
  simp only [mem_filter, mem_range, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hs, hd, hn⟩
    refine ⟨⟨s, hs⟩, ⟨hd, ?_⟩, rfl⟩
    unfold evW at hn
    rw [if_pos ⟨hj, hd, hs⟩] at hn
    split_ifs at hn with h
    · exact ⟨by simpa using h, hn⟩
  · rintro ⟨a, ⟨hd, hs, hn⟩, rfl⟩
    refine ⟨a.2, hd, ?_⟩
    unfold evW
    rw [if_pos ⟨hj, hd, a.2⟩, if_neg (by simp [hs])]
    exact hn

open Classical in
/-- Summing the walk's bad points over the threads gives `count_bad`'s set. -/
theorem sum_nBad_evW (cstar : ℕ → ℕ → ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) :
    ∑ j ∈ range D, (Pool.P0057.nBad NE Bt (evW E thr0 C θ R K D Lv Bt lev NE cstar ωs φ) j : ℝ) =
      #{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωs (cstar ja.1 ja.2) = false ∧
        evict E thr0 C θ R K D Lv Bt lev NE cstar ωs φ ja.1 ja.2 = none} := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => (Pool.P0057.nBad NE Bt
    (evW E thr0 C θ R K D Lv Bt lev NE cstar ωs φ) j : ℝ))]
  simp only [fun j : Fin D => nBad_evW (C := C) (θ := θ) (R := R) (Lv := Lv) (lev := lev) (NE := NE)
    (E := E) (thr0 := thr0) (Bt := Bt) cstar ωs φ j.2]
  rw [Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun j _ => ?_
  rw [Finset.card_filter]
  push_cast
  rfl

open Classical in
/-- **Per-run bound with the bad points counted as in `count_bad`.** If consecutive epoch lengths have
ratio at most `ρ`, then `Σ_{u<NE} (A u - g u) ≤ (θ + R α)·NE/B 0 + β NE + ((θ + R α) ρ + Bep)·#bad`, where
`#bad` is the number of opportunities `(j, a)` whose comparator copy is not sampled and, forced in, is never
evicted (exactly `count_bad`'s set, for `C = cumL cu`). -/
theorem run_bound_count (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hT : Bt 0 ∣ NE) (cu : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (g : ℕ → ℝ) (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < NE → cu u (cstar j a) = g u)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (A : ℕ → ℝ) (α β Bep : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R) (hBep0 : 0 ≤ Bep)
    (hA : ∀ f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ))
    (hBep : ∀ u, A u - g u ≤ Bep) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ j, j + 1 < D → (Bt j : ℝ) ≤ ρ * Bt (j + 1)) :
    ∑ u ∈ Finset.range NE, (A u - g u) ≤ (θ + R * α) * (NE / Bt 0) + β * NE +
      ((θ + R * α) * ρ + Bep) * #{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωs (cstar ja.1 ja.2) = false ∧
        evict E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev NE cstar ωs φ ja.1 ja.2 = none} := by
  have h1 := run_bound_closed (θ := θ) hB hLv hlev hT cu cstar hE hthr g hg ωs φ A α β Bep hα hβ hθ hR1
    hBep0 hA hBep
  simp only at h1
  rw [← sum_nBad_evW cstar ωs φ]
  set H := Pool.P0057.nBad NE Bt (evW E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev NE cstar ωs φ)
  have hc0 : (0 : ℝ) ≤ θ + R * α := by
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
  have hlast : ((Bt (D - 1) * H (D - 1) : ℕ) : ℝ) = H (D - 1) := by rw [hB.last, one_mul]
  rw [hlast] at h1
  have hS0 : (0 : ℝ) ≤ ∑ j ∈ range (D - 1), (H j : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hHl : (0 : ℝ) ≤ H (D - 1) := Nat.cast_nonneg _
  rw [hsplit]
  have e1 : (θ + R * α) * (NE / Bt 0 + ∑ j ∈ range (D - 1), (Bt j : ℝ) * H j / Bt (j + 1)) ≤
      (θ + R * α) * (NE / Bt 0) + (θ + R * α) * ρ * ∑ j ∈ range (D - 1), (H j : ℝ) := by
    rw [mul_add, mul_assoc]
    gcongr
  nlinarith [mul_nonneg hBep0 hS0, mul_nonneg (mul_nonneg hc0 hρ0) hHl]

end Pointwise

section Expected

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ} {NE Lt : ℕ}

open Classical in
/-- **Expected regret of the threaded process on the coin array** (any product law `p` on P0082's
coins). For a learner `A ω` satisfying P0086's hypotheses on every run `ω`:
`E[Σ_{u<NE} (A u - g u)] ≤ (θ + R α)·NE/B 0 + β NE + ((θ + R α) ρ + Bep)·(D·Lv·S/π + D·NE·P(not good))`,
where a run is good when every sub-pool at `NE` has at most `S - 1` copies. -/
theorem expected_boundT (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hT : Bt 0 ∣ NE) (cu : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (g : ℕ → ℝ) (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < NE → cu u (cstar j a) = g u)
    (A : (SlotC NE D Lt K × ι → Bool) → ℕ → ℝ) (α β Bep : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hθ : 0 ≤ θ)
    (hR1 : 1 ≤ R) (hBep0 : 0 ≤ Bep)
    (hA : ∀ ω f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ,
      f ∈ startPools E thr0 D Lv Bt (ωsC E NE D Lt K ω) u
        (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω) u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A ω u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ))
    (hBep : ∀ ω u, A ω u - g u ≤ Bep) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ j, j + 1 < D → (Bt j : ℝ) ≤ ρ * Bt (j + 1))
    (p : SlotC NE D Lt K × ι → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (π : ℝ) (hπ : 0 < π)
    (hπ1 : π ≤ 1)
    (hpi : ∀ (j : Fin D) (a : Fin NE) (h : Bt j ∣ a),
      π ≤ piS p (oppSet E thr0 D Bt lev NE Lt K (cstar j a)
        (by rw [hE j a (by omega) h a.2]; exact a.2)) oppVal)
    (S : ℕ) :
    ∑ ω, wtv p ω * ∑ u ∈ Finset.range NE, (A ω u - g u) ≤
      (θ + R * α) * (NE / Bt 0) + β * NE + ((θ + R * α) * ρ + Bep) * ((D * Lv * S : ℝ) / π +
        D * NE * ∑ ω, wtv p ω *
          (if ∀ r < D, ∀ ℓ < Lv, (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev (ωsC E NE D Lt K ω)
            (φC NE D Lt K ω) NE r ℓ).card + 1 ≤ S then 0 else 1)) := by
  have hw : ∀ ω, 0 ≤ wtv p ω := wtv_nonneg hp0 hp1
  have hc0 : (0 : ℝ) ≤ θ + R * α := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    positivity
  have hW : (0 : ℝ) ≤ (θ + R * α) * ρ + Bep := by positivity
  have hcount := count_bad (C := Pool.P0061.cumL cu) (θ := θ) (R := R) hB hLv hlev cstar hE hthr p hp0 hp1
    π hπ hπ1 hpi S
  set N : (SlotC NE D Lt K × ι → Bool) → ℝ := fun ω =>
    (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
      evict E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
        ja.1 ja.2 = none} : ℝ) with hN
  have hpt : ∀ ω, ∑ u ∈ Finset.range NE, (A ω u - g u) ≤
      (θ + R * α) * (NE / Bt 0) + β * NE + ((θ + R * α) * ρ + Bep) * N ω := by
    intro ω
    have := run_bound_count (θ := θ) hB hLv hlev hT cu cstar hE hthr g hg (ωsC E NE D Lt K ω)
      (φC NE D Lt K ω) (A ω) α β Bep hα hβ hθ hR1 hBep0 (hA ω) (hBep ω) ρ hρ0 hρ
    convert this using 3
  calc ∑ ω, wtv p ω * ∑ u ∈ Finset.range NE, (A ω u - g u)
      ≤ ∑ ω, wtv p ω * ((θ + R * α) * (NE / Bt 0) + β * NE + ((θ + R * α) * ρ + Bep) * N ω) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hw ω)
    _ = (θ + R * α) * (NE / Bt 0) + β * NE + ((θ + R * α) * ρ + Bep) * ∑ ω, wtv p ω * N ω := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
        have h1 : ∑ ω, wtv p ω = 1 := sum_wtv p
        rw [h1, Finset.mul_sum, one_mul, one_mul]
        congr 1
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ _ := by
        gcongr

end Expected

section Law

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {C : ι → ℕ → ℝ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {NE Lt : ℕ}

/-- P0073's coin law (`ps` on sampling slots, `q` on filter slots) on the uncurried coin array. -/
def pC (ps q : ℝ) : SlotC NE D Lt K × ι → ℝ := fun x => Pool.P0073.qOfT K D ps q x.1 x.2

open Classical in
/-- **Opportunity probability under P0085's schedule `levTh L Bt`**: a copy on its thread's grid has
opportunity probability at least `ps·(1-q)^{K·D(2L + NE/2^L + 1)}` (one sampling bit; P0085's slot count
for the filter bits). -/
theorem piS_geT {L : ℕ} (hB : BtHyp D Bt) {ps q : ℝ} (hps : 0 ≤ ps) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (c : ι) (hc : E c < NE) (hent : Bt (thr0 c) ∣ E c) (hthr : thr0 c < D) :
    ps * (1 - q) ^ (K * (D * (2 * L + NE / 2 ^ L + 1))) ≤
      piS (pC (Lt := Lt) ps q) (oppSet E thr0 D Bt (Pool.P0085.levTh L Bt) NE Lt K c hc) oppVal := by
  set F := (Finset.univ.filter fun s : Fin NE × Fin D × Fin (Lt + 1) × Fin K =>
    (s.2.1 : ℕ) = curT E thr0 D Bt c s.1 ∧ InSlotsT E thr0 D Bt (Pool.P0085.levTh L Bt) c s.1 s.2.2.1)
  have hnot : (Sum.inl ⟨E c, hc⟩, c) ∉ F.image fun s => ((Sum.inr s : SlotC NE D Lt K), c) := by
    simp
  have hF : F.card ≤ K * (D * (2 * L + NE / 2 ^ L + 1)) := by
    have h1 : F.card ≤ (Pool.P0085.slotsT E thr0 D Bt L NE c ×ˢ (Finset.univ : Finset (Fin K))).card := by
      refine Finset.card_le_card_of_injOn (fun s => (((s.1 : ℕ), (s.2.2.1 : ℕ)), s.2.2.2)) ?_ ?_
      · intro s hs
        simp only [F, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs
        simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Finset.mem_coe, Set.mem_univ,
          and_true]
        exact Pool.P0085.mem_slotsT s.1.2 hs.2
      · rintro ⟨x, r, ℓ, k⟩ hs ⟨x', r', ℓ', k'⟩ hs' heq
        simp only [F, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs hs'
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨h1, h2⟩, h3⟩ := heq
        have hx : x = x' := Fin.ext h1
        subst hx
        have hr : r = r' := Fin.ext (hs.1.trans hs'.1.symm)
        have hl : ℓ = ℓ' := Fin.ext h2
        subst hr hl h3
        rfl
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Pool.P0085.card_slotsT_le (L := L) (NE := NE) hB hent hthr
    calc F.card ≤ _ := h1
      _ ≤ D * (2 * L + NE / 2 ^ L + 1) * K := Nat.mul_le_mul_right _ h2
      _ = _ := Nat.mul_comm _ _
  unfold oppSet piS
  rw [Finset.prod_insert hnot, Finset.prod_image (fun s _ s' _ h => by simpa using h)]
  have hcw : ∀ s ∈ F, cw (pC (Lt := Lt) ps q ((Sum.inr s : SlotC NE D Lt K), c))
      (oppVal ((Sum.inr s : SlotC NE D Lt K), c)) = 1 - q := fun s _ => by
    simp [cw, pC, oppVal, Pool.P0073.qOfT]
  rw [Finset.prod_congr rfl hcw, Finset.prod_const]
  have hcw0 : cw (pC (Lt := Lt) ps q ((Sum.inl ⟨E c, hc⟩ : SlotC NE D Lt K), c))
      (oppVal ((Sum.inl ⟨E c, hc⟩ : SlotC NE D Lt K), c)) = ps := by
    simp [cw, pC, oppVal, Pool.P0073.qOfT]
  rw [hcw0]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by linarith) (by linarith) hF) hps

omit [LinearOrder ι] in
/-- P0048's weight of the uncurried array is P0046's `bw2` of the curried one. -/
theorem wtv_uncurryT {ps q : ℝ} (ω2 : Pool.P0073.SlotT NE D Lt K → ι → Bool) :
    wtv (pC ps q) (Function.uncurry ω2) = Pool.P0046.bw2 (Pool.P0073.qOfT K D ps q) ω2 := by
  unfold wtv Pool.P0046.bw2
  rw [Fintype.prod_prod_type]
  rfl

variable {lev : ℕ → ℕ → ℕ}

open Classical in
/-- The not-good term of `expected_boundT` (with `S := s0 + D·Lv·S + 1`) is at most P0073's bad-run
probability `P(some pool exceeds its P0073 bound at some a ≤ NE)`. -/
theorem notGood_le {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hD : 0 < D)
    (hLv : 0 < Lv) (s0 S : ℕ) :
    ∑ ω, wtv (pC ps q) ω *
        (if ∀ r < D, ∀ ℓ < Lv, (tpools E thr0 C θ R K D Lv Bt lev (ωsC E NE D Lt K ω)
            (φC NE D Lt K ω) NE r ℓ).card + 1 ≤ s0 + D * Lv * S + 1 then 0 else 1) ≤
      ∑ ω2 : Pool.P0073.SlotT NE D Lt K → ι → Bool, Pool.P0046.bw2 (Pool.P0073.qOfT K D ps q) ω2 *
        (if ∀ a ≤ NE, (∀ r ℓ, ℓ ≠ 0 →
            ((tpools E thr0 C θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) a r ℓ).card
              : ℝ) ≤ S) ∧
            (∀ r, ((tpools E thr0 C θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2)
              a r 0).card : ℝ) ≤ s0 + D * Lv * S)
          then 0 else 1) := by
  rw [← (Equiv.curry (Pool.P0073.SlotT NE D Lt K) ι Bool).symm.sum_comp]
  refine Finset.sum_le_sum fun ω2 _ => ?_
  simp only [Equiv.curry_symm_apply]
  have hw : wtv (pC ps q) (Function.uncurry ω2) = Pool.P0046.bw2 (Pool.P0073.qOfT K D ps q) ω2 :=
    wtv_uncurryT ω2
  rw [hw]
  have hw0 : 0 ≤ Pool.P0046.bw2 (Pool.P0073.qOfT K D ps q) ω2 :=
    Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
      cases s <;> split_ifs <;> simp [Pool.P0073.qOfT] <;> linarith
  refine mul_le_mul_of_nonneg_left ?_ hw0
  have hωs : ωsC E NE D Lt K (Function.uncurry ω2) = Pool.P0073.ωsOfT E K D ω2 := rfl
  have hφ : φC NE D Lt K (Function.uncurry ω2) = Pool.P0073.φOfT K D ω2 := rfl
  rw [hωs, hφ]
  by_cases hev : ∀ a ≤ NE, (∀ r ℓ, ℓ ≠ 0 →
      ((tpools E thr0 C θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) a r ℓ).card
        : ℝ) ≤ S) ∧
      (∀ r, ((tpools E thr0 C θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2)
        a r 0).card : ℝ) ≤ s0 + D * Lv * S)
  · rw [if_pos hev, if_pos]
    intro r _ ℓ _
    obtain ⟨h1, h2⟩ := hev NE le_rfl
    have hSle : S ≤ D * Lv * S := Nat.le_mul_of_pos_left _ (Nat.mul_pos hD hLv)
    rcases Nat.eq_zero_or_pos ℓ with hl | hl
    · subst hl
      have := h2 r
      have : (tpools E thr0 C θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2)
          NE r 0).card ≤ s0 + D * Lv * S := by exact_mod_cast this
      omega
    · have := h1 r ℓ (by omega)
      have : (tpools E thr0 C θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2)
          NE r ℓ).card ≤ S := by exact_mod_cast this
      omega
  · rw [if_neg hev]
    split_ifs <;> norm_num

end Law

section Final

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {NE Lt : ℕ}

open Classical in
/-- **Expected regret of the threaded K-query pool process, closed form** (schedule `levTh L Bt` of P0085,
coin law `pC ps q`, P0073's pool-size bounds). For any learner `A ω` within `α + β·len` of every present copy
on every interval and within `Bep` of the comparator per unit, on every run:
`E[Σ_{u<NE} (A u - g u)] ≤ (θ+Rα)·NE/B 0 + β NE + ((θ+Rα)ρ + Bep)·(D·Lv·(s0 + D·Lv·S + 1)/(ps (1-q)^{K·D(2L+NE/2^L+1)})
  + D·NE·(NE·D·δs + NE·D·(Lt+1)·K·delta))`. -/
theorem expected_regretT {L : ℕ} (hB : BtHyp D Bt) (hLv2 : L + 2 ≤ Lv) (hLt : L ≤ Lt)
    (hT : Bt 0 ∣ NE) (cu : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (g : ℕ → ℝ) (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < NE → cu u (cstar j a) = g u)
    (A : (SlotC NE D Lt K × ι → Bool) → ℕ → ℝ) (α β Bep : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hθ : 0 ≤ θ)
    (hR1 : 1 ≤ R) (hBep0 : 0 ≤ Bep)
    (hA : ∀ ω f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ,
      f ∈ startPools E thr0 D Lv Bt (ωsC E NE D Lt K ω) u
        (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt (Pool.P0085.levTh L Bt) (ωsC E NE D Lt K ω)
          (φC NE D Lt K ω) u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A ω u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + β * ((s' - s : ℕ) : ℝ))
    (hBep : ∀ ω u, A ω u - g u ≤ Bep) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ∀ j, j + 1 < D → (Bt j : ℝ) ≤ ρ * Bt (j + 1))
    {ps q : ℝ} (hps0 : 0 < ps) (hps1 : ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hEm : Monotone E) (Tmax : ℝ)
    (hC : ∀ i a b, a ≤ b → b ≤ NE → 0 ≤ Lint (Pool.P0061.cumL cu) i a b ∧
      Lint (Pool.P0061.cumL cu) i a b ≤ Tmax)
    (hTm : Tmax ≤ 2 ^ (R - 1) * θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S : ℕ) (hM0S : M0 ≤ S) (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * (S + (s0 + D * Lv * S)) ≤ S) :
    ∑ ω, wtv (pC ps q) ω * ∑ u ∈ Finset.range NE, (A ω u - g u) ≤
      (θ + R * α) * (NE / Bt 0) + β * NE + ((θ + R * α) * ρ + Bep) *
        ((D * Lv * (s0 + D * Lv * S + 1) : ℝ) / (ps * (1 - q) ^ (K * (D * (2 * L + NE / 2 ^ L + 1)))) +
          D * NE * (NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0)) := by
  have hD := hB.hD
  have hLv : 0 < Lv := by omega
  have hlev : ∀ r a, Pool.P0085.levTh L Bt r a + 1 < Lv := fun r a => by
    have := Pool.P0062.levPR_le L ((a + 1) / Bt r - 1)
    unfold Pool.P0085.levTh; omega
  have hp0 : ∀ x : SlotC NE D Lt K × ι, 0 ≤ pC ps q x := fun x => by
    rcases x with ⟨s, c⟩; cases s <;> simp [pC, Pool.P0073.qOfT] <;> linarith
  have hp1 : ∀ x : SlotC NE D Lt K × ι, pC ps q x ≤ 1 := fun x => by
    rcases x with ⟨s, c⟩; cases s <;> simp [pC, Pool.P0073.qOfT] <;> linarith
  set π := ps * (1 - q) ^ (K * (D * (2 * L + NE / 2 ^ L + 1))) with hπdef
  have hπ : 0 < π := mul_pos hps0 (pow_pos (by linarith) _)
  have hπ1 : π ≤ 1 := by
    have : (1 - q) ^ (K * (D * (2 * L + NE / 2 ^ L + 1))) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    calc π ≤ 1 * 1 := mul_le_mul hps1 this (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hpi : ∀ (j : Fin D) (a : Fin NE) (h : Bt j ∣ a),
      π ≤ piS (pC ps q) (oppSet E thr0 D Bt (Pool.P0085.levTh L Bt) NE Lt K (cstar j a)
        (by rw [hE j a (by omega) h a.2]; exact a.2)) oppVal := by
    intro j a h
    have he := hE j a (by omega) h a.2
    have ht := hthr j a (by omega) h a.2
    exact piS_geT hB hps0.le hq0 hq1.le (cstar j a) _ (by rw [he, ht]; exact h) (by rw [ht]; exact j.2)
  have h1 := expected_boundT (θ := θ) hB hLv hlev hT cu cstar hE hthr g hg A α β Bep hα hβ hθ hR1 hBep0
    hA hBep ρ hρ0 hρ (pC ps q) hp0 hp1 π hπ hπ1 hpi (s0 + D * Lv * S + 1)
  have h2 := notGood_le (E := E) (thr0 := thr0) (C := Pool.P0061.cumL cu) (θ := θ) (R := R) (Bt := Bt)
    (K := K) (lev := Pool.P0085.levTh L Bt) (NE := NE) (Lt := Lt) ⟨hps0.le, hps1⟩ hq0 hq1.le hD hLv s0 S
  have hlevLt : ∀ a < NE, ∀ r < D, Pool.P0085.levTh L Bt r a ≤ Lt := fun a _ r _ => by
    have := Pool.P0062.levPR_le L ((a + 1) / Bt r - 1)
    unfold Pool.P0085.levTh; omega
  have h3 := Pool.P0073.prob_tpools_large_le E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt
    (Pool.P0085.levTh L Bt) M0 kk ⟨hps0.le, hps1⟩ hq0 hq1.le hEm hB hLv hlev Tmax hC hR1 hTm hM0 hk hp
    hlevLt s0 δs hs (S : ℝ) hM0S (Nat.cast_nonneg _) hρS
  have hc0 : (0 : ℝ) ≤ θ + R * α := by
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    positivity
  have hW : (0 : ℝ) ≤ (θ + R * α) * ρ + Bep := by positivity
  refine h1.trans ?_
  gcongr
  · push_cast; rfl
  · convert h2.trans h3 using 2

end Final

end Pool.P0091
