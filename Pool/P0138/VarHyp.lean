import Pool.P0089.Hedge
import Pool.P0086.Asm

/-!
# Variance form of the dyadic-specialist learner hypothesis (nonnegative, unbounded losses)

* `hedge_interval_hyp_var`: P0089's dyadic-specialist learner is within
  `(2L+1)(log |Spec| + 2δT)/η + (η/2)·Σ_{[s,s')} V` of every copy on every interval of its presence,
  where `V u` is the learner's own **uncentred second moment** `palgVar u = Σ_j p_u(j)·c_u(j)²` (the
  learner-weighted local norm ⟨p, c²⟩, not a variance; "variance form" follows the naming of P0054's
  `algVar`). Only `0 ≤ cu` is assumed (no upper bound), so this applies to importance-weighted estimates;
  for those, bounds on `E[palgVar]` are local-norm bounds, not variance bounds.
* Scope (as in P0089's `hedge_interval_hyp`): `A u` (P0089's `palgLoss`) and `V u` are the learner's
  loss and second moment only at rounds `u < T` at which some specialist is awake. They are `0` at rounds
  `≥ T` AND at rounds `< T` with no present copy (empty start pools). Downstream sums of `A` must not
  treat these zeros as losses of a learner that plays every round.
* `run_bound_var`, `run_bound_closed_var`: P0086's threaded run bound with a per-round budget `V ≥ 0` in
  place of `β·len`: the total is `(θ+Rα)·(…) + Σ_{u<T} V u + Bep·(…)`. Proof: apply P0086 to `A - V`
  with `β = 0`.
-/

open Real Finset

namespace Pool.P0138

open Pool.P0019 Pool.P0054 Pool.P0089

variable {ι₀ : Type*} [Fintype ι₀] {L : ℕ}

lemma palgVar_nonneg {ι : Type*} [Fintype ι] {q : ι → ℝ} (hq : ∀ i, 0 < q i) (η : ℝ) (aw : ℕ → ι → Bool)
    (c : ℕ → ι → ℝ) (ρ : ℕ → ℝ) (t : ℕ) : 0 ≤ palgVar q η aw c ρ t := by
  unfold palgVar
  exact Finset.sum_nonneg fun j _ => mul_nonneg (pprob_nonneg hq t j) (sq_nonneg _)

/-- **Second-moment ("variance") form of P0089's `hedge_interval_hyp`**: for nonnegative (possibly
unbounded) losses. `A u` and `V u` are `palgLoss`/`palgVar` at rounds `u < T` and `0` at rounds `≥ T`;
like P0089's, `A u = V u = 0` also at rounds `< T` with no awake specialist (no present copy), so these
zeros are not losses of a learner that plays every round. -/
theorem hedge_interval_hyp_var (present : ℕ → ι₀ → Prop) (cu : ℕ → ι₀ → ℝ) (hc0 : ∀ t f, 0 ≤ cu t f)
    {η : ℝ} (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) (ρ : ℕ → ℝ) (hρ : ∀ t, |ρ t| ≤ δ)
    (T : ℕ) (hTL : T ≤ 2 ^ L) [Nonempty (Spec ι₀ L)] (f : ι₀) (s s' : ℕ) (hss' : s ≤ s')
    (hpres : ∀ u, s ≤ u → u < s' → present u f) :
    let A : ℕ → ℝ := fun u => if u < T then
      palgLoss (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ u else 0
    let V : ℕ → ℝ := fun u => if u < T then
      palgVar (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ u else 0
    ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f +
      (2 * L + 1) * (Real.log (Fintype.card (Spec ι₀ L)) + 2 * δ * T) / η +
        η / 2 * ∑ u ∈ Finset.Ico s s', V u := by
  intro A V
  classical
  have hV0 : ∀ u, 0 ≤ V u := fun u => by
    simp only [V]; split_ifs
    · exact palgVar_nonneg (fun _ => one_pos) _ _ _ _ _
    · exact le_rfl
  have hK0 : (0 : ℝ) ≤ (2 * L + 1) * (Real.log (Fintype.card (Spec ι₀ L)) + 2 * δ * T) / η := by
    have : (0 : ℝ) ≤ Real.log (Fintype.card (Spec ι₀ L)) :=
      Real.log_nonneg (show (1 : ℝ) ≤ Fintype.card (Spec ι₀ L) by exact_mod_cast Fintype.card_pos)
    positivity
  have hη2 : 0 ≤ η / 2 := by positivity
  set v := min s' T with hv
  have hvs : v ≤ s' := min_le_left _ _
  have hvT : v ≤ T := min_le_right _ _
  have hcS : ∀ t (j : Spec ι₀ L), 0 ≤ specLoss (L := L) cu t j := fun t j => hc0 t j.1
  have hcf : ∀ w, w ≤ s' → ∑ u ∈ Finset.Ico s w, cu u f ≤ ∑ u ∈ Finset.Ico s s', cu u f := fun w hw =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hw) fun u _ _ => hc0 u f
  have hVsum : ∀ w, w ≤ s' → ∑ u ∈ Finset.Ico s w, V u ≤ ∑ u ∈ Finset.Ico s s', V u := fun w hw =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hw) fun u _ _ => hV0 u
  by_cases hsv : s ≤ v
  · have hsplit : ∑ u ∈ Finset.Ico s s', A u = ∑ u ∈ Finset.Ico s v, A u := by
      rw [← Finset.sum_Ico_consecutive _ hsv hvs]
      have : ∑ u ∈ Finset.Ico v s', A u = 0 := Finset.sum_eq_zero fun u hu => by
        rw [Finset.mem_Ico] at hu
        have : ¬ u < T := by
          intro h; have : u < v := by rw [hv]; exact lt_min hu.2 h
          omega
        simp [A, this]
      rw [this, add_zero]
    rw [hsplit]
    have hAv : ∑ u ∈ Finset.Ico s v, A u =
        ∑ u ∈ Finset.Ico s v, palgLoss (fun _ => (1 : ℝ)) η (specAw (L := L) present)
          (specLoss (L := L) cu) ρ u :=
      Finset.sum_congr rfl fun u hu => by
        rw [Finset.mem_Ico] at hu
        simp [A, show u < T by omega]
    have hVv : ∑ u ∈ Finset.Ico s v, V u =
        ∑ u ∈ Finset.Ico s v, palgVar (fun _ => (1 : ℝ)) η (specAw (L := L) present)
          (specLoss (L := L) cu) ρ u :=
      Finset.sum_congr rfl fun u hu => by
        rw [Finset.mem_Ico] at hu
        simp [V, show u < T by omega]
    rw [hAv]
    let spec : ℕ × ℕ → Spec ι₀ L := fun p =>
      (f, (⟨min p.2 L, by omega⟩, ⟨p.1 % 2 ^ L, Nat.mod_lt _ (Nat.two_pow_pos L)⟩))
    have hvL : v ≤ 2 ^ L := hvT.trans hTL
    have hpiece : ∀ p ∈ dec L s v, p.2 ≤ L ∧ p.1 < 2 ^ L := by
      intro p hp
      obtain ⟨-, h1, h2⟩ := dec_dy L s v hvL p hp
      have : 2 ^ p.2 ≤ 2 ^ L := by
        have := Nat.one_le_two_pow (n := p.2)
        omega
      refine ⟨(Nat.pow_le_pow_iff_right (by norm_num)).1 this, ?_⟩
      have := Nat.one_le_two_pow (n := p.2); omega
    have hreg := pert_regret_interval_le (q := fun _ => (1 : ℝ)) (aw := specAw (L := L) present)
      (c := specLoss (L := L) cu) (ρ := ρ) (fun _ => one_pos) hη hcS hδ hρ T L s v hsv hvL hvT spec
      (fun t => cu t f)
      (by
        intro p hp t ht
        obtain ⟨hpL, hpa⟩ := hpiece p hp
        obtain ⟨hdy, h1, h2⟩ := dec_dy L s v hvL p hp
        simp only [specAw, spec, decide_eq_true_eq, Nat.mod_eq_of_lt hpa, min_eq_left hpL]
        constructor
        · rintro ⟨-, a1, a2, -⟩; exact ⟨a1, a2⟩
        · rintro ⟨a1, a2⟩; exact ⟨hdy, a1, a2, hpres t (by omega) (by omega)⟩)
      (fun p _ t _ _ => rfl)
      (Real.log_nonneg (show (1 : ℝ) ≤ Fintype.card (Spec ι₀ L) by exact_mod_cast Fintype.card_pos))
      (fun p _ => by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, div_one]
        exact le_rfl)
    rw [Finset.sum_sub_distrib, ← hVv] at hreg
    have h1 := hcf v hvs
    have h2 := hVsum v hvs
    have h3 : η / 2 * ∑ u ∈ Finset.Ico s v, V u ≤ η / 2 * ∑ u ∈ Finset.Ico s s', V u :=
      mul_le_mul_of_nonneg_left h2 hη2
    linarith
  · push Not at hsv
    have : ∑ u ∈ Finset.Ico s s', A u = 0 := Finset.sum_eq_zero fun u hu => by
      rw [Finset.mem_Ico] at hu
      have : ¬ u < T := by
        intro h; have : u < v := by rw [hv]; exact lt_min hu.2 h
        omega
      simp [A, this]
    rw [this]
    have h1 : 0 ≤ ∑ u ∈ Finset.Ico s s', cu u f := Finset.sum_nonneg fun u _ => hc0 u f
    have h2 : 0 ≤ η / 2 * ∑ u ∈ Finset.Ico s s', V u :=
      mul_nonneg hη2 (Finset.sum_nonneg fun u _ => hV0 u)
    linarith


section RunVar

open Pool.P0065 Pool.P0074 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0086

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}

/-- **P0086's per-run bound with a per-round budget** `V ≥ 0` in place of `β·len`. -/
theorem run_bound_var (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (cu : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (g : ℕ → ℝ) (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < T → cu u (cstar j a) = g u)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (A V : ℕ → ℝ) (α Bep : ℝ) (hα : 0 ≤ α) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R) (hV : ∀ u, 0 ≤ V u)
    (hA : ∀ f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + ∑ u ∈ Finset.Ico s s', V u)
    (hBep : ∀ u, A u - g u ≤ Bep) :
    let W := Pool.P0057.theWalk D T Bt (evW E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev T cstar ωs φ)
    ∑ u ∈ Finset.range T, (A u - g u) ≤ (θ + R * α) * W.length + ∑ u ∈ Finset.range T, V u +
      Bep * (((W.filter fun x => !x.cov).map Pool.P0057.len).sum : ℕ) := by
  intro W
  have h := run_bound (θ := θ) hB hLv hlev hT cu cstar hE hthr g hg ωs φ (fun u => A u - V u) α 0 Bep
    hα le_rfl hθ hR1
    (fun f s s' hss hp => by
      have := hA f s s' hss hp
      rw [Finset.sum_sub_distrib]; simp only [zero_mul, add_zero]; linarith)
    (fun u => by linarith [hBep u, hV u])
  simp only [zero_mul, add_zero] at h
  have hs : ∑ u ∈ Finset.range T, (A u - V u - g u) =
      ∑ u ∈ Finset.range T, (A u - g u) - ∑ u ∈ Finset.range T, V u := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun u _ => by ring
  rw [hs] at h
  linarith

/-- **P0086's closed-form per-run bound with a per-round budget** `V ≥ 0`. -/
theorem run_bound_closed_var (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ}
    (hT : Bt 0 ∣ T) (cu : ℕ → ι → ℝ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (g : ℕ → ℝ) (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < T → cu u (cstar j a) = g u)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (A V : ℕ → ℝ) (α Bep : ℝ) (hα : 0 ≤ α) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R) (hBep0 : 0 ≤ Bep)
    (hV : ∀ u, 0 ≤ V u)
    (hA : ∀ f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cu u f + α + ∑ u ∈ Finset.Ico s s', V u)
    (hBep : ∀ u, A u - g u ≤ Bep) :
    let H := Pool.P0057.nBad T Bt (evW E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev T cstar ωs φ)
    ∑ u ∈ Finset.range T, (A u - g u) ≤
      (θ + R * α) * (T / Bt 0 + ∑ j ∈ Finset.range (D - 1), (Bt j : ℝ) * H j / Bt (j + 1)) +
        ∑ u ∈ Finset.range T, V u + Bep * (Bt (D - 1) * H (D - 1) : ℕ) := by
  intro H
  have h := run_bound_closed (θ := θ) hB hLv hlev hT cu cstar hE hthr g hg ωs φ (fun u => A u - V u) α 0 Bep
    hα le_rfl hθ hR1 hBep0
    (fun f s s' hss hp => by
      have := hA f s s' hss hp
      rw [Finset.sum_sub_distrib]; simp only [zero_mul, add_zero]; linarith)
    (fun u => by linarith [hBep u, hV u])
  simp only [zero_mul, add_zero] at h
  have hs : ∑ u ∈ Finset.range T, (A u - V u - g u) =
      ∑ u ∈ Finset.range T, (A u - g u) - ∑ u ∈ Finset.range T, V u := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun u _ => by ring
  rw [hs] at h
  linarith

/-- **Per-run bound for P0089's learner, nonnegative unbounded data.** P0089's dyadic-specialist learner run
over P0065's threaded pools (present = in a start pool), with covers on the same nonnegative per-round data
`cu` (e.g. importance-weighted estimates), satisfies P0086's closed-form per-run bound with the
second-moment budget `(η/2)·palgVar` in place of `β·T`. Scope: `A u` is P0089's `palgLoss`, which is `0`
at rounds with no present copy and at rounds `≥ T`; so `Σ_{u<T}(A u − g u)` is the learner's loss minus
the comparator's only on rounds where some copy is present, not the regret of an algorithm that plays
every round (the empty-pool rounds must be handled downstream, as P0089 warns). -/
theorem run_bound_closed_hedge [Nonempty ι] (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    {T L : ℕ} (hTL : T ≤ 2 ^ L)
    (hT : Bt 0 ∣ T) (cu : ℕ → ι → ℝ) (hc0 : ∀ t f, 0 ≤ cu t f) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (g : ℕ → ℝ) (hg : ∀ j a u, j ≤ D - 1 → Bt j ∣ a → a < T → cu u (cstar j a) = g u)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    {η : ℝ} (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) (ρ : ℕ → ℝ) (hρ : ∀ t, |ρ t| ≤ δ)
    (hθ : 0 ≤ θ) (hR1 : 1 ≤ R) (Bep : ℝ) (hBep0 : 0 ≤ Bep) :
    let present : ℕ → ι → Prop := fun u f => ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev ωs φ u) r ℓ
    let A : ℕ → ℝ := fun u => if u < T then
      palgLoss (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ u else 0
    let Vr : ℕ → ℝ := fun u => if u < T then
      palgVar (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) cu) ρ u else 0
    let α : ℝ := (2 * L + 1) * (Real.log (Fintype.card (Spec ι L)) + 2 * δ * T) / η
    let H := Pool.P0057.nBad T Bt (evW E thr0 (Pool.P0061.cumL cu) θ R K D Lv Bt lev T cstar ωs φ)
    (∀ u, A u - g u ≤ Bep) →
    ∑ u ∈ Finset.range T, (A u - g u) ≤
      (θ + R * α) * (T / Bt 0 + ∑ j ∈ Finset.range (D - 1), (Bt j : ℝ) * H j / Bt (j + 1)) +
        η / 2 * ∑ u ∈ Finset.range T, Vr u + Bep * (Bt (D - 1) * H (D - 1) : ℕ) := by
  intro present A Vr α H hBep
  have hα : 0 ≤ α := by
    have : (0 : ℝ) ≤ Real.log (Fintype.card (Spec ι L)) :=
      Real.log_nonneg (show (1 : ℝ) ≤ Fintype.card (Spec ι L) by exact_mod_cast Fintype.card_pos)
    positivity
  have hV0 : ∀ u, 0 ≤ η / 2 * Vr u := fun u => by
    have : 0 ≤ Vr u := by
      simp only [Vr]; split_ifs
      · exact palgVar_nonneg (fun _ => one_pos) _ _ _ _ _
      · exact le_rfl
    positivity
  have h := run_bound_closed_var (θ := θ) hB hLv hlev hT cu cstar hE hthr g hg ωs φ A (fun u => η / 2 * Vr u)
    α Bep hα hθ hR1 hBep0 hV0
    (fun f s s' hss hp => by
      have := hedge_interval_hyp_var (L := L) present cu hc0 hη hδ ρ hρ T hTL f s s' hss hp
      rw [← Finset.mul_sum]; exact this)
    hBep
  rw [← Finset.mul_sum] at h
  exact h

end RunVar

end Pool.P0138
