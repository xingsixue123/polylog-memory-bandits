import Pool.P0207.Assemble

/-!
# Per-level split of the walk right-hand side 

P0186's `run_bound_mix` ends with `NE·a₀ + Σ_{1≤j<D} Bt_{j−1}·nBad_{j−1}·a_j + nBad_{D−1}·c`. P0197/P0207 bound
its expectation by `NE·a₀ + M·Kb` with ONE weight `M ≥ Bt_{j−1}·a_j` for every level. Here coarse levels (any
predicate `cz`) are instead bounded pathwise with `Bt_{j−1}·nBad_{j−1} ≤ NE + Bt_{j−1}` (at most one bad point per
level-`(j−1)` epoch start below `NE`), and only the other levels need `Bt_{j−1}·a_j ≤ M`.
-/

namespace Pool.P0259

open Finset

/-- The right-hand side of P0186's `run_bound_mix`, as a function of the per-level bad counts `nb`. -/
noncomputable def walkRHS (NE D : ℕ) (Bt : ℕ → ℕ) (nb : ℕ → ℕ) (a : ℕ → ℝ) (c : ℝ) : ℝ :=
  NE * a 0 + ∑ j ∈ Ico 1 D, (Bt (j - 1) : ℝ) * (nb (j - 1) : ℝ) * a j + (nb (D - 1) : ℝ) * c

/-- Multiples of `b > 0` below `N`: at most `N / b + 1`. -/
theorem card_dvd_range_le (N b : ℕ) (hb : 0 < b) :
    ((range N).filter fun s => b ∣ s).card ≤ N / b + 1 := by
  have hsub : (range N).filter (fun s => b ∣ s) ⊆ (range (N / b + 1)).image fun k => b * k := by
    intro s hs
    rw [mem_filter, mem_range] at hs
    obtain ⟨hsN, k, rfl⟩ := hs
    refine mem_image.2 ⟨k, mem_range.2 ?_, rfl⟩
    have : k ≤ N / b := (Nat.le_div_iff_mul_le hb).2 (by rw [mul_comm]; omega)
    omega
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

/-- **Pathwise level cap**: the level-`j` bad epoch starts below `NE` are at most the level-`j` epoch starts, so
`Bt_j · nBadB_j ≤ NE + Bt_j`. -/
theorem nBadB_mul_le (NE : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Pool.P0135.Out) (j : ℕ) (hb : 0 < B j) :
    (B j : ℝ) * (Pool.P0135.nBadB NE B t j : ℝ) ≤ NE + B j := by
  have h1 : Pool.P0135.nBadB NE B t j ≤ NE / B j + 1 := by
    unfold Pool.P0135.nBadB
    refine le_trans (card_le_card ?_) (card_dvd_range_le NE (B j) hb)
    intro s hs
    rw [mem_filter] at hs ⊢
    exact ⟨hs.1, hs.2.1⟩
  have h2 : B j * (Pool.P0135.nBadB NE B t j) ≤ NE + B j := by
    calc B j * Pool.P0135.nBadB NE B t j ≤ B j * (NE / B j + 1) := Nat.mul_le_mul_left _ h1
      _ = B j * (NE / B j) + B j := by ring
      _ ≤ NE + B j := by
          have := Nat.mul_div_le NE (B j)
          omega
  exact_mod_cast h2

/-- The weights with every coarse level `j ≥ 1` set to `0` (level `0` is kept). -/
noncomputable def aFine (cz : ℕ → Prop) [DecidablePred cz] (a : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if j ≠ 0 ∧ cz j then 0 else a j

theorem aFine_zero (cz : ℕ → Prop) [DecidablePred cz] (a : ℕ → ℝ) : aFine cz a 0 = a 0 := by
  simp [aFine]

theorem aFine_nonneg (cz : ℕ → Prop) [DecidablePred cz] (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (j : ℕ) :
    0 ≤ aFine cz a j := by
  unfold aFine; split_ifs <;> simp [ha j]

/-- The coarse part, bounded pathwise: `Σ_{1≤j<D, cz j} (NE + Bt_{j−1})·a_j`. -/
noncomputable def coarseSum (NE D : ℕ) (Bt : ℕ → ℕ) (cz : ℕ → Prop) [DecidablePred cz] (a : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Ico 1 D, if cz j then ((NE : ℝ) + Bt (j - 1)) * a j else 0

/-- **Pathwise split.** With nonnegative weights and the level cap at coarse levels, the right-hand side is at most
the same right-hand side with the coarse weights removed, plus `coarseSum`. -/
theorem walkRHS_split (NE D : ℕ) (Bt : ℕ → ℕ) (nb : ℕ → ℕ) (a : ℕ → ℝ) (c : ℝ)
    (cz : ℕ → Prop) [DecidablePred cz] (ha : ∀ j, 0 ≤ a j)
    (hcap : ∀ j ∈ Ico 1 D, cz j → (Bt (j - 1) : ℝ) * (nb (j - 1) : ℝ) ≤ NE + Bt (j - 1)) :
    walkRHS NE D Bt nb a c ≤ walkRHS NE D Bt nb (aFine cz a) c + coarseSum NE D Bt cz a := by
  unfold walkRHS coarseSum
  rw [aFine_zero]
  have hsum : ∑ j ∈ Ico 1 D, (Bt (j - 1) : ℝ) * (nb (j - 1) : ℝ) * a j ≤
      ∑ j ∈ Ico 1 D, (Bt (j - 1) : ℝ) * (nb (j - 1) : ℝ) * aFine cz a j +
        ∑ j ∈ Ico 1 D, if cz j then ((NE : ℝ) + Bt (j - 1)) * a j else 0 := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun j hj => ?_
    have hj0 : j ≠ 0 := by rw [mem_Ico] at hj; omega
    by_cases h : cz j
    · simp only [aFine, hj0, h, ne_eq, not_false_eq_true, and_self, if_true, mul_zero, zero_add]
      exact mul_le_mul_of_nonneg_right (hcap j hj h) (ha j)
    · simp [aFine, h]
  linarith

/-- The per-level bad counts of P0207's integrand (mixed outcomes of the entry-order run and the forced copy-last
runs, P0194's rule of the coin prefix `yy`, schedule `levTh Ld P.Bt`). -/
noncomputable def nbR {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : Pool.P0194.ParD n ι)
    (ℓ : Pool.P0001.LossSeq n) (Ld NE Lt : ℕ) (cstar : ℕ → ℕ → ι)
    (ω : Pool.P0082.SlotC NE P.D Lt P.K × ι → Bool) (yy : Fin NE → Pool.P0194.RC P) : ℕ → ℕ :=
  fun j => Pool.P0135.nBadB NE P.Bt (fun τ r => Pool.P0186.outMix P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt
    (Pool.P0085.levTh Ld P.Bt)
    (Pool.P0176.dzUpd P.D P.Lv P.sl 1 1 P.xr (Pool.P0194.ℓr P ℓ)
      (Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none yy)) (Pool.P0176.sortLay P.sl)
      (Pool.P0200.zE P.sl 1 (Pool.P0207.zOfR P) yy)) ∅
    (fun c' => Pool.P0176.dzUpd P.D P.Lv P.sl 1 1 P.xr (Pool.P0194.ℓr P ℓ)
      (Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none yy)) (Pool.P0176.lastLay P.sl c')
      (Pool.P0200.zE P.sl 1 (Pool.P0207.zOfR P) yy)) (fun _ => ∅) (P.D - 1) NE
    (Pool.P0082.ωsC P.E NE P.D Lt P.K ω) (Pool.P0082.φC NE P.D Lt P.K ω) (cstar r τ)) j


section Round

open Pool.P0200 Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0082 Pool.P0048 Pool.P0065 Pool.P0156
  Pool.P0186 Pool.P0207

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)

attribute [local instance] Pool.P0082.coinFintype

/-- `walkRHS` with `nbR` is P0207's integrand (the right-hand side of P0186's `run_bound_mix` for these runs). -/
theorem walkRHS_nbR_eq (Ld NE Lt : ℕ) (cstar : ℕ → ℕ → ι) (ω : SlotC NE P.D Lt P.K × ι → Bool)
    (yy : Fin NE → RC P) (a : ℕ → ℝ) (c : ℝ) :
    walkRHS NE P.D P.Bt (nbR P ℓ Ld NE Lt cstar ω yy) a c =
      NE * a 0 + ∑ j ∈ Finset.Ico 1 P.D, (P.Bt (j - 1) : ℝ) *
          (Pool.P0135.nBadB NE P.Bt (fun τ r => outMix P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt
            (Pool.P0085.levTh Ld P.Bt)
            (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (sortLay P.sl)
              (zE P.sl 1 (zOfR P) yy)) ∅
            (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (lastLay P.sl c')
              (zE P.sl 1 (zOfR P) yy)) (fun _ => ∅) (P.D - 1) NE
            (ωsC P.E NE P.D Lt P.K ω) (φC NE P.D Lt P.K ω) (cstar r τ)) (j - 1) : ℝ) * a j +
        (Pool.P0135.nBadB NE P.Bt (fun τ r => outMix P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt
            (Pool.P0085.levTh Ld P.Bt)
            (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (sortLay P.sl)
              (zE P.sl 1 (zOfR P) yy)) ∅
            (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (lastLay P.sl c')
              (zE P.sl 1 (zOfR P) yy)) (fun _ => ∅) (P.D - 1) NE
            (ωsC P.E NE P.D Lt P.K ω) (φC NE P.D Lt P.K ω) (cstar r τ)) (P.D - 1) : ℝ) * c := rfl

open Classical in
/-- **Expected walk right-hand side with a per-level split** (P0207's `exp_walkRHS_round`, sharpened). Same
hypotheses as P0207 except that the level weight bound `Bt_{j−1}·a_j ≤ M` is required only at the levels `j` with
`¬ cz j` ("fine" levels); every "coarse" level `j` (`cz j`) is charged pathwise `(NE + Bt_{j−1})·a_j` instead
(`coarseSum`), since it has at most one bad point per level-`(j−1)` epoch start below `NE` (`nBadB_mul_le`). With
`cz := fun _ => False` this is P0207's bound. -/
theorem exp_walkRHS_split (hL : P.IsLaw) (hN : 0 < P.N) (hB : BtHyp P.D P.Bt) {Ld NE Lt : ℕ}
    (hLv2 : Ld + 2 ≤ P.Lv) (hLt : Ld ≤ Lt)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < P.D → P.Bt j ∣ a → a < NE → P.E (cstar j a) = a)
    (hthr : ∀ j a, j < P.D → P.Bt j ∣ a → a < NE → P.thr0 (cstar j a) = j)
    {ps q : ℝ} (hps0 : 0 < ps) (hps1 : ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hEm : Monotone P.E) {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ P.xr j) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hR : 1 ≤ P.R) (hT : 1 / xmin * NE ≤ 2 ^ (P.R - 1) * P.θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * P.R ≤ M0)
    (hk : 4 * P.R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * P.R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < P.D →
      ∑ F ∈ (Finset.univ.filter fun c => P.E c = a ∧ P.thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => P.E c = a ∧ P.thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S') (hρS : (1 - 1 / (4 * P.R : ℝ)) ^ P.K * ((S' : ℝ) + (s0 + P.D * P.Lv * S')) ≤ S')
    (hsl : ∀ j, (P.D : ℝ) * ((s0 + P.D * P.Lv * S') + (P.Lv - 1 : ℕ) * S') + P.D * s0 + 1 ≤ P.sl j)
    (a : ℕ → ℝ) (c M : ℝ) (hM0' : 0 ≤ M) (cz : ℕ → Prop) [DecidablePred cz] (ha : ∀ j, 0 ≤ a j)
    (hMa : ∀ j, 1 ≤ j → j < P.D → ¬ cz j → (P.Bt (j - 1) : ℝ) * a j ≤ M) (hMc : c ≤ M) :
    ∑ ω, wtv (Pool.P0091.pC (NE := NE) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω *
      ∑ yy : Fin NE → RC P, Pool.P0070.wR (wR P) yy * walkRHS NE P.D P.Bt (nbR P ℓ Ld NE Lt cstar ω yy) a c ≤
      NE * a 0 + coarseSum NE P.D P.Bt cz a + M * ((P.D * P.Lv * (s0 + P.D * P.Lv * S' + 1) : ℝ) /
          (ps * (1 - q) ^ (P.K * (P.D * (2 * Ld + NE / 2 ^ Ld + 1)))) +
        P.D * NE * (NE * P.D * δs + NE * P.D * (Lt + 1) * P.K * Pool.P0042.delta (Fintype.card ι) q P.R kk M0)) := by
  set K := coarseSum NE P.D P.Bt cz a
  have hp0 : ∀ x : SlotC NE P.D Lt P.K × ι, 0 ≤ Pool.P0091.pC ps q x := fun x => by
    rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith
  have hp1 : ∀ x : SlotC NE P.D Lt P.K × ι, Pool.P0091.pC ps q x ≤ 1 := fun x => by
    rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith
  have hw : ∀ ω, 0 ≤ wtv (Pool.P0091.pC (NE := NE) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω :=
    wtv_nonneg hp0 hp1
  have hr : ∀ yy : Fin NE → RC P, 0 ≤ Pool.P0070.wR (wR P) yy :=
    fun yy => Pool.P0200.wR_nonneg_μ (wR P) (wR_nonneg P hL) yy
  have hr1 : ∑ yy : Fin NE → RC P, Pool.P0070.wR (wR P) yy = 1 := Pool.P0097.sum_wR _ (sum_wR P hL hN) NE
  have hw1 : ∑ ω : SlotC NE P.D Lt P.K × ι → Bool, wtv (Pool.P0091.pC (NE := NE) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω = 1 := sum_wtv _
  -- pathwise split
  have hpath : ∀ ω yy, walkRHS NE P.D P.Bt (nbR P ℓ Ld NE Lt cstar ω yy) a c ≤
      walkRHS NE P.D P.Bt (nbR P ℓ Ld NE Lt cstar ω yy) (aFine cz a) c + K := fun ω yy =>
    walkRHS_split NE P.D P.Bt _ a c cz ha fun j _ _ => nBadB_mul_le NE P.Bt _ (j - 1) (hB.pos _)
  -- P0207 with the coarse weights removed
  have hfine := exp_walkRHS_round P ℓ hL hN hB hLv2 hLt cstar hE hthr hps0 hps1 hq0 hq1 hEm hxmin hx hBm hR hT M0
    kk hM0 hk hp s0 δs hs S' hM0S hρS hsl (aFine cz a) c M hM0' (fun j hj1 hjD => by
      by_cases h : cz j
      · have hj0 : j ≠ 0 := by omega
        simp only [aFine, hj0, h, ne_eq, not_false_eq_true, and_self, ite_true, mul_zero]
        exact hM0'
      · have : aFine cz a j = a j := by simp [aFine, h]
        rw [this]; exact hMa j hj1 hjD h) hMc
  rw [aFine_zero] at hfine
  calc ∑ ω, wtv (Pool.P0091.pC (NE := NE) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω *
        ∑ yy : Fin NE → RC P, Pool.P0070.wR (wR P) yy * walkRHS NE P.D P.Bt (nbR P ℓ Ld NE Lt cstar ω yy) a c
      ≤ ∑ ω, wtv (Pool.P0091.pC (NE := NE) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω *
        ∑ yy : Fin NE → RC P, Pool.P0070.wR (wR P) yy *
          (walkRHS NE P.D P.Bt (nbR P ℓ Ld NE Lt cstar ω yy) (aFine cz a) c + K) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hw ω)
        exact Finset.sum_le_sum fun yy _ => mul_le_mul_of_nonneg_left (hpath ω yy) (hr yy)
    _ = (∑ ω, wtv (Pool.P0091.pC (NE := NE) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω *
        ∑ yy : Fin NE → RC P, Pool.P0070.wR (wR P) yy *
          walkRHS NE P.D P.Bt (nbR P ℓ Ld NE Lt cstar ω yy) (aFine cz a) c) + K := by
        have hin : ∀ ω, ∑ yy : Fin NE → RC P, Pool.P0070.wR (wR P) yy *
            (walkRHS NE P.D P.Bt (nbR P ℓ Ld NE Lt cstar ω yy) (aFine cz a) c + K) =
            (∑ yy : Fin NE → RC P, Pool.P0070.wR (wR P) yy *
              walkRHS NE P.D P.Bt (nbR P ℓ Ld NE Lt cstar ω yy) (aFine cz a) c) + K := by
          intro ω
          rw [Finset.sum_congr rfl (fun yy _ => mul_add _ _ _), Finset.sum_add_distrib, ← Finset.sum_mul, hr1,
            one_mul]
        rw [Finset.sum_congr rfl (fun ω _ => by rw [hin ω, mul_add]), Finset.sum_add_distrib, ← Finset.sum_mul,
          hw1, one_mul]
    _ ≤ _ := by
        have h2 : (∑ ω, wtv (Pool.P0091.pC (NE := NE) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω *
            ∑ yy : Fin NE → RC P, Pool.P0070.wR (wR P) yy *
              walkRHS NE P.D P.Bt (nbR P ℓ Ld NE Lt cstar ω yy) (aFine cz a) c) ≤
            NE * a 0 + M * ((P.D * P.Lv * (s0 + P.D * P.Lv * S' + 1) : ℝ) /
              (ps * (1 - q) ^ (P.K * (P.D * (2 * Ld + NE / 2 ^ Ld + 1)))) +
            P.D * NE * (NE * P.D * δs + NE * P.D * (Lt + 1) * P.K *
              Pool.P0042.delta (Fintype.card ι) q P.R kk M0)) := hfine
        linarith

end Round

end Pool.P0259
