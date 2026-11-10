import Pool.P0200.ExtCount
import Pool.P0197.Bridge

/-!
# Expected walk right-hand side with an external-reading rule (P0197's `exp_walkRHS_DZ` for P0200's setting)
-/

namespace Pool.P0207

open Pool.P0200
open Finset Pool.P0156 Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0168 Pool.P0135 Pool.P0186 Pool.P0197

section Walk

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ)
  (ℓr : ℕ → ι → ℝ) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ)
  {Y X : Type} [Fintype Y] (zOf : Y → Fin B → Pool.P0176.RT D sl) (ext : Y → X) (xd : X)
  (rhX : (ℕ → X) → ℕ → ι → (ℕ → ℝ) → Bool) (μ : Y → ℝ)

attribute [local instance] Pool.P0082.coinFintype

open Pool.P0176 Pool.P0082 in
/-- **Expected walk right-hand side of the per-thread process.** Over P0091/P0082's coin array (any weights `p` in
`[0,1]`) and independent rounds (`wU`, summing to `1`), if every level weight is at most `M` then the expectation of
the right-hand side of P0186's `run_bound_mix` (comparator copies `cstar`, mixed outcomes of `dzRun`: entry-order
actual run, forced copy-last runs) is at most `T·a 0 + M·Kb`, for any bound `Kb` on P0185's expected bad count. -/
theorem exp_walkRHS_X {NE Lt : ℕ} (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < D → Bt j ∣ a → a < NE → E (cstar j a) = a) (hD : 0 < D)
    (p : SlotC NE D Lt K × ι → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (a : ℕ → ℝ) (c M Kb : ℝ) (hM0 : 0 ≤ M)
    (hMa : ∀ j, 1 ≤ j → j < D → (Bt (j - 1) : ℝ) * a j ≤ M) (hMc : c ≤ M)
    (hcount : ∑ ω, Pool.P0048.wtv p ω * ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
      (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl (cstar ja.1 ja.2))
          (zE sl B zOf yy)) ∅ (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ) ≤ Kb) :
    ∑ ω, Pool.P0048.wtv p ω * ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
      (NE * a 0 + ∑ j ∈ Finset.Ico 1 D, (Bt (j - 1) : ℝ) *
          (nBadB NE Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (sortLay sl) (zE sl B zOf yy))
            ∅ (fun c' => dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl c') (zE sl B zOf yy)) (fun _ => ∅) (D - 1) NE
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (cstar r τ)) (j - 1) : ℝ) * a j +
        (nBadB NE Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (sortLay sl) (zE sl B zOf yy))
            ∅ (fun c' => dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl c') (zE sl B zOf yy)) (fun _ => ∅) (D - 1) NE
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (cstar r τ)) (D - 1) : ℝ) * c) ≤
      NE * a 0 + M * Kb := by
  classical
  have hw : ∀ ω, 0 ≤ Pool.P0048.wtv p ω := fun ω => Pool.P0048.wtv_nonneg hp0 hp1 ω
  have hwR : ∀ yy : Fin NE → Y, 0 ≤ Pool.P0070.wR μ yy :=
    fun yy => Pool.P0200.wR_nonneg_μ μ hμ0 yy
  have hsw : ∑ ω, Pool.P0048.wtv p ω = 1 := Pool.P0048.sum_wtv p
  have hsR : ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy = 1 :=
    Pool.P0097.sum_wR _ hμ1 NE
  set CNT : (SlotC NE D Lt K × ι → Bool) → (Fin NE → Y) → ℝ := fun ω yy =>
    (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl (cstar ja.1 ja.2))
          (zE sl B zOf yy)) ∅ (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ) with hCNT
  have hpt : ∀ ω yy, (NE * a 0 + ∑ j ∈ Finset.Ico 1 D, (Bt (j - 1) : ℝ) *
          (nBadB NE Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (sortLay sl) (zE sl B zOf yy))
            ∅ (fun c' => dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl c') (zE sl B zOf yy)) (fun _ => ∅) (D - 1) NE
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (cstar r τ)) (j - 1) : ℝ) * a j +
        (nBadB NE Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (sortLay sl) (zE sl B zOf yy))
            ∅ (fun c' => dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl c') (zE sl B zOf yy)) (fun _ => ∅) (D - 1) NE
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (cstar r τ)) (D - 1) : ℝ) * c) ≤ NE * a 0 + M * CNT ω yy := by
    intro ω yy
    refine (walkRHS_le (T := NE) _ a c M hM0 hMa hMc hD).trans ?_
    have hle : ∑ j ∈ Finset.range D, (nBadB NE Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev
        (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (sortLay sl) (zE sl B zOf yy)) ∅
        (fun c' => dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl c') (zE sl B zOf yy)) (fun _ => ∅) (D - 1) NE
        (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (cstar r τ)) j : ℝ) ≤ CNT ω yy := by
      have hsum := sum_card_filter_eq (D := D) NE (fun j a => Bt j ∣ a ∧ ωsC E NE D Lt K ω (cstar j a) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl (cstar j a))
          (zE sl B zOf yy)) ∅ (forceS (ωsC E NE D Lt K ω) (cstar j a)) (forceF K (φC NE D Lt K ω) (cstar j a)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) j a = none)
      refine (Finset.sum_le_sum fun j hj => ?_).trans (le_of_eq (hsum.trans ?_))
      · have := nBadB_le (E := E) (thr0 := thr0) (θ := θ) (R := R) (K := K) (Lv := Lv) (lev := lev)
          (upd := dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (sortLay sl) (zE sl B zOf yy)) (aux0 := ∅)
          (U := fun c' => dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl c') (zE sl B zOf yy)) (A0 := fun _ => ∅)
          (T := NE) (ωs := ωsC E NE D Lt K ω) (φ := φC NE D Lt K ω) cstar hE (Finset.mem_range.1 hj)
        refine Nat.cast_le.mpr (this.trans_eq ?_)
        congr 1; ext a; simp only [Finset.mem_filter]
      · rw [hCNT]
        beta_reduce
        congr 2; ext ja; simp only [Finset.mem_filter]
    have := mul_le_mul_of_nonneg_left hle hM0
    linarith
  calc _ ≤ ∑ ω, Pool.P0048.wtv p ω * ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
        (NE * a 0 + M * CNT ω yy) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hw ω)
        exact Finset.sum_le_sum fun yy _ => mul_le_mul_of_nonneg_left (hpt ω yy) (hwR yy)
    _ = NE * a 0 + M * ∑ ω, Pool.P0048.wtv p ω * ∑ yy : Fin NE → Y,
        Pool.P0070.wR μ yy * CNT ω yy := by
        have hin : ∀ ω, ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
            (NE * a 0 + M * CNT ω yy) = NE * a 0 + M * ∑ yy : Fin NE → Y,
              Pool.P0070.wR μ yy * CNT ω yy := by
          intro ω
          have h : ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy * (NE * a 0 + M * CNT ω yy) =
              (∑ yy : Fin NE → Y, Pool.P0070.wR μ yy) * (NE * a 0) +
                M * ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy * CNT ω yy := by
            rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun yy _ => by ring
          rw [h, hsR, one_mul]
        simp only [hin]
        have h : ∑ ω, Pool.P0048.wtv p ω * (NE * a 0 + M * ∑ yy : Fin NE → Y,
              Pool.P0070.wR μ yy * CNT ω yy) =
            (∑ ω, Pool.P0048.wtv p ω) * (NE * a 0) + M * ∑ ω, Pool.P0048.wtv p ω * ∑ yy : Fin NE → Y,
              Pool.P0070.wR μ yy * CNT ω yy := by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun ω _ => by ring
        rw [h, hsw, one_mul]
    _ ≤ NE * a 0 + M * Kb := by
        have := mul_le_mul_of_nonneg_left hcount hM0
        linarith

end Walk

end Pool.P0207
