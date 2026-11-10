import Pool.P0200.ExtLaw

/-!
# Bad walk points of `dzRun` when the retirement rule reads external coin information

P0185's count (`count_bad_DZ`, `count_bad_DZ_closed`) for unit coins `y : Y` with weight `μ`, slot part `zOf y` and a
causal rule family `rhX` reading the external parts `ext y` (P0200's `law_sort_last_X`). The pathwise lemmas of P0185
(`bad_leD`, `card_surv_leD`, `card_bad_leD`, `GoodAD`, `prob_notGoodAD_le`) are used at the rule `rhX (extE ω)` of
each coin sequence.
-/

namespace Pool.P0200

open Finset Pool.P0095 Pool.P0065 Pool.P0081 Pool.P0082 Pool.P0052 Pool.P0048 Pool.P0105 Pool.P0156 Pool.P0164
  Pool.P0176 Pool.P0185

section Count

attribute [local instance] coinFintype

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ) (ℓr : ℕ → ι → ℝ)
  {Y X : Type} [Fintype Y] (zOf : Y → Fin B → RT D sl) (ext : Y → X) (xd : X)
  (rhX : (ℕ → X) → ℕ → ι → (ℕ → ℝ) → Bool) (μ : Y → ℝ) {NE Lt : ℕ}

open Classical in
/-- The coin probability that, in the entry-order run on sampling/filter coins `ω`, no thread overflows before `NE`
and the copy `c` survives (with small pools); the rule is read at each unit-coin sequence's external history. -/
noncomputable def fSurvX (S : ℕ) (c : ι) (ω : SlotC NE D Lt K × ι → Bool) : ℝ :=
  ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
    (if NoOverflowD Lv sl E thr0 Bt (ωsC E NE D Lt K ω) NE
          (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
            (sortLay sl) NE (zE sl B zOf yy)) ∧
        SurvD D Lv NE S c
          (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
            (sortLay sl) NE (zE sl B zOf yy))
      then 1 else 0)

omit [LinearOrder ι] [Fintype ι] in
theorem wR_nonneg_μ (hμ0 : ∀ y, 0 ≤ μ y) {T : ℕ} (yy : Fin T → Y) : 0 ≤ Pool.P0070.wR μ yy :=
  Finset.prod_nonneg fun _ _ => hμ0 _

theorem fSurv_nonnegX (hμ0 : ∀ y, 0 ≤ μ y) (S : ℕ) (c : ι) (ω : SlotC NE D Lt K × ι → Bool) :
    0 ≤ fSurvX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ S c ω :=
  Finset.sum_nonneg fun yy _ => mul_nonneg (wR_nonneg_μ μ hμ0 yy) (by split_ifs <;> norm_num)

open Classical in
/-- **Per-opportunity law step** with an external-reading rule (P0185's `forced_lawD`). -/
theorem forced_lawX (hc : Causal rhX) (A : PermAct sl B zOf ext μ) (S : ℕ) (c : ι) (hcE : E c < NE)
    (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
      (if NoOverflowD Lv sl E thr0 Bt (forceS (ωsC E NE D Lt K ω) c) NE
            (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (forceS (ωsC E NE D Lt K ω) c)
              (forceF K (φC NE D Lt K ω) c) (lastLay sl c) NE (zE sl B zOf yy)) ∧
          SurvD D Lv NE S c (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev
            (forceS (ωsC E NE D Lt K ω) c) (forceF K (φC NE D Lt K ω) c) (lastLay sl c) NE (zE sl B zOf yy))
        then 1 else 0) =
      fSurvX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ S c
        (force (oppSet E thr0 D Bt lev NE Lt K c hcE) oppVal ω) := by
  set ω' := force (oppSet E thr0 D Bt lev NE Lt K c hcE) oppVal ω
  have htr : ∀ yy : Fin NE → Y,
      trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (forceS (ωsC E NE D Lt K ω) c)
        (forceF K (φC NE D Lt K ω) c) (lastLay sl c) NE (zE sl B zOf yy) =
      trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (ωsC E NE D Lt K ω') (φC NE D Lt K ω')
        (lastLay sl c) NE (zE sl B zOf yy) := by
    intro yy; funext a
    simp only [trajD]
    exact (gRun_force_eq E thr0 θ R K D Lv Bt lev
      (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl c) (zE sl B zOf yy)) ∅ c hcE ω _).symm
  have hs := Pool.P0119.ωsC_force E thr0 K D Bt lev c hcE ω
  simp only [htr]
  rw [← hs]
  unfold fSurvX
  exact (law_sort_last_X Lv sl B Bm xr ℓr E thr0 θ R K Bt lev (ωsC E NE D Lt K ω') (φC NE D Lt K ω') zOf ext xd rhX μ
    hc A c NE (SurvD D Lv NE S c)).symm

open Classical in
theorem fSurv_gridX (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) :
    (if Bt ja.1 ∣ ja.2 then fSurvX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ S (cstar ja.1 ja.2) ω
      else 0) =
      ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
        (if Bt ja.1 ∣ ja.2 ∧ NoOverflowD Lv sl E thr0 Bt (ωsC E NE D Lt K ω) NE
            (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
              (sortLay sl) NE (zE sl B zOf yy)) ∧
          SurvD D Lv NE S (cstar ja.1 ja.2)
            (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
              (sortLay sl) NE (zE sl B zOf yy))
        then 1 else 0) := by
  by_cases h : Bt ja.1 ∣ ja.2
  · rw [if_pos h]
    unfold fSurvX
    refine Finset.sum_congr rfl fun yy _ => ?_
    congr 1
    exact if_congr (by simp [h]) rfl rfl
  · rw [if_neg h]
    symm
    exact Finset.sum_eq_zero fun yy _ => by simp [h]

open Classical in
/-- The cap: in every coin vector, the grid opportunities carry total survival weight at most `D·Lv·S`. -/
theorem cap_fSurvX (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (hD : 0 < D) (hLv : 0 < Lv)
    (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j) (S : ℕ)
    (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 then
        fSurvX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ S (cstar ja.1 ja.2) ω else 0)
      ≤ D * Lv * S := by
  simp only [fSurv_gridX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ cstar S _ ω]
  rw [Finset.sum_comm]
  calc ∑ yy : Fin NE → Y, ∑ ja : Fin D × Fin NE, Pool.P0070.wR μ yy *
        (if Bt ja.1 ∣ ja.2 ∧ NoOverflowD Lv sl E thr0 Bt (ωsC E NE D Lt K ω) NE
            (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
              (sortLay sl) NE (zE sl B zOf yy)) ∧
          SurvD D Lv NE S (cstar ja.1 ja.2)
            (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
              (sortLay sl) NE (zE sl B zOf yy))
        then 1 else 0)
      ≤ ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy * (D * Lv * S) := by
        refine Finset.sum_le_sum fun yy _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (wR_nonneg_μ μ hμ0 yy)
        refine le_trans ?_ (card_surv_leD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr (rhX (extE ext xd yy)) hD hLv hlev
          cstar hE hthr (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (zE sl B zOf yy) S)
        rw [Finset.card_filter]
        push_cast
        exact Finset.sum_le_sum fun ja _ => by
          by_cases h1 : Bt ja.1 ∣ ja.2 ∧ NoOverflowD Lv sl E thr0 Bt (ωsC E NE D Lt K ω) NE
              (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (ωsC E NE D Lt K ω)
                (φC NE D Lt K ω) (sortLay sl) NE (zE sl B zOf yy)) ∧
            SurvD D Lv NE S (cstar ja.1 ja.2)
              (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (ωsC E NE D Lt K ω)
                (φC NE D Lt K ω) (sortLay sl) NE (zE sl B zOf yy))
          · rw [if_pos h1, if_pos ⟨h1.1, h1.2.2⟩]
          · rw [if_neg h1]; split_ifs <;> norm_num
    _ = D * Lv * S := by
        rw [← Finset.sum_mul, Pool.P0097.sum_wR _ hμ1 NE, one_mul]

open Classical in
/-- The survival weight of grid point `ja` (zero off the grid). -/
noncomputable def fGX (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) : ℝ :=
  if Bt ja.1 ∣ ja.2 then fSurvX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ S (cstar ja.1 ja.2) ω else 0

theorem fG_nonnegX (hμ0 : ∀ y, 0 ≤ μ y) (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE)
    (ω : SlotC NE D Lt K × ι → Bool) :
    0 ≤ fGX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ cstar S ja ω := by
  unfold fGX; split_ifs
  · exact fSurv_nonnegX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ hμ0 S _ ω
  · exact le_rfl

open Classical in
theorem cap_fGX (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1) (hD : 0 < D) (hLv : 0 < Lv)
    (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j) (S : ℕ)
    (Sop : Fin D × Fin NE → Finset (SlotC NE D Lt K × ι)) (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ ja : Fin D × Fin NE, (if EvS (Sop ja) oppVal ω then
        fGX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ cstar S ja ω else 0) ≤ D * Lv * S := by
  refine le_trans (Finset.sum_le_sum fun ja _ => ?_)
    (cap_fSurvX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ hμ0 hμ1 hD hLv hlev cstar hE hthr S ω)
  by_cases h : EvS (Sop ja) oppVal ω
  · rw [if_pos h]; rfl
  · rw [if_neg h]; exact fG_nonnegX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ hμ0 cstar S ja ω

open Classical in
theorem hper_fGX (hc : Causal rhX) (A : PermAct sl B zOf ext μ) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hD : 0 < D) (S : ℕ) (ω : SlotC NE D Lt K × ι → Bool) (ja : Fin D × Fin NE) :
    ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
      (if Bt ja.1 ∣ ja.2 ∧
        NoOverflowD Lv sl E thr0 Bt (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
          (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
            (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (lastLay sl (cstar ja.1 ja.2)) NE (zE sl B zOf yy)) ∧
        SurvD D Lv NE S (cstar ja.1 ja.2) (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
          (lastLay sl (cstar ja.1 ja.2)) NE (zE sl B zOf yy)) then 1 else 0) =
      fGX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ cstar S ja
        (force (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω) := by
  by_cases h : Bt ja.1 ∣ ja.2
  · unfold fGX Pool.P0119.SopG
    rw [if_pos h, dif_pos h]
    rw [← forced_lawX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ hc A S (cstar ja.1 ja.2) _ ω]
    refine Finset.sum_congr rfl fun yy _ => ?_
    congr 1
    exact if_congr (by simp [h]) rfl rfl
  · unfold fGX
    rw [if_neg h]
    exact Finset.sum_eq_zero fun yy _ => by simp [h]

open Classical in
/-- **Expected number of bad opportunities when the rule reads external coin information** (P0185's
`count_bad_DZ` for a causal rule family `rhX` reading `ext`). Over the sampling/filter coins (P0082's array, weights
`wtv p`) and independent unit coins `y ∼ μ`, the expected number of grid opportunities `(j, a)` whose comparator copy
is not sampled and, forced into its own copy-last run (with the rule of the same unit coins), is never evicted before
`NE` is at most `D·Lv·S/π + D·NE·P(the actual run is not GoodAD)`. -/
theorem count_bad_X (hc : Causal rhX) (A : PermAct sl B zOf ext μ) (hμ0 : ∀ y, 0 ≤ μ y) (hμ1 : ∑ y, μ y = 1)
    (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (p : SlotC NE D Lt K × ι → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (π : ℝ) (hπ : 0 < π)
    (hπ1 : π ≤ 1)
    (hpi : ∀ (j : Fin D) (a : Fin NE) (h : Bt j ∣ a),
      π ≤ piS p (oppSet E thr0 D Bt lev NE Lt K (cstar j a)
        (by rw [hE j a (by omega) h a.2]; exact a.2)) oppVal)
    (S : ℕ) :
    ∑ ω, wtv p ω * ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
      (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev
          (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl (cstar ja.1 ja.2)) (zE sl B zOf yy)) ∅
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ)
      ≤ (D * Lv * S : ℝ) / π + D * NE * ∑ ω, wtv p ω * ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
        (if GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr (rhX (extE ext xd yy)) NE S (ωsC E NE D Lt K ω)
          (φC NE D Lt K ω) (zE sl B zOf yy) then 0 else 1) := by
  have hD := hB.hD
  have hw : ∀ ω, 0 ≤ wtv p ω := wtv_nonneg hp0 hp1
  have hwR : ∀ yy : Fin NE → Y, 0 ≤ Pool.P0070.wR μ yy := fun yy => wR_nonneg_μ μ hμ0 yy
  have hpiG : ∀ ja : Fin D × Fin NE, π ≤ piS p (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal := by
    intro ja
    by_cases h : Bt ja.1 ∣ ja.2
    · unfold Pool.P0119.SopG; rw [dif_pos h]; exact hpi ja.1 ja.2 h
    · unfold Pool.P0119.SopG; rw [dif_neg h]; simp only [piS, Finset.prod_empty]; exact hπ1
  have hcap : ∀ ω : SlotC NE D Lt K × ι → Bool, ∑ ja : Fin D × Fin NE,
      (if EvS (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω then
        fGX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ cstar S ja ω else 0) ≤ (D * Lv * S : ℝ) :=
    cap_fGX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ hμ0 hμ1 hD hLv hlev cstar hE hthr S
      (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD)
  have hcount := Pool.P0119.forced_count_real p hp0 hp1 (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD)
    (fun _ => oppVal) (fGX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ cstar S)
    (fG_nonnegX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ hμ0 cstar S)
    (D * Lv * S : ℝ) π hπ hpiG (fun ω => by convert hcap ω)
  refine le_trans (Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun yy _ =>
    mul_le_mul_of_nonneg_left (card_bad_leD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr (rhX (extE ext xd yy)) cstar hE hD
      S ω (zE sl B zOf yy)) (hwR yy)) (hw ω)) ?_
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : ∀ ω, ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
      ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 ∧
        NoOverflowD Lv sl E thr0 Bt (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
          (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev
            (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
            (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (lastLay sl (cstar ja.1 ja.2)) NE (zE sl B zOf yy)) ∧
        SurvD D Lv NE S (cstar ja.1 ja.2) (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) E thr0 θ R K Bt lev
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
          (lastLay sl (cstar ja.1 ja.2)) NE (zE sl B zOf yy)) then 1 else 0) =
      ∑ ja, fGX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ cstar S ja
        (force (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω) := by
    intro ω
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ja _ => ?_
    rw [← hper_fGX E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr zOf ext xd rhX μ hc A cstar hE hD S ω ja]
  simp only [h1]
  have h2 : ∑ ω, wtv p ω * ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
      ((D : ℝ) * NE * (if GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr (rhX (extE ext xd yy)) NE S
        (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (zE sl B zOf yy) then 0 else 1)) =
      D * NE * ∑ ω, wtv p ω * ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
        (if GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr (rhX (extE ext xd yy)) NE S (ωsC E NE D Lt K ω)
          (φC NE D Lt K ω) (zE sl B zOf yy) then 0 else 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun yy _ => by ring
  rw [h2]
  refine le_trans (le_of_eq ?_) (add_le_add_left hcount _)
  congr 1

end Count

end Pool.P0200

namespace Pool.P0200

open Finset Pool.P0095 Pool.P0065 Pool.P0081 Pool.P0082 Pool.P0052 Pool.P0048 Pool.P0105 Pool.P0156 Pool.P0164
  Pool.P0176 Pool.P0185

section Closed

attribute [local instance] coinFintype

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ) (ℓr : ℕ → ι → ℝ)
  {Y X : Type} [Fintype Y] (zOf : Y → Fin B → RT D sl) (ext : Y → X) (xd : X)
  (rhX : (ℕ → X) → ℕ → ι → (ℕ → ℝ) → Bool) (μ : Y → ℝ) {NE Lt : ℕ}

open Classical in
/-- **Bad walk points with an external-reading rule, closed form** (P0185's `count_bad_DZ_closed`): with P0085's
schedule `levTh Ld Bt`, P0091's coin law `pC ps q`, independent unit coins `y ∼ μ` (a law) and
`S = s0 + D·Lv·S' + 1`, `E[#bad] ≤ D·Lv·S/(ps(1−q)^{K·D(2Ld+NE/2^Ld+1)}) + D·NE·(NE·D·δs + NE·D·(Lt+1)·K·delta)`. -/
theorem count_bad_X_closed (hc : Causal rhX) (A : PermAct sl B zOf ext μ) (hμ0 : ∀ y, 0 ≤ μ y)
    (hμ1 : ∑ y, μ y = 1)
    (hB : BtHyp D Bt) {Ld : ℕ} (hLv2 : Ld + 2 ≤ Lv) (hLt : Ld ≤ Lt)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    {ps q : ℝ} (hps0 : 0 < ps) (hps1 : ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hEm : Monotone E) {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ xr j) (hℓ0 : ∀ u x, 0 ≤ ℓr u x)
    (hℓ1 : ∀ u x, ℓr u x ≤ 1) (hBm0 : 0 ≤ Bm) (hBm : Bm ≤ B / xmin)
    (hR : 1 ≤ R) (hT : B / xmin * NE ≤ 2 ^ (R - 1) * θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * R ≤ M0)
    (hk : 4 * R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S') (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * ((S' : ℝ) + (s0 + D * Lv * S')) ≤ S')
    (hsl : ∀ j, (D : ℝ) * ((s0 + D * Lv * S') + (Lv - 1 : ℕ) * S') + D * s0 + 1 ≤ sl j) :
    ∑ ω, Pool.P0048.wtv (Pool.P0091.pC (NE := NE) (D := D) (Lt := Lt) (K := K) ps q) ω *
      ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
      (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt)
          (dzUpd D Lv sl B Bm xr ℓr (rhX (extE ext xd yy)) (lastLay sl (cstar ja.1 ja.2)) (zE sl B zOf yy)) ∅
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ)
      ≤ (D * Lv * (s0 + D * Lv * S' + 1) : ℝ) / (ps * (1 - q) ^ (K * (D * (2 * Ld + NE / 2 ^ Ld + 1)))) +
        D * NE * (NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0) := by
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
    exact Pool.P0091.piS_geT (E := E) (thr0 := thr0) hB hps0.le hq0 hq1.le (cstar j a) _ (by rw [he, ht]; exact h)
      (by rw [ht]; exact j.2)
  have h1 := count_bad_X E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) sl B Bm xr ℓr zOf ext xd rhX μ hc A hμ0 hμ1
    hB hLv hlev cstar hE hthr (Pool.P0091.pC ps q) hp0 hp1 π hπ hπ1 hpi (s0 + D * Lv * S' + 1)
  set Pbad := (NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0 : ℝ) with hPbad
  have hPna : ∑ ω, Pool.P0048.wtv (Pool.P0091.pC ps q) ω * ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
      (if GoodAD E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) sl B Bm xr ℓr (rhX (extE ext xd yy)) NE
        (s0 + D * Lv * S' + 1) (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (zE sl B zOf yy) then 0 else 1) ≤ Pbad := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ yy : Fin NE → Y, ∑ ω, Pool.P0048.wtv (Pool.P0091.pC ps q) ω *
          (Pool.P0070.wR μ yy *
          (if GoodAD E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) sl B Bm xr ℓr (rhX (extE ext xd yy)) NE
            (s0 + D * Lv * S' + 1) (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (zE sl B zOf yy) then 0 else 1))
        = ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy *
          ∑ ω, Pool.P0048.wtv (Pool.P0091.pC ps q) ω *
          (if GoodAD E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) sl B Bm xr ℓr (rhX (extE ext xd yy)) NE
            (s0 + D * Lv * S' + 1) (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (zE sl B zOf yy) then 0 else 1) := by
          refine Finset.sum_congr rfl fun yy _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ ∑ yy : Fin NE → Y, Pool.P0070.wR μ yy * Pbad :=
          Finset.sum_le_sum fun yy _ => mul_le_mul_of_nonneg_left
            (prob_notGoodAD_le E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) sl B Bm xr ℓr (rhX (extE ext xd yy))
              ⟨hps0.le, hps1⟩ hq0 hq1.le hEm hB hLv hlev hxmin hx hℓ0 hℓ1 hBm0 hBm hR hT M0 kk hM0 hk hp hlevLt s0
              δs hs S' hM0S hρS hsl (zE sl B zOf yy))
            (wR_nonneg_μ μ hμ0 yy)
      _ = Pbad := by rw [← Finset.sum_mul, Pool.P0097.sum_wR _ hμ1 NE, one_mul]
  refine h1.trans ?_
  have hDNE : (0 : ℝ) ≤ D * NE := by positivity
  have := mul_le_mul_of_nonneg_left hPna hDNE
  push_cast at this ⊢
  linarith

end Closed

end Pool.P0200
