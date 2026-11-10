import Pool.P0176.DZProc
import Pool.P0164.ZCount
import Pool.P0170.ZGood

/-!
# Bad walk points of Design Z's per-thread multi-slot process (P0119/P0164 for `dzRun`; P0166's C5)
-/

namespace Pool.P0185

open Finset Pool.P0095 Pool.P0065 Pool.P0081 Pool.P0082 Pool.P0052 Pool.P0048 Pool.P0105 Pool.P0156 Pool.P0164
  Pool.P0176

section Count

attribute [local instance] coinFintype

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ) (ℓr : ℕ → ι → ℝ)
  (rh : ℕ → ι → (ℕ → ℝ) → Bool) (w0 : ℝ) {NE Lt : ℕ}

/-- The survival event of opportunity `c` on a trajectory: `c` is in some pool at `NE` and every sub-pool at
`NE` has at most `S` copies. -/
def SurvD (NE S : ℕ) (c : ι) (tr : ℕ → GSt ι (Finset ι)) : Prop :=
  (∃ r ℓ, c ∈ (tr NE).pools r ℓ) ∧ ∀ r < D, ∀ ℓ < Lv, ((tr NE).pools r ℓ).card ≤ S

open Classical in
/-- The slot probability that, in the entry-order run on coins `ω`, nothing overflows before `NE` and the
copy `c` survives (with small pools). -/
noncomputable def fSurvD (S : ℕ) (c : ι) (ω : SlotC NE D Lt K × ι → Bool) : ℝ :=
  ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
    (if NoOverflowD Lv sl E thr0 Bt (ωsC E NE D Lt K ω) NE
          (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (sortLay sl) NE (extZ sl B yy)) ∧
        SurvD D Lv NE S c
          (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (sortLay sl) NE (extZ sl B yy))
      then 1 else 0)

omit [LinearOrder ι] [Fintype ι] in
theorem wR_nonneg_U (hw0 : 0 ≤ w0) (hx0 : ∀ j, 0 ≤ xr j) {T : ℕ} (yy : Fin T → Fin B → RT D sl) :
    0 ≤ Pool.P0070.wR (wU sl B xr w0) yy :=
  Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun t _ => by
    rcases yy _ t with _ | ⟨j, k⟩
    · exact hw0
    · exact hx0 j

theorem fSurv_nonnegD (hw0 : 0 ≤ w0) (hx0 : ∀ j, 0 ≤ xr j) (S : ℕ) (c : ι) (ω : SlotC NE D Lt K × ι → Bool) :
    0 ≤ fSurvD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 S c ω :=
  Finset.sum_nonneg fun yy _ => mul_nonneg (wR_nonneg_U D sl B xr w0 hw0 hx0 yy) (by split_ifs <;> norm_num)

open Classical in
/-- **Per-opportunity law step.** The slot probability that the FORCED copy-last run of `c` (on coins `ω`)
does not overflow and has `c` surviving equals `fSurv` at the forced coins: the forced run is the run on the
P0048-forced coins (`foRun_force_eq`), and P0111 moves copy-last to entry order. -/
theorem forced_lawD (S : ℕ) (c : ι) (hc : E c < NE) (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
      (if NoOverflowD Lv sl E thr0 Bt (forceS (ωsC E NE D Lt K ω) c) NE
            (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (forceS (ωsC E NE D Lt K ω) c) (forceF K (φC NE D Lt K ω) c)
              (lastLay sl c) NE (extZ sl B yy)) ∧
          SurvD D Lv NE S c (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (forceS (ωsC E NE D Lt K ω) c)
            (forceF K (φC NE D Lt K ω) c) (lastLay sl c) NE (extZ sl B yy))
        then 1 else 0) =
      fSurvD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 S c (force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω) := by
  set ω' := force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω
  have htr : ∀ yy : Fin NE → Fin B → RT D sl,
      trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (forceS (ωsC E NE D Lt K ω) c) (forceF K (φC NE D Lt K ω) c)
        (lastLay sl c) NE (extZ sl B yy) =
      trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (ωsC E NE D Lt K ω') (φC NE D Lt K ω') (lastLay sl c) NE (extZ sl B yy) := by
    intro yy; funext a
    simp only [trajD]
    exact (gRun_force_eq E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl c) (extZ sl B yy)) ∅ c hc ω _).symm
  have hs := Pool.P0119.ωsC_force E thr0 K D Bt lev c hc ω
  simp only [htr]
  rw [← hs]
  unfold fSurvD
  exact (law_sort_last_DZ Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (ωsC E NE D Lt K ω') (φC NE D Lt K ω') w0 c NE
    (SurvD D Lv NE S c)).symm

end Count

section Bad

attribute [local instance] coinFintype

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ) (ℓr : ℕ → ι → ℝ)
  (rh : ℕ → ι → (ℕ → ℝ) → Bool) (w0 : ℝ)

/-- **Forced runs overflow every thread at most one slot later than the actual run** (P0115's
`Vat_forced_card_le`, per thread). -/
theorem Vblk_forced_card_le {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (y : ℕ → Fin B → RT D sl) (u : ℕ) (j : ℕ) :
    (blockMem Lv (startPools E thr0 D Lv Bt (forceS ωs c) u
        (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) y (forceS ωs c) (forceF K φ c) u).pools) j).card ≤
      (blockMem Lv (startPools E thr0 D Lv Bt ωs u
        (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) y ωs φ u).pools) j).card + 1 := by
  classical
  have hs : AgreeOff c (forceS ωs c) ωs := fun x hx => by simp [forceS, Function.update_of_ne hx]
  have hP : (fun r ℓ => ((dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) y (forceS ωs c) (forceF K φ c)
      u).pools r ℓ).erase c) = (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) y ωs φ u).pools := by
    funext r ℓ
    rw [(dz_forced_erase Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev y hc φ u).1 r ℓ,
      dz_free_eq Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev y hc φ u]
  have hV : (blockMem Lv (startPools E thr0 D Lv Bt (forceS ωs c) u
      (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) y (forceS ωs c) (forceF K φ c) u).pools) j).erase c =
      blockMem Lv (startPools E thr0 D Lv Bt ωs u
        (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) y ωs φ u).pools) j := by
    rw [← blockMem_erase]
    congr 1
    funext r ℓ
    rw [startPools_erase c (forceS ωs c) ωs hs hc, hP]
  have := Finset.pred_card_le_card_erase (s := blockMem Lv (startPools E thr0 D Lv Bt (forceS ωs c) u
    (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) y (forceS ωs c) (forceF K φ c) u).pools) j) (a := c)
  rw [hV] at this
  omega

/-- The good event of the actual (entry-order) run: every thread has at least one free slot before `T`, and sub-pools
have size at most `S − 1` at `T`. -/
def GoodAD (T S : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin B → RT D sl) : Prop :=
  (∀ u < T, ∀ j : Fin D, (blockMem Lv (startPools E thr0 D Lv Bt ωs u
      (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) y ωs φ u).pools) j).card + 1 ≤ sl j) ∧
    ∀ r < D, ∀ ℓ < Lv, ((dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) y ωs φ T).pools r ℓ).card + 1 ≤ S

open Classical in
/-- **A bad opportunity survives in its forced run, or the actual run is not good.** If `c` is not sampled and,
forced in, is never evicted before `T` (P0065's `evict … = none`, with the forced run's own estimates), then either
its forced copy-last run does not overflow and `c` survives at `T` with small pools, or the actual run fails
`GoodA`. -/
theorem bad_leD (T S : ℕ) (cstar : ℕ → ℕ → ι) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} (y : ℕ → Fin B → RT D sl)
    {j a : ℕ} (ha : a < T) (hc : ωs (cstar j a) = false)
    (hev : evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl (cstar j a)) y) ∅ (forceS ωs (cstar j a)) (forceF K φ (cstar j a))) θ R K D Lv Bt lev T cstar ωs φ j a = none) :
    (1 : ℝ) ≤ (if NoOverflowD Lv sl E thr0 Bt (forceS ωs (cstar j a)) T
            (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (forceS ωs (cstar j a)) (forceF K φ (cstar j a))
              (lastLay sl (cstar j a)) T y) ∧
          SurvD D Lv T S (cstar j a) (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (forceS ωs (cstar j a))
            (forceF K φ (cstar j a)) (lastLay sl (cstar j a)) T y) then 1 else 0) +
      (if GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh T S ωs φ y then 0 else 1) := by
  set c := cstar j a with hcdef
  by_cases hg : GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh T S ωs φ y
  · rw [if_pos hg, add_zero, if_pos]
    have hmin : ∀ u, u ≤ T → min u T = u := fun u hu => Nat.min_eq_left hu
    refine ⟨fun u hu => ?_, ⟨?_, fun r hr ℓ hℓ => ?_⟩⟩
    · simp only [trajD, hmin u hu.le]
      intro jj
      have h1 := Vblk_forced_card_le E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh hc φ y u jj
      have h2 := hg.1 u hu jj
      unfold blockMem at h1 h2 ⊢
      omega
    · simp only [trajD, Nat.min_self]
      unfold evict at hev
      split_ifs at hev with h
      have hal : Alive E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl c) y) ∅ (forceS ωs c)
          (forceF K φ c))
          θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) T c := by
        by_contra hna
        exact h ⟨T, ha, le_rfl, hna⟩
      obtain ⟨r, ℓ, hm⟩ := hal
      refine ⟨r, ℓ, ?_⟩
      rwa [← gRun_pools_eq] at hm
    · simp only [trajD, Nat.min_self]
      have he := (dz_forced_erase Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev y hc φ T).1 r ℓ
      rw [dz_free_eq Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev y hc φ T] at he
      have h1 := Finset.pred_card_le_card_erase (s := (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) y
        (forceS ωs c) (forceF K φ c) T).pools r ℓ) (a := c)
      rw [he] at h1
      have h2 := hg.2 r hr ℓ hℓ
      omega
  · rw [if_neg hg]
    have : (0 : ℝ) ≤ (if NoOverflowD Lv sl E thr0 Bt (forceS ωs c) T
            (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (forceS ωs c) (forceF K φ c) (lastLay sl c) T y) ∧
          SurvD D Lv T S c (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (forceS ωs c) (forceF K φ c) (lastLay sl c) T y)
        then 1 else 0) := by split_ifs <;> norm_num
    linarith

end Bad

section Main

attribute [local instance] coinFintype

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ) (ℓr : ℕ → ι → ℝ)
  (rh : ℕ → ι → (ℕ → ℝ) → Bool) (w0 : ℝ) {NE Lt : ℕ}

open Classical in
/-- At most `D·Lv·S` grid opportunities survive with small pools in one run. -/
theorem card_surv_leD (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin B → RT D sl) (S : ℕ) :
    (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ SurvD D Lv NE S (cstar ja.1 ja.2)
      (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (sortLay sl) NE y)} : ℝ) ≤ D * Lv * S := by
  set F := (Finset.univ.filter fun ja : Fin D × Fin NE => Bt ja.1 ∣ ja.2 ∧ SurvD D Lv NE S (cstar ja.1 ja.2)
      (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (sortLay sl) NE y)) with hF
  by_cases hne : F.Nonempty
  · obtain ⟨ja0, hja0⟩ := hne
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hja0
    have hsz := hja0.2.2
    simp only [trajD, Nat.min_self] at hsz
    rw [gRun_pools_eq] at hsz
    have hinj : Set.InjOn (fun ja : Fin D × Fin NE => cstar ja.1 ja.2) (F : Set (Fin D × Fin NE)) := by
      rintro ⟨j, a⟩ hj1 ⟨j', a'⟩ hj2 heq
      simp only [hF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj1 hj2
      simp only at heq
      have h1 := hE j a (by omega) hj1.1 a.2
      have h2 := hE j' a' (by omega) hj2.1 a'.2
      have h3 := hthr j a (by omega) hj1.1 a.2
      have h4 := hthr j' a' (by omega) hj2.1 a'.2
      rw [heq] at h1 h3
      ext <;> simp only <;> omega
    have himg := Finset.card_image_of_injOn hinj
    have hA := card_alive_le hD hLv hlev _ _ NE S hsz (F.image fun ja : Fin D × Fin NE => cstar ja.1 ja.2)
      (fun c hc => by
        simp only [Finset.mem_image, hF, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        obtain ⟨ja, ⟨-, hal, -⟩, rfl⟩ := hc
        obtain ⟨r, ℓ, hm⟩ := hal
        simp only [trajD, Nat.min_self] at hm
        rw [gRun_pools_eq] at hm
        exact ⟨r, ℓ, hm⟩)
    rw [himg] at hA
    exact_mod_cast hA
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

open Classical in
theorem fSurv_gridD (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) :
    (if Bt ja.1 ∣ ja.2 then fSurvD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 S (cstar ja.1 ja.2) ω else 0) =
      ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
        (if Bt ja.1 ∣ ja.2 ∧ NoOverflowD Lv sl E thr0 Bt (ωsC E NE D Lt K ω) NE
            (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (sortLay sl) NE (extZ sl B yy)) ∧
          SurvD D Lv NE S (cstar ja.1 ja.2)
            (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (sortLay sl) NE (extZ sl B yy))
        then 1 else 0) := by
  by_cases h : Bt ja.1 ∣ ja.2
  · rw [if_pos h]
    unfold fSurvD
    refine Finset.sum_congr rfl fun yy _ => ?_
    congr 1
    exact if_congr (by simp [h]) rfl rfl
  · rw [if_neg h]
    symm
    exact Finset.sum_eq_zero fun yy _ => by simp [h]

open Classical in
/-- The cap: in every coin vector, the grid opportunities carry total survival weight at most `D·Lv·S`. -/
theorem cap_fSurvD (hw0 : 0 ≤ w0) (hx0 : ∀ j, 0 ≤ xr j) (hw1 : ∑ zc : Fin B → RT D sl, wU sl B xr w0 zc = 1) (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j) (S : ℕ)
    (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 then fSurvD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 S (cstar ja.1 ja.2) ω else 0)
      ≤ D * Lv * S := by
  simp only [fSurv_gridD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 cstar S _ ω]
  rw [Finset.sum_comm]
  calc ∑ yy : Fin NE → Fin B → RT D sl, ∑ ja : Fin D × Fin NE, Pool.P0070.wR (wU sl B xr w0) yy *
        (if Bt ja.1 ∣ ja.2 ∧ NoOverflowD Lv sl E thr0 Bt (ωsC E NE D Lt K ω) NE
            (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (sortLay sl) NE (extZ sl B yy)) ∧
          SurvD D Lv NE S (cstar ja.1 ja.2)
            (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (sortLay sl) NE (extZ sl B yy))
        then 1 else 0)
      ≤ ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy * (D * Lv * S) := by
        refine Finset.sum_le_sum fun yy _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (wR_nonneg_U D sl B xr w0 hw0 hx0 yy)
        refine le_trans ?_ (card_surv_leD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh hD hLv hlev cstar hE hthr
          (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extZ sl B yy) S)
        rw [Finset.card_filter]
        push_cast
        exact Finset.sum_le_sum fun ja _ => by
          by_cases h1 : Bt ja.1 ∣ ja.2 ∧ NoOverflowD Lv sl E thr0 Bt (ωsC E NE D Lt K ω) NE
              (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (sortLay sl) NE (extZ sl B yy)) ∧
            SurvD D Lv NE S (cstar ja.1 ja.2)
              (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (sortLay sl) NE (extZ sl B yy))
          · rw [if_pos h1, if_pos ⟨h1.1, h1.2.2⟩]
          · rw [if_neg h1]; split_ifs <;> norm_num
    _ = D * Lv * S := by
        rw [← Finset.sum_mul, Pool.P0097.sum_wR _ hw1 NE, one_mul]

open Classical in
/-- Pointwise: the bad opportunities are the surviving forced ones, plus all of them on runs that are not good. -/
theorem card_bad_leD (cstar : ℕ → ℕ → ι) (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hD : 0 < D) (S : ℕ) (ω : SlotC NE D Lt K × ι → Bool) (yy : ℕ → Fin B → RT D sl) :
    (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl (cstar ja.1 ja.2)) yy) ∅ (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ) ≤
      ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 ∧
          NoOverflowD Lv sl E thr0 Bt (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
            (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
              (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (lastLay sl (cstar ja.1 ja.2)) NE yy) ∧
          SurvD D Lv NE S (cstar ja.1 ja.2) (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev
            (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
            (lastLay sl (cstar ja.1 ja.2)) NE yy) then 1 else 0) +
        D * NE * (if GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) yy then 0 else 1) := by
  rw [Finset.card_filter]
  push_cast
  have hcard : (D * NE : ℝ) = ∑ _ja : Fin D × Fin NE, (1 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
  rw [hcard, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ja _ => ?_
  split_ifs with h1 h2 h3 h4 <;> try norm_num
  all_goals first
    | (have := bad_leD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh NE S cstar yy (j := ja.1) (a := ja.2) ja.2.2 h1.2.1 h1.2.2
       rw [if_neg (fun h => by tauto), if_pos (by assumption)] at this; linarith)
    | (have := bad_leD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh NE S cstar yy (j := ja.1) (a := ja.2) ja.2.2 h1.2.1 h1.2.2
       simp_all)

open Classical in
/-- The survival weight of grid point `ja` (zero off the grid). -/
noncomputable def fGD (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) : ℝ :=
  if Bt ja.1 ∣ ja.2 then fSurvD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 S (cstar ja.1 ja.2) ω else 0

theorem fG_nonnegD (hw0 : 0 ≤ w0) (hx0 : ∀ j, 0 ≤ xr j) (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) :
    0 ≤ fGD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 cstar S ja ω := by
  unfold fGD; split_ifs
  · exact fSurv_nonnegD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 hw0 hx0 S _ ω
  · exact le_rfl

open Classical in
theorem cap_fGD (hw0 : 0 ≤ w0) (hx0 : ∀ j, 0 ≤ xr j) (hw1 : ∑ zc : Fin B → RT D sl, wU sl B xr w0 zc = 1) (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j) (S : ℕ)
    (Sop : Fin D × Fin NE → Finset (SlotC NE D Lt K × ι)) (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ ja : Fin D × Fin NE, (if EvS (Sop ja) oppVal ω then fGD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 cstar S ja ω else 0)
      ≤ D * Lv * S := by
  refine le_trans (Finset.sum_le_sum fun ja _ => ?_)
    (cap_fSurvD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 hw0 hx0 hw1 hD hLv hlev cstar hE hthr S ω)
  by_cases h : EvS (Sop ja) oppVal ω
  · rw [if_pos h]; rfl
  · rw [if_neg h]; exact fG_nonnegD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 hw0 hx0 cstar S ja ω

open Classical in
theorem hper_fGD (cstar : ℕ → ℕ → ι) (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hD : 0 < D) (S : ℕ) (ω : SlotC NE D Lt K × ι → Bool) (ja : Fin D × Fin NE) :
    ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
      (if Bt ja.1 ∣ ja.2 ∧
        NoOverflowD Lv sl E thr0 Bt (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
          (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
            (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (lastLay sl (cstar ja.1 ja.2)) NE (extZ sl B yy)) ∧
        SurvD D Lv NE S (cstar ja.1 ja.2) (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
          (lastLay sl (cstar ja.1 ja.2)) NE (extZ sl B yy)) then 1 else 0) =
      fGD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 cstar S ja (force (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω) := by
  by_cases h : Bt ja.1 ∣ ja.2
  · unfold fGD Pool.P0119.SopG
    rw [if_pos h, dif_pos h]
    rw [← forced_lawD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 S (cstar ja.1 ja.2) _ ω]
    refine Finset.sum_congr rfl fun yy _ => ?_
    congr 1
    exact if_congr (by simp [h]) rfl rfl
  · unfold fGD
    rw [if_neg h]
    exact Finset.sum_eq_zero fun yy _ => by simp [h]

open Classical in
/-- **Expected number of bad opportunities of the per-thread process** (P0119/P0164's count for `dzRun`). Over the
sampling/filter coins (P0082's array, weights `wtv p`) and independent rounds with per-thread rates (round weights
`wR (wU sl B xr w0)`: slot `(j, k)` has weight `xr j`, a non-slot round `w0`), the expected number of grid
opportunities `(j, a)` whose comparator copy is not sampled and, forced into its own forced copy-last run, is never
evicted before `NE` is at most `D·Lv·S/π + D·NE·P(the actual run is not GoodA)`. -/
theorem count_bad_DZ (hw0 : 0 ≤ w0) (hx0 : ∀ j, 0 ≤ xr j) (hw1 : ∑ zc : Fin B → RT D sl, wU sl B xr w0 zc = 1) (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (p : SlotC NE D Lt K × ι → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (π : ℝ) (hπ : 0 < π)
    (hπ1 : π ≤ 1)
    (hpi : ∀ (j : Fin D) (a : Fin NE) (h : Bt j ∣ a),
      π ≤ piS p (oppSet E thr0 D Bt lev NE Lt K (cstar j a)
        (by rw [hE j a (by omega) h a.2]; exact a.2)) oppVal)
    (S : ℕ) :
    ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
      (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl (cstar ja.1 ja.2)) (extZ sl B yy)) ∅ (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ)
      ≤ (D * Lv * S : ℝ) / π + D * NE * ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin B → RT D sl,
        Pool.P0070.wR (wU sl B xr w0) yy *
        (if GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extZ sl B yy) then 0 else 1) := by
  have hD := hB.hD
  have hw : ∀ ω, 0 ≤ wtv p ω := wtv_nonneg hp0 hp1
  have hwR : ∀ yy : Fin NE → Fin B → RT D sl, 0 ≤ Pool.P0070.wR (wU sl B xr w0) yy := fun yy => wR_nonneg_U D sl B xr w0 hw0 hx0 yy
  have hpiG : ∀ ja : Fin D × Fin NE, π ≤ piS p (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal := by
    intro ja
    by_cases h : Bt ja.1 ∣ ja.2
    · unfold Pool.P0119.SopG; rw [dif_pos h]; exact hpi ja.1 ja.2 h
    · unfold Pool.P0119.SopG; rw [dif_neg h]; simp only [piS, Finset.prod_empty]; exact hπ1
  have hcap : ∀ ω : SlotC NE D Lt K × ι → Bool, ∑ ja : Fin D × Fin NE,
      (if EvS (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω then fGD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 cstar S ja ω
        else 0) ≤ (D * Lv * S : ℝ) :=
    cap_fGD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 hw0 hx0 hw1 hD hLv hlev cstar hE hthr S (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD)
  have hcount := Pool.P0119.forced_count_real p hp0 hp1 (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD) (fun _ => oppVal)
    (fGD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 cstar S) (fG_nonnegD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 hw0 hx0 cstar S)
    (D * Lv * S : ℝ) π hπ hpiG (fun ω => by convert hcap ω)
  refine le_trans (Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun yy _ =>
    mul_le_mul_of_nonneg_left (card_bad_leD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh cstar hE hD S ω (extZ sl B yy))
      (hwR yy)) (hw ω)) ?_
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : ∀ ω, ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
      ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 ∧
        NoOverflowD Lv sl E thr0 Bt (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
          (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
            (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (lastLay sl (cstar ja.1 ja.2)) NE (extZ sl B yy)) ∧
        SurvD D Lv NE S (cstar ja.1 ja.2) (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
          (lastLay sl (cstar ja.1 ja.2)) NE (extZ sl B yy)) then 1 else 0) =
      ∑ ja, fGD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 cstar S ja (force (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω) := by
    intro ω
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ja _ => ?_
    rw [← hper_fGD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh w0 cstar hE hD S ω ja]
  simp only [h1]
  have h2 : ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
      ((D : ℝ) * NE * (if GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
        (extZ sl B yy) then 0 else 1)) =
      D * NE * ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
        (if GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extZ sl B yy) then 0 else 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun yy _ => by ring
  rw [h2]
  refine le_trans (le_of_eq ?_) (add_le_add_left hcount _)
  congr 1

end Main
section Weights

variable {D : ℕ} (sl : Fin D → ℕ) (B : ℕ) (xr : Fin D → ℝ) (w0 : ℝ)

/-- Independent rounds: the unit weights sum to the `B`-th power of the round weights' sum. -/
theorem sum_wU : ∑ zc : Fin B → RT D sl, wU sl B xr w0 zc = (∑ r : RT D sl, wRT sl xr w0 r) ^ B := by
  unfold wU
  rw [← Fintype.prod_sum (fun (_ : Fin B) (r : RT D sl) => wRT sl xr w0 r)]
  simp

theorem sum_wU_one (h : ∑ r : RT D sl, wRT sl xr w0 r = 1) : ∑ zc : Fin B → RT D sl, wU sl B xr w0 zc = 1 := by
  rw [sum_wU, h, one_pow]

end Weights

section NotGood

attribute [local instance] coinFintype

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ) (ℓr : ℕ → ι → ℝ)
  (rh : ℕ → ι → (ℕ → ℝ) → Bool) {NE Lt : ℕ}

omit [Fintype ι] in
theorem blockMem_sub_members (sp : ℕ → ℕ → Finset ι) (j : Fin D) : blockMem Lv sp j ⊆ members D Lv sp :=
  fun _ h => mem_blockMem_members Lv j.2 h

theorem goodAD_of_goodRunT (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (ω2 : Pool.P0073.SlotT NE D Lt K → ι → Bool) (y : ℕ → Fin B → RT D sl) (s0 : ℕ) (M0 ρ : ℝ) (S' : ℕ) (hρ : 0 ≤ ρ)
    (hg : Pool.P0073.GoodRunT E thr0
      (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) y) ∅ (Pool.P0073.ωsOfT E K D ω2)
        (Pool.P0073.φOfT K D ω2))
      θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) NE s0 M0 ρ)
    (hM0S : M0 ≤ S') (hρS : ρ * ((S' : ℝ) + (s0 + D * Lv * S')) ≤ S')
    (hsl : ∀ j, (D : ℝ) * ((s0 + D * Lv * S') + (Lv - 1 : ℕ) * S') + D * s0 + 1 ≤ sl j) :
    GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh NE (s0 + D * Lv * S' + 1) (Pool.P0073.ωsOfT E K D ω2)
      (Pool.P0073.φOfT K D ω2) y := by
  have hcard := fun a ha => Pool.P0073.tpools_card_le hB hLv hlev _ _ NE s0 M0 ρ S' hρ hg hM0S (Nat.cast_nonneg _) hρS a ha
  refine ⟨fun u hu j => ?_, fun r hr ℓ hℓ => ?_⟩
  · have hpe := gRun_pools_eq E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) y) ∅
      (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) u
    have h := Pool.P0109.members_startPools_card_le E thr0 D Lv Bt (Pool.P0073.ωsOfT E K D ω2) u _ s0 S'
      (s0 + D * Lv * S') (hcard u hu.le).1 (hcard u hu.le).2.1 (fun r hr hd => hg.1 u hu r hr hd)
    rw [← hpe] at h
    have hsub := Finset.card_le_card (blockMem_sub_members D Lv (startPools E thr0 D Lv Bt (Pool.P0073.ωsOfT E K D ω2) u
      (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) y (Pool.P0073.ωsOfT E K D ω2)
        (Pool.P0073.φOfT K D ω2) u).pools) j)
    have hsub' : ((blockMem Lv (startPools E thr0 D Lv Bt (Pool.P0073.ωsOfT E K D ω2) u
      (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) y (Pool.P0073.ωsOfT E K D ω2)
        (Pool.P0073.φOfT K D ω2) u).pools) j).card : ℝ) ≤ (members D Lv (startPools E thr0 D Lv Bt
          (Pool.P0073.ωsOfT E K D ω2) u (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) y
            (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) u).pools)).card := by exact_mod_cast hsub
    have : ((blockMem Lv (startPools E thr0 D Lv Bt (Pool.P0073.ωsOfT E K D ω2) u
      (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) y (Pool.P0073.ωsOfT E K D ω2)
        (Pool.P0073.φOfT K D ω2) u).pools) j).card : ℝ) + 1 ≤ sl j := by
      have := hsl j; linarith
    exact_mod_cast this
  · have hpe := gRun_pools_eq E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) y) ∅
      (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) NE
    show ((dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) y (Pool.P0073.ωsOfT E K D ω2)
      (Pool.P0073.φOfT K D ω2) NE).pools r ℓ).card + 1 ≤ s0 + D * Lv * S' + 1
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
      have : ((tpools E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) y) ∅
          (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2)) θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2)
          (Pool.P0073.φOfT K D ω2) NE r 0).card : ℝ) + 1 ≤ ((s0 + D * Lv * S' + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have := h1 r ℓ (by omega)
      have : ((tpools E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) y) ∅
          (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2)) θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2)
          (Pool.P0073.φOfT K D ω2) NE r ℓ).card : ℝ) + 1 ≤ ((s0 + D * Lv * S' + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this

open Classical in
/-- **The actual per-thread run is good except with P0109's probability**, for every fixed sequence of unit
coins. -/
theorem prob_notGoodAD_le {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hE : Monotone E) (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ xr j) (hℓ0 : ∀ u x, 0 ≤ ℓr u x)
    (hℓ1 : ∀ u x, ℓr u x ≤ 1) (hBm0 : 0 ≤ Bm) (hBm : Bm ≤ B / xmin)
    (hR : 1 ≤ R) (hT : B / xmin * NE ≤ 2 ^ (R - 1) * θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * R ≤ M0)
    (hk : 4 * R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * R))
    (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S') (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * ((S' : ℝ) + (s0 + D * Lv * S')) ≤ S')
    (hsl : ∀ j, (D : ℝ) * ((s0 + D * Lv * S') + (Lv - 1 : ℕ) * S') + D * s0 + 1 ≤ sl j)
    (y : ℕ → Fin B → RT D sl) :
    ∑ ω, Pool.P0048.wtv (Pool.P0091.pC (NE := NE) (D := D) (Lt := Lt) (K := K) ps q) ω *
      (if GoodAD E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh NE (s0 + D * Lv * S' + 1) (ωsC E NE D Lt K ω)
          (φC NE D Lt K ω) y then 0 else 1) ≤
      NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0 := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hρ0 : 0 ≤ (1 - 1 / (4 * R : ℝ)) ^ K := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  rw [← (Equiv.curry (Pool.P0073.SlotT NE D Lt K) ι Bool).symm.sum_comp]
  refine le_trans (Finset.sum_le_sum fun ω2 _ => ?_) (prob_not_goodRunT_gen E thr0 θ R K D Lv Bt lev
    (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) y) ∅ M0 kk hps hq0 hq1 hE hB.hD hLv hlev (by positivity)
    (fun ωs φ a x => dzInc_bounds B Bm xr ℓr hxmin hx hℓ0 hℓ1 hBm0 hBm a _ _ x)
    hR hT hM0 hk hp hlevLt s0 δs hs)
  simp only [Equiv.curry_symm_apply]
  rw [Pool.P0091.wtv_uncurryT ω2]
  have hw0 : 0 ≤ Pool.P0046.bw2 (Pool.P0073.qOfT K D ps q) ω2 :=
    Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
      cases s <;> split_ifs <;> simp [Pool.P0073.qOfT] <;> linarith [hps.1, hps.2]
  refine mul_le_mul_of_nonneg_left ?_ hw0
  have hωs : ωsC E NE D Lt K (Function.uncurry ω2) = Pool.P0073.ωsOfT E K D ω2 := rfl
  have hφ : φC NE D Lt K (Function.uncurry ω2) = Pool.P0073.φOfT K D ω2 := rfl
  rw [hωs, hφ]
  by_cases hg : Pool.P0073.GoodRunT E thr0 (gCof E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) y)
      ∅ ω2) θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
  · rw [if_pos (goodAD_of_goodRunT E thr0 θ R K D Lv Bt lev sl B Bm xr ℓr rh hB hLv hlev ω2 y s0 M0 _ S' hρ0 hg hM0S
      hρS hsl)]
    split_ifs; norm_num
  · rw [if_neg hg]; split_ifs <;> norm_num

end NotGood

section Closed

attribute [local instance] coinFintype

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ) (ℓr : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) (w0 : ℝ)
  {NE Lt : ℕ}

open Classical in
/-- **Bad walk points of the per-thread process, closed form**: with P0085's schedule `levTh Ld Bt`, P0091's coin
law `pC ps q`, independent rounds with weights `wRT` summing to `1`, and `S = s0 + D·Lv·S' + 1`,
`E[#bad] ≤ D·Lv·S/(ps(1−q)^{K·D(2Ld+NE/2^Ld+1)}) + D·NE·(NE·D·δs + NE·D·(Lt+1)·K·delta)`. -/
theorem count_bad_DZ_closed (hw0 : 0 ≤ w0) (hx0 : ∀ j, 0 ≤ xr j) (hw1 : ∑ r : RT D sl, wRT sl xr w0 r = 1)
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
      ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
      (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt)
          (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl (cstar ja.1 ja.2)) (extZ sl B yy)) ∅
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
  have hW1 := sum_wU_one sl B xr w0 hw1
  have h1 := count_bad_DZ E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) sl B Bm xr ℓr rh w0 hw0 hx0 hW1 hB hLv hlev
    cstar hE hthr (Pool.P0091.pC ps q) hp0 hp1 π hπ hπ1 hpi (s0 + D * Lv * S' + 1)
  set Pbad := (NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0 : ℝ) with hPbad
  have hPna : ∑ ω, Pool.P0048.wtv (Pool.P0091.pC ps q) ω * ∑ yy : Fin NE → Fin B → RT D sl,
      Pool.P0070.wR (wU sl B xr w0) yy *
      (if GoodAD E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) sl B Bm xr ℓr rh NE (s0 + D * Lv * S' + 1)
        (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extZ sl B yy) then 0 else 1) ≤ Pbad := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ yy : Fin NE → Fin B → RT D sl, ∑ ω, Pool.P0048.wtv (Pool.P0091.pC ps q) ω *
          (Pool.P0070.wR (wU sl B xr w0) yy *
          (if GoodAD E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) sl B Bm xr ℓr rh NE (s0 + D * Lv * S' + 1)
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extZ sl B yy) then 0 else 1))
        = ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
          ∑ ω, Pool.P0048.wtv (Pool.P0091.pC ps q) ω *
          (if GoodAD E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) sl B Bm xr ℓr rh NE (s0 + D * Lv * S' + 1)
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extZ sl B yy) then 0 else 1) := by
          refine Finset.sum_congr rfl fun yy _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy * Pbad :=
          Finset.sum_le_sum fun yy _ => mul_le_mul_of_nonneg_left
            (prob_notGoodAD_le E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) sl B Bm xr ℓr rh ⟨hps0.le, hps1⟩ hq0
              hq1.le hEm hB hLv hlev hxmin hx hℓ0 hℓ1 hBm0 hBm hR hT M0 kk hM0 hk hp hlevLt s0 δs hs S' hM0S hρS hsl
              (extZ sl B yy))
            (wR_nonneg_U D sl B xr w0 hw0 hx0 yy)
      _ = Pbad := by rw [← Finset.sum_mul, Pool.P0097.sum_wR _ hW1 NE, one_mul]
  refine h1.trans ?_
  have hDNE : (0 : ℝ) ≤ D * NE := by positivity
  have := mul_le_mul_of_nonneg_left hPna hDNE
  push_cast at this ⊢
  linarith

end Closed

end Pool.P0185
