import Pool.P0186.RunMix
import Pool.P0185.DZCount

/-!
# From P0186's walk bound to P0185's bad count (Design Z per-thread process)

* `outZ_bad_evict`: a bad forced outcome (P0168) is a never-evicted forced copy (P0065's `evict … = none`, the notion
  that P0164/P0185 count).
* `nBadB_le`: P0186's mixed bad epoch starts at level `j` are among the unsampled never-evicted opportunities.
* `coup_dz`: for P0176's `dzRun`, the forced copy-last run is coupled with the entry-order run (`dz_forced_erase`,
  `dz_free_eq`), which is P0186's `Coup`.
* `walkRHS_le`: the right-hand side of P0186's `run_bound_mix` is at most `T·a 0 + M·#{bad opportunities}` when every
  level weight is at most `M`.
-/

namespace Pool.P0197

open Finset Pool.P0156 Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0168
  Pool.P0135 Pool.P0186

section Generic

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E : ι → ℕ} {thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}
  {upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι} {aux0 : Finset ι}
  {U : ι → ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι} {A0 : ι → Finset ι}
  {T : ℕ} {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool}

/-- The actual-run outcome of a copy is never `bad`. -/
lemma outA_ne_bad {jmax : ℕ} {c : ι} : outA E thr0 θ R K D Lv Bt lev upd aux0 jmax T ωs φ c ≠ .bad := by
  unfold outA
  split
  · simp
  · split_ifs <;> simp
  · simp
  · simp

/-- **A bad forced outcome is a never-evicted forced copy.** -/
theorem outZ_bad_evict {jmax : ℕ} (cstar : ℕ → ℕ → ι) {j a : ℕ} (hE : E (cstar j a) = a)
    (h : outZ E thr0 θ R K D Lv Bt lev (U (cstar j a)) (A0 (cstar j a)) jmax T ωs φ (cstar j a) = .bad) :
    evict E thr0 (fChat E thr0 θ R K D Lv Bt lev (U (cstar j a)) (A0 (cstar j a)) ωs φ (cstar j a)) θ R K D Lv Bt
      lev T cstar ωs φ j a = none := by
  classical
  have hrem : remT E thr0 θ R K D Lv Bt lev (U (cstar j a)) (A0 (cstar j a)) T ωs φ (cstar j a) = none := by
    unfold outZ at h
    split at h <;> first | rfl | (split_ifs at h) | cases h
    all_goals simp_all
  unfold remT at hrem
  split_ifs at hrem with hh
  unfold evict
  rw [dif_neg]
  rintro ⟨y, h1, h2, h3⟩
  apply hh
  refine ⟨y, by rw [hE]; exact h1, h2, ?_⟩
  rw [fRun_pools]
  exact h3

open Classical in
/-- **Mixed bad epoch starts are unsampled never-evicted opportunities.** -/
theorem nBadB_le (cstar : ℕ → ℕ → ι) (hE : ∀ j a, j < D → Bt j ∣ a → a < T → E (cstar j a) = a) {j : ℕ}
    (hj : j < D) :
    nBadB T Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev upd aux0 U A0 (D - 1) T ωs φ (cstar r τ)) j ≤
      ((Finset.range T).filter fun a => Bt j ∣ a ∧ ωs (cstar j a) = false ∧
        evict E thr0 (fChat E thr0 θ R K D Lv Bt lev (U (cstar j a)) (A0 (cstar j a)) ωs φ (cstar j a)) θ R K D Lv
          Bt lev T cstar ωs φ j a = none).card := by
  unfold nBadB
  refine Finset.card_le_card fun a ha => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at ha ⊢
  obtain ⟨haT, hd, hb⟩ := ha
  refine ⟨haT, hd, ?_⟩
  unfold outMix at hb
  split_ifs at hb with hs
  · exact absurd hb outA_ne_bad
  · exact ⟨by simpa using hs, outZ_bad_evict cstar (hE j a hj hd haT) hb⟩

/-- **The walk's right-hand side.** If every level weight is at most `M` (`Bt (j-1)·a j` for `1 ≤ j < D` and `c`),
the right-hand side of P0186's `run_bound_mix` is at most `T·a 0 + M·Σ_{j<D} nBad j`. -/
theorem walkRHS_le (t : ℕ → ℕ → Out) (a : ℕ → ℝ) (c M : ℝ) (hM0 : 0 ≤ M)
    (hMa : ∀ j, 1 ≤ j → j < D → (Bt (j - 1) : ℝ) * a j ≤ M) (hMc : c ≤ M) (hD : 0 < D) :
    T * a 0 + ∑ j ∈ Finset.Ico 1 D, (Bt (j - 1) : ℝ) * (nBadB T Bt t (j - 1) : ℝ) * a j +
        (nBadB T Bt t (D - 1) : ℝ) * c ≤
      T * a 0 + M * ∑ j ∈ Finset.range D, (nBadB T Bt t j : ℝ) := by
  have h1 : ∑ j ∈ Finset.Ico 1 D, (Bt (j - 1) : ℝ) * (nBadB T Bt t (j - 1) : ℝ) * a j ≤
      ∑ j ∈ Finset.Ico 1 D, M * (nBadB T Bt t (j - 1) : ℝ) := by
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    have := hMa j hj.1 hj.2
    have h0 : (0 : ℝ) ≤ nBadB T Bt t (j - 1) := Nat.cast_nonneg _
    nlinarith
  have h2 : (nBadB T Bt t (D - 1) : ℝ) * c ≤ M * (nBadB T Bt t (D - 1) : ℝ) := by
    have h0 : (0 : ℝ) ≤ nBadB T Bt t (D - 1) := Nat.cast_nonneg _
    nlinarith
  have h3 : ∑ j ∈ Finset.Ico 1 D, M * (nBadB T Bt t (j - 1) : ℝ) + M * (nBadB T Bt t (D - 1) : ℝ) =
      M * ∑ j ∈ Finset.range D, (nBadB T Bt t j : ℝ) := by
    rw [← Finset.mul_sum, ← mul_add]
    congr 1
    obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    rw [Finset.sum_range_succ, show D' + 1 - 1 = D' by omega]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range, show D' + 1 - 1 = D' by omega]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 2; omega
  linarith

end Generic

section DZ

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ)
  (ℓr : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ)

/-- **P0186's coupling hypothesis holds for P0176's per-thread process**: the actual run is the entry-order run, and
an unsampled copy's own run is its forced copy-last run. -/
theorem coup_dz (z : ℕ → Fin B → Pool.P0176.RT D sl) {c : ι} {ωs : ι → Bool} (hc : ωs c = false)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) :
    Coup E thr0 θ R K D Lv Bt lev (Pool.P0176.dzUpd D Lv sl B Bm xr ℓr rh (Pool.P0176.sortLay sl) z) ∅
      (fun c' => Pool.P0176.dzUpd D Lv sl B Bm xr ℓr rh (Pool.P0176.lastLay sl c') z) (fun _ => ∅) ωs φ c := by
  intro a
  have h1 := Pool.P0176.dz_forced_erase Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev z hc φ a
  have h2 := Pool.P0176.dz_free_eq Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev z hc φ a
  refine ⟨fun r ℓ => ?_, fun x hx t => ?_⟩
  · have := h1.1 r ℓ; rw [h2] at this; exact this
  · have := h1.2.1 x hx t; rw [h2] at this; exact this

open Classical in
/-- Level sums of the bad counts are the count over the product `Fin D × Fin T`. -/
theorem sum_card_filter_eq (T : ℕ) (P : ℕ → ℕ → Prop) :
    ∑ j ∈ Finset.range D, (((Finset.range T).filter fun a => P j a).card : ℝ) =
      ((Finset.univ.filter fun ja : Fin D × Fin T => P ja.1 ja.2).card : ℝ) := by
  simp only [Finset.card_filter, Nat.cast_sum]
  rw [Fintype.sum_prod_type, ← Fin.sum_univ_eq_sum_range (fun j => ∑ a ∈ Finset.range T, ((if P j a then 1 else 0 : ℕ) : ℝ))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun a => ((if P j a then 1 else 0 : ℕ) : ℝ))]

attribute [local instance] Pool.P0082.coinFintype

open Pool.P0176 Pool.P0082 in
/-- **Expected walk right-hand side of the per-thread process.** Over P0091/P0082's coin array (any weights `p` in
`[0,1]`) and independent rounds (`wU`, summing to `1`), if every level weight is at most `M` then the expectation of
the right-hand side of P0186's `run_bound_mix` (comparator copies `cstar`, mixed outcomes of `dzRun`: entry-order
actual run, forced copy-last runs) is at most `T·a 0 + M·Kb`, for any bound `Kb` on P0185's expected bad count. -/
theorem exp_walkRHS_DZ {NE Lt : ℕ} (w0 : ℝ) (hw0 : 0 ≤ w0) (hx0 : ∀ j, 0 ≤ xr j)
    (hw1 : ∑ zc : Fin B → RT D sl, wU sl B xr w0 zc = 1) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < D → Bt j ∣ a → a < NE → E (cstar j a) = a) (hD : 0 < D)
    (p : SlotC NE D Lt K × ι → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (a : ℕ → ℝ) (c M Kb : ℝ) (hM0 : 0 ≤ M)
    (hMa : ∀ j, 1 ≤ j → j < D → (Bt (j - 1) : ℝ) * a j ≤ M) (hMc : c ≤ M)
    (hcount : ∑ ω, Pool.P0048.wtv p ω * ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
      (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl (cstar ja.1 ja.2))
          (extZ sl B yy)) ∅ (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ) ≤ Kb) :
    ∑ ω, Pool.P0048.wtv p ω * ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
      (NE * a 0 + ∑ j ∈ Finset.Ico 1 D, (Bt (j - 1) : ℝ) *
          (nBadB NE Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) (extZ sl B yy))
            ∅ (fun c' => dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl c') (extZ sl B yy)) (fun _ => ∅) (D - 1) NE
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (cstar r τ)) (j - 1) : ℝ) * a j +
        (nBadB NE Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) (extZ sl B yy))
            ∅ (fun c' => dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl c') (extZ sl B yy)) (fun _ => ∅) (D - 1) NE
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (cstar r τ)) (D - 1) : ℝ) * c) ≤
      NE * a 0 + M * Kb := by
  classical
  have hw : ∀ ω, 0 ≤ Pool.P0048.wtv p ω := fun ω => Pool.P0048.wtv_nonneg hp0 hp1 ω
  have hwR : ∀ yy : Fin NE → Fin B → RT D sl, 0 ≤ Pool.P0070.wR (wU sl B xr w0) yy :=
    fun yy => Pool.P0185.wR_nonneg_U D sl B xr w0 hw0 hx0 yy
  have hsw : ∑ ω, Pool.P0048.wtv p ω = 1 := Pool.P0048.sum_wtv p
  have hsR : ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy = 1 :=
    Pool.P0097.sum_wR _ hw1 NE
  set CNT : (SlotC NE D Lt K × ι → Bool) → (Fin NE → Fin B → RT D sl) → ℝ := fun ω yy =>
    (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl (cstar ja.1 ja.2))
          (extZ sl B yy)) ∅ (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ) with hCNT
  have hpt : ∀ ω yy, (NE * a 0 + ∑ j ∈ Finset.Ico 1 D, (Bt (j - 1) : ℝ) *
          (nBadB NE Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) (extZ sl B yy))
            ∅ (fun c' => dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl c') (extZ sl B yy)) (fun _ => ∅) (D - 1) NE
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (cstar r τ)) (j - 1) : ℝ) * a j +
        (nBadB NE Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) (extZ sl B yy))
            ∅ (fun c' => dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl c') (extZ sl B yy)) (fun _ => ∅) (D - 1) NE
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (cstar r τ)) (D - 1) : ℝ) * c) ≤ NE * a 0 + M * CNT ω yy := by
    intro ω yy
    refine (walkRHS_le (T := NE) _ a c M hM0 hMa hMc hD).trans ?_
    have hle : ∑ j ∈ Finset.range D, (nBadB NE Bt (fun τ r => outMix E thr0 θ R K D Lv Bt lev
        (dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) (extZ sl B yy)) ∅
        (fun c' => dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl c') (extZ sl B yy)) (fun _ => ∅) (D - 1) NE
        (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (cstar r τ)) j : ℝ) ≤ CNT ω yy := by
      have hsum := sum_card_filter_eq (D := D) NE (fun j a => Bt j ∣ a ∧ ωsC E NE D Lt K ω (cstar j a) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl (cstar j a))
          (extZ sl B yy)) ∅ (forceS (ωsC E NE D Lt K ω) (cstar j a)) (forceF K (φC NE D Lt K ω) (cstar j a)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) j a = none)
      refine (Finset.sum_le_sum fun j hj => ?_).trans (le_of_eq (hsum.trans ?_))
      · have := nBadB_le (E := E) (thr0 := thr0) (θ := θ) (R := R) (K := K) (Lv := Lv) (lev := lev)
          (upd := dzUpd D Lv sl B Bm xr ℓr rh (sortLay sl) (extZ sl B yy)) (aux0 := ∅)
          (U := fun c' => dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl c') (extZ sl B yy)) (A0 := fun _ => ∅)
          (T := NE) (ωs := ωsC E NE D Lt K ω) (φ := φC NE D Lt K ω) cstar hE (Finset.mem_range.1 hj)
        refine Nat.cast_le.mpr (this.trans_eq ?_)
        congr 1; ext a; simp only [Finset.mem_filter]
      · rw [hCNT]
        beta_reduce
        congr 2; ext ja; simp only [Finset.mem_filter]
    have := mul_le_mul_of_nonneg_left hle hM0
    linarith
  calc _ ≤ ∑ ω, Pool.P0048.wtv p ω * ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
        (NE * a 0 + M * CNT ω yy) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hw ω)
        exact Finset.sum_le_sum fun yy _ => mul_le_mul_of_nonneg_left (hpt ω yy) (hwR yy)
    _ = NE * a 0 + M * ∑ ω, Pool.P0048.wtv p ω * ∑ yy : Fin NE → Fin B → RT D sl,
        Pool.P0070.wR (wU sl B xr w0) yy * CNT ω yy := by
        have hin : ∀ ω, ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy *
            (NE * a 0 + M * CNT ω yy) = NE * a 0 + M * ∑ yy : Fin NE → Fin B → RT D sl,
              Pool.P0070.wR (wU sl B xr w0) yy * CNT ω yy := by
          intro ω
          have h : ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy * (NE * a 0 + M * CNT ω yy) =
              (∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy) * (NE * a 0) +
                M * ∑ yy : Fin NE → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) yy * CNT ω yy := by
            rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun yy _ => by ring
          rw [h, hsR, one_mul]
        simp only [hin]
        have h : ∑ ω, Pool.P0048.wtv p ω * (NE * a 0 + M * ∑ yy : Fin NE → Fin B → RT D sl,
              Pool.P0070.wR (wU sl B xr w0) yy * CNT ω yy) =
            (∑ ω, Pool.P0048.wtv p ω) * (NE * a 0) + M * ∑ ω, Pool.P0048.wtv p ω * ∑ yy : Fin NE → Fin B → RT D sl,
              Pool.P0070.wR (wU sl B xr w0) yy * CNT ω yy := by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun ω _ => by ring
        rw [h, hsw, one_mul]
    _ ≤ NE * a 0 + M * Kb := by
        have := mul_le_mul_of_nonneg_left hcount hM0
        linarith

end DZ

end Pool.P0197
