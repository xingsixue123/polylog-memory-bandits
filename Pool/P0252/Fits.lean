import Pool.P0221.Overflow
import Pool.P0218.RecUp

/-!
# P0185's `GoodAD` gives both fit hypotheses of P0242's `run_bound_occ` (actual run and forced runs)
-/

namespace Pool.P0252

open Finset Pool.P0001 Pool.P0194

variable {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] (P : ParD n ι)

/-- The good event of P0185 (as used by P0221) for P0194's run on a coin prefix `rc` of length `T`. -/
def GoodR (ℓ : LossSeq n) (T S : ℕ) (rc : Fin T → RC P) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) :
    Prop :=
  Pool.P0185.GoodAD P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev P.sl 1 1 P.xr (ℓr P ℓ)
    (Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none rc)) T S ωs φ
    (Pool.P0200.zE P.sl 1 (Pool.P0207.zOfR P) rc)

/-- The entry-order run's pools at `u` (the run `GoodR` is about). -/
noncomputable abbrev aPools (ℓ : LossSeq n) {T : ℕ} (rc : Fin T → RC P) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (lay : (j : Fin P.D) → Finset ι → Fin (P.sl j) → Option ι) (u : ℕ) :
    ℕ → ℕ → Finset ι :=
  (Pool.P0176.dzRun P.Lv P.sl 1 1 P.xr (ℓr P ℓ)
    (Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none rc)) P.E P.thr0 P.θ P.R P.K P.Bt P.lev lay
    (Pool.P0200.zE P.sl 1 (Pool.P0207.zOfR P) rc) ωs φ u).pools

theorem sBE_PL (ℓ : LossSeq n) (c : ι) (e : ℕ → Option (Bool × P.AB.Y × P.AB.Z)) :
    ∀ u, Pool.P0207.sBE (Pool.P0218.PL P c) ℓ e u = Pool.P0207.sBE P ℓ e u
  | 0 => rfl
  | u + 1 => by
    simp only [Pool.P0207.sBE]; rw [sBE_PL ℓ c e u]
    rcases e u with _ | ⟨b, yb, zb⟩
    · rfl
    · cases b <;> rfl

theorem BhE_PL (ℓ : LossSeq n) (c : ι) (e : ℕ → Option (Bool × P.AB.Y × P.AB.Z)) :
    ∀ u, Pool.P0207.BhE (Pool.P0218.PL P c) ℓ e u = Pool.P0207.BhE P ℓ e u
  | 0 => rfl
  | u + 1 => by
    simp only [Pool.P0207.BhE]
    rw [BhE_PL ℓ c e u, sBE_PL P ℓ c e u]
    rcases e u with _ | ⟨b, yb, zb⟩
    · rfl
    · cases b <;> rfl

theorem rhXR_PL (ℓ : LossSeq n) (c : ι) (e : ℕ → Option (Bool × P.AB.Y × P.AB.Z)) :
    Pool.P0207.rhXR (Pool.P0218.PL P c) ℓ e = Pool.P0207.rhXR P ℓ e := by
  funext u x h
  simp only [Pool.P0207.rhXR, BhE_PL P ℓ c e]
  rfl

/-- Block members grow by at most the one forced copy. -/
theorem blockMem_subset_insert {Lv : ℕ} (c : ι) (A B : ℕ → ℕ → Finset ι) (h : ∀ r ℓ, (A r ℓ).erase c = B r ℓ)
    (j : ℕ) : Pool.P0176.blockMem Lv A j ⊆ insert c (Pool.P0176.blockMem Lv B j) := by
  intro x hx
  unfold Pool.P0176.blockMem at hx ⊢
  rw [Finset.mem_biUnion] at hx
  obtain ⟨l, hl, hxl⟩ := hx
  by_cases hxc : x = c
  · exact hxc ▸ Finset.mem_insert_self _ _
  · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨l, hl, ?_⟩)
    rw [← h j l]
    exact Finset.mem_erase.2 ⟨hxc, hxl⟩

/-- **Actual run fits** on `GoodR` (entry-order layout). -/
theorem fits_actual (hlay : P.lay = Pool.P0176.sortLay P.sl) (ℓ : LossSeq n) {T S : ℕ} (rc0 : RC P)
    (rc : Fin T → RC P) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (hG : GoodR P ℓ T S rc ωs φ) :
    ∀ u < T, Pool.P0176.Fits P.Lv P.sl (sp P ℓ (Pool.P0207.extω P rc0 rc) ωs φ u) := by
  intro u hu j
  unfold sp
  rw [Pool.P0207.pool_eq P ℓ ωs φ rc0 rc u hu.le, hlay]
  have := hG.1 u hu j
  omega

/-- **Forced runs fit** on `GoodR`: for an unsampled copy `c`, the copy-last run with `c` forced in (P0218's `PL`)
has, at every unit `u < T`, at most one more block member than the actual entry-order run. -/
theorem fits_forced (ℓ : LossSeq n) {T S : ℕ} (rc0 : RC P) (rc : Fin T → RC P) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (hG : GoodR P ℓ T S rc ωs φ) (c : ι) (hc : ωs c = false) :
    ∀ u < T, Pool.P0176.Fits (Pool.P0218.PL P c).Lv (Pool.P0218.PL P c).sl
      (sp (Pool.P0218.PL P c) ℓ (Pool.P0207.extω (Pool.P0218.PL P c) rc0 rc) (Pool.P0065.forceS ωs c)
        (Pool.P0065.forceF (Pool.P0218.PL P c).K φ c) u) := by
  classical
  intro u hu j
  unfold sp
  rw [Pool.P0207.pool_eq (Pool.P0218.PL P c) ℓ (Pool.P0065.forceS ωs c) (Pool.P0065.forceF _ φ c) rc0 rc u hu.le]
  have hrh : Pool.P0207.rhXR (Pool.P0218.PL P c) ℓ (Pool.P0200.extE (Pool.P0207.extR (Pool.P0218.PL P c)) none rc) =
      Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none rc) := rhXR_PL P ℓ c _
  rw [hrh]
  -- the forced copy-last run is the actual entry-order run plus `c`
  have h1 := (Pool.P0176.dz_forced_erase P.Lv P.sl 1 1 P.xr (ℓr P ℓ)
    (Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none rc)) P.E P.thr0 P.θ P.R P.K P.Bt P.lev
    (Pool.P0200.zE P.sl 1 (Pool.P0207.zOfR P) rc) hc φ u).1
  have h2 := Pool.P0176.dz_free_eq P.Lv P.sl 1 1 P.xr (ℓr P ℓ)
    (Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none rc)) P.E P.thr0 P.θ P.R P.K P.Bt P.lev
    (Pool.P0200.zE P.sl 1 (Pool.P0207.zOfR P) rc) hc φ u
  rw [h2] at h1
  have hs : Pool.P0052.AgreeOff c (Pool.P0065.forceS ωs c) ωs := fun x hx => by
    simp [Pool.P0065.forceS, Function.update_of_ne hx]
  have hst : ∀ r l, (Pool.P0065.startPools P.E P.thr0 P.D P.Lv P.Bt (Pool.P0065.forceS ωs c) u
      (aPools P ℓ rc (Pool.P0065.forceS ωs c) (Pool.P0065.forceF P.K φ c) (Pool.P0176.lastLay P.sl c) u) r l).erase c =
      Pool.P0065.startPools P.E P.thr0 P.D P.Lv P.Bt ωs u
        (aPools P ℓ rc ωs φ (Pool.P0176.sortLay P.sl) u) r l := by
    intro r l
    rw [Pool.P0065.startPools_erase c _ ωs hs hc]
    congr 1
    funext r' l'
    exact h1 r' l'
  have hsub := blockMem_subset_insert (Lv := P.Lv) c _ _ hst j
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hg : (Pool.P0176.blockMem P.Lv (Pool.P0065.startPools P.E P.thr0 P.D P.Lv P.Bt ωs u
      (aPools P ℓ rc ωs φ (Pool.P0176.sortLay P.sl) u)) j).card + 1 ≤ P.sl j := hG.1 u hu j
  have hfin := hcard.trans hg
  exact hfin

section Prob

open Pool.P0201 Pool.P0217

variable {m : MPar n ι}

attribute [local instance] Pool.P0082.coinFintype

/-- Both fit events of P0242's `run_bound_occ` (`hfit` and `hfF`) for the run of `m.P` on the prefix `rc` with the
array's sampling/filter bits. -/
def FitsAll (m : MPar n ι) (T : ℕ) (ℓ : LossSeq n) (rc0 : RC m.P) (rc : Fin T → RC m.P)
    (arr : Pool.P0116.Arr (pp m) T → Bool) : Prop :=
  (∀ u < T, Pool.P0176.Fits m.P.Lv m.P.sl (sp m.P ℓ (Pool.P0207.extω m.P rc0 rc)
      (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) u)) ∧
  ∀ c, Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr c = false → ∀ u < T,
    Pool.P0176.Fits (Pool.P0218.PL m.P c).Lv (Pool.P0218.PL m.P c).sl
      (sp (Pool.P0218.PL m.P c) ℓ (Pool.P0207.extω (Pool.P0218.PL m.P c) rc0 rc)
        (Pool.P0065.forceS (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) c)
        (Pool.P0065.forceF (Pool.P0218.PL m.P c).K (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) c) u)

open Classical in
/-- **The fit events of `run_bound_occ` fail with array probability at most P0221's overflow bound**, for every fixed
round-coin prefix (entry-order layout; P0185/P0221's hypotheses at horizon `T`). -/
theorem prob_not_fitsAll (hlay : m.P.lay = Pool.P0176.sortLay m.P.sl) {T : ℕ} (ℓ : LossSeq n) (rc₀ : RC m.P)
    (hE : Monotone m.P.E) (hB : Pool.P0065.BtHyp m.P.D m.P.Bt) (hLv : 0 < m.P.Lv)
    (hlev : ∀ r a, m.P.lev r a + 1 < m.P.Lv)
    {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ m.P.xr j) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hR : 1 ≤ m.P.R) (hT : 1 / xmin * T ≤ 2 ^ (m.P.R - 1) * m.P.θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * m.P.R ≤ M0)
    (hk : 4 * m.P.R * kk ≤ M0) (hp : m.q * (Real.exp 1 - 1) ≤ 1 / (32 * m.P.R))
    (hlevLt : ∀ a < T, ∀ r < m.P.D, m.P.lev r a ≤ m.Lf) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < T → r < m.P.D →
      ∑ F ∈ (Finset.univ.filter fun c => m.P.E c = a ∧ m.P.thr0 c = r).powerset,
        m.ps ^ F.card * (1 - m.ps) ^ ((Finset.univ.filter fun c => m.P.E c = a ∧ m.P.thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S')
    (hρS : (1 - 1 / (4 * m.P.R : ℝ)) ^ m.P.K * ((S' : ℝ) + (s0 + m.P.D * m.P.Lv * S')) ≤ S')
    (hsl : ∀ j, (m.P.D : ℝ) * ((s0 + m.P.D * m.P.Lv * S') + (m.P.Lv - 1 : ℕ) * S') + m.P.D * s0 + 1 ≤ m.P.sl j)
    (rc : Fin T → RC m.P) :
    ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * (if FitsAll m T ℓ rc₀ rc arr then 0 else 1) ≤
      T * m.P.D * δs + T * m.P.D * (m.Lf + 1) * m.P.K * Pool.P0042.delta (Fintype.card ι) m.q m.P.R kk M0 := by
  have hw0 : ∀ arr : Pool.P0116.Arr (pp m) T → Bool, 0 ≤ Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr := by
    intro arr
    refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) arr
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [m.hps.1, m.hq.1]
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [m.hps.2, m.hq.2]
  have hBm' : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) / xmin := by rw [Nat.cast_one]; exact hBm
  have hT' : ((1 : ℕ) : ℝ) / xmin * T ≤ 2 ^ (m.P.R - 1) * m.P.θ := by rw [Nat.cast_one]; exact hT
  have hP := Pool.P0185.prob_notGoodAD_le (NE := T) (Lt := m.Lf) m.P.E m.P.thr0 m.P.θ m.P.R m.P.K m.P.D m.P.Lv
    m.P.Bt m.P.lev m.P.sl 1 1 m.P.xr
    (ℓr m.P ℓ) (Pool.P0207.rhXR m.P ℓ (Pool.P0200.extE (Pool.P0207.extR m.P) none rc)) m.hps
    m.hq.1 m.hq.2 hE hB hLv hlev hxmin hx (fun u x => (Pool.P0207.ℓr_mem m.P ℓ u x).1)
    (fun u x => (Pool.P0207.ℓr_mem m.P ℓ u x).2) zero_le_one hBm' hR hT'
    M0 kk hM0 hk hp hlevLt s0 δs hs S' hM0S hρS hsl (Pool.P0200.zE m.P.sl 1 (Pool.P0207.zOfR m.P) rc)
  refine le_trans (Finset.sum_le_sum fun arr _ => mul_le_mul_of_nonneg_left ?_ (hw0 arr)) hP
  by_cases hG : Pool.P0185.GoodAD m.P.E m.P.thr0 m.P.θ m.P.R m.P.K m.P.D m.P.Lv m.P.Bt m.P.lev m.P.sl 1 1 m.P.xr
    (ℓr m.P ℓ) (Pool.P0207.rhXR m.P ℓ (Pool.P0200.extE (Pool.P0207.extR m.P) none rc)) T
    (s0 + m.P.D * m.P.Lv * S' + 1)
    (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr)
    (Pool.P0200.zE m.P.sl 1 (Pool.P0207.zOfR m.P) rc)
  · have hfa : FitsAll m T ℓ rc₀ rc arr :=
      ⟨fits_actual m.P hlay ℓ rc₀ rc _ _ hG, fun c hc => fits_forced m.P ℓ rc₀ rc _ _ hG c hc⟩
    rw [if_pos hfa, if_pos hG]
  · rw [if_neg hG]; split_ifs <;> norm_num

end Prob

end Pool.P0252
