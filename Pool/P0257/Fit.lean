import Pool.P0218.RecUp
import Pool.P0221.Overflow
import Pool.P0228.ExpD

/-!
# Forced runs fit whenever the actual run keeps one free slot per thread

P0218's `hup_rec` (and the walk line built on it) needs, for every UNSAMPLED comparator copy `c`, that `c`'s forced
run (P0218's `PL c`: layout `lastLay c`, bits `forceS ωs c`, `forceF φ c`) fits at every round before `T` (`hfF`),
besides the actual run fitting (`hfA`, P0228's `Fits` event). This file bounds both at once.

* `fits_forced` (pathwise): with `P.lay = sortLay`, if every thread of the actual run has a free slot at round `u`
  (`|block| + 1 ≤ sl`), every unsampled copy's forced run fits at `u`. Proof: P0185's `Vblk_forced_card_le` (a forced
  run's blocks exceed the actual run's by at most one), with rule (b″) layout-independent (P0218's `rhD_PL`).
* `sp_eq_pre`: P0194's start pools on an extended prefix are P0207's prefix run (rule `rhXR`, slot coins `zE`).
* `FitAll`: actual run fits and every unsampled copy's forced run fits, at every round `< T`.
* `fitAll_of_goodAD`: P0185's `GoodAD` (prefix run, horizon `T`) implies `FitAll`.
* **`sum_not_fitAll_le`**: averaged over P0091's sampling/filter law and P0194's round coins,
  `P(¬FitAll) ≤ T·D·δs + T·D·(Lt+1)·K·delta` (the bound of P0221's `sum_ovf_le`), under P0185's hypotheses.
* `sum_not_le_of_imp`: any event implied by `FitAll` (e.g. P0228's `Fits` event alone, or `hfF` alone) has
  averaged failure probability at most that of `FitAll`.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065

namespace Pool.P0257

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι)

/-- **Pathwise.** With the entry-order layout, if at round `u` every thread of the actual run keeps a free slot, then
the forced run of every unsampled copy `c` (P0218's `PL c` with the forced bits) fits at round `u`. -/
theorem fits_forced (hlay : P.lay = sortLay P.sl) (ℓ : LossSeq n) (ω : ℕ → RC P) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) {c : ι} (hc : ωs c = false) (u : ℕ)
    (hblk : ∀ j : Fin P.D, (blockMem P.Lv (sp P ℓ ω ωs φ u) j).card + 1 ≤ P.sl j) :
    Fits P.Lv P.sl (sp (Pool.P0218.PL P c) ℓ ω (forceS ωs c) (forceF P.K φ c) u) := by
  intro j
  have h := Pool.P0185.Vblk_forced_card_le P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev P.sl 1 1 P.xr (ℓr P ℓ)
    (rhD P ℓ ω) hc φ (zc P ω) u j
  have hj := hblk j
  unfold sp pool at hj ⊢
  rw [Pool.P0218.rhD_PL P ℓ ω c]
  rw [hlay] at hj
  change (blockMem P.Lv (startPools P.E P.thr0 P.D P.Lv P.Bt (forceS ωs c) u
    (dzRun P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.E P.thr0 P.θ P.R P.K P.Bt P.lev (lastLay P.sl c) (zc P ω)
      (forceS ωs c) (forceF P.K φ c) u).pools) j).card ≤ P.sl j
  omega

/-- The actual run's start pools on an extended prefix are P0207's prefix run (rule `rhXR`, slot coins `zE`). -/
theorem sp_eq_pre (hlay : P.lay = sortLay P.sl) {T : ℕ} (ℓ : LossSeq n) (rc₀ : RC P) (rc : Fin T → RC P)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (u : ℕ) (hu : u ≤ T) :
    sp P ℓ (Pool.P0210.extR P rc₀ rc) ωs φ u =
      startPools P.E P.thr0 P.D P.Lv P.Bt ωs u
        (dzRun P.Lv P.sl 1 1 P.xr (ℓr P ℓ)
          (Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none rc)) P.E P.thr0 P.θ P.R P.K
          P.Bt P.lev (sortLay P.sl) (Pool.P0200.zE P.sl 1 (Pool.P0207.zOfR P) rc) ωs φ u).pools := by
  have hext : Pool.P0210.extR P rc₀ rc = Pool.P0207.extω P rc₀ rc := rfl
  unfold sp
  rw [hext, Pool.P0207.pool_eq P ℓ ωs φ rc₀ rc u hu, hlay]

/-- The joint fitting event on a coin prefix: the actual run and the forced run of every unsampled copy fit at
every round before `T`. -/
def FitAll (T : ℕ) (ℓ : LossSeq n) (rc₀ : RC P) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
    (rc : Fin T → RC P) : Prop :=
  (∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ rc) ωs φ t)) ∧
    ∀ c, ωs c = false → ∀ t < T,
      Fits P.Lv P.sl (sp (Pool.P0218.PL P c) ℓ (Pool.P0210.extR P rc₀ rc) (forceS ωs c) (forceF P.K φ c) t)

/-- **P0185's good event implies the joint fitting event** (pathwise, entry-order layout). -/
theorem fitAll_of_goodAD (hlay : P.lay = sortLay P.sl) {T : ℕ} (ℓ : LossSeq n) (rc₀ : RC P) (rc : Fin T → RC P)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (S : ℕ)
    (hG : Pool.P0185.GoodAD P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev P.sl 1 1 P.xr (ℓr P ℓ)
      (Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none rc)) T S ωs φ
      (Pool.P0200.zE P.sl 1 (Pool.P0207.zOfR P) rc)) :
    FitAll P T ℓ rc₀ ωs φ rc := by
  have hblk : ∀ t < T, ∀ j : Fin P.D,
      (blockMem P.Lv (sp P ℓ (Pool.P0210.extR P rc₀ rc) ωs φ t) j).card + 1 ≤ P.sl j := by
    intro t ht j
    rw [sp_eq_pre P hlay ℓ rc₀ rc ωs φ t ht.le]
    exact hG.1 t ht j
  refine ⟨fun t ht j => ?_, fun c hc t ht => fits_forced P hlay ℓ _ ωs φ hc t (hblk t ht)⟩
  have := hblk t ht j
  omega

section Prob

attribute [local instance] Pool.P0082.coinFintype

open Classical in
/-- **The joint overflow probability (actual run and all forced runs) is at most P0109's failure bound**, averaged
over P0091's sampling/filter law: for every loss sequence, with P0185's hypotheses at horizon `NE = T`,
`E_arr[P_rc(¬FitAll)] ≤ T·D·δs + T·D·(Lt+1)·K·delta(|ι|, q, R, kk, M0)`. -/
theorem sum_not_fitAll_le (hlay : P.lay = sortLay P.sl) (hL : P.IsLaw) (hN : 0 < P.N) {T Lt : ℕ}
    (ℓ : LossSeq n) (rc₀ : RC P) {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hE : Monotone P.E) (hB : BtHyp P.D P.Bt) (hLv : 0 < P.Lv)
    (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ P.xr j) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hR : 1 ≤ P.R) (hT : 1 / xmin * T ≤ 2 ^ (P.R - 1) * P.θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * P.R ≤ M0)
    (hk : 4 * P.R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * P.R))
    (hlevLt : ∀ a < T, ∀ r < P.D, P.lev r a ≤ Lt) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < T → r < P.D →
      ∑ F ∈ (Finset.univ.filter fun c => P.E c = a ∧ P.thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => P.E c = a ∧ P.thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S')
    (hρS : (1 - 1 / (4 * P.R : ℝ)) ^ P.K * ((S' : ℝ) + (s0 + P.D * P.Lv * S')) ≤ S')
    (hsl : ∀ j, (P.D : ℝ) * ((s0 + P.D * P.Lv * S') + (P.Lv - 1 : ℕ) * S') + P.D * s0 + 1 ≤ P.sl j) :
    ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
      ∑ rc : Fin T → RC P, Pool.P0202.pw (wR P) rc *
        (if FitAll P T ℓ rc₀ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc
          then 0 else 1) ≤
      T * P.D * δs + T * P.D * (Lt + 1) * P.K * Pool.P0042.delta (Fintype.card ι) q P.R kk M0 := by
  have hw0 : ∀ ω2 : Pool.P0082.SlotC T P.D Lt P.K × ι → Bool,
      0 ≤ Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 := by
    intro ω2
    refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) ω2
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [hps.1, hq0]
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [hps.2, hq1]
  have h1 : ∑ rc, wR P rc = 1 := sum_wR P hL hN
  have hrc : ∀ rc : Fin T → RC P, ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
      (if FitAll P T ℓ rc₀ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc then 0 else 1) ≤
      T * P.D * δs + T * P.D * (Lt + 1) * P.K * Pool.P0042.delta (Fintype.card ι) q P.R kk M0 := by
    intro rc
    have hBm' : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) / xmin := by rw [Nat.cast_one]; exact hBm
    have hT' : ((1 : ℕ) : ℝ) / xmin * T ≤ 2 ^ (P.R - 1) * P.θ := by rw [Nat.cast_one]; exact hT
    have hP := Pool.P0185.prob_notGoodAD_le (NE := T) (Lt := Lt) P.E P.thr0 P.θ P.R P.K P.D P.Lv
      P.Bt P.lev P.sl 1 1 P.xr
      (ℓr P ℓ) (Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none rc)) hps
      hq0 hq1 hE hB hLv hlev hxmin hx (fun u x => (Pool.P0207.ℓr_mem P ℓ u x).1)
      (fun u x => (Pool.P0207.ℓr_mem P ℓ u x).2) zero_le_one hBm' hR hT'
      M0 kk hM0 hk hp hlevLt s0 δs hs S' hM0S hρS hsl (Pool.P0200.zE P.sl 1 (Pool.P0207.zOfR P) rc)
    refine le_trans (Finset.sum_le_sum fun ω2 _ => mul_le_mul_of_nonneg_left ?_ (hw0 ω2)) hP
    by_cases hG : Pool.P0185.GoodAD P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev P.sl 1 1 P.xr
      (ℓr P ℓ) (Pool.P0207.rhXR P ℓ (Pool.P0200.extE (Pool.P0207.extR P) none rc)) T
      (s0 + P.D * P.Lv * S' + 1)
      (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2)
      (Pool.P0200.zE P.sl 1 (Pool.P0207.zOfR P) rc)
    · rw [if_pos (fitAll_of_goodAD P hlay ℓ rc₀ rc _ _ _ hG), if_pos hG]
    · rw [if_neg hG]; split_ifs <;> norm_num
  calc ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
        ∑ rc : Fin T → RC P, Pool.P0202.pw (wR P) rc *
          (if FitAll P T ℓ rc₀ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc
            then 0 else 1)
      = ∑ rc : Fin T → RC P, Pool.P0202.pw (wR P) rc *
          ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
            (if FitAll P T ℓ rc₀ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc
              then 0 else 1) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ rc : Fin T → RC P, Pool.P0202.pw (wR P) rc *
          (T * P.D * δs + T * P.D * (Lt + 1) * P.K * Pool.P0042.delta (Fintype.card ι) q P.R kk M0) :=
        Finset.sum_le_sum fun rc _ => mul_le_mul_of_nonneg_left (hrc rc)
          (Finset.prod_nonneg fun j _ => wR_nonneg P hL _)
    _ = _ := by rw [← Finset.sum_mul, Pool.P0202.sum_pw_one h1 T, one_mul]

open Classical in
/-- Any event implied by `FitAll` on every prefix fails with at most `FitAll`'s averaged probability. -/
theorem sum_not_le_of_imp {T Lt : ℕ} (ℓ : LossSeq n) (rc₀ : RC P) (hL : P.IsLaw) {ps q : ℝ}
    (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (G : (ι → Bool) → (ℕ → ℕ → ℕ → Fin P.K → ι → Bool) → (Fin T → RC P) → Prop)
    (hG : ∀ ωs φ rc, FitAll P T ℓ rc₀ ωs φ rc → G ωs φ rc) :
    ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
      ∑ rc : Fin T → RC P, Pool.P0202.pw (wR P) rc *
        (if G (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc then 0 else 1) ≤
    ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω2 *
      ∑ rc : Fin T → RC P, Pool.P0202.pw (wR P) rc *
        (if FitAll P T ℓ rc₀ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc
          then 0 else 1) := by
  refine Finset.sum_le_sum fun ω2 _ => mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun rc _ => mul_le_mul_of_nonneg_left ?_
      (Finset.prod_nonneg fun j _ => wR_nonneg P hL _)) ?_
  · by_cases hF : FitAll P T ℓ rc₀ (Pool.P0082.ωsC P.E T P.D Lt P.K ω2) (Pool.P0082.φC T P.D Lt P.K ω2) rc
    · rw [if_pos (hG _ _ _ hF), if_pos hF]
    · rw [if_neg hF]; split_ifs <;> norm_num
  · refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) ω2
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [hps.1, hq0]
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [hps.2, hq1]

end Prob

end Pool.P0257
