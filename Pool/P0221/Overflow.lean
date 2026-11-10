import Pool.P0217.Regret
import Pool.P0207.Round

/-!
# The overflow term `ovf` of P0217, bounded by P0185's not-good probability (entry-order layout)
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0201 Pool.P0206 Pool.P0194 Pool.P0214 Pool.P0217

namespace Pool.P0221

section WithDec

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {m : MPar n ι}

attribute [local instance] finSeqYZ finSeqJ Pool.P0082.coinFintype

omit [DecidableEq ι] in
/-- P0194's start pools on the extended prefix are those of P0207's entry-order run (layout `sortLay`). -/
theorem sp_eq_sort (hlay : m.P.lay = Pool.P0176.sortLay m.P.sl) {T : ℕ} (ℓ : LossSeq n) (rc₀ : RC m.P)
    (rc : Fin T → RC m.P) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin m.P.K → ι → Bool) (u : ℕ) (hu : u ≤ T) :
    sp m.P ℓ (extRC m T rc₀ rc) ωs φ u =
      Pool.P0065.startPools m.P.E m.P.thr0 m.P.D m.P.Lv m.P.Bt ωs u
        (Pool.P0176.dzRun m.P.Lv m.P.sl 1 1 m.P.xr (ℓr m.P ℓ)
          (Pool.P0207.rhXR m.P ℓ (Pool.P0200.extE (Pool.P0207.extR m.P) none rc)) m.P.E m.P.thr0 m.P.θ m.P.R m.P.K
          m.P.Bt m.P.lev (Pool.P0176.sortLay m.P.sl) (Pool.P0200.zE m.P.sl 1 (Pool.P0207.zOfR m.P) rc) ωs φ u).pools := by
  unfold sp
  rw [show extRC m T rc₀ rc = Pool.P0207.extω m.P rc₀ rc from rfl, Pool.P0207.pool_eq m.P ℓ ωs φ rc₀ rc u hu, hlay]

open Classical in
/-- **Good runs do not overflow.** With the entry-order layout and `Σ_j sl_j ≤ Ns`, if P0185's `GoodAD` holds for the
run with P0207's prefix rule and slot coins (horizon `T`), then every start pool before `T` fits. -/
theorem fitP_of_goodAD (hlay : m.P.lay = Pool.P0176.sortLay m.P.sl) (hcap : ∑ j, m.P.sl j ≤ m.Ns) {T : ℕ}
    (ℓ : LossSeq n) (rc₀ : RC m.P) (rc : Fin T → RC m.P) (arr : Pool.P0116.Arr (pp m) T → Bool) (S : ℕ)
    (hG : Pool.P0185.GoodAD m.P.E m.P.thr0 m.P.θ m.P.R m.P.K m.P.D m.P.Lv m.P.Bt m.P.lev m.P.sl 1 1 m.P.xr
      (ℓr m.P (sh ℓ)) (Pool.P0207.rhXR m.P (sh ℓ) (Pool.P0200.extE (Pool.P0207.extR m.P) none rc)) T S
      (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr)
      (Pool.P0200.zE m.P.sl 1 (Pool.P0207.zOfR m.P) rc)) :
    FitP m T ℓ rc₀ rc arr := by
  refine fitP_of_blocks ℓ rc₀ rc arr (fun v hv j => ?_) hcap
  rw [sp_eq_sort hlay (sh ℓ) rc₀ rc _ _ v hv.le]
  exact hG.1 v hv j

end WithDec

section Prob

variable {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] {m : MPar n ι}

attribute [local instance] Pool.P0082.coinFintype

open Classical in
/-- **The overflow term is at most P0109's failure probability** (entry-order layout, `Σ_j sl_j ≤ Ns`, and P0185's
hypotheses at horizon `NE = T`, `Lt = Lf`, `B = Bm = 1`):
`E_arr[ovf] ≤ T·D·δs + T·D·(Lf+1)·K·delta`. -/
theorem sum_ovf_le (hlay : m.P.lay = Pool.P0176.sortLay m.P.sl) (hcap : ∑ j, m.P.sl j ≤ m.Ns) {T : ℕ}
    (ℓ : LossSeq n) (rc₀ : RC m.P) (hL : m.P.IsLaw) (hN : 0 < m.P.N)
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
    (hsl : ∀ j, (m.P.D : ℝ) * ((s0 + m.P.D * m.P.Lv * S') + (m.P.Lv - 1 : ℕ) * S') + m.P.D * s0 + 1 ≤ m.P.sl j) :
    ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * ovf m T ℓ rc₀ arr ≤
      T * m.P.D * δs + T * m.P.D * (m.Lf + 1) * m.P.K * Pool.P0042.delta (Fintype.card ι) m.q m.P.R kk M0 := by
  have hw0 : ∀ arr : Pool.P0116.Arr (pp m) T → Bool, 0 ≤ Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr := by
    intro arr
    refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) arr
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [m.hps.1, m.hq.1]
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [m.hps.2, m.hq.2]
  have h1 : ∑ rc, wR m.P rc = 1 := sum_wR m.P hL hN
  -- for every fixed round-coin prefix, the array probability of overflow is at most Pbad
  have hrc : ∀ rc : Fin T → RC m.P, ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
      (if FitP m T ℓ rc₀ rc arr then 0 else 1) ≤
      T * m.P.D * δs + T * m.P.D * (m.Lf + 1) * m.P.K * Pool.P0042.delta (Fintype.card ι) m.q m.P.R kk M0 := by
    intro rc
    have hBm' : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) / xmin := by rw [Nat.cast_one]; exact hBm
    have hT' : ((1 : ℕ) : ℝ) / xmin * T ≤ 2 ^ (m.P.R - 1) * m.P.θ := by rw [Nat.cast_one]; exact hT
    have hP := Pool.P0185.prob_notGoodAD_le (NE := T) (Lt := m.Lf) m.P.E m.P.thr0 m.P.θ m.P.R m.P.K m.P.D m.P.Lv
      m.P.Bt m.P.lev m.P.sl 1 1 m.P.xr
      (ℓr m.P (sh ℓ)) (Pool.P0207.rhXR m.P (sh ℓ) (Pool.P0200.extE (Pool.P0207.extR m.P) none rc)) m.hps
      m.hq.1 m.hq.2 hE hB hLv hlev hxmin hx (fun u x => (Pool.P0207.ℓr_mem m.P (sh ℓ) u x).1)
      (fun u x => (Pool.P0207.ℓr_mem m.P (sh ℓ) u x).2) zero_le_one hBm' hR hT'
      M0 kk hM0 hk hp hlevLt s0 δs hs S' hM0S hρS hsl (Pool.P0200.zE m.P.sl 1 (Pool.P0207.zOfR m.P) rc)
    refine le_trans (Finset.sum_le_sum fun arr _ => mul_le_mul_of_nonneg_left ?_ (hw0 arr)) hP
    by_cases hG : Pool.P0185.GoodAD m.P.E m.P.thr0 m.P.θ m.P.R m.P.K m.P.D m.P.Lv m.P.Bt m.P.lev m.P.sl 1 1 m.P.xr
      (ℓr m.P (sh ℓ)) (Pool.P0207.rhXR m.P (sh ℓ) (Pool.P0200.extE (Pool.P0207.extR m.P) none rc)) T
      (s0 + m.P.D * m.P.Lv * S' + 1)
      (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr)
      (Pool.P0200.zE m.P.sl 1 (Pool.P0207.zOfR m.P) rc)
    · rw [if_pos (fitP_of_goodAD hlay hcap ℓ rc₀ rc arr _ hG), if_pos hG]
    · rw [if_neg hG]; split_ifs <;> norm_num
  unfold ovf
  calc ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
        ∑ rc : Fin T → RC m.P, Pool.P0202.pw (wR m.P) rc * (if FitP m T ℓ rc₀ rc arr then 0 else 1)
      = ∑ rc : Fin T → RC m.P, Pool.P0202.pw (wR m.P) rc *
          ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * (if FitP m T ℓ rc₀ rc arr then 0 else 1) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ rc : Fin T → RC m.P, Pool.P0202.pw (wR m.P) rc *
          (T * m.P.D * δs + T * m.P.D * (m.Lf + 1) * m.P.K * Pool.P0042.delta (Fintype.card ι) m.q m.P.R kk M0) :=
        Finset.sum_le_sum fun rc _ => mul_le_mul_of_nonneg_left (hrc rc)
          (Finset.prod_nonneg fun j _ => wR_nonneg m.P hL _)
    _ = _ := by rw [← Finset.sum_mul, Pool.P0202.sum_pw_one h1 T, one_mul]

open Classical in
/-- **The machine's regret with BASE and overflow discharged.** P0217's `regret_le_base` with the overflow term bounded
by `sum_ovf_le` (entry-order layout, `Σ_j sl_j ≤ Ns`, P0185's hypotheses at horizon `T`): for a best arm `i`,
`regret ≤ 1 + T·(T·D·δs + T·D·(Lf+1)·K·delta) + (wB + Σ_s x_s)·regret(Sub(BASE, wB), ℓ(·+1), T) + E_arr[algT_i + slotT]`. -/
theorem regret_le_ovf [DecidableEq ι] [NeZero n] (hlay : m.P.lay = Pool.P0176.sortLay m.P.sl)
    (hcap : ∑ j, m.P.sl j ≤ m.Ns) {T : ℕ} (hI : m.Intended T) (hL : m.P.IsLaw) (hN : 0 < m.P.N)
    (ℓ : LossSeq n) (ω₀ : Yc m × Zc m) (rc₀ : RC m.P)
    (hE : Monotone m.P.E) (hB : Pool.P0065.BtHyp m.P.D m.P.Bt)
    {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ m.P.xr j) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hR : 1 ≤ m.P.R) (hT : 1 / xmin * T ≤ 2 ^ (m.P.R - 1) * m.P.θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * m.P.R ≤ M0)
    (hk : 4 * m.P.R * kk ≤ M0) (hp : m.q * (Real.exp 1 - 1) ≤ 1 / (32 * m.P.R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < T → r < m.P.D →
      ∑ F ∈ (Finset.univ.filter fun c => m.P.E c = a ∧ m.P.thr0 c = r).powerset,
        m.ps ^ F.card * (1 - m.ps) ^ ((Finset.univ.filter fun c => m.P.E c = a ∧ m.P.thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S')
    (hρS : (1 - 1 / (4 * m.P.R : ℝ)) ^ m.P.K * ((S' : ℝ) + (s0 + m.P.D * m.P.Lv * S')) ≤ S')
    (hsl : ∀ j, (m.P.D : ℝ) * ((s0 + m.P.D * m.P.Lv * S') + (m.P.Lv - 1 : ℕ) * S') + m.P.D * s0 + 1 ≤ m.P.sl j) :
    ∃ i : Fin n, bestLoss ℓ (T + 1) = cumLoss ℓ (T + 1) i ∧ regret (mach m).toMachine ℓ (T + 1) ≤
      1 + T * (T * m.P.D * δs + T * m.P.D * (m.Lf + 1) * m.P.K * Pool.P0042.delta (Fintype.card ι) m.q m.P.R kk M0) +
        (m.P.wB + ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1) *
          regret (Pool.P0055.Sub m.P.AB.toMachine m.P.wB hL.1 (Pool.P0202.wB_le_one m.P hL)) (sh ℓ) T +
        ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * (algT m T ℓ rc₀ i arr + slotT m T ℓ rc₀ arr) := by
  obtain ⟨i, hbest, hi⟩ := regret_le_base hI hL hN ℓ ω₀ rc₀
  refine ⟨i, hbest, hi.trans ?_⟩
  have hO := sum_ovf_le (m := m) hlay hcap ℓ rc₀ hL hN hE hB hI.hLv hI.hlev hxmin hx hBm hR hT M0 kk hM0 hk hp
    (fun a _ r _ => hI.hLf r a) s0 δs hs S' hM0S hρS hsl
  have hO' : ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * ovf m T ℓ rc₀ arr ≤
      T * m.P.D * δs + T * m.P.D * (m.Lf + 1) * m.P.K * Pool.P0042.delta (Fintype.card ι) m.q m.P.R kk M0 := by
    convert hO using 2
    exact Finset.ext fun x => by simp
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hO' hT0
  linarith

end Prob

end Pool.P0221
