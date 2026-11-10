import Pool.P0221.Overflow
import Pool.P0217.Regret

/-!
# The per-thread fit probability in P0234's `badTerm` and P0246's `badTermP`, bounded by P0185's not-good probability

P0234's `badTerm` and P0246's `badTermP` contain `P(some thread does not fit before T)` (P0176's `Fits`, per thread: block members
`≤ sl j`), a different event from P0217's `ovf` (total members `≤ Ns`). P0185's `GoodAD` gives both (each block has a
free slot), so P0221's argument bounds the array average of the fit failure by the same `T·D·δs + T·D·(Lf+1)·K·delta`.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0201 Pool.P0206 Pool.P0194 Pool.P0214 Pool.P0217

namespace Pool.P0251

variable {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι] {m : MPar n ι}

attribute [local instance] Pool.P0082.coinFintype

open Classical in
/-- **Good runs fit in every thread.** With the entry-order layout, if P0185's `GoodAD` holds for the run with
P0207's prefix rule and slot coins (horizon `T`), then every thread fits at every round before `T`. -/
theorem fits_of_goodAD (hlay : m.P.lay = Pool.P0176.sortLay m.P.sl) {T : ℕ}
    (ℓ : LossSeq n) (rc₀ : RC m.P) (rc : Fin T → RC m.P) (arr : Pool.P0116.Arr (pp m) T → Bool) (S : ℕ)
    (hG : Pool.P0185.GoodAD m.P.E m.P.thr0 m.P.θ m.P.R m.P.K m.P.D m.P.Lv m.P.Bt m.P.lev m.P.sl 1 1 m.P.xr
      (ℓr m.P (sh ℓ)) (Pool.P0207.rhXR m.P (sh ℓ) (Pool.P0200.extE (Pool.P0207.extR m.P) none rc)) T S
      (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr)
      (Pool.P0200.zE m.P.sl 1 (Pool.P0207.zOfR m.P) rc)) :
    ∀ t < T, Pool.P0176.Fits m.P.Lv m.P.sl (sp m.P (sh ℓ) (Pool.P0210.extR m.P rc₀ rc)
      (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) t) := by
  intro t ht j
  have h := hG.1 t ht j
  rw [← extRC_eq rc₀ rc, Pool.P0221.sp_eq_sort hlay (sh ℓ) rc₀ rc _ _ t ht.le]
  omega

open Classical in
/-- **The fit failure of P0234's `badTerm` and P0246's `badTermP`, averaged over the sampling/filter arrays**, is at most P0221's bound
(entry-order layout and P0185's hypotheses at horizon `T`):
`E_arr[P_rc(some thread does not fit before T)] ≤ T·D·δs + T·D·(Lf+1)·K·delta`. -/
theorem sum_notFits_le (hlay : m.P.lay = Pool.P0176.sortLay m.P.sl) {T : ℕ}
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
    ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
        ∑ ω : Fin T → RC m.P, Pool.P0202.pw (wR m.P) ω *
          (if ∀ t < T, Pool.P0176.Fits m.P.Lv m.P.sl (sp m.P (sh ℓ) (Pool.P0210.extR m.P rc₀ ω)
              (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) t)
            then 0 else 1) ≤
      T * m.P.D * δs + T * m.P.D * (m.Lf + 1) * m.P.K * Pool.P0042.delta (Fintype.card ι) m.q m.P.R kk M0 := by
  have hw0 : ∀ arr : Pool.P0116.Arr (pp m) T → Bool, 0 ≤ Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr := by
    intro arr
    refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) arr
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [m.hps.1, m.hq.1]
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [m.hps.2, m.hq.2]
  have h1 : ∑ rc, wR m.P rc = 1 := sum_wR m.P hL hN
  set Fit : (Fin T → RC m.P) → (Pool.P0116.Arr (pp m) T → Bool) → Prop := fun ω arr =>
    ∀ t < T, Pool.P0176.Fits m.P.Lv m.P.sl (sp m.P (sh ℓ) (Pool.P0210.extR m.P rc₀ ω)
      (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) t)
  have hrc : ∀ rc : Fin T → RC m.P, ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
      (if Fit rc arr then 0 else 1) ≤
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
    · rw [if_pos (fits_of_goodAD hlay ℓ rc₀ rc arr _ hG), if_pos hG]
    · rw [if_neg hG]; split_ifs <;> norm_num
  calc ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
        ∑ rc : Fin T → RC m.P, Pool.P0202.pw (wR m.P) rc * (if Fit rc arr then 0 else 1)
      = ∑ rc : Fin T → RC m.P, Pool.P0202.pw (wR m.P) rc *
          ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * (if Fit rc arr then 0 else 1) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ rc : Fin T → RC m.P, Pool.P0202.pw (wR m.P) rc *
          (T * m.P.D * δs + T * m.P.D * (m.Lf + 1) * m.P.K * Pool.P0042.delta (Fintype.card ι) m.q m.P.R kk M0) :=
        Finset.sum_le_sum fun rc _ => mul_le_mul_of_nonneg_left (hrc rc)
          (Finset.prod_nonneg fun j _ => wR_nonneg m.P hL _)
    _ = _ := by rw [← Finset.sum_mul, Pool.P0202.sum_pw_one h1 T, one_mul]

end Pool.P0251
