import Pool.P0214.CoinLaw
import Pool.P0210.Split

/-! # The machine's regret for P0194's process, split (P0214's coin law ∘ P0210's split) -/

open Finset Pool.P0001 Pool.P0050 Pool.P0201 Pool.P0206 Pool.P0194 Pool.P0214

namespace Pool.P0217

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {m : MPar n ι}

attribute [local instance] finSeqYZ finSeqJ Pool.P0082.coinFintype

theorem extRC_eq (rc₀ : RC m.P) {T : ℕ} (rc : Fin T → RC m.P) : extRC m T rc₀ rc = Pool.P0210.extR m.P rc₀ rc := rfl

open Classical in
/-- Probability (under P0194's round weights) that some start pool before `T` overflows, for a fixed array. -/
noncomputable def ovf (m : MPar n ι) (T : ℕ) (ℓ : LossSeq n) (rc₀ : RC m.P) (arr : Pool.P0116.Arr (pp m) T → Bool) : ℝ :=
  ∑ rc : Fin T → RC m.P, Pool.P0202.pw (wR m.P) rc * (if FitP m T ℓ rc₀ rc arr then 0 else 1)

/-- P0210's `regret_split_base` of the process's expected regret against arm `i` (losses `ℓ(·+1)`), for a fixed
array: BASE's gap with weight `wB + Σ_s x_s`, ALG's gap with weight `wE`, and each slot's gap to BASE. -/
noncomputable def splitR (m : MPar n ι) (T : ℕ) (ℓ : LossSeq n) (rc₀ : RC m.P) (i : Fin n)
    (arr : Pool.P0116.Arr (pp m) T → Bool) : ℝ :=
  ∑ u ∈ range T, ∑ ω' : Fin u → RC m.P, Pool.P0202.pw (wR m.P) ω' *
    ((m.P.wB + ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1) *
        (bPol m.P (sh ℓ) (Pool.P0210.extR m.P rc₀ ω') u - (sh ℓ u i).toNat) +
      m.P.wE * (aPol m.P (sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
        (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) (Pool.P0210.extR m.P rc₀ ω') u - (sh ℓ u i).toNat) +
      ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1 *
        (slotVal m.P (sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
          (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) (Pool.P0210.extR m.P rc₀ ω') u s -
          bPol m.P (sh ℓ) (Pool.P0210.extR m.P rc₀ ω') u))

open Classical in
/-- **The machine's regret against an arm, split.** Under P0201's regime `MPar.Intended m T`, P0194's `IsLaw` and
`0 < N`: the machine's expected loss over machine rounds `0..T` minus arm `i`'s loss is at most
`1 + T·E_arr[ovf] + E_arr[splitR]` (P0091's array law; `splitR` = P0210's split for the process with losses
`ℓ(·+1)` and sampling/filter bits `ωsC arr`, `φC arr`). -/
theorem expLoss_sub_le_split {T : ℕ} (hI : m.Intended T) (hL : m.P.IsLaw) (hN : 0 < m.P.N) (ℓ : LossSeq n)
    (ω₀ : Yc m × Zc m) (rc₀ : RC m.P) (i : Fin n) :
    ∑ t ∈ range (T + 1), (mach m).toMachine.expLoss ℓ t - cumLoss ℓ (T + 1) i ≤
      1 + T * ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * ovf m T ℓ rc₀ arr +
        ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * splitR m T ℓ rc₀ i arr := by
  have hb := sum_expLoss_le_intended hI ℓ ω₀ rc₀
  have h1 : ∑ rc, wR m.P rc = 1 := sum_wR m.P hL hN
  have hpw1 : ∑ rc : Fin T → RC m.P, Pool.P0202.pw (wR m.P) rc = 1 := Pool.P0202.sum_pw_one h1 T
  have hw1 : ∑ arr : Pool.P0116.Arr (pp m) T → Bool, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr = 1 :=
    Pool.P0048.sum_wtv _
  have hcum : cumLoss ℓ (T + 1) i = ((ℓ 0 i).toNat : ℝ) + ∑ u ∈ range T, ((sh ℓ u i).toNat : ℝ) := by
    unfold cumLoss; rw [Finset.sum_range_succ']; simp only [sh]; ring
  have h0 : (0 : ℝ) ≤ ((ℓ 0 i).toNat : ℝ) := Nat.cast_nonneg _
  set C : ℝ := ∑ u ∈ range T, ((sh ℓ u i).toNat : ℝ) with hC
  have hHf : ∀ arr, ∑ rc : Fin T → RC m.P, (∏ u, wR m.P (rc u)) * Hf m T ℓ rc₀ rc arr =
      1 + C + splitR m T ℓ rc₀ i arr + T * ovf m T ℓ rc₀ arr := by
    intro arr
    have hs := Pool.P0210.regret_split_base m.P (sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
      (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) hL hN rc₀ T i
    have e : ∀ rc : Fin T → RC m.P, (∏ u, wR m.P (rc u)) * Hf m T ℓ rc₀ rc arr =
        Pool.P0202.pw (wR m.P) rc * 1 + Pool.P0202.pw (wR m.P) rc * ∑ u ∈ range T, ((sh ℓ u (play m.P (sh ℓ)
          (Pool.P0210.extR m.P rc₀ rc) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
            (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) u)).toNat : ℝ) +
          T * (Pool.P0202.pw (wR m.P) rc * (if FitP m T ℓ rc₀ rc arr then 0 else 1)) := by
      intro rc; simp only [Hf, extRC_eq, Pool.P0202.pw]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hpw1]
    unfold splitR ovf
    linarith [hs]
  have hb2 : ∑ arr : Pool.P0116.Arr (pp m) T → Bool, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
      ∑ rc : Fin T → RC m.P, (∏ u, wR m.P (rc u)) * Hf m T ℓ rc₀ rc arr =
      (1 + C) + ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * splitR m T ℓ rc₀ i arr +
        T * ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * ovf m T ℓ rc₀ arr := by
    simp only [hHf, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun _ _ => by ring
  rw [hcum]
  rw [hb2] at hb
  linarith

/-- **The machine's regret, split** (`n ≥ 1`): for a best arm `i` in hindsight over machine rounds `0..T`. -/
theorem regret_le_split [NeZero n] {T : ℕ} (hI : m.Intended T) (hL : m.P.IsLaw) (hN : 0 < m.P.N) (ℓ : LossSeq n)
    (ω₀ : Yc m × Zc m) (rc₀ : RC m.P) :
    ∃ i : Fin n, bestLoss ℓ (T + 1) = cumLoss ℓ (T + 1) i ∧ regret (mach m).toMachine ℓ (T + 1) ≤
      1 + T * ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * ovf m T ℓ rc₀ arr +
        ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * splitR m T ℓ rc₀ i arr := by
  obtain ⟨i, hi⟩ := exists_bestLoss_eq ℓ (T + 1)
  refine ⟨i, hi, ?_⟩
  unfold regret
  rw [hi]
  exact expLoss_sub_le_split hI hL hN ℓ ω₀ rc₀ i

omit [DecidableEq ι] in
/-- **Overflow from thread blocks.** If, before `T`, every thread's block of start-pool members leaves a free slot
(`|blockMem j| + 1 ≤ sl j`, the first part of P0185's `GoodAD` for P0194's pools) and `Σ_j sl j ≤ Ns`, then all start
pools fit (`FitP`). -/
theorem fitP_of_blocks {T : ℕ} (ℓ : LossSeq n) (rc₀ : RC m.P) (rc : Fin T → RC m.P)
    (arr : Pool.P0116.Arr (pp m) T → Bool)
    (hb : ∀ v < T, ∀ j : Fin m.P.D, (Pool.P0176.blockMem m.P.Lv (sp m.P (sh ℓ) (extRC m T rc₀ rc)
      (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) v) j).card + 1 ≤ m.P.sl j)
    (hN : ∑ j, m.P.sl j ≤ m.Ns) : FitP m T ℓ rc₀ rc arr := by
  intro v hv
  unfold Pool.P0095.members
  refine Finset.card_biUnion_le.trans ?_
  rw [← Fin.sum_univ_eq_sum_range]
  refine (Finset.sum_le_sum fun j _ => ?_).trans hN
  have := hb v hv j
  unfold Pool.P0176.blockMem at this
  omega

/-- The BASE part of `splitR` (independent of the array). -/
noncomputable def baseT (m : MPar n ι) (T : ℕ) (ℓ : LossSeq n) (rc₀ : RC m.P) (i : Fin n) : ℝ :=
  ∑ u ∈ range T, ∑ ω' : Fin u → RC m.P, Pool.P0202.pw (wR m.P) ω' *
    (bPol m.P (sh ℓ) (Pool.P0210.extR m.P rc₀ ω') u - (sh ℓ u i).toNat)

/-- ALG's part of `splitR` (weight `wE` included). -/
noncomputable def algT (m : MPar n ι) (T : ℕ) (ℓ : LossSeq n) (rc₀ : RC m.P) (i : Fin n)
    (arr : Pool.P0116.Arr (pp m) T → Bool) : ℝ :=
  ∑ u ∈ range T, ∑ ω' : Fin u → RC m.P, Pool.P0202.pw (wR m.P) ω' *
    (m.P.wE * (aPol m.P (sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
      (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) (Pool.P0210.extR m.P rc₀ ω') u - (sh ℓ u i).toNat))

/-- The slots' part of `splitR` (probing against BASE, weights `x_s` included). -/
noncomputable def slotT (m : MPar n ι) (T : ℕ) (ℓ : LossSeq n) (rc₀ : RC m.P)
    (arr : Pool.P0116.Arr (pp m) T → Bool) : ℝ :=
  ∑ u ∈ range T, ∑ ω' : Fin u → RC m.P, Pool.P0202.pw (wR m.P) ω' *
    ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1 *
      (slotVal m.P (sh ℓ) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
        (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) (Pool.P0210.extR m.P rc₀ ω') u s -
        bPol m.P (sh ℓ) (Pool.P0210.extR m.P rc₀ ω') u)

theorem splitR_eq (T : ℕ) (ℓ : LossSeq n) (rc₀ : RC m.P) (i : Fin n) (arr : Pool.P0116.Arr (pp m) T → Bool) :
    splitR m T ℓ rc₀ i arr = (m.P.wB + ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1) * baseT m T ℓ rc₀ i +
      algT m T ℓ rc₀ i arr + slotT m T ℓ rc₀ arr := by
  unfold splitR baseT algT slotT
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1; congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

open Classical in
/-- **The machine's regret with BASE's term discharged by P0202**: under `MPar.Intended m T`, `IsLaw`, `0 < N`,
`n ≥ 1`, for a best arm `i` in hindsight,
`regret ≤ 1 + T·E_arr[ovf] + (wB + Σ_s x_s)·regret(Sub(BASE, wB), ℓ(·+1), T) + E_arr[algT + slotT]`. -/
theorem regret_le_base [NeZero n] {T : ℕ} (hI : m.Intended T) (hL : m.P.IsLaw) (hN : 0 < m.P.N) (ℓ : LossSeq n)
    (ω₀ : Yc m × Zc m) (rc₀ : RC m.P) :
    ∃ i : Fin n, bestLoss ℓ (T + 1) = cumLoss ℓ (T + 1) i ∧ regret (mach m).toMachine ℓ (T + 1) ≤
      1 + T * ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * ovf m T ℓ rc₀ arr +
        (m.P.wB + ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1) *
          regret (Pool.P0055.Sub m.P.AB.toMachine m.P.wB hL.1 (Pool.P0202.wB_le_one m.P hL)) (sh ℓ) T +
        ∑ arr, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * (algT m T ℓ rc₀ i arr + slotT m T ℓ rc₀ arr) := by
  obtain ⟨i, hbest, hi⟩ := regret_le_split hI hL hN ℓ ω₀ rc₀
  refine ⟨i, hbest, hi.trans ?_⟩
  have hw1 : ∑ arr : Pool.P0116.Arr (pp m) T → Bool, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr = 1 :=
    Pool.P0048.sum_wtv _
  have hB := Pool.P0202.sum_expect_bPol_sub_le_regret m.P hL hN (w0 := wR m.P) (fun _ => rfl) (sh ℓ) T
    (fun _ ω' => Pool.P0210.extR m.P rc₀ ω') (fun _ ω' v hv => Pool.P0210.extR_lt m.P rc₀ ω' v hv) i
  have hc : 0 ≤ m.P.wB + ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1 :=
    add_nonneg hL.1 (Finset.sum_nonneg fun s _ => hL.2.2.1 s.1)
  have hb : baseT m T ℓ rc₀ i ≤
      regret (Pool.P0055.Sub m.P.AB.toMachine m.P.wB hL.1 (Pool.P0202.wB_le_one m.P hL)) (sh ℓ) T := hB
  simp only [splitR_eq, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hw1, one_mul]
  have := mul_le_mul_of_nonneg_left hb hc
  have e : ∑ arr : Pool.P0116.Arr (pp m) T → Bool, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
      ((m.P.wB + ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1) * baseT m T ℓ rc₀ i) =
      (m.P.wB + ∑ s : Σ j : Fin m.P.D, Fin (m.P.sl j), m.P.xr s.1) * baseT m T ℓ rc₀ i := by
    rw [← Finset.sum_mul, hw1, one_mul]
  linarith

end Pool.P0217
