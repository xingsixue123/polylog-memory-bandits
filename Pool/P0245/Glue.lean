import Pool.P0236.Run
import Pool.P0217.Regret
import Pool.P0228.ExpD

/-!
# P0201's machine with the finite twin ALG: P0217's ALG term is the self-rounding ALG's, up to the overflow term
-/

namespace Pool.P0245

open Pool.P0236 Pool.P0230 Finset Pool.P0001 Pool.P0050 Pool.P0201 Pool.P0206 Pool.P0194 Pool.P0214 Pool.P0217 Pool.P0202

variable {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι]

/-- **P0201's machine parameters with the finite twin ALG**: `M0`'s parameters, with `M0.P`'s ALG replaced by the
finite twin of P0225's self-rounding ALG (`S = Ns + 1` entries, learner times `≤ KM`). -/
noncomputable def mTwin (M0 : MPar n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (KM : ℕ) [NeZero N] : MPar n ι where
  P := withTwin M0.P η ε L N G γ wE (M0.Ns + 1) KM
  kx := M0.kx
  κl := M0.κl
  Lf := M0.Lf
  Ns := M0.Ns
  TT := M0.TT
  TB := M0.TB
  Tc := M0.Tc
  ps := M0.ps
  q := M0.q
  hps := M0.hps
  hq := M0.hq
  fA := by unfold withTwin swapA; exact inferInstance
  nN := (inferInstance : NeZero N)

theorem sp_swap (P : ParD n ι) {σ2 : Type} {s2 : σ2} {dr : σ2 → Finset ι → Fin P.N → Option ι}
    {up : σ2 → Finset ι → Fin P.N → Option ι → Bool → σ2} {hm : ∀ σ V d x, dr σ V d = some x → x ∈ V}
    (ℓ : LossSeq n) (ω : ℕ → RC P) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool) (u : ℕ) :
    sp (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u = sp P ℓ ω ωs φ u := by
  unfold sp; rw [pool_swap]; rfl

theorem wR_swap (P : ParD n ι) {σ2 : Type} {s2 : σ2} {dr : σ2 → Finset ι → Fin P.N → Option ι}
    {up : σ2 → Finset ι → Fin P.N → Option ι → Bool → σ2} {hm : ∀ σ V d x, dr σ V d = some x → x ∈ V} :
    wR (swapA P σ2 s2 dr up hm) = wR P := by
  funext rc
  have : wK (swapA P σ2 s2 dr up hm) rc.1 = wK P rc.1 := by
    rcases rc with ⟨_ | _ | s, _⟩ <;> rfl
  unfold wR; rw [this]; rfl

theorem aPol_nonneg (P : ParD n ι) (ℓ : LossSeq n) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
    (ω : ℕ → RC P) (u : ℕ) : 0 ≤ aPol P ℓ ωs φ ω u :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))

section glue

variable (M0 : MPar n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (KM : ℕ) [NeZero N]

/-- The start pools before round `u` (inclusive) fit, on the coins `ω'` of the first `u` rounds. -/
def FitU (T : ℕ) (ℓ : LossSeq n) (rc₀ : RC (PG M0.P η ε L N G γ wE)) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin (PG M0.P η ε L N G γ wE).K → ι → Bool) (u : ℕ) (ω' : Fin u → RC (PG M0.P η ε L N G γ wE)) :
    Prop :=
  ∀ v ≤ u, (Pool.P0095.members M0.P.D M0.P.Lv
    (sp (PG M0.P η ε L N G γ wE) (sh ℓ) (Pool.P0210.extR (PG M0.P η ε L N G γ wE) rc₀ ω') ωs φ v)).card ≤ M0.Ns

open Classical in
/-- **P0217's ALG term for the finite-twin machine** is at most the self-rounding ALG's (same sum with
`PG = withAlgG … ρStar` in place of the twin) plus `wE·T·E_arr[ovf]`'s per-array value `wE·T·ovf`. -/
theorem algT_twin_le (hD : 0 < M0.P.D) (hLv : 0 < M0.P.Lv) (hlev : ∀ r a, M0.P.lev r a + 1 < M0.P.Lv)
    (hG : 0 < G) (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 ≤ η) (hwE0 : 0 ≤ M0.P.wE)
    (hL : (mTwin M0 η ε L N G γ wE KM).P.IsLaw)
    (T : ℕ) (hTL : T ≤ 2 ^ L) (hTK : T ≤ KM) (ℓ : LossSeq n) (rc₀ : RC (mTwin M0 η ε L N G γ wE KM).P) (i : Fin n)
    (arr : Pool.P0116.Arr (pp (mTwin M0 η ε L N G γ wE KM)) T → Bool) :
    algT (mTwin M0 η ε L N G γ wE KM) T ℓ rc₀ i arr ≤
      ∑ u ∈ range T, ∑ ω' : Fin u → RC (PG M0.P η ε L N G γ wE), pw (wR (PG M0.P η ε L N G γ wE)) ω' *
        (M0.P.wE * (aPol (PG M0.P η ε L N G γ wE) (sh ℓ)
          (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr) (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr)
          (Pool.P0210.extR (PG M0.P η ε L N G γ wE) rc₀ ω') u - (sh ℓ u i).toNat)) +
      M0.P.wE * T * ovf (mTwin M0 η ε L N G γ wE KM) T ℓ rc₀ arr := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hw1 : ∑ rc : RC (mTwin M0 η ε L N G γ wE KM).P, wR (mTwin M0 η ε L N G γ wE KM).P rc = 1 :=
    sum_wR _ hL hN
  have hw0 : ∀ rc : RC (mTwin M0 η ε L N G γ wE KM).P, 0 ≤ wR (mTwin M0 η ε L N G γ wE KM).P rc := wR_nonneg _ hL
  have hpw0 : ∀ {t : ℕ} (ω' : Fin t → RC (mTwin M0 η ε L N G γ wE KM).P),
      0 ≤ pw (wR (mTwin M0 η ε L N G γ wE KM).P) ω' := fun ω' => Finset.prod_nonneg fun j _ => hw0 _
  have hwR : wR (mTwin M0 η ε L N G γ wE KM).P = wR (PG M0.P η ε L N G γ wE) := wR_swap _
  -- per-round, per-prefix comparison
  have key : ∀ u < T, ∀ ω' : Fin u → RC (mTwin M0 η ε L N G γ wE KM).P,
      pw (wR (mTwin M0 η ε L N G γ wE KM).P) ω' * ((mTwin M0 η ε L N G γ wE KM).P.wE *
        (aPol (mTwin M0 η ε L N G γ wE KM).P (sh ℓ) (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr)
          (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr) (Pool.P0210.extR (mTwin M0 η ε L N G γ wE KM).P rc₀ ω') u -
          (sh ℓ u i).toNat)) ≤
        pw (wR (PG M0.P η ε L N G γ wE)) ω' * (M0.P.wE * (aPol (PG M0.P η ε L N G γ wE) (sh ℓ)
          (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr) (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr)
          (Pool.P0210.extR (PG M0.P η ε L N G γ wE) rc₀ ω') u - (sh ℓ u i).toNat)) +
          M0.P.wE * (pw (wR (mTwin M0 η ε L N G γ wE KM).P) ω' *
            if FitU M0 η ε L N G γ wE T ℓ rc₀ (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr)
              (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr) u ω' then 0 else 1) := by
    intro u hu ω'
    have hpw : pw (wR (mTwin M0 η ε L N G γ wE KM).P) ω' = pw (wR (PG M0.P η ε L N G γ wE)) ω' := by
      rw [hwR]; rfl
    rw [← hpw]
    have hwE' : (mTwin M0 η ε L N G γ wE KM).P.wE = M0.P.wE := rfl
    rw [hwE']
    split_ifs with hfit
    · have heq : aPol (mTwin M0 η ε L N G γ wE KM).P (sh ℓ) (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr)
            (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr) (Pool.P0210.extR (mTwin M0 η ε L N G γ wE KM).P rc₀ ω') u =
          aPol (PG M0.P η ε L N G γ wE) (sh ℓ) (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr)
            (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr) (Pool.P0210.extR (PG M0.P η ε L N G γ wE) rc₀ ω') u :=
        aPol_twin M0.P η ε L N G γ wE (sh ℓ) (Pool.P0210.extR (PG M0.P η ε L N G γ wE) rc₀ ω')
          (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr) (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr)
          hD hLv hlev hG hγ hwE hε hη (u + 1) (by omega) (by omega)
          (fun v hv => Nat.succ_le_succ ((Finset.card_le_card Finset.sdiff_subset).trans (hfit v (by omega))))
          (Nat.lt_succ_self u)
      rw [heq]; simp
    · have h1 := Pool.P0228.aPol_le_one (mTwin M0 η ε L N G γ wE KM).P (sh ℓ)
        (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr) (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr)
        (Pool.P0210.extR (mTwin M0 η ε L N G γ wE KM).P rc₀ ω') u
      have h2 := aPol_nonneg (PG M0.P η ε L N G γ wE) (sh ℓ)
        (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr) (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr)
        (Pool.P0210.extR (PG M0.P η ε L N G γ wE) rc₀ ω') u
      have h3 := hpw0 ω'
      have h4 : 0 ≤ pw (wR (mTwin M0 η ε L N G γ wE KM).P) ω' * M0.P.wE := mul_nonneg h3 hwE0
      nlinarith
  -- the overflow part
  have hov : ∀ u < T, ∑ ω' : Fin u → RC (mTwin M0 η ε L N G γ wE KM).P,
      pw (wR (mTwin M0 η ε L N G γ wE KM).P) ω' *
        (if FitU M0 η ε L N G γ wE T ℓ rc₀ (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr)
          (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr) u ω' then 0 else 1) ≤
        ovf (mTwin M0 η ε L N G γ wE KM) T ℓ rc₀ arr := by
    intro u hu
    rw [← Pool.P0202.sum_pw_prefix hw1 u _ T hu.le]
    unfold ovf
    refine Finset.sum_le_sum fun rc _ => mul_le_mul_of_nonneg_left ?_ (hpw0 rc)
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact zero_le_one
    · exfalso
      apply h1
      intro v hv
      have hag : Agree (PG M0.P η ε L N G γ wE)
          (Pool.P0210.extR (PG M0.P η ε L N G γ wE) rc₀ (Pool.P0202.pre hu.le rc))
          (extRC (mTwin M0 η ε L N G γ wE KM) T rc₀ rc) v := by
        intro w hw
        show (if h : w < u then Pool.P0202.pre hu.le rc ⟨w, h⟩ else rc₀) = (if h : w < T then rc ⟨w, h⟩ else rc₀)
        rw [dif_pos (show w < u by omega), dif_pos (show w < T by omega)]
        rfl
      have hsp := sp_congr (P := PG M0.P η ε L N G γ wE) (ℓ := sh ℓ) (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr)
        (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr) v hag
      have h3 := h2 v (by omega)
      have h4 : sp (mTwin M0 η ε L N G γ wE KM).P (sh ℓ) (extRC (mTwin M0 η ε L N G γ wE KM) T rc₀ rc)
          (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr) (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr) v =
          sp (PG M0.P η ε L N G γ wE) (sh ℓ) (extRC (mTwin M0 η ε L N G γ wE KM) T rc₀ rc)
          (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr) (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr) v :=
        sp_swap _ _ _ _ _ _
      have h3' : (Pool.P0095.members M0.P.D M0.P.Lv (sp (PG M0.P η ε L N G γ wE) (sh ℓ)
          (extRC (mTwin M0 η ε L N G γ wE KM) T rc₀ rc) (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr)
          (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr) v)).card ≤ M0.Ns := by
        rw [← h4]; exact h3
      exact (congrArg (fun s => (Pool.P0095.members M0.P.D M0.P.Lv s).card) hsp).trans_le h3'
    · exact le_rfl
  unfold algT
  refine (Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun ω' _ => key u (Finset.mem_range.1 hu) ω').trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add le_rfl ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hwE0
  calc _ ≤ ∑ u ∈ range T, ovf (mTwin M0 η ε L N G γ wE KM) T ℓ rc₀ arr :=
        Finset.sum_le_sum fun u hu => hov u (Finset.mem_range.1 hu)
    _ = T * ovf (mTwin M0 η ε L N G γ wE KM) T ℓ rc₀ arr := by simp

/-! ### Memory of the finite-twin machine -/

open Classical in
/-- **The finite twin's bits**: `log₂` of ALG's state count in `mTwin` is at most
`log₂(KM+1) + log₂(KM·Imx+1) + (Ns+1)·log₂((|ι|+1)·((KM·Bmx+1)(KM·Imx+1))^(L+1) + 1)` (P0236's `card_withTwin`). -/
theorem logb_card_twin_le :
    Real.logb 2 (Fintype.card (mTwin M0 η ε L N G γ wE KM).P.σA) ≤
      Real.logb 2 (KM + 1) + Real.logb 2 (KM * Imx η ε G γ wE + 1) +
        (M0.Ns + 1) * Real.logb 2 ((Fintype.card ι + 1) *
          ((KM * Bmx G γ wE + 1) * (KM * Imx η ε G γ wE + 1)) ^ (L + 1) + 1) := by
  have hc : Fintype.card (mTwin M0 η ε L N G γ wE KM).P.σA =
      Fintype.card (FS ι L (M0.Ns + 1) KM (KM * Imx η ε G γ wE) (KM * Bmx G γ wE)) :=
    Fintype.card_congr (Equiv.refl _)
  have hpos : 0 < Fintype.card (mTwin M0 η ε L N G γ wE KM).P.σA :=
    Fintype.card_pos_iff.2 ⟨(mTwin M0 η ε L N G γ wE KM).P.sA0⟩
  have hb := card_withTwin M0.P η ε L N G γ wE (M0.Ns + 1) KM
  rw [← hc] at hb
  calc Real.logb 2 (Fintype.card (mTwin M0 η ε L N G γ wE KM).P.σA)
      ≤ Real.logb 2 (((KM + 1) * (KM * Imx η ε G γ wE + 1) *
          ((Fintype.card ι + 1) * ((KM * Bmx G γ wE + 1) * (KM * Imx η ε G γ wE + 1)) ^ (L + 1) + 1) ^
            (M0.Ns + 1) : ℕ) : ℝ) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos)
        exact_mod_cast hb
    _ = _ := by
        push_cast
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity) (by positivity),
          Real.logb_pow]
        push_cast; ring

open Classical in
/-- **Memory of P0201's machine with the finite twin ALG**: P0201's `memBits_mach_le` with ALG's state count
bounded by `logb_card_twin_le`. -/
theorem memBits_mTwin_le :
    (mach (mTwin M0 η ε L N G γ wE KM)).toMachine.memBits ≤
      (mTwin M0 η ε L N G γ wE KM).P.AB.toMachine.memBits +
        (M0.Ns * Real.logb 2 (Fintype.card ι * 2 ^ ((pp (mTwin M0 η ε L N G γ wE KM)).Lt + 1) * (2 * (M0.TB + 1)) + 1) +
          (M0.Ns * M0.Ns : ℕ) * Real.logb 2 (M0.TT + 1) + Real.logb 2 (M0.TB + 1) +
          (Real.logb 2 (KM + 1) + Real.logb 2 (KM * Imx η ε G γ wE + 1) +
            (M0.Ns + 1) * Real.logb 2 ((Fintype.card ι + 1) *
              ((KM * Bmx G γ wE + 1) * (KM * Imx η ε G γ wE + 1)) ^ (L + 1) + 1)) +
          Real.logb 2 (M0.Tc + 1) + Real.logb 2 (Fintype.card (Pool.P0194.Kd (mTwin M0 η ε L N G γ wE KM).P)) +
          Real.logb 2 N) := by
  have h := memBits_mach_le (mTwin M0 η ε L N G γ wE KM)
  have h2 := logb_card_twin_le M0 η ε L N G γ wE KM
  have hN : (mTwin M0 η ε L N G γ wE KM).P.N = N := rfl
  rw [hN] at h
  refine h.trans ?_
  have e1 : (mTwin M0 η ε L N G γ wE KM).Ns = M0.Ns := rfl
  have e2 : (mTwin M0 η ε L N G γ wE KM).TB = M0.TB := rfl
  have e3 : (mTwin M0 η ε L N G γ wE KM).TT = M0.TT := rfl
  have e4 : (mTwin M0 η ε L N G γ wE KM).Tc = M0.Tc := rfl
  rw [e1, e2, e3, e4]
  have hσ : Real.logb 2 (Fintype.card (mTwin M0 η ε L N G γ wE KM).P.σA) ≤ _ := h2
  linarith

end glue

end Pool.P0245
