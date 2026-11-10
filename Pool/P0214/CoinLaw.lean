import Pool.P0206.Correspondence
import Pool.P0205.Locality
import Pool.P0116.Law

/-!
# C10 part 3: from the machine's coin law to the process's coins (P0194, P0091)
-/

open Finset Pool.P0001 Pool.P0050

namespace Pool.P0214



section Path

open Pool.P0201 Pool.P0206 Pool.P0194

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {m : MPar n ι}

/-- All start pools before `T` fit in `Ns`. -/
def FitAll (m : MPar n ι) (ℓ : LossSeq n) (ω : ℕ → Yc m × Zc m) (T : ℕ) : Prop :=
  ∀ v < T, (Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω v)).card ≤ m.Ns

theorem toNat_le_one (b : Bool) : (b.toNat : ℝ) ≤ 1 := by cases b <;> simp

theorem toNat_nonneg (b : Bool) : (0 : ℝ) ≤ (b.toNat : ℝ) := Nat.cast_nonneg _

open Classical in
/-- **Per-path bound.** Over machine rounds `0..T` the machine's loss is at most `1` (the dummy round) plus the process's
losses over rounds `0..T−1` (with the machine's coins mapped by `ωR`, `ωsM`, `φM`), plus `T` if some start pool before
`T` overflows. -/
theorem path_le (h : Hyp m) {W : ℕ} (hW1 : 1 ≤ W) (hW : ∀ j, m.kx j ≤ W) (ℓ : LossSeq n) (T : ℕ)
    (hTT : T * W ≤ m.TT) (hTB : T ≤ m.TB) (hTc : T ≤ m.Tc) (ω : ℕ → Yc m × Zc m) :
    ∑ t ∈ range (T + 1), ((ℓ t ((mach m).act t ((mach m).run ℓ ω t) (ω t).1)).toNat : ℝ) ≤
      1 + ∑ u ∈ range T, ((sh ℓ u (play m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u)).toNat : ℝ) +
        T * (if FitAll m ℓ ω T then 0 else 1) := by
  rw [Finset.sum_range_succ']
  have h0 := toNat_le_one (ℓ 0 ((mach m).act 0 ((mach m).run ℓ ω 0) (ω 0).1))
  have hstep : ∀ u ∈ range T, ((ℓ (u + 1) ((mach m).act (u + 1) ((mach m).run ℓ ω (u + 1)) (ω (u + 1)).1)).toNat : ℝ)
      ≤ ((sh ℓ u (play m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u)).toNat : ℝ) +
        (if FitAll m ℓ ω T then 0 else 1) := by
    intro u hu
    have huT : u < T := Finset.mem_range.mp hu
    by_cases hf : FitAll m ℓ ω T
    · rw [if_pos hf, add_zero]
      rw [act_run h hW1 hW u (le_trans (Nat.mul_le_mul_right _ huT.le) hTT) (by omega) (by omega)
        (fun v hv => hf v (by omega))]
      rfl
    · rw [if_neg hf]
      have := toNat_le_one (ℓ (u + 1) ((mach m).act (u + 1) ((mach m).run ℓ ω (u + 1)) (ω (u + 1)).1))
      have := toNat_nonneg (sh ℓ u (play m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u))
      linarith
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  linarith

end Path

section Weights

open Pool.P0201

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (m : MPar n ι)

theorem μM_apply (y : Yc m) :
    (μM m y).toReal = (m.κl y.1).toReal * (1 / (m.P.N : ℝ)) * (m.P.AB.μ y.2.2).toReal := by
  classical
  rcases y with ⟨a, d, yb⟩
  unfold μM
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single a]
  · rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single d]
    · rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single yb]
      · simp only [if_true, Pool.P0015.unif, PMF.ofFintype_apply]
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
        ring
      · intro b _ hb; rw [if_neg]; intro h; exact hb (by simpa using h.symm)
      · simp
    · intro b _ hb
      rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_zero]
      · simp
      · intro c _; rw [if_neg]; intro h; exact hb (by simpa using (congrArg (fun x => x.2.1) h).symm)
    · simp
  · intro b _ hb
    rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_zero]
    · simp
    · intro d' _
      rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_zero]
      · simp
      · intro c _; rw [if_neg]; intro h; exact hb (by simpa using (congrArg (fun x => x.1) h).symm)
  · simp

theorem νM_apply (z : Zc m) :
    (νM m z).toReal = (m.P.AB.ν z.1).toReal *
      Pool.P0051.bernWt (Pool.P0104.qd (pp m) m.ps m.q) z.2 := by
  classical
  rcases z with ⟨zb, j⟩
  unfold νM
  rw [PMF.bind_apply, tsum_fintype, Finset.sum_eq_single zb]
  · rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single j]
    · simp only [if_true]
      rw [ENNReal.toReal_mul, ← Pool.P0051.bernVec_apply (Pool.P0104.qd_mem (pp m) m.hps m.hq)]
    · intro b _ hb; rw [if_neg]; intro h; exact hb (by simpa using h.symm)
    · simp
  · intro b _ hb
    rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_zero]
    · simp
    · intro c _; rw [if_neg]; intro h; exact hb (by simpa using (congrArg (fun x => x.1) h).symm)
  · simp

end Weights

section Locality

open Pool.P0201 Pool.P0206 Pool.P0205 Pool.P0194

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (m : MPar n ι) (T : ℕ)

/-- The process round coins of rounds `0..T−1` (machine rounds `1..T`). -/
def rcOf (ω : Fin (T + 1) → Yc m × Zc m) : Fin T → RC m.P :=
  fun u => ((ω u.succ).1.1, (ω u.succ).1.2.1, (ω u.succ).1.2.2, (ω u.succ).2.1)

/-- Round coins on `ℕ` from finitely many (a default beyond `T`). -/
def extRC (rc₀ : RC m.P) (rc : Fin T → RC m.P) : ℕ → RC m.P := fun u => if h : u < T then rc ⟨u, h⟩ else rc₀

/-- The machine's day bits. -/
def jsOf (ω : Fin (T + 1) → Yc m × Zc m) : Fin (T + 1) → Pool.P0104.Jd (pp m) → Bool := fun t => (ω t).2.2

/-- P0091's coin array read off the machine's day bits (P0116's `arrOf`, horizon `NE = T`). -/
def arrM (ω : Fin (T + 1) → Yc m × Zc m) : Pool.P0116.Arr (pp m) T → Bool := Pool.P0116.arrOf (pp m) T (jsOf m T ω)

variable {m T}

theorem agree_R (ω₀ : Yc m × Zc m) (rc₀ : RC m.P) (ω : Fin (T + 1) → Yc m × Zc m) :
    Agree m.P (ωR m (ext (mach m) ω₀ ω)) (extRC m T rc₀ (rcOf m T ω)) T := by
  intro v hv
  have hh : v + 1 < T + 1 := by omega
  simp only [ωR, Pool.P0205.ext, extRC, rcOf, dif_pos hv, hh, ↓reduceDIte]
  rfl

theorem agree_S (ω₀ : Yc m × Zc m) (ω : Fin (T + 1) → Yc m × Zc m) {u : ℕ} (hu : u < T) :
    AgreeS' (P := m.P) (ωsM m (ext (mach m) ω₀ ω)) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K (arrM m T ω))
      (φM m (ext (mach m) ω₀ ω)) (Pool.P0082.φC T m.P.D m.Lf m.P.K (arrM m T ω)) u := by
  have hs : ∀ c, m.P.E c ≤ u → ωsM m (ext (mach m) ω₀ ω) c =
      Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K (arrM m T ω) c := by
    intro c hc
    have h1 : m.P.E c < T := by omega
    have h2 : m.P.E c < T + 1 := by omega
    simp only [ωsM, Pool.P0205.ext, Pool.P0082.ωsC, dif_pos h1, h2, ↓reduceDIte, arrM, Pool.P0116.arrOf, Pool.P0116.σT, jsOf]
    rfl
  refine ⟨⟨fun c hc => hs c (by omega), fun r a ha => ?_⟩, fun c hc => hs c (by omega)⟩
  funext l k c
  have ha1 : a + 1 < T + 1 := by omega
  simp only [φM, Pool.P0104.φz, Pool.P0082.φC, Pool.P0205.ext, ha1, ↓reduceDIte, arrM, Pool.P0116.arrOf, Pool.P0116.σT, jsOf]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨by omega, h1.1, h1.2⟩ h2
  · exact absurd ⟨h2.2.1, h2.2.2⟩ h1
  · rfl

variable (m T)

/-- All start pools before `T` fit, for the process driven by round coins `rc` and the array `arr`. -/
def FitP (ℓ : LossSeq n) (rc₀ : RC m.P) (rc : Fin T → RC m.P) (arr : Pool.P0116.Arr (pp m) T → Bool) : Prop :=
  ∀ v < T, (Pool.P0095.members m.P.D m.P.Lv (sp m.P (sh ℓ) (extRC m T rc₀ rc)
    (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr) (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) v)).card ≤ m.Ns

open Classical in
/-- The process's loss over rounds `0..T−1` (losses `sh ℓ`) plus `1` and `T·[overflow]`, from the round coins and the
array. -/
noncomputable def Hf (ℓ : LossSeq n) (rc₀ : RC m.P) (rc : Fin T → RC m.P) (arr : Pool.P0116.Arr (pp m) T → Bool) : ℝ :=
  1 + ∑ u ∈ range T, ((sh ℓ u (play m.P (sh ℓ) (extRC m T rc₀ rc) (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K arr)
      (Pool.P0082.φC T m.P.D m.Lf m.P.K arr) u)).toNat : ℝ) +
    T * (if FitP m T ℓ rc₀ rc arr then 0 else 1)

variable {m T}

open Classical in
theorem pathRHS_eq (ℓ : LossSeq n) (ω₀ : Yc m × Zc m) (rc₀ : RC m.P) (ω : Fin (T + 1) → Yc m × Zc m) :
    1 + ∑ u ∈ range T, ((sh ℓ u (play m.P (sh ℓ) (ωR m (ext (mach m) ω₀ ω)) (ωsM m (ext (mach m) ω₀ ω))
        (φM m (ext (mach m) ω₀ ω)) u)).toNat : ℝ) +
      T * (if FitAll m ℓ (ext (mach m) ω₀ ω) T then 0 else 1) = Hf m T ℓ rc₀ (rcOf m T ω) (arrM m T ω) := by
  unfold Hf
  have hR := agree_R ω₀ rc₀ ω
  have hplay : ∀ u ∈ range T, play m.P (sh ℓ) (ωR m (ext (mach m) ω₀ ω)) (ωsM m (ext (mach m) ω₀ ω))
      (φM m (ext (mach m) ω₀ ω)) u = play m.P (sh ℓ) (extRC m T rc₀ (rcOf m T ω))
        (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K (arrM m T ω)) (Pool.P0082.φC T m.P.D m.Lf m.P.K (arrM m T ω)) u := by
    intro u hu
    have huT := Finset.mem_range.mp hu
    rw [play_congr _ _ u (hR.mono (by omega))]
    exact play_congr_s _ _ (agree_S ω₀ ω huT)
  have hfit : FitAll m ℓ (ext (mach m) ω₀ ω) T ↔ FitP m T ℓ rc₀ (rcOf m T ω) (arrM m T ω) := by
    have hsp : ∀ v < T, SPu m ℓ (ext (mach m) ω₀ ω) v = sp m.P (sh ℓ) (extRC m T rc₀ (rcOf m T ω))
        (Pool.P0082.ωsC m.P.E T m.P.D m.Lf m.P.K (arrM m T ω)) (Pool.P0082.φC T m.P.D m.Lf m.P.K (arrM m T ω)) v := by
      intro v hv
      show sp m.P (sh ℓ) (ωR m (ext (mach m) ω₀ ω)) _ _ v = _
      rw [sp_congr _ _ v (hR.mono hv.le)]
      have hS := agree_S ω₀ ω hv
      exact sp_congr_s _ _ hS.1 hS.2
    unfold FitAll FitP
    constructor
    · intro hf v hv; rw [← hsp v hv]; exact hf v hv
    · intro hf v hv; rw [hsp v hv]; exact hf v hv
  rw [Finset.sum_congr rfl fun u hu => by rw [hplay u hu]]
  simp only [hfit]

end Locality

section Change

open Pool.P0201 Pool.P0206 Pool.P0205 Pool.P0194

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (m : MPar n ι)

/-- The machine's per-round weight of the round-coin part. -/
noncomputable def wK' (rc : RC m.P) : ℝ :=
  (m.κl rc.1).toReal * (1 / (m.P.N : ℝ)) * (m.P.AB.μ rc.2.2.1).toReal * (m.P.AB.ν rc.2.2.2).toReal

/-- A machine coin as (round coin, day bits). -/
def splitE : (Yc m × Zc m) ≃ RC m.P × (Pool.P0104.Jd (pp m) → Bool) where
  toFun x := ((x.1.1, x.1.2.1, x.1.2.2, x.2.1), x.2.2)
  invFun p := ((p.1.1, p.1.2.1, p.1.2.2.1), (p.1.2.2.2, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable {m}

theorem wK'_nonneg (rc : RC m.P) : 0 ≤ wK' m rc := by
  unfold wK'; have : (0 : ℝ) ≤ 1 / (m.P.N : ℝ) := by positivity
  positivity

theorem sum_wK' : ∑ rc : RC m.P, wK' m rc = 1 := by
  have hκ : ∑ κ : Kd m.P, (m.κl κ).toReal = 1 := pmf_sum_toReal m.κl
  have hμ : ∑ y : m.P.AB.Y, (m.P.AB.μ y).toReal = 1 := pmf_sum_toReal m.P.AB.μ
  have hν : ∑ z : m.P.AB.Z, (m.P.AB.ν z).toReal = 1 := pmf_sum_toReal m.P.AB.ν
  have hN : ∑ _d : Fin m.P.N, (1 / (m.P.N : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m.P.N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m.P.N)
    field_simp
  unfold wK'
  simp only [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, hν, mul_one, ← Finset.sum_mul, hμ]
  rw [hκ, hN, one_mul]

/-- Finiteness of the coin-sequence spaces (the nesting is too deep for default instance search). -/
noncomputable def finSeqYZ (T : ℕ) : Fintype (Fin T → Yc m × Zc m) :=
  @Pi.instFintype _ _ _ _ (fun _ => (inferInstance : Fintype ((mach m).Y × (mach m).Z)))

noncomputable def finSeqJ (T : ℕ) : Fintype (Fin T → Pool.P0104.Jd (pp m) → Bool) :=
  @Pi.instFintype _ _ _ _ (fun _ => (inferInstance : Fintype (Pool.P0104.Jd (pp m) → Bool)))

attribute [local instance] finSeqYZ finSeqJ

theorem W_split {T : ℕ} (ω : Fin T → Yc m × Zc m) :
    (mach m).W ω = (∏ t, wK' m (splitE m (ω t)).1) *
      ∏ t, Pool.P0051.bernWt (Pool.P0104.qd (pp m) m.ps m.q) (ω t).2.2 := by
  unfold CoinAlg.W
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  show (μM m (ω t).1).toReal * (νM m (ω t).2).toReal = _
  rw [μM_apply, νM_apply]
  unfold wK' splitE
  simp only [Equiv.coe_fn_mk]
  ring

/-- Splitting the coin sequence into the round-coin sequence and the day-bit sequence. -/
theorem sum_split_coins {T : ℕ} (F : (Fin T → RC m.P × (Pool.P0104.Jd (pp m) → Bool)) → ℝ) :
    ∑ ω : Fin T → Yc m × Zc m, (mach m).W ω * F (fun t => splitE m (ω t)) =
      ∑ rcf : Fin T → RC m.P, ∑ js : Fin T → Pool.P0104.Jd (pp m) → Bool,
        (∏ t, wK' m (rcf t)) * (∏ t, Pool.P0051.bernWt (Pool.P0104.qd (pp m) m.ps m.q) (js t)) *
          F (fun t => (rcf t, js t)) := by
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.arrowCongr (Equiv.refl _) (splitE m)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)) _ _ ?_
  intro ω
  rw [W_split]
  rfl

/-- Round `0`'s round coin integrates out. -/
theorem sum_cons {T : ℕ} (G : (Fin T → RC m.P) → ℝ) :
    ∑ rcf : Fin (T + 1) → RC m.P, (∏ t, wK' m (rcf t)) * G (fun u => rcf u.succ) =
      ∑ rc : Fin T → RC m.P, (∏ u, wK' m (rc u)) * G rc := by
  rw [← (Fin.consEquiv fun _ : Fin (T + 1) => RC m.P).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_wK', one_mul]

attribute [local instance] Pool.P0082.coinFintype

/-- Finiteness of the uncurried day-bit space. -/
noncomputable def dayFin (T : ℕ) : Fintype (Fin (T + 1) × Pool.P0104.Jd (pp m) → Bool) :=
  @Pi.instFintype _ _ instDecidableEqProd inferInstance (fun _ => inferInstance)

attribute [local instance] dayFin

/-- **The day bits marginalize to P0091's coin law** on the array (P0116's `σT`, horizon `NE = T`). -/
theorem sum_js {T : ℕ} (K : (Pool.P0116.Arr (pp m) T → Bool) → ℝ) :
    ∑ js : Fin (T + 1) → Pool.P0104.Jd (pp m) → Bool,
      (∏ t, Pool.P0051.bernWt (Pool.P0104.qd (pp m) m.ps m.q) (js t)) * K (Pool.P0116.arrOf (pp m) T js) =
      ∑ arr : Pool.P0116.Arr (pp m) T → Bool, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr * K arr := by
  have hb : ∀ js : Fin (T + 1) → Pool.P0104.Jd (pp m) → Bool,
      (∏ t, Pool.P0051.bernWt (Pool.P0104.qd (pp m) m.ps m.q) (js t)) =
        Pool.P0046.bw (fun tj : Fin (T + 1) × Pool.P0104.Jd (pp m) => Pool.P0104.qd (pp m) m.ps m.q tj.2)
          (fun tj => js tj.1 tj.2) := fun js => Pool.P0084.prod_bw_curry _ js
  simp only [hb]
  calc ∑ js : Fin (T + 1) → Pool.P0104.Jd (pp m) → Bool,
        Pool.P0046.bw (fun tj : Fin (T + 1) × Pool.P0104.Jd (pp m) => Pool.P0104.qd (pp m) m.ps m.q tj.2)
          (fun tj => js tj.1 tj.2) * K (Pool.P0116.arrOf (pp m) T js)
      = ∑ y : Fin (T + 1) × Pool.P0104.Jd (pp m) → Bool,
          Pool.P0046.bw (fun tj : Fin (T + 1) × Pool.P0104.Jd (pp m) => Pool.P0104.qd (pp m) m.ps m.q tj.2) y *
            K (y ∘ Pool.P0116.σT (pp m) T) := by
        refine Fintype.sum_equiv (Equiv.curry (Fin (T + 1)) (Pool.P0104.Jd (pp m)) Bool).symm _ _ ?_
        intro js
        rfl
    _ = ∑ arr : Pool.P0116.Arr (pp m) T → Bool,
          Pool.P0046.bw (fun x => Pool.P0104.qd (pp m) m.ps m.q (Pool.P0116.σT (pp m) T x).2) arr * K arr :=
        Pool.P0084.sum_bw_comp _ (Pool.P0116.σT (pp m) T) (Pool.P0116.σT_inj (pp m) T) K
    _ = _ := by
        refine Finset.sum_congr rfl fun arr _ => ?_
        congr 1
        unfold Pool.P0046.bw Pool.P0048.wtv Pool.P0048.cw
        refine Finset.prod_congr rfl fun x _ => ?_
        rcases x with ⟨e | ⟨a, r, l, k⟩, c⟩ <;> rfl

end Change

section Main

open Pool.P0201 Pool.P0206 Pool.P0205 Pool.P0194

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {m : MPar n ι}

attribute [local instance] finSeqYZ finSeqJ Pool.P0082.coinFintype

theorem W_nonneg {T : ℕ} (ω : Fin T → Yc m × Zc m) : 0 ≤ (mach m).W ω :=
  Finset.prod_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

open Classical in
/-- **C10 part 3: the machine's expected loss over machine rounds `0..T` is at most the expectation, under the
round-coin weights `wK'` (independent rounds) and P0091's coin law on the array (horizon `NE = T`), of `Hf`: one dummy
round plus the process's loss over process rounds `0..T−1` plus `T·[some start pool overflows]`.** -/
theorem sum_expLoss_le (h : Hyp m) {W : ℕ} (hW1 : 1 ≤ W) (hW : ∀ j, m.kx j ≤ W) (ℓ : LossSeq n) (T : ℕ)
    (hTT : T * W ≤ m.TT) (hTB : T ≤ m.TB) (hTc : T ≤ m.Tc) (ω₀ : Yc m × Zc m) (rc₀ : RC m.P) :
    ∑ t ∈ range (T + 1), (mach m).toMachine.expLoss ℓ t ≤
      ∑ arr : Pool.P0116.Arr (pp m) T → Bool, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
        ∑ rc : Fin T → RC m.P, (∏ u, wK' m (rc u)) * Hf m T ℓ rc₀ rc arr := by
  rw [sum_expLoss_eq (mach m) ℓ ω₀ (T + 1)]
  calc ∑ ω : Fin (T + 1) → (mach m).Y × (mach m).Z, (mach m).W ω * ∑ t ∈ range (T + 1),
        ((ℓ t ((mach m).act t ((mach m).run ℓ (ext (mach m) ω₀ ω) t) (ext (mach m) ω₀ ω t).1)).toNat : ℝ)
      ≤ ∑ ω : Fin (T + 1) → Yc m × Zc m, (mach m).W ω * Hf m T ℓ rc₀ (rcOf m T ω) (arrM m T ω) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (W_nonneg ω)
        rw [← pathRHS_eq ℓ ω₀ rc₀ ω]
        exact path_le h hW1 hW ℓ T hTT hTB hTc _
    _ = ∑ ω : Fin (T + 1) → Yc m × Zc m, (mach m).W ω *
          (fun p : Fin (T + 1) → RC m.P × (Pool.P0104.Jd (pp m) → Bool) =>
            Hf m T ℓ rc₀ (fun u => (p u.succ).1) (Pool.P0116.arrOf (pp m) T (fun t => (p t).2)))
          (fun t => splitE m (ω t)) := rfl
    _ = ∑ rcf : Fin (T + 1) → RC m.P, ∑ js : Fin (T + 1) → Pool.P0104.Jd (pp m) → Bool,
          (∏ t, wK' m (rcf t)) * (∏ t, Pool.P0051.bernWt (Pool.P0104.qd (pp m) m.ps m.q) (js t)) *
            Hf m T ℓ rc₀ (fun u => rcf u.succ) (Pool.P0116.arrOf (pp m) T js) := by
        convert sum_split_coins (m := m) (T := T + 1) (fun p => Hf m T ℓ rc₀ (fun u => (p u.succ).1)
          (Pool.P0116.arrOf (pp m) T (fun t => (p t).2))) using 1
    _ = ∑ js : Fin (T + 1) → Pool.P0104.Jd (pp m) → Bool,
          (∏ t, Pool.P0051.bernWt (Pool.P0104.qd (pp m) m.ps m.q) (js t)) *
            ∑ rcf : Fin (T + 1) → RC m.P, (∏ t, wK' m (rcf t)) *
              Hf m T ℓ rc₀ (fun u => rcf u.succ) (Pool.P0116.arrOf (pp m) T js) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun js _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun rcf _ => ?_
        ring
    _ = ∑ js : Fin (T + 1) → Pool.P0104.Jd (pp m) → Bool,
          (∏ t, Pool.P0051.bernWt (Pool.P0104.qd (pp m) m.ps m.q) (js t)) *
            ∑ rc : Fin T → RC m.P, (∏ u, wK' m (rc u)) * Hf m T ℓ rc₀ rc (Pool.P0116.arrOf (pp m) T js) := by
        refine Finset.sum_congr rfl fun js _ => ?_
        rw [sum_cons (fun rc => Hf m T ℓ rc₀ rc (Pool.P0116.arrOf (pp m) T js))]
    _ = _ := sum_js (fun arr => ∑ rc : Fin T → RC m.P, (∏ u, wK' m (rc u)) * Hf m T ℓ rc₀ rc arr)

theorem wK'_eq_wR (hκ : ∀ κ, (m.κl κ).toReal = wK m.P κ) (rc : RC m.P) : wK' m rc = wR m.P rc := by
  unfold wK' wR; rw [hκ]

open Classical in
/-- **C10 part 3 with P0194's round weights**: when the machine's kind law is P0194's `wK`, the round-coin weights are
P0194's `wR`. -/
theorem sum_expLoss_le_wR (h : Hyp m) (hκ : ∀ κ, (m.κl κ).toReal = wK m.P κ) {W : ℕ} (hW1 : 1 ≤ W)
    (hW : ∀ j, m.kx j ≤ W) (ℓ : LossSeq n) (T : ℕ)
    (hTT : T * W ≤ m.TT) (hTB : T ≤ m.TB) (hTc : T ≤ m.Tc) (ω₀ : Yc m × Zc m) (rc₀ : RC m.P) :
    ∑ t ∈ range (T + 1), (mach m).toMachine.expLoss ℓ t ≤
      ∑ arr : Pool.P0116.Arr (pp m) T → Bool, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
        ∑ rc : Fin T → RC m.P, (∏ u, wR m.P (rc u)) * Hf m T ℓ rc₀ rc arr := by
  simpa only [wK'_eq_wR hκ] using sum_expLoss_le h hW1 hW ℓ T hTT hTB hTc ω₀ rc₀

open Classical in
/-- **C10 part 3 under P0201's regime**: under `MPar.Intended m T`, the machine's expected loss over machine rounds
`0..T` is at most the expectation, under P0194's round-coin weights `wR` (independent rounds) and P0091's coin law on
the array, of `Hf` = one dummy round + the process's loss over process rounds `0..T−1` (losses `ℓ(·+1)`) +
`T·[some start pool overflows]`. -/
theorem sum_expLoss_le_intended {T : ℕ} (hI : m.Intended T) (ℓ : LossSeq n) (ω₀ : Yc m × Zc m) (rc₀ : RC m.P) :
    ∑ t ∈ range (T + 1), (mach m).toMachine.expLoss ℓ t ≤
      ∑ arr : Pool.P0116.Arr (pp m) T → Bool, Pool.P0048.wtv (Pool.P0091.pC m.ps m.q) arr *
        ∑ rc : Fin T → RC m.P, (∏ u, wR m.P (rc u)) * Hf m T ℓ rc₀ rc arr :=
  sum_expLoss_le_wR (hyp_of_intended hI) hI.κl_eq (one_le_kmax hI) kx_le_kmax ℓ T (mul_kmax_le hI le_rfl)
    hI.hTB hI.hTc ω₀ rc₀


end Main

end Pool.P0214
