import Pool.P0266.Congr
import Pool.P0252.Fits
import Pool.P0243.Budget

/-!
# ALG's term averaged over the sampling/filter array (P0217's `E_arr[algT]` for P0225's `withAlgG`)

P0250's `alg_expect_final` bounds P0234's `algTerm` for every fixed array. Here it is averaged over P0091's array law:
the walk weight `walkW` is P0259's `walkRHS` with explicit weights (`walkW_eq`), and its expectation is P0259's split
bound (`exp_walkW`, via `Congr.lean`'s `nbad_eq_nbR`); the learner budget is P0243's `budget_sum` (`exp_budget`); the
two no-overflow events are P0252's (`sum_notFit_le`).
-/

namespace Pool.P0266

open Finset Pool.P0194 Pool.P0212 Pool.P0176 Pool.P0200 Pool.P0001 Pool.P0050

section Arith

/-- Averaging a per-array bound `F ≤ W·(C + X + Y) + W·T₀·Q` against weights summing to one. -/
theorem avg_le {α : Type} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1)
    (F X Y Q : α → ℝ) {W C T₀ : ℝ} (h : ∀ a, F a ≤ W * (C + X a + Y a) + W * T₀ * Q a) :
    ∑ a, w a * F a ≤ W * (C + ∑ a, w a * X a) + W * ∑ a, w a * Y a + W * T₀ * ∑ a, w a * Q a := by
  calc ∑ a, w a * F a ≤ ∑ a, w a * (W * (C + X a + Y a) + W * T₀ * Q a) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hw a)
    _ = W * C * ∑ a, w a + W * ∑ a, w a * X a + W * ∑ a, w a * Y a + W * T₀ * ∑ a, w a * Q a := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
    _ = _ := by rw [hs]; ring

/-- The weights that make P0259's `walkRHS` equal to P0250's `walkW`: `a₀ = 0`, `a_j = ρ(A + B√(Bt j))/Bt(j−1)`. -/
noncomputable def aW (A B : ℝ) (Bt : ℕ → ℕ) (ρ : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 0 else ρ * (A + B * √(Bt j : ℝ)) / (Bt (j - 1) : ℝ)

theorem aW_nonneg {A B ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (Bt : ℕ → ℕ) (j : ℕ) : 0 ≤ aW A B Bt ρ j := by
  unfold aW; split_ifs
  · exact le_rfl
  · positivity

/-- **P0250's `walkW` is P0259's `walkRHS`** with the weights `aW` and `c = ccP`. -/
theorem walkW_eq {A B ρ : ℝ} {Bt : ℕ → ℕ} (hpos : ∀ j, 0 < Bt j) (NE D : ℕ) (nb : ℕ → ℕ) :
    Pool.P0250.walkW A B Bt D ρ (fun j => (nb j : ℝ)) =
      Pool.P0259.walkRHS NE D Bt nb (aW A B Bt ρ) (Pool.P0250.ccP A B Bt D) := by
  unfold Pool.P0250.walkW Pool.P0259.walkRHS
  have h0 : aW A B Bt ρ 0 = 0 := by simp [aW]
  rw [h0, mul_zero, zero_add, mul_comm ((nb (D - 1) : ℝ))]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_Ico] at hj
  have hb : (0 : ℝ) < Bt (j - 1) := by exact_mod_cast hpos (j - 1)
  unfold aW
  rw [if_neg (by omega)]
  field_simp

end Arith

section Fit

attribute [local instance] Pool.P0082.coinFintype

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ)
  (ℓ : LossSeq n) (T : ℕ) (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

local notation "QQ" => Pool.P0225.withAlgG P η L N G γ wE ρG

/-- P0250's `FitA` on P0252's good event (P0252's `fits_actual`). -/
theorem fitA_of_goodR (hlay : (QQ).lay = sortLay (QQ).sl) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (QQ).K → ι → Bool)
    {S : ℕ} (rc : Fin T → RC (QQ)) (hG : Pool.P0252.GoodR (QQ) ℓ T S rc ωs φ) :
    Pool.P0250.FitA P η L N G γ wE ρG ℓ ωs φ T (Pool.P0210.extR (QQ) rc0 rc) :=
  Pool.P0252.fits_actual (QQ) hlay ℓ rc0 rc ωs φ hG

/-- P0250's `FitF` on P0252's good event (P0252's `fits_forced`). -/
theorem fitF_of_goodR (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (QQ).K → ι → Bool) {S : ℕ} (cstar : ℕ → ℕ → ι)
    (rc : Fin T → RC (QQ)) (hG : Pool.P0252.GoodR (QQ) ℓ T S rc ωs φ) :
    Pool.P0250.FitF P η L N G γ wE ρG ℓ ωs φ T cstar (Pool.P0210.extR (QQ) rc0 rc) := by
  intro j a _ _ _ hc u hu
  exact Pool.P0252.fits_forced (QQ) ℓ rc0 rc ωs φ hG (cstar j a) hc u hu

open Classical in
/-- **Both no-overflow events, averaged over the array and the round coins** (entry-order layout, P0185's
hypotheses at horizon `T`): `E_arr E[[¬FitA] + [¬FitF]] ≤ 2·(T·D·δs + T·D·(Lf+1)·K·delta)`. -/
theorem sum_notFit_le (hlay : (QQ).lay = sortLay (QQ).sl) (hL : (QQ).IsLaw) (hN : 0 < (QQ).N) {Lf : ℕ} {ps q : ℝ}
    (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hE : Monotone (QQ).E) (hB : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hLv : 0 < (QQ).Lv)
    (hlev : ∀ r a, (QQ).lev r a + 1 < (QQ).Lv)
    {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ (QQ).xr j) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hR : 1 ≤ (QQ).R) (hT : 1 / xmin * T ≤ 2 ^ ((QQ).R - 1) * (QQ).θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * (QQ).R ≤ M0)
    (hk : 4 * (QQ).R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * (QQ).R))
    (hlevLt : ∀ a < T, ∀ r < (QQ).D, (QQ).lev r a ≤ Lf) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < T → r < (QQ).D →
      ∑ F ∈ (Finset.univ.filter fun c => (QQ).E c = a ∧ (QQ).thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => (QQ).E c = a ∧ (QQ).thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S')
    (hρS : (1 - 1 / (4 * (QQ).R : ℝ)) ^ (QQ).K * ((S' : ℝ) + (s0 + (QQ).D * (QQ).Lv * S')) ≤ S')
    (hsl : ∀ j, ((QQ).D : ℝ) * ((s0 + (QQ).D * (QQ).Lv * S') + ((QQ).Lv - 1 : ℕ) * S') + (QQ).D * s0 + 1 ≤ (QQ).sl j)
    (cstar : ℕ → ℕ → ι) :
    ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool,
        Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
      (∑ rc : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) rc *
          (if Pool.P0250.FitA P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
              (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T (Pool.P0210.extR (QQ) rc0 rc) then 0 else 1) +
        ∑ rc : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) rc *
          (if Pool.P0250.FitF P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
              (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T cstar (Pool.P0210.extR (QQ) rc0 rc) then 0 else 1)) ≤
      2 * (T * (QQ).D * δs + T * (QQ).D * (Lf + 1) * (QQ).K * Pool.P0042.delta (Fintype.card ι) q (QQ).R kk M0) := by
  have hw0 : ∀ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool,
      0 ≤ Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr := by
    intro arr
    refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) arr
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [hps.1, hq0]
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [hps.2, hq1]
  have h1 : ∑ rc, wR (QQ) rc = 1 := sum_wR (QQ) hL hN
  set Pbad := T * (QQ).D * δs + T * (QQ).D * (Lf + 1) * (QQ).K * Pool.P0042.delta (Fintype.card ι) q (QQ).R kk M0
  set GA : (Fin T → RC (QQ)) → (Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool) → Prop := fun rc arr =>
    Pool.P0252.GoodR (QQ) ℓ T (s0 + (QQ).D * (QQ).Lv * S' + 1) rc (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
      (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) with hGA
  have hrc : ∀ rc : Fin T → RC (QQ),
      ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool,
        Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
        ((if Pool.P0250.FitA P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
              (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T (Pool.P0210.extR (QQ) rc0 rc) then (0 : ℝ) else 1) +
          (if Pool.P0250.FitF P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
              (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T cstar (Pool.P0210.extR (QQ) rc0 rc) then 0 else 1)) ≤
        2 * Pbad := by
    intro rc
    have hBm' : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) / xmin := by rw [Nat.cast_one]; exact hBm
    have hT' : ((1 : ℕ) : ℝ) / xmin * T ≤ 2 ^ ((QQ).R - 1) * (QQ).θ := by rw [Nat.cast_one]; exact hT
    have hP := Pool.P0185.prob_notGoodAD_le (NE := T) (Lt := Lf) (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D
      (QQ).Lv (QQ).Bt (QQ).lev (QQ).sl 1 1 (QQ).xr
      (ℓr (QQ) ℓ) (Pool.P0207.rhXR (QQ) ℓ (extE (Pool.P0207.extR (QQ)) none rc)) hps hq0 hq1 hE hB hLv hlev hxmin hx
      (fun u x => (Pool.P0207.ℓr_mem (QQ) ℓ u x).1) (fun u x => (Pool.P0207.ℓr_mem (QQ) ℓ u x).2) zero_le_one hBm' hR
      hT' M0 kk hM0 hk hp hlevLt s0 δs hs S' hM0S hρS hsl (zE (QQ).sl 1 (Pool.P0207.zOfR (QQ)) rc)
    have hstep : ∀ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool,
        ((if Pool.P0250.FitA P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
              (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T (Pool.P0210.extR (QQ) rc0 rc) then (0 : ℝ) else 1) +
          (if Pool.P0250.FitF P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
              (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T cstar (Pool.P0210.extR (QQ) rc0 rc) then 0 else 1)) ≤
        2 * (if GA rc arr then 0 else 1) := by
      intro arr
      by_cases hG : GA rc arr
      · rw [if_pos (fitA_of_goodR P η L N G γ wE ρG ℓ T rc0 hlay _ _ rc hG),
          if_pos (fitF_of_goodR P η L N G γ wE ρG ℓ T rc0 _ _ cstar rc hG), if_pos hG]; norm_num
      · rw [if_neg hG]; split_ifs <;> norm_num
    calc _ ≤ ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool,
          Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
          (2 * (if GA rc arr then 0 else 1)) :=
          Finset.sum_le_sum fun arr _ => mul_le_mul_of_nonneg_left (hstep arr) (hw0 arr)
      _ = 2 * ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool,
          Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
          (if GA rc arr then 0 else 1) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ 2 * Pbad := mul_le_mul_of_nonneg_left hP (by norm_num)
  calc _ = ∑ rc : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) rc *
        ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool,
          Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
          ((if Pool.P0250.FitA P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
              (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T (Pool.P0210.extR (QQ) rc0 rc) then (0 : ℝ) else 1) +
          (if Pool.P0250.FitF P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
              (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T cstar (Pool.P0210.extR (QQ) rc0 rc) then 0 else 1)) := by
        conv_rhs => simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun arr _ => ?_
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun rc _ => by ring
    _ ≤ ∑ rc : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) rc * (2 * Pbad) :=
        Finset.sum_le_sum fun rc _ => mul_le_mul_of_nonneg_left (hrc rc)
          (Finset.prod_nonneg fun j _ => wR_nonneg (QQ) hL _)
    _ = 2 * Pbad := by rw [← Finset.sum_mul, Pool.P0202.sum_pw_one h1 T, one_mul]

end Fit

section Budget

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ)
  (ℓ : LossSeq n) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (Pool.P0225.withAlgG P η L N G γ wE ρG).K → ι → Bool)
  (T : ℕ) (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

local notation "QQ" => Pool.P0225.withAlgG P η L N G γ wE ρG

open Classical in
/-- **The learner budget of P0250's bound, in expectation** (fixed sampling/filter bits): on P0250's good event the
budget `Σ_{u<T}((η/2)·VR + slT)` is P0243's `Σ_{u<T} vOK` and every round fits, so P0243's `budget_sum` gives
`E[[GoodAll]·Σ_{u<T} V] ≤ T·Cb(Σ_j sl_j)`. -/
theorem exp_budget (hL : (QQ).IsLaw) (hN : 0 < (QQ).N) (hη : 0 ≤ η) (hwE : P.wE = wE) (hwE0 : 0 < wE) (hγ : 0 < γ)
    (hG : 1 ≤ G) {Ls Lb Lc Lt κ : ℝ} (hκ : 0 ≤ κ) (hTL : T ≤ 2 ^ L) (cstar : ℕ → ℕ → ι) :
    ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
        (if Pool.P0250.GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω)
          then ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
              Pool.P0242.slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u) else 0) ≤
      T * Pool.P0243.Cb η N G γ wE (∑ j : Fin (QQ).D, ((QQ).sl j : ℝ)) κ := by
  have hb := Pool.P0243.budget_sum P η L N G γ wE ρG ℓ ωs φ rc0 T hL hN hη hwE hwE0 hγ hG hκ hTL (Nat.zero_le T) le_rfl
  rw [Nat.cast_zero, sub_zero] at hb
  refine le_trans (Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (Pool.P0228.pw_nonneg (QQ) hL ω)) hb
  by_cases hg : Pool.P0250.GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω)
  · have hfit := hg.2.1
    rw [if_pos hg, if_pos hfit]
    unfold Pool.P0154.isum
    rw [← Finset.range_eq_Ico]
    refine le_of_eq (Finset.sum_congr rfl fun u hu => ?_)
    have hu' : u < T := Finset.mem_range.1 hu
    unfold Pool.P0242.slT Pool.P0243.vOK
    rw [if_pos hu', max_comm]
  · rw [if_neg hg]
    split_ifs
    · exact Finset.sum_nonneg fun u _ => Pool.P0243.vOK_nonneg P η L N G γ wE ρG ℓ ωs φ rc0 T hη _ _ u
    · exact le_rfl

end Budget

section Walk

attribute [local instance] Pool.P0082.coinFintype

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ)
  (ℓ : LossSeq n) (T : ℕ) (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

local notation "QQ" => Pool.P0225.withAlgG P η L N G γ wE ρG

open Classical in
/-- **The walk weight of P0250's bound, averaged over the array and the round coins** (entry-order layout, schedule
`levTh Ld`): with P0259's split at the levels `cz` (coarse levels charged pathwise),
`E_arr E[walkW(A, B, ρ, nBad)] ≤ coarseSum(aW) + M·(P0207's closed count)` whenever `ρ(A + B√(Bt j)) ≤ M` at the
fine levels and `A + B√(Bt(D−1)) ≤ M`. -/
theorem exp_walkW {A B ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (hlay : (QQ).lay = sortLay (QQ).sl) (hL : (QQ).IsLaw) (hN : 0 < (QQ).N) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt)
    {Ld Lf : ℕ} (hlev : (QQ).lev = Pool.P0085.levTh Ld (QQ).Bt) (hLv2 : Ld + 2 ≤ (QQ).Lv) (hLdf : Ld ≤ Lf)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    {ps q : ℝ} (hps0 : 0 < ps) (hps1 : ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hEm : Monotone (QQ).E) {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ (QQ).xr j) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hR : 1 ≤ (QQ).R) (hT : 1 / xmin * T ≤ 2 ^ ((QQ).R - 1) * (QQ).θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * (QQ).R ≤ M0)
    (hk : 4 * (QQ).R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * (QQ).R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < T → r < (QQ).D →
      ∑ F ∈ (Finset.univ.filter fun c => (QQ).E c = a ∧ (QQ).thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => (QQ).E c = a ∧ (QQ).thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S')
    (hρS : (1 - 1 / (4 * (QQ).R : ℝ)) ^ (QQ).K * ((S' : ℝ) + (s0 + (QQ).D * (QQ).Lv * S')) ≤ S')
    (hsl : ∀ j, ((QQ).D : ℝ) * ((s0 + (QQ).D * (QQ).Lv * S') + ((QQ).Lv - 1 : ℕ) * S') + (QQ).D * s0 + 1 ≤ (QQ).sl j)
    (M : ℝ) (hM0' : 0 ≤ M) (cz : ℕ → Prop) [DecidablePred cz]
    (hMa : ∀ j, 1 ≤ j → j < (QQ).D → ¬ cz j → ρ * (A + B * √((QQ).Bt j : ℝ)) ≤ M)
    (hMc : Pool.P0250.ccP A B (QQ).Bt (QQ).D ≤ M) :
    ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool,
        Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
      ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
        Pool.P0250.walkW A B (QQ).Bt (QQ).D ρ (fun j => Pool.P0250.nbad P η L N G γ wE ρG ℓ
          (Pool.P0210.extR (QQ) rc0 ω) (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
          (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T cstar j) ≤
      Pool.P0259.coarseSum T (QQ).D (QQ).Bt cz (aW A B (QQ).Bt ρ) +
        M * (((QQ).D * (QQ).Lv * (s0 + (QQ).D * (QQ).Lv * S' + 1) : ℝ) /
          (ps * (1 - q) ^ ((QQ).K * ((QQ).D * (2 * Ld + T / 2 ^ Ld + 1)))) +
        (QQ).D * T * (T * (QQ).D * δs + T * (QQ).D * (Lf + 1) * (QQ).K * Pool.P0042.delta (Fintype.card ι) q (QQ).R kk M0)) := by
  have h := Pool.P0259.exp_walkRHS_split (QQ) ℓ hL hN hBt hLv2 hLdf cstar hE hthr hps0 hps1 hq0 hq1 hEm hxmin hx hBm hR
    hT M0 kk hM0 hk hp s0 δs hs S' hM0S hρS hsl (aW A B (QQ).Bt ρ) (Pool.P0250.ccP A B (QQ).Bt (QQ).D) M hM0' cz
    (aW_nonneg hA hB hρ (QQ).Bt)
    (fun j hj1 hjD hcz => by
      have hb : (0 : ℝ) < (QQ).Bt (j - 1) := by exact_mod_cast hBt.pos (j - 1)
      unfold aW; rw [if_neg (by omega), mul_div_cancel₀ _ hb.ne']
      exact hMa j hj1 hjD hcz) hMc
  have h0 : aW A B (QQ).Bt ρ 0 = 0 := by simp [aW]
  rw [h0, mul_zero, zero_add] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun arr _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  have e : (fun j => Pool.P0250.nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω)
      (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T cstar j) =
      fun j => ((Pool.P0259.nbR (QQ) ℓ Ld T Lf cstar arr ω j : ℕ) : ℝ) :=
    funext fun j => nbad_eq_nbR P η L N G γ wE ρG ℓ T rc0 hlay hlev cstar arr ω j
  rw [e, walkW_eq hBt.pos T]

end Walk

section Final

attribute [local instance] Pool.P0082.coinFintype

open Pool.P0250 (AP BP ΛP ccP)
open Pool.P0226 (αT αT_nonneg)

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ)
  (ℓ : LossSeq n) (T : ℕ) (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

local notation "QQ" => Pool.P0225.withAlgG P η L N G γ wE ρG

set_option maxHeartbeats 4000000 in
open Classical in
/-- **ALG's term averaged over the sampling/filter array** (P0217's `E_arr[algT]` integrand form for P0225's
`withAlgG`; entry-order layout, schedule `levTh Ld`, P0250's parameter family): with P0259's level split `cz` and a
fine-level weight bound `Mw`,
`E_arr[algTerm] ≤ wE·(T·(A/Bt₀ + B/√Bt₀) + coarseSum + Mw·count) + wE·T·Cb(Σ_j sl_j)
  + wE·T·(2·(T·D·δs + T·D·(Lf+1)·K·delta) + 4|ι|(T+1)²e^{−Ls} + 2(T+1)²e^{−Lb} + (|ι|+1)(T+1)²e^{−Lc} + (T+1)²e^{−Lt})`. -/
theorem algT_arr (hD : 0 < P.D)
    (hL : (Pool.P0225.withAlgG P η L N G γ wE ρG).IsLaw) (hN : 0 < (Pool.P0225.withAlgG P η L N G γ wE ρG).N) (hη : 0 < η) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρG : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)
    {Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).xr j)
    (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hBt0 : ∀ i, 0 < (QQ).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((QQ).Bt (i - 1) : ℝ) ≤ ρ * (QQ).Bt i) (hx0 : 1 / Pool.P0191.xrN (QQ).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QQ).xr i ≤ max M (TT / (nn * (QQ).Bt i)))
    (hΘ : ∀ f, ((QQ).thr0 f : ℝ) ≤ Θ)
    (hlay : (Pool.P0225.withAlgG P η L N G γ wE ρG).lay = Pool.P0176.sortLay (Pool.P0225.withAlgG P η L N G γ wE ρG).sl)
    (hθ : 0 ≤ (QQ).θ) (hR1 : 1 ≤ (QQ).R) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hT : (QQ).Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    (i : Fin n) (harm : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).arm (cstar j a) = i)
    (hΛ' : ∀ c u, ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ
        (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤ (QQ).Λ c u)
    (hTΘ : 0 ≤ Θ * (ρ * TT / nn))
    (h1 : 1 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ + BP P η L N G γ wE ρG Ls M)
    (hlayOK : Pool.P0191.LayOK (QQ).sl (QQ).lay) (hxr0 : ∀ j, 0 < (QQ).xr j) (hxr1 : ∀ j, (QQ).xr j ≤ 1)
    (hcw : (QQ).cB * (QQ).wB = 1) (hLs0 : 0 < Ls) (hLb0 : 0 < Lb) (hκ1 : κ ≤ 1)
    {Ld Lf : ℕ} (hlevT : (QQ).lev = Pool.P0085.levTh Ld (QQ).Bt) (hLv2 : Ld + 2 ≤ (QQ).Lv) (hLdf : Ld ≤ Lf)
    {ps q : ℝ} (hps0 : 0 < ps) (hps1 : ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hEm : Monotone (QQ).E) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hTθ : 1 / xmin * T ≤ 2 ^ ((QQ).R - 1) * (QQ).θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * (QQ).R ≤ M0)
    (hk : 4 * (QQ).R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * (QQ).R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < T → r < (QQ).D →
      ∑ F ∈ (Finset.univ.filter fun c => (QQ).E c = a ∧ (QQ).thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => (QQ).E c = a ∧ (QQ).thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S')
    (hρS : (1 - 1 / (4 * (QQ).R : ℝ)) ^ (QQ).K * ((S' : ℝ) + (s0 + (QQ).D * (QQ).Lv * S')) ≤ S')
    (hsl : ∀ j, ((QQ).D : ℝ) * ((s0 + (QQ).D * (QQ).Lv * S') + ((QQ).Lv - 1 : ℕ) * S') + (QQ).D * s0 + 1 ≤ (QQ).sl j)
    (hG1 : 1 ≤ G) (Mw : ℝ) (hMw : 0 ≤ Mw) (cz : ℕ → Prop) [DecidablePred cz]
    (hMa : ∀ j, 1 ≤ j → j < (QQ).D → ¬ cz j → ρ * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ +
      BP P η L N G γ wE ρG Ls M * √((QQ).Bt j : ℝ)) ≤ Mw)
    (hMc : ccP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ≤ Mw) :
    ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
        Pool.P0234.algTerm (QQ) ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) rc0 T i ≤
      wE * (T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 + BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) +
          (Pool.P0259.coarseSum T (QQ).D (QQ).Bt cz (aW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt ρ) + Mw * (((QQ).D * (QQ).Lv * (s0 + (QQ).D * (QQ).Lv * S' + 1) : ℝ) /
          (ps * (1 - q) ^ ((QQ).K * ((QQ).D * (2 * Ld + T / 2 ^ Ld + 1)))) +
        (QQ).D * T * (T * (QQ).D * δs + T * (QQ).D * (Lf + 1) * (QQ).K * Pool.P0042.delta (Fintype.card ι) q (QQ).R kk M0)))) +
        wE * (T * Pool.P0243.Cb η N G γ wE (∑ j : Fin (QQ).D, ((QQ).sl j : ℝ)) κ) +
        wE * T * (2 * (T * (QQ).D * δs + T * (QQ).D * (Lf + 1) * (QQ).K * Pool.P0042.delta (Fintype.card ι) q (QQ).R kk M0) + (2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls))) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lb) +
          Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) +
          ((T : ℝ) + 1) ^ 2 * Real.exp (-Lt))) := by
  classical
  -- the schedule bounds, from `lev = levTh Ld Bt` and `Ld + 2 ≤ Lv`, `Ld ≤ Lf` (as in P0185's `count_bad_DZ_closed`)
  have hLv : 0 < P.Lv := by change 0 < (QQ).Lv; omega
  have hlev : ∀ r a, P.lev r a + 1 < P.Lv := fun r a => by
    change (QQ).lev r a + 1 < (QQ).Lv
    have := Pool.P0062.levPR_le Ld ((a + 1) / (QQ).Bt r - 1)
    rw [hlevT]; unfold Pool.P0085.levTh; omega
  have hlevLt : ∀ a < T, ∀ r < (QQ).D, (QQ).lev r a ≤ Lf := fun a _ r _ => by
    have := Pool.P0062.levPR_le Ld ((a + 1) / (QQ).Bt r - 1)
    rw [hlevT]; unfold Pool.P0085.levTh; omega
  have hw0 : ∀ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool, 0 ≤ Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr := fun arr =>
    Pool.P0048.wtv_nonneg (fun x => by
        rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith)
      (fun x => by rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith) arr
  have hs1 : ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr = 1 := Pool.P0048.sum_wtv _
  have hav := avg_le _ hw0 hs1 _ _ _ _ (fun arr => Pool.P0250.alg_expect_final P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T rc0
    hD hLv hlev hL hN hη hδ hρG hγ hwE0 hwE hTL hcB0 hLs hLb hLc hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hlay hθ hR1 hBt hT cstar hE hthr i harm hΛ' hTΘ h1 hlayOK hxr0 hxr1 hcw hLs0 hLb0 hκ1)
  refine hav.trans ?_
  -- the walk term
  have hR0 : (0 : ℝ) ≤ (QQ).R := by have : (1 : ℝ) ≤ (QQ).R := by exact_mod_cast hR1
                                    linarith
  have hα := αT_nonneg (ι := ι) η L T hη hδ
  have hA0 : 0 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ := by
    unfold AP
    have : 0 ≤ Lt / κ := div_nonneg hLt hκ.le
    have : 0 ≤ 2 * Ls / xmin := div_nonneg (by linarith) hxm.le
    have : 0 ≤ Lc / (2 * (wE * γ)) := div_nonneg hLc (by positivity)
    positivity
  have hB0 : 0 ≤ BP P η L N G γ wE ρG Ls M := by unfold BP; positivity
  have hX := exp_walkW P η L N G γ wE ρG ℓ T rc0 hA0 hB0 hρ0 hlay hL hN hBt hlevT hLv2 hLdf cstar hE hthr hps0 hps1
    hq0 hq1 hEm hxm hxr hBm hR1 hTθ M0 kk hM0 hk hp s0 δs hs S' hM0S hρS hsl Mw hMw cz hMa hMc
  -- the budget term
  have hY : ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
      ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
        (if Pool.P0250.GoodAll P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω)
          then ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T u +
              Pool.P0242.slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T rc0 κ u) else 0) ≤
      T * Pool.P0243.Cb η N G γ wE (∑ j : Fin (QQ).D, ((QQ).sl j : ℝ)) κ := by
    calc _ ≤ ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
          (T * Pool.P0243.Cb η N G γ wE (∑ j : Fin (QQ).D, ((QQ).sl j : ℝ)) κ) :=
          Finset.sum_le_sum fun arr _ => mul_le_mul_of_nonneg_left
            (exp_budget P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T rc0 hL hN hη.le hwE hwE0 hγ hG1 hκ.le hTL cstar) (hw0 arr)
      _ = _ := by rw [← Finset.sum_mul, hs1, one_mul]
  -- the failure term
  have hZ := sum_notFit_le P η L N G γ wE ρG ℓ T rc0 hlay hL hN ⟨hps0.le, hps1⟩ hq0 hq1.le hEm hBt hLv hlev hxm hxr hBm
    hR1 hTθ M0 kk hM0 hk hp hlevLt s0 δs hs S' hM0S hρS hsl cstar
  have hQ : ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
      (∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
            (if Pool.P0250.FitA P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) +
          ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
            (if Pool.P0250.FitF P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T cstar (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) +
          2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls))) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lb) +
          Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) +
          ((T : ℝ) + 1) ^ 2 * Real.exp (-Lt)) =
      ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr *
        (∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
            (if Pool.P0250.FitA P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) +
          ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
            (if Pool.P0250.FitF P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T cstar (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1)) +
        (2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls))) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lb) +
          Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) +
          ((T : ℝ) + 1) ^ 2 * Real.exp (-Lt)) := by
    rw [show (2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls))) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lb) +
          Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) +
          ((T : ℝ) + 1) ^ 2 * Real.exp (-Lt)) = ∑ arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool, Pool.P0048.wtv (Pool.P0091.pC (NE := T) (D := (QQ).D) (Lt := Lf) (K := (QQ).K) ps q) arr * (2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls))) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lb) +
          Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) +
          ((T : ℝ) + 1) ^ 2 * Real.exp (-Lt)) by
      rw [← Finset.sum_mul, hs1, one_mul], ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun arr _ => by ring
  have hwE0' : (0 : ℝ) ≤ wE := hwE0.le
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have e1 := mul_le_mul_of_nonneg_left hX hwE0'
  have e2 := mul_le_mul_of_nonneg_left hY hwE0'
  have e3 := mul_le_mul_of_nonneg_left hZ (mul_nonneg hwE0' hT0)
  rw [hQ]
  nlinarith [e1, e2, e3]

end Final

end Pool.P0266
