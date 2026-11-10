import Pool.P0258.Exp2
import Pool.P0253.Twin
import Pool.P0245.Glue

/-!
# The probing remainder of P0258 for the finite twin, in expectation (P0288's piece, step A: generic)
-/

namespace Pool.P0289

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0212 Pool.P0065

section Path

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι)

/-- The deterministic part `K₀` of P0255's `restD2_le` bound (with `c = 0` and `ρ₁ = ρ₀`). -/
noncomputable def probeK0 (T : ℕ) (L xmin M ρ nn TT Θ : ℝ) (Θn : ℕ) (Λbar : ℕ → ℝ) (ρ₀ xf : ℝ) : ℝ :=
  ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
      (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
        + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card)) *
      (if xf < P.xr j then
        Λbar j + Pool.P0222.Wocc L xmin M ρ nn TT Θ (Pool.P0238.lenOf Θn T P.Bt j)
          + Pool.P0158.widV ((Pool.P0238.lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L + P.Bmin
       else 0)
    + xf * (T * ∑ j : Fin P.D, (P.sl j : ℝ))
    + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
        (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0255.Cp P T xf j) + 1)
      + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0255.Cp P T xf j * ρ₀)

/-- The coefficient `K₁` of the learner's budget sum `Σ_{[0,T)} v`. -/
noncomputable def probeK1 : ℝ := ∑ j : Fin P.D, P.xr j * (2 * ∑ j : Fin P.D, (P.sl j : ℝ))

variable (ℓ : LossSeq n) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
  (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)

open Classical in
/-- **P0255's `restD2_le` with `c = 0` and window budgets `r x t = ρ₀ + Σ_{[E x,t)} v`** (P0243's `rOK` shape):
`restD2 ≤ K₀ + K₁·Σ_{[0,T)} v`, with `K₀ = probeK0` and `K₁ = probeK1` deterministic. -/
theorem restD2_le_K (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
    (hfit : ∀ t < T, Pool.P0176.Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ P.xr j) (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i)))
    (Θn : ℕ) (hΘn : ∀ f, P.thr0 f ≤ Θn) (hΘ : (Θn : ℝ) ≤ Θ)
    (hcB : 0 ≤ P.cB) (Λbar : ℕ → ℝ) (hΛ0 : ∀ i, 0 ≤ Λbar i) (hΛa : ∀ i i', i ≤ i' → Λbar i' ≤ Λbar i)
    (hΛn : ∀ x c, P.E x ≤ c → P.Λ x c ≤ Λbar (curT P.E P.thr0 P.D P.Bt x (c + 1)))
    (v : ℕ → ℝ) (hv : ∀ u, 0 ≤ v u) (ρ₀ : ℝ) (hρ₀ : 0 ≤ ρ₀) (xf : ℝ) (hxf : 0 ≤ xf) :
    Pool.P0255.restD2 P ℓ ωs φ hD hLv hlev T L v ρ₀ 0 (fun x t => ρ₀ + Pool.P0154.isum v (P.E x) t) xf ω ≤
      probeK0 P T L xmin M ρ nn TT Θ Θn Λbar ρ₀ xf + probeK1 P * Pool.P0154.isum v 0 T := by
  have h := Pool.P0255.restD2_le P ℓ ωs φ hD hLv hlev ω T hlay hfit hL hxm hxm1 hxr hn hT hM hρ0 hB hρ hx0 hx Θn hΘn hΘ
    hcB Λbar hΛ0 hΛa hΛn v hv ρ₀ 0 hρ₀ le_rfl ρ₀ hρ₀ xf hxf
  have e : ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0255.Cp P T xf j) + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * 0 * (Real.sqrt T *
              Real.sqrt (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0255.Cp P T xf j) + 1))
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0255.Cp P T xf j * ρ₀
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T) =
      ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
          (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0255.Cp P T xf j) + 1)
        + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0255.Cp P T xf j * ρ₀)
      + probeK1 P * Pool.P0154.isum v 0 T := by
    have e1 : probeK1 P * Pool.P0154.isum v 0 T =
        ∑ j : Fin P.D, P.xr j * (2 * ∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T := by
      unfold probeK1; exact Finset.sum_mul _ _ _
    rw [e1, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold probeK0
  linarith [h, e]

end Path

section Twin

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (S KM : ℕ)

local notation "QG" => Pool.P0236.PG P η ε L N G γ wE
local notation "TW" => Pool.P0236.withTwin P η ε L N G γ wE S KM

variable (ℓ : LossSeq n) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (Pool.P0236.PG P η ε L N G γ wE).K → ι → Bool)

theorem probeK0_nonneg (T : ℕ) {L xmin M ρ nn TT Θ : ℝ} (Θn : ℕ) (Λbar : ℕ → ℝ) {ρ₀ xf : ℝ} (hL : 0 ≤ L)
    (hxm : 0 < xmin) (hM : 0 ≤ M) (hcB : 0 ≤ (TW).cB) (hxr : ∀ j, 0 ≤ (TW).xr j) (hΛ0 : ∀ i, 0 ≤ Λbar i)
    (hρ₀ : 0 ≤ ρ₀) (hxf : 0 ≤ xf) :
    0 ≤ probeK0 (TW) T L xmin M ρ nn TT Θ Θn Λbar ρ₀ xf := by
  unfold probeK0
  have hS0 : 0 ≤ ∑ j : Fin (TW).D, ((TW).sl j : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  refine add_nonneg (add_nonneg (Finset.sum_nonneg fun j _ => ?_) (by positivity))
    (Finset.sum_nonneg fun j _ => ?_)
  · refine mul_nonneg (mul_nonneg (hxr j) (by positivity)) ?_
    split_ifs
    · have h1 : 0 ≤ Pool.P0222.Wocc L xmin M ρ nn TT Θ (Pool.P0238.lenOf Θn T (TW).Bt j) := by
        unfold Pool.P0222.Wocc; positivity
      have h2 : 0 ≤ Pool.P0158.widV ((Pool.P0238.lenOf Θn T (TW).Bt j : ℕ) * (TW).cB) (max 1 (TW).cB) L := by
        unfold Pool.P0158.widV
        have : 0 ≤ max 1 (TW).cB := le_trans zero_le_one (le_max_left _ _)
        positivity
      have h3 : (0 : ℝ) ≤ (TW).Bmin := Nat.cast_nonneg _
      linarith [hΛ0 j]
    · exact le_rfl
  · exact mul_nonneg (hxr j) (by positivity)

theorem probeK1_nonneg (hxr : ∀ j, 0 ≤ (TW).xr j) : 0 ≤ probeK1 (TW) := by
  unfold probeK1
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hxr j) (by positivity)

variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
  (hG : 0 < G) (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 ≤ η)
include hG hγ hwE hε hη

open Classical in
/-- **P0258's probing remainder `goodTermP2` for the finite twin with P0243's budgets** (`v = vOK`, `ρ₀ = ρOK`,
`c = 0`, `r = rOK`, as in P0277): `goodTermP2 ≤ K₀ + K₁·T·Cb(Σ_j sl_j)`, with P0255's deterministic `K₀`, `K₁`
(`probeK0`, `probeK1`) and P0253's budget bound. -/
theorem goodTermP2_twin_le (hL : (QG).IsLaw) (hN : 0 < (QG).N) (hwE' : P.wE = wE) (hG1 : 1 ≤ G)
    {κ Lc : ℝ} (hκ : 0 < κ) (hLc : 0 ≤ Lc) (hη0 : 0 < η) (T : ℕ) (hTL : T ≤ 2 ^ L) (rc₀ : RC (TW))
    (hlay : Pool.P0191.LayOK (TW).sl (TW).lay)
    {Ls xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ (TW).xr j) (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < (TW).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((TW).Bt (i - 1) : ℝ) ≤ ρ * (TW).Bt i) (hx0 : 1 / Pool.P0191.xrN (TW).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (TW).xr i ≤ max M (TT / (nn * (TW).Bt i)))
    (Θn : ℕ) (hΘn : ∀ f, (TW).thr0 f ≤ Θn) (hΘ : (Θn : ℝ) ≤ Θ)
    (hcB : 0 ≤ (TW).cB) (Λbar : ℕ → ℝ) (hΛ0 : ∀ i, 0 ≤ Λbar i) (hΛa : ∀ i i', i ≤ i' → Λbar i' ≤ Λbar i)
    (hΛn : ∀ x c, (TW).E x ≤ c → (TW).Λ x c ≤ Λbar (curT (TW).E (TW).thr0 (TW).D (TW).Bt x (c + 1)))
    (xf : ℝ) (hxf : 0 ≤ xf) :
    Pool.P0258.goodTermP2 (TW) ℓ ωs φ hD hLv hlev rc₀ T Ls
        (Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T κ)
        (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
        (Pool.P0243.rOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T ε κ Lc) xf ≤
      probeK0 (TW) T Ls xmin M ρ nn TT Θ Θn Λbar (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) xf +
        probeK1 (TW) * (T * Pool.P0243.Cb η N G γ wE (∑ j : Fin P.D, (P.sl j : ℝ)) κ) := by
  set K0 := probeK0 (TW) T Ls xmin M ρ nn TT Θ Θn Λbar (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) xf
  set K1 := probeK1 (TW)
  have hxr0 : ∀ j, 0 ≤ (TW).xr j := fun j => hxm.le.trans (hxr j)
  have hρOK : 0 ≤ Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc :=
    Pool.P0243.ρOK_nonneg η L γ wE T hη0 hε.le hκ hLc hγ hwE
  have hK0 : 0 ≤ K0 := probeK0_nonneg P η ε L N G γ wE S KM T Θn Λbar hLs hxm hM hcB hxr0 hΛ0 hρOK hxf
  have hK1 : 0 ≤ K1 := probeK1_nonneg P η ε L N G γ wE S KM hxr0
  have hLaw : (TW).IsLaw := hL
  have hpw0 : ∀ ω : Fin T → RC (TW), 0 ≤ Pool.P0202.pw (wR (TW)) ω := fun ω => Pool.P0228.pw_nonneg (TW) hLaw ω
  have hsum1 := Pool.P0228.sum_pw (TW) hLaw hN T
  unfold Pool.P0258.goodTermP2
  set GE : (Fin T → RC (TW)) → Prop := fun ω =>
    (∀ t < T, Pool.P0176.Fits (TW).Lv (TW).sl (sp (TW) ℓ (Pool.P0210.extR (TW) rc₀ ω) ωs φ t)) ∧
      (∀ x, Pool.P0158.GoodV (Pool.P0203.DS (TW) ℓ ωs φ rc₀ x) (Pool.P0203.gateS (TW) ℓ ωs φ rc₀ x)
        (Pool.P0203.rS (TW) x) (Pool.P0158.rmax1 (Pool.P0203.rS (TW) x)) Ls T ω) ∧
      Pool.P0158.GoodV (Pool.P0216.DB (TW) ℓ rc₀) (fun _ _ => true) (fun _ => (TW).cB)
        (Pool.P0158.rmax1 (fun _ => (TW).cB)) Ls T ω ∧
      Pool.P0228.AlgOK (TW) ℓ ωs φ T
        (Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T κ (Pool.P0210.extR (TW) rc₀ ω))
        (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
        (Pool.P0243.rOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T ε κ Lc
          (Pool.P0210.extR (TW) rc₀ ω)) (Pool.P0210.extR (TW) rc₀ ω) with hGE
  have hbud := Pool.P0253.budget_twin P η ε L N G γ wE S KM ℓ ωs φ hD hLv hlev hG hγ hwE hε hη hL hN hwE' hG1 hκ.le
    T hTL rc₀ (Nat.zero_le T) (le_refl T) GE (fun ω h t ht => by
      rw [← Pool.P0253.sp_twin P η ε L N G γ wE S KM ℓ ωs φ]; exact h.1 t ht)
  calc _ ≤ ∑ ω : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) ω * (K0 + K1 *
          (if GE ω then Pool.P0154.isum (Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T κ
            (Pool.P0210.extR (TW) rc₀ ω)) 0 T else 0)) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hpw0 ω)
        by_cases hg : GE ω
        · rw [if_pos hg, if_pos hg]
          exact restD2_le_K (TW) ℓ ωs φ hD hLv hlev (Pool.P0210.extR (TW) rc₀ ω) T hlay hg.1 hLs hxm hxm1 hxr hn
            hTT hM hρ0 hB hρ hx0 hx Θn hΘn hΘ hcB Λbar hΛ0 hΛa hΛn _
            (Pool.P0243.vOK_nonneg P η L N G γ wE _ ℓ ωs φ rc₀ T hη κ _) _ hρOK xf hxf
        · rw [if_neg hg, if_neg hg]; linarith
    _ = K0 * ∑ ω : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) ω + K1 * ∑ ω : Fin T → RC (TW),
          Pool.P0202.pw (wR (TW)) ω * (if GE ω then Pool.P0154.isum (Pool.P0243.vOK P η L N G γ wE
            (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T κ (Pool.P0210.extR (TW) rc₀ ω)) 0 T else 0) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ K0 + K1 * (T * Pool.P0243.Cb η N G γ wE (∑ j : Fin P.D, (P.sl j : ℝ)) κ) := by
        rw [hsum1, mul_one]
        simp only [Nat.cast_zero, sub_zero] at hbud
        refine add_le_add_right (mul_le_mul_of_nonneg_left ?_ hK1) _
        convert hbud using 3 with ω
        by_cases hg : GE ω
        · rw [if_pos hg, if_pos hg]
        · rw [if_neg hg, if_neg hg]

end Twin

section Avg

attribute [local instance] Pool.P0082.coinFintype

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (M0 : Pool.P0201.MPar n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (KM : ℕ) [NeZero N]

local notation "MT" => Pool.P0245.mTwin M0 η ε L N G γ wE KM

open Classical in
/-- **The array average of P0258's probing remainder for P0245's finite-twin machine** `mTwin`, with the
self-rounding ALG's budgets read with the array's bits (P0277's `v`, `ρ₀`, `c = 0`, `r`): at most
`K₀ + K₁·T·Cb(Σ_j sl_j)` (`goodTermP2_twin_le` on every array; the bound does not depend on the array). -/
theorem exp_goodTermP2_twin (hD : 0 < M0.P.D) (hLv : 0 < M0.P.Lv) (hlev : ∀ r a, M0.P.lev r a + 1 < M0.P.Lv)
    (hG : 0 < G) (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 < η) (hwE' : M0.P.wE = wE)
    (hL : (MT).P.IsLaw) (hG1 : 1 ≤ G) {κ Lc : ℝ} (hκ : 0 < κ) (hLc : 0 ≤ Lc) {T : ℕ} (hTL : T ≤ 2 ^ L)
    (ℓ : LossSeq n) (rc₀ : RC (MT).P)
    (hlay : Pool.P0191.LayOK (MT).P.sl (MT).P.lay)
    {Ls xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ (MT).P.xr j) (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ)
    (hB : ∀ i, 0 < (MT).P.Bt i)
    (hρ : ∀ i, 1 ≤ i → ((MT).P.Bt (i - 1) : ℝ) ≤ ρ * (MT).P.Bt i) (hx0 : 1 / Pool.P0191.xrN (MT).P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (MT).P.xr i ≤ max M (TT / (nn * (MT).P.Bt i)))
    (Θn : ℕ) (hΘn : ∀ f, (MT).P.thr0 f ≤ Θn) (hΘ : (Θn : ℝ) ≤ Θ)
    (hcB : 0 ≤ (MT).P.cB) (Λbar : ℕ → ℝ) (hΛ0 : ∀ i, 0 ≤ Λbar i) (hΛa : ∀ i i', i ≤ i' → Λbar i' ≤ Λbar i)
    (hΛn : ∀ x c, (MT).P.E x ≤ c → (MT).P.Λ x c ≤ Λbar (curT (MT).P.E (MT).P.thr0 (MT).P.D (MT).P.Bt x (c + 1)))
    (xf : ℝ) (hxf : 0 ≤ xf) :
    ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr *
        Pool.P0258.goodTermP2 (MT).P (Pool.P0206.sh ℓ) (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr)
          (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr) hD hLv hlev rc₀ T Ls
          (Pool.P0243.vOK M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) (Pool.P0206.sh ℓ)
            (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr)
            rc₀ T κ)
          (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
          (Pool.P0243.rOK M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) (Pool.P0206.sh ℓ)
            (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr)
            rc₀ T ε κ Lc) xf ≤
      probeK0 (MT).P T Ls xmin M ρ nn TT Θ Θn Λbar (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) xf +
        probeK1 (MT).P * (T * Pool.P0243.Cb η N G γ wE (∑ j : Fin M0.P.D, (M0.P.sl j : ℝ)) κ) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNQ : 0 < (Pool.P0236.PG M0.P η ε L N G γ wE).N := hN
  have hLQ : (Pool.P0236.PG M0.P η ε L N G γ wE).IsLaw := hL
  have hw0 : ∀ arr : Pool.P0116.Arr (Pool.P0201.pp (MT)) T → Bool,
      0 ≤ Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr := by
    intro arr
    refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) arr
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [(MT).hps.1, (MT).hq.1]
    · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [(MT).hps.2, (MT).hq.2]
  have hw1 : ∑ arr : Pool.P0116.Arr (Pool.P0201.pp (MT)) T → Bool,
      Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr = 1 := Pool.P0048.sum_wtv _
  calc _ ≤ ∑ arr : Pool.P0116.Arr (Pool.P0201.pp (MT)) T → Bool, Pool.P0048.wtv (Pool.P0091.pC (MT).ps (MT).q) arr *
        (probeK0 (MT).P T Ls xmin M ρ nn TT Θ Θn Λbar (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) xf +
          probeK1 (MT).P * (T * Pool.P0243.Cb η N G γ wE (∑ j : Fin M0.P.D, (M0.P.sl j : ℝ)) κ)) :=
        Finset.sum_le_sum fun arr _ => mul_le_mul_of_nonneg_left
          (goodTermP2_twin_le M0.P η ε L N G γ wE (M0.Ns + 1) KM (Pool.P0206.sh ℓ)
            (Pool.P0082.ωsC (MT).P.E T (MT).P.D (MT).Lf (MT).P.K arr) (Pool.P0082.φC T (MT).P.D (MT).Lf (MT).P.K arr)
            hD hLv hlev hG hγ hwE hε hη.le hLQ hNQ hwE' hG1 hκ hLc hη T hTL rc₀ hlay hLs hxm hxm1 hxr hn hTT hM hρ0 hB
            hρ hx0 hx Θn hΘn hΘ hcB Λbar hΛ0 hΛa hΛn xf hxf) (hw0 arr)
    _ = _ := by rw [← Finset.sum_mul, hw1, one_mul]

end Avg

end Pool.P0289
