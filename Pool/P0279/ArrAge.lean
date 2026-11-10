import Pool.P0266.Arr
import Pool.P0268.AlgAge

/-!
# ALG's term averaged over the array, for P0268's age-restricted family
-/

namespace Pool.P0279

open Finset Pool.P0194 Pool.P0212 Pool.P0176 Pool.P0200 Pool.P0001 Pool.P0050 Pool.P0266

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
/-- **ALG's term averaged over the sampling/filter array, AGE-RESTRICTED margins** (`algT_arr` on P0268's
`alg_expect_final_age`: P0249's walk with margins `ΛPc j m = ΛP j (min m (lenOf j))`, bounded per thread). (P0217's `E_arr[algT]` integrand form for P0225's
`withAlgG`; entry-order layout, schedule `levTh Ld`, P0250's parameter family): with P0259's level split `cz` and a
fine-level weight bound `Mw`,
`E_arr[algTerm] ≤ wE·(T·(A/Bt₀ + B/√Bt₀) + coarseSum + Mw·count) + wE·T·Cb(Σ_j sl_j)
  + wE·T·(2·(T·D·δs + T·D·(Lf+1)·K·delta) + 4|ι|(T+1)²e^{−Ls} + 2(T+1)²e^{−Lb} + (|ι|+1)(T+1)²e^{−Lc} + (T+1)²e^{−Lt})`. -/
theorem algT_arr_age (Θn : ℕ) (hΘn : ∀ c, (QQ).thr0 c ≤ Θn) (hD : 0 < P.D)
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
    (hΛ' : ∀ c u, Pool.P0268.ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn
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
  -- the schedule bounds, from `lev = levTh Ld Bt` and `Ld + 2 ≤ Lv`, `Ld ≤ Lf` (as in P0266's `algT_arr`)
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
  have hav := avg_le _ hw0 hs1 _ _ _ _ (fun arr => Pool.P0268.alg_expect_final_age P η L N G γ wE ρG ℓ (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr) (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T rc0 Θn hΘn
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

end Pool.P0279
