import Pool.P0279.ArrAge
import Pool.P0245.Glue

/-!
# ALG's term of the FINITE-TWIN machine, averaged over the array

P0245's `algT_twin_le` (the twin's ALG term ≤ the self-rounding ALG's term + `wE·T·ovf`, array by array) averaged over
the sampling/filter array, with the self-rounding term bounded by P0279's `algT_arr_age` (`ρG := ρStar`, `δ := ε`,
loss `sh ℓ`, array level `Lf := M0.Lf`, rates `ps := M0.ps`, `q := M0.q`).
-/

namespace Pool.P0281

open Finset Pool.P0194 Pool.P0212 Pool.P0176 Pool.P0200 Pool.P0001 Pool.P0050 Pool.P0266 Pool.P0279

attribute [local instance] Pool.P0082.coinFintype

open Pool.P0250 (AP BP ΛP ccP)

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (M0 : Pool.P0201.MPar n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ)
  (KM : ℕ) [NeZero N] (ℓ : LossSeq n) (T : ℕ) (rc₀ : RC (Pool.P0245.mTwin M0 η ε L N G γ wE KM).P)

local notation "QQ" => Pool.P0236.PG M0.P η ε L N G γ wE

set_option maxHeartbeats 8000000 in
open Classical in
/-- **ALG's term of the finite-twin machine `mTwin`, averaged over the sampling/filter array.** -/
theorem algT_arr_twin (Θn : ℕ) (hΘn : ∀ c, (QQ).thr0 c ≤ Θn) (hD : 0 < M0.P.D)
    (hL : (QQ).IsLaw) (hN : 0 < (QQ).N) (hη : 0 < η) (hε : 0 < ε) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : M0.P.wE = wE)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (QQ).cB)
    {Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (QQ).xr j)
    (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hBt0 : ∀ i, 0 < (QQ).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((QQ).Bt (i - 1) : ℝ) ≤ ρ * (QQ).Bt i) (hx0 : 1 / Pool.P0191.xrN (QQ).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QQ).xr i ≤ max M (TT / (nn * (QQ).Bt i)))
    (hΘ : ∀ f, ((QQ).thr0 f : ℝ) ≤ Θ)
    (hlay : (QQ).lay = Pool.P0176.sortLay (QQ).sl)
    (hθ : 0 ≤ (QQ).θ) (hR1 : 1 ≤ (QQ).R) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hT : (QQ).Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    (i : Fin n) (harm : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).arm (cstar j a) = i)
    (hΛ' : ∀ c u, Pool.P0268.ΛPc M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) T ε Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn
        (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤ (QQ).Λ c u)
    (hTΘ : 0 ≤ Θ * (ρ * TT / nn))
    (h1 : 1 ≤ AP M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) T ε Ls Lc Lt κ xmin M ρ nn TT Θ + BP M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) Ls M)
    (hlayOK : Pool.P0191.LayOK (QQ).sl (QQ).lay) (hxr0 : ∀ j, 0 < (QQ).xr j) (hxr1 : ∀ j, (QQ).xr j ≤ 1)
    (hcw : (QQ).cB * (QQ).wB = 1) (hLs0 : 0 < Ls) (hLb0 : 0 < Lb) (hκ1 : κ ≤ 1)
    {Ld : ℕ} (hlevT : (QQ).lev = Pool.P0085.levTh Ld (QQ).Bt) (hLv2 : Ld + 2 ≤ (QQ).Lv) (hLdf : Ld ≤ M0.Lf)
    (hps0 : 0 < M0.ps) (hps1 : M0.ps ≤ 1) (hq0 : 0 ≤ M0.q) (hq1 : M0.q < 1)
    (hEm : Monotone (QQ).E) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hTθ : 1 / xmin * T ≤ 2 ^ ((QQ).R - 1) * (QQ).θ) (Mr : ℝ) (kk : ℕ) (hM0 : 16 * (QQ).R ≤ Mr)
    (hk : 4 * (QQ).R * kk ≤ Mr) (hp : M0.q * (Real.exp 1 - 1) ≤ 1 / (32 * (QQ).R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < T → r < (QQ).D →
      ∑ F ∈ (Finset.univ.filter fun c => (QQ).E c = a ∧ (QQ).thr0 c = r).powerset,
        M0.ps ^ F.card * (1 - M0.ps) ^ ((Finset.univ.filter fun c => (QQ).E c = a ∧ (QQ).thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : Mr ≤ S')
    (hρS : (1 - 1 / (4 * (QQ).R : ℝ)) ^ (QQ).K * ((S' : ℝ) + (s0 + (QQ).D * (QQ).Lv * S')) ≤ S')
    (hsl : ∀ j, ((QQ).D : ℝ) * ((s0 + (QQ).D * (QQ).Lv * S') + ((QQ).Lv - 1 : ℕ) * S') + (QQ).D * s0 + 1 ≤ (QQ).sl j)
    (hG1 : 1 ≤ G) (Mw : ℝ) (hMw : 0 ≤ Mw) (cz : ℕ → Prop) [DecidablePred cz]
    (hMa : ∀ j, 1 ≤ j → j < (QQ).D → ¬ cz j → ρ * (AP M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) T ε Ls Lc Lt κ xmin M ρ nn TT Θ +
      BP M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) Ls M * √((QQ).Bt j : ℝ)) ≤ Mw)
    (hMc : ccP (AP M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) T ε Ls Lc Lt κ xmin M ρ nn TT Θ) (BP M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) Ls M) (QQ).Bt (QQ).D ≤ Mw)
    (hTK : T ≤ KM) :
    ∑ arr : Pool.P0116.Arr (Pool.P0201.pp (Pool.P0245.mTwin M0 η ε L N G γ wE KM)) T → Bool,
        Pool.P0048.wtv (Pool.P0091.pC M0.ps M0.q) arr * Pool.P0217.algT (Pool.P0245.mTwin M0 η ε L N G γ wE KM) T ℓ rc₀ i arr ≤
      wE * (T * (AP M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) T ε Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 + BP M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) Ls M / √((QQ).Bt 0 : ℝ)) +
          (Pool.P0259.coarseSum T (QQ).D (QQ).Bt cz (aW (AP M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) T ε Ls Lc Lt κ xmin M ρ nn TT Θ) (BP M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) Ls M) (QQ).Bt ρ) + Mw * (((QQ).D * (QQ).Lv * (s0 + (QQ).D * (QQ).Lv * S' + 1) : ℝ) /
          (M0.ps * (1 - M0.q) ^ ((QQ).K * ((QQ).D * (2 * Ld + T / 2 ^ Ld + 1)))) +
        (QQ).D * T * (T * (QQ).D * δs + T * (QQ).D * (M0.Lf + 1) * (QQ).K * Pool.P0042.delta (Fintype.card ι) M0.q (QQ).R kk Mr)))) +
        wE * (T * Pool.P0243.Cb η N G γ wE (∑ j : Fin (QQ).D, ((QQ).sl j : ℝ)) κ) +
        wE * T * (2 * (T * (QQ).D * δs + T * (QQ).D * (M0.Lf + 1) * (QQ).K * Pool.P0042.delta (Fintype.card ι) M0.q (QQ).R kk Mr) + (2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls))) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lb) +
          Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) +
          ((T : ℝ) + 1) ^ 2 * Real.exp (-Lt))) +
        M0.P.wE * T * ∑ arr : Pool.P0116.Arr (Pool.P0201.pp (Pool.P0245.mTwin M0 η ε L N G γ wE KM)) T → Bool,
          Pool.P0048.wtv (Pool.P0091.pC M0.ps M0.q) arr * Pool.P0217.ovf (Pool.P0245.mTwin M0 η ε L N G γ wE KM) T ℓ rc₀ arr := by
  classical
  have hw0 : ∀ arr : Pool.P0116.Arr (Pool.P0201.pp (Pool.P0245.mTwin M0 η ε L N G γ wE KM)) T → Bool, 0 ≤ Pool.P0048.wtv (Pool.P0091.pC M0.ps M0.q) arr := fun arr =>
    Pool.P0048.wtv_nonneg (fun x => by
        rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith)
      (fun x => by rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith) arr
  have hLv : 0 < M0.P.Lv := by change 0 < (QQ).Lv; omega
  have hlev : ∀ r a, M0.P.lev r a + 1 < M0.P.Lv := fun r a => by
    change (QQ).lev r a + 1 < (QQ).Lv
    have := Pool.P0062.levPR_le Ld ((a + 1) / (QQ).Bt r - 1)
    rw [hlevT]; unfold Pool.P0085.levTh; omega
  have hG : 0 < G := hG1
  have hwE0' : 0 ≤ M0.P.wE := hwE ▸ hwE0.le
  -- the twin's ALG term, array by array (P0245)
  have key : ∑ arr : Pool.P0116.Arr (Pool.P0201.pp (Pool.P0245.mTwin M0 η ε L N G γ wE KM)) T → Bool, Pool.P0048.wtv (Pool.P0091.pC M0.ps M0.q) arr * Pool.P0217.algT (Pool.P0245.mTwin M0 η ε L N G γ wE KM) T ℓ rc₀ i arr ≤
      ∑ arr : Pool.P0116.Arr (Pool.P0201.pp (Pool.P0245.mTwin M0 η ε L N G γ wE KM)) T → Bool, Pool.P0048.wtv (Pool.P0091.pC M0.ps M0.q) arr *
        Pool.P0234.algTerm (QQ) (Pool.P0206.sh ℓ) (Pool.P0082.ωsC (QQ).E T (QQ).D M0.Lf (QQ).K arr)
          (Pool.P0082.φC T (QQ).D M0.Lf (QQ).K arr) rc₀ T i +
      M0.P.wE * T * ∑ arr : Pool.P0116.Arr (Pool.P0201.pp (Pool.P0245.mTwin M0 η ε L N G γ wE KM)) T → Bool, Pool.P0048.wtv (Pool.P0091.pC M0.ps M0.q) arr * Pool.P0217.ovf (Pool.P0245.mTwin M0 η ε L N G γ wE KM) T ℓ rc₀ arr := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun arr _ => ?_
    have h := Pool.P0245.algT_twin_le M0 η ε L N G γ wE KM hD hLv hlev hG hγ hwE0 hε hη.le hwE0' hL T hTL hTK ℓ rc₀ i arr
    have h' := mul_le_mul_of_nonneg_left h (hw0 arr)
    have e : Pool.P0234.algTerm (QQ) (Pool.P0206.sh ℓ) (Pool.P0082.ωsC (QQ).E T (QQ).D M0.Lf (QQ).K arr)
          (Pool.P0082.φC T (QQ).D M0.Lf (QQ).K arr) rc₀ T i =
        ∑ u ∈ range T, ∑ ω' : Fin u → RC (QQ), Pool.P0202.pw (wR (QQ)) ω' *
          (M0.P.wE * (aPol (QQ) (Pool.P0206.sh ℓ)
            (Pool.P0082.ωsC M0.P.E T M0.P.D M0.Lf M0.P.K arr) (Pool.P0082.φC T M0.P.D M0.Lf M0.P.K arr)
            (Pool.P0210.extR (QQ) rc₀ ω') u - ((Pool.P0206.sh ℓ u i).toNat : ℝ))) := rfl
    rw [e]
    calc _ ≤ _ := h'
      _ = _ := by ring
  refine key.trans ?_
  have hA := algT_arr_age M0.P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) (Pool.P0206.sh ℓ) T rc₀ Θn hΘn hD hL hN hη
    hε.le (fun σ V ch bit => Pool.P0225.abs_ρStar_le η L N G γ wE ε hε hη.le σ V ch bit) hγ hwE0 hwE hTL hcB0 hLs hLb hLc
    hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hlay hθ hR1 hBt hT cstar hE hthr i harm hΛ' hTΘ h1 hlayOK hxr0
    hxr1 hcw hLs0 hLb0 hκ1 hlevT hLv2 hLdf hps0 hps1 hq0 hq1 hEm hBm hTθ Mr kk hM0 hk hp s0 δs hs S' hM0S hρS hsl hG1 Mw
    hMw cz hMa hMc
  have hA' : ∑ arr : Pool.P0116.Arr (Pool.P0201.pp (Pool.P0245.mTwin M0 η ε L N G γ wE KM)) T → Bool, Pool.P0048.wtv (Pool.P0091.pC M0.ps M0.q) arr *
      Pool.P0234.algTerm (QQ) (Pool.P0206.sh ℓ) (Pool.P0082.ωsC (QQ).E T (QQ).D M0.Lf (QQ).K arr)
        (Pool.P0082.φC T (QQ).D M0.Lf (QQ).K arr) rc₀ T i ≤ _ := hA
  linarith

end Pool.P0281
