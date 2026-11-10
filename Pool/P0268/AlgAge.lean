import Pool.P0250.WalkParam
import Pool.P0249.AgeWalk

/-!
# P0250's ALG-term bound through P0249's AGE-RESTRICTED walk, with age-capped record margins
-/

namespace Pool.P0268

open Finset Real Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0231 Pool.P0242 Pool.P0250
open Pool.P0226 (sum_trunc αT αT_nonneg widV_mono2 widV_nonneg gT)

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (Pool.P0225.withAlgG P η L N G γ wE ρG).K → ι → Bool) (T : ℕ)
  (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

local notation "QQ" => Pool.P0225.withAlgG P η L N G γ wE ρG

/-- P0250's record margins `ΛP` with the age capped at P0238's thread lifetime `lenOf j` (equal to `ΛP` at every
reachable age; bounded per thread, so they can serve as rule margins with a per-thread clock bound). -/
noncomputable def ΛPc (T : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ) (Θn : ℕ) (j m : ℕ) : ℝ :=
  ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ j (min m (Pool.P0238.lenOf Θn T (QQ).Bt j))

theorem run_bound_param_age (Θn : ℕ) (hΘn : ∀ c, (QQ).thr0 c ≤ Θn) (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
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
    (hS : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ rc0 f)
      (Pool.P0203.gateS (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ rc0 f) (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) f)
      (Pool.P0158.rmax1 (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl
      (sp (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u))
    (hB : Pool.P0158.GoodV (Pool.P0216.DB (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ rc0) (fun _ _ => true)
      (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) (Pool.P0158.rmax1 (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)) Lb T
      (Pool.P0203.pre _ ω T))
    (hX : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN) (lossX P η L N G γ wE ρG ℓ x)
      (obsX P η L N G γ wE ρG ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρG ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (hXm : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN)
      (YB P η L N G γ wE ρG ℓ rc0) (bPolX P η L N G γ wE ρG ℓ rc0) (obsX P η L N G γ wE ρG ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (hA : Pool.P0149.StepGood (Pool.P0240.DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lt / κ) T
      (Pool.P0203.pre _ ω T))
    (hθ : 0 ≤ (QQ).θ) (hR1 : 1 ≤ (QQ).R) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hT : (QQ).Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    (i : Fin n) (harm : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).arm (cstar j a) = i)
    (hgF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false →
      Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.gateS (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a))
        (Pool.P0158.rmax1 (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a))) Ls T
        (Pool.P0203.pre (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ω T))
    (hfF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false → ∀ u, u < T →
      Pool.P0176.Fits (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl
        (sp (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ ω (Pool.P0065.forceS ωs (cstar j a))
          (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) u))
    (hΛ' : ∀ c u, ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn
        (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤ (QQ).Λ c u)
    (hTΘ : 0 ≤ Θ * (ρ * TT / nn))
    (h1 : 1 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ + BP P η L N G γ wE ρG Ls M) :
    ∑ u ∈ Finset.range T, (aPt P η L N G γ wE ρG ℓ ω ωs φ T u - gT ℓ T i u -
        (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u + slT P η L N G γ wE ρG ℓ ω ωs φ T rc0 κ u)) ≤
      T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 +
          BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) +
        walkW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ρ
            (fun j => nbad P η L N G γ wE ρG ℓ ω ωs φ T cstar j) := by
  have hR0 : (0 : ℝ) ≤ (QQ).R := by have : (1 : ℝ) ≤ (QQ).R := by exact_mod_cast hR1
                                    linarith
  have hα := αT_nonneg (ι := ι) η L T hη hδ
  have hΓ : 0 ≤ Lc / (2 * (wE * γ)) := div_nonneg hLc (by positivity)
  have hA0 : 0 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ := by
    unfold AP; have : 0 ≤ Lt / κ := div_nonneg hLt hκ.le
    have : 0 ≤ 2 * Ls / xmin := div_nonneg (by linarith) hxm.le
    positivity
  have hB0 : 0 ≤ BP P η L N G γ wE ρG Ls M := by unfold BP; positivity
  have hf : ∀ m : ℕ, (QQ).θ + (QQ).R * (2 * αT (ι := ι) η L T δ + 2 * (Lc / (2 * (wE * γ))) +
      Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m) + Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m + Lt / κ ≤
      ffP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) m := by
    intro m
    have hW := Wocc_le (xmin := xmin) (ρ := ρ) (nn := nn) (TT := TT) hLs hM hTΘ m
    unfold ffP AP BP
    nlinarith
  have H := Pool.P0249.run_bound_occG_age P η L N G γ wE ρG ℓ ω ωs φ T rc0 Θn hΘn hD hLv hlev hL hN hη hδ hρG hγ hwE0 hwE hTL hcB0 hLs hLb
    hLc hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hlay hS hfit hB hX hXm hA hθ hR1 hBt hT cstar hE hthr i
    harm hgF hfF (ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) hΛ'
    (ffP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M))
    (aaP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt)
    (ccP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D)
    (fun j => wP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D j)
    (fun j _ => aaP_nonneg hA0 hB0 j) (ccP_nonneg hA0 hB0)
    (fun j _ m hm => hbig_P hA0 hB0 hBt.pos j m hm) (fun m hm => hsmall_P hB0 m hm) hf
    (hfB_P hBt.last (by exact h1)) (fun j m hm => by unfold ΛPc; rw [min_eq_left hm]; exact le_rfl)
    (fun i' _ => hw_P i')
  refine H.trans ?_
  exact rhs_le_thread hA0 hB0 hBt.pos hρ (T : ℝ) _ (fun j => Nat.cast_nonneg _)

open Classical in
/-- **ALG's term in expectation** (fixed sampling/filter bits; P0234's `algTerm`, i.e. P0217's `algT` integrand form):
with the parameter family of `run_bound_param`,
`algTerm ≤ wE·E[[G]·(T·(A/Bt 0 + B/√(Bt 0)) + walkW(nBad) + Σ_{u<T} V_u)] + wE·T·P(¬G)`,
`V = (η/2)·VR + slT`, `G = GoodAll`. -/
theorem alg_expect_param_age (Θn : ℕ) (hΘn : ∀ c, (QQ).thr0 c ≤ Θn) (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
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
    (hΛ' : ∀ c u, ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn
        (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤ (QQ).Λ c u)
    (hTΘ : 0 ≤ Θ * (ρ * TT / nn))
    (h1 : 1 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ + BP P η L N G γ wE ρG Ls M) :
    Pool.P0234.algTerm (QQ) ℓ ωs φ rc0 T i ≤
      wE * ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
        (if GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω) then
          T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 +
              BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) +
            walkW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ρ
            (fun j => nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T cstar j) +
            ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
              slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u) else 0) +
      wE * T * ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
        (if GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) := by
  have hwQ : (QQ).wE = wE := hwE
  have h := alg_expect_of (QQ) ℓ ωs φ rc0 hL hN (by rw [hwQ]; exact hwE0.le) T i
    (fun ω => GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω))
    (fun ω => T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 +
                  BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) +
                walkW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ρ
            (fun j => nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T cstar j) +
                ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
                  slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u)) ?_
  · rw [hwQ] at h; exact h
  intro ω hg
  obtain ⟨hS, hfit, hB, hX, hXm, hA, hgF, hfF⟩ := hg
  have H := run_bound_param_age P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 Θn hΘn hD hLv hlev hL hN hη hδ hρG hγ
    hwE0 hwE hTL hcB0 hLs hLb hLc hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hlay hS hfit hB hX hXm hA hθ hR1
    hBt hT cstar hE hthr i harm hgF hfF hΛ' hTΘ h1
  have e : ∑ u ∈ Finset.range T, (aPt P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u - gT ℓ T i u -
        (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
          slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u)) =
      ∑ u ∈ Finset.range T, (aPol (QQ) ℓ ωs φ (Pool.P0210.extR (QQ) rc0 ω) u - ((ℓ u i).toNat : ℝ)) -
        ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
          slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' : u < T := Finset.mem_range.1 hu
    unfold aPt gT; rw [if_pos hu', if_pos hu']
  rw [e] at H
  linarith
open Classical in
/-- **ALG's term in expectation, final form** (fixed sampling/filter bits): with the family of `run_bound_param`,
`algTerm ≤ wE·(T·(A/Bt 0 + B/√(Bt 0)) + E[walkW(nBad)] + E[[G]·Σ_{u<T} V_u]) + wE·T·(P(¬FitA) + P(¬FitF)
+ 4|ι|(T+1)²e^{−Ls} + 2(T+1)²e^{−Lb} + (|ι|+1)(T+1)²e^{−Lc} + (T+1)²e^{−Lt})`. -/
theorem alg_expect_final_age (Θn : ℕ) (hΘn : ∀ c, (QQ).thr0 c ≤ Θn) (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
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
    (hΛ' : ∀ c u, ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn
        (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤ (QQ).Λ c u)
    (hTΘ : 0 ≤ Θ * (ρ * TT / nn))
    (h1 : 1 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ + BP P η L N G γ wE ρG Ls M)
    (hlayOK : Pool.P0191.LayOK (QQ).sl (QQ).lay) (hxr0 : ∀ j, 0 < (QQ).xr j) (hxr1 : ∀ j, (QQ).xr j ≤ 1)
    (hcw : (QQ).cB * (QQ).wB = 1) (hLs0 : 0 < Ls) (hLb0 : 0 < Lb) (hκ1 : κ ≤ 1) :
    Pool.P0234.algTerm (QQ) ℓ ωs φ rc0 T i ≤
      wE * (T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 +
          BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) +
        ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
            walkW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ρ (fun j => nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T cstar j) +
        ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
          (if GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω) then
            ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
              slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u) else 0)) +
      wE * T * (∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
            (if FitA P η L N G γ wE ρG ℓ ωs φ T (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) +
          ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
            (if FitF P η L N G γ wE ρG ℓ ωs φ T cstar (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) +
          2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls))) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lb) +
          Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) +
          ((T : ℝ) + 1) ^ 2 * Real.exp (-Lt)) := by
  classical
  have hAP := alg_expect_param_age P η L N G γ wE ρG ℓ ωs φ T rc0 Θn hΘn hD hLv hlev hL hN hη hδ hρG hγ hwE0 hwE hTL hcB0 hLs hLb hLc hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hlay hθ hR1 hBt hT cstar hE hthr i harm hΛ' hTΘ h1
  have hPG := prob_not_goodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN hD hLv hlev hlayOK hxr0 hxr1 hcw hγ hwE0 hwE
    (Ls := Ls) (Lb := Lb) (Lc := Lc) (Lt := Lt) (κ := κ) hLs0 hLb0 hκ hκ1 cstar
  have hp : ∀ ω : Fin T → RC (QQ), 0 ≤ Pool.P0202.pw (wR (QQ)) ω := fun ω => Pool.P0228.pw_nonneg (QQ) hL ω
  have hs1 : ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω = 1 := Pool.P0228.sum_pw (QQ) hL hN T
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
  have hC0 : 0 ≤ T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 +
          BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) := by
    have : 0 ≤ ((QQ).Bt 0 : ℝ) := Nat.cast_nonneg _
    positivity
  have hK0 : (0 : ℝ) ≤ 1 := zero_le_one
  have hnb : ∀ ω : Fin T → RC (QQ), 0 ≤ walkW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ)
      (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ρ
      (fun j => nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T cstar j) := fun ω =>
    walkW_nonneg hA0 hB0 hρ0 _ (fun j => by unfold nbad; exact Nat.cast_nonneg _)
  have hfirst := split_good (fun ω : Fin T → RC (QQ) => Pool.P0202.pw (wR (QQ)) ω) hp hs1 hC0 hK0 _ hnb
    (fun ω => ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
      slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u))
    (fun ω => GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω))
  beta_reduce at hfirst
  simp only [one_mul] at hfirst
  have hw0 : 0 ≤ wE := hwE0.le
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hfirst hw0
  have := mul_le_mul_of_nonneg_left hPG (mul_nonneg hw0 hT0)
  linarith


theorem ΛPc_eq (T : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ) (Θn j m : ℕ)
    (hm : m ≤ Pool.P0238.lenOf Θn T (QQ).Bt j) :
    ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn j m =
      ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ j m := by
  unfold ΛPc; rw [min_eq_left hm]

/-- **Per-thread bound of the capped margins**: `ΛPc j m ≤ ΛP j (lenOf j)` for every age `m` (`ΛP` is monotone in the
age: the B̂ width and P0222's `Wocc` are). -/
theorem ΛPc_le (T : ℕ) {δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (Θn j m : ℕ) (hcB : 0 ≤ (QQ).cB) (hLb : 0 ≤ Lb)
    (hLs : 0 ≤ Ls) (hM : 0 ≤ M) :
    ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn j m ≤
      ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ j (Pool.P0238.lenOf Θn T (QQ).Bt j) := by
  unfold ΛPc ΛP
  have hmin : min m (Pool.P0238.lenOf Θn T (QQ).Bt j) ≤ Pool.P0238.lenOf Θn T (QQ).Bt j := min_le_right _ _
  have h1 : Pool.P0158.widV ((min m (Pool.P0238.lenOf Θn T (QQ).Bt j) : ℕ) * (QQ).cB) (max 1 (QQ).cB) Lb ≤
      Pool.P0158.widV ((Pool.P0238.lenOf Θn T (QQ).Bt j : ℕ) * (QQ).cB) (max 1 (QQ).cB) Lb :=
    widV_mono2 (by positivity) (mul_le_mul_of_nonneg_right (by exact_mod_cast hmin) hcB) le_rfl hLb
  have h2 := Pool.P0222.Wocc_mono (xmin := xmin) (ρ := ρ) (nn := nn) (TT := TT) (Θ := Θ) hLs hM hmin
  linarith

/-- **The capped margins are below P0250's**: `ΛPc j m ≤ ΛP j m` at every age (`ΛP` is monotone in the age). -/
theorem ΛPc_le_ΛP (T : ℕ) {δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (Θn j m : ℕ) (hcB : 0 ≤ (QQ).cB) (hLb : 0 ≤ Lb)
    (hLs : 0 ≤ Ls) (hM : 0 ≤ M) :
    ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn j m ≤
      ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ j m := by
  unfold ΛPc ΛP
  have hmin : min m (Pool.P0238.lenOf Θn T (QQ).Bt j) ≤ m := min_le_left _ _
  have h1 : Pool.P0158.widV ((min m (Pool.P0238.lenOf Θn T (QQ).Bt j) : ℕ) * (QQ).cB) (max 1 (QQ).cB) Lb ≤
      Pool.P0158.widV ((m : ℕ) * (QQ).cB) (max 1 (QQ).cB) Lb :=
    widV_mono2 (by positivity) (mul_le_mul_of_nonneg_right (by exact_mod_cast hmin) hcB) le_rfl hLb
  have h2 := Pool.P0222.Wocc_mono (xmin := xmin) (ρ := ρ) (nn := nn) (TT := TT) (Θ := Θ) hLs hM hmin
  linarith

/-- **P0250's margin link implies this module's**: rule margins dominating P0250's `ΛP` dominate the capped `ΛPc`, so the
`hΛ'` of `run_bound_param_age` is implied by the `hΛ'` of P0250's `run_bound_param`. -/
theorem hΛ'_of_P0250 {δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (Θn : ℕ) (hcB : 0 ≤ (QQ).cB) (hLb : 0 ≤ Lb)
    (hLs : 0 ≤ Ls) (hM : 0 ≤ M)
    (h : ∀ c u, ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ
        (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤ (QQ).Λ c u) :
    ∀ c u, ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn
        (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤ (QQ).Λ c u :=
  fun c u => (ΛPc_le_ΛP P η L N G γ wE ρG T Θn _ _ hcB hLb hLs hM).trans (h c u)

end Pool.P0268
