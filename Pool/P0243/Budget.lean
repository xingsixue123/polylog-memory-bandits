import Pool.P0243.AlgOK
import Pool.P0243.VRm
import Pool.P0223.CreditD

/-!
# ALG's budget `vOK` in expectation, on fitting rounds
-/

namespace Pool.P0243

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0231 Pool.P0240 Pool.P0210
open Pool.P0227 (supp supp_le)

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (Pool.P0225.withAlgG P η L N G γ wE ρG).K → ι → Bool)
  (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (T : ℕ)

local notation "PA" => Pool.P0225.withAlgG P η L N G γ wE ρG

/-- The per-round budget constant for at most `S` active copies:
`(S + 1)·((η/2)·(1 + 1/(4Nγ))/wE + γ + 2/N + κ·(1/wE + 1/(4N·wE·γ))) + wE/G`. -/
noncomputable def Cb (S κ : ℝ) : ℝ :=
  (S + 1) * (η / 2 * ((1 + 1 / (4 * N * γ)) / wE) + (γ + 2 / N + κ * (1 / wE + 1 / (4 * N * (wE * γ))))) + wE / G

/-- The budget's part that does not depend on the round's coin: `(S + 1)·(γ + 2/N + κ·(…)) + wE/G`. -/
noncomputable def Kb (S κ : ℝ) : ℝ := (S + 1) * (γ + 2 / N + κ * (1 / wE + 1 / (4 * N * (wE * γ)))) + wE / G

/-- **Pathwise, on a fitting round**: `vOK u ≤ (η/2)·VRp + Kb(S')` with `S' = Σ_j sl_j` (P0223's `card_active_le`). -/
theorem vOK_le_VRp (hN : 0 < (PA).N) (hwE : P.wE = wE) (hwE0 : 0 < wE) (hγ : 0 < γ) (hG : 1 ≤ G) {κ : ℝ}
    (hκ : 0 ≤ κ) (hTL : T ≤ 2 ^ L) (ω : ℕ → RC PA) {u : ℕ} (hu : u < T)
    (hfit : Pool.P0176.Fits (PA).Lv (PA).sl (sp PA ℓ ω ωs φ u)) :
    vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ ω u ≤
      η / 2 * VRp P η L N G γ wE ρG ℓ ωs φ rc0 u (Pool.P0203.pre _ ω u) (ω u) +
        Kb N G γ wE (∑ j : Fin (PA).D, ((PA).sl j : ℝ)) κ := by
  have h := vOK_le P η L N G γ wE ρG ℓ ωs φ rc0 T hN hwE hwE0 hγ hG hκ ω (u := u) (by omega)
  rw [VR_eq_VRp P η L N G γ wE ρG ℓ ωs φ rc0 T ω hu] at h
  have hc := Pool.P0223.card_active_le PA ℓ ωs φ hfit
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 ≤ γ + 2 / N + κ * (1 / wE + 1 / (4 * N * (wE * γ))) := by positivity
  have := mul_le_mul_of_nonneg_right (add_le_add_right hc 1) hc0
  unfold Kb
  linarith

theorem Cb_nonneg (hη : 0 ≤ η) (hN : 0 < N) (hwE0 : 0 < wE) (hγ : 0 < γ) {S κ : ℝ} (hS : 0 ≤ S) (hκ : 0 ≤ κ) :
    0 ≤ Cb η N G γ wE S κ := by
  unfold Cb
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

open Classical in
/-- **ALG's budget in expectation on a fitting round.** For `u < T ≤ 2^L`, over P0194's round coins (prefixes of length
`T`, extended by `rc0`): `E[[round u fits]·vOK_u] ≤ Cb(Σ_j sl_j)`. Via P0224's conditional mean of `VR` (`meanV_le`,
ported to `withAlgG`), P0227's slack bound and P0223's `card_active_le`; the fit of round `u` is read from the coins
before `u`. -/
theorem budget_round (hL : (PA).IsLaw) (hN : 0 < (PA).N) (hη : 0 ≤ η) (hwE : P.wE = wE) (hwE0 : 0 < wE)
    (hγ : 0 < γ) (hG : 1 ≤ G) {κ : ℝ} (hκ : 0 ≤ κ) (hTL : T ≤ 2 ^ L) {u : ℕ} (hu : u < T) :
    ∑ ω : Fin T → RC PA, Pool.P0202.pw (wR PA) ω *
      (if Pool.P0176.Fits (PA).Lv (PA).sl (sp PA ℓ (extR PA rc0 ω) ωs φ u)
        then vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ (extR PA rc0 ω) u else 0) ≤
      Cb η N G γ wE (∑ j : Fin (PA).D, ((PA).sl j : ℝ)) κ := by
  set S := ∑ j : Fin (PA).D, ((PA).sl j : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hN0 : 0 < N := hN
  have hN0r : (0 : ℝ) < N := by exact_mod_cast hN
  set K := Kb N G γ wE S κ
  have hK : 0 ≤ K := by unfold K Kb; positivity
  have h1 : ∑ rc, wR PA rc = 1 := sum_wR PA hL hN
  set F : (Fin (u + 1) → RC PA) → ℝ := fun ω'' =>
    if Pool.P0176.Fits (PA).Lv (PA).sl (sp PA ℓ (extR PA rc0 ω'') ωs φ u)
    then η / 2 * VRp P η L N G γ wE ρG ℓ ωs φ rc0 u (Fin.init ω'') (ω'' (Fin.last u)) + K else 0
  have hu1 : u + 1 ≤ T := hu
  -- step 1: pointwise bound by a function of the prefix of length `u + 1`
  have hpt : ∀ ω : Fin T → RC PA, Pool.P0202.pw (wR PA) ω *
      (if Pool.P0176.Fits (PA).Lv (PA).sl (sp PA ℓ (extR PA rc0 ω) ωs φ u)
        then vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ (extR PA rc0 ω) u else 0) ≤
      Pool.P0202.pw (wR PA) ω * F (Pool.P0202.pre hu1 ω) := by
    intro ω
    refine mul_le_mul_of_nonneg_left ?_ (Pool.P0228.pw_nonneg PA hL ω)
    have hag : Agree PA (extR PA rc0 (Pool.P0202.pre hu1 ω)) (extR PA rc0 ω) u :=
      fun v hv => agree_pre PA rc0 hu1 ω v (by omega)
    have hsp : sp PA ℓ (extR PA rc0 (Pool.P0202.pre hu1 ω)) ωs φ u = sp PA ℓ (extR PA rc0 ω) ωs φ u :=
      sp_congr ωs φ u hag
    have hinit : Fin.init (Pool.P0202.pre hu1 ω) = Pool.P0203.pre PA (extR PA rc0 ω) u := by
      funext i
      simp only [Fin.init, Pool.P0202.pre, Pool.P0203.pre, extR]
      rw [dif_pos (by omega)]; rfl
    have hlast : (Pool.P0202.pre hu1 ω) (Fin.last u) = extR PA rc0 ω u := by
      simp only [Pool.P0202.pre, extR]
      rw [dif_pos hu]; rfl
    simp only [F, hsp, hinit, hlast]
    split_ifs with hfit
    · exact vOK_le_VRp P η L N G γ wE ρG ℓ ωs φ rc0 T hN hwE hwE0 hγ hG hκ hTL _ hu hfit
    · exact le_rfl
  -- step 2: integrate out the future and the round's coin
  have hpre := Pool.P0202.sum_pw_prefix h1 (u + 1) F T hu1
  rw [Pool.P0202.sum_snoc_pw] at hpre
  have hin : ∀ ω' : Fin u → RC PA, ∑ z, wR PA z * F (Fin.snoc ω' z : Fin (u + 1) → RC PA) ≤
      Cb η N G γ wE S κ := by
    intro ω'
    have hFz : ∀ z, F (Fin.snoc ω' z : Fin (u + 1) → RC PA) =
        if Pool.P0176.Fits (PA).Lv (PA).sl (sp PA ℓ (extR PA rc0 ω') ωs φ u)
        then η / 2 * VRp P η L N G γ wE ρG ℓ ωs φ rc0 u ω' z + K else 0 := by
      intro z
      have hag : Agree PA (extR PA rc0 (Fin.snoc ω' z : Fin (u + 1) → RC PA)) (extR PA rc0 ω') u :=
        Pool.P0203.extD_snoc_agree PA rc0 ω' z
      simp only [F, sp_congr ωs φ u hag, Fin.init_snoc, Fin.snoc_last]
    simp_rw [hFz]
    split_ifs with hfit
    · have hk : (σX P η L N G γ wE ρG ℓ ωs φ rc0 u ω').k < 2 ^ L :=
        lt_of_le_of_lt (σs_k_le P η L N G γ wE ρG ℓ ωs φ rc0 u ω') (by omega)
      have hm := meanV_le P η L N G γ wE ρG ℓ ωs φ rc0 hL hN hγ hwE0 hwE u ω' hk
      simp_rw [Pool.P0203.nuD_toReal PA hL hN] at hm
      have hsupp : ((univ.filter fun f => pmarg η L (σX P η L N G γ wE ρG ℓ ωs φ rc0 u ω')
          (VX P η L N G γ wE ρG ℓ ωs φ rc0 u ω') f ≠ 0).card : ℝ) ≤ S + 1 := by
        have h2 := supp_le (η := η) (L := L) (σX P η L N G γ wE ρG ℓ ωs φ rc0 u ω')
          (VX P η L N G γ wE ρG ℓ ωs φ rc0 u ω')
        have h3 := Pool.P0223.card_active_le PA ℓ ωs φ hfit
        have h2' : ((univ.filter fun f => pmarg η L (σX P η L N G γ wE ρG ℓ ωs φ rc0 u ω')
            (VX P η L N G γ wE ρG ℓ ωs φ rc0 u ω') f ≠ 0).card : ℝ) ≤
            (VX P η L N G γ wE ρG ℓ ωs φ rc0 u ω').card + 1 := by exact_mod_cast h2
        have : (VX P η L N G γ wE ρG ℓ ωs φ rc0 u ω').card = (active PA ℓ (extR PA rc0 ω') ωs φ u).card := rfl
        rw [this] at h2'
        linarith
      have hc1 : 0 ≤ (1 + 1 / (4 * N * γ)) / wE := by positivity
      have hmul := mul_le_mul_of_nonneg_right hsupp hc1
      have e : ∑ z, wR PA z * (η / 2 * VRp P η L N G γ wE ρG ℓ ωs φ rc0 u ω' z + K) =
          η / 2 * ∑ z, wR PA z * VRp P η L N G γ wE ρG ℓ ωs φ rc0 u ω' z + K := by
        rw [show (∑ z, wR PA z * (η / 2 * VRp P η L N G γ wE ρG ℓ ωs φ rc0 u ω' z + K)) =
          ∑ z, (η / 2 * (wR PA z * VRp P η L N G γ wE ρG ℓ ωs φ rc0 u ω' z) + K * wR PA z) from
            Finset.sum_congr rfl fun z _ => by ring]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, mul_one]
      rw [e]
      have hm' : ∑ z, wR PA z * VRp P η L N G γ wE ρG ℓ ωs φ rc0 u ω' z ≤ (S + 1) * ((1 + 1 / (4 * N * γ)) / wE) := by
        have : ((univ.filter fun f => pmarg η L (σX P η L N G γ wE ρG ℓ ωs φ rc0 u ω')
            (VX P η L N G γ wE ρG ℓ ωs φ rc0 u ω') f ≠ 0).card : ℝ) * (1 + 1 / (4 * N * γ)) / wE =
            ((univ.filter fun f => pmarg η L (σX P η L N G γ wE ρG ℓ ωs φ rc0 u ω')
            (VX P η L N G γ wE ρG ℓ ωs φ rc0 u ω') f ≠ 0).card : ℝ) * ((1 + 1 / (4 * N * γ)) / wE) := by ring
        linarith
      have := mul_le_mul_of_nonneg_left hm' (by linarith : (0 : ℝ) ≤ η / 2)
      unfold Cb
      unfold K Kb at *
      nlinarith
    · simp only [mul_zero, Finset.sum_const_zero]
      exact Cb_nonneg η N G γ wE hη hN0 hwE0 hγ hS hκ
  calc _ ≤ ∑ ω : Fin T → RC PA, Pool.P0202.pw (wR PA) ω * F (Pool.P0202.pre hu1 ω) :=
        Finset.sum_le_sum fun ω _ => hpt ω
    _ = ∑ ω' : Fin u → RC PA, Pool.P0202.pw (wR PA) ω' * ∑ z, wR PA z * F (Fin.snoc ω' z) := hpre
    _ ≤ ∑ ω' : Fin u → RC PA, Pool.P0202.pw (wR PA) ω' * Cb η N G γ wE S κ :=
        Finset.sum_le_sum fun ω' _ => mul_le_mul_of_nonneg_left (hin ω') (Pool.P0228.pw_nonneg PA hL ω')
    _ = Cb η N G γ wE S κ := by rw [← Finset.sum_mul, Pool.P0228.sum_pw PA hL hN, one_mul]

open Classical in
/-- **Summed**: on the event that every round before `T` fits, `E[[fits]·Σ_{[a,b)} vOK] ≤ (b − a)·Cb(Σ_j sl_j)` for
`b ≤ T ≤ 2^L`. -/
theorem budget_sum (hL : (PA).IsLaw) (hN : 0 < (PA).N) (hη : 0 ≤ η) (hwE : P.wE = wE) (hwE0 : 0 < wE)
    (hγ : 0 < γ) (hG : 1 ≤ G) {κ : ℝ} (hκ : 0 ≤ κ) (hTL : T ≤ 2 ^ L) {a b : ℕ} (hab : a ≤ b) (hbT : b ≤ T) :
    ∑ ω : Fin T → RC PA, Pool.P0202.pw (wR PA) ω *
      (if ∀ t < T, Pool.P0176.Fits (PA).Lv (PA).sl (sp PA ℓ (extR PA rc0 ω) ωs φ t)
        then Pool.P0154.isum (vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ (extR PA rc0 ω)) a b else 0) ≤
      ((b : ℝ) - a) * Cb η N G γ wE (∑ j : Fin (PA).D, ((PA).sl j : ℝ)) κ := by
  have hpt : ∀ ω : Fin T → RC PA, Pool.P0202.pw (wR PA) ω *
      (if ∀ t < T, Pool.P0176.Fits (PA).Lv (PA).sl (sp PA ℓ (extR PA rc0 ω) ωs φ t)
        then Pool.P0154.isum (vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ (extR PA rc0 ω)) a b else 0) ≤
      ∑ u ∈ Ico a b, Pool.P0202.pw (wR PA) ω *
        (if Pool.P0176.Fits (PA).Lv (PA).sl (sp PA ℓ (extR PA rc0 ω) ωs φ u)
          then vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ (extR PA rc0 ω) u else 0) := by
    intro ω
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (Pool.P0228.pw_nonneg PA hL ω)
    split_ifs with hall
    · unfold Pool.P0154.isum
      refine Finset.sum_le_sum fun u hu => ?_
      simp only [Finset.mem_Ico] at hu
      rw [if_pos (hall u (by omega))]
    · exact Finset.sum_nonneg fun u _ => by
        split_ifs
        · exact vOK_nonneg P η L N G γ wE ρG ℓ ωs φ rc0 T hη κ _ u
        · exact le_rfl
  calc _ ≤ ∑ ω : Fin T → RC PA, ∑ u ∈ Ico a b, Pool.P0202.pw (wR PA) ω *
        (if Pool.P0176.Fits (PA).Lv (PA).sl (sp PA ℓ (extR PA rc0 ω) ωs φ u)
          then vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ (extR PA rc0 ω) u else 0) :=
        Finset.sum_le_sum fun ω _ => hpt ω
    _ = ∑ u ∈ Ico a b, ∑ ω : Fin T → RC PA, Pool.P0202.pw (wR PA) ω *
        (if Pool.P0176.Fits (PA).Lv (PA).sl (sp PA ℓ (extR PA rc0 ω) ωs φ u)
          then vOK P η L N G γ wE ρG ℓ ωs φ rc0 T κ (extR PA rc0 ω) u else 0) := Finset.sum_comm
    _ ≤ ∑ _u ∈ Ico a b, Cb η N G γ wE (∑ j : Fin (PA).D, ((PA).sl j : ℝ)) κ :=
        Finset.sum_le_sum fun u hu => by
          simp only [Finset.mem_Ico] at hu
          exact budget_round P η L N G γ wE ρG ℓ ωs φ rc0 T hL hN hη hwE hwE0 hγ hG hκ hTL (by omega)
    _ = _ := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hab]

end Pool.P0243
