import Pool.P0236.Run
import Pool.P0228.ExpD
import Pool.P0243.Budget

/-!
# ALG's interval guarantees transfer from the self-rounding ALG to P0236's finite twin on fitting paths
-/

namespace Pool.P0253

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0212 Pool.P0236

variable {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι]
  (P : ParD n ι) (η ε : ℝ) (L N G : ℕ) (γ wE : ℝ) (S KM : ℕ)

local notation "QG" => Pool.P0236.PG P η ε L N G γ wE
local notation "TW" => Pool.P0236.withTwin P η ε L N G γ wE S KM

variable (ℓ : LossSeq n) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (Pool.P0236.PG P η ε L N G γ wE).K → ι → Bool)

theorem bPol_twin (ω : ℕ → RC (QG)) (u : ℕ) : bPol (TW) ℓ ω u = bPol (QG) ℓ ω u := by
  unfold bPol
  rw [show sB (TW) ℓ ω u = sB (QG) ℓ ω u from sB_swap _ ℓ ω u]
  rfl

theorem wR_twin (rc : RC (QG)) : wR (TW) rc = wR (QG) rc := by
  rcases rc with ⟨_ | _ | ⟨j, s⟩, d, y, z⟩ <;> rfl

theorem pw_twin {T : ℕ} (ω : Fin T → RC (QG)) : Pool.P0202.pw (wR (TW)) ω = Pool.P0202.pw (wR (QG)) ω := by
  unfold Pool.P0202.pw
  exact Finset.prod_congr rfl fun j _ => wR_twin P η ε L N G γ wE S KM (ω j)

theorem active_twin (ω : ℕ → RC (QG)) (u : ℕ) : active (TW) ℓ ω ωs φ u = active (QG) ℓ ω ωs φ u :=
  active_swap _ ℓ ω ωs φ u

theorem sp_twin (ω : ℕ → RC (QG)) (u : ℕ) : sp (TW) ℓ ω ωs φ u = sp (QG) ℓ ω ωs φ u := by
  unfold sp; rw [show pool (TW) ℓ ω ωs φ u = pool (QG) ℓ ω ωs φ u from pool_swap _ ℓ ω ωs φ u]; rfl


/-- Fitting threads (with `Σ_j sl_j + 1 ≤ S`) give P0236's fit hypothesis `|active| + 1 ≤ S`. -/
theorem hfit_of_fits (hS : (∑ j : Fin P.D, (P.sl j : ℝ)) + 1 ≤ S) (ω : ℕ → RC (QG)) (T : ℕ)
    (hfit : ∀ t < T, Pool.P0176.Fits (QG).Lv (QG).sl (sp (QG) ℓ ω ωs φ t)) :
    ∀ u < T, (active (QG) ℓ ω ωs φ u).card + 1 ≤ S := by
  intro u hu
  have h := Pool.P0223.card_active_le (QG) ℓ ωs φ (hfit u hu)
  have h2 : ((active (QG) ℓ ω ωs φ u).card : ℝ) + 1 ≤ S := by
    have : (∑ j : Fin (QG).D, ((QG).sl j : ℝ)) = ∑ j : Fin P.D, (P.sl j : ℝ) := rfl
    linarith
  exact_mod_cast h2

variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
  (hG : 0 < G) (hγ : 0 < γ) (hwE : 0 < wE) (hε : 0 < ε) (hη : 0 ≤ η)
include hD hLv hlev hG hγ hwE hε hη

/-- **On a fitting path, P0228's `AlgOK` is the same for the finite twin and the self-rounding ALG** (any budgets):
BASE, the active sets and the losses do not depend on the ALG (P0236's `swapA` lemmas), and ALG's policy losses
before `T` agree (P0236's `aPol_twin`). -/
theorem algOK_twin_iff (T : ℕ) (hTL : T ≤ 2 ^ L) (hTK : T ≤ KM) (ω : ℕ → RC (QG))
    (hfit : ∀ u < T, (active (QG) ℓ ω ωs φ u).card + 1 ≤ S) (v : ℕ → ℝ) (ρ₀ c : ℝ) (r : ι → ℕ → ℝ) :
    Pool.P0228.AlgOK (TW) ℓ ωs φ T v ρ₀ c r ω ↔ Pool.P0228.AlgOK (QG) ℓ ωs φ T v ρ₀ c r ω := by
  have ha : ∀ u < T, aPol (TW) ℓ ωs φ ω u = aPol (QG) ℓ ωs φ ω u := fun u hu =>
    aPol_twin P η ε L N G γ wE ℓ ω ωs φ hD hLv hlev hG hγ hwE hε hη T hTL hTK hfit hu
  have hI : ∀ a b, b ≤ T → Pool.P0154.isum (fun u => bPol (TW) ℓ ω u - aPol (TW) ℓ ωs φ ω u) a b =
      Pool.P0154.isum (fun u => bPol (QG) ℓ ω u - aPol (QG) ℓ ωs φ ω u) a b := by
    intro a b hb
    unfold Pool.P0154.isum
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Finset.mem_Ico] at hu
    beta_reduce
    rw [ha u (by omega), bPol_twin P η ε L N G γ wE S KM ℓ ω u]
  have hJ : ∀ a b, b ≤ T → Pool.P0154.isum (fun u => aPol (TW) ℓ ωs φ ω u) a b =
      Pool.P0154.isum (fun u => aPol (QG) ℓ ωs φ ω u) a b := by
    intro a b hb
    unfold Pool.P0154.isum
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Finset.mem_Ico] at hu
    beta_reduce
    rw [ha u (by omega)]
  unfold Pool.P0228.AlgOK
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b hab hbT => by rw [← hI a b hbT]; exact h1 a b hab hbT, fun x t htT hEt hact => ?_⟩
    rw [← hJ _ _ htT]
    exact h2 x t htT hEt (fun u h1 h2 => by rw [active_twin]; exact hact u h1 h2)
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b hab hbT => by rw [hI a b hbT]; exact h1 a b hab hbT, fun x t htT hEt hact => ?_⟩
    rw [hJ _ _ htT]
    exact h2 x t htT hEt (fun u h1 h2 => by rw [← active_twin]; exact hact u h1 h2)

open Classical in
/-- **`P(¬AlgOK)` for the finite twin** is at most that of the self-rounding ALG plus the probability that some thread
does not fit before `T` (path-dependent budgets `v`, `r`; `Σ_j sl_j + 1 ≤ S`). -/
theorem prob_not_algOK_twin (hS : (∑ j : Fin P.D, (P.sl j : ℝ)) + 1 ≤ S) (hL : (QG).IsLaw) (T : ℕ)
    (hTL : T ≤ 2 ^ L) (hTK : T ≤ KM) (rc₀ : RC (TW)) (v : (ℕ → RC (TW)) → ℕ → ℝ) (ρ₀ c : ℝ)
    (r : (ℕ → RC (TW)) → ι → ℕ → ℝ) :
    ∑ ω : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) ω *
      (if Pool.P0228.AlgOK (TW) ℓ ωs φ T (v (Pool.P0210.extR (TW) rc₀ ω)) ρ₀ c (r (Pool.P0210.extR (TW) rc₀ ω))
          (Pool.P0210.extR (TW) rc₀ ω) then 0 else 1) ≤
      ∑ ω : Fin T → RC (QG), Pool.P0202.pw (wR (QG)) ω *
        (if Pool.P0228.AlgOK (QG) ℓ ωs φ T (v (Pool.P0210.extR (QG) rc₀ ω)) ρ₀ c (r (Pool.P0210.extR (QG) rc₀ ω))
          (Pool.P0210.extR (QG) rc₀ ω) then 0 else 1)
      + ∑ ω : Fin T → RC (QG), Pool.P0202.pw (wR (QG)) ω *
        (if ∀ t < T, Pool.P0176.Fits (QG).Lv (QG).sl (sp (QG) ℓ (Pool.P0210.extR (QG) rc₀ ω) ωs φ t)
          then 0 else 1) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hp := Pool.P0228.pw_nonneg (QG) hL ω
  rw [← mul_add, pw_twin P η ε L N G γ wE S KM ω]
  refine mul_le_mul_of_nonneg_left ?_ hp
  by_cases hF : ∀ t < T, Pool.P0176.Fits (QG).Lv (QG).sl (sp (QG) ℓ (Pool.P0210.extR (QG) rc₀ ω) ωs φ t)
  · have hiff := algOK_twin_iff P η ε L N G γ wE S KM ℓ ωs φ hD hLv hlev hG hγ hwE hε hη T hTL hTK
      (Pool.P0210.extR (QG) rc₀ ω) (hfit_of_fits P η ε L N G γ wE S ℓ ωs φ hS _ T hF)
      (v (Pool.P0210.extR (QG) rc₀ ω)) ρ₀ c (r (Pool.P0210.extR (QG) rc₀ ω))
    have hiff' : Pool.P0228.AlgOK (TW) ℓ ωs φ T (v (Pool.P0210.extR (TW) rc₀ ω)) ρ₀ c
        (r (Pool.P0210.extR (TW) rc₀ ω)) (Pool.P0210.extR (TW) rc₀ ω) ↔
        Pool.P0228.AlgOK (QG) ℓ ωs φ T (v (Pool.P0210.extR (QG) rc₀ ω)) ρ₀ c
          (r (Pool.P0210.extR (QG) rc₀ ω)) (Pool.P0210.extR (QG) rc₀ ω) := hiff
    rw [if_pos hF]
    by_cases hA : Pool.P0228.AlgOK (QG) ℓ ωs φ T (v (Pool.P0210.extR (QG) rc₀ ω)) ρ₀ c
        (r (Pool.P0210.extR (QG) rc₀ ω)) (Pool.P0210.extR (QG) rc₀ ω)
    · rw [if_pos (hiff'.2 hA), if_pos hA]; norm_num
    · rw [if_neg (fun h => hA (hiff'.1 h)), if_neg hA]; norm_num
  · rw [if_neg hF]
    split_ifs <;> norm_num

open Classical in
/-- **`P(¬AlgOK)` for the finite twin with the self-rounding ALG's budgets** (P0243's `vOK`, `ρOK`, `rOK` with
`δ = ε`, read on the same coins): at most `(|ι| + 2)(T+1)²e^{−Lc} + P(some thread does not fit before T)`. -/
theorem prob_not_algOK_twin_alg (hS : (∑ j : Fin P.D, (P.sl j : ℝ)) + 1 ≤ S) (hL : (QG).IsLaw) (hN : 0 < (QG).N)
    (hη' : 0 < η) (hwE' : P.wE = wE) (T : ℕ) (hTL : T ≤ 2 ^ L) (hTK : T ≤ KM) (rc₀ : RC (TW)) {κ : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (Lc : ℝ) :
    ∑ ω : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) ω *
      (if Pool.P0228.AlgOK (TW) ℓ ωs φ T
          (Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T κ
            (Pool.P0210.extR (TW) rc₀ ω))
          (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
          (Pool.P0243.rOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T ε κ Lc
            (Pool.P0210.extR (TW) rc₀ ω))
          (Pool.P0210.extR (TW) rc₀ ω) then 0 else 1) ≤
      ((Fintype.card ι : ℝ) + 2) * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc))
      + ∑ ω : Fin T → RC (QG), Pool.P0202.pw (wR (QG)) ω *
        (if ∀ t < T, Pool.P0176.Fits (QG).Lv (QG).sl (sp (QG) ℓ (Pool.P0210.extR (QG) rc₀ ω) ωs φ t)
          then 0 else 1) := by
  have h1 := prob_not_algOK_twin P η ε L N G γ wE S KM ℓ ωs φ hD hLv hlev hG hγ hwE hε hη hS hL T hTL hTK rc₀
    (Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T κ)
    (Pool.P0243.ρOK η L γ wE (ι := ι) T ε κ Lc) 0
    (Pool.P0243.rOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T ε κ Lc)
  have h2 := Pool.P0243.prob_not_algOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T hL hN hη'
    hε.le (fun σ V ch bit => Pool.P0225.abs_ρStar_le η L N G γ wE ε hε hη σ V ch bit) hγ hwE hwE' hTL hκ0 hκ1 Lc
  exact h1.trans (by linarith)

open Classical in
/-- **ALG's budget in expectation, read on the finite twin's coin paths**: for any event `G` of the paths implying
that every thread fits before `T`, `E_T[[G]·Σ_{[a,b)} vOK] ≤ (b − a)·Cb(Σ_j sl_j)` (P0243's `budget_sum`; the
twin's path weights are the self-rounding ALG's). -/
theorem budget_twin (hL : (QG).IsLaw) (hN : 0 < (QG).N) (hwE' : P.wE = wE) (hG1 : 1 ≤ G) {κ : ℝ} (hκ : 0 ≤ κ)
    (T : ℕ) (hTL : T ≤ 2 ^ L) (rc₀ : RC (TW)) {a b : ℕ} (hab : a ≤ b) (hbT : b ≤ T)
    (GE : (Fin T → RC (TW)) → Prop)
    (hGE : ∀ ω, GE ω → ∀ t < T, Pool.P0176.Fits (QG).Lv (QG).sl (sp (QG) ℓ (Pool.P0210.extR (QG) rc₀ ω) ωs φ t)) :
    ∑ ω : Fin T → RC (TW), Pool.P0202.pw (wR (TW)) ω *
      (if GE ω then Pool.P0154.isum (Pool.P0243.vOK P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T κ
        (Pool.P0210.extR (TW) rc₀ ω)) a b else 0) ≤
      ((b : ℝ) - a) * Pool.P0243.Cb η N G γ wE (∑ j : Fin P.D, (P.sl j : ℝ)) κ := by
  have h := Pool.P0243.budget_sum P η L N G γ wE (Pool.P0225.ρStar η L N G γ wE ε) ℓ ωs φ rc₀ T hL hN hη hwE' hwE
    hγ hG1 hκ hTL hab hbT
  refine le_trans ?_ h
  refine Finset.sum_le_sum fun ω _ => ?_
  rw [pw_twin P η ε L N G γ wE S KM ω]
  refine mul_le_mul_of_nonneg_left ?_ (Pool.P0228.pw_nonneg (QG) hL ω)
  by_cases hg : GE ω
  · rw [if_pos hg, if_pos (hGE ω hg)]; exact le_rfl
  · rw [if_neg hg]
    split_ifs
    · exact Pool.P0154.isum_nonneg _ (fun u => Pool.P0243.vOK_nonneg P η L N G γ wE _ ℓ ωs φ rc₀ T hη κ _ u) a b
    · exact le_rfl

end Pool.P0253
