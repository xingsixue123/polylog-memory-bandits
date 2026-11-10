import Pool.P0291.Eval
import Pool.P0258.Exp2
import Pool.P0283.FitAll
import Pool.P0140.Base
import Pool.P0287.Overflow
import Pool.P0278.Statement

/-!
# The one-level machine's regret (P0278's `FamHyp` assembly)
-/


namespace Pool.P0292

open Finset Pool.P0261 Pool.P0284 Pool.P0194 Pool.P0290 Pool.P0001
open scoped Pool.P0290 Pool.P0201 Pool.P0287 Pool.P0050

variable (n T : ℕ) [NeZero n] (q : ℝ) (A : Pool.P0050.CoinAlg n)

attribute [local instance] Pool.P0082.coinFintype

open Classical in
set_option maxHeartbeats 2000000 in
/-- P0287's `notFitAll_famM` restated with P0290's decidable equality (`decCpG`). -/
theorem notFitAll_famM' (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (ℓ : LossSeq n)
    (rc₀ : RC (Pool.P0287.QF n T q A)) :
    ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := Tp T) (D := (Pool.P0287.QF n T q A).D) (Lt := Ld (Tp T))
        (K := (Pool.P0287.QF n T q A).K) (1 / (n : ℝ)) (qf n (Tp T))) ω2 *
      ∑ rc : Fin (Tp T) → RC (Pool.P0287.QF n T q A), Pool.P0202.pw (wR (Pool.P0287.QF n T q A)) rc *
        (if Pool.P0257.FitAll (Pool.P0287.QF n T q A) (Tp T) ℓ rc₀
            (Pool.P0082.ωsC (Pool.P0287.QF n T q A).E (Tp T) (Pool.P0287.QF n T q A).D (Ld (Tp T))
              (Pool.P0287.QF n T q A).K ω2)
            (Pool.P0082.φC (Tp T) (Pool.P0287.QF n T q A).D (Ld (Tp T)) (Pool.P0287.QF n T q A).K ω2) rc
          then 0 else 1) ≤
      1 / ((Tp T : ℝ) + 1) ^ 2 := by
  have hTp : 1 ≤ Tp T := Tp_pos T
  have hps : 0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, by rw [div_le_one (by exact_mod_cast NeZero.pos n)]; exact_mod_cast NeZero.one_le⟩
  exact (Pool.P0257.sum_not_fitAll_le (Pool.P0287.QF n T q A) rfl (P0_isLaw n T q A hq hq1) (NeZero.pos _)
    (T := Tp T) (Lt := Ld (Tp T)) ℓ rc₀ hps (qf_mem n (Tp T)).1 (qf_mem n (Tp T)).2
    (CpG_E_mono n (Tp T)) (btHyp (Tp T)) (by show 0 < Lv (Tp T); unfold Lv; omega) (hlev (Tp T))
    (xmin := 1 / (θc n (Tp T) (Kq q) : ℝ)) (Pool.P0287.xmin_pos n T q hq)
    (fun j => xmin_le (Kq_pos q hq) j) (Pool.P0287.one_le_inv_xmin n T q hq)
    (Rc_pos (Tp T)) (by rw [one_div_one_div]; exact hT_cover n (Tp T) (Kq q))
    (Pool.P0261.M0 n (Tp T)) (kk n (Tp T)) (hM0 n (Tp T)) (hk n (Tp T)) (hp n (Tp T))
    (Pool.P0287.hlevLt_Tp T) (s0 n (Tp T)) _ (hs hTp) (Sp n (Tp T)) (hM0S n (Tp T)) (hρS hn hTp)
    (fun _ => hsl n (Tp T))).trans (Pool.P0287.ovfB_le n (Tp T) hn hTp)


section Hyps

theorem hΛ0_F (hq : 0 < q) (hq1 : q ≤ 1 / 32) : ∀ x c, 0 ≤ (famM n T q A).P.Λ x c := fun x c => by
  have hK := KcF_pos n T q hq
  have hw : 0 < wEA n T q A := by have := wEA_ge n T q A hq hq1; linarith
  exact Pool.P0275.margP_Λ_nonneg (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (ρSub n T q A) (Tp T) (δ := εA n T q) (Ls := Lx n T) (Lb := Lx n T) (Lc := Lx n T) (Lt := Lx n T)
    (κ := ηA n T q) (xmin := Pool.P0282.xf n (Tp T) (KcF n T q)) (M := KcF n T q) (ρ := 2) (nn := n) (TT := Tp T)
    (Θ := Dp (Tp T)) (Dp (Tp T)) (ηA_pos n T q) (by unfold εA; have := ηA_pos n T q; positivity) (ηA_pos n T q) hw
    (Lx_pos n T).le (Lx_pos n T).le (Lx_pos n T).le (Lx_pos n T).le (ηA_pos n T q) (xf_pos (n := n) (T' := Tp T) hK)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) x c

end Hyps



section Budgets

open Classical

/-- P0243's variance budget at `famM` (the budgets P0277/P0283/P0289 use), as P0258's `v`. -/
noncomputable def vF (ℓ : LossSeq n) (rc₀ : RC (famM n T q A).P)
    (arr : Pool.P0116.Arr (Pool.P0201.pp (famM n T q A)) (Tp T) → Bool) (ω : ℕ → RC (famM n T q A).P) (u : ℕ) : ℝ :=
  Pool.P0243.vOK (M0 n T q A).P (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q)) (Pool.P0206.sh ℓ)
    (Pool.P0082.ωsC (famM n T q A).P.E (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
    (Pool.P0082.φC (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr) rc₀ (Tp T) (ηA n T q) ω u

/-- P0243's copy budget at `famM`, as P0258's `r`. -/
noncomputable def rF (ℓ : LossSeq n) (rc₀ : RC (famM n T q A).P)
    (arr : Pool.P0116.Arr (Pool.P0201.pp (famM n T q A)) (Tp T) → Bool) (ω : ℕ → RC (famM n T q A).P)
    (x : CpG n (Tp T)) (t : ℕ) : ℝ :=
  Pool.P0243.rOK (M0 n T q A).P (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q)) (Pool.P0206.sh ℓ)
    (Pool.P0082.ωsC (famM n T q A).P.E (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
    (Pool.P0082.φC (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr) rc₀ (Tp T) (εA n T q)
    (ηA n T q) (Lx n T) ω x t

/-- P0243's interval constant at `famM`, as P0258's `ρ₀`. -/
noncomputable def ρF : ℝ :=
  Pool.P0243.ρOK (ηA n T q) (LA T) (ηA n T q) (wEA n T q A) (ι := CpG n (Tp T)) (Tp T) (εA n T q) (ηA n T q) (Lx n T)

end Budgets


set_option maxHeartbeats 2000000 in
/-- P0287's `ovf_famM` restated with P0290's decidable equality. -/
theorem Tp_ovf_famM' (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (ℓ : LossSeq n) (rc₀ : RC (famM n T q A).P) :
    (Tp T : ℝ) * ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
      Pool.P0217.ovf (famM n T q A) (Tp T) ℓ rc₀ arr ≤ 1 := by
  have hTp : 1 ≤ Tp T := Tp_pos T
  have h := (Pool.P0221.sum_ovf_le (m := famM n T q A) (T := Tp T) rfl (famM_cap n T q A) ℓ rc₀
    (famM_isLaw n T q A hq hq1) (NeZero.pos _)
    (CpG_E_mono n (Tp T)) (btHyp (Tp T)) (by show 0 < Lv (Tp T); unfold Lv; omega) (hlev (Tp T))
    (xmin := 1 / (θc n (Tp T) (Kq q) : ℝ)) (Pool.P0287.xmin_pos n T q hq)
    (fun j => xmin_le (Kq_pos q hq) j) (Pool.P0287.one_le_inv_xmin n T q hq)
    (Rc_pos (Tp T)) (by rw [one_div_one_div]; exact hT_cover n (Tp T) (Kq q))
    (Pool.P0261.M0 n (Tp T)) (kk n (Tp T)) (hM0 n (Tp T)) (hk n (Tp T)) (hp n (Tp T))
    (Pool.P0287.hlevLt_Tp T) (s0 n (Tp T)) _ (hs hTp) (Sp n (Tp T)) (hM0S n (Tp T)) (hρS hn hTp)
    (fun _ => hsl n (Tp T))).trans (Pool.P0287.ovfB_le n (Tp T) hn hTp)
  have h' : ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
      Pool.P0217.ovf (famM n T q A) (Tp T) ℓ rc₀ arr ≤ 1 / ((Tp T : ℝ) + 1) ^ 2 := by
    convert h using 2
  have hT0 : (0 : ℝ) ≤ Tp T := Nat.cast_nonneg _
  calc (Tp T : ℝ) * _ ≤ (Tp T : ℝ) * (1 / ((Tp T : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left h' hT0
    _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; nlinarith


open Classical in
set_option maxHeartbeats 4000000 in
/-- P0283's bad term at `famM` (budgets `vF`, `ρF`, `0`, `rF`; one overflow bound from `notFitAll_famM'`). -/
theorem badT_famM (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (ℓ : LossSeq n) (rc₀ : RC (famM n T q A).P) :
    ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
      Pool.P0246.badTermP (famM n T q A).P (Pool.P0206.sh ℓ)
        (Pool.P0082.ωsC (famM n T q A).P.E (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
        (Pool.P0082.φC (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr) rc₀ (Tp T) (Lx n T)
        (vF n T q A ℓ rc₀ arr) (ρF n T q A) 0 (rF n T q A ℓ rc₀ arr) ≤
      2 * (1 / ((Tp T : ℝ) + 1) ^ 2) + (Fintype.card (CpG n (Tp T)) * (2 * ((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T)) +
        2 * ((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T)) +
        ((Fintype.card (CpG n (Tp T)) : ℝ) + 2) * (((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T)) := by
  have hK := KcF_pos n T q hq
  have hI := famM_intended n T q A hq hq1
  have hw : 0 < wEA n T q A := by have := wEA_ge n T q A hq hq1; linarith
  have hps : 0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, by rw [div_le_one (by exact_mod_cast NeZero.pos n)]; exact_mod_cast NeZero.one_le⟩
  exact Pool.P0283.badTermP_twin_avg1 (M0 n T q A).P (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q)
    (ηA n T q) (wEA n T q A) ((M0 n T q A).Ns + 1) (Tp T) (Pool.P0206.sh ℓ) hI.hD hI.hLv hI.hlev
    (by show 1 ≤ NA n T q; unfold NA; omega) (ηA_pos n T q) hw
    (by unfold εA; have := ηA_pos n T q; have : (0 : ℝ) < Tp T := by exact_mod_cast Tp_pos T
        positivity)
    (ηA_pos n T q).le
    (by have := famM_cap n T q A
        have h2 : ((∑ j, (famM n T q A).P.sl j : ℕ) : ℝ) ≤ ((famM n T q A).Ns : ℕ) := by exact_mod_cast this
        push_cast at h2; show (∑ j : Fin (Dn (Tp T)), (Sl n (Tp T) : ℝ)) + 1 ≤ ((Dn (Tp T) * Sl n (Tp T) + 1 : ℕ) : ℝ)
        push_cast; rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul])
    (P0_isLaw n T q A hq hq1) (by show 0 < NA n T q; unfold NA; omega) (ηA_pos n T q) rfl (hTL_F T) le_rfl rc₀
    (ηA_pos n T q) (ηA_le_one n T q) (Lx n T) (Lx n T) hps (qf_mem n (Tp T)).1 (qf_mem n (Tp T)).2
    (1 / ((Tp T : ℝ) + 1) ^ 2) (notFitAll_famM' n T q A hn hq hq1 (Pool.P0206.sh ℓ) rc₀)


/-- `Tp·(bad-term bound) ≤ 3`. -/
theorem Tp_badB_le : (Tp T : ℝ) * (2 * (1 / ((Tp T : ℝ) + 1) ^ 2) + (Fintype.card (CpG n (Tp T)) *
    (2 * ((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T)) + 2 * ((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T)) +
      ((Fintype.card (CpG n (Tp T)) : ℝ) + 2) * (((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T))) ≤ 3 := by
  set c := (Fintype.card (CpG n (Tp T)) : ℝ)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ Tp T := Nat.cast_nonneg _
  have he : Real.exp (-Lx n T) = 1 / (((Tp T : ℝ) + 1) ^ 3 * (4 * c + 4)) := by
    unfold Lx
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, ← Real.log_rpow (by positivity),
      Real.exp_log (by positivity), Real.exp_log (by positivity)]
    rw [show ((Tp T : ℝ) + 1) ^ (3 : ℝ) = ((Tp T : ℝ) + 1) ^ (3 : ℕ) by norm_cast]
    field_simp
    rfl
  rw [he]
  have e1 : (Tp T : ℝ) * (2 * (1 / ((Tp T : ℝ) + 1) ^ 2) + (c * (2 * ((Tp T : ℝ) + 1) ^ 2 *
      (1 / (((Tp T : ℝ) + 1) ^ 3 * (4 * c + 4)))) + 2 * ((Tp T : ℝ) + 1) ^ 2 *
      (1 / (((Tp T : ℝ) + 1) ^ 3 * (4 * c + 4)))) + (c + 2) * (((Tp T : ℝ) + 1) ^ 2 *
      (1 / (((Tp T : ℝ) + 1) ^ 3 * (4 * c + 4))))) =
      (Tp T : ℝ) * (2 * (1 / ((Tp T : ℝ) + 1) ^ 2)) + (Tp T : ℝ) * ((3 * c + 4) / (((Tp T : ℝ) + 1) * (4 * c + 4))) := by
    field_simp; ring
  rw [e1]
  have k1 : (Tp T : ℝ) * (2 * (1 / ((Tp T : ℝ) + 1) ^ 2)) ≤ 2 := by
    rw [show (Tp T : ℝ) * (2 * (1 / ((Tp T : ℝ) + 1) ^ 2)) = 2 * (Tp T / ((Tp T : ℝ) + 1) ^ 2) by ring]
    have : (Tp T : ℝ) / ((Tp T : ℝ) + 1) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  have k2 : (Tp T : ℝ) * ((3 * c + 4) / (((Tp T : ℝ) + 1) * (4 * c + 4))) ≤ 1 := by
    rw [mul_div_assoc', div_le_one (by positivity)]; nlinarith
  linarith

open Classical in
set_option maxHeartbeats 8000000 in
/-- **The one-level machine's regret over the process horizon** (P0258 at `famM` with P0243's budgets, ALG term by
P0291, overflow by P0287, bad term by P0283/P0287): the probing remainder `goodTermP2` is left as a term. -/
theorem regret_famM_le (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (hnq : (n : ℝ) / T ≤ q)
    (ℓ : LossSeq n) (ω₀ : Pool.P0201.Yc (famM n T q A) × Pool.P0201.Zc (famM n T q A))
    (rc₀ : RC (famM n T q A).P) :
    regret (Pool.P0201.mach (famM n T q A)).toMachine ℓ (Tp T + 1) ≤
      6 + ((famM n T q A).P.wB + ∑ s : Σ j : Fin (famM n T q A).P.D, Fin ((famM n T q A).P.sl j),
            (famM n T q A).P.xr s.1 + (∑ j : Fin (famM n T q A).P.D, ((famM n T q A).P.sl j : ℝ)) *
              ∑ j : Fin (famM n T q A).P.D, (famM n T q A).P.xr j) *
          regret (Pool.P0055.Sub (famM n T q A).P.AB.toMachine (famM n T q A).P.wB (famM_isLaw n T q A hq hq1).1
            (Pool.P0202.wB_le_one _ (famM_isLaw n T q A hq hq1))) (Pool.P0206.sh ℓ) (Tp T) +
        5000000000000000 * Pool.P0291.Λ n T ^ 28 * Pool.P0291.Q n T q +
        ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
          Pool.P0258.goodTermP2 (famM n T q A).P (Pool.P0206.sh ℓ)
            (Pool.P0082.ωsC (famM n T q A).P.E (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
            (Pool.P0082.φC (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
            (famM_intended n T q A hq hq1).hD (famM_intended n T q A hq hq1).hLv (famM_intended n T q A hq hq1).hlev
            rc₀ (Tp T) (Lx n T) (vF n T q A ℓ rc₀ arr) (ρF n T q A) 0 (rF n T q A ℓ rc₀ arr)
            (Pool.P0282.xf n (Tp T) (KcF n T q)) := by
  have hK := KcF_pos n T q hq
  have hI := famM_intended n T q A hq hq1
  have hw0 : 0 < wEA n T q A := by have := wEA_ge n T q A hq hq1; linarith
  have hρ : 0 ≤ ρF n T q A := by
    unfold ρF Pool.P0243.ρOK
    have := Pool.P0226.αT_nonneg (ι := CpG n (Tp T)) (η := ηA n T q) (L := LA T) (T := Tp T) (ηA_pos n T q)
      (δ := εA n T q) (by unfold εA; have := ηA_pos n T q; positivity)
    have := (Lx_pos n T).le; have := ηA_pos n T q; positivity
  obtain ⟨i, -, hreg⟩ := Pool.P0258.regret_le_absorbedP2 (m := famM n T q A) (T := Tp T) hI
    (famM_isLaw n T q A hq hq1) (NeZero.pos _) ℓ ω₀ rc₀ (famM_intended n T q A hq hq1).hD (famM_intended n T q A hq hq1).hLv (famM_intended n T q A hq hq1).hlev (Tp_pos T) (L := Lx n T) (Lx_pos n T)
    (by show (0 : ℕ) < Bm n (Tp T); exact Bm_pos n (Tp T)) (Pool.P0191.layOK_sort _) (fun j => xr_pos hK j)
    (fun j => xr_le_one hK j) (fun i j hij => xr_anti hK hij) (hcw_F n T q A hq) (hΛ0_F n T q A hq hq1)
    (by show 0 < wEA n T q A; exact hw0)
    (vF n T q A ℓ rc₀) (ρF n T q A) 0
    (fun arr ω u => Pool.P0243.vOK_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ (ηA_pos n T q).le _ _ _) hρ le_rfl
    (rF n T q A ℓ rc₀) (xf := Pool.P0282.xf n (Tp T) (KcF n T q)) (fun j => floor_le_xr hK j)
  refine hreg.trans ?_
  -- names
  set w := fun (arr : Pool.P0116.Arr (Pool.P0201.pp (famM n T q A)) (Tp T) → Bool) => Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr with hwdef
  set c1 := 1 - ((∑ j, ((famM n T q A).P.sl j : ℝ)) * ∑ j, (famM n T q A).P.xr j) / (famM n T q A).P.wE with hc1
  set c2 := (∑ s : Σ j : Fin (famM n T q A).P.D, Fin ((famM n T q A).P.sl j), (famM n T q A).P.xr s.1) +
    (∑ j, ((famM n T q A).P.sl j : ℝ)) * ∑ j, (famM n T q A).P.xr j with hc2
  set X := fun (arr : Pool.P0116.Arr (Pool.P0201.pp (famM n T q A)) (Tp T) → Bool) => Pool.P0217.algT (famM n T q A) (Tp T) ℓ rc₀ i arr with hX
  set Z := fun (arr : Pool.P0116.Arr (Pool.P0201.pp (famM n T q A)) (Tp T) → Bool) => Pool.P0246.badTermP (famM n T q A).P (Pool.P0206.sh ℓ)
    (Pool.P0082.ωsC (famM n T q A).P.E (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
    (Pool.P0082.φC (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr) rc₀ (Tp T) (Lx n T)
    (vF n T q A ℓ rc₀ arr) (ρF n T q A) 0 (rF n T q A ℓ rc₀ arr) with hZ
  set Y := fun (arr : Pool.P0116.Arr (Pool.P0201.pp (famM n T q A)) (Tp T) → Bool) => Pool.P0258.goodTermP2 (famM n T q A).P (Pool.P0206.sh ℓ)
    (Pool.P0082.ωsC (famM n T q A).P.E (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
    (Pool.P0082.φC (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
    (famM_intended n T q A hq hq1).hD (famM_intended n T q A hq hq1).hLv (famM_intended n T q A hq hq1).hlev rc₀ (Tp T) (Lx n T) (vF n T q A ℓ rc₀ arr) (ρF n T q A) 0 (rF n T q A ℓ rc₀ arr)
    (Pool.P0282.xf n (Tp T) (KcF n T q)) with hY
  have esum : ∑ arr, w arr * (c1 * X arr + Y arr + c2 * (Tp T : ℝ) * Z arr) =
      c1 * ∑ arr, w arr * X arr + ∑ arr, w arr * Y arr + c2 * (Tp T : ℝ) * ∑ arr, w arr * Z arr := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun arr _ => by ring
  rw [esum]
  -- bounds
  have hA := Pool.P0291.algT_famM_le n T q A hn hnT hq hq1 hnq ℓ rc₀ i
  have hO := Tp_ovf_famM' n T q A hn hq hq1 ℓ rc₀
  have hB := badT_famM n T q A hn hq hq1 ℓ rc₀
  have hB3 := Tp_badB_le n T
  have hsw := slot_weights_le n T q hq
  have hκ : ((∑ j, ((famM n T q A).P.sl j : ℝ)) * ∑ j, (famM n T q A).P.xr j) ≤ q / 4 := by
    have := hsw.2; exact this
  have hX1 : (∑ s : Σ j : Fin (famM n T q A).P.D, Fin ((famM n T q A).P.sl j), (famM n T q A).P.xr s.1) ≤ q / 4 := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact hsw.1
  have hκ0 : 0 ≤ (∑ j, ((famM n T q A).P.sl j : ℝ)) * ∑ j, (famM n T q A).P.xr j :=
    mul_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => (xr_pos hK j).le)
  have hX10 : 0 ≤ (∑ s : Σ j : Fin (famM n T q A).P.D, Fin ((famM n T q A).P.sl j), (famM n T q A).P.xr s.1) :=
    Finset.sum_nonneg fun s _ => (xr_pos hK s.1).le
  have hwE : (famM n T q A).P.wE = wEA n T q A := rfl
  have hwE1 : wEA n T q A ≤ 1 := Pool.P0291.wEA_le_one n T q A hn hnT hq hq1 hnq
  have hwEge := wEA_ge n T q A hq hq1
  have hc10 : 0 ≤ c1 := by
    rw [hc1, hwE, sub_nonneg, div_le_one hw0]; linarith
  have hc11 : c1 ≤ 1 := by
    rw [hc1, sub_le_self_iff]; exact div_nonneg hκ0 hw0.le
  have hc20 : 0 ≤ c2 := by rw [hc2]; linarith
  have hc21 : c2 ≤ 1 := by rw [hc2]; linarith
  have hTp0 : (0 : ℝ) ≤ Tp T := Nat.cast_nonneg _
  set O := ∑ arr, w arr * Pool.P0217.ovf (famM n T q A) (Tp T) ℓ rc₀ arr with hOdef
  set Bd := 5000000000000000 * Pool.P0291.Λ n T ^ 28 * Pool.P0291.Q n T q with hBd
  have hBd0 : 0 ≤ Bd := by
    have := Pool.P0291.Λ_ge n T; have := Pool.P0291.Q_ge_one n T q hn hnT hq hq1 hnq; positivity
  have hO0 : 0 ≤ (Tp T : ℝ) * O := by
    rw [hOdef]; apply mul_nonneg hTp0
    refine Finset.sum_nonneg fun arr _ => mul_nonneg ?_ ?_
    · refine Pool.P0048.wtv_nonneg (fun x => ?_) (fun x => ?_) arr
      · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;>
          linarith [(famM n T q A).hps.1, (famM n T q A).hq.1, (famM n T q A).hps.2, (famM n T q A).hq.2]
      · rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;>
          linarith [(famM n T q A).hps.1, (famM n T q A).hq.1, (famM n T q A).hps.2, (famM n T q A).hq.2]
    · unfold Pool.P0217.ovf
      exact Finset.sum_nonneg fun rc _ => mul_nonneg (Finset.prod_nonneg fun j _ =>
        Pool.P0194.wR_nonneg _ (famM_isLaw n T q A hq hq1) _) (by split_ifs <;> norm_num)
  -- ALG part: c1·E[algT] ≤ Bd + Tp·O
  have kA : c1 * ∑ arr, w arr * X arr ≤ Bd + (Tp T : ℝ) * O := by
    have h1 : ∑ arr, w arr * X arr ≤ Bd + wEA n T q A * (Tp T : ℝ) * O := hA
    have h2 : wEA n T q A * (Tp T : ℝ) * O ≤ (Tp T : ℝ) * O := by
      rw [mul_assoc]; exact mul_le_of_le_one_left hO0 hwE1
    rcases le_total 0 (∑ arr, w arr * X arr) with hpos | hneg
    · calc c1 * ∑ arr, w arr * X arr ≤ 1 * ∑ arr, w arr * X arr := mul_le_mul_of_nonneg_right hc11 hpos
        _ ≤ Bd + (Tp T : ℝ) * O := by linarith
    · have : c1 * ∑ arr, w arr * X arr ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc10 hneg
      linarith
  -- bad part
  have kB : c2 * (Tp T : ℝ) * ∑ arr, w arr * Z arr ≤ 3 := by
    have h3 : (Tp T : ℝ) * ∑ arr, w arr * Z arr ≤ 3 := (mul_le_mul_of_nonneg_left hB hTp0).trans hB3
    rw [show c2 * (Tp T : ℝ) * ∑ arr, w arr * Z arr = c2 * ((Tp T : ℝ) * ∑ arr, w arr * Z arr) by ring]
    rcases le_total 0 ((Tp T : ℝ) * ∑ arr, w arr * Z arr) with hp | hm
    · calc c2 * ((Tp T : ℝ) * ∑ arr, w arr * Z arr) ≤ 1 * ((Tp T : ℝ) * ∑ arr, w arr * Z arr) :=
            mul_le_mul_of_nonneg_right hc21 hp
        _ ≤ 3 := by linarith
    · have := mul_nonpos_of_nonneg_of_nonpos hc20 hm; linarith
  have eY : (∑ arr, w arr * Y arr) = ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
      Pool.P0258.goodTermP2 (famM n T q A).P (Pool.P0206.sh ℓ)
        (Pool.P0082.ωsC (famM n T q A).P.E (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
        (Pool.P0082.φC (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
        (famM_intended n T q A hq hq1).hD (famM_intended n T q A hq hq1).hLv (famM_intended n T q A hq hq1).hlev
        rc₀ (Tp T) (Lx n T) (vF n T q A ℓ rc₀ arr) (ρF n T q A) 0 (rF n T q A ℓ rc₀ arr)
        (Pool.P0282.xf n (Tp T) (KcF n T q)) := rfl
  linarith


section Final

open Classical

/-- **The open probing piece, as a hypothesis**: the array-averaged probing remainder of P0258 at P0284's machine
(P0243's budgets) is `≤ Cg·Lg^kg·√(nT/q)`. -/
def GoodBound (Cg : ℝ) (kg : ℕ) : Prop :=
  ∀ (n T : ℕ) [NeZero n] (q : ℝ) (A : Pool.P0050.CoinAlg n) (_hA : Pool.P0173.CoinHom A) (hn : 1 ≤ n) (hnT : n ≤ T)
    (hq : 0 < q) (hq1 : q ≤ 1 / 32), (n : ℝ) / T ≤ q → ∀ (ℓ : LossSeq n) (rc₀ : RC (famM n T q A).P),
      ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
          Pool.P0258.goodTermP2 (famM n T q A).P (Pool.P0206.sh ℓ)
            (Pool.P0082.ωsC (famM n T q A).P.E (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
            (Pool.P0082.φC (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
            (famM_intended n T q A hq hq1).hD (famM_intended n T q A hq hq1).hLv (famM_intended n T q A hq hq1).hlev
            rc₀ (Tp T) (Lx n T) (vF n T q A ℓ rc₀ arr) (ρF n T q A) 0 (rF n T q A ℓ rc₀ arr)
            (Pool.P0282.xf n (Tp T) (KcF n T q)) ≤ Cg * Pool.P0161.Lg n T ^ kg * Real.sqrt (n * T / q)

/-- The constant of the family hypothesis. -/
noncomputable def CF (Cg : ℝ) : ℝ := 6 + 5000000000000000 * 5 ^ 28 + max Cg 0 + 160 * 600001 ^ 2 * 5 ^ 26

set_option maxHeartbeats 8000000 in
/-- **P0278's `FamHyp` from the probing bound**: P0284's machine `machF` (process horizon `Tp`, BASE rate
`γ = q/2`) meets P0278's family hypothesis with `C = CF Cg`, `k = max 28 kg`, given `GoodBound Cg kg`. -/
theorem famHyp_of_good {Cg : ℝ} {kg : ℕ} (hG : GoodBound Cg kg) :
    Pool.P0278.FamHyp (CF Cg) (max 28 kg) := by
  intro n T q hn hnT hnq hq1 A hA
  haveI : NeZero n := ⟨by omega⟩
  have hT1 : 1 ≤ T := le_trans hn hnT
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < q := lt_of_lt_of_le (div_pos hn0 hTr) hnq
  have hLg := Pool.P0161.one_le_Lg hn hT1
  set k := max 28 kg with hk
  have hLk : ∀ a, a ≤ k → Pool.P0161.Lg n T ^ a ≤ Pool.P0161.Lg n T ^ k := fun a ha => pow_le_pow_right₀ hLg ha
  have hLk1 : 1 ≤ Pool.P0161.Lg n T ^ k := one_le_pow₀ hLg
  have hCF : CF Cg = 6 + 5000000000000000 * 5 ^ 28 + max Cg 0 + 160 * 600001 ^ 2 * 5 ^ 26 := rfl
  refine ⟨machF n T q A, machF_hom n T q A, ?_, q / 2, by positivity, by linarith, ?_⟩
  · -- memory
    refine (memBits_machF_Lg n T q A hn hnT hq hq1 hnq).trans (add_le_add le_rfl ?_)
    have h26 := hLk 26 (by omega)
    have : 160 * 600001 ^ 2 * 5 ^ 26 ≤ CF Cg := by rw [hCF]; have := le_max_right Cg 0; norm_num; linarith
    have hC0 : 0 ≤ CF Cg := by rw [hCF]; have := le_max_right Cg 0; positivity
    exact mul_le_mul this h26 (by positivity) hC0
  · -- the regret
    have hK := KcF_pos n T q hq
    have hsw := slot_weights_le n T q hq
    have hX1 : (∑ s : Σ j : Fin (famM n T q A).P.D, Fin ((famM n T q A).P.sl j), (famM n T q A).P.xr s.1) ≤ q / 4 := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact hsw.1
    have hκ : (∑ j : Fin (famM n T q A).P.D, ((famM n T q A).P.sl j : ℝ)) *
        ∑ j : Fin (famM n T q A).P.D, (famM n T q A).P.xr j ≤ q / 4 := hsw.2
    have hκ0 : 0 ≤ (∑ j : Fin (famM n T q A).P.D, ((famM n T q A).P.sl j : ℝ)) *
        ∑ j : Fin (famM n T q A).P.D, (famM n T q A).P.xr j :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => (xr_pos hK j).le)
    have hX10 : 0 ≤ (∑ s : Σ j : Fin (famM n T q A).P.D, Fin ((famM n T q A).P.sl j), (famM n T q A).P.xr s.1) :=
      Finset.sum_nonneg fun s _ => (xr_pos hK s.1).le
    have hwB : (famM n T q A).P.wB = q / 2 := rfl
    refine ⟨(famM n T q A).P.wB + ∑ s : Σ j : Fin (famM n T q A).P.D, Fin ((famM n T q A).P.sl j),
        (famM n T q A).P.xr s.1 + (∑ j : Fin (famM n T q A).P.D, ((famM n T q A).P.sl j : ℝ)) *
          ∑ j : Fin (famM n T q A).P.D, (famM n T q A).P.xr j, Tp T, by positivity, ?_, Tp_le T hT1,
        by rw [hwB]; positivity, by rw [hwB]; linarith, fun ℓ => ?_⟩
    · have : (Tp T : ℝ) ≤ 2 * T := by exact_mod_cast Tp_le T hT1
      nlinarith
    · refine ⟨Pool.P0206.sh (Pool.P0140.zeroAfter ℓ T), ?_⟩
      -- coins to start from
      have hNA : 0 < (famM n T q A).P.N := NeZero.pos _
      let y : A.Y := A.μ.support_nonempty.some
      let z : A.Z := A.ν.support_nonempty.some
      let rc₀ : RC (famM n T q A).P := (none, ⟨0, hNA⟩, y, z)
      let ω₀ : Pool.P0201.Yc (famM n T q A) × Pool.P0201.Zc (famM n T q A) :=
        ((none, ⟨0, hNA⟩, y), (z, fun _ => false))
      have hle : T ≤ Tp T + 1 := (le_Tp T).trans (Nat.le_succ _)
      rw [← Pool.P0140.regret_zeroAfter (machF n T q A).toMachine ℓ hle]
      have hR := regret_famM_le n T q A hn hnT hq hq1 hnq (Pool.P0140.zeroAfter ℓ T) ω₀ rc₀
      have hgood := hG n T q A hA hn hnT hq hq1 hnq (Pool.P0140.zeroAfter ℓ T) rc₀
      have eM : regret (machF n T q A).toMachine (Pool.P0140.zeroAfter ℓ T) (Tp T + 1) =
          regret (Pool.P0201.mach (famM n T q A)).toMachine (Pool.P0140.zeroAfter ℓ T) (Tp T + 1) := rfl
      rw [eM]
      refine hR.trans ?_
      set Q := Real.sqrt ((n : ℝ) * T / q) with hQ
      have hQ1 : 1 ≤ Q := Pool.P0291.Q_ge_one n T q hn hnT hq hq1 hnq
      have hΛ := Pool.P0284.BB_le_Lg n T hn hnT
      have hΛ0 : (0 : ℝ) ≤ Pool.P0291.Λ n T := by unfold Pool.P0291.Λ; positivity
      have hΛ28 : Pool.P0291.Λ n T ^ 28 ≤ 5 ^ 28 * Pool.P0161.Lg n T ^ k := by
        have h1 : Pool.P0291.Λ n T ^ 28 ≤ (5 * Pool.P0161.Lg n T) ^ 28 := pow_le_pow_left₀ hΛ0 hΛ 28
        rw [mul_pow] at h1
        have h2 := hLk 28 (le_max_left _ _)
        nlinarith
      have hQ0 : 0 ≤ Q := by linarith
      have k1 : 5000000000000000 * Pool.P0291.Λ n T ^ 28 * Pool.P0291.Q n T q ≤
          5000000000000000 * 5 ^ 28 * Pool.P0161.Lg n T ^ k * Q := by
        have := mul_le_mul_of_nonneg_right hΛ28 hQ0
        show 5000000000000000 * Pool.P0291.Λ n T ^ 28 * Q ≤ _
        nlinarith
      have k2 : Cg * Pool.P0161.Lg n T ^ kg * Q ≤ max Cg 0 * Pool.P0161.Lg n T ^ k * Q := by
        have hkg := hLk kg (le_max_right _ _)
        have h0 : 0 ≤ Pool.P0161.Lg n T ^ kg := by positivity
        have : Cg * Pool.P0161.Lg n T ^ kg ≤ max Cg 0 * Pool.P0161.Lg n T ^ k :=
          (mul_le_mul_of_nonneg_right (le_max_left Cg 0) h0).trans
            (mul_le_mul_of_nonneg_left hkg (le_max_right Cg 0))
        exact mul_le_mul_of_nonneg_right this hQ0
      have k3 : (6 : ℝ) ≤ 6 * Pool.P0161.Lg n T ^ k * Q := by nlinarith
      have k4 : 0 ≤ 160 * 600001 ^ 2 * 5 ^ 26 * Pool.P0161.Lg n T ^ k * Q := by positivity
      have eS : regret (Pool.P0055.Sub (famM n T q A).P.AB.toMachine (famM n T q A).P.wB (famM_isLaw n T q A hq hq1).1
          (Pool.P0202.wB_le_one _ (famM_isLaw n T q A hq hq1))) (Pool.P0206.sh (Pool.P0140.zeroAfter ℓ T)) (Tp T) =
          regret (Pool.P0055.Sub A.toMachine (q / 2) (by positivity) (by linarith))
            (Pool.P0206.sh (Pool.P0140.zeroAfter ℓ T)) (Tp T) := rfl
      rw [eS] at hR ⊢
      have eC : CF Cg * Pool.P0161.Lg n T ^ k * Q = (6 * Pool.P0161.Lg n T ^ k * Q) +
          5000000000000000 * 5 ^ 28 * Pool.P0161.Lg n T ^ k * Q + max Cg 0 * Pool.P0161.Lg n T ^ k * Q +
          160 * 600001 ^ 2 * 5 ^ 26 * Pool.P0161.Lg n T ^ k * Q := by rw [hCF]; ring
      rw [eC]
      linarith

end Final

end Pool.P0292
