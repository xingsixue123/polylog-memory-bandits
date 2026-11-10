import Pool.P0292.Statement
import Pool.P0289.Probe
import Pool.P0282.MargBound

/-!
# The probing remainder at P0284's machine (`GoodBound` of P0292)
-/

namespace Pool.P0294

open Finset Pool.P0261 Pool.P0284 Pool.P0194 Pool.P0290 Pool.P0001 Pool.P0292
open scoped Pool.P0290 Pool.P0201 Pool.P0287 Pool.P0050

variable (n T : ℕ) [NeZero n] (q : ℝ) (A : Pool.P0050.CoinAlg n)

attribute [local instance] Pool.P0082.coinFintype

/-- The clock bound of the probing remainder: P0275's `ΛbarP` for `famM`'s margins. -/
noncomputable abbrev ΛbF : ℕ → ℝ :=
  Pool.P0275.ΛbarP (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (ρSub n T q A)
    (Tp T) (εA n T q) (Lx n T) (Lx n T) (Lx n T) (Lx n T) (ηA n T q) (Pool.P0282.xf n (Tp T) (KcF n T q))
    (KcF n T q) 2 n (Tp T) (Dp (Tp T)) (Dp (Tp T))

theorem hΛn_F (hq : 0 < q) : ∀ x c, (famM n T q A).P.E x ≤ c → (famM n T q A).P.Λ x c ≤
    ΛbF n T q A (Pool.P0065.curT (famM n T q A).P.E (famM n T q A).P.thr0 (famM n T q A).P.D (famM n T q A).P.Bt x
      (c + 1)) := fun x c _ =>
  Pool.P0275.margOf_le_Λbar (P0 n T q A).E (P0 n T q A).thr0 (P0 n T q A).D (P0 n T q A).Bt
    (fun j m => Pool.P0268.ΛPc_le (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
      (ρSub n T q A) (Tp T) (δ := εA n T q) (Ls := Lx n T) (Lb := Lx n T) (Lc := Lx n T) (Lt := Lx n T)
      (κ := ηA n T q) (xmin := Pool.P0282.xf n (Tp T) (KcF n T q)) (M := KcF n T q) (ρ := 2) (nn := n)
      (TT := Tp T) (Θ := Dp (Tp T)) (Dp (Tp T)) j m (by show (0 : ℝ) ≤ 1 / (q / 2); positivity) (Lx_pos n T).le
      (Lx_pos n T).le (Nat.cast_nonneg _)) x c

open Classical in
set_option maxHeartbeats 8000000 in
/-- P0289's averaged bound at `famM` with every hypothesis discharged. -/
theorem good_raw (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (ℓ : LossSeq n)
    (rc₀ : RC (famM n T q A).P) :
    ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
        Pool.P0258.goodTermP2 (famM n T q A).P (Pool.P0206.sh ℓ)
          (Pool.P0082.ωsC (famM n T q A).P.E (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
          (Pool.P0082.φC (Tp T) (famM n T q A).P.D (famM n T q A).Lf (famM n T q A).P.K arr)
          (famM_intended n T q A hq hq1).hD (famM_intended n T q A hq hq1).hLv (famM_intended n T q A hq hq1).hlev
          rc₀ (Tp T) (Lx n T) (vF n T q A ℓ rc₀ arr) (ρF n T q A) 0 (rF n T q A ℓ rc₀ arr)
          (Pool.P0282.xf n (Tp T) (KcF n T q)) ≤
      Pool.P0289.probeK0 (famM n T q A).P (Tp T) (Lx n T) (Pool.P0282.xf n (Tp T) (KcF n T q)) (KcF n T q) 2 n
          (Tp T) (Dp (Tp T)) (Dp (Tp T)) (ΛbF n T q A) (ρF n T q A) (Pool.P0282.xf n (Tp T) (KcF n T q)) +
        Pool.P0289.probeK1 (famM n T q A).P * ((Tp T : ℝ) * Pool.P0243.Cb (ηA n T q) (NA n T q) (NA n T q) (ηA n T q)
          (wEA n T q A) (∑ j : Fin (M0 n T q A).P.D, ((M0 n T q A).P.sl j : ℝ)) (ηA n T q)) := by
  have hK := KcF_pos n T q hq
  have hI := famM_intended n T q A hq hq1
  have hw : 0 < wEA n T q A := by have := wEA_ge n T q A hq hq1; linarith
  exact Pool.P0289.exp_goodTermP2_twin (M0 n T q A) (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q)
    (wEA n T q A) (Tp T) hI.hD hI.hLv hI.hlev (by show 0 < NA n T q; unfold NA; omega) (ηA_pos n T q) hw
    (by unfold εA; have := ηA_pos n T q; have : (0 : ℝ) < Tp T := by exact_mod_cast Tp_pos T
        positivity)
    (ηA_pos n T q) rfl (famM_isLaw n T q A hq hq1) (by show 1 ≤ NA n T q; unfold NA; omega)
    (κ := ηA n T q) (Lc := Lx n T) (ηA_pos n T q) (Lx_pos n T).le (hTL_F T) ℓ rc₀ (Pool.P0191.layOK_sort _)
    (Ls := Lx n T) (xmin := Pool.P0282.xf n (Tp T) (KcF n T q)) (M := KcF n T q) (ρ := 2) (nn := n) (TT := Tp T)
    (Θ := Dp (Tp T)) (Lx_pos n T).le (xf_pos (n := n) (T' := Tp T) hK) (xf_le_one (n := n) (T' := Tp T) hK)
    (fun j => floor_le_xr hK j) (by exact_mod_cast NeZero.pos n) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by norm_num) (fun i => Nat.two_pow_pos _) (fun i hi => Bt_pred_le (Tp T) i hi) (hx0_F n T q A hn hq)
    (hx_F n T q A hn hq) (Dp (Tp T)) (hΘn_F n T q A) le_rfl (by show (0 : ℝ) ≤ 1 / (q / 2); positivity)
    (ΛbF n T q A)
    (fun i => Pool.P0275.ΛbarP_nonneg (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
      (ρSub n T q A) (Tp T) (Dp (Tp T)) (ηA_pos n T q) (by unfold εA; have := ηA_pos n T q; positivity) (ηA_pos n T q)
      hw (Lx_pos n T).le (Lx_pos n T).le (Lx_pos n T).le (Lx_pos n T).le (ηA_pos n T q)
      (xf_pos (n := n) (T' := Tp T) hK) (Nat.cast_nonneg _) (Nat.cast_nonneg _) i)
    (fun i i' h => Pool.P0275.ΛbarP_anti _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i i' h)
    (hΛn_F n T q A hq) (Pool.P0282.xf n (Tp T) (KcF n T q)) (xf_pos (n := n) (T' := Tp T) hK).le

section Widths

theorem Wocc_le4 {L xmin M ρ' nn TT Θ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) (hX : 0 ≤ Θ * (ρ' * TT / nn)) {m : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hm : (m : ℝ) ≤ 4 * b) :
    Pool.P0222.Wocc L xmin M ρ' nn TT Θ m ≤
      2 * L / xmin + 2 * Real.sqrt (L * (Θ * (ρ' * TT / nn))) + 4 * Real.sqrt (L * M) * Real.sqrt b := by
  unfold Pool.P0222.Wocc
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have h1 : Real.sqrt (L * (m * M + Θ * (ρ' * TT / nn))) ≤
      Real.sqrt (L * (m * M)) + Real.sqrt (L * (Θ * (ρ' * TT / nn))) := by
    rw [mul_add]; exact Pool.P0282.sqrt_add_le' (by positivity) (mul_nonneg hL hX)
  have h2 : Real.sqrt (L * (m * M)) ≤ 2 * Real.sqrt (L * M) * Real.sqrt b := by
    rw [show L * (m * M) = m * (L * M) by ring]; exact Pool.P0282.sqrt_mul_le_two (mul_nonneg hL hM) hb hm0 hm
  linarith

theorem widV_le4 {cB L : ℝ} (hcB : 0 ≤ cB) (hL : 0 ≤ L) {m : ℕ} {b : ℝ} (hb : 0 ≤ b) (hm : (m : ℝ) ≤ 4 * b) :
    Pool.P0158.widV (m * cB) (max 1 cB) L ≤ 2 * max 1 cB * L + 4 * Real.sqrt (cB * L) * Real.sqrt b := by
  unfold Pool.P0158.widV
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have : Real.sqrt (m * cB * L) ≤ 2 * Real.sqrt (cB * L) * Real.sqrt b := by
    rw [mul_assoc]; exact Pool.P0282.sqrt_mul_le_two (mul_nonneg hcB hL) hb hm0 hm
  linarith

end Widths

/-- The constant part of the per-thread charge. -/
noncomputable abbrev αF : ℝ :=
  Pool.P0282.α₀ (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (ρSub n T q A) (Tp T)
      (εA n T q) (Lx n T) (Lx n T) (Lx n T) (Lx n T) (ηA n T q) (Pool.P0282.xf n (Tp T) (KcF n T q)) (KcF n T q) 2 n
      (Tp T) (Dp (Tp T)) +
    (2 * Lx n T / Pool.P0282.xf n (Tp T) (KcF n T q) + 2 * Real.sqrt (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n))))
    + 2 * max 1 (1 / (q / 2)) * Lx n T + Real.sqrt ((Tp T : ℝ) / n)

/-- The `√Bt`-coefficient of the per-thread charge. -/
noncomputable abbrev βF : ℝ :=
  Pool.P0282.β₀ (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (ρSub n T q A) (Tp T)
      (Lx n T) (Lx n T) (KcF n T q) +
    4 * Real.sqrt (Lx n T * KcF n T q) + 4 * Real.sqrt (1 / (q / 2) * Lx n T)

theorem Mb_le (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (hnq : (n : ℝ) / T ≤ q)
    (j : Fin (Dn (Tp T))) :
    ΛbF n T q A j + Pool.P0222.Wocc (Lx n T) (Pool.P0282.xf n (Tp T) (KcF n T q)) (KcF n T q) 2 n (Tp T) (Dp (Tp T))
        (Pool.P0238.lenOf (Dp (Tp T)) (Tp T) (Bt (Tp T)) j) +
      Pool.P0158.widV ((Pool.P0238.lenOf (Dp (Tp T)) (Tp T) (Bt (Tp T)) j : ℕ) * (1 / (q / 2))) (max 1 (1 / (q / 2)))
        (Lx n T) + (Bm n (Tp T) : ℝ) ≤ αF n T q A + βF n T q A * Real.sqrt (Bt (Tp T) j) := by
  have hK := KcF_pos n T q hq
  have hw : 0 < wEA n T q A := by have := wEA_ge n T q A hq hq1; linarith
  have hLx := (Lx_pos n T).le
  have hcB : (0 : ℝ) ≤ 1 / (q / 2) := by positivity
  have hb0 : (0 : ℝ) ≤ Bt (Tp T) j := Nat.cast_nonneg _
  have hlen : ((Pool.P0238.lenOf (Dp (Tp T)) (Tp T) (Bt (Tp T)) j : ℕ) : ℝ) ≤ 4 * (Bt (Tp T) j : ℕ) := by
    exact_mod_cast Pool.P0282.lenOf_le' (Tp T) (Dp (Tp T)) (Tp_pos T) le_rfl j
  have h1 := Pool.P0282.ΛbarP_le (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (ρSub n T q A) (Tp T) (Tp_pos T) rfl rfl (δ := εA n T q) (Ls := Lx n T) (Lb := Lx n T) (Lc := Lx n T)
    (Lt := Lx n T) (κ := ηA n T q) (xmin := Pool.P0282.xf n (Tp T) (KcF n T q)) (M := KcF n T q) (ρ := 2) (nn := n)
    (TT := Tp T) (Θ := Dp (Tp T)) (ηA_pos n T q) (by unfold εA; have := ηA_pos n T q; positivity) (ηA_pos n T q)
    hw hLx hLx hLx hLx (ηA_pos n T q) (xf_pos (n := n) (T' := Tp T) hK) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hcB (by positivity) (Dp (Tp T)) le_rfl j (by have := j.2; omega)
  have h2 := Wocc_le4 (xmin := Pool.P0282.xf n (Tp T) (KcF n T q)) hLx (Nat.cast_nonneg (KcF n T q))
    (show (0 : ℝ) ≤ (Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n) by positivity) hb0 hlen
  have h3 := widV_le4 hcB hLx hb0 hlen
  have h4 := Pool.P0291.Bm_le_r n T q hn hnT hq hq1 hnq
  simp only [αF, βF]
  have hsb := Real.sqrt_nonneg ((Bt (Tp T) j : ℕ) : ℝ)
  nlinarith

theorem αF_nonneg (hq : 0 < q) (hq1 : q ≤ 1 / 32) : 0 ≤ αF n T q A := by
  have hK := KcF_pos n T q hq
  have hw : 0 < wEA n T q A := by have := wEA_ge n T q A hq hq1; linarith
  have hLx := (Lx_pos n T).le
  have hxf := xf_pos (n := n) (T' := Tp T) hK
  have hη := ηA_pos n T q
  have hAP := Pool.P0282.AP_nonneg (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (ρSub n T q A) (Tp T) (δ := εA n T q) (Ls := Lx n T) (Lc := Lx n T) (Lt := Lx n T) (κ := ηA n T q)
    (xmin := Pool.P0282.xf n (Tp T) (KcF n T q)) (M := (KcF n T q : ℝ)) (ρ := 2) (nn := n) (TT := Tp T)
    (Θ := Dp (Tp T)) hη (by unfold εA; positivity) hη hw hLx hLx hLx hη hxf (Nat.cast_nonneg _)
  have hα := Pool.P0226.αT_nonneg (ι := CpG n (Tp T)) (η := ηA n T q) (L := LA T) (T := Tp T) hη
    (δ := εA n T q) (by unfold εA; positivity)
  simp only [αF, Pool.P0282.α₀]
  have : 0 ≤ Lx n T / ηA n T q := div_nonneg hLx hη.le
  have : 0 ≤ Lx n T / (2 * (wEA n T q A * ηA n T q)) := div_nonneg hLx (by positivity)
  have : 0 ≤ 2 * Lx n T / Pool.P0282.xf n (Tp T) (KcF n T q) := div_nonneg (by linarith) hxf.le
  have : (0 : ℝ) ≤ max 1 (P0 n T q A).cB := le_trans zero_le_one (le_max_left _ _)
  have : (0 : ℝ) ≤ max 1 (1 / (q / 2)) := le_trans zero_le_one (le_max_left _ _)
  have := Real.sqrt_nonneg (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n)))
  have := Real.sqrt_nonneg ((Tp T : ℝ) / n)
  have := Real.sqrt_nonneg (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / (n : ℝ))))
  positivity

theorem βF_nonneg : 0 ≤ βF n T q A := by
  have := Pool.P0282.BP_nonneg (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (ρSub n T q A) (Lx n T) (KcF n T q)
  simp only [βF, Pool.P0282.β₀]; positivity

/-- **P0289's `K₀` at `famM`**, bounded by P0282's thread sums. -/
theorem probeK0_le (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (hnq : (n : ℝ) / T ≤ q) :
    Pool.P0289.probeK0 (famM n T q A).P (Tp T) (Lx n T) (Pool.P0282.xf n (Tp T) (KcF n T q)) (KcF n T q) 2 n
        (Tp T) (Dp (Tp T)) (Dp (Tp T)) (ΛbF n T q A) (ρF n T q A) (Pool.P0282.xf n (Tp T) (KcF n T q)) ≤
      (Dn (Tp T) * Sl n (Tp T) : ℝ) * Dn (Tp T) * ((4 * n + 2) * αF n T q A +
          5 * βF n T q A * Real.sqrt (n * Tp T / KcF n T q)) +
        Pool.P0282.xf n (Tp T) (KcF n T q) * (Tp T * (Dn (Tp T) * Sl n (Tp T) : ℝ)) +
        Dn (Tp T) * ((Dn (Tp T) * Sl n (Tp T) : ℝ) * ρF n T q A * (2 * (Dn (Tp T) * Sl n (Tp T) : ℝ) * (2 * n + 1) + 1)
          + (Dn (Tp T) * Sl n (Tp T) : ℝ) * (2 * n + 1) * ρF n T q A) := by
  have hK := KcF_pos n T q hq
  have hS : (∑ j : Fin (famM n T q A).P.D, ((famM n T q A).P.sl j : ℝ)) = (Dn (Tp T) * Sl n (Tp T) : ℝ) := by
    show (∑ _j : Fin (Dn (Tp T)), (Sl n (Tp T) : ℝ)) = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hS0 : (0 : ℝ) ≤ (Dn (Tp T) * Sl n (Tp T) : ℝ) := by positivity
  have hρ : 0 ≤ ρF n T q A := by
    unfold ρF Pool.P0243.ρOK
    have := Pool.P0226.αT_nonneg (ι := CpG n (Tp T)) (η := ηA n T q) (L := LA T) (T := Tp T) (ηA_pos n T q)
      (δ := εA n T q) (by unfold εA; have := ηA_pos n T q; positivity)
    have := (Lx_pos n T).le; have := ηA_pos n T q
    have : 0 < wEA n T q A := by have := wEA_ge n T q A hq hq1; linarith
    positivity
  unfold Pool.P0289.probeK0
  rw [hS]
  refine add_le_add (add_le_add ?_ le_rfl) ?_
  · exact Pool.P0282.thread_sum_le (n := n) (T := Tp T) (Kc := KcF n T q) hn hK (Tp_pos T) hS0
      (αF_nonneg n T q A hq hq1) (βF_nonneg n T q A) _ (fun j _ => Mb_le n T q A hn hnT hq hq1 hnq j)
  · calc _ ≤ ∑ _j : Fin (Dn (Tp T)), ((Dn (Tp T) * Sl n (Tp T) : ℝ) * ρF n T q A *
          (2 * (Dn (Tp T) * Sl n (Tp T) : ℝ) * (2 * n + 1) + 1) + (Dn (Tp T) * Sl n (Tp T) : ℝ) * (2 * n + 1) *
            ρF n T q A) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hxC := Pool.P0282.xr_Cp_le (n := n) (T := Tp T) (Kc := KcF n T q) hn hK j
          have hx0 : 0 ≤ xr n (Tp T) (KcF n T q) j := (xr_pos hK j).le
          have hx1 : xr n (Tp T) (KcF n T q) j ≤ 1 := xr_le_one hK j
          set C := (((if xr n (Tp T) (KcF n T q) j ≤ Pool.P0282.xf n (Tp T) (KcF n T q) then 0 else
            ((range (Tp T)).filter (fun t => Pool.P0065.canonT (Dn (Tp T)) (Bt (Tp T)) t = j)).card : ℕ) : ℝ))
          show xr n (Tp T) (KcF n T q) j * ((Dn (Tp T) * Sl n (Tp T) : ℝ) * ρF n T q A *
              (2 * ((Dn (Tp T) * Sl n (Tp T) : ℝ) * C) + 1) + (Dn (Tp T) * Sl n (Tp T) : ℝ) * C * ρF n T q A) ≤ _
          have e : xr n (Tp T) (KcF n T q) j * ((Dn (Tp T) * Sl n (Tp T) : ℝ) * ρF n T q A *
              (2 * ((Dn (Tp T) * Sl n (Tp T) : ℝ) * C) + 1) + (Dn (Tp T) * Sl n (Tp T) : ℝ) * C * ρF n T q A) =
              (Dn (Tp T) * Sl n (Tp T) : ℝ) * ρF n T q A * (2 * (Dn (Tp T) * Sl n (Tp T) : ℝ) *
                (xr n (Tp T) (KcF n T q) j * C) + xr n (Tp T) (KcF n T q) j) +
              (Dn (Tp T) * Sl n (Tp T) : ℝ) * (xr n (Tp T) (KcF n T q) j * C) * ρF n T q A := by ring
          rw [e]
          have k1 : 2 * (Dn (Tp T) * Sl n (Tp T) : ℝ) * (xr n (Tp T) (KcF n T q) j * C) + xr n (Tp T) (KcF n T q) j ≤
              2 * (Dn (Tp T) * Sl n (Tp T) : ℝ) * (2 * n + 1) + 1 := by nlinarith
          have k2 : (Dn (Tp T) * Sl n (Tp T) : ℝ) * (xr n (Tp T) (KcF n T q) j * C) * ρF n T q A ≤
              (Dn (Tp T) * Sl n (Tp T) : ℝ) * (2 * n + 1) * ρF n T q A :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxC hS0) hρ
          have k3 := mul_le_mul_of_nonneg_left k1 (mul_nonneg hS0 hρ)
          linarith
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

section Eq

/-- P0250's `AP`/`BP` read only `θ`, `R` of the process: margins and roundings do not matter. -/
theorem AP_margP {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ)
    (ρ1 ρ2 ρ3 : Pool.P0212.AState ι → Finset ι → Option ι → Bool → ℝ) (T' : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ)
    (Θn : ℕ) :
    Pool.P0250.AP (Pool.P0275.margP P η L N G γ wE ρ1 T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρ2 T' δ Ls
      Lc Lt κ xmin M ρ nn TT Θ = Pool.P0250.AP P η L N G γ wE ρ3 T' δ Ls Lc Lt κ xmin M ρ nn TT Θ := rfl

theorem BP_margP {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ)
    (ρ1 ρ2 ρ3 : Pool.P0212.AState ι → Finset ι → Option ι → Bool → ℝ) (T' : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ)
    (Θn : ℕ) (Ls' M' : ℝ) :
    Pool.P0250.BP (Pool.P0275.margP P η L N G γ wE ρ1 T' δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρ2 Ls' M' =
      Pool.P0250.BP P η L N G γ wE ρ3 Ls' M' := rfl

theorem AP_P0 : Pool.P0250.AP (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (ρSub n T q A) (Tp T) (εA n T q) (Lx n T) (Lx n T) (Lx n T) (ηA n T q) (Pool.P0282.xf n (Tp T) (KcF n T q))
    (KcF n T q) 2 n (Tp T) (Dp (Tp T)) = APF n T q A :=
  (AP_margP n (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (ρSub n T q A)
    (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q)) (ρSub n T q A)
    (Tp T) (εA n T q) (Lx n T) (Lx n T) (Lx n T) (Lx n T) (ηA n T q) (Pool.P0282.xf n (Tp T) (KcF n T q))
    (KcF n T q) 2 n (Tp T) (Dp (Tp T)) (Dp (Tp T))).symm

theorem BP_P0 : Pool.P0250.BP (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (ρSub n T q A) (Lx n T) (KcF n T q) = BPF n T q A :=
  (BP_margP n (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (ρSub n T q A)
    (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q)) (ρSub n T q A)
    (Tp T) (εA n T q) (Lx n T) (Lx n T) (Lx n T) (Lx n T) (ηA n T q) (Pool.P0282.xf n (Tp T) (KcF n T q))
    (KcF n T q) 2 n (Tp T) (Dp (Tp T)) (Dp (Tp T)) (Lx n T) (KcF n T q)).symm

end Eq


/-- The final arithmetic of the probing bound (abstract). -/
theorem good_final_arith (L Q S D nn aF bF R xT r cb K1 : ℝ) (hL : 1 ≤ L) (hQ : 1 ≤ Q) (hS0 : 0 ≤ S)
    (hS : S ≤ 600000 * L ^ 12) (hD0 : 0 ≤ D) (hD : D ≤ L) (hn : 1 ≤ nn) (ha0 : 0 ≤ aF) (hb0 : 0 ≤ bF) (hR0 : 0 ≤ R)
    (ha : nn * aF ≤ 20000000000 * L ^ 17 * Q) (hb : bF * R ≤ 200000 * L ^ 9 * Q) (hxT : xT ≤ 2 * (2 * Q))
    (hr0 : 0 ≤ r) (hr : (2 * nn + 1) * r ≤ 600 * L ^ 2 * Q) (hK1 : K1 ≤ 2 * L * S) (hK10 : 0 ≤ K1)
    (hcb0 : 0 ≤ cb) (hcb : cb ≤ 10000000 * L ^ 12 * Q) :
    S * D * ((4 * nn + 2) * aF + 5 * bF * R) + xT * S + D * (S * r * (2 * S * (2 * nn + 1) + 1) + S * (2 * nn + 1) * r)
      + K1 * cb ≤ 100000000000000000 * L ^ 30 * Q := by
  have hQ0 : 0 ≤ Q := by linarith
  have hLp : ∀ a, a ≤ 30 → L ^ a ≤ L ^ 30 := fun a ha => pow_le_pow_right₀ hL ha
  -- (a)
  have A1 : (4 * nn + 2) * aF ≤ 120000000000 * L ^ 17 * Q := by nlinarith
  have A2 : 5 * bF * R ≤ 1000000 * L ^ 9 * Q := by nlinarith
  have hL9 : L ^ 9 ≤ L ^ 17 := pow_le_pow_right₀ hL (by norm_num)
  have A3 : (4 * nn + 2) * aF + 5 * bF * R ≤ 121000000000 * L ^ 17 * Q := by
    have := mul_le_mul_of_nonneg_right hL9 hQ0; nlinarith
  have hSD : S * D ≤ 600000 * L ^ 13 := by
    calc S * D ≤ (600000 * L ^ 12) * L := mul_le_mul hS hD hD0 (by positivity)
      _ = 600000 * L ^ 13 := by ring
  have hX0 : 0 ≤ (4 * nn + 2) * aF + 5 * bF * R := by
    have : 0 ≤ (4 * nn + 2) * aF := mul_nonneg (by linarith) ha0
    have : 0 ≤ 5 * bF * R := by positivity
    linarith
  have T1 : S * D * ((4 * nn + 2) * aF + 5 * bF * R) ≤ 72600000000000000 * L ^ 30 * Q := by
    calc S * D * ((4 * nn + 2) * aF + 5 * bF * R) ≤ (600000 * L ^ 13) * (121000000000 * L ^ 17 * Q) :=
          mul_le_mul hSD A3 hX0 (by positivity)
      _ = 72600000000000000 * L ^ 30 * Q := by ring
  -- (b)
  have T2 : xT * S ≤ 2400000 * L ^ 30 * Q := by
    have h12 := hLp 12 (by norm_num)
    rcases le_total 0 xT with hx | hx
    · calc xT * S ≤ (4 * Q) * (600000 * L ^ 12) := mul_le_mul (by linarith) hS hS0 (by positivity)
        _ = 2400000 * (L ^ 12 * Q) := by ring
        _ ≤ 2400000 * (L ^ 30 * Q) := by have := mul_le_mul_of_nonneg_right h12 hQ0; linarith
        _ = _ := by ring
    · have : xT * S ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx hS0
      have : 0 ≤ L ^ 30 * Q := by positivity
      linarith
  -- (c)
  have T3 : D * (S * r * (2 * S * (2 * nn + 1) + 1) + S * (2 * nn + 1) * r) ≤ 500000000000000 * L ^ 30 * Q := by
    have hrr : r ≤ (2 * nn + 1) * r := by nlinarith
    have e : S * r * (2 * S * (2 * nn + 1) + 1) + S * (2 * nn + 1) * r =
        2 * S * S * ((2 * nn + 1) * r) + S * r + S * ((2 * nn + 1) * r) := by ring
    have k : S * r * (2 * S * (2 * nn + 1) + 1) + S * (2 * nn + 1) * r ≤
        (2 * S * S + 2 * S) * ((2 * nn + 1) * r) := by
      rw [e]; nlinarith [mul_le_mul_of_nonneg_left hrr hS0]
    have hSS : 2 * S * S + 2 * S ≤ 720001200000 * L ^ 24 := by
      have h1 : S * S ≤ (600000 * L ^ 12) * (600000 * L ^ 12) := mul_le_mul hS hS hS0 (by positivity)
      have h24 : L ^ 12 ≤ L ^ 24 := pow_le_pow_right₀ hL (by norm_num)
      have : (600000 * L ^ 12) * (600000 * L ^ 12) = 360000000000 * L ^ 24 := by ring
      nlinarith
    have hpr : 0 ≤ (2 * nn + 1) * r := by positivity
    calc D * (S * r * (2 * S * (2 * nn + 1) + 1) + S * (2 * nn + 1) * r) ≤ L * ((2 * S * S + 2 * S) * ((2 * nn + 1) * r)) :=
          mul_le_mul hD k (by positivity) (by positivity)
      _ ≤ L * ((720001200000 * L ^ 24) * (600 * L ^ 2 * Q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hSS hr hpr (by positivity)) (by positivity)
      _ = 432000720000000 * (L ^ 27 * Q) := by ring
      _ ≤ 432000720000000 * (L ^ 30 * Q) := by
          have := mul_le_mul_of_nonneg_right (hLp 27 (by norm_num)) hQ0; nlinarith
      _ ≤ _ := by have : 0 ≤ L ^ 30 * Q := by positivity
                  nlinarith
  -- (d)
  have T4 : K1 * cb ≤ 12000000000000 * L ^ 30 * Q := by
    calc K1 * cb ≤ (2 * L * (600000 * L ^ 12)) * (10000000 * L ^ 12 * Q) :=
          mul_le_mul (hK1.trans (mul_le_mul_of_nonneg_left hS (by positivity))) hcb hcb0 (by positivity)
      _ = 12000000000000 * (L ^ 25 * Q) := by ring
      _ ≤ 12000000000000 * (L ^ 30 * Q) := by
          have := mul_le_mul_of_nonneg_right (hLp 25 (by norm_num)) hQ0; nlinarith
      _ = _ := by ring
  have : 0 ≤ L ^ 30 * Q := by positivity
  nlinarith

section Scale

variable (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (hnq : (n : ℝ) / T ≤ q)
include hn hnT hq hq1 hnq

open Pool.P0291 in
set_option maxHeartbeats 4000000 in
theorem nαF_le : (n : ℝ) * αF n T q A ≤ 20000000000 * Λ n T ^ 17 * Q n T q := by
  have hK := KcF_pos n T q hq
  have hΛ := Λ_ge n T
  have hQ := Q_ge_one n T q hn hnT hq hq1 hnq
  have hLx := Lx_le n T
  have hLx0 := (Lx_pos n T).le
  have hs := one_le_sA n T q (le_trans hn hnT) hnq
  have hη := ηA_eq n T q hn hnT hq hq1 hnq
  obtain ⟨k1, _, _, k4, k5⟩ := s_facts n T q hn hnT hq hq1 hnq
  have hnq' := n_div_q_le n T q hn hnT hq hq1 hnq
  have hα := αT_le n T q hn hnT hq hq1 hnq
  have hθ := θc_le_r n T q hn hnT hq hq1 hnq
  have hxf : 1 / Pool.P0282.xf n (Tp T) (KcF n T q) = (θc n (Tp T) (Kq q) : ℝ) := by
    rw [one_div_xf (n := n) (T' := Tp T) hK]; rfl
  have hw := wEA_ge n T q A hq hq1
  have hnA := (nAPF_le n T q A hn hnT hq hq1 hnq).1
  have hD := Dn_le n T
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hcB : max 1 (1 / (q / 2)) = 2 / q := by
    rw [max_eq_right]; · ring
    rw [show 1 / (q / 2) = 2 / q by ring, le_div_iff₀ hq]; linarith
  have hcB' : (P0 n T q A).cB = 1 / (q / 2) := rfl
  have hDp : (Dp (Tp T) : ℝ) ≤ Λ n T := by have := hD; unfold Dn at this; push_cast at this; linarith
  set r := Real.sqrt ((Tp T : ℝ) / n)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hsq : Real.sqrt (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n))) ≤ 5 * Λ n T * r := by
    have e : Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n)) = (2 * Lx n T * Dp (Tp T)) * ((Tp T : ℝ) / n) := by ring
    rw [e, Real.sqrt_mul (by positivity)]
    apply mul_le_mul_of_nonneg_right _ hr0
    apply Real.sqrt_le_iff.2 ⟨by positivity, _⟩
    have : 2 * Lx n T * Dp (Tp T) ≤ 2 * (12 * Λ n T) * Λ n T :=
      mul_le_mul (by linarith) hDp (Nat.cast_nonneg _) (by positivity)
    nlinarith
  -- per-term bounds (each times n)
  set sA' := sA n T q
  have t1 : (n : ℝ) * (Lx n T / ηA n T q) ≤ 24 * Λ n T * Q n T q := by
    rw [hη, show Lx n T / (1 / sA') = Lx n T * sA' by field_simp]
    calc (n : ℝ) * (Lx n T * sA') = Lx n T * (n * sA') := by ring
      _ ≤ (12 * Λ n T) * (2 * Q n T q) := mul_le_mul hLx k1 (by positivity) (by positivity)
      _ = 24 * Λ n T * Q n T q := by ring
  have t2 : (n : ℝ) * Pool.P0226.αT (ι := CpG n (Tp T)) (ηA n T q) (LA T) (Tp T) (εA n T q) ≤
      140 * Λ n T ^ 2 * Q n T q := by
    calc (n : ℝ) * Pool.P0226.αT (ι := CpG n (Tp T)) (ηA n T q) (LA T) (Tp T) (εA n T q)
        ≤ n * (70 * Λ n T ^ 2 * sA') := mul_le_mul_of_nonneg_left hα hn0
      _ = 70 * Λ n T ^ 2 * (n * sA') := by ring
      _ ≤ 70 * Λ n T ^ 2 * (2 * Q n T q) := mul_le_mul_of_nonneg_left k1 (by positivity)
      _ = 140 * Λ n T ^ 2 * Q n T q := by ring
  have t3 : (n : ℝ) * (Lx n T / (2 * (wEA n T q A * ηA n T q))) ≤ 24 * Λ n T * Q n T q := by
    have : Lx n T / (2 * (wEA n T q A * ηA n T q)) ≤ Lx n T / ηA n T q := by
      apply div_le_div_of_nonneg_left hLx0 (ηA_pos n T q); nlinarith [ηA_pos n T q]
    exact (mul_le_mul_of_nonneg_left this hn0).trans t1
  have t4 : (n : ℝ) * (2 * max 1 (1 / (q / 2)) * Lx n T) ≤ 48 * Λ n T * Q n T q := by
    rw [hcB]
    calc (n : ℝ) * (2 * (2 / q) * Lx n T) = 4 * Lx n T * (n / q) := by ring
      _ ≤ 4 * (12 * Λ n T) * Q n T q := mul_le_mul (by linarith) hnq' (by positivity) (by positivity)
      _ = 48 * Λ n T * Q n T q := by ring
  have t5 : (n : ℝ) * (2 * Lx n T / Pool.P0282.xf n (Tp T) (KcF n T q)) ≤
      24 * Λ n T * (4800000 * Λ n T ^ 13 * Q n T q + 2 * Q n T q) := by
    have e : (n : ℝ) * (2 * Lx n T / Pool.P0282.xf n (Tp T) (KcF n T q)) =
        2 * Lx n T * (n * (1 / Pool.P0282.xf n (Tp T) (KcF n T q))) := by ring
    rw [e, hxf]
    have h1 : (n : ℝ) * (θc n (Tp T) (Kq q) : ℝ) ≤ 4800000 * Λ n T ^ 13 * Q n T q + 2 * Q n T q := by
      have := mul_le_mul_of_nonneg_left hθ hn0
      have e2 : (n : ℝ) * (4800000 * Λ n T ^ 13 / q + r) = 4800000 * Λ n T ^ 13 * (n / q) + n * r := by ring
      rw [e2] at this
      have := mul_le_mul_of_nonneg_left hnq' (show (0 : ℝ) ≤ 4800000 * Λ n T ^ 13 by positivity)
      linarith
    calc 2 * Lx n T * (n * (θc n (Tp T) (Kq q) : ℝ)) ≤ 2 * (12 * Λ n T) * (4800000 * Λ n T ^ 13 * Q n T q +
        2 * Q n T q) := mul_le_mul (by linarith) h1 (by positivity) (by positivity)
      _ = 24 * Λ n T * (4800000 * Λ n T ^ 13 * Q n T q + 2 * Q n T q) := by ring
  have t6 : (n : ℝ) * (2 * Real.sqrt (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n)))) ≤ 20 * Λ n T * Q n T q := by
    calc (n : ℝ) * (2 * Real.sqrt (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n)))) ≤ n * (2 * (5 * Λ n T * r)) :=
          mul_le_mul_of_nonneg_left (by linarith) hn0
      _ = 10 * Λ n T * (n * r) := by ring
      _ ≤ 10 * Λ n T * (2 * Q n T q) := mul_le_mul_of_nonneg_left k5 (by positivity)
      _ = 20 * Λ n T * Q n T q := by ring
  have t7 : (n : ℝ) * ((2 * (Dn (Tp T) : ℝ) + 1) * APF n T q A) ≤ 3 * Λ n T * (5000000000 * Λ n T ^ 16 * Q n T q) := by
    have hA0 := APF_nonneg n T q A hq hq1
    calc (n : ℝ) * ((2 * (Dn (Tp T) : ℝ) + 1) * APF n T q A) = (2 * (Dn (Tp T) : ℝ) + 1) * (n * APF n T q A) := by ring
      _ ≤ (3 * Λ n T) * (5000000000 * Λ n T ^ 16 * Q n T q) :=
          mul_le_mul (by linarith) hnA (by positivity) (by positivity)
  have t8 : (n : ℝ) * r ≤ 2 * Q n T q := k5
  -- assemble
  have hαF : αF n T q A = Lx n T / ηA n T q + Pool.P0226.αT (ι := CpG n (Tp T)) (ηA n T q) (LA T) (Tp T) (εA n T q) +
      Lx n T / (2 * (wEA n T q A * ηA n T q)) + 2 * max 1 (1 / (q / 2)) * Lx n T +
      2 * Lx n T / Pool.P0282.xf n (Tp T) (KcF n T q) + 2 * Real.sqrt (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n)))
      + (2 * (Dn (Tp T) : ℝ) + 1) * APF n T q A +
      (2 * Lx n T / Pool.P0282.xf n (Tp T) (KcF n T q) +
        2 * Real.sqrt (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n)))) +
      2 * max 1 (1 / (q / 2)) * Lx n T + r := by
    unfold αF Pool.P0282.α₀
    rw [AP_P0, hcB']
  rw [hαF]
  have hp : ∀ a, a ≤ 17 → Λ n T ^ a ≤ Λ n T ^ 17 := fun a ha => pow_le_pow_right₀ hΛ ha
  have p1 : Λ n T ≤ Λ n T ^ 17 := by simpa using hp 1 (by norm_num)
  have p2 := hp 2 (by norm_num)
  have p14 : Λ n T * Λ n T ^ 13 ≤ Λ n T ^ 17 := by rw [← pow_succ']; exact hp 14 (by norm_num)
  have p17 : Λ n T * Λ n T ^ 16 = Λ n T ^ 17 := by rw [← pow_succ']
  have hQ0 : 0 ≤ Q n T q := by linarith
  have u1 := mul_le_mul_of_nonneg_right p1 hQ0
  have u2 := mul_le_mul_of_nonneg_right p2 hQ0
  have u3 := mul_le_mul_of_nonneg_right p14 hQ0
  have u4 : (1 : ℝ) * Q n T q ≤ Λ n T ^ 17 * Q n T q := mul_le_mul_of_nonneg_right (one_le_pow₀ hΛ) hQ0
  have e5 : 24 * Λ n T * (4800000 * Λ n T ^ 13 * Q n T q + 2 * Q n T q) =
      115200000 * (Λ n T * Λ n T ^ 13 * Q n T q) + 48 * (Λ n T * Q n T q) := by ring
  have e7 : 3 * Λ n T * (5000000000 * Λ n T ^ 16 * Q n T q) = 15000000000 * (Λ n T ^ 17 * Q n T q) := by
    rw [← p17]; ring
  rw [e5] at t5; rw [e7] at t7
  nlinarith

open Pool.P0291 in
set_option maxHeartbeats 4000000 in
theorem βF_le : βF n T q A * Real.sqrt (n * Tp T / KcF n T q) ≤ 200000 * Λ n T ^ 9 * Q n T q := by
  have hK := KcF_pos n T q hq
  have hKr : (1 : ℝ) ≤ KcF n T q := by exact_mod_cast hK
  have hΛ := Λ_ge n T
  have hQ := Q_ge_one n T q hn hnT hq hq1 hnq
  have hLx := Lx_le n T
  have hLx0 := (Lx_pos n T).le
  have hD := Dn_le n T
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTp0 : (0 : ℝ) ≤ Tp T := Nat.cast_nonneg _
  have hBP := BPF_sqrt_le n T q A hn hnT hq hq1 hnq
  have hB0 : 0 ≤ BPF n T q A := Pool.P0282.BP_nonneg _ _ _ _ _ _ _ _ _ _
  set R := Real.sqrt ((n : ℝ) * Tp T / KcF n T q) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hRle : R ≤ Real.sqrt ((n : ℝ) * Tp T) := Real.sqrt_le_sqrt (div_le_self (by positivity) hKr)
  have hnT2 : Real.sqrt ((n : ℝ) * Tp T) ≤ 2 * Q n T q :=
    sqrt_le_Q n T q hn hnT hq hq1 hnq (X := (Tp T : ℝ)) (by rw [le_div_iff₀ hq]; nlinarith)
  -- √(cB·Lx)·R ≤ 10Λ·Q
  have a1 : Real.sqrt (1 / (q / 2) * Lx n T) * R ≤ 10 * Λ n T * Q n T q := by
    have e : Real.sqrt (1 / (q / 2) * Lx n T) * R ≤ Real.sqrt (2 * Lx n T) * Real.sqrt (n * ((Tp T : ℝ) / q)) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
      apply Real.sqrt_le_sqrt
      rw [show 1 / (q / 2) * Lx n T * ((n : ℝ) * Tp T / KcF n T q) = 2 * Lx n T * (n * ((Tp T : ℝ) / q)) / KcF n T q by
        field_simp]
      exact div_le_self (by positivity) hKr
    have h2 := sqrt_le_Q n T q hn hnT hq hq1 hnq (X := (Tp T : ℝ) / q) le_rfl
    have h3 : Real.sqrt (2 * Lx n T) ≤ 5 * Λ n T := by
      apply Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    calc Real.sqrt (1 / (q / 2) * Lx n T) * R ≤ Real.sqrt (2 * Lx n T) * Real.sqrt (n * ((Tp T : ℝ) / q)) := e
      _ ≤ (5 * Λ n T) * (2 * Q n T q) := mul_le_mul h3 h2 (Real.sqrt_nonneg _) (by positivity)
      _ = 10 * Λ n T * Q n T q := by ring
  -- √(Lx·Kc)·R ≤ 8Λ·Q
  have a2 : Real.sqrt (Lx n T * KcF n T q) * R ≤ 8 * Λ n T * Q n T q := by
    have e : Real.sqrt (Lx n T * KcF n T q) * R = Real.sqrt (Lx n T) * Real.sqrt ((n : ℝ) * Tp T) := by
      rw [hR, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul hLx0]; congr 1; field_simp
    have h3 : Real.sqrt (Lx n T) ≤ 4 * Λ n T := Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
    rw [e]
    calc Real.sqrt (Lx n T) * Real.sqrt ((n : ℝ) * Tp T) ≤ (4 * Λ n T) * (2 * Q n T q) :=
          mul_le_mul h3 hnT2 (Real.sqrt_nonneg _) (by positivity)
      _ = 8 * Λ n T * Q n T q := by ring
  -- (2D+1)·BP·R ≤ 186000Λ⁹Q
  have a3 : (2 * (Dn (Tp T) : ℝ) + 1) * BPF n T q A * R ≤ 186000 * Λ n T ^ 9 * Q n T q := by
    calc (2 * (Dn (Tp T) : ℝ) + 1) * BPF n T q A * R ≤ (3 * Λ n T) * (BPF n T q A * Real.sqrt ((n : ℝ) * Tp T)) := by
          rw [mul_assoc]; exact mul_le_mul (by linarith) (mul_le_mul_of_nonneg_left hRle hB0) (by positivity)
            (by positivity)
      _ ≤ (3 * Λ n T) * (62000 * Λ n T ^ 8 * Q n T q) := mul_le_mul_of_nonneg_left hBP (by positivity)
      _ = 186000 * Λ n T ^ 9 * Q n T q := by ring
  have hβ : βF n T q A = 4 * Real.sqrt (1 / (q / 2) * Lx n T) + 4 * Real.sqrt (Lx n T * KcF n T q) +
      (2 * (Dn (Tp T) : ℝ) + 1) * BPF n T q A + 4 * Real.sqrt (Lx n T * KcF n T q) +
      4 * Real.sqrt (1 / (q / 2) * Lx n T) := by
    unfold βF Pool.P0282.β₀; rw [BP_P0]; rfl
  rw [hβ]
  have hQ0 : 0 ≤ Q n T q := by linarith
  have p9 : Λ n T ≤ Λ n T ^ 9 := by simpa using pow_le_pow_right₀ hΛ (show 1 ≤ 9 by norm_num)
  have u := mul_le_mul_of_nonneg_right p9 hQ0
  nlinarith

open Pool.P0291 in
theorem ρF_le : (2 * n + 1) * ρF n T q A ≤ 600 * Λ n T ^ 2 * Q n T q ∧ 0 ≤ ρF n T q A := by
  have hΛ := Λ_ge n T
  have hLx := Lx_le n T
  have hLx0 := (Lx_pos n T).le
  have hs := one_le_sA n T q (le_trans hn hnT) hnq
  have hη := ηA_eq n T q hn hnT hq hq1 hnq
  obtain ⟨k1, k2, _, _, _⟩ := s_facts n T q hn hnT hq hq1 hnq
  have hα := αT_le n T q hn hnT hq hq1 hnq
  have hα0 := Pool.P0226.αT_nonneg (ι := CpG n (Tp T)) (η := ηA n T q) (L := LA T) (T := Tp T) (ηA_pos n T q)
    (δ := εA n T q) (by unfold εA; have := ηA_pos n T q; positivity)
  have hw := wEA_ge n T q A hq hq1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have e : ρF n T q A = Lx n T * sA n T q + Pool.P0226.αT (ι := CpG n (Tp T)) (ηA n T q) (LA T) (Tp T) (εA n T q) +
      Lx n T * sA n T q / (2 * wEA n T q A) := by
    unfold ρF Pool.P0243.ρOK; rw [hη]; field_simp
  have h3 : Lx n T * sA n T q / (2 * wEA n T q A) ≤ Lx n T * sA n T q := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [mul_nonneg hLx0 (by linarith : (0 : ℝ) ≤ sA n T q)]
  have h0 : 0 ≤ Lx n T * sA n T q / (2 * wEA n T q A) := by
    apply div_nonneg (mul_nonneg hLx0 (by linarith)) (by linarith)
  have hρ : ρF n T q A ≤ 94 * Λ n T ^ 2 * sA n T q := by
    rw [e]
    have : Lx n T * sA n T q ≤ 12 * Λ n T * sA n T q := mul_le_mul_of_nonneg_right hLx (by linarith)
    have hL2 : Λ n T * sA n T q ≤ Λ n T ^ 2 * sA n T q := by
      apply mul_le_mul_of_nonneg_right _ (by linarith); nlinarith
    linarith
  refine ⟨?_, by rw [e]; have := mul_nonneg hLx0 (by linarith : (0 : ℝ) ≤ sA n T q); linarith⟩
  have hns : (2 * (n : ℝ) + 1) * sA n T q ≤ 6 * Q n T q := by nlinarith
  calc (2 * (n : ℝ) + 1) * ρF n T q A ≤ (2 * n + 1) * (94 * Λ n T ^ 2 * sA n T q) :=
        mul_le_mul_of_nonneg_left hρ (by positivity)
    _ = 94 * Λ n T ^ 2 * ((2 * n + 1) * sA n T q) := by ring
    _ ≤ 94 * Λ n T ^ 2 * (6 * Q n T q) := mul_le_mul_of_nonneg_left hns (by positivity)
    _ ≤ 600 * Λ n T ^ 2 * Q n T q := by have := Q_ge_one n T q hn hnT hq hq1 hnq; nlinarith [sq_nonneg (Λ n T)]

end Scale

open Pool.P0291 in
set_option maxHeartbeats 8000000 in
/-- **The probing remainder at P0284's machine is `Õ(√(nT/q))`**: P0292's `GoodBound`. -/
theorem goodBound : GoodBound (100000000000000000 * 5 ^ 30) 30 := by
  intro n T _ q A _ hn hnT hq hq1 hnq ℓ rc₀
  refine (good_raw n T q A hn hnT hq hq1 ℓ rc₀).trans ?_
  have hK := KcF_pos n T q hq
  have hΛ := Λ_ge n T
  have hQ := Q_ge_one n T q hn hnT hq hq1 hnq
  have hQ0 : 0 ≤ Q n T q := by linarith
  have hD := Dn_le n T
  have hNs := Ns_le_r n T
  have hK0 := probeK0_le n T q A hn hnT hq hq1 hnq
  have hα := nαF_le n T q A hn hnT hq hq1 hnq
  have hβ := βF_le n T q A hn hnT hq hq1 hnq
  obtain ⟨hρ, hρ0⟩ := ρF_le n T q A hn hnT hq hq1 hnq
  have hCb := TCbF_le n T q A hn hnT hq hq1 hnq
  have hxf := Pool.P0282.xf_mul_T_le (n := n) (T := Tp T) (Kc := KcF n T q) hn
  have hnTp : Real.sqrt ((n : ℝ) * Tp T) ≤ 2 * Q n T q :=
    sqrt_le_Q n T q hn hnT hq hq1 hnq (X := (Tp T : ℝ)) (by rw [le_div_iff₀ hq]; nlinarith [(Nat.cast_nonneg (Tp T) : (0 : ℝ) ≤ Tp T)])
  have hαF0 := αF_nonneg n T q A hq hq1
  have hβF0 := βF_nonneg n T q A
  set S := (Dn (Tp T) * Sl n (Tp T) : ℝ) with hSdef
  have hS0 : 0 ≤ S := by positivity
  have hD0 : (0 : ℝ) ≤ Dn (Tp T) := Nat.cast_nonneg _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- probeK1 ≤ 2·Λ·S
  have hK1 : Pool.P0289.probeK1 (famM n T q A).P ≤ 2 * Λ n T * S := by
    unfold Pool.P0289.probeK1
    show ∑ j : Fin (Dn (Tp T)), xr n (Tp T) (KcF n T q) j * (2 * ∑ _j : Fin (Dn (Tp T)), (Sl n (Tp T) : ℝ)) ≤ _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
    have h1 := sum_xr_le (n := n) (T := Tp T) hK
    have hKr : (1 : ℝ) ≤ KcF n T q := by exact_mod_cast hK
    have h2 : (Dn (Tp T) : ℝ) / KcF n T q ≤ Λ n T := (div_le_self hD0 hKr).trans hD
    have : ∑ j : Fin (Dn (Tp T)), xr n (Tp T) (KcF n T q) j ≤ Λ n T := h1.trans h2
    have : 0 ≤ 2 * ((Dn (Tp T) : ℝ) * Sl n (Tp T)) := by positivity
    calc (∑ j : Fin (Dn (Tp T)), xr n (Tp T) (KcF n T q) j) * (2 * ((Dn (Tp T) : ℝ) * Sl n (Tp T))) ≤
        Λ n T * (2 * ((Dn (Tp T) : ℝ) * Sl n (Tp T))) := mul_le_mul_of_nonneg_right ‹_› this
      _ = 2 * Λ n T * S := by rw [hSdef]; ring
  have hCbe : (Tp T : ℝ) * Pool.P0243.Cb (ηA n T q) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
      (∑ j : Fin (M0 n T q A).P.D, ((M0 n T q A).P.sl j : ℝ)) (ηA n T q) ≤ 10000000 * Λ n T ^ 12 * Q n T q := hCb
  have hCb0 : 0 ≤ (Tp T : ℝ) * Pool.P0243.Cb (ηA n T q) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
      (∑ j : Fin (M0 n T q A).P.D, ((M0 n T q A).P.sl j : ℝ)) (ηA n T q) :=
    mul_nonneg (Nat.cast_nonneg _) (CbF_nonneg n T q A hn hnT hq hq1 hnq)
  have hK10 : 0 ≤ Pool.P0289.probeK1 (famM n T q A).P := by
    unfold Pool.P0289.probeK1
    exact Finset.sum_nonneg fun j _ => mul_nonneg (xr_pos hK j).le
      (by positivity)
  have hR0 : 0 ≤ Real.sqrt ((n : ℝ) * Tp T / KcF n T q) := Real.sqrt_nonneg _
  have hxT : Pool.P0282.xf n (Tp T) (KcF n T q) * Tp T ≤ 2 * (2 * Q n T q) := hxf.trans (by linarith)
  have hfin := good_final_arith (Λ n T) (Q n T q) S (Dn (Tp T)) n (αF n T q A) (βF n T q A)
    (Real.sqrt ((n : ℝ) * Tp T / KcF n T q)) (Pool.P0282.xf n (Tp T) (KcF n T q) * Tp T) (ρF n T q A)
    ((Tp T : ℝ) * Pool.P0243.Cb (ηA n T q) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
      (∑ j : Fin (M0 n T q A).P.D, ((M0 n T q A).P.sl j : ℝ)) (ηA n T q)) (Pool.P0289.probeK1 (famM n T q A).P)
    hΛ hQ hS0 hNs hD0 hD hn1 hαF0 hβF0 hR0 hα hβ hxT hρ0 hρ hK1 hK10 hCb0 hCbe
  have hK0' : Pool.P0289.probeK0 (famM n T q A).P (Tp T) (Lx n T) (Pool.P0282.xf n (Tp T) (KcF n T q)) (KcF n T q) 2 n
      (Tp T) (Dp (Tp T)) (Dp (Tp T)) (ΛbF n T q A) (ρF n T q A) (Pool.P0282.xf n (Tp T) (KcF n T q)) ≤
      S * Dn (Tp T) * ((4 * n + 2) * αF n T q A + 5 * βF n T q A * Real.sqrt ((n : ℝ) * Tp T / KcF n T q)) +
        Pool.P0282.xf n (Tp T) (KcF n T q) * Tp T * S +
        Dn (Tp T) * (S * ρF n T q A * (2 * S * (2 * n + 1) + 1) + S * (2 * n + 1) * ρF n T q A) := by
    have e : Pool.P0282.xf n (Tp T) (KcF n T q) * ((Tp T : ℝ) * S) = Pool.P0282.xf n (Tp T) (KcF n T q) * Tp T * S := by
      ring
    linarith [hK0]
  -- Λ^30 ≤ 5^30·Lg^30
  have hΛL := Pool.P0284.BB_le_Lg n T hn hnT
  have hΛ0 : (0 : ℝ) ≤ Λ n T := by linarith
  have h30 : Λ n T ^ 30 ≤ 5 ^ 30 * Pool.P0161.Lg n T ^ 30 := by
    have := pow_le_pow_left₀ hΛ0 hΛL 30; rwa [mul_pow] at this
  have hfin2 : 100000000000000000 * Λ n T ^ 30 * Q n T q ≤
      100000000000000000 * 5 ^ 30 * Pool.P0161.Lg n T ^ 30 * Real.sqrt (n * T / q) := by
    have := mul_le_mul_of_nonneg_right h30 hQ0
    show 100000000000000000 * Λ n T ^ 30 * Q n T q ≤ _
    nlinarith
  linarith


end Pool.P0294

