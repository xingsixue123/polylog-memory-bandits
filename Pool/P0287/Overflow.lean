import Pool.P0284.Memory
import Pool.P0221.Overflow
import Pool.P0257.Fit
import Pool.P0287.Numerics

/-!
# The overflow term at P0284's machine (P0262's F7, overflow piece)

* `ovf_famM`: P0221's `sum_ovf_le` with every hypothesis discharged at `famM n T q A` (process horizon `Tp T`), composed
  with `ovfB_le`: `E_arr[ovf] ≤ 1/(Tp+1)²`; `Tp_mul_ovf_famM`: the machine bound's term `Tp·E_arr[ovf] ≤ 1/(Tp+1)`.
* `QF`: P0283's `QG` for `famM` (P0236's self-rounding ALG on P0284's margins `P1`).
* `notFitAll_famM`: P0257's `sum_not_fitAll_le` for `QF`, every hypothesis discharged, composed with `ovfB_le`:
  the averaged `P(¬FitAll) ≤ 1/(Tp+1)²` — the bound `B` of P0283's `badTermP_twin_avg1` for `famM`.
* Helpers (hypothesis discharges reusable by other F7 steps): `hlevLt_Tp`, `xmin_pos`, `one_le_inv_xmin`.
-/

namespace Pool.P0287

attribute [local instance] Pool.P0082.coinFintype

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0201 Pool.P0261 Pool.P0284

variable (n T : ℕ) [NeZero n] (q : ℝ) (A : Pool.P0050.CoinAlg n)

theorem hlevLt_Tp : ∀ a < Tp T, ∀ r < Dn (Tp T), Pool.P0085.levTh (Ld (Tp T)) (Bt (Tp T)) r a ≤ Ld (Tp T) := by
  intro a _ r _
  have := Pool.P0062.levPR_le (Ld (Tp T)) ((a + 1) / Bt (Tp T) r - 1)
  unfold Pool.P0085.levTh; omega

theorem xmin_pos (hq : 0 < q) : (0 : ℝ) < 1 / (θc n (Tp T) (Kq q) : ℝ) := by
  have := Kc_pos (n := n) (T := Tp T) (Kq_pos q hq); unfold θc; positivity

theorem one_le_inv_xmin (hq : 0 < q) : (1 : ℝ) ≤ 1 / (1 / (θc n (Tp T) (Kq q) : ℝ)) := by
  rw [one_div_one_div]
  have := Kc_pos (n := n) (T := Tp T) (Kq_pos q hq); unfold θc
  exact_mod_cast le_trans this (le_max_left _ _)

set_option maxHeartbeats 2000000 in
/-- **P0221's averaged overflow term at P0284's machine is `≤ 1/(Tp+1)²`.** -/
theorem ovf_famM (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (ℓ : LossSeq n) (rc₀ : RC (famM n T q A).P) :
    ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
      Pool.P0217.ovf (famM n T q A) (Tp T) ℓ rc₀ arr ≤ 1 / ((Tp T : ℝ) + 1) ^ 2 := by
  have hTp : 1 ≤ Tp T := Tp_pos T
  have h := (Pool.P0221.sum_ovf_le (m := famM n T q A) (T := Tp T) rfl (famM_cap n T q A) ℓ rc₀
    (famM_isLaw n T q A hq hq1) (NeZero.pos _)
    (CpG_E_mono n (Tp T)) (btHyp (Tp T)) (by show 0 < Lv (Tp T); unfold Lv; omega) (hlev (Tp T))
    (xmin := 1 / (θc n (Tp T) (Kq q) : ℝ)) (xmin_pos n T q hq)
    (fun j => xmin_le (Kq_pos q hq) j) (one_le_inv_xmin n T q hq)
    (Rc_pos (Tp T)) (by rw [one_div_one_div]; exact hT_cover n (Tp T) (Kq q))
    (M0 n (Tp T)) (kk n (Tp T)) (hM0 n (Tp T)) (hk n (Tp T)) (hp n (Tp T))
    (hlevLt_Tp T) (s0 n (Tp T)) _ (hs hTp) (Sp n (Tp T)) (hM0S n (Tp T)) (hρS hn hTp)
    (fun _ => hsl n (Tp T))).trans (Pool.P0287.ovfB_le n (Tp T) hn hTp)
  convert h using 2
  exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)


/-- The self-rounding ALG's process on P0284's margins (P0283's `QG` for `famM`). -/
noncomputable abbrev QF : ParD n (CpG n (Tp T)) :=
  Pool.P0236.PG (P1 n T q A) (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)


/-- The machine bound's overflow term `Tp·E_arr[ovf]` (P0217/P0221/P0246) is `≤ 1/(Tp+1)` at P0284's machine. -/
theorem Tp_mul_ovf_famM (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (ℓ : LossSeq n) (rc₀ : RC (famM n T q A).P) :
    (Tp T : ℝ) * ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
      Pool.P0217.ovf (famM n T q A) (Tp T) ℓ rc₀ arr ≤ 1 / ((Tp T : ℝ) + 1) := by
  have h := ovf_famM n T q A hn hq hq1 ℓ rc₀
  have hT0 : (0 : ℝ) ≤ Tp T := Nat.cast_nonneg _
  calc (Tp T : ℝ) * _ ≤ (Tp T : ℝ) * (1 / ((Tp T : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left h hT0
    _ ≤ ((Tp T : ℝ) + 1) * (1 / ((Tp T : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / ((Tp T : ℝ) + 1) := by field_simp

scoped instance : NeZero (QF n T q A).N := ⟨by show NA n T q ≠ 0; exact NeZero.ne _⟩

open Classical in
set_option maxHeartbeats 2000000 in
/-- **P0257's averaged `P(¬FitAll)` for the self-rounding ALG on P0284's margins is `≤ 1/(Tp+1)²`**: the bound `B`
of P0283's `badTermP_twin_avg1` for `famM`. -/
theorem notFitAll_famM (hn : 1 ≤ n) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (ℓ : LossSeq n) (rc₀ : RC (QF n T q A)) :
    ∑ ω2, Pool.P0048.wtv (Pool.P0091.pC (NE := Tp T) (D := (QF n T q A).D) (Lt := Ld (Tp T)) (K := (QF n T q A).K)
        (1 / (n : ℝ)) (qf n (Tp T))) ω2 *
      ∑ rc : Fin (Tp T) → RC (QF n T q A), Pool.P0202.pw (wR (QF n T q A)) rc *
        (if Pool.P0257.FitAll (QF n T q A) (Tp T) ℓ rc₀
            (Pool.P0082.ωsC (QF n T q A).E (Tp T) (QF n T q A).D (Ld (Tp T)) (QF n T q A).K ω2)
            (Pool.P0082.φC (Tp T) (QF n T q A).D (Ld (Tp T)) (QF n T q A).K ω2) rc then 0 else 1) ≤
      1 / ((Tp T : ℝ) + 1) ^ 2 := by
  have hTp : 1 ≤ Tp T := Tp_pos T
  have hps : 0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, by rw [div_le_one (by exact_mod_cast NeZero.pos n)]; exact_mod_cast NeZero.one_le⟩
  have h := (Pool.P0257.sum_not_fitAll_le (QF n T q A) rfl (P0_isLaw n T q A hq hq1) (NeZero.pos _)
    (T := Tp T) (Lt := Ld (Tp T)) ℓ rc₀ hps (qf_mem n (Tp T)).1 (qf_mem n (Tp T)).2
    (CpG_E_mono n (Tp T)) (btHyp (Tp T)) (by show 0 < Lv (Tp T); unfold Lv; omega) (hlev (Tp T))
    (xmin := 1 / (θc n (Tp T) (Kq q) : ℝ)) (xmin_pos n T q hq)
    (fun j => xmin_le (Kq_pos q hq) j) (one_le_inv_xmin n T q hq)
    (Rc_pos (Tp T)) (by rw [one_div_one_div]; exact hT_cover n (Tp T) (Kq q))
    (M0 n (Tp T)) (kk n (Tp T)) (hM0 n (Tp T)) (hk n (Tp T)) (hp n (Tp T))
    (hlevLt_Tp T) (s0 n (Tp T)) _ (hs hTp) (Sp n (Tp T)) (hM0S n (Tp T)) (hρS hn hTp)
    (fun _ => hsl n (Tp T))).trans (Pool.P0287.ovfB_le n (Tp T) hn hTp)
  convert h using 2
  exact congrArg (@Finset.univ _) (Subsingleton.elim _ _)

end Pool.P0287
