import Pool.P0239.ProbeCap
import Pool.P0238.Count
import Pool.P0255.CreditP
import Pool.P0247.Win

/-!
# P0194's probing term with CHECK-ROUND margins, the lifetime cap and positive-jump credit (pathwise)
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0203 Pool.P0176 Pool.P0065

namespace Pool.P0255

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- The largest rule margin of copy `x` over its CHECK rounds `[E x, e − 1)` (`0` if none): the margins that P0219's
check bound can use at a boundary `m < e` are those of rounds `m − 1 < e − 1`; the last round's margin never is. -/
noncomputable def ΛMc (e : ℕ) (x : ι) : ℝ :=
  if h : (Ico (P.E x) (e - 1)).Nonempty then (Ico (P.E x) (e - 1)).sup' h (P.Λ x) else 0

theorem Λ_le_ΛMc {e c : ℕ} (x : ι) (h1 : P.E x ≤ c) (h2 : c < e - 1) : P.Λ x c ≤ ΛMc P e x := by
  have hc : c ∈ Ico (P.E x) (e - 1) := Finset.mem_Ico.mpr ⟨h1, h2⟩
  unfold ΛMc
  rw [dif_pos ⟨c, hc⟩]
  exact Finset.le_sup' (P.Λ x) hc

theorem ΛMc_nonneg (hΛ0 : ∀ x c, 0 ≤ P.Λ x c) (e : ℕ) (x : ι) : 0 ≤ ΛMc P e x := by
  unfold ΛMc
  split_ifs with h
  · obtain ⟨c, hc⟩ := h
    exact (hΛ0 x c).trans (Finset.le_sup' (P.Λ x) hc)
  · exact le_rfl

theorem ΛMc_le_ΛM (e : ℕ) (x : ι) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c) : ΛMc P e x ≤ Pool.P0223.ΛM P e x := by
  unfold ΛMc
  split_ifs with h
  · refine Finset.sup'_le h _ fun c hc => ?_
    rw [Finset.mem_Ico] at hc
    exact Pool.P0223.Λ_le_ΛM P x hc.1 (by omega)
  · exact Pool.P0223.ΛM_nonneg P hΛ0 e x

/-- P0223's per-copy margin with the check-round maximum `ΛMc` in place of `ΛM`. -/
noncomputable def MOfWc (L : ℝ) (e : ℕ) (x : ι) : ℝ := Pool.P0219.MOfB P L (ΛMc P e x) x e

variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
variable (rc0 : RC P)

open Classical in
/-- **P0194's probing term, pathwise, with P0209's window, monotonicity and check hypotheses discharged** on the
event that every thread fits before `T` and the slot and `B̂` good events hold on the prefix of length `T`. The rates
must be nonincreasing in the thread index (coarser threads, lower index, get larger rates, as in P0150). Each copy's
end term is CAPPED: `(final rate)·min(margin + widths + Bmin, window length)` (P0223's `probe_pathD` has the uncapped
`(final rate)·(margin + widths + Bmin)`). Only the credit term (rate jumps × lead over BASE) remains, for P0154/P0162. -/
theorem probe_pathD2 (ω : ℕ → RC P) (T : ℕ) {L : ℝ} (hL : 0 < L) (hB : 0 < P.Bmin)
    (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j) (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i)
    (hcB : 0 ≤ P.cB) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    (hgS : ∀ x, Pool.P0158.GoodV (DS P ℓ ωs φ rc0 x) (gateS P ℓ ωs φ rc0 x) (rS P x) (Pool.P0158.rmax1 (rS P x)) L T
      (pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (pre P ω T)) :
    ∑ u ∈ range T, ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - bPol P ℓ ω u) ≤
      ∑ x ∈ univ.filter (fun x => P.E x < T),
        (Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x * min (MOfWc P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin)
            ((Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x : ℕ) : ℝ) +
          ∑ t ∈ Ico (P.E x + 1) (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x),
            (Pool.P0209.rateD P ℓ ωs φ ω t x - Pool.P0209.rateD P ℓ ωs φ ω (t - 1) x) *
              max 0 (-Pool.P0154.isum (fun t => ℓr P ℓ t x - bPol P ℓ ω t) (P.E x) t)) := by
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T
  -- window facts
  have hwin : ∀ x, P.E x < T → P.E x ≤ b x ∧ b x ≤ T ∧
      ∀ t < T, (x ∈ active P ℓ ω ωs φ t ↔ P.E x ≤ t ∧ t < b x) :=
    fun x hxT => Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hxT
  have hM0 : ∀ x, P.E x < T → 0 ≤ MOfWc P L (b x) x := by
    intro x _
    unfold MOfWc Pool.P0219.MOfB
    have := (Pool.P0158.widV_pos (V := ∑ s ∈ Ico (P.E x) (b x), rS P x s)
      (Pool.P0158.rmax1_pos (rS P x) (P.E x) (b x)) hL).le
    have := (Pool.P0158.widV_pos (V := ∑ _s ∈ Ico (P.E x) (b x), P.cB)
      (Pool.P0158.rmax1_pos (fun _ => P.cB) (P.E x) (b x)) hL).le
    have := ΛMc_nonneg P hΛ0 (b x) x
    linarith
  refine Pool.P0239.probe_totalD_le_cap P ℓ ωs φ ω T b (fun x => MOfWc P L (b x) x) hB hM0 (fun x hx => (hwin x hx).1)
    (fun x hx => (hwin x hx).2.1) (fun j => (hxr j).le) ?_ ?_ ?_
  · -- hout
    intro x u hu hout
    apply Pool.P0223.rateD_inactive P ℓ ω ωs φ hlay
    intro hact
    have hE := Pool.P0215.E_le_of_active P ℓ ω ωs φ hD hLv hlev hact
    by_cases hxT : P.E x < T
    · have := ((hwin x hxT).2.2 u hu).1 hact
      omega
    · omega
  · -- hmono
    intro x hxT t ht1 ht2
    have hw := (hwin x hxT).2.2
    have hbT := (hwin x hxT).2.1
    have ha1 : x ∈ active P ℓ ω ωs φ (t - 1) := (hw (t - 1) (by omega)).2 ⟨by omega, by omega⟩
    have ha2 : x ∈ active P ℓ ω ωs φ t := (hw t (by omega)).2 ⟨by omega, ht2⟩
    rw [Pool.P0223.rateD_active P ℓ ω ωs φ hD hLv hlev hlay (hfit (t - 1) (by omega)) ha1,
      Pool.P0223.rateD_active P ℓ ω ωs φ hD hLv hlev hlay (hfit t (by omega)) ha2]
    apply hanti
    show curT P.E P.thr0 P.D P.Bt x t ≤ curT P.E P.thr0 P.D P.Bt x (t - 1)
    exact curT_mono (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) x (by omega) (by omega)
  · -- hcheck
    intro x hxT m hEm hmb hBm
    have hw := (hwin x hxT).2.2
    have hbT := (hwin x hxT).2.1
    have h := Pool.P0219.check_bound P ℓ ωs φ rc0 ω T x (hgS x) hgB (b x) hbT
      (fun t h1 h2 => (hw t (by omega)).2 ⟨h1, h2⟩) m hEm hmb hBm (fun t h1 h2 => hfit t (by omega))
    refine h.trans ?_
    unfold MOfWc Pool.P0219.MOfB
    have hrS : ∀ s, 0 ≤ rS P x s := fun s => Pool.P0191.rC_nonneg 1 P.xr P.E P.thr0 P.Bt hxr x s
    have e1 : Pool.P0158.widV (∑ s ∈ Ico (P.E x) m, rS P x s) (Pool.P0158.rmax1 (rS P x) (P.E x) m) L ≤
        Pool.P0158.widV (∑ s ∈ Ico (P.E x) (b x), rS P x s) (Pool.P0158.rmax1 (rS P x) (P.E x) (b x)) L :=
      Pool.P0219.widV_mono2 hL.le (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
        fun s _ _ => hrS s) (Pool.P0219.rmax1_mono _ (by omega))
    have e2 : Pool.P0158.widV (∑ _s ∈ Ico (P.E x) m, P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) m) L ≤
        Pool.P0158.widV (∑ _s ∈ Ico (P.E x) (b x), P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) (b x)) L :=
      Pool.P0219.widV_mono2 hL.le (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
        fun s _ _ => hcB) (Pool.P0219.rmax1_mono _ (by omega))
    linarith [Λ_le_ΛMc P (e := b x) (c := m - 1) x (by omega) (by omega)]

open Classical in
/-- **P0194's probing term, pathwise, with the credit absorbed** (`probe_pathD` + `credit_D`): on the event that every
thread fits before `T` and the slot and `B̂` good events hold, the probing term is at most
`Σ_x (final rate)·min(margin + widths + Bmin, window length)` (the CAPPED end term; P0223's `probe_credit_pathD` has it
without the `min`) plus `(S'·Σ_j x_j)·(BASE − ALG)[0,T)` plus the per-thread slack of
`credit_D`, given ALG's interval guarantees `hint` (against BASE) and `hA` (against each copy over its active window). -/
theorem probe_credit_pathD2 (rc0 : RC P) (ω : ℕ → RC P) (T : ℕ) (hT : 1 ≤ T) {L : ℝ} (hL : 0 < L)
    (hB : 0 < P.Bmin) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j)
    (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i)
    (hcB : 0 ≤ P.cB) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    (hgS : ∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc0 x) (Pool.P0203.gateS P ℓ ωs φ rc0 x)
      (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T (Pool.P0203.pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (Pool.P0203.pre P ω T))
    (v : ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) {xf : ℝ} (hfl : ∀ j, xf ≤ P.xr j)
    (hint : ∀ a b, a ≤ b → b ≤ T →
      -Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) a b ≤
        ρ₀ + Pool.P0154.isum v a b + c * Real.sqrt ((b : ℝ) - a))
    (r : ι → ℕ → ℝ)
    (hA : ∀ x t, t ≤ T → P.E x < t → (∀ u, P.E x ≤ u → u < t → x ∈ active P ℓ ω ωs φ u) →
      Pool.P0154.isum (fun u => aPol P ℓ ωs φ ω u) (P.E x) t ≤
        Pool.P0154.isum (fun u => ℓr P ℓ u x) (P.E x) t + r x t) :
    ∑ u ∈ range T, ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - bPol P ℓ ω u) ≤
      ∑ x ∈ univ.filter (fun x => P.E x < T),
          Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x *
            min (MOfWc P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin)
              ((Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x : ℕ) : ℝ)
        + (((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) 0 T
        + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * (Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * c *
            (Real.sqrt T * Real.sqrt (2 * (Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card + 1))
          + ∑ i ∈ Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j, max 0 (r i.1 i.2))) := by
  have h1 := probe_pathD2 P ℓ ωs φ hD hLv hlev rc0 ω T hL hB hlay hxr hanti hcB hΛ0 hfit hgS hgB
  have h2 := Pool.P0255.credit_DP P ℓ ωs φ hD hLv hlev ω T hlay hfit hT hxr hanti hfl v ρ₀ c hv hρ₀ hc hint r hA
  rw [Finset.sum_add_distrib] at h1
  linarith


open Classical in
/-- **The non-absorbed part of the refined pathwise bound** (`probe_credit_pathD2`): capped end terms with
check-round margins, and the per-thread credit slack over the positive jumps `WjP`. -/
noncomputable def restD2 (T : ℕ) (L : ℝ) (v : ℕ → ℝ) (ρ₀ c : ℝ) (r : ι → ℕ → ℝ) (xf : ℝ) (ω : ℕ → RC P) : ℝ :=
  ∑ x ∈ univ.filter (fun x => P.E x < T),
      Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x *
        min (MOfWc P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin)
          ((Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x : ℕ) : ℝ)
    + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
        (2 * (Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card + 1)
      + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
      + (∑ j : Fin P.D, (P.sl j : ℝ)) * c *
        (Real.sqrt T * Real.sqrt (2 * (Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card + 1))
      + ∑ i ∈ Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j, max 0 (r i.1 i.2))

/-- The pathwise bound in the `κ·(BASE − ALG) + restD2` form. -/
theorem probe_le_restD2 (ω : ℕ → RC P) (T : ℕ) (hT : 1 ≤ T) {L : ℝ} (hL : 0 < L)
    (hB : 0 < P.Bmin) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j)
    (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i)
    (hcB : 0 ≤ P.cB) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    (hgS : ∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc0 x) (Pool.P0203.gateS P ℓ ωs φ rc0 x)
      (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T (Pool.P0203.pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (Pool.P0203.pre P ω T))
    (v : ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) {xf : ℝ} (hfl : ∀ j, xf ≤ P.xr j)
    (hint : ∀ a b, a ≤ b → b ≤ T →
      -Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) a b ≤
        ρ₀ + Pool.P0154.isum v a b + c * Real.sqrt ((b : ℝ) - a))
    (r : ι → ℕ → ℝ)
    (hA : ∀ x t, t ≤ T → P.E x < t → (∀ u, P.E x ≤ u → u < t → x ∈ active P ℓ ω ωs φ u) →
      Pool.P0154.isum (fun u => aPol P ℓ ωs φ ω u) (P.E x) t ≤
        Pool.P0154.isum (fun u => ℓr P ℓ u x) (P.E x) t + r x t) :
    ∑ u ∈ range T, Pool.P0228.probeU P ℓ ωs φ ω u ≤
      ((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          ∑ u ∈ range T, (bPol P ℓ ω u - aPol P ℓ ωs φ ω u)
        + restD2 P ℓ ωs φ hD hLv hlev T L v ρ₀ c r xf ω := by
  have h := probe_credit_pathD2 P ℓ ωs φ hD hLv hlev rc0 ω T hT hL hB hlay hxr hanti hcB hΛ0 hfit hgS hgB v ρ₀ c
    hv hρ₀ hc hfl hint r hA
  unfold Pool.P0228.probeU restD2
  unfold Pool.P0154.isum at h ⊢
  beta_reduce at h
  rw [Finset.range_eq_Ico] at h ⊢
  linarith

/-- P0238's `MOfW_le` for the check-round margin `MOfWc`, with the margins bounded by the thread of the NEXT round
(`Λ x c ≤ Λbar(curT x (c + 1))`, the thread P0235/P0242's rule link `hΛ'` reads): every check round `c < b − 1` of a copy
ending in thread `j` has `curT x (c + 1) ≥ j`. -/
theorem MOfWc_le (ω : ℕ → RC P) (T : ℕ) {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ P.xr j) (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i))) (hΘ : ∀ f, (P.thr0 f : ℝ) ≤ Θ)
    (hcB : 0 ≤ P.cB) (Λbar : ℕ → ℝ) (hΛ0 : ∀ i, 0 ≤ Λbar i) (hΛa : ∀ i i', i ≤ i' → Λbar i' ≤ Λbar i)
    (hΛn : ∀ x c, P.E x ≤ c → P.Λ x c ≤ Λbar (curT P.E P.thr0 P.D P.Bt x (c + 1)))
    (j : ℕ) {x : ι} (hx' : x ∈ Pool.P0238.endIn P ℓ ωs φ hD hLv hlev ω T j) (len : ℕ)
    (hlen : Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x ≤ len) :
    MOfWc P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x ≤
      Λbar j + Pool.P0222.Wocc L xmin M ρ nn TT Θ len + Pool.P0158.widV (len * P.cB) (max 1 P.cB) L := by
  simp only [Pool.P0238.endIn, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
  obtain ⟨hxT, hEb, hend⟩ := hx'
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x
  unfold MOfWc Pool.P0219.MOfB
  have hΛM : ΛMc P b x ≤ Λbar j := by
    unfold ΛMc
    split_ifs with h
    · refine Finset.sup'_le h _ fun c hc => (hΛn x c (Finset.mem_Ico.mp hc).1).trans (hΛa _ _ ?_)
      rw [Finset.mem_Ico] at hc
      rw [← hend]
      exact curT_mono (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) x (by omega) (by omega)
    · exact hΛ0 j
  have hW : Pool.P0158.widV (∑ s ∈ Ico (P.E x) b, Pool.P0203.rS P x s) (Pool.P0158.rmax1 (Pool.P0203.rS P x) (P.E x) b) L
      ≤ Pool.P0222.Wocc L xmin M ρ nn TT Θ len :=
    (Pool.P0222.widV_le_occ P x hL hxm hxm1 hxr hn hT hM hρ0 hB hρ hx0 hx (hΘ x) (fun _ => le_rfl)).trans
      (Pool.P0222.Wocc_mono hL hM hlen)
  have hWB : Pool.P0158.widV (∑ _s ∈ Ico (P.E x) b, P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) b) L ≤
      Pool.P0158.widV (len * P.cB) (max 1 P.cB) L := by
    refine Pool.P0219.widV_mono2 hL ?_ (Pool.P0238.rmax1_const_le hcB _ _)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hcB
  linarith

open Classical in
/-- Thresholded count `C_j` of P0238: `0` for threads at the floor. -/
noncomputable def Cp (T : ℕ) (xf : ℝ) (j : Fin P.D) : ℕ :=
  if P.xr j ≤ xf then 0 else ((range T).filter (fun t => canonT P.D P.Bt t = j)).card

theorem card_WjP_le (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t)) (xf : ℝ) (j : Fin P.D) :
    ((Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card : ℝ) ≤ (∑ j : Fin P.D, (P.sl j : ℝ)) * Cp P T xf j := by
  unfold Pool.P0255.WjP Cp
  split_ifs
  · simp
  · exact Pool.P0223.card_Wj_le_canon P ℓ ωs φ hD hLv hlev ω T hlay hfit j

theorem sum_winP_le (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t)) (v : ℕ → ℝ) (hv : ∀ u, 0 ≤ v u) (ρ₁ : ℝ) (hρ₁ : 0 ≤ ρ₁)
    (xf : ℝ) (j : Fin P.D) :
    ∑ i ∈ Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j, max 0 (ρ₁ + Pool.P0154.isum v (P.E i.1) i.2) ≤
      (Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card * ρ₁ +
        (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T := by
  unfold Pool.P0255.WjP
  split_ifs
  · simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul, zero_add]
    exact mul_nonneg (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _) (Pool.P0154.isum_nonneg v hv _ _)
  · exact Pool.P0247.sum_win_le P ℓ ωs φ hD hLv hlev ω T hlay hfit v hv ρ₁ hρ₁ j

open Classical in
/-- **`restD2` bounded by counts (pathwise, on no-overflow), window-form copy budgets `r x t = ρ₁ + Σ_{[E x,t)} v`.**
Only threads ABOVE the rate floor `xf` pay `x_j·S'(C_j + N_j)·Mb_j` and per-jump credit; all copies ending at the
floor together pay `xf·T·S'`. Margins are bounded by the NEXT round's thread (`hΛn`). -/
theorem restD2_le (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ P.xr j) (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i)))
    (Θn : ℕ) (hΘn : ∀ f, P.thr0 f ≤ Θn) (hΘ : (Θn : ℝ) ≤ Θ)
    (hcB : 0 ≤ P.cB) (Λbar : ℕ → ℝ) (hΛ0 : ∀ i, 0 ≤ Λbar i) (hΛa : ∀ i i', i ≤ i' → Λbar i' ≤ Λbar i)
    (hΛn : ∀ x c, P.E x ≤ c → P.Λ x c ≤ Λbar (curT P.E P.thr0 P.D P.Bt x (c + 1)))
    (v : ℕ → ℝ) (hv : ∀ u, 0 ≤ v u) (ρ₀ c : ℝ) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (ρ₁ : ℝ) (hρ₁ : 0 ≤ ρ₁)
    (xf : ℝ) (hxf : 0 ≤ xf) :
    restD2 P ℓ ωs φ hD hLv hlev T L v ρ₀ c (fun x t => ρ₁ + Pool.P0154.isum v (P.E x) t) xf ω ≤
      ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
          (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
            + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card)) *
          (if xf < P.xr j then
            Λbar j + Pool.P0222.Wocc L xmin M ρ nn TT Θ (Pool.P0238.lenOf Θn T P.Bt j)
              + Pool.P0158.widV ((Pool.P0238.lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L + P.Bmin
           else 0)
        + xf * (T * ∑ j : Fin P.D, (P.sl j : ℝ))
        + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) * Cp P T xf j) + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * c * (Real.sqrt T *
              Real.sqrt (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) * Cp P T xf j) + 1))
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Cp P T xf j * ρ₁
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T) := by
  set S' := ∑ j : Fin P.D, (P.sl j : ℝ)
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hxr0 : ∀ j, 0 ≤ P.xr j := fun j => hxm.le.trans (hxr j)
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T
  set rate := fun x => Pool.P0209.rateD P ℓ ωs φ ω (b x - 1) x
  set Mb : Fin P.D → ℝ := fun j => Λbar j + Pool.P0222.Wocc L xmin M ρ nn TT Θ (Pool.P0238.lenOf Θn T P.Bt j)
      + Pool.P0158.widV ((Pool.P0238.lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L + P.Bmin
  have hMb0 : ∀ j, 0 ≤ Mb j := by
    intro j
    have h1 : 0 ≤ Pool.P0222.Wocc L xmin M ρ nn TT Θ (Pool.P0238.lenOf Θn T P.Bt j) := by
      unfold Pool.P0222.Wocc; positivity
    have h2 : 0 ≤ Pool.P0158.widV ((Pool.P0238.lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L := by
      unfold Pool.P0158.widV
      have : 0 ≤ max 1 P.cB := le_trans zero_le_one (le_max_left _ _)
      positivity
    have h3 : (0 : ℝ) ≤ P.Bmin := Nat.cast_nonneg _
    show 0 ≤ Λbar j + _ + _ + (P.Bmin : ℝ)
    linarith [hΛ0 j]
  -- end term: cap at the window, threshold at `xf`
  have hpt : ∀ x ∈ univ.filter (fun x => P.E x < T),
      rate x * min (MOfWc P L (b x) x + P.Bmin) ((b x - P.E x : ℕ) : ℝ) ≤
        (if xf < rate x then rate x * (MOfWc P L (b x) x + P.Bmin) else 0) + xf * ((b x - P.E x : ℕ) : ℝ) := by
    intro x _
    have hr0 : 0 ≤ rate x := Finset.sum_nonneg fun s _ => by split_ifs <;> simp [hxr0]
    have hw0 : (0 : ℝ) ≤ ((b x - P.E x : ℕ) : ℝ) := Nat.cast_nonneg _
    split_ifs with h
    · have := mul_le_mul_of_nonneg_left (min_le_left (MOfWc P L (b x) x + P.Bmin) ((b x - P.E x : ℕ) : ℝ)) hr0
      nlinarith
    · push Not at h
      have h1 := mul_le_mul_of_nonneg_left (min_le_right (MOfWc P L (b x) x + P.Bmin) ((b x - P.E x : ℕ) : ℝ)) hr0
      have h2 := mul_le_mul_of_nonneg_right h hw0
      linarith
  have hwin := Pool.P0239.sum_window_le P ℓ ωs φ hD hLv hlev ω T hfit
  set M' : ι → ℝ := fun x => if xf < rate x then MOfWc P L (b x) x else -(P.Bmin : ℝ)
  have hsel : ∑ x ∈ univ.filter (fun x => P.E x < T),
      (if xf < rate x then rate x * (MOfWc P L (b x) x + P.Bmin) else 0) =
      ∑ x ∈ univ.filter (fun x => P.E x < T), rate x * (M' x + P.Bmin) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [M']
    split_ifs <;> ring
  have hend := Pool.P0238.end_term_le P ℓ ωs φ hD hLv hlev ω T hlay hfit hxr0 M'
    (fun j => if xf < P.xr j then Mb j else 0) (fun j => by split_ifs; exact hMb0 j; exact le_rfl)
    (fun j x hxe => by
      have hxe' := hxe
      simp only [Pool.P0238.endIn, Finset.mem_filter, Finset.mem_univ, true_and] at hxe'
      obtain ⟨hxT, hEb, hend⟩ := hxe'
      have hw := Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hxT
      have hb1 : b x = Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x := rfl
      have ha : x ∈ active P ℓ ω ωs φ (b x - 1) := (hw.2.2 (b x - 1) (by omega)).2 ⟨by omega, by omega⟩
      have hrate : rate x = P.xr j := by
        show Pool.P0209.rateD P ℓ ωs φ ω (b x - 1) x = P.xr j
        rw [Pool.P0223.rateD_active P ℓ ω ωs φ hD hLv hlev hlay (hfit _ (by omega)) ha]
        congr 1; exact Fin.ext hend
      simp only [M', hrate]
      split_ifs with h
      · have hlen : b x - P.E x ≤ Pool.P0238.lenOf Θn T P.Bt j := by
          unfold Pool.P0238.lenOf
          split_ifs with hj
          · exact Pool.P0238.life_le P ℓ ωs φ hD hLv hlev ω T hB Θn hΘn j hj hxe
          · omega
        have := MOfWc_le P ℓ ωs φ hD hLv hlev ω T hL hxm hxm1 hxr hn hT hM hρ0 hB hρ hx0 hx
          (fun f => le_trans (by exact_mod_cast hΘn f) hΘ) hcB Λbar hΛ0 hΛa hΛn j hxe _ hlen
        show _ ≤ Λbar j + _ + _ + (P.Bmin : ℝ)
        linarith
      · simp)
  have hendT : ∑ x ∈ univ.filter (fun x => P.E x < T),
      rate x * min (MOfWc P L (b x) x + P.Bmin) ((b x - P.E x : ℕ) : ℝ) ≤
      ∑ j : Fin P.D, P.xr j * (S' * (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
            + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card)) *
          (if xf < P.xr j then Mb j else 0) + xf * (T * S') := by
    calc _ ≤ ∑ x ∈ univ.filter (fun x => P.E x < T),
          ((if xf < rate x then rate x * (MOfWc P L (b x) x + P.Bmin) else 0) + xf * ((b x - P.E x : ℕ) : ℝ)) :=
          Finset.sum_le_sum hpt
      _ = _ + xf * ∑ x ∈ univ.filter (fun x => P.E x < T), ((b x - P.E x : ℕ) : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by rw [hsel]; gcongr
  -- slack
  have hslack : ∀ j : Fin P.D,
      S' * ρ₀ * (2 * (Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card + 1)
        + S' * Pool.P0154.isum v 0 T
        + S' * c * (Real.sqrt T * Real.sqrt (2 * (Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card + 1))
        + ∑ i ∈ Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j,
            max 0 (ρ₁ + Pool.P0154.isum v (P.E i.1) i.2) ≤
      S' * ρ₀ * (2 * (S' * Cp P T xf j) + 1)
        + S' * Pool.P0154.isum v 0 T
        + S' * c * (Real.sqrt T * Real.sqrt (2 * (S' * Cp P T xf j) + 1))
        + S' * Cp P T xf j * ρ₁ + S' * Pool.P0154.isum v 0 T := by
    intro j
    have hW := card_WjP_le P ℓ ωs φ hD hLv hlev ω T hlay hfit xf j
    have hr := sum_winP_le P ℓ ωs φ hD hLv hlev ω T hlay hfit v hv ρ₁ hρ₁ xf j
    set W := (Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card
    have hsq : Real.sqrt (2 * (W : ℝ) + 1) ≤ Real.sqrt (2 * (S' * Cp P T xf j) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have e1 : S' * ρ₀ * (2 * W + 1) ≤ S' * ρ₀ * (2 * (S' * Cp P T xf j) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hS0 hρ₀)
    have e2 : S' * c * (Real.sqrt T * Real.sqrt (2 * W + 1)) ≤
        S' * c * (Real.sqrt T * Real.sqrt (2 * (S' * Cp P T xf j) + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)) (mul_nonneg hS0 hc)
    have e3 : (W : ℝ) * ρ₁ ≤ S' * Cp P T xf j * ρ₁ := mul_le_mul_of_nonneg_right hW hρ₁
    linarith
  unfold restD2
  have hsl := Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin P.D))) =>
    mul_le_mul_of_nonneg_left (hslack j) (hxr0 j)
  linarith [hendT]

theorem WjP_subset (ω : ℕ → RC P) (T : ℕ) (xf : ℝ) (j : Fin P.D) :
    Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j ⊆ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j := by
  unfold Pool.P0255.WjP; split_ifs
  · exact Finset.empty_subset _
  · exact le_rfl

theorem MOfWc_le_MOfW (L : ℝ) (e : ℕ) (x : ι) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c) :
    MOfWc P L e x ≤ Pool.P0223.MOfW P L e x := by
  unfold MOfWc Pool.P0223.MOfW Pool.P0219.MOfB
  linarith [ΛMc_le_ΛM P e x hΛ0]

/-- **The refinement is never worse**: `restD2 ≤` P0239's `restDcap` (check-round margins `≤` all-round margins,
positive jumps `⊆` all jumps), for nonnegative rates, margins, `ρ₀`, `c`. -/
theorem restD2_le_restDcap (hxr0 : ∀ j, 0 ≤ P.xr j) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c) (T : ℕ) (L : ℝ) (v : ℕ → ℝ)
    (ρ₀ c : ℝ) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (r : ι → ℕ → ℝ) (xf : ℝ) (ω : ℕ → RC P) :
    restD2 P ℓ ωs φ hD hLv hlev T L v ρ₀ c r xf ω ≤
      Pool.P0239.restDcap P ℓ ωs φ hD hLv hlev T L v ρ₀ c r ω := by
  unfold restD2 Pool.P0239.restDcap
  have hS0 : 0 ≤ ∑ j : Fin P.D, (P.sl j : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  refine add_le_add (Finset.sum_le_sum fun x _ => ?_) (Finset.sum_le_sum fun j _ => ?_)
  · refine mul_le_mul_of_nonneg_left (min_le_min_right _ ?_)
      (Finset.sum_nonneg fun s _ => by split_ifs <;> simp [hxr0])
    linarith [MOfWc_le_MOfW P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x hΛ0]
  · refine mul_le_mul_of_nonneg_left ?_ (hxr0 j)
    have hsub := WjP_subset P ℓ ωs φ hD hLv hlev ω T xf j
    have hcard : ((Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card : ℝ) ≤
        (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card := by exact_mod_cast Finset.card_le_card hsub
    have e1 := mul_le_mul_of_nonneg_left (show 2 * ((Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card : ℝ) + 1
      ≤ 2 * (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1 by linarith) (mul_nonneg hS0 hρ₀)
    have e2 : Real.sqrt (2 * ((Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j).card : ℝ) + 1) ≤
        Real.sqrt (2 * (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1) := Real.sqrt_le_sqrt (by linarith)
    have e3 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 (Real.sqrt_nonneg (T : ℝ)))
      (mul_nonneg hS0 hc)
    have e4 : ∑ i ∈ Pool.P0255.WjP P ℓ ωs φ hD hLv hlev ω T xf j, max 0 (r i.1 i.2) ≤
        ∑ i ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j, max 0 (r i.1 i.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => le_max_left _ _
    linarith

end Pool.P0255
