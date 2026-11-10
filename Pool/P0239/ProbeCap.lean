import Pool.P0228.ExpD

/-!
# Lifetime cap for P0194's probing term
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0203 Pool.P0176 Pool.P0065

namespace Pool.P0239

/-- **One member at a nondecreasing rate, with the final gap capped by the window length.** As P0209's
`member_rate_le`, but the final factor is `min (M + Bmin) (b − a)`: the gap since entry is at most the number of
rounds, since every gap is `≤ 1`. -/
theorem member_rate_le_cap (r g : ℕ → ℝ) (hg : ∀ t, g t ≤ 1) (a b Bmin : ℕ) (hab : a ≤ b) (hB : 0 < Bmin)
    (M : ℝ) (hM : 0 ≤ M) (hr0 : ∀ t, 0 ≤ r t)
    (hmono : ∀ t, a + 1 ≤ t → t < b → r (t - 1) ≤ r t)
    (hcheck : ∀ m, a < m → m < b → Bmin ∣ m → ∑ t ∈ Ico a m, g t ≤ M) :
    ∑ t ∈ Ico a b, r t * g t ≤
      r (b - 1) * min (M + Bmin) ((b - a : ℕ) : ℝ) +
        ∑ t ∈ Ico (a + 1) b, (r t - r (t - 1)) * max 0 (-Pool.P0154.isum g a t) := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · simp only [Finset.Ico_self, Finset.sum_empty, Nat.sub_self, Nat.cast_zero]
    have : (Finset.Ico (a + 1) a) = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this, Finset.sum_empty, add_zero]
    exact mul_nonneg (hr0 _) (le_min (by positivity) le_rfl)
  have h1 := Pool.P0154.abel_le r g a b hlt hmono
  have h2 := Pool.P0196.sum_le_of_checks g hg a b Bmin hab hB M hM hcheck
  have h2' : Pool.P0154.isum g a b ≤ ((b - a : ℕ) : ℝ) := by
    unfold Pool.P0154.isum
    calc ∑ t ∈ Ico a b, g t ≤ ∑ _t ∈ Ico a b, (1 : ℝ) := Finset.sum_le_sum fun t _ => hg t
      _ = ((b - a : ℕ) : ℝ) := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  have h3 : r (b - 1) * Pool.P0154.isum g a b ≤ r (b - 1) * min (M + Bmin) ((b - a : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (le_min h2 h2') (hr0 _)
  linarith

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- **P0209's `probe_totalD_le` with the lifetime cap** `min (M x + Bmin) (b x − E x)`. -/
theorem probe_totalD_le_cap (ω : ℕ → RC P) (T : ℕ) (b : ι → ℕ) (M : ι → ℝ) (hB : 0 < P.Bmin)
    (hM : ∀ x, P.E x < T → 0 ≤ M x) (hEb : ∀ x, P.E x < T → P.E x ≤ b x)
    (hbT : ∀ x, P.E x < T → b x ≤ T)
    (hxr : ∀ j, 0 ≤ P.xr j)
    (hout : ∀ x u, u < T → (u < P.E x ∨ b x ≤ u) → Pool.P0209.rateD P ℓ ωs φ ω u x = 0)
    (hmono : ∀ x, P.E x < T → ∀ t, P.E x + 1 ≤ t → t < b x →
      Pool.P0209.rateD P ℓ ωs φ ω (t - 1) x ≤ Pool.P0209.rateD P ℓ ωs φ ω t x)
    (hcheck : ∀ x, P.E x < T → ∀ m, P.E x < m → m < b x → P.Bmin ∣ m →
      ∑ t ∈ Ico (P.E x) m, (ℓr P ℓ t x - bPol P ℓ ω t) ≤ M x) :
    ∑ u ∈ range T, ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - bPol P ℓ ω u) ≤
      ∑ x ∈ Finset.univ.filter (fun x => P.E x < T),
        (Pool.P0209.rateD P ℓ ωs φ ω (b x - 1) x * min (M x + P.Bmin) ((b x - P.E x : ℕ) : ℝ) +
        ∑ t ∈ Ico (P.E x + 1) (b x), (Pool.P0209.rateD P ℓ ωs φ ω t x - Pool.P0209.rateD P ℓ ωs φ ω (t - 1) x) *
          max 0 (-Pool.P0154.isum (fun t => ℓr P ℓ t x - bPol P ℓ ω t) (P.E x) t)) := by
  simp only [Pool.P0209.sum_probeD_eq]
  rw [Finset.sum_comm]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => P.E x < T)]
  have hlate : ∑ x ∈ Finset.univ.filter (fun x => ¬ P.E x < T),
      ∑ u ∈ range T, Pool.P0209.rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) = 0 := by
    refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun u hu => ?_
    have h1 := (Finset.mem_filter.1 hx).2
    have h2 := Finset.mem_range.1 hu
    rw [hout x u h2 (Or.inl (by omega)), zero_mul]
  rw [hlate, add_zero]
  refine Finset.sum_le_sum fun x hx => ?_
  have hxT : P.E x < T := (Finset.mem_filter.1 hx).2
  have hwin : ∑ u ∈ range T, Pool.P0209.rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) =
      ∑ u ∈ Ico (P.E x) (b x), Pool.P0209.rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) := by
    rw [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le (P.E x)) ((hEb x hxT).trans (hbT x hxT)),
      ← Finset.sum_Ico_consecutive _ (hEb x hxT) (hbT x hxT)]
    have h1 : ∑ u ∈ Ico 0 (P.E x), Pool.P0209.rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) = 0 :=
      Finset.sum_eq_zero fun u hu => by
        have := Finset.mem_Ico.1 hu
        rw [hout x u (by omega) (Or.inl this.2), zero_mul]
    have h2 : ∑ u ∈ Ico (b x) T, Pool.P0209.rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) = 0 :=
      Finset.sum_eq_zero fun u hu => by
        have := Finset.mem_Ico.1 hu
        rw [hout x u this.2 (Or.inr this.1), zero_mul]
    rw [h1, h2, zero_add, add_zero]
  rw [hwin]
  have hg : ∀ t, ℓr P ℓ t x - bPol P ℓ ω t ≤ 1 := by
    intro t
    have h1 : ℓr P ℓ t x ≤ 1 := by unfold ℓr; cases ℓ t (P.arm x) <;> simp
    have h2 : 0 ≤ bPol P ℓ ω t := by
      unfold bPol
      exact Finset.sum_nonneg fun yB _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
    linarith
  have hr0 : ∀ t, 0 ≤ Pool.P0209.rateD P ℓ ωs φ ω t x := fun t =>
    Finset.sum_nonneg fun s _ => by split_ifs <;> simp [hxr]
  exact member_rate_le_cap (fun t => Pool.P0209.rateD P ℓ ωs φ ω t x) (fun t => ℓr P ℓ t x - bPol P ℓ ω t) hg
    (P.E x) (b x) P.Bmin (hEb x hxT) hB (M x) (hM x hxT) hr0 (hmono x hxT) (hcheck x hxT)

variable (rc0 : RC P)
variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)

open Classical in
/-- **P0194's probing term, pathwise, with P0209's window, monotonicity and check hypotheses discharged** on the
event that every thread fits before `T` and the slot and `B̂` good events hold on the prefix of length `T`. The rates
must be nonincreasing in the thread index (coarser threads, lower index, get larger rates, as in P0150). Each copy's
end term is CAPPED: `(final rate)·min(margin + widths + Bmin, window length)` (P0223's `probe_pathD` has the uncapped
`(final rate)·(margin + widths + Bmin)`). Only the credit term (rate jumps × lead over BASE) remains, for P0154/P0162. -/
theorem probe_pathD_cap (ω : ℕ → RC P) (T : ℕ) {L : ℝ} (hL : 0 < L) (hB : 0 < P.Bmin)
    (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j) (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i)
    (hcB : 0 ≤ P.cB) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    (hgS : ∀ x, Pool.P0158.GoodV (DS P ℓ ωs φ rc0 x) (gateS P ℓ ωs φ rc0 x) (rS P x) (Pool.P0158.rmax1 (rS P x)) L T
      (pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (pre P ω T)) :
    ∑ u ∈ range T, ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - bPol P ℓ ω u) ≤
      ∑ x ∈ univ.filter (fun x => P.E x < T),
        (Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x * min (Pool.P0223.MOfW P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin)
            ((Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x : ℕ) : ℝ) +
          ∑ t ∈ Ico (P.E x + 1) (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x),
            (Pool.P0209.rateD P ℓ ωs φ ω t x - Pool.P0209.rateD P ℓ ωs φ ω (t - 1) x) *
              max 0 (-Pool.P0154.isum (fun t => ℓr P ℓ t x - bPol P ℓ ω t) (P.E x) t)) := by
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T
  -- window facts
  have hwin : ∀ x, P.E x < T → P.E x ≤ b x ∧ b x ≤ T ∧
      ∀ t < T, (x ∈ active P ℓ ω ωs φ t ↔ P.E x ≤ t ∧ t < b x) :=
    fun x hxT => Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hxT
  have hM0 : ∀ x, P.E x < T → 0 ≤ Pool.P0223.MOfW P L (b x) x := by
    intro x _
    unfold Pool.P0223.MOfW Pool.P0219.MOfB
    have := (Pool.P0158.widV_pos (V := ∑ s ∈ Ico (P.E x) (b x), rS P x s)
      (Pool.P0158.rmax1_pos (rS P x) (P.E x) (b x)) hL).le
    have := (Pool.P0158.widV_pos (V := ∑ _s ∈ Ico (P.E x) (b x), P.cB)
      (Pool.P0158.rmax1_pos (fun _ => P.cB) (P.E x) (b x)) hL).le
    have := Pool.P0223.ΛM_nonneg P hΛ0 (b x) x
    linarith
  refine probe_totalD_le_cap P ℓ ωs φ ω T b (fun x => Pool.P0223.MOfW P L (b x) x) hB hM0 (fun x hx => (hwin x hx).1)
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
    unfold Pool.P0223.MOfW Pool.P0219.MOfB
    have hrS : ∀ s, 0 ≤ rS P x s := fun s => Pool.P0191.rC_nonneg 1 P.xr P.E P.thr0 P.Bt hxr x s
    have e1 : Pool.P0158.widV (∑ s ∈ Ico (P.E x) m, rS P x s) (Pool.P0158.rmax1 (rS P x) (P.E x) m) L ≤
        Pool.P0158.widV (∑ s ∈ Ico (P.E x) (b x), rS P x s) (Pool.P0158.rmax1 (rS P x) (P.E x) (b x)) L :=
      Pool.P0219.widV_mono2 hL.le (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
        fun s _ _ => hrS s) (Pool.P0219.rmax1_mono _ (by omega))
    have e2 : Pool.P0158.widV (∑ _s ∈ Ico (P.E x) m, P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) m) L ≤
        Pool.P0158.widV (∑ _s ∈ Ico (P.E x) (b x), P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) (b x)) L :=
      Pool.P0219.widV_mono2 hL.le (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
        fun s _ _ => hcB) (Pool.P0219.rmax1_mono _ (by omega))
    linarith [Pool.P0223.Λ_le_ΛM P (e := b x) (c := m - 1) x (by omega) (by omega)]

open Classical in
/-- **P0194's probing term, pathwise, with the credit absorbed** (`probe_pathD` + `credit_D`): on the event that every
thread fits before `T` and the slot and `B̂` good events hold, the probing term is at most
`Σ_x (final rate)·min(margin + widths + Bmin, window length)` (the CAPPED end term; P0223's `probe_credit_pathD` has it
without the `min`) plus `(S'·Σ_j x_j)·(BASE − ALG)[0,T)` plus the per-thread slack of
`credit_D`, given ALG's interval guarantees `hint` (against BASE) and `hA` (against each copy over its active window). -/
theorem probe_credit_pathD_cap (rc0 : RC P) (ω : ℕ → RC P) (T : ℕ) (hT : 1 ≤ T) {L : ℝ} (hL : 0 < L)
    (hB : 0 < P.Bmin) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j)
    (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i)
    (hcB : 0 ≤ P.cB) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    (hgS : ∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc0 x) (Pool.P0203.gateS P ℓ ωs φ rc0 x)
      (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T (Pool.P0203.pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (Pool.P0203.pre P ω T))
    (v : ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c)
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
            min (Pool.P0223.MOfW P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin)
              ((Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x : ℕ) : ℝ)
        + (((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) 0 T
        + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * c *
            (Real.sqrt T * Real.sqrt (2 * (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1))
          + ∑ i ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j, max 0 (r i.1 i.2))) := by
  have h1 := probe_pathD_cap P ℓ ωs φ rc0 hD hLv hlev ω T hL hB hlay hxr hanti hcB hΛ0 hfit hgS hgB
  have h2 := Pool.P0223.credit_D P ℓ ωs φ hD hLv hlev ω T hT hlay hfit hxr hanti v ρ₀ c hv hρ₀ hc hint r hA
  rw [Finset.sum_add_distrib] at h1
  linarith

open Classical in
/-- **The windows of the copies entering before `T` sum to at most `T·Σ_j sl_j`** when every thread fits before `T`
(each round has at most `Σ_j sl_j` active copies, P0223's `card_active_le`). -/
theorem sum_window_le (ω : ℕ → RC P) (T : ℕ) (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t)) :
    ∑ x ∈ univ.filter (fun x => P.E x < T),
        ((Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x : ℕ) : ℝ) ≤
      T * ∑ j : Fin P.D, (P.sl j : ℝ) := by
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T
  have hcount : ∀ x ∈ univ.filter (fun x => P.E x < T), ((b x - P.E x : ℕ) : ℝ) =
      ∑ t ∈ range T, if x ∈ active P ℓ ω ωs φ t then (1 : ℝ) else 0 := by
    intro x hx
    have hxT := (Finset.mem_filter.1 hx).2
    have hw := Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hxT
    have hbT : b x ≤ T := hw.2.1
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (range T).filter (fun t => x ∈ active P ℓ ω ωs φ t) = Ico (P.E x) (b x) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩; exact (hw.2.2 t h1).1 h2
      · rintro ⟨h1, h2⟩; exact ⟨by omega, (hw.2.2 t (by omega)).2 ⟨h1, h2⟩⟩
    rw [this, Nat.card_Ico]
  rw [Finset.sum_congr rfl hcount, Finset.sum_comm]
  calc ∑ t ∈ range T, ∑ x ∈ univ.filter (fun x => P.E x < T),
        (if x ∈ active P ℓ ω ωs φ t then (1 : ℝ) else 0)
      ≤ ∑ t ∈ range T, ((active P ℓ ω ωs φ t).card : ℝ) := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast Finset.card_le_card (fun x hx => (Finset.mem_filter.1 hx).2)
    _ ≤ ∑ _t ∈ range T, ∑ j : Fin P.D, (P.sl j : ℝ) :=
        Finset.sum_le_sum fun t ht => Pool.P0223.card_active_le P ℓ ωs φ (hfit t (Finset.mem_range.1 ht))
    _ = T * ∑ j : Fin P.D, (P.sl j : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

open Classical in
/-- **Split of the capped end term at a rate threshold `xf`.** Copies whose final rate is `≤ xf` cost at most
`xf × window`, and the windows sum to `≤ T·Σ_j sl_j` on fitting paths; only copies ending ABOVE the threshold pay
`margin + widths + Bmin`. -/
theorem capped_end_le (ω : ℕ → RC P) (T : ℕ) (L xf : ℝ) (hxf : 0 ≤ xf) (hxr : ∀ j, 0 ≤ P.xr j)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t)) :
    ∑ x ∈ univ.filter (fun x => P.E x < T),
        Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x *
          min (Pool.P0223.MOfW P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin)
            ((Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x : ℕ) : ℝ) ≤
      ∑ x ∈ univ.filter (fun x => P.E x < T),
          (if xf < Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x then
            Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x *
              (Pool.P0223.MOfW P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin) else 0)
        + xf * (T * ∑ j : Fin P.D, (P.sl j : ℝ)) := by
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T
  have hw := sum_window_le P ℓ ωs φ hD hLv hlev ω T hfit
  have hpt : ∀ x ∈ univ.filter (fun x => P.E x < T),
      Pool.P0209.rateD P ℓ ωs φ ω (b x - 1) x * min (Pool.P0223.MOfW P L (b x) x + P.Bmin) ((b x - P.E x : ℕ) : ℝ) ≤
        (if xf < Pool.P0209.rateD P ℓ ωs φ ω (b x - 1) x then
            Pool.P0209.rateD P ℓ ωs φ ω (b x - 1) x * (Pool.P0223.MOfW P L (b x) x + P.Bmin) else 0)
          + xf * ((b x - P.E x : ℕ) : ℝ) := by
    intro x _
    have hr0 : 0 ≤ Pool.P0209.rateD P ℓ ωs φ ω (b x - 1) x :=
      Finset.sum_nonneg fun s _ => by split_ifs <;> simp [hxr]
    have hw0 : (0 : ℝ) ≤ ((b x - P.E x : ℕ) : ℝ) := Nat.cast_nonneg _
    split_ifs with h
    · have := mul_le_mul_of_nonneg_left (min_le_left (Pool.P0223.MOfW P L (b x) x + P.Bmin)
        ((b x - P.E x : ℕ) : ℝ)) hr0
      nlinarith
    · push Not at h
      have h1 := mul_le_mul_of_nonneg_left (min_le_right (Pool.P0223.MOfW P L (b x) x + P.Bmin)
        ((b x - P.E x : ℕ) : ℝ)) hr0
      have h2 := mul_le_mul_of_nonneg_right h hw0
      linarith
  calc _ ≤ ∑ x ∈ univ.filter (fun x => P.E x < T),
        ((if xf < Pool.P0209.rateD P ℓ ωs φ ω (b x - 1) x then
            Pool.P0209.rateD P ℓ ωs φ ω (b x - 1) x * (Pool.P0223.MOfW P L (b x) x + P.Bmin) else 0)
          + xf * ((b x - P.E x : ℕ) : ℝ)) := Finset.sum_le_sum hpt
    _ = _ + xf * ∑ x ∈ univ.filter (fun x => P.E x < T), ((b x - P.E x : ℕ) : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := by gcongr

open Pool.P0228 in
/-- The non-absorbed part of the CAPPED pathwise bound (P0228's `restD` with the end term
`rate_end·min (margin + widths + Bmin) (window length)`). -/
noncomputable def restDcap (T : ℕ) (L : ℝ) (v : ℕ → ℝ) (ρ₀ c : ℝ) (r : ι → ℕ → ℝ) (ω : ℕ → RC P) : ℝ :=
  ∑ x ∈ univ.filter (fun x => P.E x < T),
      Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x *
        min (Pool.P0223.MOfW P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin)
          ((Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x : ℕ) : ℝ)
    + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
        (2 * (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1)
      + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
      + (∑ j : Fin P.D, (P.sl j : ℝ)) * c *
        (Real.sqrt T * Real.sqrt (2 * (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1))
      + ∑ i ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j, max 0 (r i.1 i.2))

variable (rc₀ : RC P)

open Classical in
/-- **P0194's probing term in expectation (P0217's `slotT` form, fixed sampling/filter bits).** With
`κ = (Σ_j sl_j)(Σ_j x_j)` and `X₁ = Σ_s x_s`:
`slotT ≤ κ·Σ_u E[bPol_u − aPol_u] + E[[G]·restDcap] + (X₁ + κ)·T·(P(overflow) + |ι|·2(T+1)²e^{−L} + 2(T+1)²e^{−L}
+ P(¬AlgOK))` (P0228's `slot_expect` with its `restD` replaced by the capped `restDcap ≤ restD`), where `G` = no overflow ∧ P0203's slot good event (all copies) ∧ P0216's `B̂` good event ∧ `AlgOK`. -/
theorem slot_expect_cap (hL : P.IsLaw) (hN : 0 < P.N) (T : ℕ) (hT : 1 ≤ T) {L : ℝ} (hLp : 0 < L)
    (hB : 0 < P.Bmin) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j) (hxr1 : ∀ j, P.xr j ≤ 1)
    (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i) (hcw : P.cB * P.wB = 1) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (v : ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (r : ι → ℕ → ℝ) :
    ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' * Pool.P0228.probeU P ℓ ωs φ (Pool.P0210.extR P rc₀ ω') u ≤
      ((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
            (bPol P ℓ (Pool.P0210.extR P rc₀ ω') u - aPol P ℓ ωs φ (Pool.P0210.extR P rc₀ ω') u)
        + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
            (if (∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t)) ∧
                (∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc₀ x) (Pool.P0203.gateS P ℓ ωs φ rc₀ x)
                  (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T ω) ∧
                Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc₀) (fun _ _ => true) (fun _ => P.cB)
                  (Pool.P0158.rmax1 (fun _ => P.cB)) L T ω ∧
                Pool.P0228.AlgOK P ℓ ωs φ T v ρ₀ c r (Pool.P0210.extR P rc₀ ω)
              then restDcap P ℓ ωs φ hD hLv hlev T L v ρ₀ c r (Pool.P0210.extR P rc₀ ω) else 0)
        + ((∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + (∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j)
            * T * ((∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
                (if ∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t) then 0 else 1))
              + Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L))
              + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)
              + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
                (if Pool.P0228.AlgOK P ℓ ωs φ T v ρ₀ c r (Pool.P0210.extR P rc₀ ω) then 0 else 1)) := by
  set κ := (∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j with hκdef
  have hκ : 0 ≤ κ := mul_nonneg (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _)
    (Finset.sum_nonneg fun j _ => (hxr j).le)
  have hcB : 0 ≤ P.cB := by linarith [(Pool.P0216.cB_ge_one P hL hcw).1]
  set Fit : (Fin T → RC P) → Prop := fun ω => ∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t)
  set GS : (Fin T → RC P) → Prop := fun ω => ∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc₀ x)
    (Pool.P0203.gateS P ℓ ωs φ rc₀ x) (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T ω
  set GB : (Fin T → RC P) → Prop := fun ω => Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc₀) (fun _ _ => true)
    (fun _ => P.cB) (Pool.P0158.rmax1 (fun _ => P.cB)) L T ω
  set GA : (Fin T → RC P) → Prop := fun ω => Pool.P0228.AlgOK P ℓ ωs φ T v ρ₀ c r (Pool.P0210.extR P rc₀ ω)
  have hstep := Pool.P0228.slot_expect_of P ℓ ωs φ rc₀ hL hN T κ hκ (fun ω => Fit ω ∧ GS ω ∧ GB ω ∧ GA ω)
    (fun ω => restDcap P ℓ ωs φ hD hLv hlev T L v ρ₀ c r (Pool.P0210.extR P rc₀ ω)) ?_
  · refine hstep.trans ?_
    have hX : 0 ≤ (∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + κ :=
      add_nonneg (Finset.sum_nonneg fun s _ => (hxr s.1).le) hκ
    have hcoef : 0 ≤ ((∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + κ) * T := mul_nonneg hX (Nat.cast_nonneg _)
    -- union bound for the bad event
    have hunion : ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if Fit ω ∧ GS ω ∧ GB ω ∧ GA ω then 0 else 1) ≤
        (∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if Fit ω then 0 else 1))
          + Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L))
          + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)
          + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if GA ω then 0 else 1) := by
      have hS : ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if GS ω then 0 else 1) ≤
          Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) := by
        have h := Pool.P0203.prob_not_goodDS_all P ℓ ωs φ rc₀ hL hN hD hLv hlev hlay hxr hxr1 hLp T
        simp_rw [Pool.P0228.wgt_eq_pw P hL hN] at h
        exact h
      have hBd : ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if GB ω then 0 else 1) ≤
          2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
        have h := Pool.P0216.prob_not_goodB P ℓ rc₀ hL hN hcw hLp T
        simp_rw [Pool.P0228.wgt_eq_pw P hL hN] at h
        exact h
      have hpt : ∀ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if Fit ω ∧ GS ω ∧ GB ω ∧ GA ω then 0 else 1) ≤
          Pool.P0202.pw (wR P) ω * (if Fit ω then 0 else 1) + Pool.P0202.pw (wR P) ω * (if GS ω then 0 else 1)
            + Pool.P0202.pw (wR P) ω * (if GB ω then 0 else 1) + Pool.P0202.pw (wR P) ω * (if GA ω then 0 else 1) := by
        intro ω
        have hp := Pool.P0228.pw_nonneg P hL ω
        rw [← mul_add, ← mul_add, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hp
        by_cases h1 : Fit ω <;> by_cases h2 : GS ω <;> by_cases h3 : GB ω <;> by_cases h4 : GA ω <;>
          simp only [h1, h2, h3, h4, and_self, and_true, and_false, ite_true, ite_false] <;>
          norm_num
      have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin T → RC P))) fun ω _ => hpt ω
      simp only [Finset.sum_add_distrib] at hsum
      linarith
    have := mul_le_mul_of_nonneg_left hunion hcoef
    linarith
  · -- the pathwise bound on the good event
    rintro ω ⟨hfit, hgS, hgB, hint, hA⟩
    have hpre := Pool.P0228.pre_extR P rc₀ ω
    have h := probe_credit_pathD_cap P ℓ ωs φ hD hLv hlev rc₀ (Pool.P0210.extR P rc₀ ω) T hT hLp hB hlay
      hxr hanti hcB hΛ0 hfit (by rw [hpre]; exact hgS) (by rw [hpre]; exact hgB) v ρ₀ c hv hρ₀ hc hint r hA
    unfold Pool.P0228.probeU restDcap
    unfold Pool.P0154.isum at h ⊢
    beta_reduce at h
    rw [Finset.range_eq_Ico] at h ⊢
    rw [hκdef]
    linarith

open Pool.P0228 in
/-- The capped rest term is never larger than P0228's `restD` (the cap only lowers the end term). -/
theorem restDcap_le_restD (hxr : ∀ j, 0 ≤ P.xr j) (T : ℕ) (L : ℝ) (v : ℕ → ℝ) (ρ₀ c : ℝ) (r : ι → ℕ → ℝ)
    (ω : ℕ → RC P) :
    restDcap P ℓ ωs φ hD hLv hlev T L v ρ₀ c r ω ≤ restD P ℓ ωs φ hD hLv hlev T L v ρ₀ c r ω := by
  unfold restDcap restD
  gcongr with x _
  · exact Finset.sum_nonneg fun s _ => by split_ifs <;> simp [hxr]
  · exact min_le_left _ _

end Pool.P0239
