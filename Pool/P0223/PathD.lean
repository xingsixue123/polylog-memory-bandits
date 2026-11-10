import Pool.P0219.CheckD
import Pool.P0223.RateD

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0203 Pool.P0176 Pool.P0065

namespace Pool.P0223

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

variable (rc0 : RC P)

/-- The largest rule margin of copy `x` over the rounds `[E x, e)` (`0` if there are none). -/
noncomputable def ΛM (e : ℕ) (x : ι) : ℝ :=
  if h : (Ico (P.E x) e).Nonempty then (Ico (P.E x) e).sup' h (P.Λ x) else 0

theorem Λ_le_ΛM {e c : ℕ} (x : ι) (h1 : P.E x ≤ c) (h2 : c < e) : P.Λ x c ≤ ΛM P e x := by
  have hc : c ∈ Ico (P.E x) e := Finset.mem_Ico.mpr ⟨h1, h2⟩
  unfold ΛM
  rw [dif_pos ⟨c, hc⟩]
  exact Finset.le_sup' (P.Λ x) hc

theorem ΛM_nonneg (hΛ0 : ∀ x c, 0 ≤ P.Λ x c) (e : ℕ) (x : ι) : 0 ≤ ΛM P e x := by
  unfold ΛM
  split_ifs with h
  · obtain ⟨c, hc⟩ := h
    exact (hΛ0 x c).trans (Finset.le_sup' (P.Λ x) hc)
  · exact le_rfl

/-- The per-copy margin over its active window `[E x, e)`: P0219's lifetime-scale constant `MOfB` with the largest
rule margin over the window, `ΛM`, in place of a uniform margin bound. -/
noncomputable def MOfW (L : ℝ) (e : ℕ) (x : ι) : ℝ := Pool.P0219.MOfB P L (ΛM P e x) x e

variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)

open Classical in
/-- The end of a copy's active window before `T` (its entry if it is never active before `T`). -/
noncomputable def bOf (ω : ℕ → RC P) (T : ℕ) (x : ι) : ℕ :=
  if hx : ∃ t < T, x ∈ active P ℓ ω ωs φ t then
    (Pool.P0215.active_interval P ℓ ω ωs φ hD hLv hlev T x hx).choose
  else P.E x

open Classical in
/-- Window facts: a copy entering before `T` is active before `T` exactly on `[E x, bOf x)`. -/
theorem win_facts (ω : ℕ → RC P) (T : ℕ) (x : ι) (hxT : P.E x < T) :
    P.E x ≤ bOf P ℓ ωs φ hD hLv hlev ω T x ∧ bOf P ℓ ωs φ hD hLv hlev ω T x ≤ T ∧
      ∀ t < T, (x ∈ active P ℓ ω ωs φ t ↔ P.E x ≤ t ∧ t < bOf P ℓ ωs φ hD hLv hlev ω T x) := by
  by_cases hx : ∃ t < T, x ∈ active P ℓ ω ωs φ t
  · have := (Pool.P0215.active_interval P ℓ ω ωs φ hD hLv hlev T x hx).choose_spec
    simp only [bOf, dif_pos hx]
    exact this
  · simp only [bOf, dif_neg hx]
    refine ⟨le_rfl, hxT.le, fun t ht => ⟨fun h => absurd ⟨t, ht, h⟩ hx, fun h => by omega⟩⟩

open Classical in
/-- **P0194's probing term, pathwise, with P0209's window, monotonicity and check hypotheses discharged** on the
event that every thread fits before `T` and the slot and `B̂` good events hold on the prefix of length `T`. The rates
must be nonincreasing in the thread index (coarser threads, lower index, get larger rates, as in P0150). Only the
credit term (rate jumps × lead over BASE) remains, for P0154/P0162. -/
theorem probe_pathD (ω : ℕ → RC P) (T : ℕ) {L : ℝ} (hL : 0 < L) (hB : 0 < P.Bmin)
    (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j) (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i)
    (hcB : 0 ≤ P.cB) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    (hgS : ∀ x, Pool.P0158.GoodV (DS P ℓ ωs φ rc0 x) (gateS P ℓ ωs φ rc0 x) (rS P x) (Pool.P0158.rmax1 (rS P x)) L T
      (pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (pre P ω T)) :
    ∑ u ∈ range T, ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - bPol P ℓ ω u) ≤
      ∑ x ∈ univ.filter (fun x => P.E x < T),
        (Pool.P0209.rateD P ℓ ωs φ ω (bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x * (MOfW P L (bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin) +
          ∑ t ∈ Ico (P.E x + 1) (bOf P ℓ ωs φ hD hLv hlev ω T x),
            (Pool.P0209.rateD P ℓ ωs φ ω t x - Pool.P0209.rateD P ℓ ωs φ ω (t - 1) x) *
              max 0 (-Pool.P0154.isum (fun t => ℓr P ℓ t x - bPol P ℓ ω t) (P.E x) t)) := by
  set b := bOf P ℓ ωs φ hD hLv hlev ω T
  -- window facts
  have hwin : ∀ x, P.E x < T → P.E x ≤ b x ∧ b x ≤ T ∧
      ∀ t < T, (x ∈ active P ℓ ω ωs φ t ↔ P.E x ≤ t ∧ t < b x) :=
    fun x hxT => win_facts P ℓ ωs φ hD hLv hlev ω T x hxT
  have hM0 : ∀ x, P.E x < T → 0 ≤ MOfW P L (b x) x := by
    intro x _
    unfold MOfW Pool.P0219.MOfB
    have := (Pool.P0158.widV_pos (V := ∑ s ∈ Ico (P.E x) (b x), rS P x s)
      (Pool.P0158.rmax1_pos (rS P x) (P.E x) (b x)) hL).le
    have := (Pool.P0158.widV_pos (V := ∑ _s ∈ Ico (P.E x) (b x), P.cB)
      (Pool.P0158.rmax1_pos (fun _ => P.cB) (P.E x) (b x)) hL).le
    have := ΛM_nonneg P hΛ0 (b x) x
    linarith
  refine Pool.P0209.probe_totalD_le P ℓ ωs φ ω T b (fun x => MOfW P L (b x) x) hB hM0 (fun x hx => (hwin x hx).1)
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
    unfold MOfW Pool.P0219.MOfB
    have hrS : ∀ s, 0 ≤ rS P x s := fun s => Pool.P0191.rC_nonneg 1 P.xr P.E P.thr0 P.Bt hxr x s
    have e1 : Pool.P0158.widV (∑ s ∈ Ico (P.E x) m, rS P x s) (Pool.P0158.rmax1 (rS P x) (P.E x) m) L ≤
        Pool.P0158.widV (∑ s ∈ Ico (P.E x) (b x), rS P x s) (Pool.P0158.rmax1 (rS P x) (P.E x) (b x)) L :=
      Pool.P0219.widV_mono2 hL.le (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
        fun s _ _ => hrS s) (Pool.P0219.rmax1_mono _ (by omega))
    have e2 : Pool.P0158.widV (∑ _s ∈ Ico (P.E x) m, P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) m) L ≤
        Pool.P0158.widV (∑ _s ∈ Ico (P.E x) (b x), P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) (b x)) L :=
      Pool.P0219.widV_mono2 hL.le (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl (by omega))
        fun s _ _ => hcB) (Pool.P0219.rmax1_mono _ (by omega))
    linarith [Λ_le_ΛM P (e := b x) (c := m - 1) x (by omega) (by omega)]

end Pool.P0223
