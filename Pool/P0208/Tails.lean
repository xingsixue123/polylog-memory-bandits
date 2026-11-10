import Pool.P0203.DSlot
import Pool.P0186.RecCert
import Pool.P0193.VarCert
import Pool.P0171.VarT

/-!
# Actual-run slot tails for P0194's process, on P0203's good event (inputs toward P0186's `hlo`)

P0186's per-run bound asks, for every member `f` actively present on `[s, s')`, for the slot lower tail
`Σ ℓ ≤ Σ incrOf(data) + W(s' − s)` (`ActHyp.hlo`, for ALL `s ≤ s'`). Its certificates also use an upper tail `hup` on
the RECORD data `recD` (actual data for sampled copies, the forced run's data for unsampled ones). This file proves,
for P0194's process (pool = P0176's `dzRun` with `B = 1`), on the horizon `[0, T)` only:

* `sp_ok`, `mem_members_iff`, `E_le_of_active`, **`presAct_iff`**: P0186's `PresAct` on P0194's pool is "active
  (P0194's `active`) at every round of `[s, s')`" (as P0198 for P0181).
* **`tails_of_good`**: on P0203's good event at horizon `T` and if no thread overflows before `T` (`Fits` at every
  round `< T`), for every copy `f` active on `[s, s') ⊆ [0, T)`, the lower AND the upper tail of the ACTUAL pool data
  hold with the copy- and interval-dependent width `widV(Σ_{[s,s')} 1/x_{curT f}, max(1, max_{[s,s')} 1/x_{curT f}), L)`.
  The upper tail is for actual-run data of active copies only; it is NOT P0186's `hup` (no `recD`/forced-run form).
* **`hlo_of_good`**, **`hlo_len`**: the lower tail in the shape of `ActHyp.hlo` (hypothesis `PresAct`), but only for
  `s' ≤ T` and on the good event: the horizon-`T`, good-event form of `ActHyp.hlo`, not the field itself.
* `rS_le`, **`widV_le_len`**: with every rate `≥ xmin ∈ (0, 1]`, the width is at most `Wlen(s' − s) =
  2√(L·(s' − s)/xmin) + 2L/xmin` (monotone in the length).
* **`widV_le_sqrt_occ`**: with P0171's occupancy hypotheses on the rates, the width is at most
  `2ρ₀L + 2√(L·((s' − s)·M + thr0 f·ρT/n))`: the per-piece shape of P0193's `pieceW_le_sqrt`.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0156 Pool.P0065 Pool.P0095 Pool.P0203

namespace Pool.P0208

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n) (ω : ℕ → RC P)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- The pool's data (P0156's `gChat` of P0194's `dzRun`). -/
noncomputable abbrev dat : ι → ℕ → ℝ :=
  gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
    (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ

section Bridge

variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
include hD hLv hlev

/-- Start-pool membership: entry no later than `u`, indices in range. -/
lemma sp_ok (u : ℕ) : StartOK P.E P.thr0 P.D P.Lv P.Bt u (sp P ℓ ω ωs φ u) := by
  unfold sp pool
  rw [gRun_pools_eq]
  exact start_ok hD hLv (tpools_ok hD hLv hlev ωs φ u) ωs

lemma mem_members_iff (u : ℕ) (x : ι) :
    x ∈ members P.D P.Lv (sp P ℓ ω ωs φ u) ↔ ∃ r l, x ∈ sp P ℓ ω ωs φ u r l := by
  unfold members
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨r, -, l, -, h⟩; exact ⟨r, l, h⟩
  · rintro ⟨r, l, h⟩
    obtain ⟨-, -, hl, hr⟩ := sp_ok P ℓ ω ωs φ hD hLv hlev u x r l h
    exact ⟨r, hr, l, hl, h⟩

lemma E_le_of_active {u : ℕ} {x : ι} (h : x ∈ active P ℓ ω ωs φ u) : P.E x ≤ u := by
  unfold active at h
  rw [Finset.mem_sdiff, mem_members_iff P ℓ ω ωs φ hD hLv hlev] at h
  obtain ⟨⟨r, l, h⟩, -⟩ := h
  exact (sp_ok P ℓ ω ωs φ hD hLv hlev u x r l h).1

/-- **Bridge to P0186**: `PresAct` on P0194's pool is "active at every round of `[s, s')`". -/
theorem presAct_iff (x : ι) (s s' : ℕ) :
    Pool.P0186.PresAct P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ x s s' ↔
      ∀ u, s ≤ u → u < s' → x ∈ active P ℓ ω ωs φ u := by
  unfold Pool.P0186.PresAct Pool.P0186.PresA
  constructor
  · rintro ⟨h1, h2⟩ u hu1 hu2
    unfold active
    rw [Finset.mem_sdiff, mem_members_iff P ℓ ω ωs φ hD hLv hlev]
    exact ⟨h1 u hu1 hu2, h2 u hu1 hu2⟩
  · intro h
    refine ⟨fun u hu1 hu2 => ?_, fun u hu1 hu2 => ?_⟩
    · have := h u hu1 hu2
      unfold active at this
      rw [Finset.mem_sdiff, mem_members_iff P ℓ ω ωs φ hD hLv hlev] at this
      exact this.1
    · have := h u hu1 hu2
      unfold active at this
      rw [Finset.mem_sdiff] at this
      exact this.2

end Bridge

open Classical in
/-- On rounds where the copy is active and all threads fit, the gated sum is the plain sum. -/
theorem gated_eq (f : ι) {s s' : ℕ} (hact : ∀ u, s ≤ u → u < s' → f ∈ active P ℓ ω ωs φ u)
    (hfit : ∀ u, s ≤ u → u < s' → Fits P.Lv P.sl (sp P ℓ ω ωs φ u)) :
    (∑ u ∈ Ico s s', if f ∈ active P ℓ ω ωs φ u ∧ Fits P.Lv P.sl (sp P ℓ ω ωs φ u) then
        (dat P ℓ ω ωs φ f (u + 1) - dat P ℓ ω ωs φ f u) - ℓr P ℓ u f else 0) =
      ∑ u ∈ Ico s s', Pool.P0105.incrOf (dat P ℓ ω ωs φ) u f - ∑ u ∈ Ico s s', ℓr P ℓ u f := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hu
  rw [if_pos ⟨hact u h1 h2, hfit u h1 h2⟩]
  rfl

open Classical in
/-- **Lower and upper tails of the ACTUAL pool data on the good event** (inputs toward P0186's `hlo`; the upper tail
is NOT P0186's `hup`, which is on the record data `recD`), with the copy- and interval-dependent width, for a copy
active at every round of `[s, s') ⊆ [0, T)`. `GoodV` is P0203's event for copy `f` on the length-`T` prefix of
`ω`. -/
theorem tails_of_good (rc0 : RC P) (f : ι) {L : ℝ} (T : ℕ)
    (hgood : Pool.P0158.GoodV (DS P ℓ ωs φ rc0 f) (gateS P ℓ ωs φ rc0 f) (rS P f) (Pool.P0158.rmax1 (rS P f)) L T
      (pre P ω T))
    (hfit : ∀ u, u < T → Fits P.Lv P.sl (sp P ℓ ω ωs φ u)) {s s' : ℕ} (hss : s ≤ s') (hs'T : s' ≤ T)
    (hact : ∀ u, s ≤ u → u < s' → f ∈ active P ℓ ω ωs φ u) :
    ∑ u ∈ Ico s s', ℓr P ℓ u f ≤ ∑ u ∈ Ico s s', Pool.P0105.incrOf (dat P ℓ ω ωs φ) u f +
        Pool.P0158.widV (∑ u ∈ Ico s s', rS P f u) (Pool.P0158.rmax1 (rS P f) s s') L ∧
      ∑ u ∈ Ico s s', Pool.P0105.incrOf (dat P ℓ ω ωs φ) u f ≤ ∑ u ∈ Ico s s', ℓr P ℓ u f +
        Pool.P0158.widV (∑ u ∈ Ico s s', rS P f u) (Pool.P0158.rmax1 (rS P f) s s') L := by
  have h := goodV_run P ℓ ωs φ rc0 ω f T hgood s s' hss hs'T
  rw [gated_eq P ℓ ω ωs φ f hact (fun u _ h2 => hfit u (by omega))] at h
  have := abs_lt.1 h
  constructor <;> linarith [this.1, this.2]

/-- **Lower tail in the shape of P0186's `ActHyp.hlo`, horizon-`T` and good-event form**: for every member actively
present on `[s, s')` with `s' ≤ T`. Not the field `ActHyp.hlo` itself, which has no horizon. -/
theorem hlo_of_good (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (rc0 : RC P) {L : ℝ}
    (T : ℕ) (hgood : ∀ f, Pool.P0158.GoodV (DS P ℓ ωs φ rc0 f) (gateS P ℓ ωs φ rc0 f) (rS P f)
      (Pool.P0158.rmax1 (rS P f)) L T (pre P ω T))
    (hfit : ∀ u, u < T → Fits P.Lv P.sl (sp P ℓ ω ωs φ u)) (f : ι) {s s' : ℕ} (hss : s ≤ s') (hs'T : s' ≤ T)
    (hP : Pool.P0186.PresAct P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ f s s') :
    ∑ u ∈ Ico s s', ℓr P ℓ u f ≤ ∑ u ∈ Ico s s', Pool.P0105.incrOf (dat P ℓ ω ωs φ) u f +
      Pool.P0158.widV (∑ u ∈ Ico s s', rS P f u) (Pool.P0158.rmax1 (rS P f) s s') L :=
  (tails_of_good P ℓ ω ωs φ rc0 f T (hgood f) hfit hss hs'T
    ((presAct_iff P ℓ ω ωs φ hD hLv hlev f s s').1 hP)).1

/-- `1/x` at any thread is at most `1/xmin` when every rate is at least `xmin` and `xmin ≤ 1`. -/
theorem rS_le (f : ι) {xmin : ℝ} (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ P.xr j) (u : ℕ) :
    rS P f u ≤ 1 / xmin := by
  unfold rS Pool.P0191.rC Pool.P0191.xrN
  rw [Nat.cast_one]
  split_ifs with h
  · exact one_div_le_one_div_of_le hxm (hxr _)
  · rw [div_one]; exact (one_le_one_div hxm hxm1)

/-- **The width with a rate floor**: if every rate is at least `xmin ∈ (0, 1]`, the width on `[s, s')` is at most
`2√(L·(s' − s)/xmin) + 2L/xmin`, a monotone function of the length (the form of P0186's `W`). -/
theorem widV_le_len (f : ι) {xmin L : ℝ} (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hL : 0 ≤ L)
    (hxr : ∀ j, xmin ≤ P.xr j) (s s' : ℕ) :
    Pool.P0158.widV (∑ u ∈ Ico s s', rS P f u) (Pool.P0158.rmax1 (rS P f) s s') L ≤
      2 * √(L * ((s' - s : ℕ) / xmin)) + 2 * L / xmin := by
  have hr := rS_le P f hxm hxm1 hxr
  have hV : ∑ u ∈ Ico s s', rS P f u ≤ (s' - s : ℕ) / xmin := by
    calc ∑ u ∈ Ico s s', rS P f u ≤ ∑ _u ∈ Ico s s', 1 / xmin := Finset.sum_le_sum fun u _ => hr u
      _ = (s' - s : ℕ) / xmin := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]; ring
  have hρ : Pool.P0158.rmax1 (rS P f) s s' ≤ 1 / xmin := by
    unfold Pool.P0158.rmax1
    refine max_le (one_le_one_div hxm hxm1) ?_
    have : ((Finset.Ico s s').sup (fun u => Real.toNNReal (rS P f u)) : NNReal) ≤ Real.toNNReal (1 / xmin) :=
      Finset.sup_le fun u _ => Real.toNNReal_le_toNNReal (hr u)
    have h' := (NNReal.coe_le_coe.2 this)
    rwa [Real.coe_toNNReal _ (by positivity)] at h'
  unfold Pool.P0158.widV
  have hs : √((∑ u ∈ Ico s s', rS P f u) * L) ≤ √(L * ((s' - s : ℕ) / xmin)) := by
    apply Real.sqrt_le_sqrt; rw [mul_comm]; exact mul_le_mul_of_nonneg_left hV hL
  have h2 : 2 * Pool.P0158.rmax1 (rS P f) s s' * L ≤ 2 * L / xmin := by
    have := mul_le_mul_of_nonneg_right hρ hL
    calc 2 * Pool.P0158.rmax1 (rS P f) s s' * L = 2 * (Pool.P0158.rmax1 (rS P f) s s' * L) := by ring
      _ ≤ 2 * (1 / xmin * L) := by linarith
      _ = 2 * L / xmin := by ring
  linarith

/-- **The width in P0193's per-piece shape** (thread benefit kept): under P0171's occupancy hypotheses on the
thread rates (`1/x_0 ≤ M`, `1/x_i ≤ max(M, T/(n·Bt_i))`, `Bt_{i−1} ≤ ρ·Bt_i`), for a copy entered by `s` and a range
bound `ρ₀`, the width on `[s, s')` is at most `2ρ₀L + 2√(L·((s' − s)·M + thr0 f·ρT/n))`. -/
theorem widV_le_sqrt_occ (f : ι) {M ρ nn TT ρ₀ L : ℝ} (hL : 0 ≤ L) (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M)
    (hB : ∀ i, 0 < P.Bt i) (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i)
    (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i)))
    (s s' : ℕ) (hs : P.E f ≤ s) (hρ₀ : Pool.P0158.rmax1 (rS P f) s s' ≤ ρ₀) :
    Pool.P0158.widV (∑ u ∈ Ico s s', rS P f u) (Pool.P0158.rmax1 (rS P f) s s') L ≤
      2 * ρ₀ * L + 2 * √(L * (((s' - s : ℕ) : ℝ) * M + P.thr0 f * (ρ * TT / nn))) := by
  have hV : ∑ u ∈ Ico s s', rS P f u ≤ ((s' - s : ℕ) : ℝ) * M + P.thr0 f * (ρ * TT / nn) := by
    have h := Pool.P0171.sum_inv_rate_le (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) f
      (Pool.P0191.xrN P.xr) M ρ nn TT hn hT hM hB hρ hx0 hx s s' hs
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun u _ => ?_
    simp [rS, Pool.P0191.rC]
  exact Pool.P0193.widV_le_sqrt hL hV hρ₀

open Classical in
/-- **The horizon-`T`, good-event form of P0186's `ActHyp.hlo` with a length-only width** (rate floor `xmin`): on
P0203's good event (all copies) and without thread overflow before `T`, every member actively present on `[s, s')`
with `s' ≤ T` has `Σ ℓ ≤ Σ incrOf(data) + Wlen(s' − s)`, `Wlen(m) = 2√(L·m/xmin) + 2L/xmin`. Not the field
`ActHyp.hlo` itself (no horizon there). -/
theorem hlo_len (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (rc0 : RC P) {L xmin : ℝ}
    (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ P.xr j) (T : ℕ)
    (hgood : ∀ f, Pool.P0158.GoodV (DS P ℓ ωs φ rc0 f) (gateS P ℓ ωs φ rc0 f) (rS P f)
      (Pool.P0158.rmax1 (rS P f)) L T (pre P ω T))
    (hfit : ∀ u, u < T → Fits P.Lv P.sl (sp P ℓ ω ωs φ u)) (f : ι) {s s' : ℕ} (hss : s ≤ s') (hs'T : s' ≤ T)
    (hP : Pool.P0186.PresAct P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ f s s') :
    ∑ u ∈ Ico s s', ℓr P ℓ u f ≤ ∑ u ∈ Ico s s', Pool.P0105.incrOf (dat P ℓ ω ωs φ) u f +
      (2 * √(L * ((s' - s : ℕ) / xmin)) + 2 * L / xmin) :=
  (hlo_of_good P ℓ ω ωs φ hD hLv hlev rc0 T hgood hfit f hss hs'T hP).trans
    (add_le_add le_rfl (widV_le_len P f hxm hxm1 hL hxr s s'))

end Pool.P0208
