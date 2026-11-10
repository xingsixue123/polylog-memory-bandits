import Pool.P0216.BConc
import Pool.P0207.Rule
import Pool.P0211.RuleD

/-!
# The (b″) check bound for P0194's per-thread process (P0209's `hcheck`)

P0211 proves that rule (b″) did not fire (`estGapD_lt`) and that a concentration hypothesis `hconc` gives the check
bound (`check_le`). Here `hconc` is discharged on P0203's slot good event and P0216's `B̂` good event.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0203 Pool.P0176 Pool.P0156

namespace Pool.P0219

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- P0194's realized data history (P0156's `gChat` of its pool). -/
noncomputable abbrev dat (ω : ℕ → RC P) : ι → ℕ → ℝ :=
  gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
    (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ

/-- P0211's estimated gap is the data history since entry minus `B̂` since entry. -/
theorem estGapD_eq (ω : ℕ → RC P) (x : ι) (m : ℕ) (hE : P.E x ≤ m) :
    Pool.P0211.estGapD P ℓ ωs φ ω x m =
      dat P ℓ ωs φ ω x m - dat P ℓ ωs φ ω x (P.E x) - (Bh P ℓ ω m - Bh P ℓ ω (P.E x)) := by
  have hf1 := gEst_frozen P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
    (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ x m le_rfl
  have hf2 := gEst_frozen P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
    (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ x m hE
  unfold Pool.P0211.estGapD dat
  rw [← hf1, ← hf2]
  rfl

variable (rc0 : RC P)

open Classical in
/-- **Concentration at a check (P0211's `hconc`).** On P0203's slot good event for `x` and P0216's `B̂` good event
(both on the prefix of length `T`), if `x` is active and every thread fits on `[E x, m)` with `m ≤ T`, the true gap
since entry is at most P0211's estimated gap plus the slot width and the `B̂` width. -/
theorem conc_good (ω : ℕ → RC P) {L : ℝ} (T : ℕ) (x : ι)
    (hgS : Pool.P0158.GoodV (DS P ℓ ωs φ rc0 x) (gateS P ℓ ωs φ rc0 x) (rS P x) (Pool.P0158.rmax1 (rS P x)) L T
      (pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (pre P ω T))
    (m : ℕ) (hEm : P.E x ≤ m) (hmT : m ≤ T)
    (hact : ∀ t, P.E x ≤ t → t < m → x ∈ active P ℓ ω ωs φ t)
    (hfit : ∀ t, P.E x ≤ t → t < m → Fits P.Lv P.sl (sp P ℓ ω ωs φ t)) :
    ∑ t ∈ Ico (P.E x) m, (ℓr P ℓ t x - bPol P ℓ ω t) ≤
      Pool.P0211.estGapD P ℓ ωs φ ω x m
        + (Pool.P0158.widV (∑ s ∈ Ico (P.E x) m, rS P x s) (Pool.P0158.rmax1 (rS P x) (P.E x) m) L
          + Pool.P0158.widV (∑ _s ∈ Ico (P.E x) m, P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) m) L) := by
  have hS := goodV_run P ℓ ωs φ rc0 ω x T hgS (P.E x) m hEm hmT
  have hBd := Pool.P0216.goodB_run P ℓ rc0 ω T hgB (P.E x) m hEm hmT
  have hif : ∀ u ∈ Ico (P.E x) m, (if x ∈ active P ℓ ω ωs φ u ∧ Fits P.Lv P.sl (sp P ℓ ω ωs φ u) then
      (dat P ℓ ωs φ ω x (u + 1) - dat P ℓ ωs φ ω x u) - ℓr P ℓ u x else 0)
        = (dat P ℓ ωs φ ω x (u + 1) - dat P ℓ ωs φ ω x u) - ℓr P ℓ u x := by
    intro u hu
    rw [Finset.mem_Ico] at hu
    rw [if_pos ⟨hact u hu.1 hu.2, hfit u hu.1 hu.2⟩]
  rw [Finset.sum_congr rfl hif, Finset.sum_sub_distrib,
    Pool.P0207.sum_Ico_telescope (fun u => dat P ℓ ωs φ ω x u) hEm] at hS
  rw [Finset.sum_sub_distrib, ← Pool.P0216.Bh_sum P ℓ ω (P.E x) m hEm] at hBd
  rw [Finset.sum_sub_distrib, estGapD_eq P ℓ ωs φ ω x m hEm]
  have h1 := (abs_lt.mp hS).1
  have h2 := (abs_lt.mp hBd).2
  linarith

open Classical in
/-- **Check bound (P0209's `hcheck`).** Under the two good events, if `x` is active on `[E x, b)` with `b ≤ T`, every
thread fits on `[E x, m)`, `E x < m < b` and `Bmin ∣ m`, the true gap since entry is below the margin plus the two
widths (P0211's `check_le` with `hconc` from `conc_good`). -/
theorem check_bound (ω : ℕ → RC P) {L : ℝ} (T : ℕ) (x : ι)
    (hgS : Pool.P0158.GoodV (DS P ℓ ωs φ rc0 x) (gateS P ℓ ωs φ rc0 x) (rS P x) (Pool.P0158.rmax1 (rS P x)) L T
      (pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (pre P ω T))
    (b : ℕ) (hbT : b ≤ T) (hint : ∀ t, P.E x ≤ t → t < b → x ∈ active P ℓ ω ωs φ t)
    (m : ℕ) (hEm : P.E x < m) (hmb : m < b) (hB : P.Bmin ∣ m)
    (hfit : ∀ t, P.E x ≤ t → t < m → Fits P.Lv P.sl (sp P ℓ ω ωs φ t)) :
    ∑ t ∈ Ico (P.E x) m, (ℓr P ℓ t x - bPol P ℓ ω t) ≤
      P.Λ x (m - 1) + Pool.P0158.widV (∑ s ∈ Ico (P.E x) m, rS P x s) (Pool.P0158.rmax1 (rS P x) (P.E x) m) L
        + Pool.P0158.widV (∑ _s ∈ Ico (P.E x) m, P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) m) L := by
  have hc := conc_good P ℓ ωs φ rc0 ω T x hgS hgB m hEm.le (by omega)
    (fun t h1 h2 => hint t h1 (by omega)) hfit
  have := Pool.P0211.check_le P ℓ ωs φ ω x b hint _ m hEm hmb hB hc
  linarith

theorem rmax1_mono (r : ℕ → ℝ) {a m T : ℕ} (hmT : m ≤ T) : Pool.P0158.rmax1 r a m ≤ Pool.P0158.rmax1 r a T := by
  unfold Pool.P0158.rmax1
  refine max_le_max le_rfl ?_
  exact_mod_cast Finset.sup_mono (Finset.Ico_subset_Ico le_rfl hmT)

theorem widV_mono2 {V V' ρ ρ' L : ℝ} (hL : 0 ≤ L) (hV : V ≤ V') (hρ : ρ ≤ ρ') :
    Pool.P0158.widV V ρ L ≤ Pool.P0158.widV V' ρ' L := by
  unfold Pool.P0158.widV
  have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hV hL)
  nlinarith

/-- The `m`-independent check margin of copy `x` over the horizon `T`: a uniform rule margin `Λb` plus the slot and
`B̂` widths over `[E x, T)`. -/
noncomputable def MOf (L Λb : ℝ) (T : ℕ) (x : ι) : ℝ :=
  Λb + Pool.P0158.widV (∑ s ∈ Ico (P.E x) T, rS P x s) (Pool.P0158.rmax1 (rS P x) (P.E x) T) L
    + Pool.P0158.widV (∑ _s ∈ Ico (P.E x) T, P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) T) L

open Classical in
/-- **Uniform check bound (the form of P0209's `hcheck` for one copy).** Under the two good events, with positive
slot weights, `cB ≥ 0`, `L ≥ 0` and margins `Λ x c ≤ Λb`, if `x` is active on `[E x, b)` with `b ≤ T` and every thread
fits on `[E x, b)`, then at EVERY check boundary `m` with `E x < m < b` and `Bmin ∣ m` the true gap since entry is at
most the single constant `MOf P L Λb T x` (independent of `m`). -/
theorem check_bound_unif (ω : ℕ → RC P) {L : ℝ} (hL : 0 ≤ L) (T : ℕ) (x : ι) (hxr : ∀ j, 0 < P.xr j)
    (hcB : 0 ≤ P.cB) (Λb : ℝ) (hΛ : ∀ c, P.Λ x c ≤ Λb)
    (hgS : Pool.P0158.GoodV (DS P ℓ ωs φ rc0 x) (gateS P ℓ ωs φ rc0 x) (rS P x) (Pool.P0158.rmax1 (rS P x)) L T
      (pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (pre P ω T))
    (b : ℕ) (hbT : b ≤ T) (hint : ∀ t, P.E x ≤ t → t < b → x ∈ active P ℓ ω ωs φ t)
    (hfit : ∀ t, P.E x ≤ t → t < b → Fits P.Lv P.sl (sp P ℓ ω ωs φ t)) :
    ∀ m, P.E x < m → m < b → P.Bmin ∣ m →
      ∑ t ∈ Ico (P.E x) m, (ℓr P ℓ t x - bPol P ℓ ω t) ≤ MOf P L Λb T x := by
  intro m hEm hmb hB
  have h := check_bound P ℓ ωs φ rc0 ω T x hgS hgB b hbT hint m hEm hmb hB
    (fun t h1 h2 => hfit t h1 (by omega))
  refine h.trans ?_
  unfold MOf
  have hrS : ∀ s, 0 ≤ rS P x s := fun s => Pool.P0191.rC_nonneg 1 P.xr P.E P.thr0 P.Bt hxr x s
  have e1 := widV_mono2 (L := L) hL (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ico_subset_Ico (le_refl (P.E x)) (show m ≤ T by omega)) fun s _ _ => hrS s)
    (rmax1_mono (rS P x) (a := P.E x) (show m ≤ T by omega))
  have e2 := widV_mono2 (L := L) hL (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ico_subset_Ico (le_refl (P.E x)) (show m ≤ T by omega)) fun s _ _ => hcB)
    (rmax1_mono (fun _ => P.cB) (a := P.E x) (show m ≤ T by omega))
  linarith [hΛ (m - 1)]

/-- The lifetime-scale check margin: as `MOf`, with the widths over the copy's own window `[E x, b)`. -/
noncomputable def MOfB (L Λb : ℝ) (x : ι) (b : ℕ) : ℝ :=
  Λb + Pool.P0158.widV (∑ s ∈ Ico (P.E x) b, rS P x s) (Pool.P0158.rmax1 (rS P x) (P.E x) b) L
    + Pool.P0158.widV (∑ _s ∈ Ico (P.E x) b, P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) b) L

open Classical in
/-- **Uniform check bound at the copy's lifetime scale.** As `check_bound_unif`, with the constant
`MOfB P L Λb x b` (widths over `[E x, b)` instead of `[E x, T)`); P0209's `hcheck` allows `M x` to depend on `b x`. -/
theorem check_bound_unif_b (ω : ℕ → RC P) {L : ℝ} (hL : 0 ≤ L) (T : ℕ) (x : ι) (hxr : ∀ j, 0 < P.xr j)
    (hcB : 0 ≤ P.cB) (Λb : ℝ) (hΛ : ∀ c, P.Λ x c ≤ Λb)
    (hgS : Pool.P0158.GoodV (DS P ℓ ωs φ rc0 x) (gateS P ℓ ωs φ rc0 x) (rS P x) (Pool.P0158.rmax1 (rS P x)) L T
      (pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (pre P ω T))
    (b : ℕ) (hbT : b ≤ T) (hint : ∀ t, P.E x ≤ t → t < b → x ∈ active P ℓ ω ωs φ t)
    (hfit : ∀ t, P.E x ≤ t → t < b → Fits P.Lv P.sl (sp P ℓ ω ωs φ t)) :
    ∀ m, P.E x < m → m < b → P.Bmin ∣ m →
      ∑ t ∈ Ico (P.E x) m, (ℓr P ℓ t x - bPol P ℓ ω t) ≤ MOfB P L Λb x b := by
  intro m hEm hmb hB
  have h := check_bound P ℓ ωs φ rc0 ω T x hgS hgB b hbT hint m hEm hmb hB
    (fun t h1 h2 => hfit t h1 (by omega))
  refine h.trans ?_
  unfold MOfB
  have hrS : ∀ s, 0 ≤ rS P x s := fun s => Pool.P0191.rC_nonneg 1 P.xr P.E P.thr0 P.Bt hxr x s
  have e1 := widV_mono2 (L := L) hL (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ico_subset_Ico (le_refl (P.E x)) (show m ≤ b by omega)) fun s _ _ => hrS s)
    (rmax1_mono (rS P x) (a := P.E x) (show m ≤ b by omega))
  have e2 := widV_mono2 (L := L) hL (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Ico_subset_Ico (le_refl (P.E x)) (show m ≤ b by omega)) fun s _ _ => hcB)
    (rmax1_mono (fun _ => P.cB) (a := P.E x) (show m ≤ b by omega))
  linarith [hΛ (m - 1)]

end Pool.P0219
