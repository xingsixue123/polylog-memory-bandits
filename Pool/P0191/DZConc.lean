import Pool.P0176.DZProc
import Pool.P0158.FreedV

/-!
# Unbiasedness and interval-uniform concentration of the slot data of P0176's process (P0166's C7 inputs)

* Independent rounds: `sum_prod_coord`, `sum_prod_coord2`, `sum_prod_sum`, **`sum_prod_sq_sum`** (the variance of a
  sum of centred per-round terms is the sum of the variances).
* One unit of P0176's process: `LayOK` (every member of a fitting block holds exactly one slot; only members are
  shown), `Norm` (round weights sum to one), `round_mean`, **`unit_mean`**, **`unit_var`**, `one_of_slotSum`,
  `layOK_sort`, `layOK_last`.
* `start_loc`: a start-pool member of thread `r` at unit `s` has `r = curT c s` (P0065's `start_ok` for P0156's `gRun`).
* The process: `wU_nonneg`, `sum_wU`, `νU` (the law of a unit's coins), `νU_toReal`, `wgt_νU`, `xrN`, `stAt`, `spAt`,
  `gateC`, `DC` (gated unit estimation error), `rC` (`B / x` at the current thread), `active_block`, `dzC_le`,
  `inc_bounds`, **`incrV_DC`** (P0158's `IncrV`), **`prob_not_goodDZ`**, **`prob_not_goodDZ_all`**, **`DC_eq_run`**.
-/

namespace Pool.P0191

open Finset

section Prod

variable {Y : Type*} [Fintype Y] {B : ℕ} (w : Y → ℝ)

/-- Averaging a function of round `s` over independent rounds with weights `w` (summing to `1`). -/
theorem sum_prod_coord (hw : ∑ y, w y = 1) (s : Fin B) (h : Y → ℝ) :
    ∑ z : Fin B → Y, (∏ t, w (z t)) * h (z s) = ∑ y, w y * h y := by
  classical
  have := Fintype.prod_sum (κ := fun _ : Fin B => Y) (fun (t : Fin B) (y : Y) => w y * if t = s then h y else 1)
  rw [Finset.prod_eq_single s (fun t _ hts => by simp [hts, ← Finset.sum_mul, hw])
    (fun h' => absurd (Finset.mem_univ s) h')] at this
  simp only [if_true] at this
  rw [this]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ s (fun t => h (z t))]
  simp

/-- Two different rounds are independent. -/
theorem sum_prod_coord2 (hw : ∑ y, w y = 1) {s s' : Fin B} (hss : s ≠ s') (h k : Y → ℝ) :
    ∑ z : Fin B → Y, (∏ t, w (z t)) * (h (z s) * k (z s')) = (∑ y, w y * h y) * ∑ y, w y * k y := by
  classical
  have := Fintype.prod_sum (κ := fun _ : Fin B => Y) (fun (t : Fin B) (y : Y) =>
    w y * ((if t = s then h y else 1) * (if t = s' then k y else 1)))
  have hrest : ∀ t ∈ (univ : Finset (Fin B)), t ≠ s → t ≠ s' →
      ∑ y, w y * ((if t = s then h y else 1) * (if t = s' then k y else 1)) = 1 := by
    intro t _ h1 h2; simp [h1, h2, hw]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ s'),
    ← Finset.prod_erase_mul _ _ (Finset.mem_erase.2 ⟨hss, Finset.mem_univ s⟩),
    Finset.prod_eq_one (s := ((univ : Finset (Fin B)).erase s').erase s) (fun t ht => hrest t (Finset.mem_univ t)
      (Finset.ne_of_mem_erase ht) (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht)))] at this
  simp only [if_true, if_neg hss, if_neg (Ne.symm hss), one_mul, mul_one] at this
  rw [this]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ s (fun t => h (z t)),
    Finset.prod_ite_eq' Finset.univ s' (fun t => k (z t))]
  simp only [Finset.mem_univ, if_true]

/-- The mean of a sum of per-round terms. -/
theorem sum_prod_sum (hw : ∑ y, w y = 1) (g : Fin B → Y → ℝ) :
    ∑ z : Fin B → Y, (∏ t, w (z t)) * ∑ t, g t (z t) = ∑ t, ∑ y, w y * g t y := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => sum_prod_coord w hw t (g t)

/-- **Variance of a sum of centred per-round terms**: the cross terms vanish. -/
theorem sum_prod_sq_sum (hw : ∑ y, w y = 1) (g : Fin B → Y → ℝ) (hg : ∀ t, ∑ y, w y * g t y = 0) :
    ∑ z : Fin B → Y, (∏ t, w (z t)) * (∑ t, g t (z t)) ^ 2 = ∑ t, ∑ y, w y * g t y ^ 2 := by
  classical
  have hsq : ∀ z : Fin B → Y, (∑ t, g t (z t)) ^ 2 = ∑ t, ∑ t', g t (z t) * g t' (z t') := by
    intro z; rw [sq, Finset.sum_mul_sum]
  simp only [hsq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_comm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
  have h0 : ∀ t' ∈ (univ : Finset (Fin B)).erase t,
      ∑ z : Fin B → Y, (∏ u, w (z u)) * (g t (z t) * g t' (z t')) = 0 := by
    intro t' ht'
    rw [sum_prod_coord2 w hw (Ne.symm (Finset.ne_of_mem_erase ht')) (g t) (g t'), hg t, zero_mul]
  rw [Finset.sum_eq_zero h0, add_zero]
  rw [← sum_prod_coord w hw t (fun y => g t y ^ 2)]
  refine Finset.sum_congr rfl fun z _ => by ring

end Prod

section Unit

open Pool.P0176 Pool.P0156 Pool.P0065 Pool.P0095

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ)
  (xr : Fin D → ℝ) (ℓr : ℕ → ι → ℝ)

open Classical in
/-- A layout places every member of a fitting block in exactly one slot and shows only members. -/
structure LayOK (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) : Prop where
  one : ∀ j V x, V.card ≤ sl j → x ∈ V → (univ.filter fun k => lay j V k = some x).card = 1
  mem : ∀ j V k y, lay j V k = some y → y ∈ V

/-- The rounds' weights sum to one: `w0 + Σ_j sl_j·x_j = 1`. -/
def Norm (w0 : ℝ) : Prop := ∑ r : RT D sl, wRT sl xr w0 r = 1

open Classical in
/-- **One round, mean.** If copy `x` is a member of block `j0` only, block `j0` fits and `x_{j0} ≠ 0`, a round
observes `x` with weight `x_{j0}`, and its contribution has mean `ℓ`. -/
theorem round_mean (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (hlay : LayOK sl lay) (w0 : ℝ)
    (sp : ℕ → ℕ → Finset ι) (a : ℕ) (x : ι) (t : Fin B) (j0 : Fin D) (hx : x ∈ blockMem Lv sp j0)
    (hxo : ∀ j : Fin D, j ≠ j0 → x ∉ blockMem Lv sp j) (hfit : (blockMem Lv sp j0).card ≤ sl j0)
    (hxr : xr j0 ≠ 0) (f : ℝ → ℝ) (hf : f 0 = 0) :
    ∑ r : RT D sl, wRT sl xr w0 r * f (dzC D B xr ℓr a x t (obsR D Lv sl lay sp r)) =
      xr j0 * f (ℓr (a * B + t) x / xr j0) := by
  rw [Fintype.sum_option]
  simp only [obsR, dzC, hf, mul_zero, zero_add]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j0]
  · have hc := hlay.one j0 _ x hfit hx
    have hterm : ∀ k : Fin (sl j0), wRT sl xr w0 (some ⟨j0, k⟩) *
        f (match (lay j0 (blockMem Lv sp j0) k).map (fun y => (j0, y)) with
          | none => 0
          | some (j, y) => if y = x then ℓr (a * B + t) x / xr j else 0) =
        if lay j0 (blockMem Lv sp j0) k = some x then xr j0 * f (ℓr (a * B + t) x / xr j0) else 0 := by
      intro k
      simp only [wRT]
      rcases h : lay j0 (blockMem Lv sp j0) k with _ | y
      · simp [hf]
      · by_cases hyx : y = x
        · subst hyx; simp
        · simp [hyx, hf]
    calc _ = ∑ k : Fin (sl j0), (if lay j0 (blockMem Lv sp j0) k = some x then
            xr j0 * f (ℓr (a * B + t) x / xr j0) else 0) := Finset.sum_congr rfl fun k _ => hterm k
      _ = _ := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, hc, Nat.cast_one,
          one_mul]
  · intro j _ hj
    refine Finset.sum_eq_zero fun k _ => ?_
    show wRT sl xr w0 (some ⟨j, k⟩) * f (match (lay j (blockMem Lv sp j) k).map (fun y => (j, y)) with
          | none => 0
          | some (j, y) => if y = x then ℓr (a * B + t) x / xr j else 0) = 0
    simp only [wRT]
    rcases h : lay j (blockMem Lv sp j) k with _ | y
    · simp [hf]
    · have hy := hlay.mem j _ k y h
      have hyx : y ≠ x := fun e => hxo j hj (e ▸ hy)
      simp [hyx, hf]
  · intro h; exact absurd (Finset.mem_univ j0) h

/-- **Unit mean.** Under independent rounds with normalized weights, an active copy `x` (a member of block `j0` only,
block `j0` fits) gains on average exactly its unit loss. -/
theorem unit_mean (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (hlay : LayOK sl lay) (w0 : ℝ)
    (hN : Norm sl xr w0) (sp : ℕ → ℕ → Finset ι) (a : ℕ) (ret : Finset ι) (x : ι) (hxr' : x ∉ ret) (j0 : Fin D)
    (hx : x ∈ blockMem Lv sp j0) (hxo : ∀ j : Fin D, j ≠ j0 → x ∉ blockMem Lv sp j)
    (hfit : (blockMem Lv sp j0).card ≤ sl j0) (hxr : xr j0 ≠ 0) :
    ∑ zc : Fin B → RT D sl, wU sl B xr w0 zc * dzIncO D B Bm xr ℓr a ret (obsU Lv sl B lay sp zc) x =
      ∑ t : Fin B, ℓr (a * B + t) x := by
  simp only [dzIncO, if_neg hxr', obsU, wU]
  rw [sum_prod_sum (wRT sl xr w0) hN (fun t r => dzC D B xr ℓr a x t (obsR D Lv sl lay sp r))]
  refine Finset.sum_congr rfl fun t _ => ?_
  have h := round_mean Lv sl B xr ℓr lay hlay w0 sp a x t j0 hx hxo hfit hxr id rfl
  simp only [id] at h
  rw [h]; field_simp

/-- **Unit variance.** Under the same hypotheses, the squared deviation of the unit increment from the unit loss has
mean at most `Σ_t ℓ_t² / x_{j0}`. -/
theorem unit_var (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (hlay : LayOK sl lay) (w0 : ℝ)
    (hN : Norm sl xr w0) (sp : ℕ → ℕ → Finset ι) (a : ℕ) (ret : Finset ι) (x : ι) (hxr' : x ∉ ret) (j0 : Fin D)
    (hx : x ∈ blockMem Lv sp j0) (hxo : ∀ j : Fin D, j ≠ j0 → x ∉ blockMem Lv sp j)
    (hfit : (blockMem Lv sp j0).card ≤ sl j0) (hxr : 0 < xr j0) :
    ∑ zc : Fin B → RT D sl, wU sl B xr w0 zc *
        (dzIncO D B Bm xr ℓr a ret (obsU Lv sl B lay sp zc) x - ∑ t : Fin B, ℓr (a * B + t) x) ^ 2 ≤
      ∑ t : Fin B, ℓr (a * B + t) x ^ 2 / xr j0 := by
  have hN1 : ∑ r, wRT sl xr w0 r = 1 := hN
  have hm : ∀ t : Fin B, ∑ r, wRT sl xr w0 r * dzC D B xr ℓr a x t (obsR D Lv sl lay sp r) =
      ℓr (a * B + t) x := by
    intro t
    have h := round_mean Lv sl B xr ℓr lay hlay w0 sp a x t j0 hx hxo hfit hxr.ne' id rfl
    simp only [id] at h
    rw [h]; field_simp
  have hsq : ∀ t : Fin B, ∑ r, wRT sl xr w0 r * dzC D B xr ℓr a x t (obsR D Lv sl lay sp r) ^ 2 =
      ℓr (a * B + t) x ^ 2 / xr j0 := by
    intro t
    rw [round_mean Lv sl B xr ℓr lay hlay w0 sp a x t j0 hx hxo hfit hxr.ne' (fun u => u ^ 2) (by norm_num)]
    field_simp
  set g : Fin B → RT D sl → ℝ := fun t r => dzC D B xr ℓr a x t (obsR D Lv sl lay sp r) - ℓr (a * B + t) x with hg
  have hg0 : ∀ t, ∑ r, wRT sl xr w0 r * g t r = 0 := by
    intro t
    simp only [hg, mul_sub, Finset.sum_sub_distrib, hm t, ← Finset.sum_mul, hN1, one_mul, sub_self]
  have hrw : ∀ zc : Fin B → RT D sl, dzIncO D B Bm xr ℓr a ret (obsU Lv sl B lay sp zc) x -
      ∑ t : Fin B, ℓr (a * B + t) x = ∑ t, g t (zc t) := by
    intro zc
    simp only [dzIncO, if_neg hxr', obsU, hg, Finset.sum_sub_distrib]
  simp only [hrw, wU]
  rw [sum_prod_sq_sum (wRT sl xr w0) hN g hg0]
  refine Finset.sum_le_sum fun t _ => ?_
  have hv : ∑ r, wRT sl xr w0 r * g t r ^ 2 = ℓr (a * B + t) x ^ 2 / xr j0 - ℓr (a * B + t) x ^ 2 := by
    have : ∀ r, wRT sl xr w0 r * g t r ^ 2 = wRT sl xr w0 r * dzC D B xr ℓr a x t (obsR D Lv sl lay sp r) ^ 2 -
        2 * ℓr (a * B + t) x * (wRT sl xr w0 r * dzC D B xr ℓr a x t (obsR D Lv sl lay sp r)) +
        ℓr (a * B + t) x ^ 2 * wRT sl xr w0 r := by intro r; simp only [hg]; ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsq t, hm t, hN1]
    ring
  rw [hv]
  nlinarith [sq_nonneg (ℓr (a * B + t) x)]

open Classical in
theorem one_of_slotSum {s : ℕ} (occ : Finset ι → Fin s → Option ι) (hS : Pool.P0105.SlotSum s occ) (V : Finset ι)
    (hV : V.card ≤ s) (x : ι) (hx : x ∈ V) : (univ.filter fun k => occ V k = some x).card = 1 := by
  have h := hS V hV (fun o => if o = some x then (1 : ℝ) else 0) (by simp)
  have h1 : ∑ z ∈ V, (if (some z : Option ι) = some x then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single x (fun z _ hz => by simp [hz]) (fun h' => absurd hx h')]; simp
  rw [h1] at h
  have h2 : ((univ.filter fun k => occ V k = some x).card : ℝ) = 1 := by
    rw [Finset.card_filter]; push_cast; convert h using 2
  exact_mod_cast h2

/-- **P0176's sorted layout is `LayOK`.** -/
theorem layOK_sort : LayOK sl (sortLay (ι := ι) sl) where
  one j V x hV hx := one_of_slotSum _ (Pool.P0105.slotSum_occSort (sl j)) V hV x hx
  mem j V k y h := by
    simp only [sortLay, occSort] at h
    split_ifs at h with hk
    cases h
    exact (Finset.mem_sort _).1 (List.getElem_mem _)

/-- **P0176's copy-last layout is `LayOK`.** -/
theorem layOK_last (c : ι) : LayOK sl (lastLay (ι := ι) sl c) where
  one j V x hV hx := one_of_slotSum _ (Pool.P0105.slotSum_occLast (sl j) c) V hV x hx
  mem j V k y h := by
    simp only [lastLay, Pool.P0105.occLast_eq_lastList] at h
    split_ifs at h with hk
    cases h
    have hm := List.getElem_mem hk
    have : (Pool.P0105.lastList c V)[k.1] ∈ (Pool.P0105.lastList c V).toFinset := List.mem_toFinset.2 hm
    rwa [Pool.P0105.lastList_toFinset] at this

end Unit

section Loc

open Pool.P0176 Pool.P0156 Pool.P0065 Pool.P0095

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) {σ : Type}

/-- **Location.** In P0156's generic process, a copy in a start pool of thread `r` at unit `s` is in its current
thread: `r = curT c s`, and `r < D` (P0065's `start_ok`). -/
theorem start_loc (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → σ → (ι → ℝ) × σ) (aux0 : σ) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (s : ℕ) {c : ι} {r ℓ : ℕ}
    (h : c ∈ startPools E thr0 D Lv Bt ωs s (gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ s).pools r ℓ) :
    r = curT E thr0 D Bt c s ∧ r < D := by
  rw [gRun_pools_eq] at h
  have := start_ok hD hLv (tpools_ok hD hLv hlev ωs φ s) ωs c r ℓ h
  exact ⟨this.2.1, this.2.2.2⟩

end Loc

section Proc

open Pool.P0176 Pool.P0156 Pool.P0065 Pool.P0095

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ)
  (xr : Fin D → ℝ) (ℓr : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ)
  (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

/-- Unit weights are nonnegative. -/
theorem wU_nonneg (w0 : ℝ) (hw0 : 0 ≤ w0) (hxr : ∀ j, 0 ≤ xr j) (zc : Fin B → RT D sl) : 0 ≤ wU sl B xr w0 zc :=
  Finset.prod_nonneg fun t _ => by
    rcases zc t with _ | ⟨j, k⟩
    · exact hw0
    · exact hxr j

/-- Unit weights sum to one. -/
theorem sum_wU (w0 : ℝ) (hN : Norm sl xr w0) : ∑ zc : Fin B → RT D sl, wU sl B xr w0 zc = 1 := by
  have := Fintype.prod_sum (κ := fun _ : Fin B => RT D sl) (fun (_ : Fin B) r => wRT sl xr w0 r)
  unfold wU
  rw [← this]
  have hN1 : ∑ r, wRT sl xr w0 r = 1 := hN
  simp [hN1]

/-- **The law of a unit's coins** (independent rounds with weights `wRT`), as a PMF. -/
noncomputable def νU (w0 : ℝ) (hw0 : 0 ≤ w0) (hxr : ∀ j, 0 ≤ xr j) (hN : Norm sl xr w0) : PMF (Fin B → RT D sl) :=
  PMF.ofFintype (fun zc => ENNReal.ofReal (wU sl B xr w0 zc)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun zc _ => wU_nonneg sl B xr w0 hw0 hxr zc), sum_wU sl B xr w0 hN,
      ENNReal.ofReal_one])

theorem νU_toReal (w0 : ℝ) (hw0 : 0 ≤ w0) (hxr : ∀ j, 0 ≤ xr j) (hN : Norm sl xr w0) (zc : Fin B → RT D sl) :
    (νU sl B xr w0 hw0 hxr hN zc).toReal = wU sl B xr w0 zc := by
  simp [νU, ENNReal.toReal_ofReal (wU_nonneg sl B xr w0 hw0 hxr zc)]

/-- **Bridge**: P0158's path weight under `νU` is the product of unit weights `wU` (P0070's `wR`, as in
P0176/P0185). -/
theorem wgt_νU (w0 : ℝ) (hw0 : 0 ≤ w0) (hxr : ∀ j, 0 ≤ xr j) (hN : Norm sl xr w0) {T : ℕ}
    (ω : Fin T → Fin B → RT D sl) :
    Pool.P0092.wgt (νU sl B xr w0 hw0 hxr hN) ω = Pool.P0070.wR (wU sl B xr w0) ω := by
  unfold Pool.P0092.wgt Pool.P0070.wR
  exact Finset.prod_congr rfl fun u _ => νU_toReal sl B xr w0 hw0 hxr hN (ω u)

/-- The rate of thread `i` (`1` outside `[0, D)`). -/
noncomputable def xrN (i : ℕ) : ℝ := if h : i < D then xr ⟨i, h⟩ else 1

/-- The state of the run at unit `s` on the first `s` unit coins. -/
noncomputable abbrev stAt (s : ℕ) (ω : Fin s → Fin B → RT D sl) : GSt ι (Finset ι) :=
  dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay (extZ sl B ω) ωs φ s

/-- Its start pools. -/
noncomputable abbrev spAt (s : ℕ) (ω : Fin s → Fin B → RT D sl) : ℕ → ℕ → Finset ι :=
  startPools E thr0 D Lv Bt ωs s (stAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω).pools

open Classical in
/-- **The gate of copy `c` at unit `s`**: `c` is a start-pool member, not retired, and every thread fits. -/
noncomputable def gateC (c : ι) (s : ℕ) (ω : Fin s → Fin B → RT D sl) : Bool :=
  decide (c ∈ members D Lv (spAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω) ∧
    c ∉ (stAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω).aux ∧
    Fits Lv sl (spAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω))

/-- **The gated estimation error of copy `c` in unit `s`**: its unit increment minus its unit loss. -/
noncomputable def DC (c : ι) (s : ℕ) (ω : Fin (s + 1) → Fin B → RT D sl) : ℝ :=
  if gateC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c s (Fin.init ω) then
    dzIncO D B Bm xr ℓr s (stAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s (Fin.init ω)).aux
      (obsU Lv sl B lay (spAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s (Fin.init ω)) (ω (Fin.last s))) c -
      ∑ t : Fin B, ℓr (s * B + t) c
  else 0

/-- The range and variance proxy of copy `c` at unit `s`: `B / x` at its current thread (clock-determined). -/
noncomputable def rC (c : ι) (s : ℕ) : ℝ := B / xrN xr (curT E thr0 D Bt c s)

theorem xrN_pos (hxr : ∀ j, 0 < xr j) (i : ℕ) : 0 < xrN xr i := by
  unfold xrN; split_ifs
  · exact hxr _
  · exact one_pos

theorem rC_nonneg (hxr : ∀ j, 0 < xr j) (c : ι) (s : ℕ) : 0 ≤ rC B xr E thr0 Bt c s :=
  div_nonneg (Nat.cast_nonneg B) (xrN_pos xr hxr _).le

/-- **An active copy is in exactly one block, its current thread's.** -/
theorem active_block (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (c : ι) (s : ℕ)
    (ω : Fin s → Fin B → RT D sl)
    (hm : c ∈ members D Lv (spAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω)) :
    ∃ h : curT E thr0 D Bt c s < D,
      c ∈ blockMem Lv (spAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω) (⟨curT E thr0 D Bt c s, h⟩ : Fin D) ∧
      ∀ j : Fin D, j ≠ ⟨curT E thr0 D Bt c s, h⟩ →
        c ∉ blockMem Lv (spAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω) j := by
  simp only [members, Finset.mem_biUnion, Finset.mem_range] at hm
  obtain ⟨r, hr, ℓ, hℓ, hc⟩ := hm
  obtain ⟨hrc, hrD⟩ := start_loc E thr0 θ R K D Lv Bt lev hD hLv hlev _ _ ωs φ s hc
  subst hrc
  refine ⟨hrD, ?_, fun j hj hcj => hj ?_⟩
  · simp only [blockMem, Finset.mem_biUnion, Finset.mem_range]; exact ⟨ℓ, hℓ, hc⟩
  · simp only [blockMem, Finset.mem_biUnion, Finset.mem_range] at hcj
    obtain ⟨ℓ', hℓ', hc'⟩ := hcj
    have := (start_loc E thr0 θ R K D Lv Bt lev hD hLv hlev _ _ ωs φ s hc').1
    exact Fin.ext this

/-- Bounds on one round's contribution for a copy in exactly one block `j0`. -/
theorem dzC_le (hlay : LayOK sl lay) (hxr : ∀ j, 0 < xr j) (hℓ0 : ∀ u x, 0 ≤ ℓr u x) (hℓ1 : ∀ u x, ℓr u x ≤ 1)
    (sp : ℕ → ℕ → Finset ι) (a : ℕ) (x : ι) (t : Fin B) (j0 : Fin D)
    (hxo : ∀ j : Fin D, j ≠ j0 → x ∉ blockMem Lv sp j) (r : RT D sl) :
    0 ≤ dzC D B xr ℓr a x t (obsR D Lv sl lay sp r) ∧ dzC D B xr ℓr a x t (obsR D Lv sl lay sp r) ≤ 1 / xr j0 := by
  rcases r with _ | ⟨j, k⟩
  · simp only [obsR, dzC]; exact ⟨le_rfl, (one_div_pos.2 (hxr j0)).le⟩
  · have key : dzC D B xr ℓr a x t (obsR D Lv sl lay sp (some ⟨j, k⟩)) =
        if lay j (blockMem Lv sp j) k = some x then ℓr (a * B + t) x / xr j else 0 := by
      show dzC D B xr ℓr a x t ((lay j (blockMem Lv sp j) k).map fun y => (j, y)) = _
      rcases lay j (blockMem Lv sp j) k with _ | y
      · simp [dzC]
      · by_cases hyx : y = x
        · subst hyx; simp [dzC]
        · simp [dzC, hyx]
    rw [key]
    split_ifs with h
    · have hj : j = j0 := by
        by_contra hne; exact hxo j hne (hlay.mem j _ k x h)
      subst hj
      exact ⟨div_nonneg (hℓ0 _ _) (hxr j).le, div_le_div_of_nonneg_right (hℓ1 _ _) (hxr j).le⟩
    · exact ⟨le_rfl, (one_div_pos.2 (hxr j0)).le⟩

/-- The unit increment of an active copy lies in `[0, B / x_{j0}]`. -/
theorem inc_bounds (hlay : LayOK sl lay) (hxr : ∀ j, 0 < xr j) (hℓ0 : ∀ u x, 0 ≤ ℓr u x)
    (hℓ1 : ∀ u x, ℓr u x ≤ 1) (sp : ℕ → ℕ → Finset ι) (a : ℕ) (ret : Finset ι) (x : ι) (hxr' : x ∉ ret)
    (j0 : Fin D) (hxo : ∀ j : Fin D, j ≠ j0 → x ∉ blockMem Lv sp j) (zc : Fin B → RT D sl) :
    0 ≤ dzIncO D B Bm xr ℓr a ret (obsU Lv sl B lay sp zc) x ∧
      dzIncO D B Bm xr ℓr a ret (obsU Lv sl B lay sp zc) x ≤ B / xr j0 := by
  simp only [dzIncO, if_neg hxr', obsU]
  refine ⟨Finset.sum_nonneg fun t _ =>
    (dzC_le Lv sl B xr ℓr lay hlay hxr hℓ0 hℓ1 sp a x t j0 hxo (zc t)).1, ?_⟩
  calc ∑ t : Fin B, dzC D B xr ℓr a x t (obsR D Lv sl lay sp (zc t)) ≤ ∑ _t : Fin B, 1 / xr j0 :=
        Finset.sum_le_sum fun t _ => (dzC_le Lv sl B xr ℓr lay hlay hxr hℓ0 hℓ1 sp a x t j0 hxo (zc t)).2
    _ = B / xr j0 := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **The gated estimation errors of every copy satisfy P0158's hypotheses**: range and variance proxy `B/x` at the
copy's current thread, centred given the past, and bounded below by `−B/x`. -/
theorem incrV_DC (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (hlay : LayOK sl lay)
    (w0 : ℝ) (hw0 : 0 ≤ w0) (hxr : ∀ j, 0 < xr j) (hxr1 : ∀ j, xr j ≤ 1) (hN : Norm sl xr w0)
    (hℓ0 : ∀ u x, 0 ≤ ℓr u x) (hℓ1 : ∀ u x, ℓr u x ≤ 1) (c : ι) :
    Pool.P0158.IncrV (νU sl B xr w0 hw0 (fun j => (hxr j).le) hN)
        (DC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c) (rC B xr E thr0 Bt c) (rC B xr E thr0 Bt c) ∧
      ∀ s (ω : Fin s → Fin B → RT D sl) z,
        -rC B xr E thr0 Bt c s ≤ DC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c s (Fin.snoc ω z) := by
  -- the facts at an active unit
  have hact : ∀ s (ω : Fin s → Fin B → RT D sl),
      gateC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c s ω = true →
      ∃ h : curT E thr0 D Bt c s < D,
        rC B xr E thr0 Bt c s = B / xr ⟨curT E thr0 D Bt c s, h⟩ ∧
        c ∈ blockMem Lv (spAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω)
          ((⟨curT E thr0 D Bt c s, h⟩ : Fin D) : ℕ) ∧
        (∀ j : Fin D, j ≠ ⟨curT E thr0 D Bt c s, h⟩ →
          c ∉ blockMem Lv (spAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω) j) ∧
        c ∉ (stAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω).aux ∧
        Fits Lv sl (spAt Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ s ω) := by
    intro s ω hg
    simp only [gateC, decide_eq_true_eq] at hg
    obtain ⟨hm, hret, hfit⟩ := hg
    obtain ⟨h, hin, hout⟩ := active_block Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ hD hLv hlev c s ω hm
    exact ⟨h, by simp [rC, xrN, h], hin, hout, hret, hfit⟩
  have htruth0 : ∀ s, 0 ≤ ∑ t : Fin B, ℓr (s * B + t) c := fun s => Finset.sum_nonneg fun t _ => hℓ0 _ _
  have htruthB : ∀ s, ∑ t : Fin B, ℓr (s * B + t) c ≤ B := fun s => by
    calc ∑ t : Fin B, ℓr (s * B + t) c ≤ ∑ _t : Fin B, (1 : ℝ) := Finset.sum_le_sum fun t _ => hℓ1 _ _
      _ = B := by simp
  have hrC := rC_nonneg B xr E thr0 Bt hxr c
  refine ⟨⟨fun s ω z => ?_, fun s ω => ?_, fun s ω => ?_⟩, fun s ω z => ?_⟩
  · -- up
    simp only [DC, Fin.init_snoc, Fin.snoc_last]
    split_ifs with hg
    · obtain ⟨h, hr, hin, hout, hret, hfit⟩ := hact s ω hg
      rw [hr]
      have := (inc_bounds Lv sl B Bm xr ℓr lay hlay hxr hℓ0 hℓ1 _ s _ c hret _ hout z).2
      linarith [htruth0 s]
    · exact hrC s
  · -- mean
    simp only [DC, Fin.init_snoc, Fin.snoc_last, νU_toReal]
    split_ifs with hg
    · obtain ⟨h, hr, hin, hout, hret, hfit⟩ := hact s ω hg
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_wU sl B xr w0 hN, one_mul]
      rw [unit_mean Lv sl B Bm xr ℓr lay hlay w0 hN _ s _ c hret _ hin hout (hfit _) (hxr _).ne', sub_self]
    · simp
  · -- var
    simp only [DC, Fin.init_snoc, Fin.snoc_last, νU_toReal]
    split_ifs with hg
    · obtain ⟨h, hr, hin, hout, hret, hfit⟩ := hact s ω hg
      rw [hr]
      refine (unit_var Lv sl B Bm xr ℓr lay hlay w0 hN _ s _ c hret _ hin hout (hfit _) (hxr _)).trans ?_
      calc ∑ t : Fin B, ℓr (s * B + t) c ^ 2 / xr ⟨curT E thr0 D Bt c s, h⟩
          ≤ ∑ _t : Fin B, 1 / xr ⟨curT E thr0 D Bt c s, h⟩ := Finset.sum_le_sum fun t _ =>
            div_le_div_of_nonneg_right (by nlinarith [hℓ0 (s * B + t) c, hℓ1 (s * B + t) c]) (hxr _).le
        _ = B / xr ⟨curT E thr0 D Bt c s, h⟩ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, Finset.sum_const_zero]
      exact hrC s
  · -- lower
    simp only [DC, Fin.init_snoc, Fin.snoc_last]
    split_ifs with hg
    · obtain ⟨h, hr, hin, hout, hret, hfit⟩ := hact s ω hg
      rw [hr]
      have h0 := (inc_bounds Lv sl B Bm xr ℓr lay hlay hxr hℓ0 hℓ1 _ s _ c hret _ hout z).1
      have hB : (B : ℝ) ≤ B / xr ⟨curT E thr0 D Bt c s, h⟩ :=
        le_div_self (Nat.cast_nonneg B) (hxr _) (hxr1 _)
      linarith [htruthB s]
    · linarith [hrC s]

open Classical in
/-- **Interval-uniform concentration of P0176's slot data, for one copy.** Under independent rounds with normalized
weights and any layout placing every member of a fitting thread in exactly one slot (e.g. `sortLay`, `lastLay`), with
probability at least `1 − 2(T+1)²e^{−L}` over the unit coins, on EVERY interval `[a, b) ⊆ [0, T)` the sum over the
active units of copy `c` (member, not retired, all threads fit) of (unit increment − unit loss) is less than
`2√(L·Σ_{[a,b)} B/x_{curT}) + 2·ρ·L` in absolute value, with `ρ = max(1, max_{[a,b)} B/x_{curT})`. -/
theorem prob_not_goodDZ (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (hlay : LayOK sl lay)
    (w0 : ℝ) (hw0 : 0 ≤ w0) (hxr : ∀ j, 0 < xr j) (hxr1 : ∀ j, xr j ≤ 1) (hN : Norm sl xr w0)
    (hℓ0 : ∀ u x, 0 ≤ ℓr u x) (hℓ1 : ∀ u x, ℓr u x ≤ 1) (c : ι) {L : ℝ} (hL : 0 < L) (T : ℕ) :
    (∑ ω : Fin T → Fin B → RT D sl, Pool.P0092.wgt (νU sl B xr w0 hw0 (fun j => (hxr j).le) hN) ω *
      if Pool.P0158.GoodV (DC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c)
          (gateC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c) (rC B xr E thr0 Bt c)
          (Pool.P0158.rmax1 (rC B xr E thr0 Bt c)) L T ω then (0 : ℝ) else 1) ≤
      2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
  obtain ⟨hI, hlow⟩ := incrV_DC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ hD hLv hlev hlay w0 hw0 hxr hxr1 hN
    hℓ0 hℓ1 c
  exact Pool.P0158.prob_not_goodV _ _ _ hI hlow (rC_nonneg B xr E thr0 Bt hxr c) _
    (fun a b => Pool.P0158.rmax1_pos _ a b) (fun a b s has hsb => Pool.P0158.le_rmax1 _ has hsb) hL T

open Classical in
/-- **All copies at once** (union bound): with probability at least `1 − |ι|·2(T+1)²e^{−L}` the interval-uniform
bound of `prob_not_goodDZ` holds for every copy. -/
theorem prob_not_goodDZ_all (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (hlay : LayOK sl lay)
    (w0 : ℝ) (hw0 : 0 ≤ w0) (hxr : ∀ j, 0 < xr j) (hxr1 : ∀ j, xr j ≤ 1) (hN : Norm sl xr w0)
    (hℓ0 : ∀ u x, 0 ≤ ℓr u x) (hℓ1 : ∀ u x, ℓr u x ≤ 1) {L : ℝ} (hL : 0 < L) (T : ℕ) :
    (∑ ω : Fin T → Fin B → RT D sl, Pool.P0092.wgt (νU sl B xr w0 hw0 (fun j => (hxr j).le) hN) ω *
      if ∀ c, Pool.P0158.GoodV (DC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c)
          (gateC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c) (rC B xr E thr0 Bt c)
          (Pool.P0158.rmax1 (rC B xr E thr0 Bt c)) L T ω then (0 : ℝ) else 1) ≤
      Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) := by
  have hw : ∀ ω : Fin T → Fin B → RT D sl, 0 ≤ Pool.P0092.wgt (νU sl B xr w0 hw0 (fun j => (hxr j).le) hN) ω :=
    fun ω => Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  calc _ ≤ ∑ ω : Fin T → Fin B → RT D sl, Pool.P0092.wgt (νU sl B xr w0 hw0 (fun j => (hxr j).le) hN) ω *
        ∑ c : ι, (if Pool.P0158.GoodV (DC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c)
          (gateC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c) (rC B xr E thr0 Bt c)
          (Pool.P0158.rmax1 (rC B xr E thr0 Bt c)) L T ω then (0 : ℝ) else 1) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hw ω)
        split_ifs with hall
        · exact Finset.sum_nonneg fun c _ => by split_ifs <;> norm_num
        · push_neg at hall
          obtain ⟨c, hc⟩ := hall
          refine le_trans ?_ (Finset.single_le_sum (f := fun c => if Pool.P0158.GoodV
            (DC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c)
            (gateC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c) (rC B xr E thr0 Bt c)
            (Pool.P0158.rmax1 (rC B xr E thr0 Bt c)) L T ω then (0 : ℝ) else 1)
            (fun c _ => by split_ifs <;> norm_num) (Finset.mem_univ c))
          simp [hc]
    _ = ∑ c : ι, ∑ ω : Fin T → Fin B → RT D sl, Pool.P0092.wgt (νU sl B xr w0 hw0 (fun j => (hxr j).le) hN) ω *
        (if Pool.P0158.GoodV (DC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c)
          (gateC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c) (rC B xr E thr0 Bt c)
          (Pool.P0158.rmax1 (rC B xr E thr0 Bt c)) L T ω then (0 : ℝ) else 1) := by
        simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ _c : ι, 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := Finset.sum_le_sum fun c _ =>
        prob_not_goodDZ Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ hD hLv hlev hlay w0 hw0 hxr hxr1 hN
          hℓ0 hℓ1 c hL T
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Identification**: on the run driven by the unit coins `ω'` (extended by non-slot rounds), the gated error of
copy `c` at unit `s` is its data increment (P0156's `gChat`) minus its unit loss, when active. -/
theorem DC_eq_run (c : ι) (s : ℕ) (ω' : Fin (s + 1) → Fin B → RT D sl) :
    DC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c s ω' =
      if gateC Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay ωs φ c s (Fin.init ω') then
        (gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh lay (extZ sl B ω')) ∅ ωs φ c (s + 1) -
          gChat E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh lay (extZ sl B ω')) ∅ ωs φ c s) -
          ∑ t : Fin B, ℓr (s * B + t) c
      else 0 := by
  unfold DC
  split_ifs with hg
  · congr 1
    rw [gChat_succ, add_sub_cancel_left]
    have hst : dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay (extZ sl B ω') ωs φ s =
        dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay (extZ sl B (Fin.init ω')) ωs φ s :=
      dzRun_congr_z Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay s
        (fun v hv => (extZ_init sl B ω' v hv).symm)
    unfold gInc
    simp only [dzRun] at hst
    rw [hst]
    simp only [dzUpd, dzUpdO, extZ_last]
    rfl
  · rfl

end Proc

end Pool.P0191
