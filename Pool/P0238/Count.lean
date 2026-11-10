import Pool.P0223.CreditD
import Pool.P0171.VarT
import Pool.P0222.OccW
import Pool.P0228.ExpD

/-!
# Copies ending in a thread, and the end-rate term of P0223's probing bound grouped by thread
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065

namespace Pool.P0238

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
  (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
  (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
  (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))

open Classical in
/-- Copies entering before `T`, ever active before `T`, whose current thread at the end of their active window is
`j`. -/
noncomputable def endIn (j : ℕ) : Finset ι :=
  univ.filter fun x => P.E x < T ∧ P.E x < Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x ∧
    curT P.E P.thr0 P.D P.Bt x (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) = j

include hlay hfit in
/-- A copy ending in thread `j` either started in thread `j` (`thr0 x = j`) or jumped into it (a pair in P0223's
`Wj j`). -/
theorem endIn_cases (j : Fin P.D) {x : ι} (hx : x ∈ endIn P ℓ ωs φ hD hLv hlev ω T j) :
    P.thr0 x = j ∨ ∃ t, (x, t) ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j := by
  classical
  simp only [endIn, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨hxT, hEb, hend⟩ := hx
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x
  have hbT : b ≤ T := (Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hxT).2.1
  by_cases h0 : curT P.E P.thr0 P.D P.Bt x (P.E x) = j
  · left
    rw [curT_of_le (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) le_rfl] at h0
    exact h0
  · right
    have hex : ∃ k, curT P.E P.thr0 P.D P.Bt x (P.E x + k) = j := ⟨b - 1 - P.E x, by
      rw [show P.E x + (b - 1 - P.E x) = b - 1 by omega]; exact hend⟩
    set k0 := Nat.find hex with hk0
    have hk0spec : curT P.E P.thr0 P.D P.Bt x (P.E x + k0) = j := Nat.find_spec hex
    have hk0pos : 0 < k0 := by
      rcases Nat.eq_zero_or_pos k0 with h | h
      · rw [h, add_zero] at hk0spec; exact absurd hk0spec h0
      · exact h
    have hk0le : k0 ≤ b - 1 - P.E x := Nat.find_min' hex (by
      rw [show P.E x + (b - 1 - P.E x) = b - 1 by omega]; exact hend)
    have hprev : curT P.E P.thr0 P.D P.Bt x (P.E x + k0 - 1) ≠ j := by
      have := Nat.find_min hex (show k0 - 1 < k0 by omega)
      rwa [show P.E x + (k0 - 1) = P.E x + k0 - 1 by omega] at this
    refine ⟨P.E x + k0, ?_⟩
    have hw : (x, P.E x + k0) ∈ Pool.P0223.Wall P ℓ ωs φ hD hLv hlev ω T := by
      unfold Pool.P0223.Wall
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range]
      exact ⟨⟨hxT, by omega⟩, by omega, by omega⟩
    obtain ⟨h0', -, -, -⟩ := Pool.P0223.rates_wall P ℓ ωs φ hD hLv hlev ω T hlay hfit hw
    unfold Pool.P0223.Wj
    simp only [Finset.mem_filter]
    refine ⟨⟨hw, ?_⟩, ?_⟩
    · show curT P.E P.thr0 P.D P.Bt x (P.E x + k0) ≠ curT P.E P.thr0 P.D P.Bt x (P.E x + k0 - 1)
      rw [hk0spec]; exact fun h => hprev h.symm
    · unfold Pool.P0223.key
      simp only at h0' ⊢
      rw [dif_pos h0']
      exact Fin.ext hk0spec

include hlay hfit in
open Classical in
/-- **Copies ending in a thread.** `#endIn j ≤ S'·(#{t < T : canonT t = j} + #{t < T : some index of ι (sampled or not) has entry round t in thread j
})`, `S' = Σ_j sl j`. -/
theorem card_endIn_le (j : Fin P.D) :
    ((endIn P ℓ ωs φ hD hLv hlev ω T j).card : ℝ) ≤
      (∑ j : Fin P.D, (P.sl j : ℝ)) * (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
        + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card) := by
  set S' := ∑ j : Fin P.D, (P.sl j : ℝ)
  set A := (endIn P ℓ ωs φ hD hLv hlev ω T j).filter (fun x => P.thr0 x = j)
  set B := (endIn P ℓ ωs φ hD hLv hlev ω T j).filter (fun x => P.thr0 x ≠ j)
  have hsplit : (endIn P ℓ ωs φ hD hLv hlev ω T j).card = A.card + B.card :=
    (Finset.card_filter_add_card_filter_not _).symm
  -- B: injects into the first coordinates of `Wj j`
  have hB : (B.card : ℝ) ≤ S' * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card := by
    have h1 : B.card ≤ ((Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).image Prod.fst).card := by
      apply Finset.card_le_card
      intro x hx
      rw [Finset.mem_filter] at hx
      rcases endIn_cases P ℓ ωs φ hD hLv hlev ω T hlay hfit j hx.1 with h | ⟨t, ht⟩
      · exact absurd h hx.2
      · exact Finset.mem_image.mpr ⟨(x, t), ht, rfl⟩
    have h2 := Finset.card_image_le (s := Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j) (f := Prod.fst)
    have h3 := Pool.P0223.card_Wj_le_canon P ℓ ωs φ hD hLv hlev ω T hlay hfit j
    have : (B.card : ℝ) ≤ (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card := by exact_mod_cast h1.trans h2
    linarith
  -- A: fibres over the entry round, each made of active copies
  have hA : (A.card : ℝ) ≤ S' * ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card := by
    have hmaps : ∀ x ∈ A, P.E x ∈ (range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j) := by
      intro x hx
      simp only [A, endIn, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx.1.1, x, rfl, hx.2⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    push_cast
    refine le_trans (Finset.sum_le_sum (g := fun _ => S') fun t ht => ?_)
      (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]))
    rw [Finset.mem_filter, Finset.mem_range] at ht
    have hcard : (A.filter (fun x => P.E x = t)).card ≤ (active P ℓ ω ωs φ t).card := by
      apply Finset.card_le_card
      intro x hx
      simp only [A, endIn, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨⟨⟨hxT, hEb, -⟩, -⟩, rfl⟩ := hx
      exact ((Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hxT).2.2 (P.E x) ht.1).2 ⟨le_rfl, hEb⟩
    exact le_trans (by exact_mod_cast hcard) (Pool.P0223.card_active_le P ℓ ωs φ (hfit t ht.1))
  rw [hsplit]
  push_cast
  linarith

end Pool.P0238

namespace Pool.P0238

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
  (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
  (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
  (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))

include hlay hfit in
open Classical in
/-- **End-rate term by thread.** If every copy ending in thread `j` has `M x + Bmin ≤ Mb j` (`Mb ≥ 0`), the end-rate
term of P0223's probing bound is at most `Σ_j x_j·#endIn j·Mb j`, hence at most
`Σ_j x_j·S'·(#{t<T : canonT t = j} + #{t<T : ∃ y, E y = t ∧ thr0 y = j})·Mb j`. -/
theorem end_term_le (hxr : ∀ j, 0 ≤ P.xr j) (M : ι → ℝ) (Mb : Fin P.D → ℝ) (hMb : ∀ j, 0 ≤ Mb j)
    (hM : ∀ j : Fin P.D, ∀ x ∈ endIn P ℓ ωs φ hD hLv hlev ω T j, M x + P.Bmin ≤ Mb j) :
    ∑ x ∈ univ.filter (fun x => P.E x < T),
        Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x * (M x + P.Bmin) ≤
      ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
        (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
          + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card)) * Mb j := by
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T
  set jOf : ι → Fin P.D := fun x =>
    if h : curT P.E P.thr0 P.D P.Bt x (b x - 1) < P.D then ⟨_, h⟩ else ⟨0, hD⟩
  set X := univ.filter (fun x => P.E x < T)
  have hwin : ∀ x, P.E x < T → P.E x ≤ b x ∧ b x ≤ T ∧
      ∀ t < T, (x ∈ active P ℓ ω ωs φ t ↔ P.E x ≤ t ∧ t < b x) :=
    fun x hx => Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hx
  set Y := X.filter (fun x => P.E x < b x)
  -- pointwise: inactive copies contribute 0, the others ≤ x_{jOf x}·Mb (jOf x)
  have hpt : ∀ x ∈ X, Pool.P0209.rateD P ℓ ωs φ ω (b x - 1) x * (M x + P.Bmin) ≤
      if x ∈ Y then P.xr (jOf x) * Mb (jOf x) else 0 := by
    intro x hx
    have hxT : P.E x < T := (Finset.mem_filter.mp hx).2
    obtain ⟨hEb, hbT, hw⟩ := hwin x hxT
    by_cases hY : x ∈ Y
    · rw [if_pos hY]
      have hlt : P.E x < b x := (Finset.mem_filter.mp hY).2
      have ha : x ∈ active P ℓ ω ωs φ (b x - 1) := (hw (b x - 1) (by omega)).2 ⟨by omega, by omega⟩
      have hcl := Pool.P0223.curT_lt P ℓ ω ωs φ hD hLv hlev ha
      have hr := Pool.P0223.rateD_active P ℓ ω ωs φ hD hLv hlev hlay (hfit _ (by omega)) ha
      have hj : jOf x = ⟨_, hcl⟩ := by simp only [jOf, dif_pos hcl]
      rw [hr, ← hj]
      have hmem : x ∈ endIn P ℓ ωs φ hD hLv hlev ω T (jOf x) := by
        simp only [endIn, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hxT, hlt, by rw [hj]⟩
      exact mul_le_mul_of_nonneg_left (hM _ x hmem) (hxr _)
    · rw [if_neg hY]
      have hnot : ¬ P.E x < b x := fun h => hY (Finset.mem_filter.mpr ⟨hx, h⟩)
      have hinact : x ∉ active P ℓ ω ωs φ (b x - 1) := by
        intro ha
        by_cases hb1 : b x - 1 < T
        · have := ((hw (b x - 1) hb1).1 ha); omega
        · omega
      rw [Pool.P0223.rateD_inactive P ℓ ω ωs φ hlay hinact, zero_mul]
  have h1 := Finset.sum_le_sum hpt
  rw [← Finset.sum_filter] at h1
  have hXY : X.filter (fun a => a ∈ Y) = Y := by
    ext a; simp only [Y, Finset.mem_filter]; constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨h.1, h⟩
  rw [hXY] at h1
  -- group Y by thread
  have hmaps : ∀ x ∈ Y, jOf x ∈ (univ : Finset (Fin P.D)) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps] at h1
  refine h1.trans (Finset.sum_le_sum fun j _ => ?_)
  have hfib : ∑ x ∈ Y.filter (fun x => jOf x = j), P.xr (jOf x) * Mb (jOf x) =
      ((Y.filter (fun x => jOf x = j)).card : ℝ) * (P.xr j * Mb j) := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]), Finset.sum_const, nsmul_eq_mul]
  rw [hfib]
  have hsub : (Y.filter (fun x => jOf x = j)).card ≤ (endIn P ℓ ωs φ hD hLv hlev ω T j).card := by
    apply Finset.card_le_card
    intro x hx
    simp only [Y, X, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨hxT, hlt⟩, hj⟩ := hx
    simp only [endIn, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hxT, hlt, ?_⟩
    obtain ⟨-, hbT, hw⟩ := hwin x hxT
    have ha : x ∈ active P ℓ ω ωs φ (b x - 1) := (hw (b x - 1) (by omega)).2 ⟨by omega, by omega⟩
    have hcl := Pool.P0223.curT_lt P ℓ ω ωs φ hD hLv hlev ha
    have : jOf x = ⟨_, hcl⟩ := by simp only [jOf, dif_pos hcl]
    rw [this] at hj
    rw [← hj]
  have hc := card_endIn_le P ℓ ωs φ hD hLv hlev ω T hlay hfit j
  have hcY : ((Y.filter (fun x => jOf x = j)).card : ℝ) ≤ (endIn P ℓ ωs φ hD hLv hlev ω T j).card := by
    exact_mod_cast hsub
  have hxm : 0 ≤ P.xr j * Mb j := mul_nonneg (hxr j) (hMb j)
  calc ((Y.filter (fun x => jOf x = j)).card : ℝ) * (P.xr j * Mb j)
      ≤ ((∑ j : Fin P.D, (P.sl j : ℝ)) * (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
          + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card)) * (P.xr j * Mb j) :=
        mul_le_mul_of_nonneg_right (hcY.trans hc) hxm
    _ = _ := by ring

end Pool.P0238

namespace Pool.P0238

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
  (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
  (ω : ℕ → RC P) (T : ℕ)

/-- **Lifetime of a copy ending in a fine thread.** If a copy ends its active window in thread `j ≥ 1` and every
entry thread is `≤ Θn`, its window has length `≤ Σ_{i ∈ [j, Θn]} Bt(i−1)` (P0171's occupancy count per thread). -/
theorem life_le (hB : ∀ i, 0 < P.Bt i) (Θn : ℕ) (hΘ : ∀ x, P.thr0 x ≤ Θn) (j : ℕ) (hj : 1 ≤ j) {x : ι}
    (hx : x ∈ endIn P ℓ ωs φ hD hLv hlev ω T j) :
    Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x ≤ ∑ i ∈ Finset.Icc j Θn, P.Bt (i - 1) := by
  classical
  simp only [endIn, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨hxT, hEb, hend⟩ := hx
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x
  have hmaps : ∀ u ∈ Finset.Ico (P.E x) b, curT P.E P.thr0 P.D P.Bt x u ∈ Finset.Icc j Θn := by
    intro u hu
    rw [Finset.mem_Ico] at hu
    rw [Finset.mem_Icc]
    constructor
    · rw [← hend]
      exact curT_mono (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) x (by omega) hu.1
    · exact (curT_le_thr0 (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) x u).trans (hΘ x)
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  rw [Nat.card_Ico] at hcard
  rw [hcard]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi1 : 1 ≤ i := le_trans hj (Finset.mem_Icc.mp hi).1
  exact Pool.P0171.card_curT_eq_le (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) x hi1 (hB _) (P.E x) b le_rfl

end Pool.P0238

namespace Pool.P0238

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
  (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
  (ω : ℕ → RC P) (T : ℕ)

theorem rmax1_const_le {c : ℝ} (hc : 0 ≤ c) (a b : ℕ) : Pool.P0158.rmax1 (fun _ => c) a b ≤ max 1 c := by
  unfold Pool.P0158.rmax1
  refine max_le_max le_rfl ?_
  have h : (Finset.Ico a b).sup (fun _ => Real.toNNReal c) ≤ Real.toNNReal c := Finset.sup_le fun _ _ => le_rfl
  have h' : (((Finset.Ico a b).sup (fun _ => Real.toNNReal c) : NNReal) : ℝ) ≤ (Real.toNNReal c : ℝ) := by
    exact_mod_cast h
  rwa [Real.coe_toNNReal _ hc] at h'

/-- **Per-copy margin of a copy ending in thread `j`.** With margins `Λ x c ≤ Λbar (curT x c)` (`Λbar` antitone in
the thread index, `≥ 0`), P0222's occupancy hypotheses and a lifetime bound `b − E ≤ len`, the margin `MOfW` of
P0223 is at most `Λbar j + Wocc(len) + widV(len·cB, max 1 cB, L)`. -/
theorem MOfW_le {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ P.xr j) (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i))) (hΘ : ∀ f, (P.thr0 f : ℝ) ≤ Θ)
    (hcB : 0 ≤ P.cB) (Λbar : ℕ → ℝ) (hΛ0 : ∀ i, 0 ≤ Λbar i) (hΛa : ∀ i i', i ≤ i' → Λbar i' ≤ Λbar i)
    (hΛ : ∀ x c, P.Λ x c ≤ Λbar (curT P.E P.thr0 P.D P.Bt x c))
    (j : ℕ) {x : ι} (hx : x ∈ endIn P ℓ ωs φ hD hLv hlev ω T j) (len : ℕ)
    (hlen : Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x ≤ len) :
    Pool.P0223.MOfW P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x ≤
      Λbar j + Pool.P0222.Wocc L xmin M ρ nn TT Θ len + Pool.P0158.widV (len * P.cB) (max 1 P.cB) L := by
  simp only [endIn, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨hxT, hEb, hend⟩ := hx
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x
  unfold Pool.P0223.MOfW Pool.P0219.MOfB
  -- margin
  have hΛM : Pool.P0223.ΛM P b x ≤ Λbar j := by
    unfold Pool.P0223.ΛM
    split_ifs with h
    · refine Finset.sup'_le h _ fun c hc => (hΛ x c).trans (hΛa _ _ ?_)
      rw [Finset.mem_Ico] at hc
      rw [← hend]
      exact curT_mono (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) x (by omega) hc.1
    · exact hΛ0 j
  -- slot width
  have hW : Pool.P0158.widV (∑ s ∈ Ico (P.E x) b, Pool.P0203.rS P x s) (Pool.P0158.rmax1 (Pool.P0203.rS P x) (P.E x) b) L
      ≤ Pool.P0222.Wocc L xmin M ρ nn TT Θ len :=
    (Pool.P0222.widV_le_occ P x hL hxm hxm1 hxr hn hT hM hρ0 hB hρ hx0 hx (hΘ x) (fun _ => le_rfl)).trans
      (Pool.P0222.Wocc_mono hL hM hlen)
  -- B̂ width
  have hWB : Pool.P0158.widV (∑ _s ∈ Ico (P.E x) b, P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) (P.E x) b) L ≤
      Pool.P0158.widV (len * P.cB) (max 1 P.cB) L := by
    refine Pool.P0219.widV_mono2 hL ?_ (rmax1_const_le hcB _ _)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hcB
  linarith

end Pool.P0238

namespace Pool.P0238

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
  (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)

/-- The lifetime bound used for copies ending in thread `j`. -/
def lenOf (Θn T : ℕ) (Bt : ℕ → ℕ) (j : ℕ) : ℕ := if 1 ≤ j then ∑ i ∈ Finset.Icc j Θn, Bt (i - 1) else T

open Classical in
/-- **P0228's `restD` bounded by counts (pathwise, on no-overflow).** With `S' = Σ_j sl j`,
`C_j = #{t<T : canonT t = j}`, `N_j = #{t<T : ∃ y, E y = t ∧ thr0 y = j}` (all indices of `ι`, sampled or not),
`Mb_j = Λbar j + Wocc(len_j) + widV(len_j·cB, max 1 cB, L) + Bmin` and ALG's slacks `r ≤ Rb`:
`restD ≤ Σ_j x_j·S'·(C_j + N_j)·Mb_j + Σ_j x_j·(S'ρ₀(2S'C_j + 1) + S'·V[0,T) + S'c·√T·√(2S'C_j + 1) + S'C_j·Rb)`. -/
theorem restD_le (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ P.xr j) (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i)))
    (Θn : ℕ) (hΘn : ∀ f, P.thr0 f ≤ Θn) (hΘ : (Θn : ℝ) ≤ Θ)
    (hcB : 0 ≤ P.cB) (Λbar : ℕ → ℝ) (hΛ0 : ∀ i, 0 ≤ Λbar i) (hΛa : ∀ i i', i ≤ i' → Λbar i' ≤ Λbar i)
    (hΛ : ∀ x c, P.Λ x c ≤ Λbar (curT P.E P.thr0 P.D P.Bt x c))
    (v : ℕ → ℝ) (ρ₀ c : ℝ) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (r : ι → ℕ → ℝ) (Rb : ℝ) (hRb : 0 ≤ Rb)
    (hr : ∀ x t, r x t ≤ Rb) :
    Pool.P0228.restD P ℓ ωs φ hD hLv hlev T L v ρ₀ c r ω ≤
      ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
          (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
            + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card)) *
          (Λbar j + Pool.P0222.Wocc L xmin M ρ nn TT Θ (lenOf Θn T P.Bt j)
            + Pool.P0158.widV ((lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L + P.Bmin)
        + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * c * (Real.sqrt T *
              Real.sqrt (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
                ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1))
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card * Rb) := by
  set S' := ∑ j : Fin P.D, (P.sl j : ℝ)
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hxr0 : ∀ j, 0 ≤ P.xr j := fun j => hxm.le.trans (hxr j)
  unfold Pool.P0228.restD
  refine add_le_add ?_ (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hxr0 j))
  · -- end-rate term
    refine end_term_le P ℓ ωs φ hD hLv hlev ω T hlay hfit hxr0 _ _ (fun j => ?_) (fun j x hxe => ?_)
    · have h1 : 0 ≤ Pool.P0222.Wocc L xmin M ρ nn TT Θ (lenOf Θn T P.Bt j) := by
        unfold Pool.P0222.Wocc; positivity
      have h2 : 0 ≤ Pool.P0158.widV ((lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L := by
        unfold Pool.P0158.widV
        have : 0 ≤ max 1 P.cB := le_trans zero_le_one (le_max_left _ _)
        positivity
      have h3 : (0 : ℝ) ≤ P.Bmin := Nat.cast_nonneg _
      linarith [hΛ0 j]
    · have hlen : Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x ≤ lenOf Θn T P.Bt j := by
        unfold lenOf
        split_ifs with hj
        · exact life_le P ℓ ωs φ hD hLv hlev ω T hB Θn hΘn j hj hxe
        · simp only [endIn, Finset.mem_filter, Finset.mem_univ, true_and] at hxe
          have := (Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hxe.1).2.1
          omega
      have := MOfW_le P ℓ ωs φ hD hLv hlev ω T hL hxm hxm1 hxr hn hT hM hρ0 hB hρ hx0 hx
        (fun f => le_trans (by exact_mod_cast hΘn f) hΘ) hcB Λbar hΛ0 hΛa hΛ j hxe _ hlen
      linarith
  · -- per-thread credit slack
    have hW := Pool.P0223.card_Wj_le_canon P ℓ ωs φ hD hLv hlev ω T hlay hfit j
    set C := ((range T).filter (fun t => canonT P.D P.Bt t = j)).card
    set W := (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card
    have hWc : (W : ℝ) ≤ S' * C := hW
    have hsq : Real.sqrt (2 * (W : ℝ) + 1) ≤ Real.sqrt (2 * (S' * C) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hrsum : ∑ i ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j, max 0 (r i.1 i.2) ≤ S' * C * Rb := by
      calc _ ≤ ∑ _i ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j, Rb :=
            Finset.sum_le_sum fun i _ => max_le hRb (hr _ _)
        _ = W * Rb := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ S' * C * Rb := mul_le_mul_of_nonneg_right hWc hRb
    have e1 : S' * ρ₀ * (2 * W + 1) ≤ S' * ρ₀ * (2 * (S' * C) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hS0 hρ₀)
    have e2 : S' * c * (Real.sqrt T * Real.sqrt (2 * W + 1)) ≤ S' * c * (Real.sqrt T * Real.sqrt (2 * (S' * C) + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)) (mul_nonneg hS0 hc)
    linarith

end Pool.P0238

namespace Pool.P0238

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
  (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)

open Classical in
/-- **Good-event term of P0228's `slot_expect`, generic.** If on every path where every thread fits `restD ≤ Bd`
(`Bd ≥ 0`, deterministic), then `E_T[[G]·restD] ≤ Bd` for any event `G` implying fits. -/
theorem good_le (hL : P.IsLaw) (hN : 0 < P.N) (rc₀ : RC P) (T : ℕ) (L : ℝ) (v : ℕ → ℝ) (ρ₀ c : ℝ)
    (r : ι → ℕ → ℝ) (Bd : ℝ) (hBd0 : 0 ≤ Bd) (G : (Fin T → RC P) → Prop)
    (hGfit : ∀ ω, G ω → ∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t))
    (hBd : ∀ ω : Fin T → RC P, (∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t)) →
      Pool.P0228.restD P ℓ ωs φ hD hLv hlev T L v ρ₀ c r (Pool.P0210.extR P rc₀ ω) ≤ Bd) :
    ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
      (if G ω then Pool.P0228.restD P ℓ ωs φ hD hLv hlev T L v ρ₀ c r (Pool.P0210.extR P rc₀ ω) else 0) ≤ Bd := by
  calc _ ≤ ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * Bd := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (Pool.P0228.pw_nonneg P hL ω)
        split_ifs with h
        · exact hBd ω (hGfit ω h)
        · exact hBd0
    _ = Bd := by rw [← Finset.sum_mul, Pool.P0228.sum_pw P hL hN, one_mul]

end Pool.P0238

namespace Pool.P0238

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
  (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)

open Classical in
/-- **P0228's good term bounded by the counts** (`good_le ∘ restD_le`): with `v ≥ 0` the count bound of `restD_le` is
`≥ 0`, so `E_T[[G]·restD] ≤` that bound for every event `G` implying no overflow before `T`. -/
theorem good_restD_le (hL' : P.IsLaw) (hN : 0 < P.N) (rc₀ : RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
    {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ P.xr j) (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i)))
    (Θn : ℕ) (hΘn : ∀ f, P.thr0 f ≤ Θn) (hΘ : (Θn : ℝ) ≤ Θ)
    (hcB : 0 ≤ P.cB) (Λbar : ℕ → ℝ) (hΛ0 : ∀ i, 0 ≤ Λbar i) (hΛa : ∀ i i', i ≤ i' → Λbar i' ≤ Λbar i)
    (hΛ : ∀ x c, P.Λ x c ≤ Λbar (curT P.E P.thr0 P.D P.Bt x c))
    (v : ℕ → ℝ) (hv : ∀ u, 0 ≤ v u) (ρ₀ c : ℝ) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (r : ι → ℕ → ℝ) (Rb : ℝ)
    (hRb : 0 ≤ Rb) (hr : ∀ x t, r x t ≤ Rb) (G : (Fin T → RC P) → Prop)
    (hGfit : ∀ ω, G ω → ∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t)) :
    ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
      (if G ω then Pool.P0228.restD P ℓ ωs φ hD hLv hlev T L v ρ₀ c r (Pool.P0210.extR P rc₀ ω) else 0) ≤
      ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
          (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
            + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card)) *
          (Λbar j + Pool.P0222.Wocc L xmin M ρ nn TT Θ (lenOf Θn T P.Bt j)
            + Pool.P0158.widV ((lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L + P.Bmin)
        + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * c * (Real.sqrt T *
              Real.sqrt (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
                ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1))
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card * Rb) := by
  have hS0 : 0 ≤ ∑ j : Fin P.D, (P.sl j : ℝ) := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hxr0 : ∀ j, 0 ≤ P.xr j := fun j => hxm.le.trans (hxr j)
  have hvs : 0 ≤ Pool.P0154.isum v 0 T := Pool.P0154.isum_nonneg v hv 0 T
  refine good_le P ℓ ωs φ hD hLv hlev hL' hN rc₀ T L v ρ₀ c r _ ?_ G hGfit (fun ω hfit =>
    restD_le P ℓ ωs φ hD hLv hlev (Pool.P0210.extR P rc₀ ω) T hlay hfit hL hxm hxm1 hxr hn hT hM hρ0 hB hρ hx0 hx
      Θn hΘn hΘ hcB Λbar hΛ0 hΛa hΛ v ρ₀ c hρ₀ hc r Rb hRb hr)
  refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) (Finset.sum_nonneg fun j _ => ?_)
  · have h1 : 0 ≤ Pool.P0222.Wocc L xmin M ρ nn TT Θ (lenOf Θn T P.Bt j) := by
      unfold Pool.P0222.Wocc; positivity
    have h2 : 0 ≤ Pool.P0158.widV ((lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L := by
      unfold Pool.P0158.widV
      have : 0 ≤ max 1 P.cB := le_trans zero_le_one (le_max_left _ _)
      positivity
    have h3 : (0 : ℝ) ≤ P.Bmin := Nat.cast_nonneg _
    have := hΛ0 j
    have := hxr0 j
    positivity
  · have := hxr0 j
    positivity

end Pool.P0238
