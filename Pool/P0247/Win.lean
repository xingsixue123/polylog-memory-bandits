import Pool.P0238.Count

/-!
# P0238's count bound of `restD` with WINDOW-FORM copy budgets

P0228's copy budgets `r x t` (ALG vs copy `x` over its window `[E x, t)`) are, for a learner, of the form
`ρ₁ + Σ_{[E x, t)} v` with the per-round budget `v` (P0233/P0243: `rOK = ρOK + isum vOK (E x) t`). P0238's `restD_le`
bounds them by a constant `Rb`, which charges the full `Σ_{[0,T)} v` to every jump. Here the jumps' windows into one
thread have multiplicity `≤ S'` (P0223's `mult_le`), so all of them together cost `|Wj|·ρ₁ + S'·Σ_{[0,T)} v`.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065

namespace Pool.P0247

open Pool.P0238 (lenOf endIn)

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
  (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)

/-- **Window budgets of the jumps into one thread.** When every thread fits before `T`: for `v ≥ 0`, `ρ₁ ≥ 0`,
`Σ_{(x,t) ∈ Wj j} max 0 (ρ₁ + Σ_{[E x, t)} v) ≤ |Wj j|·ρ₁ + S'·Σ_{[0,T)} v` (`S' = Σ_j sl_j`). -/
theorem sum_win_le (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t)) (v : ℕ → ℝ) (hv : ∀ u, 0 ≤ v u) (ρ₁ : ℝ) (hρ₁ : 0 ≤ ρ₁)
    (j : Fin P.D) :
    ∑ i ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j, max 0 (ρ₁ + Pool.P0154.isum v (P.E i.1) i.2) ≤
      (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card * ρ₁ +
        (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T := by
  set W := Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j
  have hle : ∀ i ∈ W, i.2 ≤ T := by
    intro i hi
    simp only [W, Pool.P0223.Wj, Pool.P0223.Wall, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hi
    omega
  have e1 : ∑ i ∈ W, max 0 (ρ₁ + Pool.P0154.isum v (P.E i.1) i.2) =
      ∑ i ∈ W, (ρ₁ + Pool.P0154.isum v (P.E i.1) i.2) :=
    Finset.sum_congr rfl fun i _ => max_eq_right (add_nonneg hρ₁ (Pool.P0154.isum_nonneg v hv _ _))
  rw [e1, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Pool.P0154.sum_windows_eq W (fun i => P.E i.1) (fun i => i.2) v T hle]
  have h2 : ∑ u ∈ range T, (Pool.P0154.mult W (fun i => P.E i.1) (fun i => i.2) u : ℝ) * v u ≤
      ∑ u ∈ range T, (∑ j : Fin P.D, (P.sl j : ℝ)) * v u :=
    Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_right
      (Pool.P0223.mult_le P ℓ ωs φ hD hLv hlev ω T hlay hfit j u) (hv u)
  rw [← Finset.mul_sum] at h2
  have hI : Pool.P0154.isum v 0 T = ∑ u ∈ range T, v u := by unfold Pool.P0154.isum; rw [Finset.range_eq_Ico]
  rw [hI]
  linarith

/-- **P0228's `restD` bounded by counts (pathwise, on no-overflow), window-form budgets.** With `S' = Σ_j sl j`,
`C_j = #{t<T : canonT t = j}`, `N_j = #{t<T : ∃ y, E y = t ∧ thr0 y = j}` (all indices of `ι`, sampled or not),
`Mb_j = Λbar j + Wocc(len_j) + widV(len_j·cB, max 1 cB, L) + Bmin`, per-round budget `v ≥ 0` and copy budgets
`r x t = ρ₁ + Σ_{[E x, t)} v` (no constant `Rb`):
`restD ≤ Σ_j x_j·S'·(C_j + N_j)·Mb_j + Σ_j x_j·(S'ρ₀(2S'C_j + 1) + S'·V[0,T) + S'c·√T·√(2S'C_j + 1) + S'C_j·ρ₁
+ S'·V[0,T))`, i.e. P0238's `restD_le` bound with `Rb := ρ₁` plus one extra `S'·V[0,T)` per thread (the window
budgets, by `sum_win_le`), where `V[0,T) = Σ_{[0,T)} v`. -/
theorem restD_le_win (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ P.xr j) (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i)))
    (Θn : ℕ) (hΘn : ∀ f, P.thr0 f ≤ Θn) (hΘ : (Θn : ℝ) ≤ Θ)
    (hcB : 0 ≤ P.cB) (Λbar : ℕ → ℝ) (hΛ0 : ∀ i, 0 ≤ Λbar i) (hΛa : ∀ i i', i ≤ i' → Λbar i' ≤ Λbar i)
    (hΛ : ∀ x c, P.Λ x c ≤ Λbar (curT P.E P.thr0 P.D P.Bt x c))
    (v : ℕ → ℝ) (hv : ∀ u, 0 ≤ v u) (ρ₀ c : ℝ) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (ρ₁ : ℝ) (hρ₁ : 0 ≤ ρ₁) :
    Pool.P0228.restD P ℓ ωs φ hD hLv hlev T L v ρ₀ c (fun x t => ρ₁ + Pool.P0154.isum v (P.E x) t) ω ≤
      ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
          (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
            + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card)) *
          (Λbar j + Pool.P0222.Wocc L xmin M ρ nn TT Θ (Pool.P0238.lenOf Θn T P.Bt j)
            + Pool.P0158.widV ((lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L + P.Bmin)
        + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * c * (Real.sqrt T *
              Real.sqrt (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
                ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1))
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card * ρ₁
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T) := by
  set S' := ∑ j : Fin P.D, (P.sl j : ℝ)
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hxr0 : ∀ j, 0 ≤ P.xr j := fun j => hxm.le.trans (hxr j)
  unfold Pool.P0228.restD
  refine add_le_add ?_ (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hxr0 j))
  · -- end-rate term
    refine Pool.P0238.end_term_le P ℓ ωs φ hD hLv hlev ω T hlay hfit hxr0 _ _ (fun j => ?_) (fun j x hxe => ?_)
    · have h1 : 0 ≤ Pool.P0222.Wocc L xmin M ρ nn TT Θ (Pool.P0238.lenOf Θn T P.Bt j) := by
        unfold Pool.P0222.Wocc; positivity
      have h2 : 0 ≤ Pool.P0158.widV ((lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L := by
        unfold Pool.P0158.widV
        have : 0 ≤ max 1 P.cB := le_trans zero_le_one (le_max_left _ _)
        positivity
      have h3 : (0 : ℝ) ≤ P.Bmin := Nat.cast_nonneg _
      linarith [hΛ0 j]
    · have hlen : Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - P.E x ≤ lenOf Θn T P.Bt j := by
        unfold Pool.P0238.lenOf
        split_ifs with hj
        · exact Pool.P0238.life_le P ℓ ωs φ hD hLv hlev ω T hB Θn hΘn j hj hxe
        · simp only [Pool.P0238.endIn, Finset.mem_filter, Finset.mem_univ, true_and] at hxe
          have := (Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hxe.1).2.1
          omega
      have := Pool.P0238.MOfW_le P ℓ ωs φ hD hLv hlev ω T hL hxm hxm1 hxr hn hT hM hρ0 hB hρ hx0 hx
        (fun f => le_trans (by exact_mod_cast hΘn f) hΘ) hcB Λbar hΛ0 hΛa hΛ j hxe _ hlen
      linarith
  · -- per-thread credit slack
    have hW := Pool.P0223.card_Wj_le_canon P ℓ ωs φ hD hLv hlev ω T hlay hfit j
    set C := ((range T).filter (fun t => canonT P.D P.Bt t = j)).card
    set W := (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card
    have hWc : (W : ℝ) ≤ S' * C := hW
    have hsq : Real.sqrt (2 * (W : ℝ) + 1) ≤ Real.sqrt (2 * (S' * C) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hrsum : ∑ i ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j,
        max 0 (ρ₁ + Pool.P0154.isum v (P.E i.1) i.2) ≤ S' * C * ρ₁ + S' * Pool.P0154.isum v 0 T := by
      have hwin := sum_win_le P ℓ ωs φ hD hLv hlev ω T hlay hfit v hv ρ₁ hρ₁ j
      have : (W : ℝ) * ρ₁ ≤ S' * C * ρ₁ := mul_le_mul_of_nonneg_right hWc hρ₁
      linarith
    have e1 : S' * ρ₀ * (2 * W + 1) ≤ S' * ρ₀ * (2 * (S' * C) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hS0 hρ₀)
    have e2 : S' * c * (Real.sqrt T * Real.sqrt (2 * W + 1)) ≤ S' * c * (Real.sqrt T * Real.sqrt (2 * (S' * C) + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)) (mul_nonneg hS0 hc)
    linarith


open Classical in
/-- **In expectation, with a path-dependent budget.** For `v` a function of the coin path (`v ≥ 0`), copy budgets in
window form `r x t = ρ₁ + Σ_{[E x, t)} v`, and any event `G` implying that every thread fits before `T`:
`E_T[[G]·restD] ≤ (P0238's count terms with Rb replaced by ρ₁) + 2·S'·(Σ_j x_j)·E_T[[G]·Σ_{[0,T)} v]`. -/
theorem good_restD_win (hL' : P.IsLaw) (hN : 0 < P.N) (rc₀ : RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
    {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ P.xr j) (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i)))
    (Θn : ℕ) (hΘn : ∀ f, P.thr0 f ≤ Θn) (hΘ : (Θn : ℝ) ≤ Θ)
    (hcB : 0 ≤ P.cB) (Λbar : ℕ → ℝ) (hΛ0 : ∀ i, 0 ≤ Λbar i) (hΛa : ∀ i i', i ≤ i' → Λbar i' ≤ Λbar i)
    (hΛ : ∀ x c, P.Λ x c ≤ Λbar (curT P.E P.thr0 P.D P.Bt x c))
    (v : (ℕ → RC P) → ℕ → ℝ) (hv : ∀ ω u, 0 ≤ v ω u) (ρ₀ c : ℝ) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (ρ₁ : ℝ)
    (hρ₁ : 0 ≤ ρ₁) (G : (Fin T → RC P) → Prop)
    (hGfit : ∀ ω, G ω → ∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t)) :
    ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
      (if G ω then Pool.P0228.restD P ℓ ωs φ hD hLv hlev T L (v (Pool.P0210.extR P rc₀ ω)) ρ₀ c
        (fun x t => ρ₁ + Pool.P0154.isum (v (Pool.P0210.extR P rc₀ ω)) (P.E x) t) (Pool.P0210.extR P rc₀ ω) else 0) ≤
      (∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
          (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
            + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card)) *
          (Λbar j + Pool.P0222.Wocc L xmin M ρ nn TT Θ (lenOf Θn T P.Bt j)
            + Pool.P0158.widV ((lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L + P.Bmin)
        + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * c * (Real.sqrt T *
              Real.sqrt (2 * ((∑ j : Fin P.D, (P.sl j : ℝ)) *
                ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1))
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card * ρ₁))
        + 2 * (∑ j : Fin P.D, (P.sl j : ℝ)) * (∑ j : Fin P.D, P.xr j) *
          ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
            (if G ω then Pool.P0154.isum (v (Pool.P0210.extR P rc₀ ω)) 0 T else 0) := by
  set S' := ∑ j : Fin P.D, (P.sl j : ℝ)
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  have hxr0 : ∀ j, 0 ≤ P.xr j := fun j => hxm.le.trans (hxr j)
  set A := ∑ j : Fin P.D, P.xr j * (S' * (((range T).filter (fun t => canonT P.D P.Bt t = j)).card
            + ((range T).filter (fun t => ∃ y, P.E y = t ∧ P.thr0 y = j)).card)) *
          (Λbar j + Pool.P0222.Wocc L xmin M ρ nn TT Θ (lenOf Θn T P.Bt j)
            + Pool.P0158.widV ((lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L + P.Bmin)
  set B := ∑ j : Fin P.D, P.xr j * (S' * ρ₀ *
            (2 * (S' * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1)
          + S' * c * (Real.sqrt T * Real.sqrt (2 * (S' * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1))
          + S' * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card * ρ₁)
  have hA : 0 ≤ A := Finset.sum_nonneg fun j _ => by
    have h1 : 0 ≤ Pool.P0222.Wocc L xmin M ρ nn TT Θ (lenOf Θn T P.Bt j) := by
      unfold Pool.P0222.Wocc; positivity
    have h2 : 0 ≤ Pool.P0158.widV ((lenOf Θn T P.Bt j : ℕ) * P.cB) (max 1 P.cB) L := by
      unfold Pool.P0158.widV
      have : 0 ≤ max 1 P.cB := le_trans zero_le_one (le_max_left _ _)
      positivity
    have h3 : (0 : ℝ) ≤ P.Bmin := Nat.cast_nonneg _
    have := hΛ0 j
    have := hxr0 j
    positivity
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => by
    have := hxr0 j
    positivity
  have hpt : ∀ ω : Fin T → RC P, (if G ω then Pool.P0228.restD P ℓ ωs φ hD hLv hlev T L
        (v (Pool.P0210.extR P rc₀ ω)) ρ₀ c
        (fun x t => ρ₁ + Pool.P0154.isum (v (Pool.P0210.extR P rc₀ ω)) (P.E x) t) (Pool.P0210.extR P rc₀ ω) else 0) ≤
      (A + B) + 2 * S' * (∑ j : Fin P.D, P.xr j) *
        (if G ω then Pool.P0154.isum (v (Pool.P0210.extR P rc₀ ω)) 0 T else 0) := by
    intro ω
    split_ifs with hG
    · have h := restD_le_win P ℓ ωs φ hD hLv hlev (Pool.P0210.extR P rc₀ ω) T hlay (hGfit ω hG) hL hxm hxm1 hxr
        hn hT hM hρ0 hB hρ hx0 hx Θn hΘn hΘ hcB Λbar hΛ0 hΛa hΛ (v (Pool.P0210.extR P rc₀ ω)) (hv _) ρ₀ c hρ₀ hc ρ₁
        hρ₁
      have e : ∑ j : Fin P.D, P.xr j * (S' * ρ₀ *
            (2 * (S' * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1)
          + S' * Pool.P0154.isum (v (Pool.P0210.extR P rc₀ ω)) 0 T
          + S' * c * (Real.sqrt T * Real.sqrt (2 * (S' * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card) + 1))
          + S' * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card * ρ₁
          + S' * Pool.P0154.isum (v (Pool.P0210.extR P rc₀ ω)) 0 T) =
          B + 2 * S' * (∑ j : Fin P.D, P.xr j) * Pool.P0154.isum (v (Pool.P0210.extR P rc₀ ω)) 0 T := by
        simp only [B, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by ring
      linarith
    · have : 0 ≤ 2 * S' * (∑ j : Fin P.D, P.xr j) * 0 := by simp
      linarith
  calc _ ≤ ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * ((A + B) + 2 * S' * (∑ j : Fin P.D, P.xr j) *
        (if G ω then Pool.P0154.isum (v (Pool.P0210.extR P rc₀ ω)) 0 T else 0)) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (Pool.P0228.pw_nonneg P hL' ω)
    _ = (A + B) + 2 * S' * (∑ j : Fin P.D, P.xr j) * ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
        (if G ω then Pool.P0154.isum (v (Pool.P0210.extR P rc₀ ω)) 0 T else 0) := by
      have hK : ∀ (K : ℝ) (I : (Fin T → RC P) → ℝ), ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * ((A + B) + K * I ω)
          = (A + B) + K * ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * I ω := by
        intro K I
        rw [show (∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * ((A + B) + K * I ω)) =
            ∑ ω : Fin T → RC P, ((A + B) * Pool.P0202.pw (wR P) ω + K * (Pool.P0202.pw (wR P) ω * I ω)) from
          Finset.sum_congr rfl (fun ω _ => by ring), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          Pool.P0228.sum_pw P hL' hN, mul_one]
      exact hK _ _

end Pool.P0247
