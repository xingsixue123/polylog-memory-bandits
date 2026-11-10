import Pool.P0223.CreditD

/-!
# P0223's credit bound restricted to POSITIVE rate jumps (threads above a rate floor)
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0203 Pool.P0176 Pool.P0065

namespace Pool.P0255

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
  (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)

open Classical in
/-- The jumps into thread `j` that can change the rate: none into a thread at the floor `xf`. -/
noncomputable def WjP (ω : ℕ → RC P) (T : ℕ) (xf : ℝ) (j : Fin P.D) : Finset (ι × ℕ) :=
  if P.xr j ≤ xf then ∅ else Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j

section Facts

variable (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
  (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
include hlay hfit

/-- A jump into a thread at the floor is zero (the source thread is finer, hence also at the floor). -/
theorem jmp_floor (hxr : ∀ j, 0 < P.xr j) (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i) {xf : ℝ}
    (hfl : ∀ j, xf ≤ P.xr j) (j : Fin P.D) (hj : P.xr j ≤ xf) {i : ι × ℕ}
    (hi : i ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j) : Pool.P0223.jmp P ℓ ωs φ ω i.1 i.2 = 0 := by
  have hb := Pool.P0223.jmp_bounds P ℓ ωs φ hD hLv hlev ω T hlay hfit hxr hanti j hi
  unfold Pool.P0223.Wj at hi
  rw [Finset.mem_filter, Finset.mem_filter] at hi
  obtain ⟨⟨hw, -⟩, hk⟩ := hi
  obtain ⟨h0, h1, e0, e1⟩ := Pool.P0223.rates_wall P ℓ ωs φ hD hLv hlev ω T hlay hfit hw
  have hkj : (⟨_, h0⟩ : Fin P.D) = j := by
    unfold Pool.P0223.key at hk; rw [dif_pos h0] at hk; exact hk
  have hjm : Pool.P0223.jmp P ℓ ωs φ ω i.1 i.2 = P.xr j - P.xr ⟨_, h1⟩ := by
    unfold Pool.P0223.jmp; rw [e0, e1, hkj]
  have := hfl ⟨_, h1⟩
  linarith [hb.1]

open Classical in
/-- **P0223's `credit_D` with only the jumps that can change the rate.** Same hypotheses, plus a rate floor `xf`
(`xf ≤ x_j` for all `j`): the credit sum is at most `(S'·Σ_j x_j)·(BASE − ALG)[0,T)` plus the per-thread slack in which
the jump count `|Wj|` is replaced by `|WjP|` (`= 0` for threads at the floor). -/
theorem credit_DP (hT : 1 ≤ T) (hxr : ∀ j, 0 < P.xr j) (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i)
    {xf : ℝ} (hfl : ∀ j, xf ≤ P.xr j)
    (v : ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c)
    (hint : ∀ a b, a ≤ b → b ≤ T →
      -Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) a b ≤
        ρ₀ + Pool.P0154.isum v a b + c * Real.sqrt ((b : ℝ) - a))
    (r : ι → ℕ → ℝ)
    (hA : ∀ x t, t ≤ T → P.E x < t → (∀ u, P.E x ≤ u → u < t → x ∈ active P ℓ ω ωs φ u) →
      Pool.P0154.isum (fun u => aPol P ℓ ωs φ ω u) (P.E x) t ≤
        Pool.P0154.isum (fun u => ℓr P ℓ u x) (P.E x) t + r x t) :
    ∑ x ∈ univ.filter (fun x => P.E x < T),
        ∑ t ∈ Ico (P.E x + 1) (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x),
          (Pool.P0209.rateD P ℓ ωs φ ω t x - Pool.P0209.rateD P ℓ ωs φ ω (t - 1) x) *
            max 0 (-Pool.P0154.isum (fun t => ℓr P ℓ t x - bPol P ℓ ω t) (P.E x) t)
      ≤ ((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) 0 T
        + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * (WjP P ℓ ωs φ hD hLv hlev ω T xf j).card + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * c *
            (Real.sqrt T * Real.sqrt (2 * (WjP P ℓ ωs φ hD hLv hlev ω T xf j).card + 1))
          + ∑ i ∈ WjP P ℓ ωs φ hD hLv hlev ω T xf j, max 0 (r i.1 i.2)) := by
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T
  set S' := ∑ j : Fin P.D, (P.sl j : ℝ)
  have hsum : ∑ x ∈ univ.filter (fun x => P.E x < T), ∑ t ∈ Ico (P.E x + 1) (b x),
        Pool.P0223.jmp P ℓ ωs φ ω x t * max 0 (Pool.P0223.lead P ℓ ω x t) =
      ∑ i ∈ Pool.P0223.Wall P ℓ ωs φ hD hLv hlev ω T,
        Pool.P0223.jmp P ℓ ωs φ ω i.1 i.2 * max 0 (Pool.P0223.lead P ℓ ω i.1 i.2) := by
    unfold Pool.P0223.Wall
    conv_rhs => rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_filter] at hx
    have hbT : b x ≤ T := (Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hx.2).2.1
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  -- floored threads contribute nothing
  have hP : ∑ j : Fin P.D, ∑ i ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j,
        Pool.P0223.jmp P ℓ ωs φ ω i.1 i.2 * max 0 (Pool.P0223.lead P ℓ ω i.1 i.2) =
      ∑ j : Fin P.D, ∑ i ∈ WjP P ℓ ωs φ hD hLv hlev ω T xf j,
        Pool.P0223.jmp P ℓ ωs φ ω i.1 i.2 * max 0 (Pool.P0223.lead P ℓ ω i.1 i.2) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold WjP
    split_ifs with hj
    · rw [Finset.sum_empty]
      exact Finset.sum_eq_zero fun i hi => by
        rw [jmp_floor P ℓ ωs φ hD hLv hlev ω T hlay hfit hxr hanti hfl j hj hi, zero_mul]
    · rfl
  show ∑ x ∈ univ.filter (fun x => P.E x < T), ∑ t ∈ Ico (P.E x + 1) (b x),
        Pool.P0223.jmp P ℓ ωs φ ω x t * max 0 (Pool.P0223.lead P ℓ ω x t) ≤ _
  rw [hsum, Pool.P0223.sum_wall_eq P ℓ ωs φ hD hLv hlev ω T hlay hfit, hP]
  refine Pool.P0162.jump_cost_threads (fun i : ι × ℕ => P.E i.1) (fun i => i.2) univ
    (WjP P ℓ ωs φ hD hLv hlev ω T xf) (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) v ρ₀ S' c P.xr T hT hv hρ₀ hc
    hS0 hint ?_ ?_ (fun j _ => (hxr j).le) (fun i => Pool.P0223.jmp P ℓ ωs φ ω i.1 i.2)
    (fun i => Pool.P0223.lead P ℓ ω i.1 i.2) (fun i => r i.1 i.2) ?_ ?_
  · intro j _ i hi
    unfold WjP at hi
    split_ifs at hi
    · simp at hi
    · unfold Pool.P0223.Wj Pool.P0223.Wall at hi
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hi
      exact hi.1.1.1.2.le
  · intro j _ u
    refine le_trans ?_ (Pool.P0223.mult_le P ℓ ωs φ hD hLv hlev ω T hlay hfit j u)
    unfold WjP
    split_ifs
    · unfold Pool.P0154.mult; simp
    · exact le_rfl
  · intro j _ i hi
    unfold WjP at hi
    split_ifs at hi
    · simp at hi
    · exact Pool.P0223.jmp_bounds P ℓ ωs φ hD hLv hlev ω T hlay hfit hxr hanti j hi
  · intro j _ i hi
    unfold WjP at hi
    split_ifs at hi
    · simp at hi
    · unfold Pool.P0223.Wj Pool.P0223.Wall at hi
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and] at hi
      obtain ⟨⟨⟨⟨hxT, htT⟩, hE, htb⟩, -⟩, -⟩ := hi
      have hw := (Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T i.1 hxT)
      have halg := hA i.1 i.2 htT.le (by omega)
        (fun u h1 h2 => (hw.2.2 u (by omega)).2 ⟨h1, by omega⟩)
      exact Pool.P0154.lead_le (fun u => bPol P ℓ ω u) (fun u => aPol P ℓ ωs φ ω u) (fun u => ℓr P ℓ u i.1)
        (P.E i.1) i.2 (r i.1 i.2) halg

end Facts

end Pool.P0255
