import Pool.P0282.Threads
import Pool.P0275.Margins

/-!
# P0275's margins on P0261's epochs: `ΛbarP j ≤ α₀ + β₀√Bt_j` (P0262's F7, part 2)
-/

namespace Pool.P0282

open Finset Pool.P0261 Pool.P0250

/-- On P0261's epochs (`Bt(j−1) = 2·Bt j` for `1 ≤ j ≤ Dp`), P0250's rule-margin budget is
`wP i ≤ (2D+1)·(A + B·√Bt_i)` for `i ≤ D − 1`. -/
theorem wP_le (T : ℕ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (i : ℕ) (hi : i ≤ Dn T - 1) :
    wP A B (Bt T) (Dn T) i ≤ (2 * Dn T + 1) * (A + B * Real.sqrt (Bt T i)) := by
  unfold wP
  have hBi : (1 : ℝ) ≤ Bt T i := by exact_mod_cast Nat.one_le_two_pow
  have hsi : 1 ≤ Real.sqrt (Bt T i) := by rw [Real.one_le_sqrt]; exact hBi
  have hterm : ∀ j ∈ Ico 1 (Dn T), (if i ≤ j - 1 then (Bt T (j - 1) : ℝ) * aaP A B (Bt T) j else 0) ≤
      2 * (A + B * Real.sqrt (Bt T i)) := by
    intro j hj
    rw [mem_Ico] at hj
    split_ifs with hij
    · have hb : (Bt T (j - 1) : ℝ) = 2 * Bt T j := by
        have : Bt T (j - 1) = 2 * Bt T j := by
          unfold Bt; rw [← pow_succ']; congr 1; unfold Dn at hj; omega
        exact_mod_cast this
      have hbj : (0 : ℝ) < Bt T j := by exact_mod_cast Nat.two_pow_pos _
      have hsj : Real.sqrt (Bt T j) ^ 2 = Bt T j := Real.sq_sqrt hbj.le
      have hsj0 : 0 < Real.sqrt (Bt T j) := Real.sqrt_pos.2 hbj
      have hji : Real.sqrt (Bt T j) ≤ Real.sqrt (Bt T i) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Bt_anti T (show i ≤ j by omega))
      unfold aaP
      rw [hb]
      have e : 2 * (Bt T j : ℝ) * (A / Bt T j + B / Real.sqrt (Bt T j)) = 2 * A + 2 * B * Real.sqrt (Bt T j) := by
        field_simp; nlinarith [hsj]
      rw [e]; nlinarith
    · have : 0 ≤ A + B * Real.sqrt (Bt T i) := by positivity
      linarith
  have hsum : ∑ j ∈ Ico 1 (Dn T), (if i ≤ j - 1 then (Bt T (j - 1) : ℝ) * aaP A B (Bt T) j else 0) ≤
      Dn T * (2 * (A + B * Real.sqrt (Bt T i))) := by
    calc _ ≤ ∑ _j ∈ Ico 1 (Dn T), 2 * (A + B * Real.sqrt (Bt T i)) := Finset.sum_le_sum hterm
      _ = ((Ico 1 (Dn T)).card : ℝ) * (2 * (A + B * Real.sqrt (Bt T i))) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Dn T * (2 * (A + B * Real.sqrt (Bt T i))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [Nat.card_Ico]; exact_mod_cast Nat.sub_le _ _
  have hcc : (if i ≤ Dn T - 1 then ccP A B (Bt T) (Dn T) else 0) ≤ A + B * Real.sqrt (Bt T i) := by
    rw [ite_eq_left_of_eq_true _ _ (eq_true hi)]; unfold ccP
    rw [Pool.P0282.Bt_last]; simp only [Nat.cast_one, Real.sqrt_one, mul_one]; nlinarith
  nlinarith

theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

theorem sqrt_mul_le_two {m b X : ℝ} (hX : 0 ≤ X) (hb : 0 ≤ b) (hm0 : 0 ≤ m) (hm : m ≤ 4 * b) :
    Real.sqrt (m * X) ≤ 2 * Real.sqrt X * Real.sqrt b := by
  have h1 := Real.sq_sqrt hX
  have h2 := Real.sq_sqrt hb
  calc Real.sqrt (m * X) ≤ Real.sqrt ((2 * Real.sqrt X * Real.sqrt b) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have : (2 * Real.sqrt X * Real.sqrt b) ^ 2 = 4 * b * X := by rw [mul_pow, mul_pow, h1, h2]; ring
        rw [this]; nlinarith
    _ = 2 * Real.sqrt X * Real.sqrt b := Real.sqrt_sq (by positivity)

section Margins

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : Pool.P0194.ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ)
  (ρG : Pool.P0212.AState ι → Finset ι → Option ι → Bool → ℝ)

/-- The constant part of the margin bound. -/
noncomputable def α₀ (T : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ) : ℝ :=
  Lt / κ + Pool.P0226.αT (ι := ι) η L T δ + Lc / (2 * (wE * γ)) + 2 * max 1 P.cB * Lb + 2 * Ls / xmin +
    2 * Real.sqrt (Ls * (Θ * (ρ * TT / nn))) + (2 * Dn T + 1) * AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ

/-- The `√Bt`-coefficient of the margin bound. -/
noncomputable def β₀ (T : ℕ) (Ls Lb M : ℝ) : ℝ :=
  4 * Real.sqrt (P.cB * Lb) + 4 * Real.sqrt (Ls * M) + (2 * Dn T + 1) * BP P η L N G γ wE ρG Ls M

theorem AP_nonneg (T : ℕ) {δ Ls Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hη : 0 < η) (hδ : 0 ≤ δ) (hγ : 0 < γ)
    (hwE : 0 < wE) (hLs : 0 ≤ Ls) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ) (hxm : 0 < xmin) (hθ : 0 ≤ P.θ) :
    0 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ := by
  have hα := Pool.P0226.αT_nonneg (ι := ι) (η := η) (L := L) (T := T) hη hδ
  unfold AP
  have : 0 ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).θ := hθ
  have := Real.sqrt_nonneg (Ls * (Θ * (ρ * TT / nn)))
  have : 0 ≤ Lc / (2 * (wE * γ)) := div_nonneg hLc (by positivity)
  have : 0 ≤ 2 * Ls / xmin := div_nonneg (by linarith) hxm.le
  have : 0 ≤ Lt / κ := div_nonneg hLt hκ.le
  positivity

theorem BP_nonneg (Ls M : ℝ) : 0 ≤ BP P η L N G γ wE ρG Ls M := by
  unfold BP; positivity

/-- **P0250's record margins on P0261's epochs**: at ages `m ≤ 4·Bt_j`, `ΛP j m ≤ α₀ + β₀·√Bt_j`. -/
theorem ΛP_le (T : ℕ) (hBt : P.Bt = Bt T) (hD : P.D = Dn T) {δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ}
    (hη : 0 < η) (hδ : 0 ≤ δ) (hγ : 0 < γ) (hwE : 0 < wE) (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc)
    (hLt : 0 ≤ Lt) (hκ : 0 < κ) (hxm : 0 < xmin) (hM : 0 ≤ M) (hθ : 0 ≤ P.θ) (hcB : 0 ≤ P.cB)
    (hTΘ : 0 ≤ Θ * (ρ * TT / nn)) (j m : ℕ) (hj : j ≤ Dn T - 1) (hm : m ≤ 4 * Bt T j) :
    ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ j m ≤
      α₀ P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ +
        β₀ P η L N G γ wE ρG T Ls Lb M * Real.sqrt (Bt T j) := by
  have hAP := AP_nonneg P η L N G γ wE ρG T (δ := δ) (Lc := Lc) (Lt := Lt) (κ := κ) (M := M) (ρ := ρ) (nn := nn)
    (TT := TT) (Θ := Θ) hη hδ hγ hwE hLs hLc hLt hκ hxm hθ
  have hBP := BP_nonneg P η L N G γ wE ρG Ls M
  have hw := wP_le T hAP hBP j hj
  have hb0 : (0 : ℝ) ≤ Bt T j := Nat.cast_nonneg _
  have hsb := Real.sq_sqrt hb0
  have hm' : (m : ℝ) ≤ 4 * Bt T j := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  -- B̂ width
  have hW1 : Pool.P0158.widV (m * P.cB) (max 1 P.cB) Lb ≤
      2 * max 1 P.cB * Lb + 4 * Real.sqrt (P.cB * Lb) * Real.sqrt (Bt T j) := by
    unfold Pool.P0158.widV
    have : Real.sqrt (m * P.cB * Lb) ≤ 2 * Real.sqrt (P.cB * Lb) * Real.sqrt (Bt T j) := by
      rw [mul_assoc]; exact sqrt_mul_le_two (mul_nonneg hcB hLb) hb0 hm0 hm'
    linarith
  -- occupancy width
  have hW2 : Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m ≤
      2 * Ls / xmin + 2 * Real.sqrt (Ls * (Θ * (ρ * TT / nn))) + 4 * Real.sqrt (Ls * M) * Real.sqrt (Bt T j) := by
    unfold Pool.P0222.Wocc
    have h1 : Real.sqrt (Ls * (m * M + Θ * (ρ * TT / nn))) ≤
        Real.sqrt (Ls * (m * M)) + Real.sqrt (Ls * (Θ * (ρ * TT / nn))) := by
      rw [mul_add]; exact sqrt_add_le' (by positivity) (mul_nonneg hLs hTΘ)
    have h2 : Real.sqrt (Ls * (m * M)) ≤ 2 * Real.sqrt (Ls * M) * Real.sqrt (Bt T j) := by
      rw [show Ls * (m * M) = m * (Ls * M) by ring]; exact sqrt_mul_le_two (mul_nonneg hLs hM) hb0 hm0 hm'
    linarith
  have hα := Pool.P0226.αT_nonneg (ι := ι) (η := η) (L := L) (T := T) hη hδ
  have hw' : wP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M)
      (Pool.P0225.withAlgG P η L N G γ wE ρG).Bt (Pool.P0225.withAlgG P η L N G γ wE ρG).D j ≤
      (2 * Dn T + 1) * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ +
        BP P η L N G γ wE ρG Ls M * Real.sqrt (Bt T j)) := by
    have e1 : (Pool.P0225.withAlgG P η L N G γ wE ρG).Bt = Bt T := hBt
    have e2 : (Pool.P0225.withAlgG P η L N G γ wE ρG).D = Dn T := hD
    rw [e1, e2]; exact hw
  have e3 : (Pool.P0225.withAlgG P η L N G γ wE ρG).cB = P.cB := rfl
  unfold ΛP α₀ β₀
  rw [e3]
  nlinarith [Real.sqrt_nonneg ((Bt T j : ℕ) : ℝ)]

/-- **P0275's clock bound on P0261's epochs**: `ΛbarP i ≤ α₀ + β₀·√Bt_i` for every thread `i ≤ D − 1`, when the
entry threads are `≤ Θn ≤ Dp`. -/
theorem ΛbarP_le (T : ℕ) (hT : 1 ≤ T) (hBt : P.Bt = Bt T) (hD : P.D = Dn T) {δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ}
    (hη : 0 < η) (hδ : 0 ≤ δ) (hγ : 0 < γ) (hwE : 0 < wE) (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc)
    (hLt : 0 ≤ Lt) (hκ : 0 < κ) (hxm : 0 < xmin) (hM : 0 ≤ M) (hθ : 0 ≤ P.θ) (hcB : 0 ≤ P.cB)
    (hTΘ : 0 ≤ Θ * (ρ * TT / nn)) (Θn : ℕ) (hΘn : Θn ≤ Dp T) (i : ℕ) (hi : i ≤ Dn T - 1) :
    Pool.P0275.ΛbarP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn i ≤
      α₀ P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ +
        β₀ P η L N G γ wE ρG T Ls Lb M * Real.sqrt (Bt T i) := by
  unfold Pool.P0275.ΛbarP
  obtain ⟨j', hj1, hj2, he⟩ := Pool.P0275.Λbar_eq P.D (fun j => ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn
    TT Θ j (Pool.P0238.lenOf Θn T P.Bt j)) i
  rw [he]
  rw [hD] at hj1 hj2
  have hij : i ≤ j' := by rw [min_eq_left hi] at hj1; exact hj1
  have hlen : Pool.P0238.lenOf Θn T P.Bt j' ≤ 4 * Bt T j' := by
    rw [hBt]; exact Pool.P0282.lenOf_le' T Θn hT hΘn j'
  refine (ΛP_le P η L N G γ wE ρG T hBt hD hη hδ hγ hwE hLs hLb hLc hLt hκ hxm hM hθ hcB hTΘ j' _ hj2 hlen).trans ?_
  have hβ : 0 ≤ β₀ P η L N G γ wE ρG T Ls Lb M := by
    unfold β₀; have := BP_nonneg P η L N G γ wE ρG Ls M; positivity
  have hs : Real.sqrt (Bt T j') ≤ Real.sqrt (Bt T i) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Bt_anti T hij)
  nlinarith

end Margins

end Pool.P0282
