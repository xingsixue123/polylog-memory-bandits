import Pool.Prelude

/-!
# Rounding a finite distribution to multiples of 1/N (P0166's component C8)

A distribution `p` on a finite type `α` with a distinguished element `b` (Design Z: ALG's experts, `b` = the BASE
meta-arm) is rounded down to multiples of `1/N` off `b`, and the missing mass goes to `b`:
`cnt i = ⌊p i · N⌋₊` for `i ≠ b`, `cnt b = N − Σ_{j ≠ b} cnt j`, `pt i = cnt i / N`.
-/

namespace Pool.P0179

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] (N : ℕ) (b : α) (p : α → ℝ)

/-- Rounded counts. -/
noncomputable def cnt (i : α) : ℕ :=
  if i = b then N - ∑ j ∈ univ.erase b, ⌊p j * N⌋₊ else ⌊p i * N⌋₊

/-- The rounded distribution. -/
noncomputable def pt (i : α) : ℝ := (cnt N b p i : ℝ) / N

variable {N b p}

section Basic

variable (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
include hp0 hp1

lemma sum_floor_le : ∑ j ∈ univ.erase b, ⌊p j * N⌋₊ ≤ N := by
  have h1 : ((∑ j ∈ univ.erase b, ⌊p j * N⌋₊ : ℕ) : ℝ) ≤ ∑ j ∈ univ.erase b, p j * N := by
    push_cast
    exact Finset.sum_le_sum fun j _ => Nat.floor_le (mul_nonneg (hp0 j) (Nat.cast_nonneg N))
  have h2 : ∑ j ∈ univ.erase b, p j * N ≤ N := by
    rw [← Finset.sum_mul]
    have : ∑ j ∈ univ.erase b, p j ≤ ∑ j, p j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _ => hp0 j)
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  exact_mod_cast h1.trans h2

lemma sum_cnt : ∑ i, cnt N b p i = N := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
  have h : ∑ i ∈ univ.erase b, cnt N b p i = ∑ j ∈ univ.erase b, ⌊p j * N⌋₊ :=
    Finset.sum_congr rfl fun i hi => by simp [cnt, Finset.ne_of_mem_erase hi]
  rw [h]
  simp only [cnt, if_true]
  have := sum_floor_le hp0 hp1 (N := N) (b := b)
  omega

end Basic

lemma pt_nonneg (i : α) : 0 ≤ pt N b p i := by unfold pt; positivity

lemma sum_pt (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) : ∑ i, pt N b p i = 1 := by
  unfold pt
  rw [← Finset.sum_div]
  have : (∑ i, (cnt N b p i : ℝ)) = N := by exact_mod_cast sum_cnt hp0 hp1
  rw [this]; field_simp

/-- Off `b`, the rounded mass is at most the true mass, and less by under `1/N`. -/
lemma pt_le_of_ne (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) {i : α} (hi : i ≠ b) :
    pt N b p i ≤ p i ∧ p i < pt N b p i + 1 / N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold pt cnt
  rw [if_neg hi]
  have h1 := Nat.floor_le (mul_nonneg (hp0 i) hNr.le)
  have h2 := Nat.lt_floor_add_one (p i * N)
  constructor
  · rw [div_le_iff₀ hNr]; exact h1
  · rw [← add_div, lt_div_iff₀ hNr]; exact h2

/-- The missing mass `pt b − p b = Σ_{i ≠ b} (p i − pt i)` lies in `[0, (|α| − 1)/N]`. -/
lemma pt_b_bounds (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    pt N b p b - p b = ∑ i ∈ univ.erase b, (p i - pt N b p i) ∧ 0 ≤ pt N b p b - p b ∧
      pt N b p b - p b ≤ ((Fintype.card α - 1 : ℕ) : ℝ) / N := by
  have hs := sum_pt hN hp0 hp1 (b := b)
  have e1 : ∑ i, p i = p b + ∑ i ∈ univ.erase b, p i := (Finset.add_sum_erase _ _ (Finset.mem_univ b)).symm
  have e2 : ∑ i, pt N b p i = pt N b p b + ∑ i ∈ univ.erase b, pt N b p i :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ b)).symm
  have heq : pt N b p b - p b = ∑ i ∈ univ.erase b, (p i - pt N b p i) := by
    rw [Finset.sum_sub_distrib]; linarith
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    exact Finset.sum_nonneg fun i hi => by
      have := (pt_le_of_ne hN hp0 (Finset.ne_of_mem_erase hi)).1; linarith
  · rw [heq]
    calc ∑ i ∈ univ.erase b, (p i - pt N b p i) ≤ ∑ _i ∈ univ.erase b, (1 / N : ℝ) :=
          Finset.sum_le_sum fun i hi => by
            have := (pt_le_of_ne hN hp0 (Finset.ne_of_mem_erase hi)).2; linarith
      _ = ((Fintype.card α - 1 : ℕ) : ℝ) / N := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ, nsmul_eq_mul]
          field_simp

/-- **1. Played loss.** For losses in `[0, 1]`, the rounded and the true expected losses differ by at most
`(|α| − 1)/N`. -/
theorem played_loss_le (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (ℓ : α → ℝ)
    (hl0 : ∀ i, 0 ≤ ℓ i) (hl1 : ∀ i, ℓ i ≤ 1) :
    |∑ i, pt N b p i * ℓ i - ∑ i, p i * ℓ i| ≤ ((Fintype.card α - 1 : ℕ) : ℝ) / N := by
  obtain ⟨heq, hnn, hle⟩ := pt_b_bounds hN hp0 hp1 (b := b)
  have hsplit : ∑ i, pt N b p i * ℓ i - ∑ i, p i * ℓ i =
      (pt N b p b - p b) * ℓ b - ∑ i ∈ univ.erase b, (p i - pt N b p i) * ℓ i := by
    rw [← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
    have : ∑ i ∈ univ.erase b, (pt N b p i * ℓ i - p i * ℓ i) =
        -∑ i ∈ univ.erase b, (p i - pt N b p i) * ℓ i := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; ring
  have hA : 0 ≤ ∑ i ∈ univ.erase b, (p i - pt N b p i) * ℓ i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (by
      have := (pt_le_of_ne hN hp0 (Finset.ne_of_mem_erase hi)).1; linarith) (hl0 i)
  have hB : ∑ i ∈ univ.erase b, (p i - pt N b p i) * ℓ i ≤ pt N b p b - p b := by
    rw [heq]
    exact Finset.sum_le_sum fun i hi => by
      have := (pt_le_of_ne hN hp0 (Finset.ne_of_mem_erase hi)).1
      nlinarith [hl1 i, hl0 i]
  have hC : 0 ≤ (pt N b p b - p b) * ℓ b := mul_nonneg hnn (hl0 b)
  have hD : (pt N b p b - p b) * ℓ b ≤ pt N b p b - p b := by nlinarith [hl1 b]
  rw [hsplit, abs_le]
  constructor <;> linarith

/-- Every true mass is at most the rounded mass plus `1/N` (at `b`: at most the rounded mass). -/
lemma p_le_pt_add (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (i : α) :
    p i ≤ pt N b p i + 1 / N := by
  by_cases hi : i = b
  · subst hi
    have := (pt_b_bounds hN hp0 hp1 (b := i)).2.1
    have : (0 : ℝ) ≤ 1 / N := by positivity
    linarith
  · exact (pt_le_of_ne hN hp0 hi).2.le

/-- **2. IX bias** with rounded denominators: `Σ p_i ℓ_i γ/(pt_i + γ) ≤ |α|·(γ + 1/N)`. -/
theorem ix_bias_le (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (ℓ : α → ℝ)
    (hl0 : ∀ i, 0 ≤ ℓ i) (hl1 : ∀ i, ℓ i ≤ 1) {γ : ℝ} (hγ : 0 < γ) :
    ∑ i, p i * ℓ i * (γ / (pt N b p i + γ)) ≤ Fintype.card α * (γ + 1 / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∀ i, p i * ℓ i * (γ / (pt N b p i + γ)) ≤ γ + 1 / N := by
    intro i
    have hpt := pt_nonneg (N := N) (b := b) (p := p) i
    have hden : 0 < pt N b p i + γ := by linarith
    have h1 : p i * ℓ i ≤ p i := by nlinarith [hp0 i, hl1 i]
    have h2 : p i * ℓ i * (γ / (pt N b p i + γ)) ≤ p i * (γ / (pt N b p i + γ)) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have h3 : p i * (γ / (pt N b p i + γ)) ≤ (pt N b p i + 1 / N) * (γ / (pt N b p i + γ)) :=
      mul_le_mul_of_nonneg_right (p_le_pt_add hN hp0 hp1 i) (by positivity)
    have h4 : (pt N b p i + 1 / N) * (γ / (pt N b p i + γ)) ≤ γ + 1 / N := by
      rw [add_mul]
      have e1 : pt N b p i * (γ / (pt N b p i + γ)) ≤ γ := by
        rw [mul_div_assoc', div_le_iff₀ hden]; nlinarith
      have e2 : 1 / N * (γ / (pt N b p i + γ)) ≤ 1 / N := by
        have : γ / (pt N b p i + γ) ≤ 1 := by rw [div_le_one hden]; linarith
        have : (0 : ℝ) ≤ 1 / N := by positivity
        nlinarith
      linarith
    linarith
  calc ∑ i, p i * ℓ i * (γ / (pt N b p i + γ)) ≤ ∑ _i : α, (γ + 1 / N) := Finset.sum_le_sum fun i _ => key i
    _ = Fintype.card α * (γ + 1 / N) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Per-element second-moment bound: `p_i ℓ_i² pt_i/(pt_i + γ)² ≤ 1 + 1/(4Nγ)`
(using `t/(t+γ)² ≤ 1/(4γ)` for `t ≥ 0`). -/
lemma sm_term_le (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (ℓ : α → ℝ)
    (hl0 : ∀ i, 0 ≤ ℓ i) (hl1 : ∀ i, ℓ i ≤ 1) {γ : ℝ} (hγ : 0 < γ) (i : α) :
    p i * ℓ i ^ 2 * (pt N b p i / (pt N b p i + γ) ^ 2) ≤ 1 + 1 / (4 * N * γ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set t := pt N b p i with ht
  have hpt : 0 ≤ t := pt_nonneg i
  have hden : 0 < t + γ := by linarith
  have hq : 0 ≤ t / (t + γ) ^ 2 := by positivity
  have h1 : p i * ℓ i ^ 2 * (t / (t + γ) ^ 2) ≤ p i * (t / (t + γ) ^ 2) := by
    have hl2 : ℓ i ^ 2 ≤ 1 := by nlinarith [hl0 i, hl1 i]
    have : p i * ℓ i ^ 2 ≤ p i := by nlinarith [hp0 i, sq_nonneg (ℓ i)]
    exact mul_le_mul_of_nonneg_right this hq
  have h2 : p i * (t / (t + γ) ^ 2) ≤ (t + 1 / N) * (t / (t + γ) ^ 2) :=
    mul_le_mul_of_nonneg_right (p_le_pt_add hN hp0 hp1 i) hq
  have h3 : t * (t / (t + γ) ^ 2) ≤ 1 := by
    rw [mul_div_assoc', div_le_one (by positivity)]; nlinarith
  have h4 : 1 / N * (t / (t + γ) ^ 2) ≤ 1 / (4 * N * γ) := by
    have : t / (t + γ) ^ 2 ≤ 1 / (4 * γ) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [sq_nonneg (t - γ)]
    calc 1 / N * (t / (t + γ) ^ 2) ≤ 1 / N * (1 / (4 * γ)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / (4 * N * γ) := by field_simp
  nlinarith

/-- **3. Second moment** with rounded denominators: `Σ p_i ℓ_i² pt_i/(pt_i + γ)² ≤ |α|·(1 + 1/(4Nγ))`. -/
theorem second_moment_le (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (ℓ : α → ℝ)
    (hl0 : ∀ i, 0 ≤ ℓ i) (hl1 : ∀ i, ℓ i ≤ 1) {γ : ℝ} (hγ : 0 < γ) :
    ∑ i, p i * ℓ i ^ 2 * (pt N b p i / (pt N b p i + γ) ^ 2) ≤ Fintype.card α * (1 + 1 / (4 * N * γ)) := by
  calc ∑ i, p i * ℓ i ^ 2 * (pt N b p i / (pt N b p i + γ) ^ 2) ≤ ∑ _i : α, (1 + 1 / (4 * N * γ)) :=
        Finset.sum_le_sum fun i _ => sm_term_le hN hp0 hp1 ℓ hl0 hl1 hγ i
    _ = Fintype.card α * (1 + 1 / (4 * N * γ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-! ### Support versions (only elements with `p i ≠ 0` are charged) -/

/-- Off `b`, an element with `p i = 0` has rounded mass `0`. -/
lemma pt_eq_zero_of_ne (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) {i : α} (hi : i ≠ b) (h : p i = 0) :
    pt N b p i = 0 :=
  le_antisymm (h ▸ (pt_le_of_ne hN hp0 hi).1) (pt_nonneg i)

omit [DecidableEq α] in
/-- A sum of terms bounded by `C` that vanish where `p i = 0` is at most `#{i | p i ≠ 0}·C`. -/
lemma sum_le_supp (f : α → ℝ) {C : ℝ} (hf : ∀ i, f i ≤ C) (hz : ∀ i, p i = 0 → f i = 0) :
    ∑ i, f i ≤ (univ.filter fun i => p i ≠ 0).card * C := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => p i ≠ 0)]
  have h0 : ∑ i ∈ univ.filter (fun i => ¬ p i ≠ 0), f i = 0 :=
    Finset.sum_eq_zero fun i hi => hz i (by simpa using (Finset.mem_filter.mp hi).2)
  rw [h0, add_zero]
  calc ∑ i ∈ univ.filter (fun i => p i ≠ 0), f i ≤ ∑ _i ∈ univ.filter (fun i => p i ≠ 0), C :=
        Finset.sum_le_sum fun i _ => hf i
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The missing mass at `b` is at most `#{i ≠ b | p i ≠ 0}/N`. -/
lemma pt_b_le_supp (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    pt N b p b - p b ≤ ((univ.erase b).filter (fun i => p i ≠ 0)).card / N := by
  rw [(pt_b_bounds hN hp0 hp1 (b := b)).1, ← Finset.sum_filter_add_sum_filter_not (univ.erase b)
    (fun i => p i ≠ 0)]
  have h0 : ∑ i ∈ (univ.erase b).filter (fun i => ¬ p i ≠ 0), (p i - pt N b p i) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      obtain ⟨hi1, hi2⟩ := Finset.mem_filter.mp hi
      have hpz : p i = 0 := by simpa using hi2
      rw [hpz, pt_eq_zero_of_ne hN hp0 (Finset.ne_of_mem_erase hi1) hpz, sub_zero]
  rw [h0, add_zero]
  calc ∑ i ∈ (univ.erase b).filter (fun i => p i ≠ 0), (p i - pt N b p i)
        ≤ ∑ _i ∈ (univ.erase b).filter (fun i => p i ≠ 0), (1 / N : ℝ) :=
          Finset.sum_le_sum fun i hi => by
            have := (pt_le_of_ne hN hp0 (Finset.ne_of_mem_erase (Finset.mem_filter.mp hi).1)).2
            linarith
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **1′. Played loss, support version**: `|⟨pt − p, ℓ⟩| ≤ #{i ≠ b | p i ≠ 0}/N`. -/
theorem played_loss_le_supp (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (ℓ : α → ℝ)
    (hl0 : ∀ i, 0 ≤ ℓ i) (hl1 : ∀ i, ℓ i ≤ 1) :
    |∑ i, pt N b p i * ℓ i - ∑ i, p i * ℓ i| ≤ ((univ.erase b).filter (fun i => p i ≠ 0)).card / N := by
  obtain ⟨heq, hnn, -⟩ := pt_b_bounds hN hp0 hp1 (b := b)
  have hle := pt_b_le_supp hN hp0 hp1 (b := b)
  have hsplit : ∑ i, pt N b p i * ℓ i - ∑ i, p i * ℓ i =
      (pt N b p b - p b) * ℓ b - ∑ i ∈ univ.erase b, (p i - pt N b p i) * ℓ i := by
    rw [← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
    have : ∑ i ∈ univ.erase b, (pt N b p i * ℓ i - p i * ℓ i) =
        -∑ i ∈ univ.erase b, (p i - pt N b p i) * ℓ i := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]; ring
  have hA : 0 ≤ ∑ i ∈ univ.erase b, (p i - pt N b p i) * ℓ i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (by
      have := (pt_le_of_ne hN hp0 (Finset.ne_of_mem_erase hi)).1; linarith) (hl0 i)
  have hB : ∑ i ∈ univ.erase b, (p i - pt N b p i) * ℓ i ≤ pt N b p b - p b := by
    rw [heq]
    exact Finset.sum_le_sum fun i hi => by
      have := (pt_le_of_ne hN hp0 (Finset.ne_of_mem_erase hi)).1
      nlinarith [hl1 i, hl0 i]
  have hC : 0 ≤ (pt N b p b - p b) * ℓ b := mul_nonneg hnn (hl0 b)
  have hD : (pt N b p b - p b) * ℓ b ≤ pt N b p b - p b := by nlinarith [hl1 b]
  rw [hsplit, abs_le]
  constructor <;> linarith

/-! ### Scaled observation probability `ρ·pt_i` (Design Z: the draw happens only on exploitation rounds) -/

/-- **2″. IX bias, scaled and on the support**: for `0 < ρ`,
`Σ p_i ℓ_i γ/(ρ·pt_i + γ) ≤ #{i | p i ≠ 0}·(γ/ρ + 1/N)`. With `ρ = 1` this is the support version of term 2. -/
theorem ix_bias_le_scaled (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (ℓ : α → ℝ)
    (hl0 : ∀ i, 0 ≤ ℓ i) (hl1 : ∀ i, ℓ i ≤ 1) {γ ρ : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) :
    ∑ i, p i * ℓ i * (γ / (ρ * pt N b p i + γ)) ≤
      (univ.filter fun i => p i ≠ 0).card * (γ / ρ + 1 / N) := by
  have hγρ : 0 < γ / ρ := div_pos hγ hρ
  have hterm : ∀ i, p i * ℓ i * (γ / (ρ * pt N b p i + γ)) ≤ γ / ρ + 1 / N := by
    intro i
    have hpt := pt_nonneg (N := N) (b := b) (p := p) i
    have e : γ / (ρ * pt N b p i + γ) = (γ / ρ) / (pt N b p i + γ / ρ) := by
      field_simp
    rw [e]
    have hden : 0 < pt N b p i + γ / ρ := by linarith
    have h1 : p i * ℓ i ≤ p i := by nlinarith [hp0 i, hl1 i]
    have h3 : p i ≤ pt N b p i + 1 / N := p_le_pt_add hN hp0 hp1 i
    have hq : 0 ≤ (γ / ρ) / (pt N b p i + γ / ρ) := by positivity
    have e1 : pt N b p i * ((γ / ρ) / (pt N b p i + γ / ρ)) ≤ γ / ρ := by
      rw [mul_div_assoc', div_le_iff₀ hden]; nlinarith
    have e2 : 1 / N * ((γ / ρ) / (pt N b p i + γ / ρ)) ≤ 1 / N := by
      have : (γ / ρ) / (pt N b p i + γ / ρ) ≤ 1 := by rw [div_le_one hden]; linarith
      have : (0 : ℝ) ≤ 1 / N := by positivity
      nlinarith
    calc p i * ℓ i * ((γ / ρ) / (pt N b p i + γ / ρ)) ≤ p i * ((γ / ρ) / (pt N b p i + γ / ρ)) :=
          mul_le_mul_of_nonneg_right h1 hq
      _ ≤ (pt N b p i + 1 / N) * ((γ / ρ) / (pt N b p i + γ / ρ)) := mul_le_mul_of_nonneg_right h3 hq
      _ ≤ γ / ρ + 1 / N := by rw [add_mul]; linarith
  exact sum_le_supp _ hterm (fun i h => by rw [h]; ring)

/-- **3″. Second moment, scaled and on the support**: for `0 < ρ`, the second moment of IX estimates
`ℓ_i·1[obs i]/(ρ·pt_i + γ)` with `P(obs i) = ρ·pt_i`, weighted by `p`, is
`Σ p_i ℓ_i² ρ·pt_i/(ρ·pt_i + γ)² ≤ #{i | p i ≠ 0}·(1/ρ + 1/(4Nγ))`. -/
theorem second_moment_le_scaled (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (ℓ : α → ℝ)
    (hl0 : ∀ i, 0 ≤ ℓ i) (hl1 : ∀ i, ℓ i ≤ 1) {γ ρ : ℝ} (hγ : 0 < γ) (hρ : 0 < ρ) :
    ∑ i, p i * ℓ i ^ 2 * (ρ * pt N b p i / (ρ * pt N b p i + γ) ^ 2) ≤
      (univ.filter fun i => p i ≠ 0).card * (1 / ρ + 1 / (4 * N * γ)) := by
  have hγρ : 0 < γ / ρ := div_pos hγ hρ
  have hterm : ∀ i, p i * ℓ i ^ 2 * (ρ * pt N b p i / (ρ * pt N b p i + γ) ^ 2) ≤
      1 / ρ + 1 / (4 * N * γ) := by
    intro i
    have hpt := pt_nonneg (N := N) (b := b) (p := p) i
    have e : ρ * pt N b p i / (ρ * pt N b p i + γ) ^ 2 =
        (1 / ρ) * (pt N b p i / (pt N b p i + γ / ρ) ^ 2) := by
      have : 0 < pt N b p i + γ / ρ := by linarith
      field_simp
    have h := sm_term_le hN hp0 hp1 (b := b) ℓ hl0 hl1 hγρ i
    have e2 : 1 / (4 * N * (γ / ρ)) = ρ * (1 / (4 * N * γ)) := by field_simp
    rw [e2] at h
    rw [e, show p i * ℓ i ^ 2 * (1 / ρ * (pt N b p i / (pt N b p i + γ / ρ) ^ 2)) =
      (1 / ρ) * (p i * ℓ i ^ 2 * (pt N b p i / (pt N b p i + γ / ρ) ^ 2)) by ring]
    have hr : 0 ≤ 1 / ρ := by positivity
    calc (1 / ρ) * (p i * ℓ i ^ 2 * (pt N b p i / (pt N b p i + γ / ρ) ^ 2))
        ≤ (1 / ρ) * (1 + ρ * (1 / (4 * N * γ))) := mul_le_mul_of_nonneg_left h hr
      _ = 1 / ρ + 1 / (4 * N * γ) := by field_simp
  exact sum_le_supp _ hterm (fun i h => by rw [h]; ring)

section Draw

/-- **Coin realization.** A deterministic map from a uniform coin on `Fin N` to `α` whose fibres have exactly
`cnt i` elements. -/
noncomputable def draw (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) : Fin N → α :=
  fun k => ((Fintype.equivOfCardEq (by
    rw [Fintype.card_sigma, Fintype.card_fin]
    simp only [Fintype.card_fin]
    exact (sum_cnt hp0 hp1).symm) : Fin N ≃ Σ i : α, Fin (cnt N b p i)) k).1

theorem card_draw_fiber (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (i : α) :
    (univ.filter fun k : Fin N => draw (N := N) (b := b) hp0 hp1 k = i).card = cnt N b p i := by
  classical
  unfold draw
  set e : Fin N ≃ Σ i : α, Fin (cnt N b p i) := Fintype.equivOfCardEq _
  have : (univ.filter fun k : Fin N => (e k).1 = i) = (univ.filter fun s : (Σ i : α, Fin (cnt N b p i)) => s.1 = i).map
      e.symm.toEmbedding := by
    ext k; simp
  rw [this, Finset.card_map]
  have h2 : (univ.filter fun s : (Σ i : α, Fin (cnt N b p i)) => s.1 = i) =
      (univ : Finset (Fin (cnt N b p i))).map ⟨fun x => (⟨i, x⟩ : Σ i : α, Fin (cnt N b p i)), fun x y h => by
        simpa using h⟩ := by
    ext ⟨j, x⟩
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro rfl; exact ⟨x, rfl⟩
    · rintro ⟨y, h⟩; exact (Sigma.mk.inj_iff.1 h).1.symm
  rw [h2, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Under the uniform coin, the drawn element has law `pt`. -/
theorem prob_draw (hN : 0 < N) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) (i : α) :
    ((univ.filter fun k : Fin N => draw (N := N) (b := b) hp0 hp1 k = i).card : ℝ) / N = pt N b p i := by
  rw [card_draw_fiber]; rfl

end Draw

end Pool.P0179
