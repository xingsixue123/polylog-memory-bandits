import Pool.P0154.Credit

open Finset Pool.P0154

namespace Pool.P0162

/-- AM–GM: `c·√ℓ ≤ c·λ + c·ℓ/(4λ)` for `λ > 0`, `c ≥ 0`, `ℓ ≥ 0`. -/
lemma sqrt_le_amgm (c lam : ℝ) (hc : 0 ≤ c) (hlam0 : 0 < lam) (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    c * Real.sqrt ℓ ≤ c * lam + c / (4 * lam) * ℓ := by
  have hs := Real.sq_sqrt hℓ
  have key : Real.sqrt ℓ ≤ lam + ℓ / (4 * lam) := by
    have h4 : 0 < 4 * lam := by positivity
    have : lam + ℓ / (4 * lam) = (4 * lam ^ 2 + ℓ) / (4 * lam) := by field_simp
    rw [this, le_div_iff₀ h4]
    nlinarith [sq_nonneg (Real.sqrt ℓ - 2 * lam)]
  have : c / (4 * lam) * ℓ = c * (ℓ / (4 * lam)) := by ring
  rw [this, ← mul_add]
  exact mul_le_mul_of_nonneg_left key hc

lemma isum_add_const (v : ℕ → ℝ) (κ : ℝ) (a b : ℕ) (hab : a ≤ b) :
    isum (fun u => v u + κ) a b = isum v a b + κ * ((b : ℝ) - a) := by
  unfold isum
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hab]
  ring

variable {ι : Type*} (W : Finset ι) (s e : ι → ℕ)

/-- `windows` with an extra width term `c·√(b−a)` in the interval guarantee, for any `λ > 0`. -/
theorem windows_sqrt_lam (f v : ℕ → ℝ) (ρ₀ S c lam : ℝ) (T : ℕ) (hv : ∀ u, 0 ≤ v u)
    (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (hlam0 : 0 < lam)
    (hint : ∀ a b, a ≤ b → b ≤ T →
      -isum f a b ≤ ρ₀ + isum v a b + c * Real.sqrt ((b : ℝ) - a))
    (he : ∀ i ∈ W, e i ≤ T) (hmult : ∀ u, (mult W s e u : ℝ) ≤ S) :
    ∑ i ∈ W, isum f (s i) (e i)
      ≤ S * isum f 0 T + S * (ρ₀ + c * lam) * (2 * W.card + 1)
        + S * (isum v 0 T + c / (4 * lam) * T) := by
  have hκ : 0 ≤ c / (4 * lam) := by positivity
  have hint' : ∀ a b, a ≤ b → b ≤ T →
      -isum f a b ≤ (ρ₀ + c * lam) + isum (fun u => v u + c / (4 * lam)) a b := by
    intro a b hab hbT
    rw [isum_add_const v _ a b hab]
    have h1 := hint a b hab hbT
    have hba : (0 : ℝ) ≤ (b : ℝ) - a := by
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      linarith
    have h2 := sqrt_le_amgm c lam hc hlam0 _ hba
    linarith
  have hw := windows W s e f (fun u => v u + c / (4 * lam)) (ρ₀ + c * lam) S T
    (fun u => add_nonneg (hv u) hκ) (by positivity) hint' he hmult
  rw [isum_add_const v _ 0 T (Nat.zero_le T)] at hw
  simpa using hw

/-- Optimized width: with `λ = √T / (2√(2N+1))` the width part is `S·c·√T·√(2N+1)`. -/
theorem windows_sqrt (f v : ℕ → ℝ) (ρ₀ S c : ℝ) (T : ℕ) (hT : 1 ≤ T) (hv : ∀ u, 0 ≤ v u)
    (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (hS0 : 0 ≤ S)
    (hint : ∀ a b, a ≤ b → b ≤ T →
      -isum f a b ≤ ρ₀ + isum v a b + c * Real.sqrt ((b : ℝ) - a))
    (he : ∀ i ∈ W, e i ≤ T) (hmult : ∀ u, (mult W s e u : ℝ) ≤ S) :
    ∑ i ∈ W, isum f (s i) (e i)
      ≤ S * isum f 0 T + S * ρ₀ * (2 * W.card + 1) + S * isum v 0 T
        + S * c * (Real.sqrt T * Real.sqrt (2 * W.card + 1)) := by
  set m : ℝ := 2 * W.card + 1 with hm
  have hm0 : 0 < m := by positivity
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hsT := Real.sqrt_pos.mpr hT0
  have hsm := Real.sqrt_pos.mpr hm0
  set lam := Real.sqrt T / (2 * Real.sqrt m) with hlam
  have hlam0 : 0 < lam := by positivity
  have hw := windows_sqrt_lam W s e f v ρ₀ S c lam T hv hρ₀ hc hlam0 hint he hmult
  have hTT : Real.sqrt (T : ℝ) * Real.sqrt T = T := Real.mul_self_sqrt hT0.le
  have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
  have hid : c * lam * m + c / (4 * lam) * T = c * (Real.sqrt T * Real.sqrt m) := by
    rw [hlam]
    field_simp
    rw [Real.sq_sqrt hT0.le, Real.sq_sqrt hm0.le]
    ring
  have : S * (ρ₀ + c * lam) * m + S * (isum v 0 T + c / (4 * lam) * T)
      = S * ρ₀ * m + S * isum v 0 T + S * (c * lam * m + c / (4 * lam) * T) := by ring
  rw [hid] at this
  linarith

/-- `jump_cost` with the extra width term `c·√(b−a)` (optimized `λ`, `T ≥ 1`). -/
theorem jump_cost_sqrt (f v : ℕ → ℝ) (ρ₀ S c xbar : ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (hS0 : 0 ≤ S)
    (hint : ∀ a b, a ≤ b → b ≤ T →
      -isum f a b ≤ ρ₀ + isum v a b + c * Real.sqrt ((b : ℝ) - a))
    (he : ∀ i ∈ W, e i ≤ T) (hmult : ∀ u, (mult W s e u : ℝ) ≤ S) (hxbar : 0 ≤ xbar)
    (Δ lead r : ι → ℝ) (hΔ : ∀ i ∈ W, 0 ≤ Δ i ∧ Δ i ≤ xbar)
    (hlead : ∀ i ∈ W, lead i ≤ isum f (s i) (e i) + r i) :
    ∑ i ∈ W, Δ i * max 0 (lead i)
      ≤ xbar * (S * isum f 0 T + S * ρ₀ * (2 * W.card + 1) + S * isum v 0 T
          + S * c * (Real.sqrt T * Real.sqrt (2 * W.card + 1)) + ∑ i ∈ W, max 0 (r i)) := by
  classical
  set Wp := W.filter (fun i => 0 < lead i) with hWp
  have hstep1 : ∑ i ∈ W, Δ i * max 0 (lead i) ≤ xbar * ∑ i ∈ Wp, lead i := by
    rw [Finset.mul_sum, hWp, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨h0, h1⟩ := hΔ i hi
    by_cases hp : 0 < lead i
    · rw [if_pos hp, max_eq_right hp.le]
      exact mul_le_mul_of_nonneg_right h1 hp.le
    · rw [if_neg hp, max_eq_left (not_lt.mp hp), mul_zero]
  have hmultp : ∀ u, (mult Wp s e u : ℝ) ≤ S := by
    intro u
    have : mult Wp s e u ≤ mult W s e u := by
      unfold mult
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨(Finset.mem_filter.mp hi.1).1, hi.2⟩
    exact le_trans (by exact_mod_cast this) (hmult u)
  have hep : ∀ i ∈ Wp, e i ≤ T := fun i hi => he i (Finset.mem_filter.mp hi).1
  have hw := windows_sqrt Wp s e f v ρ₀ S c T hT hv hρ₀ hc hS0 hint hep hmultp
  have hleadp : ∑ i ∈ Wp, lead i ≤ ∑ i ∈ Wp, (isum f (s i) (e i) + max 0 (r i)) :=
    Finset.sum_le_sum (fun i hi =>
      le_trans (hlead i (Finset.mem_filter.mp hi).1) (by linarith [le_max_right 0 (r i)]))
  rw [Finset.sum_add_distrib] at hleadp
  have hcard : (Wp.card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_filter_le W _
  have hr : ∑ i ∈ Wp, max 0 (r i) ≤ ∑ i ∈ W, max 0 (r i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ W)
      (fun i _ _ => le_max_left 0 (r i))
  have hSρ : S * ρ₀ * (2 * Wp.card + 1) ≤ S * ρ₀ * (2 * W.card + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hS0 hρ₀)
  have hsq : Real.sqrt (2 * Wp.card + 1) ≤ Real.sqrt (2 * W.card + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsq' : S * c * (Real.sqrt T * Real.sqrt (2 * Wp.card + 1))
      ≤ S * c * (Real.sqrt T * Real.sqrt (2 * W.card + 1)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _))
      (mul_nonneg hS0 hc)
  have hbound : ∑ i ∈ Wp, lead i ≤ S * isum f 0 T + S * ρ₀ * (2 * W.card + 1) + S * isum v 0 T
      + S * c * (Real.sqrt T * Real.sqrt (2 * W.card + 1)) + ∑ i ∈ W, max 0 (r i) := by
    linarith
  exact le_trans hstep1 (mul_le_mul_of_nonneg_left hbound hxbar)

/-- Grouping by destination thread: summing `jump_cost_sqrt` over a finite set of threads `Θ`, each
with its own jump events `Wj j` (multiplicity ≤ S), cap `xj j` and slacks, gives the coefficient
`S·Σ_j xj j` on `F[0,T) = Reg_BASE − Reg_ALG`. -/
theorem jump_cost_threads {κ : Type*} (Θ : Finset κ) (Wj : κ → Finset ι) (f v : ℕ → ℝ)
    (ρ₀ S c : ℝ) (xj : κ → ℝ) (T : ℕ) (hT : 1 ≤ T)
    (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (hS0 : 0 ≤ S)
    (hint : ∀ a b, a ≤ b → b ≤ T →
      -isum f a b ≤ ρ₀ + isum v a b + c * Real.sqrt ((b : ℝ) - a))
    (he : ∀ j ∈ Θ, ∀ i ∈ Wj j, e i ≤ T) (hmult : ∀ j ∈ Θ, ∀ u, (mult (Wj j) s e u : ℝ) ≤ S)
    (hx : ∀ j ∈ Θ, 0 ≤ xj j)
    (Δ lead r : ι → ℝ) (hΔ : ∀ j ∈ Θ, ∀ i ∈ Wj j, 0 ≤ Δ i ∧ Δ i ≤ xj j)
    (hlead : ∀ j ∈ Θ, ∀ i ∈ Wj j, lead i ≤ isum f (s i) (e i) + r i) :
    ∑ j ∈ Θ, ∑ i ∈ Wj j, Δ i * max 0 (lead i)
      ≤ (S * ∑ j ∈ Θ, xj j) * isum f 0 T
        + ∑ j ∈ Θ, xj j * (S * ρ₀ * (2 * (Wj j).card + 1) + S * isum v 0 T
          + S * c * (Real.sqrt T * Real.sqrt (2 * (Wj j).card + 1)) + ∑ i ∈ Wj j, max 0 (r i)) := by
  have h := Finset.sum_le_sum (fun j hj => jump_cost_sqrt (Wj j) s e f v ρ₀ S c (xj j) T hT hv
    hρ₀ hc hS0 hint (he j hj) (hmult j hj) (hx j hj) Δ lead r (hΔ j hj) (hlead j hj))
  refine le_trans h (le_of_eq ?_)
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Non-vacuity: the interval hypothesis with a width term holds when `f ≥ 0`. -/
example (T : ℕ) : ∀ a b, a ≤ b → b ≤ T →
    -isum (fun _ => (1 : ℝ)) a b ≤ 0 + isum (fun _ => (0 : ℝ)) a b + 1 * Real.sqrt ((b : ℝ) - a) := by
  intro a b _ _
  have h1 : (0 : ℝ) ≤ isum (fun _ => (1 : ℝ)) a b := Finset.sum_nonneg (fun _ _ => zero_le_one)
  have h2 := Real.sqrt_nonneg ((b : ℝ) - a)
  have h3 : isum (fun _ => (0 : ℝ)) a b = 0 := by simp [isum]
  linarith

/-- The width term is genuinely used: for `f = −1` on `[0,4)` (ALG worse than BASE by 1 per round),
the affine hypothesis with `ρ₀ = 0`, `v = 0` fails on `[0,4)`, while the width form holds with `c = 2`. -/
example : ¬ (-isum (fun _ => (-1 : ℝ)) 0 4 ≤ 0 + isum (fun _ => (0 : ℝ)) 0 4) ∧
    -isum (fun _ => (-1 : ℝ)) 0 4 ≤ 0 + isum (fun _ => (0 : ℝ)) 0 4 + 2 * Real.sqrt ((4 : ℝ) - 0) := by
  have h4 : Real.sqrt ((4 : ℝ) - 0) = 2 := by
    rw [sub_zero, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨?_, ?_⟩
  · simp [isum]
  · rw [h4]; simp [isum]; norm_num

/-- Positive control: `jump_cost_sqrt` applied to a nonempty window set with a positive lead.
One window `[0,1)`, `f ≡ 1`, `lead = 1 = F[0,1) + 0`, jump `Δ = 1 ≤ x̄ = 1`, multiplicity `≤ 1`,
`ρ₀ = c = 0`, `v ≡ 0`, `T = 1`: the theorem gives `1 ≤ 1·(1·F[0,1) + …) = 1`. -/
example : ∑ i ∈ (Finset.univ : Finset (Fin 1)), (fun _ => (1 : ℝ)) i * max 0 ((fun _ => (1 : ℝ)) i)
    ≤ 1 * (1 * isum (fun _ => (1 : ℝ)) 0 1 + 1 * 0 * (2 * (Finset.univ : Finset (Fin 1)).card + 1)
      + 1 * isum (fun _ => (0 : ℝ)) 0 1
      + 1 * 0 * (Real.sqrt (1 : ℕ) * Real.sqrt (2 * (Finset.univ : Finset (Fin 1)).card + 1))
      + ∑ i ∈ (Finset.univ : Finset (Fin 1)), max 0 ((fun _ => (0 : ℝ)) i)) := by
  refine jump_cost_sqrt (Finset.univ : Finset (Fin 1)) (fun _ => 0) (fun _ => 1)
    (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ)) 0 1 0 1 1 le_rfl (fun _ => le_rfl) le_rfl le_rfl
    zero_le_one ?_ ?_ ?_ zero_le_one (fun _ => 1) (fun _ => 1) (fun _ => 0) ?_ ?_
  · intro a b hab _
    have h1 : (0 : ℝ) ≤ isum (fun _ => (1 : ℝ)) a b := Finset.sum_nonneg (fun _ _ => zero_le_one)
    have h3 : isum (fun _ => (0 : ℝ)) a b = 0 := by simp [isum]
    linarith
  · intro i _; exact le_rfl
  · intro u
    have : mult (Finset.univ : Finset (Fin 1)) (fun _ => 0) (fun _ => 1) u ≤ 1 := by
      unfold mult
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    exact_mod_cast this
  · intro i _; exact ⟨zero_le_one, le_rfl⟩
  · intro i _; simp [isum]

end Pool.P0162
