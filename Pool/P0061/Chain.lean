import Pool.P0030.MergeCore
import Pool.P0041.Bench
import Pool.P0009.Hedge
import Pool.P0049.Walk

/-!
# Good-interval certificates, deterministic part: chain cover + per-epoch learner ⇒ interval cost

* `sum_le_pieceSum`: if a learner's epoch loss `A u` is within `R` of the epoch loss `c u f` of
  every member `f` of a P0030 chain on every epoch from `f`'s entry up to `t`, then the learner's loss on `[a, t)`
  is at most the chain's piecewise loss `pieceSum` plus `(t - a) R`.
* `hedgeLoss_le`: Hedge (P0009) with the uniform prior over a fixed pool, losses in `[0,1]`, is within
  `log |P| / η + η B / 2` of every pool member over `B` rounds (the per-epoch learner of a K-query pool baseline).
* `sum_le_oneLevel`: P0049's one-level walk (`D = 0`, unit epochs) with **linear** good-interval costs
  `θ + R (e - a)` (instead of P0049's `α √(e-a) + β` form): total `≤ (θ + R) T + c · #bad`
  (`θ` is charged once per epoch, not once per good interval).
-/

open Finset

namespace Pool.P0061

variable {ι : Type*} [LinearOrder ι] (E : ι → ℕ) (c : ℕ → ι → ℝ) (A : ℕ → ℝ) (R : ℝ) (t : ℕ)

/-- Cumulative loss before epoch `e`. -/
def cumL (i : ι) (e : ℕ) : ℝ := ∑ u ∈ range e, c u i

omit [LinearOrder ι] in
theorem Lint_cumL (i : ι) {a b : ℕ} (hab : a ≤ b) :
    Pool.P0030.Lint (cumL c) i a b = ∑ u ∈ Ico a b, c u i := by
  unfold Pool.P0030.Lint cumL
  rw [← sum_range_add_sum_Ico _ hab]; ring

/-- If the learner is within `R` of every chain member on every epoch where that member is present
(from its entry epoch up to `t`), the learner's loss on `[a, t)` is at most the chain's piecewise loss
plus `(t - a) R`. -/
theorem sum_le_pieceSum (ch : List ι) (a : ℕ) (hok : Pool.P0030.ChainOK E t ch a)
    (hpres : ∀ f ∈ ch, ∀ u, E f ≤ u → u < t → A u ≤ c u f + R) :
    ∑ u ∈ Ico a t, A u ≤ Pool.P0030.pieceSum E (cumL c) t ch a + ((t - a : ℕ) : ℝ) * R := by
  induction ch generalizing a with
  | nil => exact hok.elim
  | cons f rest ih =>
    cases rest with
    | nil =>
      obtain ⟨hfa, hat⟩ := hok
      simp only [Pool.P0030.pieceSum]
      rw [Lint_cumL c f hat]
      have : ∑ u ∈ Ico a t, A u ≤ ∑ u ∈ Ico a t, (c u f + R) := by
        apply sum_le_sum; intro u hu; rw [mem_Ico] at hu
        exact hpres f (by simp) u (by omega) hu.2
      rw [sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul] at this
      linarith
    | cons g rest' =>
      obtain ⟨hfa, hag, hok'⟩ := hok
      have hgt : E g ≤ t := Pool.P0041.chain_le_t E t (g :: rest') (E g) hok'
      have ih' := ih (E g) hok' (fun f' hf' => hpres f' (List.mem_cons_of_mem _ hf'))
      simp only [Pool.P0030.pieceSum]
      rw [Lint_cumL c f hag, ← sum_Ico_consecutive _ hag hgt]
      have h1 : ∑ u ∈ Ico a (E g), A u ≤ ∑ u ∈ Ico a (E g), (c u f + R) := by
        apply sum_le_sum; intro u hu; rw [mem_Ico] at hu
        exact hpres f (by simp) u (by omega) (by omega)
      rw [sum_add_distrib, sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
      have hcast : ((t - a : ℕ) : ℝ) = ((E g - a : ℕ) : ℝ) + ((t - E g : ℕ) : ℝ) := by
        rw [← Nat.cast_add]; congr 1; omega
      rw [hcast]
      nlinarith [ih']


/-- Expected loss of Hedge (uniform prior over the pool `P`, rate `η`) run for `B` rounds on losses `x r j`. -/
noncomputable def hedgeLoss (P : Finset ι) (η : ℝ) (B : ℕ) (x : ℕ → ι → ℝ) : ℝ :=
  ∑ r ∈ range B, ∑ j : P, Pool.P0009.prob (fun _ => (1 : ℝ)) η (fun r (j : P) => x r j.1) r j * x r j.1

omit [LinearOrder ι] in
/-- Hedge over a fixed pool, losses in `[0,1]`: within `log |P| / η + η B / 2` of every pool member. -/
theorem hedgeLoss_le (P : Finset ι) {η : ℝ} (hη : 0 < η) (B : ℕ) (x : ℕ → ι → ℝ)
    (hx0 : ∀ r j, 0 ≤ x r j) (hx1 : ∀ r j, x r j ≤ 1) {f : ι} (hf : f ∈ P) :
    hedgeLoss P η B x ≤ ∑ r ∈ range B, x r f + Real.log P.card / η + η / 2 * B := by
  have : Nonempty P := ⟨⟨f, hf⟩⟩
  have h := Pool.P0009.hedge_regret_uniform (ι := P) hη (fun r (j : P) => x r j.1)
    (fun r j => hx0 r j.1) B ⟨f, hf⟩
  have hsq : ∑ r ∈ range B, ∑ j : P, Pool.P0009.prob (fun _ => (1 : ℝ)) η
      (fun r (j : P) => x r j.1) r j * x r j.1 ^ 2 ≤ B := by
    have : ∀ r ∈ range B, ∑ j : P, Pool.P0009.prob (fun _ => (1 : ℝ)) η
        (fun r (j : P) => x r j.1) r j * x r j.1 ^ 2 ≤ 1 := by
      intro r _
      calc _ ≤ ∑ j : P, Pool.P0009.prob (fun _ => (1 : ℝ)) η (fun r (j : P) => x r j.1) r j := by
            apply sum_le_sum; intro j _
            have hp := Pool.P0009.prob_nonneg (ι := P) (q := fun _ => (1 : ℝ)) (η := η)
              (fun _ => one_pos) (fun r (j : P) => x r j.1) r j
            have : x r j.1 ^ 2 ≤ 1 := by nlinarith [hx0 r j.1, hx1 r j.1]
            nlinarith
        _ = 1 := Pool.P0009.sum_prob (ι := P) (q := fun _ => (1 : ℝ)) (η := η) (fun _ => one_pos) _ r
    calc _ ≤ ∑ r ∈ range B, (1 : ℝ) := sum_le_sum this
      _ = B := by simp
  have hcard : (Fintype.card P : ℝ) = P.card := by simp
  unfold hedgeLoss
  rw [hcard] at h
  unfold Pool.P0009.cum at h
  nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : (0:ℝ) ≤ η / 2)]


section OneLevel

open Pool.P0049

/-- One-level walk with linear good-interval costs: if each good interval `[a, e)` costs at most
`θ + R (e - a)` and each bad epoch at most `c ≥ 0`, the total is at most `(θ + R) T + c · #bad`.
Note: the margin `θ` is charged once per EPOCH here (the proof uses `θ ≤ θ (e - a)`), not once per good
interval; the bound `θ · #(good intervals) + R T + c · #bad` is not what is stated. With a constant `θ`
this is the worst case anyway; if `θ` grows with the interval length this form is lossy. -/
theorem sum_le_oneLevel {T : ℕ} {ev : ℕ → ℕ → Option ℕ} (h : Hyp 0 (fun _ => 1) T ev)
    (r : ℕ → ℝ) {θ R c : ℝ} (hθ : 0 ≤ θ) (hR : 0 ≤ R) (hc : 0 ≤ c)
    (hgood : ∀ a e, a < T → ev 0 a = some e → ∑ u ∈ Ico a e, r u ≤ θ + R * ((e - a : ℕ) : ℝ))
    (hbad : ∀ a, a < T → ev 0 a = none → r a ≤ c) :
    ∑ u ∈ range T, r u ≤ (θ + R) * T + c * ((range T).filter (fun a => ev 0 a = none)).card := by
  have hw := sum_Ico_eq_walk h r 0 0 le_rfl (dvd_zero _)
  have h1 := sum_Ico_eq_walk h (fun _ => (1 : ℝ)) 0 0 le_rfl (dvd_zero _)
  have hv := valid_of_mem h 0 0 le_rfl (dvd_zero _)
  have hnb := nb_le_card h 0
  simp only [Nat.one_dvd, true_and] at hnb
  have key : ∀ x ∈ walk 0 (fun _ => 1) T ev 0 0,
      cov 0 (fun _ => 1) r x ≤ (θ + R) * cov 0 (fun _ => 1) (fun _ => (1 : ℝ)) x + c * (nb 0 x : ℝ) := by
    intro x hx
    have hvx := hv x hx
    cases x with
    | good a e k =>
      obtain ⟨hk, -, haT, hev, hae⟩ := hvx
      have hk0 : k = 0 := by omega
      subst hk0
      simp only [cov, nb, sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, CharP.cast_eq_zero, mul_zero,
        add_zero]
      have := hgood a e haT hev
      have hlen : (1 : ℝ) ≤ ((e - a : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ e - a)
      nlinarith
    | bad a k =>
      obtain ⟨hk, -, haT, hev⟩ := hvx
      have hk0 : k = 0 := by omega
      subst hk0
      simp only [cov, nb, ite_true, sum_const, nsmul_eq_mul, mul_one, Nat.cast_one,
        zero_add, Nat.add_sub_cancel_left, Finset.Ico_add_one_right_eq_Icc, Icc_self, sum_singleton]
      have := hbad a haT hev
      nlinarith
  have hw' : ∑ u ∈ range T, r u = ((walk 0 (fun _ => 1) T ev 0 0).map (cov 0 (fun _ => 1) r)).sum := by
    rw [range_eq_Ico]; exact hw
  rw [hw']
  calc ((walk 0 (fun _ => 1) T ev 0 0).map (cov 0 (fun _ => 1) r)).sum
      ≤ ((walk 0 (fun _ => 1) T ev 0 0).map (fun x => (θ + R) * cov 0 (fun _ => 1) (fun _ => (1 : ℝ)) x
          + c * (nb 0 x : ℝ))).sum := List.sum_le_sum (fun x hx => key x hx)
    _ = (θ + R) * ((walk 0 (fun _ => 1) T ev 0 0).map (cov 0 (fun _ => 1) (fun _ => (1 : ℝ)))).sum
          + c * (((walk 0 (fun _ => 1) T ev 0 0).map (nb 0)).sum : ℕ) := by
        rw [List.sum_map_add, List.sum_map_mul_left, List.sum_map_mul_left]
        rw [Nat.cast_list_sum, List.map_map]; rfl
    _ ≤ (θ + R) * T + c * ((range T).filter (fun a => ev 0 a = none)).card := by
        rw [← h1]; simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.sub_zero]
        have : ((((walk 0 (fun _ => 1) T ev 0 0).map (nb 0)).sum : ℕ) : ℝ) ≤
            ((range T).filter (fun a => ev 0 a = none)).card := by exact_mod_cast hnb
        nlinarith

end OneLevel

end Pool.P0061
