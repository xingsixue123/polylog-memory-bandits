import Pool.Prelude

open Finset

namespace Pool.P0154

/-- Interval sum `F[a,b) = Σ_{u ∈ [a,b)} f u`. -/
noncomputable def isum (f : ℕ → ℝ) (a b : ℕ) : ℝ := ∑ u ∈ Ico a b, f u

lemma isum_split (f : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    isum f a c = isum f a b + isum f b c := by
  unfold isum
  rw [Finset.sum_Ico_consecutive _ hab hbc]

lemma isum_succ (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    isum f a (b + 1) = isum f a b + f b := by
  rw [isum_split f hab (Nat.le_succ b)]
  simp [isum]

lemma isum_nonneg (v : ℕ → ℝ) (hv : ∀ u, 0 ≤ v u) (a b : ℕ) : 0 ≤ isum v a b :=
  Finset.sum_nonneg (fun u _ => hv u)

/-! ### Summation by parts for a nondecreasing rate -/

/-- Abel summation on `[s, D)`. -/
theorem abel (x g : ℕ → ℝ) (s : ℕ) : ∀ D, s < D →
    ∑ t ∈ Ico s D, x t * g t
      = x (D - 1) * isum g s D - ∑ t ∈ Ico (s + 1) D, (x t - x (t - 1)) * isum g s t := by
  intro D hD
  induction D with
  | zero => omega
  | succ D ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hD with h | h
    · have hsD : s + 1 ≤ D := h
      rw [Finset.sum_Ico_succ_top (by omega), ih h, Finset.sum_Ico_succ_top hsD,
        isum_succ g (by omega : s ≤ D)]
      have : D + 1 - 1 = D := by omega
      rw [this]
      have hD1 : D - 1 + 1 = D := by omega
      ring
    · subst h
      simp [isum]

/-- With a nondecreasing rate, the weighted cost is at most the final rate times the final
prefix gap plus, at every rate increase, the increase times the current lead `(-G)⁺`. -/
theorem abel_le (x g : ℕ → ℝ) (s D : ℕ) (hD : s < D)
    (hmono : ∀ t, s + 1 ≤ t → t < D → x (t - 1) ≤ x t) :
    ∑ t ∈ Ico s D, x t * g t
      ≤ x (D - 1) * isum g s D + ∑ t ∈ Ico (s + 1) D, (x t - x (t - 1)) * max 0 (-isum g s t) := by
  rw [abel x g s D hD]
  have : -(∑ t ∈ Ico (s + 1) D, (x t - x (t - 1)) * isum g s t)
      ≤ ∑ t ∈ Ico (s + 1) D, (x t - x (t - 1)) * max 0 (-isum g s t) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro t ht
    rw [Finset.mem_Ico] at ht
    have h0 : 0 ≤ x t - x (t - 1) := by linarith [hmono t ht.1 ht.2]
    have : -((x t - x (t - 1)) * isum g s t) = (x t - x (t - 1)) * (-isum g s t) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) h0
  linarith

/-! ### Piecewise-constant weights against an interval guarantee -/

/-- Number of change points of `h` in `[1, T)`. -/
noncomputable def chg (h : ℕ → ℝ) (T : ℕ) : ℕ :=
  ((Ico 1 T).filter (fun u => h u ≠ h (u - 1))).card

section Pieces

variable (f v : ℕ → ℝ) (ρ₀ S : ℝ)

/-- Invariant for the run induction: some `a ≤ T` starts the current constant run. -/
theorem pieces_aux (Tm : ℕ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀)
    (hint : ∀ a b, a ≤ b → b ≤ Tm → -isum f a b ≤ ρ₀ + isum v a b)
    (h : ℕ → ℝ) (h0 : ∀ u, 0 ≤ h u) (hS : ∀ u, h u ≤ S) :
    ∀ T, 1 ≤ T → T ≤ Tm → ∃ a, a < T ∧ (∀ u, a ≤ u → u < T → h u = h a) ∧
      ∑ u ∈ range T, h u * (-f u)
        ≤ S * ρ₀ * (chg h T) + S * isum v 0 a + h a * (-isum f a T) := by
  intro T hT hTm
  induction T with
  | zero => omega
  | succ T ih =>
    rcases Nat.eq_zero_or_pos T with rfl | hTpos
    · refine ⟨0, by omega, ?_, ?_⟩
      · intro u hu1 hu2; interval_cases u; rfl
      · simp [chg, isum]
    · obtain ⟨a, haT, hconst, hbound⟩ := ih hTpos (by omega)
      have hS0 : 0 ≤ S := le_trans (h0 0) (hS 0)
      by_cases hc : h T = h (T - 1)
      · -- same run
        refine ⟨a, by omega, ?_, ?_⟩
        · intro u hu1 hu2
          rcases Nat.lt_succ_iff_lt_or_eq.mp hu2 with hu | hu
          · exact hconst u hu1 hu
          · rw [hu, hc]; exact hconst (T - 1) (by omega) (by omega)
        · have hchg : chg h (T + 1) = chg h T := by
            unfold chg
            rw [Nat.Ico_succ_right_eq_insert_Ico (by omega : 1 ≤ T), Finset.filter_insert]
            simp [hc]
          rw [Finset.sum_range_succ, hchg, isum_succ f (by omega : a ≤ T)]
          have hTa : h T = h a := by rw [hc]; exact hconst (T - 1) (by omega) (by omega)
          rw [hTa]
          nlinarith [hbound]
      · -- new run starting at T
        refine ⟨T, by omega, ?_, ?_⟩
        · intro u hu1 hu2; have : u = T := by omega
          subst this; rfl
        · have hchg : chg h (T + 1) = chg h T + 1 := by
            unfold chg
            rw [Nat.Ico_succ_right_eq_insert_Ico (by omega : 1 ≤ T), Finset.filter_insert]
            simp only [ne_eq, hc, not_false_eq_true, if_true]
            rw [Finset.card_insert_of_notMem]
            simp
          rw [Finset.sum_range_succ, hchg]
          -- close the old run [a, T)
          have hclose : h a * (-isum f a T) ≤ S * ρ₀ + S * isum v a T := by
            have hI := hint a T (by omega) (by omega)
            have hva := isum_nonneg v hv a T
            rcases le_or_gt (-isum f a T) 0 with hneg | hpos
            · have : h a * (-isum f a T) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (h0 a) hneg
              nlinarith
            · calc h a * (-isum f a T) ≤ S * (-isum f a T) :=
                    mul_le_mul_of_nonneg_right (hS a) hpos.le
                _ ≤ S * (ρ₀ + isum v a T) := mul_le_mul_of_nonneg_left hI hS0
                _ = S * ρ₀ + S * isum v a T := by ring
          have hsplit : isum v 0 T = isum v 0 a + isum v a T := isum_split v (by omega) (by omega)
          have hlast : isum f T (T + 1) = f T := by simp [isum]
          rw [hsplit, hlast]
          push_cast
          nlinarith [hbound, hclose]

/-- Piecewise-constant nonnegative weights bounded by `S`, against an interval guarantee
`-F[a,b) ≤ ρ₀ + V[a,b)`: the weighted sum of `-f` is at most `S·ρ₀·(changes+1) + S·V[0,T)`. -/
theorem pieces (T : ℕ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀)
    (hint : ∀ a b, a ≤ b → b ≤ T → -isum f a b ≤ ρ₀ + isum v a b)
    (h : ℕ → ℝ) (h0 : ∀ u, 0 ≤ h u) (hS : ∀ u, h u ≤ S) :
    ∑ u ∈ range T, h u * (-f u) ≤ S * ρ₀ * ((chg h T : ℝ) + 1) + S * isum v 0 T := by
  have hS0 : 0 ≤ S := le_trans (h0 0) (hS 0)
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · simp [isum]; positivity
  obtain ⟨a, haT, _, hb⟩ := pieces_aux f v ρ₀ S T hv hρ₀ hint h h0 hS T hT le_rfl
  have hclose : h a * (-isum f a T) ≤ S * ρ₀ + S * isum v a T := by
    have hI := hint a T (by omega) le_rfl
    rcases le_or_gt (-isum f a T) 0 with hneg | hpos
    · have : h a * (-isum f a T) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (h0 a) hneg
      have := isum_nonneg v hv a T
      nlinarith
    · calc h a * (-isum f a T) ≤ S * (-isum f a T) := mul_le_mul_of_nonneg_right (hS a) hpos.le
        _ ≤ S * (ρ₀ + isum v a T) := mul_le_mul_of_nonneg_left hI hS0
        _ = S * ρ₀ + S * isum v a T := by ring
  have hsplit : isum v 0 T = isum v 0 a + isum v a T := isum_split v (by omega) (by omega)
  rw [hsplit]
  nlinarith [hb, hclose]

end Pieces

/-! ### Windows of bounded multiplicity -/

section Windows

variable {ι : Type*} (W : Finset ι) (s e : ι → ℕ)

/-- Number of windows `[s i, e i)` containing round `u`. -/
def mult (u : ℕ) : ℕ := (W.filter (fun i => s i ≤ u ∧ u < e i)).card

lemma sum_windows_eq (f : ℕ → ℝ) (T : ℕ) (he : ∀ i ∈ W, e i ≤ T) :
    ∑ i ∈ W, isum f (s i) (e i) = ∑ u ∈ range T, (mult W s e u : ℝ) * f u := by
  unfold isum mult
  have : ∀ i ∈ W, ∑ u ∈ Ico (s i) (e i), f u
      = ∑ u ∈ range T, if s i ≤ u ∧ u < e i then f u else 0 := by
    intro i hi
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext u
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro hu; exact ⟨by have := he i hi; omega, hu⟩
    · intro hu; exact hu.2
  rw [Finset.sum_congr rfl this, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

lemma mult_eq_zero (T : ℕ) (he : ∀ i ∈ W, e i ≤ T) (u : ℕ) (hu : T ≤ u) : mult W s e u = 0 := by
  unfold mult
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi h
  have := he i hi
  omega

/-- The multiplicity changes only at window endpoints. -/
lemma chg_le (S : ℝ) (T : ℕ) :
    chg (fun u => S - (mult W s e u : ℝ)) T ≤ 2 * W.card := by
  unfold chg
  have hsub : (Ico 1 T).filter (fun u => S - (mult W s e u : ℝ) ≠ S - (mult W s e (u - 1) : ℝ))
      ⊆ W.image s ∪ W.image e := by
    intro u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨hu1, hne⟩ := hu
    rw [Finset.mem_Ico] at hu1
    by_contra hnot
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hnot
    push_neg at hnot
    apply hne
    have : mult W s e u = mult W s e (u - 1) := by
      unfold mult
      congr 1
      apply Finset.filter_congr
      intro i hi
      have h1 := hnot.1 i hi
      have h2 := hnot.2 i hi
      omega
    rw [this]
  calc ((Ico 1 T).filter _).card ≤ (W.image s ∪ W.image e).card := Finset.card_le_card hsub
    _ ≤ (W.image s).card + (W.image e).card := Finset.card_union_le _ _
    _ ≤ W.card + W.card := add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * W.card := by ring

/-- **Windows lemma.** If at most `S` windows contain any round and `-F[a,b) ≤ ρ₀ + V[a,b)` on
every interval, then the window sums of `f` add up to at most `S·F[0,T) + S·ρ₀·(2N+1) + S·V[0,T)`,
with `N` the number of windows. -/
theorem windows (f v : ℕ → ℝ) (ρ₀ S : ℝ) (T : ℕ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀)
    (hint : ∀ a b, a ≤ b → b ≤ T → -isum f a b ≤ ρ₀ + isum v a b)
    (he : ∀ i ∈ W, e i ≤ T) (hmult : ∀ u, (mult W s e u : ℝ) ≤ S) :
    ∑ i ∈ W, isum f (s i) (e i)
      ≤ S * isum f 0 T + S * ρ₀ * (2 * W.card + 1) + S * isum v 0 T := by
  set h : ℕ → ℝ := fun u => S - (mult W s e u : ℝ) with hh
  have h0 : ∀ u, 0 ≤ h u := fun u => by simp only [hh]; linarith [hmult u]
  have hS : ∀ u, h u ≤ S := fun u => by
    simp only [hh]; have : (0 : ℝ) ≤ mult W s e u := Nat.cast_nonneg _; linarith
  have hS0 : 0 ≤ S := le_trans (h0 0) (hS 0)
  have hp := pieces f v ρ₀ S T hv hρ₀ hint h h0 hS
  have hc : ((chg h T : ℕ) : ℝ) ≤ 2 * W.card := by
    have := chg_le W s e S T
    exact_mod_cast this
  have hexp : ∑ u ∈ range T, h u * (-f u)
      = -(S * isum f 0 T) + ∑ i ∈ W, isum f (s i) (e i) := by
    rw [sum_windows_eq W s e f T he]
    simp only [hh, isum, Finset.range_eq_Ico]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro u _; ring
  have : S * ρ₀ * ((chg h T : ℝ) + 1) ≤ S * ρ₀ * (2 * W.card + 1) := by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hS0 hρ₀); linarith
  linarith

/-- **Credit lemma.** Leads bounded by window sums plus slack add up to at most
`S·F[0,T) + S·ρ₀·(2N+1) + S·V[0,T) + Σ slack`. -/
theorem credit (f v : ℕ → ℝ) (ρ₀ S : ℝ) (T : ℕ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀)
    (hint : ∀ a b, a ≤ b → b ≤ T → -isum f a b ≤ ρ₀ + isum v a b)
    (he : ∀ i ∈ W, e i ≤ T) (hmult : ∀ u, (mult W s e u : ℝ) ≤ S)
    (lead r : ι → ℝ) (hlead : ∀ i ∈ W, lead i ≤ isum f (s i) (e i) + r i) :
    ∑ i ∈ W, lead i
      ≤ S * isum f 0 T + S * ρ₀ * (2 * W.card + 1) + S * isum v 0 T + ∑ i ∈ W, r i := by
  have h1 : ∑ i ∈ W, lead i ≤ ∑ i ∈ W, (isum f (s i) (e i) + r i) := Finset.sum_le_sum hlead
  rw [Finset.sum_add_distrib] at h1
  have := windows W s e f v ρ₀ S T hv hρ₀ hint he hmult
  linarith

/-- A lead of a member over BASE on `[τ, t)` is at most BASE-minus-ALG on `[τ, t)` plus ALG's
slack against that member there: if `A[τ,t) ≤ L[τ,t) + r` then `B[τ,t) − L[τ,t) ≤ (B−A)[τ,t) + r`. -/
lemma lead_le (b a ℓ : ℕ → ℝ) (τ t : ℕ) (r : ℝ) (halg : isum a τ t ≤ isum ℓ τ t + r) :
    -isum (fun u => ℓ u - b u) τ t ≤ isum (fun u => b u - a u) τ t + r := by
  unfold isum at *
  simp only [Finset.sum_sub_distrib]
  linarith

/-- **Jump cost.** Rate increases `Δ i ∈ [0, x̄]` at events `i` whose lead windows `[s i, e i)` have
multiplicity at most `S`, with leads bounded by window sums of `f = b − a` plus slack `r i`, cost
`Σ Δ·lead⁺ ≤ x̄·(S·F[0,T) + S·ρ₀·(2N+1) + S·V[0,T) + Σ r⁺)`. -/
theorem jump_cost (f v : ℕ → ℝ) (ρ₀ S xbar : ℝ) (T : ℕ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀)
    (hint : ∀ a b, a ≤ b → b ≤ T → -isum f a b ≤ ρ₀ + isum v a b)
    (he : ∀ i ∈ W, e i ≤ T) (hmult : ∀ u, (mult W s e u : ℝ) ≤ S)
    (hxbar : 0 ≤ xbar) (Δ lead r : ι → ℝ) (hΔ : ∀ i ∈ W, 0 ≤ Δ i ∧ Δ i ≤ xbar)
    (hlead : ∀ i ∈ W, lead i ≤ isum f (s i) (e i) + r i) :
    ∑ i ∈ W, Δ i * max 0 (lead i)
      ≤ xbar * (S * isum f 0 T + S * ρ₀ * (2 * W.card + 1) + S * isum v 0 T
          + ∑ i ∈ W, max 0 (r i)) := by
  classical
  have hS0 : 0 ≤ S := le_trans (Nat.cast_nonneg _) (hmult 0)
  set Wp := W.filter (fun i => 0 < lead i) with hWp
  -- reduce to positive leads
  have hstep1 : ∑ i ∈ W, Δ i * max 0 (lead i) ≤ ∑ i ∈ Wp, xbar * lead i := by
    rw [hWp, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨h0, h1⟩ := hΔ i hi
    by_cases hp : 0 < lead i
    · rw [if_pos hp, max_eq_right hp.le]
      exact mul_le_mul_of_nonneg_right h1 hp.le
    · rw [if_neg hp, max_eq_left (not_lt.mp hp), mul_zero]
  -- the positive-lead subfamily satisfies the credit lemma's hypotheses
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
  have hleadp : ∀ i ∈ Wp, lead i ≤ isum f (s i) (e i) + max 0 (r i) := fun i hi =>
    le_trans (hlead i (Finset.mem_filter.mp hi).1) (by linarith [le_max_right 0 (r i)])
  have hcr := credit Wp s e f v ρ₀ S T hv hρ₀ hint hep hmultp lead (fun i => max 0 (r i)) hleadp
  have hcard : (Wp.card : ℝ) ≤ W.card := by exact_mod_cast Finset.card_filter_le W _
  have hr : ∑ i ∈ Wp, max 0 (r i) ≤ ∑ i ∈ W, max 0 (r i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ W)
      (fun i _ _ => le_max_left 0 (r i))
  have hSρ : S * ρ₀ * (2 * Wp.card + 1) ≤ S * ρ₀ * (2 * W.card + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hS0 hρ₀)
  rw [← Finset.mul_sum] at hstep1
  have hbound : ∑ i ∈ Wp, lead i ≤ S * isum f 0 T + S * ρ₀ * (2 * W.card + 1) + S * isum v 0 T
      + ∑ i ∈ W, max 0 (r i) := by linarith
  calc ∑ i ∈ W, Δ i * max 0 (lead i) ≤ xbar * ∑ i ∈ Wp, lead i := hstep1
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hxbar

end Windows

/-- Bookkeeping: if the regret is `(1−c)·R_A + c·R_B + P` and the rate-increase part satisfies
`P ≤ E + κ·(R_B − R_A)`, the increase cost moves `κ` of ALG's weight onto BASE. -/
theorem absorb (Reg RA RB P E c κ : ℝ) (hreg : Reg = (1 - c) * RA + c * RB + P)
    (hP : P ≤ E + κ * (RB - RA)) : Reg ≤ (1 - c - κ) * RA + (c + κ) * RB + E := by
  rw [hreg]; nlinarith

/-- Negative control: without the multiplicity hypothesis the windows lemma fails. Two copies
of the window `[0,1)` with `f 0 = 1` (so `-F ≤ 0` on every interval) sum to `2`, while
`S·F[0,1) = 1` for `S = 1`; indeed the multiplicity at round `0` is `2`. -/
example : mult (Finset.univ : Finset (Fin 2)) (fun _ => 0) (fun _ => 1) 0 = 2 ∧
    ∑ i ∈ (Finset.univ : Finset (Fin 2)), isum (fun _ => (1 : ℝ)) ((fun _ => 0) i) ((fun _ => 1) i)
      > 1 * isum (fun _ => (1 : ℝ)) 0 1 + 1 * 0 * (2 * 2 + 1) + 1 * isum (fun _ => (0 : ℝ)) 0 1 := by
  refine ⟨by decide, ?_⟩
  simp [isum]

/-- Non-vacuity: the hypotheses of `windows` hold for a nonnegative `f` with `ρ₀ = 0`, `v = 0`. -/
example (T : ℕ) : ∀ a b, a ≤ b → b ≤ T → -isum (fun _ => (1 : ℝ)) a b ≤ 0 + isum (fun _ => (0 : ℝ)) a b := by
  intro a b _ _
  have : (0 : ℝ) ≤ isum (fun _ => (1 : ℝ)) a b := Finset.sum_nonneg (fun _ _ => zero_le_one)
  simp only [isum, Finset.sum_const_zero, zero_add] at this ⊢
  linarith

/-- Positive control with a mixed-sign `f` (the case of interest): `T = 2`, `f = (−1, 1)`,
`ρ₀ = 1`, `v = 0`, two windows `[1,2)`, `S = 2`. The interval hypothesis holds, `windows` applies,
and the window sum `2` exceeds `S·F[0,2) = 0`, so the `S·ρ₀·(2N+1)` term is really used. -/
example :
    let f : ℕ → ℝ := fun u => if u = 0 then -1 else 1
    (∀ a b, a ≤ b → b ≤ 2 → -isum f a b ≤ 1 + isum (fun _ => (0 : ℝ)) a b) ∧
    ∑ i ∈ (Finset.univ : Finset (Fin 2)), isum f ((fun _ => 1) i) ((fun _ => 2) i) = 2 ∧
    2 * isum f 0 2 = 0 ∧
    ∑ i ∈ (Finset.univ : Finset (Fin 2)), isum f ((fun _ => 1) i) ((fun _ => 2) i)
      ≤ 2 * isum f 0 2 + 2 * 1 * (2 * (Finset.univ : Finset (Fin 2)).card + 1)
        + 2 * isum (fun _ => (0 : ℝ)) 0 2 := by
  intro f
  have hint : ∀ a b, a ≤ b → b ≤ 2 → -isum f a b ≤ 1 + isum (fun _ => (0 : ℝ)) a b := by
    intro a b hab hb
    interval_cases b <;> interval_cases a <;> simp [isum, f, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ]
  refine ⟨hint, ?_, ?_, ?_⟩
  · norm_num [isum, f]
  · norm_num [isum, f, Finset.sum_range_succ]
  · refine windows Finset.univ (fun _ => 1) (fun _ => 2) f (fun _ => 0) 1 2 2 (fun _ => le_refl 0)
      zero_le_one hint (fun _ _ => le_refl 2) ?_
    intro u
    have : mult (Finset.univ : Finset (Fin 2)) (fun _ => 1) (fun _ => 2) u ≤ 2 := by
      unfold mult
      exact le_trans (Finset.card_filter_le _ _) (by simp)
    exact_mod_cast this

end Pool.P0154
