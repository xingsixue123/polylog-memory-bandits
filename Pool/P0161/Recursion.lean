import Pool.P0161.Defs

/-!
# Horizon recursion: `DZStepAt c k` (hence `DZStep c k`) implies `MinimaxPolylogAchievable`

Strong induction on the horizon `H` with the constant `q = qOf c k n H = 1/(32Λ²)`, `Λ = max c 1 · Lg(n,H)^k`:
horizons `H ≤ (12Λ²)²·n` use `triv` (regret `≤ H ≤ 12Λ²√(nH)`); larger ones apply one step to the
machine built for horizon `⌈4qH⌉ ≤ H/2`, whose regret `12Λ²√(n⌈4qH⌉) ≤ 12Λ²√(nH)/(2Λ)` makes the step's
bound `Λ(6Λ√(nH) + 6Λ√(nH)) = 12Λ²√(nH)`: the bound is a fixed point, so constants do not compound.
Each step adds `≤ Λ` bits and halves the horizon, so memory is `≤ log₂ T · Λ`.
-/

open Pool.P0001 Real

namespace Pool.P0161

section Rec

variable {c : ℝ} {k : ℕ} (hstep : DZStepAt c k) {n : ℕ} (hn : 1 ≤ n)

lemma Lg_nonneg {n H : ℕ} (hn : 1 ≤ n) (hH : 1 ≤ H) : 0 ≤ Real.log ((n : ℝ) * H) := by
  apply Real.log_nonneg
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) ≤ H := by exact_mod_cast hH
  nlinarith

lemma one_le_Lg {n H : ℕ} (hn : 1 ≤ n) (hH : 1 ≤ H) : 1 ≤ Lg n H := by
  have := Lg_nonneg hn hH; unfold Lg; linarith

lemma Lg_mono {n H T : ℕ} (hn : 1 ≤ n) (hH : 1 ≤ H) (hHT : H ≤ T) : Lg n H ≤ Lg n T := by
  unfold Lg
  have h1 : (0 : ℝ) < (n : ℝ) * H := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) ≤ H := by exact_mod_cast hH
    positivity
  have h2 : (n : ℝ) * H ≤ n * T := by
    apply mul_le_mul_of_nonneg_left (by exact_mod_cast hHT) (by positivity)
  linarith [Real.log_le_log h1 h2]

lemma one_le_Lam {T : ℕ} (hn : 1 ≤ n) (hT : 1 ≤ T) : 1 ≤ Lam c k n T := by
  unfold Lam
  have h1 := one_le_Lg hn hT
  have : 1 ≤ Lg n T ^ k := one_le_pow₀ h1
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ max c 1 * Lg n T ^ k := mul_le_mul (le_max_right _ _) this (by norm_num)
        (le_trans (by norm_num) (le_max_right _ _))

lemma cLg_le_Lam {n H T : ℕ} (hn : 1 ≤ n) (hH : 1 ≤ H) (hHT : H ≤ T) :
    c * Lg n H ^ k ≤ Lam c k n T := by
  unfold Lam
  have h0 : 0 ≤ Lg n H ^ k := pow_nonneg (le_trans zero_le_one (one_le_Lg hn hH)) k
  have h1 : Lg n H ^ k ≤ Lg n T ^ k :=
    pow_le_pow_left₀ (le_trans zero_le_one (one_le_Lg hn hH)) (Lg_mono hn hH hHT) k
  calc c * Lg n H ^ k ≤ max c 1 * Lg n H ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max c 1 * Lg n T ^ k :=
        mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one (le_max_right _ _))

/-- Arithmetic core of the step: with `q = 1/(32Λ²)` and `H' ≤ 8qH`,
`Λ(√(nH/q) + 12Λ²√(nH')) ≤ 12Λ²√(nH)`. -/
lemma step_arith {Λ x y q : ℝ} (hΛ : 1 ≤ Λ) (hx : 0 ≤ x) (_hy : 0 ≤ y)
    (hq : q = 1 / (32 * Λ ^ 2)) (hyx : y ≤ 8 * q * x) :
    Λ * (Real.sqrt (x / q) + 12 * Λ ^ 2 * Real.sqrt y) ≤ 12 * Λ ^ 2 * Real.sqrt x := by
  have hΛ0 : 0 < Λ := by linarith
  have h1 : Real.sqrt (x / q) ≤ 6 * Λ * Real.sqrt x := by
    rw [hq, div_div_eq_mul_div, div_one, Real.sqrt_le_left (by positivity)]
    · rw [mul_pow, mul_pow, Real.sq_sqrt hx]
      nlinarith [sq_nonneg Λ, mul_nonneg hx (sq_nonneg Λ)]
  have h2 : Real.sqrt y ≤ Real.sqrt x / (2 * Λ) := by
    rw [le_div_iff₀ (by positivity)]
    have : Real.sqrt y ≤ Real.sqrt (x / (4 * Λ ^ 2)) := by
      apply Real.sqrt_le_sqrt
      calc y ≤ 8 * q * x := hyx
        _ = x / (4 * Λ ^ 2) := by rw [hq]; field_simp; ring
    rw [Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ 4 * Λ ^ 2),
      show (4 : ℝ) * Λ ^ 2 = (2 * Λ) ^ 2 by ring, Real.sqrt_sq (by positivity)] at this
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have h3 : 12 * Λ ^ 2 * Real.sqrt y ≤ 6 * Λ * Real.sqrt x := by
    calc 12 * Λ ^ 2 * Real.sqrt y ≤ 12 * Λ ^ 2 * (Real.sqrt x / (2 * Λ)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 6 * Λ * Real.sqrt x := by field_simp; ring
  calc Λ * (Real.sqrt (x / q) + 12 * Λ ^ 2 * Real.sqrt y)
      ≤ Λ * (6 * Λ * Real.sqrt x + 6 * Λ * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h3) hΛ0.le
    _ = 12 * Λ ^ 2 * Real.sqrt x := by ring

lemma Lam_mono {n H T : ℕ} (hn : 1 ≤ n) (hH : 1 ≤ H) (hHT : H ≤ T) : Lam c k n H ≤ Lam c k n T := by
  unfold Lam
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_trans zero_le_one (one_le_Lg hn hH)) (Lg_mono hn hH hHT) k)
    (le_trans zero_le_one (le_max_right _ _))

include hstep hn in
/-- **Horizon recursion.** For every horizon `H ≥ 1` there is a homogeneous machine with
`≤ log₂ H · Λ_H` bits and regret `≤ 12Λ_H²√(nH)`, `Λ_H = Lam c k n H`. Each step uses `DZStepAt` at
horizon `H`, i.e. only the rate `q = qOf c k n H = 1/(32Λ_H²)`. -/
theorem exists_machine :
    ∀ H, 1 ≤ H → ∃ M : Machine n, M.IsHomogeneous ∧
      M.memBits ≤ (Nat.log 2 H : ℝ) * Lam c k n H ∧
      ∀ ℓ : LossSeq n, regret M ℓ H ≤ 12 * Lam c k n H ^ 2 * Real.sqrt (n * H) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  intro H
  induction H using Nat.strong_induction_on with
  | _ H ih =>
  intro hH1
  set Λ := Lam c k n H with hΛdef
  have hΛ : 1 ≤ Λ := one_le_Lam hn hH1
  by_cases hsmall : (H : ℝ) ≤ (12 * Λ ^ 2) ^ 2 * n
  · refine ⟨triv n hn, triv_isHomogeneous n hn, ?_, fun ℓ => ?_⟩
    · rw [triv_memBits]; positivity
    · calc regret (triv n hn) ℓ H ≤ H := regret_le _ _ _
        _ = Real.sqrt H * Real.sqrt H := (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ (12 * Λ ^ 2 * Real.sqrt n) * Real.sqrt H := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
            exact hsmall
        _ = 12 * Λ ^ 2 * Real.sqrt (n * H) := by rw [Real.sqrt_mul (by positivity)]; ring
  · push Not at hsmall
    set q : ℝ := qOf c k n H with hqdef
    have hq : q = 1 / (32 * Λ ^ 2) := rfl
    have hqpos : 0 < q := by rw [hq]; positivity
    have hHbig : (144 : ℝ) * Λ ^ 4 * n < H := by nlinarith
    have hΛ4 : (1 : ℝ) ≤ Λ ^ 4 := one_le_pow₀ hΛ
    have hΛ2 : (1 : ℝ) ≤ Λ ^ 2 := one_le_pow₀ hΛ
    have hH144 : (144 : ℝ) < H := by nlinarith
    have hnH : n ≤ H := by exact_mod_cast (show (n : ℝ) ≤ H by nlinarith)
    -- the inner horizon
    set H' := ⌈4 * q * H⌉₊ with hH'
    have h4q : 4 * q * H = H / (8 * Λ ^ 2) := by rw [hq]; field_simp; ring
    have h4q1 : 1 ≤ 4 * q * H := by
      rw [h4q, le_div_iff₀ (by positivity)]; nlinarith
    have hH'1 : 1 ≤ H' := by
      rw [hH']; exact Nat.one_le_iff_ne_zero.mpr (by
        intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
    have hH'le : (H' : ℝ) ≤ 8 * q * H := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 4 * q * H by positivity)
      linarith
    have hH'half : 2 * H' ≤ H := by
      have h8 : 8 * q * H ≤ H / 4 := by
        rw [show 8 * q * H = 2 * (4 * q * H) by ring, h4q]
        have : (H : ℝ) / (8 * Λ ^ 2) ≤ H / 8 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith)
        linarith
      have : (2 * H' : ℝ) ≤ H := by linarith
      exact_mod_cast this
    have hH'lt : H' < H := by omega
    obtain ⟨MB, hMBh, hMBm, hMBr⟩ := ih H' hH'lt hH'1
    have hLm : Lam c k n H' ≤ Λ := Lam_mono hn hH'1 hH'lt.le
    have hLm0 : 0 ≤ Lam c k n H' := le_trans zero_le_one (one_le_Lam hn hH'1)
    have hMBr' : ∀ ℓ : LossSeq n, regret MB ℓ ⌈4 * qOf c k n H * H⌉₊ ≤
        12 * Λ ^ 2 * Real.sqrt (n * H') := by
      intro ℓ
      calc regret MB ℓ ⌈4 * qOf c k n H * H⌉₊ = regret MB ℓ H' := rfl
        _ ≤ 12 * Lam c k n H' ^ 2 * Real.sqrt (n * H') := hMBr ℓ
        _ ≤ 12 * Λ ^ 2 * Real.sqrt (n * H') := by
            gcongr
    have hnq : (n : ℝ) / H ≤ qOf c k n H := by
      rw [← hqdef, hq, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    obtain ⟨M, hMh, hMm, hMr⟩ := hstep n H hn hnH hnq MB hMBh
      (12 * Λ ^ 2 * Real.sqrt (n * H')) hMBr'
    have hle := cLg_le_Lam (c := c) (k := k) hn hH1 (le_refl H)
    refine ⟨M, hMh, ?_, fun ℓ => ?_⟩
    · -- memory: log₂ H' + 1 ≤ log₂ H
      have hlog : (Nat.log 2 H' : ℝ) + 1 ≤ Nat.log 2 H := by
        have : Nat.log 2 H' + 1 ≤ Nat.log 2 H := by
          calc Nat.log 2 H' + 1 = Nat.log 2 (H' * 2) :=
                (Nat.log_mul_base (by norm_num) (by omega)).symm
            _ ≤ Nat.log 2 H := Nat.log_mono_right (by omega)
        exact_mod_cast this
      calc M.memBits ≤ MB.memBits + c * Lg n H ^ k := hMm
        _ ≤ (Nat.log 2 H' : ℝ) * Lam c k n H' + Λ := add_le_add hMBm hle
        _ ≤ (Nat.log 2 H' : ℝ) * Λ + Λ := by
            gcongr
        _ = ((Nat.log 2 H' : ℝ) + 1) * Λ := by ring
        _ ≤ (Nat.log 2 H : ℝ) * Λ := mul_le_mul_of_nonneg_right hlog (by linarith)
    · have hX : 0 ≤ Real.sqrt (n * H / q) + 12 * Λ ^ 2 * Real.sqrt (n * H') := by positivity
      calc regret M ℓ H ≤ c * Lg n H ^ k * (Real.sqrt (n * H / q) + 12 * Λ ^ 2 * Real.sqrt (n * H')) :=
            hMr ℓ
        _ ≤ Λ * (Real.sqrt (n * H / q) + 12 * Λ ^ 2 * Real.sqrt (n * H')) :=
            mul_le_mul_of_nonneg_right hle hX
        _ ≤ 12 * Λ ^ 2 * Real.sqrt (n * H) := by
            apply step_arith hΛ (by positivity) (by positivity) hq
            calc (n : ℝ) * H' ≤ n * (8 * q * H) := mul_le_mul_of_nonneg_left hH'le (by positivity)
              _ = 8 * q * (n * H) := by ring

end Rec

lemma one_le_log {n T : ℕ} (h2 : 2 ≤ n) (hnT : n ≤ T) : 1 ≤ Real.log ((n : ℝ) * T) := by
  have h4 : (4 : ℝ) ≤ (n : ℝ) * T := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast h2
    have : (2 : ℝ) ≤ T := by exact_mod_cast (le_trans h2 hnT)
    nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

lemma natLog_le_two_log {n T : ℕ} (hn : 1 ≤ n) (hnT : n ≤ T) :
    (Nat.log 2 T : ℝ) ≤ 2 * Real.log ((n : ℝ) * T) := by
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast le_trans hn hnT
  have h1 : (Nat.log 2 T : ℝ) ≤ Real.logb 2 T := Real.natLog_le_logb _ _
  have h2 : Real.logb 2 T ≤ 2 * Real.log T := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have := Real.log_nonneg hT
    nlinarith [Real.log_two_gt_d9]
  have h3 : Real.log T ≤ Real.log ((n : ℝ) * T) := by
    apply Real.log_le_log (by linarith)
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  linarith

/-- `DZStep` (every admissible `q`) implies `DZStepAt` (the single rate `qOf`). -/
theorem dzstepAt_of_dzstep {c : ℝ} {k : ℕ} (h : DZStep c k) : DZStepAt c k := by
  intro n T hn hnT hq MB hMB RB hRB
  have hT : 1 ≤ T := le_trans hn hnT
  have hΛ : 1 ≤ Lam c k n T := one_le_Lam hn hT
  have hqc : qOf c k n T * (c * Lg n T ^ k) ≤ 1 := by
    have hle := cLg_le_Lam (c := c) (k := k) hn hT (le_refl T)
    have hq0 : 0 < qOf c k n T := by unfold qOf; positivity
    calc qOf c k n T * (c * Lg n T ^ k) ≤ qOf c k n T * Lam c k n T :=
          mul_le_mul_of_nonneg_left hle hq0.le
      _ = 1 / (32 * Lam c k n T) := by unfold qOf; field_simp
      _ ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  exact h n T hn hnT _ hq hqc MB hMB RB hRB

/-- **Conditional resolution.** A one-level step at the single rate `q = 1/(32Λ²)` with polylogarithmic
loss (`DZStepAt c k`) implies the positive resolution `MinimaxPolylogAchievable`. -/
theorem minimax_of_DZStepAt {c : ℝ} {k : ℕ} (hstep : DZStepAt c k) : MinimaxPolylogAchievable := by
  classical
  let F : Family := fun n T hn =>
    if h : n ≤ T ∧ 2 ≤ n then Classical.choose (exists_machine hstep hn T (le_trans hn h.1))
    else triv n hn
  have hspec : ∀ n T (hn : 1 ≤ n) (h : n ≤ T ∧ 2 ≤ n), F n T hn =
      Classical.choose (exists_machine hstep hn T (le_trans hn h.1)) := by
    intro n T hn h; simp only [F, dif_pos h]
  have htriv : ∀ n T (hn : 1 ≤ n) (h : ¬ (n ≤ T ∧ 2 ≤ n)), F n T hn = triv n hn := by
    intro n T hn h; simp only [F, dif_neg h]
  set c₁ := max c 1 with hc₁
  have hc₁1 : 1 ≤ c₁ := le_max_right _ _
  -- the constant Λ in terms of log(nT)
  have hLam : ∀ n T, 2 ≤ n → n ≤ T →
      Lam c k n T ≤ c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ k := by
    intro n T h2 hnT
    have hl := one_le_log h2 hnT
    unfold Lam Lg
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) k)
      (by linarith)
  refine ⟨F, ?_, ⟨2 * c₁ * 2 ^ k, k + 1, ?_⟩, ⟨12 * c₁ ^ 2 * 4 ^ k, 2 * k, ?_⟩⟩
  · intro n T hn
    by_cases h : n ≤ T ∧ 2 ≤ n
    · rw [hspec n T hn h]
      exact (Classical.choose_spec (exists_machine hstep hn T (le_trans hn h.1))).1
    · rw [htriv n T hn h]; exact triv_isHomogeneous n hn
  · intro n T hn hnT
    have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := Lg_nonneg hn (le_trans hn hnT)
    by_cases h : n ≤ T ∧ 2 ≤ n
    · rw [hspec n T hn h]
      have hm := (Classical.choose_spec (exists_machine hstep hn T (le_trans hn h.1))).2.1
      have hΛ0 : 0 ≤ Lam c k n T := le_trans zero_le_one (one_le_Lam hn (le_trans hn hnT))
      calc _ ≤ (Nat.log 2 T : ℝ) * Lam c k n T := hm
        _ ≤ (2 * Real.log ((n : ℝ) * T)) * (c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ k) :=
            mul_le_mul (natLog_le_two_log hn hnT) (hLam n T h.2 hnT) hΛ0 (by positivity)
        _ = 2 * c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ (k + 1) := by ring
    · rw [htriv n T hn h, triv_memBits]; positivity
  · intro n T hn hnT ℓ
    have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := Lg_nonneg hn (le_trans hn hnT)
    by_cases h : n ≤ T ∧ 2 ≤ n
    · rw [hspec n T hn h]
      have hr := (Classical.choose_spec (exists_machine hstep hn T (le_trans hn h.1))).2.2 ℓ
      have hΛ1 := one_le_Lam (c := c) (k := k) hn (le_trans hn hnT)
      have hΛ2 : Lam c k n T ^ 2 ≤ c₁ ^ 2 * 4 ^ k * Real.log ((n : ℝ) * T) ^ (2 * k) := by
        calc Lam c k n T ^ 2 ≤ (c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ k) ^ 2 :=
              pow_le_pow_left₀ (by linarith) (hLam n T h.2 hnT) 2
          _ = c₁ ^ 2 * 4 ^ k * Real.log ((n : ℝ) * T) ^ (2 * k) := by
              rw [show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
                pow_mul]; ring
      calc _ ≤ 12 * Lam c k n T ^ 2 * Real.sqrt (n * T) := hr
        _ ≤ 12 * (c₁ ^ 2 * 4 ^ k * Real.log ((n : ℝ) * T) ^ (2 * k)) * Real.sqrt (n * T) := by
            gcongr
        _ = 12 * c₁ ^ 2 * 4 ^ k * Real.sqrt (n * T) * Real.log ((n : ℝ) * T) ^ (2 * k) := by ring
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [regret_one]; positivity


lemma memBits_nonneg {n : ℕ} (M : Machine n) : 0 ≤ M.memBits := by
  have : Nonempty M.State := ⟨M.init.support_nonempty.some⟩
  apply Real.logb_nonneg one_lt_two
  exact_mod_cast Fintype.card_pos

/-- **Converse.** The positive resolution implies `DZStep c k` for some `c, k` (take the resolving
machine and ignore the base): `DZStep` is equivalent to `MinimaxPolylogAchievable`; its interest is
that it is a ONE-level statement about an arbitrary base. -/
theorem minimax_of_DZStep {c : ℝ} {k : ℕ} (hstep : DZStep c k) : MinimaxPolylogAchievable :=
  minimax_of_DZStepAt (dzstepAt_of_dzstep hstep)

theorem dzstep_of_minimax (h : MinimaxPolylogAchievable) : ∃ (c : ℝ) (k : ℕ), DZStep c k := by
  obtain ⟨F, hF, ⟨C, k, hmem⟩, ⟨C', k', hreg⟩⟩ := h
  refine ⟨max C 0 + max C' 0 + 1, k + k', ?_⟩
  intro n T hn hnT q hq hqc MB _ RB hRB
  have hT : 1 ≤ T := le_trans hn hnT
  have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := Lg_nonneg hn hT
  have hL1 : 1 ≤ Lg n T := one_le_Lg hn hT
  have hlL : Real.log ((n : ℝ) * T) ≤ Lg n T := by unfold Lg; linarith
  set K := k + k'
  set c := max C 0 + max C' 0 + 1 with hc
  have hc1 : 1 ≤ c := by have := le_max_right C 0; have := le_max_right C' 0; linarith
  have hLK : 1 ≤ Lg n T ^ K := one_le_pow₀ hL1
  have hpow : ∀ j, j ≤ K → Real.log ((n : ℝ) * T) ^ j ≤ Lg n T ^ K := fun j hj =>
    (pow_le_pow_left₀ hl0 hlL j).trans (pow_le_pow_right₀ hL1 hj)
  have hcL : 1 ≤ c * Lg n T ^ K := by nlinarith
  have hqpos : 0 < q := lt_of_lt_of_le (by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    have : (0 : ℝ) < T := by exact_mod_cast hT
    positivity) hq
  have hq1 : q ≤ 1 := by nlinarith
  have hRB0 : 0 ≤ RB := by
    have := hRB (fun _ _ => false)
    rwa [Pool.P0144.regret_zero_seq] at this
  refine ⟨F n T hn, hF n T hn, ?_, fun ℓ => ?_⟩
  · have h1 := hmem n T hn hnT
    have h2 : C * Real.log ((n : ℝ) * T) ^ k ≤ c * Lg n T ^ K := by
      calc C * Real.log ((n : ℝ) * T) ^ k ≤ max C 0 * Real.log ((n : ℝ) * T) ^ k :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hl0 _)
        _ ≤ c * Lg n T ^ K := mul_le_mul (by
            have := le_max_right C' 0; linarith) (hpow k (by omega)) (pow_nonneg hl0 _)
              (by linarith)
    have := memBits_nonneg MB
    linarith
  · have h1 := hreg n T hn hnT ℓ
    have hs : Real.sqrt (n * T) ≤ Real.sqrt (n * T / q) :=
      Real.sqrt_le_sqrt (le_div_self (by positivity) hqpos hq1)
    have hs0 : 0 ≤ Real.sqrt ((n : ℝ) * T) := Real.sqrt_nonneg _
    calc regret (F n T hn) ℓ T ≤ C' * Real.sqrt (n * T) * Real.log (n * T) ^ k' := h1
      _ ≤ max C' 0 * Real.sqrt (n * T) * Lg n T ^ K := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hs0)
            (hpow k' (by omega)) (pow_nonneg hl0 _) (by positivity)
      _ ≤ c * Lg n T ^ K * (Real.sqrt (n * T / q) + RB) := by
          have hcC : max C' 0 ≤ c := by have := le_max_right C 0; linarith
          calc max C' 0 * Real.sqrt (n * T) * Lg n T ^ K
              ≤ c * Real.sqrt (n * T) * Lg n T ^ K := by gcongr
            _ = c * Lg n T ^ K * Real.sqrt (n * T) := by ring
            _ ≤ c * Lg n T ^ K * (Real.sqrt (n * T / q) + RB) := by gcongr; linarith

end Pool.P0161
