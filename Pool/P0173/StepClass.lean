import Pool.P0161.Statement
import Pool.P0050.CoinAlg

/-!
# The one-level step of P0161 restricted to a class of machines (here: homogeneous P0050 coin algorithms)

* `StepAtIn Cls c k`: P0161's `DZStepAt c k` with bases AND outputs in a class `Cls`.
* `minimax_of_StepAtIn`: if `Cls` contains, for every `n ≥ 1`, a homogeneous zero-bit machine, then
  `StepAtIn Cls c k → MinimaxPolylogAchievable`, by P0161's horizon recursion (the class is carried along).
* `CoinHom A`: the P0050 coin algorithm `A` does not use the round number. `toMachine_isHomogeneous`.
* `CoinCls M`: `M = A.toMachine` for a homogeneous coin algorithm `A`; `coinCls_zero`: the all-`Unit` coin algorithm
  gives a homogeneous zero-bit member.
* `minimax_of_StepAtCoin`: the step for coin-algorithm bases (outputs coin algorithms) implies the target.
* `stepAtIn_true`: with the trivial class, `StepAtIn` is P0161's `DZStepAt`. For a smaller class the hypothesis
  is weaker on the input side (fewer bases) and stronger on the output side (the output must be in the class).
-/

open Pool.P0001 Pool.P0161 Real

namespace Pool.P0173

/-- P0161's `DZStepAt c k` with bases and outputs in the class `Cls`. -/
def StepAtIn (Cls : ∀ {n : ℕ}, Machine n → Prop) (c : ℝ) (k : ℕ) : Prop :=
  ∀ (n T : ℕ), 1 ≤ n → n ≤ T → (n : ℝ) / T ≤ qOf c k n T →
    ∀ (MB : Machine n), Cls MB → MB.IsHomogeneous → ∀ RB : ℝ,
      (∀ ℓ : LossSeq n, regret MB ℓ ⌈4 * qOf c k n T * T⌉₊ ≤ RB) →
      ∃ M : Machine n, Cls M ∧ M.IsHomogeneous ∧ M.memBits ≤ MB.memBits + c * Lg n T ^ k ∧
        ∀ ℓ : LossSeq n, regret M ℓ T ≤ c * Lg n T ^ k * (Real.sqrt (n * T / qOf c k n T) + RB)

/-- With the trivial class the restricted step is P0161's `DZStepAt`. -/
theorem stepAtIn_true {c : ℝ} {k : ℕ} : StepAtIn (fun _ => True) c k ↔ DZStepAt c k := by
  constructor
  · intro h n T hn hnT hq MB hMB RB hRB
    obtain ⟨M, -, hM⟩ := h n T hn hnT hq MB trivial hMB RB hRB
    exact ⟨M, hM⟩
  · intro h n T hn hnT hq MB _ hMB RB hRB
    obtain ⟨M, hM⟩ := h n T hn hnT hq MB hMB RB hRB
    exact ⟨M, trivial, hM⟩

section Rec

variable {Cls : ∀ {n : ℕ}, Machine n → Prop} {c : ℝ} {k : ℕ} (hstep : StepAtIn Cls c k)
  (hzero : ∀ (n : ℕ), 1 ≤ n → ∃ M0 : Machine n, Cls M0 ∧ M0.IsHomogeneous ∧ M0.memBits ≤ 0)
  {n : ℕ} (hn : 1 ≤ n)

include hstep hzero hn in
/-- P0161's horizon recursion (`Pool.P0161.exists_machine`) inside the class `Cls`. -/
theorem exists_machineIn :
    ∀ H, 1 ≤ H → ∃ M : Machine n, Cls M ∧ M.IsHomogeneous ∧
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
  · obtain ⟨M0, hM0c, hM0h, hM0m⟩ := hzero n hn
    refine ⟨M0, hM0c, hM0h, ?_, fun ℓ => ?_⟩
    · exact hM0m.trans (by positivity)
    · calc regret M0 ℓ H ≤ H := regret_le _ _ _
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
    obtain ⟨MB, hMBc, hMBh, hMBm, hMBr⟩ := ih H' hH'lt hH'1
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
    obtain ⟨M, hMc, hMh, hMm, hMr⟩ := hstep n H hn hnH hnq MB hMBc hMBh
      (12 * Λ ^ 2 * Real.sqrt (n * H')) hMBr'
    have hle := cLg_le_Lam (c := c) (k := k) hn hH1 (le_refl H)
    refine ⟨M, hMc, hMh, ?_, fun ℓ => ?_⟩
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

theorem minimax_of_StepAtIn {Cls : ∀ {n : ℕ}, Machine n → Prop} {c : ℝ} {k : ℕ}
    (hstep : StepAtIn Cls c k)
    (hzero : ∀ (n : ℕ), 1 ≤ n → ∃ M0 : Machine n, Cls M0 ∧ M0.IsHomogeneous ∧ M0.memBits ≤ 0) :
    MinimaxPolylogAchievable := by
  classical
  let F : Family := fun n T hn =>
    if h : n ≤ T ∧ 2 ≤ n then Classical.choose (exists_machineIn hstep hzero hn T (le_trans hn h.1))
    else triv n hn
  have hspec : ∀ n T (hn : 1 ≤ n) (h : n ≤ T ∧ 2 ≤ n), F n T hn =
      Classical.choose (exists_machineIn hstep hzero hn T (le_trans hn h.1)) := by
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
      exact (Classical.choose_spec (exists_machineIn hstep hzero hn T (le_trans hn h.1))).2.1
    · rw [htriv n T hn h]; exact triv_isHomogeneous n hn
  · intro n T hn hnT
    have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := Lg_nonneg hn (le_trans hn hnT)
    by_cases h : n ≤ T ∧ 2 ≤ n
    · rw [hspec n T hn h]
      have hm := (Classical.choose_spec (exists_machineIn hstep hzero hn T (le_trans hn h.1))).2.2.1
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
      have hr := (Classical.choose_spec (exists_machineIn hstep hzero hn T (le_trans hn h.1))).2.2.2 ℓ
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



open Pool.P0050 in
/-- A P0050 coin algorithm whose rules do not use the round number. -/
def CoinHom {n : ℕ} (A : CoinAlg n) : Prop :=
  (∀ t s y, A.act t s y = A.act 0 s y) ∧ (∀ t s y b z, A.upd t s y b z = A.upd 0 s y b z)

open Pool.P0050 in
theorem toMachine_isHomogeneous {n : ℕ} {A : CoinAlg n} (h : CoinHom A) : A.toMachine.IsHomogeneous := by
  refine ⟨fun t p => ?_, fun t p a b => ?_⟩
  · show PMF.pure (A.act t p.1 p.2) = PMF.pure (A.act 0 p.1 p.2)
    rw [h.1]
  · show (A.ν.bind fun z => A.μ.map fun y' => (A.upd t p.1 p.2 b z, y')) =
      A.ν.bind fun z => A.μ.map fun y' => (A.upd 0 p.1 p.2 b z, y')
    simp_rw [h.2 t]

open Pool.P0050 in
/-- The class of machines realized by homogeneous coin algorithms. -/
def CoinCls {n : ℕ} (M : Machine n) : Prop := ∃ A : CoinAlg n, CoinHom A ∧ M = A.toMachine

open Pool.P0050 in
/-- The all-`Unit` coin algorithm pulling arm `0`. -/
noncomputable def trivCoin (n : ℕ) (hn : 1 ≤ n) : CoinAlg n where
  S := Unit
  Y := Unit
  Z := Unit
  μ := PMF.pure ()
  ν := PMF.pure ()
  s0 := ()
  act _ _ _ := ⟨0, hn⟩
  upd _ _ _ _ _ := ()

open Pool.P0050 in
theorem coinCls_zero (n : ℕ) (hn : 1 ≤ n) :
    ∃ M0 : Machine n, CoinCls M0 ∧ M0.IsHomogeneous ∧ M0.memBits ≤ 0 := by
  have hh : CoinHom (trivCoin n hn) := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  refine ⟨(trivCoin n hn).toMachine, ⟨trivCoin n hn, hh, rfl⟩, toMachine_isHomogeneous hh, ?_⟩
  show Real.logb 2 (Fintype.card (Unit × Unit)) ≤ 0
  simp

/-- **Coin-algorithm version.** The one-level step at P0161's rate for homogeneous coin-algorithm bases, with
homogeneous coin-algorithm outputs, implies `MinimaxPolylogAchievable`. -/
theorem minimax_of_StepAtCoin {c : ℝ} {k : ℕ} (hstep : StepAtIn (fun {n} M => CoinCls (n := n) M) c k) :
    MinimaxPolylogAchievable :=
  minimax_of_StepAtIn hstep coinCls_zero

end Pool.P0173
