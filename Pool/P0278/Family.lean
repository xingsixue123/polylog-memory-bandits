import Pool.P0173.Statement
import Pool.P0067.SubFixed
import Pool.P0144.AnyBase
import Pool.P0140.Base

/-!
# The main result from a one-level family with an explicit BASE term
-/

namespace Pool.P0278

open Pool.P0001 Pool.P0050 Pool.P0055 Pool.P0161 Pool.P0173

/-- **One-level family hypothesis.** For every admissible `n ≤ T` and rate `n/T ≤ q ≤ 1/32`, and every homogeneous
coin algorithm `A` (BASE), there is a homogeneous coin algorithm with at most `C·Lg^k` more bits whose regret over `T`
rounds is at most `C·Lg^k·√(nT/q)` plus `β ≤ 2γ` times the regret of `A` subsampled at a rate `γ` over `Tb` rounds, with
`γ·Tb ≤ q·T` and `Tb ≤ 2T` (on some loss sequence `ℓ'` that may depend on `ℓ`). This form is INTENDED to match P0217/P0258's machine bound with
`wB = γ`, the process horizon `Tb` and the BASE coefficient `wB + X₁ + κ ≤ 2·wB`; the match is CLAIMED, not proved
here (P0217/P0246 are stated at horizon `T + 1` on the shifted sequence and carry further additive terms). `FamHyp` is
UNIFORM in the rate `q`; the proof only uses the single rate of `FamHypAt` below, which is the weaker interface. -/
def FamHyp (C : ℝ) (k : ℕ) : Prop :=
  ∀ (n T : ℕ) (q : ℝ), 1 ≤ n → n ≤ T → (n : ℝ) / T ≤ q → q ≤ 1 / 32 →
    ∀ A : CoinAlg n, CoinHom A →
      ∃ M : CoinAlg n, CoinHom M ∧ M.toMachine.memBits ≤ A.toMachine.memBits + C * Lg n T ^ k ∧
        ∃ (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (β : ℝ) (Tb : ℕ), 0 < γ ∧ γ * Tb ≤ q * T ∧ Tb ≤ 2 * T ∧
          0 ≤ β ∧ β ≤ 2 * γ ∧
          ∀ ℓ : LossSeq n, ∃ ℓ' : LossSeq n,
            regret M.toMachine ℓ T ≤
              C * Lg n T ^ k * Real.sqrt (n * T / q) + β * regret (Sub A.toMachine γ h0 h1) ℓ' Tb

/-- **The family hypothesis at the single rate the proof uses**, `q = qOf (max C 0 + 6) k n T` (the rate of P0173's
`StepAtIn` with `c = max C 0 + 6`), required only when `n/T ≤ q`. Weaker than `FamHyp` (`famHypAt_of_famHyp`). -/
def FamHypAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ (n T : ℕ), 1 ≤ n → n ≤ T → (n : ℝ) / T ≤ qOf (max C 0 + 6) k n T →
    ∀ A : CoinAlg n, CoinHom A →
      ∃ M : CoinAlg n, CoinHom M ∧ M.toMachine.memBits ≤ A.toMachine.memBits + C * Lg n T ^ k ∧
        ∃ (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (β : ℝ) (Tb : ℕ), 0 < γ ∧ γ * Tb ≤ qOf (max C 0 + 6) k n T * T ∧
          Tb ≤ 2 * T ∧ 0 ≤ β ∧ β ≤ 2 * γ ∧
          ∀ ℓ : LossSeq n, ∃ ℓ' : LossSeq n,
            regret M.toMachine ℓ T ≤
              C * Lg n T ^ k * Real.sqrt (n * T / qOf (max C 0 + 6) k n T) +
                β * regret (Sub A.toMachine γ h0 h1) ℓ' Tb

theorem qOf_pos (c : ℝ) (k n T : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T) : 0 < qOf c k n T := by
  unfold qOf
  have := Pool.P0161.one_le_Lam (c := c) (k := k) hn hT
  positivity

theorem qOf_le (c : ℝ) (k n T : ℕ) (hn : 1 ≤ n) (hT : 1 ≤ T) : qOf c k n T ≤ 1 / 32 := by
  unfold qOf
  have h := Pool.P0161.one_le_Lam (c := c) (k := k) hn hT
  have h2 : 1 ≤ Lam c k n T ^ 2 := one_le_pow₀ h
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- `T·e^{−qT} ≤ 1/q`. -/
theorem T_exp_le {q : ℝ} (hq : 0 < q) (T : ℕ) : (T : ℝ) * Real.exp (-(q * T)) ≤ 1 / q := by
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have he := Real.add_one_le_exp (q * T)
  have hp := Real.exp_pos (q * T)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hp hq]
  nlinarith

/-- `1/q ≤ √(nT/q)` when `n/T ≤ q` and `n ≥ 1`. -/
theorem inv_le_sqrt {n T : ℕ} {q : ℝ} (hn : 1 ≤ n) (hT : 1 ≤ T) (hq : 0 < q) (hnq : (n : ℝ) / T ≤ q) :
    1 / q ≤ Real.sqrt (n * T / q) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  apply Real.le_sqrt_of_sq_le
  have h1 : 1 / q ≤ T := by
    rw [div_le_iff₀ hq]
    rw [div_le_iff₀ (by positivity)] at hnq
    nlinarith
  have h2 : (1 / q) ^ 2 = (1 / q) * (1 / q) := sq _
  have h3 : (n : ℝ) * T / q = (n * T) * (1 / q) := by ring
  rw [h2, h3]
  have : 0 ≤ 1 / q := by positivity
  apply mul_le_mul_of_nonneg_right _ this
  nlinarith

/-- **The step from the family hypothesis** (P0173's `StepAtIn` for homogeneous coin algorithms), with
`c = max C 0 + 6` and the same `k`. The BASE term is bounded by P0067's fixed-horizon subsampling bound at
`H = ⌈4qT⌉` (tail `x = qT`), and `Tb·e^{−qT} ≤ 2/q ≤ 2√(nT/q)`. -/
theorem stepAtIn_of_famHypAt {C : ℝ} {k : ℕ} (hF : FamHypAt C k) :
    StepAtIn (fun {n} M => CoinCls (n := n) M) (max C 0 + 6) k := by
  intro n T hn hnT hq MB hcls hMB RB hRB
  obtain ⟨A, hA, rfl⟩ := hcls
  haveI : NeZero n := ⟨by omega⟩
  have hT : 1 ≤ T := le_trans hn hnT
  set c := max C 0 + 6 with hc
  set q := qOf c k n T with hqdef
  have hq0 : 0 < q := qOf_pos c k n T hn hT
  obtain ⟨M, hM, hmem, γ, h0, h1, β, Tb, hγ, hγT, hTb, hβ0, hβ, hreg⟩ :=
    hF n T hn hnT hq A hA
  have hL1 : 1 ≤ Lg n T := Pool.P0161.one_le_Lg hn hT
  have hLk : 1 ≤ Lg n T ^ k := one_le_pow₀ hL1
  have hCc : C ≤ c := by rw [hc]; linarith [le_max_left C 0]
  have hc6 : max C 0 + 4 ≤ c := by rw [hc]; linarith
  refine ⟨M.toMachine, ⟨M, hM, rfl⟩, toMachine_isHomogeneous hM, ?_, fun ℓ => ?_⟩
  · refine hmem.trans ?_
    have : C * Lg n T ^ k ≤ c * Lg n T ^ k := mul_le_mul_of_nonneg_right hCc (by linarith)
    linarith
  · obtain ⟨ℓ', hℓ⟩ := hreg ℓ
    set H := ⌈4 * q * T⌉₊ with hH
    have hRB0 : 0 ≤ RB := by
      have := hRB (fun _ _ => false)
      rwa [Pool.P0144.regret_zero_seq] at this
    have hsub := Pool.P0067.regret_Sub_le_fixed A.toMachine (toMachine_isHomogeneous hA) hγ h1 ℓ' Tb H RB hRB0
      (fun ℓ'' m _ hmH => Pool.P0140.regret_prefix_le _ hRB ℓ'' hmH)
    have hHq : 4 * q * T ≤ H := Nat.le_ceil _
    have htail := Pool.P0067.tail_le_exp h0 Tb H (x := q * T) (by linarith)
    have hTb' : (Tb : ℝ) ≤ 2 * T := by exact_mod_cast hTb
    have hexp : (Tb : ℝ) * Real.exp (-(q * T)) ≤ 2 / q := by
      have := T_exp_le hq0 T
      have he := (Real.exp_pos (-(q * T))).le
      calc (Tb : ℝ) * Real.exp (-(q * T)) ≤ (2 * T) * Real.exp (-(q * T)) := mul_le_mul_of_nonneg_right hTb' he
        _ = 2 * (T * Real.exp (-(q * T))) := by ring
        _ ≤ 2 * (1 / q) := by linarith
        _ = 2 / q := by ring
    have hS : regret (Sub A.toMachine γ h0 h1) ℓ' Tb ≤ (1 / γ) * (RB + 2 / q) := by
      refine hsub.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have : (Tb : ℝ) * ((1 + γ) ^ Tb / 2 ^ (H + 1)) ≤ Tb * Real.exp (-(q * T)) :=
        mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
      linarith
    have hβS : β * regret (Sub A.toMachine γ h0 h1) ℓ' Tb ≤ 2 * (RB + 2 / q) := by
      have hpos : 0 ≤ RB + 2 / q := by positivity
      calc β * regret (Sub A.toMachine γ h0 h1) ℓ' Tb ≤ β * ((1 / γ) * (RB + 2 / q)) :=
            mul_le_mul_of_nonneg_left hS hβ0
        _ = (β / γ) * (RB + 2 / q) := by ring
        _ ≤ 2 * (RB + 2 / q) := by
            apply mul_le_mul_of_nonneg_right _ hpos
            rw [div_le_iff₀ hγ]; linarith
    have hinv := inv_le_sqrt hn hT hq0 hq
    set s := Real.sqrt (n * T / q)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have h2q : 2 / q = 2 * (1 / q) := by ring
    -- assemble
    have hfin : C * Lg n T ^ k * s + 2 * (RB + 2 / q) ≤ c * Lg n T ^ k * (s + RB) := by
      have e1 : C * Lg n T ^ k * s ≤ max C 0 * Lg n T ^ k * s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hs0
      have e2 : 4 * s ≤ 4 * Lg n T ^ k * s := by nlinarith
      have e3 : 2 * RB ≤ 6 * Lg n T ^ k * RB := by nlinarith
      have e4 : 0 ≤ max C 0 * Lg n T ^ k * RB :=
        mul_nonneg (mul_nonneg (le_max_right _ _) (by linarith)) hRB0
      rw [hc, h2q]
      nlinarith
    linarith

/-- The uniform family hypothesis implies the single-rate one. -/
theorem famHypAt_of_famHyp {C : ℝ} {k : ℕ} (hF : FamHyp C k) : FamHypAt C k := by
  intro n T hn hnT hq A hA
  have hT : 1 ≤ T := le_trans hn hnT
  exact hF n T _ hn hnT hq (qOf_le _ k n T hn hT) A hA

theorem stepAtIn_of_famHyp {C : ℝ} {k : ℕ} (hF : FamHyp C k) :
    StepAtIn (fun {n} M => CoinCls (n := n) M) (max C 0 + 6) k :=
  stepAtIn_of_famHypAt (famHypAt_of_famHyp hF)

end Pool.P0278
