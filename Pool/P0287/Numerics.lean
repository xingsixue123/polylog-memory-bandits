import Pool.P0284.Memory
import Pool.P0079.Params

/-!
# Numerics of P0221's overflow bound at P0261's sizes

`ovfB_le`: for `1 ≤ n`, `1 ≤ T`, P0221/P0257's averaged overflow expression with P0261's sizes,
`T·D·δs + T·D·(Ld+1)·Kf·delta(|CpG n T|, qf, Rc, kk, M0)` with `δs = exp(e − 1 − (s0 + 1))` (P0261's `hs`), is at most
`1/(T+1)²`. Via `a = Lam n T`: `n·T < 2^a`, `|CpG| ≤ 2^(2a)`, `qf·kk = 32a²`, `M0 ≥ 4·Rc·kk`, `2^40 ≤ e^32`.
-/

namespace Pool.P0287

open Finset Pool.P0261

variable (n T : ℕ) [NeZero n]

theorem nT_lt : n * T < 2 ^ Lam n T := by
  unfold Lam; exact Nat.lt_pow_succ_log_self (by norm_num) _

theorem T_lt (hn : 1 ≤ n) : T < 2 ^ Lam n T := by
  have := nT_lt n T; nlinarith

theorem logT_le_Lam (hn : 1 ≤ n) : Nat.log 2 T + 1 ≤ Lam n T := by
  unfold Lam
  have : Nat.log 2 T ≤ Nat.log 2 (n * T) := Nat.log_mono_right (Nat.le_mul_of_pos_left _ (by omega))
  omega

theorem one_le_Lam : 1 ≤ Lam n T := by unfold Lam; omega

theorem card_le (hn : 1 ≤ n) : Fintype.card (CpG n T) ≤ 2 ^ (2 * Lam n T) := by
  have h1 : Fintype.card (CpG n T) ≤ T * Dn T * n := by
    calc Fintype.card (CpG n T) ≤ Fintype.card (Pool.P0121.TM.Cp n T (Dn T)) := Fintype.card_subtype_le _
      _ = T * Dn T * n := Fintype.card_fin _
  have h2 := nT_lt n T
  have h3 : Dn T ≤ Lam n T := by have := logT_le_Lam n T hn; unfold Dn Dp; omega
  have h4 : Lam n T ≤ 2 ^ Lam n T := Nat.lt_two_pow_self.le
  calc Fintype.card (CpG n T) ≤ (n * T) * Dn T := by nlinarith
    _ ≤ 2 ^ Lam n T * 2 ^ Lam n T := Nat.mul_le_mul h2.le (h3.trans h4)
    _ = 2 ^ (2 * Lam n T) := by rw [← pow_add]; ring_nf

/-- `2^40 ≤ e^32`. -/
theorem two_pow40_le : (2 : ℝ) ^ 40 ≤ Real.exp 32 := by
  have h := Real.exp_one_gt_d9
  have h1 : (2.7 : ℝ) ^ 32 ≤ Real.exp 1 ^ 32 := pow_le_pow_left₀ (by norm_num) (by linarith) 32
  rw [← Real.exp_nat_mul] at h1
  norm_num at h1
  refine le_trans ?_ h1
  norm_num

/-- `2^(40 a²) ≤ e^(32 a²)`. -/
theorem two_pow_le_exp (a : ℕ) : (2 : ℝ) ^ (40 * a ^ 2) ≤ Real.exp (32 * a ^ 2) := by
  rw [pow_mul, show (32 : ℝ) * a ^ 2 = (a ^ 2 : ℕ) * 32 by push_cast; ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) two_pow40_le _

/-- The natural-number core: the weight `(N+1)·R·N + Σ_{m<R} N^m + 1 ≤ 2^(2a²+3a+3)`. -/
theorem W_le (N R a : ℕ) (ha : 1 ≤ a) (hN : N ≤ 2 ^ (2 * a)) (hR : R ≤ a + 1) :
    (N + 1) * R * N + ∑ m ∈ range R, N ^ m + 1 ≤ 2 ^ (2 * a ^ 2 + 3 * a + 3) := by
  have ha2 : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
  have hR2 : R ≤ 2 ^ a := hR.trans ha2
  have h1 : 1 ≤ 2 ^ (2 * a) := Nat.one_le_two_pow
  have hs : ∑ m ∈ range R, N ^ m ≤ 2 ^ a * 2 ^ (2 * a ^ 2 + 2 * a) := by
    calc ∑ m ∈ range R, N ^ m ≤ ∑ _m ∈ range R, (2 ^ (2 * a)) ^ (a + 1) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' : m ≤ a + 1 := by rw [Finset.mem_range] at hm; omega
          calc N ^ m ≤ (2 ^ (2 * a)) ^ m := Nat.pow_le_pow_left hN m
            _ ≤ (2 ^ (2 * a)) ^ (a + 1) := Nat.pow_le_pow_right h1 hm'
      _ = R * (2 ^ (2 * a)) ^ (a + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ 2 ^ a * 2 ^ (2 * a ^ 2 + 2 * a) := by
          rw [← pow_mul]; exact Nat.mul_le_mul hR2 (le_of_eq (by ring_nf))
  have hN1 : N + 1 ≤ 2 ^ (2 * a + 1) := by rw [pow_succ]; omega
  have hp : (N + 1) * R * N ≤ 2 ^ (2 * a + 1) * 2 ^ a * 2 ^ (2 * a) :=
    Nat.mul_le_mul (Nat.mul_le_mul hN1 hR2) hN
  have e1 : 2 ^ (2 * a + 1) * 2 ^ a * 2 ^ (2 * a) = 2 ^ (5 * a + 1) := by
    rw [← pow_add, ← pow_add]; ring_nf
  have e2 : 2 ^ a * 2 ^ (2 * a ^ 2 + 2 * a) = 2 ^ (2 * a ^ 2 + 3 * a) := by rw [← pow_add]; ring_nf
  rw [e1] at hp; rw [e2] at hs
  have h5 : 2 ^ (5 * a + 1) ≤ 2 ^ (2 * a ^ 2 + 3 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h6 : 2 ^ (2 * a ^ 2 + 3 * a) ≤ 2 ^ (2 * a ^ 2 + 3 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h7 : 1 ≤ 2 ^ (2 * a ^ 2 + 3 * a + 1) := Nat.one_le_two_pow
  have e3 : 2 ^ (2 * a ^ 2 + 3 * a + 3) = 4 * 2 ^ (2 * a ^ 2 + 3 * a + 1) := by
    rw [show 2 * a ^ 2 + 3 * a + 3 = 2 + (2 * a ^ 2 + 3 * a + 1) by ring, pow_add]; norm_num
  omega


/-- The δs part: `T·D·exp(e − 1 − (s0 + 1)) ≤ 1/(2(T+1)²)`. -/
theorem part1_le (hn : 1 ≤ n) :
    (T : ℝ) * Dn T * Real.exp (Real.exp 1 - 1 - (s0 n T + 1)) ≤ 1 / (2 * ((T : ℝ) + 1) ^ 2) := by
  set a := Lam n T with ha_def
  have ha1 : 1 ≤ a := one_le_Lam n T
  have hT := T_lt n T hn
  have hD : Dn T ≤ a := by have := logT_le_Lam n T hn; unfold Dn Dp; omega
  have h2a : 2 * a ≤ 2 ^ a := by
    have := Nat.lt_two_pow_self (n := a - 1)
    have e : 2 ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ', Nat.sub_add_cancel ha1]
    omega
  -- natural core: 2·T·D·(T+1)² ≤ 2^(4a)
  have hX : 2 * T * Dn T * (T + 1) ^ 2 ≤ 2 ^ (4 * a) := by
    have h1 : T + 1 ≤ 2 ^ a := hT
    calc 2 * T * Dn T * (T + 1) ^ 2 = T * (2 * Dn T) * (T + 1) ^ 2 := by ring
      _ ≤ 2 ^ a * 2 ^ a * (2 ^ a) ^ 2 := by
          gcongr <;> omega
      _ = 2 ^ (4 * a) := by rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
  have hXr : (2 : ℝ) * T * Dn T * ((T : ℝ) + 1) ^ 2 ≤ (2 : ℝ) ^ (4 * a) := by exact_mod_cast hX
  have h2e : (2 : ℝ) ^ (4 * a) ≤ Real.exp (4 * a) := by
    rw [show (4 : ℝ) * a = ((4 * a : ℕ) : ℝ) * 1 by push_cast; ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp 1]) _
  have hs0 : (s0 n T : ℝ) = 4 * a + 2 := by unfold s0; push_cast; ring
  have he4 : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
  have hexp : Real.exp (4 * a) * Real.exp (Real.exp 1 - 1 - (s0 n T + 1)) ≤ 1 := by
    rw [← Real.exp_add, hs0]
    rw [Real.exp_le_one_iff]; linarith
  have hpos : (0 : ℝ) < 2 * ((T : ℝ) + 1) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have hE0 : 0 ≤ Real.exp (Real.exp 1 - 1 - (s0 n T + 1)) := (Real.exp_pos _).le
  calc (T : ℝ) * Dn T * Real.exp (Real.exp 1 - 1 - (s0 n T + 1)) * (2 * ((T : ℝ) + 1) ^ 2)
      = ((2 : ℝ) * T * Dn T * ((T : ℝ) + 1) ^ 2) * Real.exp (Real.exp 1 - 1 - (s0 n T + 1)) := by ring
    _ ≤ Real.exp (4 * a) * Real.exp (Real.exp 1 - 1 - (s0 n T + 1)) :=
        mul_le_mul_of_nonneg_right (hXr.trans h2e) hE0
    _ ≤ 1 := hexp

/-- `P0042.delta ≤ W·e^{−32a²}` at P0261's sizes. -/
theorem delta_le_W (hn : 1 ≤ n) :
    Pool.P0042.delta (Fintype.card (CpG n T)) (qf n T) (Rc T) (kk n T) (M0 n T) ≤
      (((Fintype.card (CpG n T) + 1) * Rc T * Fintype.card (CpG n T) +
        ∑ m ∈ range (Rc T), Fintype.card (CpG n T) ^ m + 1 : ℕ) : ℝ) * Real.exp (-(32 * (Lam n T : ℝ) ^ 2)) := by
  set N := Fintype.card (CpG n T)
  have hQ : (64 : ℝ) ≤ Qd n T := by
    have := Qd_ge n T; have := Rc_pos T
    have : (1 : ℝ) ≤ Rc T := by exact_mod_cast Rc_pos T
    linarith
  have hQ0 : (0 : ℝ) < Qd n T := by linarith
  have hpk : qf n T * (kk n T : ℝ) = 32 * (Lam n T : ℝ) ^ 2 := by
    unfold qf kk; push_cast; field_simp
  have hpow : (1 - qf n T) ^ kk n T ≤ Real.exp (-(32 * (Lam n T : ℝ) ^ 2)) := by
    have := Pool.P0079.one_sub_pow_le_exp (qf_mem n T).1 (qf_mem n T).2 (kk n T)
    rwa [hpk] at this
  have hR : (0 : ℝ) < Rc T := by exact_mod_cast Rc_pos T
  have hM : (32 * (Lam n T : ℝ) ^ 2) ≤ (M0 n T : ℝ) / (32 * Rc T) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 := hk n T
    have hkk : (kk n T : ℝ) = 32 * (Lam n T : ℝ) ^ 2 * Qd n T := by unfold kk; push_cast; ring
    rw [hkk] at h1
    have : (0 : ℝ) ≤ (Lam n T : ℝ) ^ 2 := by positivity
    nlinarith
  have h3 : Real.exp (-((M0 n T : ℝ) / (32 * (Rc T : ℕ)))) ≤ Real.exp (-(32 * (Lam n T : ℝ) ^ 2)) :=
    Real.exp_le_exp.2 (by push_cast; linarith)
  have hE := (Real.exp_pos (-(32 * (Lam n T : ℝ) ^ 2))).le
  unfold Pool.P0042.delta
  push_cast
  have hs0 : (0 : ℝ) ≤ ∑ m ∈ range (Rc T), (N : ℝ) ^ m := Finset.sum_nonneg fun _ _ => by positivity
  have hA : (0 : ℝ) ≤ ((N : ℝ) + 1) * Rc T * N := by positivity
  have hp1 := mul_le_mul_of_nonneg_left hpow hA
  have hp2 := mul_le_mul_of_nonneg_left hpow hs0
  nlinarith [h3]

/-- **The overflow expression at P0261's sizes is `≤ 1/(T+1)²`.** -/
theorem ovfB_le (hn : 1 ≤ n) (hT1 : 1 ≤ T) :
    (T : ℝ) * Dn T * Real.exp (Real.exp 1 - 1 - (s0 n T + 1)) +
      (T : ℝ) * Dn T * ((Ld T : ℝ) + 1) * Kf n T *
        Pool.P0042.delta (Fintype.card (CpG n T)) (qf n T) (Rc T) (kk n T) (M0 n T) ≤
      1 / ((T : ℝ) + 1) ^ 2 := by
  set a := Lam n T with ha_def
  have ha1 : 1 ≤ a := one_le_Lam n T
  have hT := T_lt n T hn
  have hL := logT_le_Lam n T hn
  have hD : Dn T ≤ a := by unfold Dn Dp; omega
  have hLd : Ld T + 1 ≤ a + 1 := by unfold Ld; omega
  have hRc : Rc T ≤ a + 1 := by unfold Rc; omega
  have hpa : a + 1 ≤ 2 ^ a := Nat.lt_two_pow_self
  have hKf : Kf n T ≤ 2 ^ (2 * a + 3) := by
    unfold Kf
    calc 4 * Rc T * (2 * (Lam n T + 1)) ≤ 4 * (a + 1) * (2 * (a + 1)) := by rw [← ha_def]; gcongr
      _ = 8 * ((a + 1) * (a + 1)) := by ring
      _ ≤ 8 * (2 ^ a * 2 ^ a) := by gcongr
      _ = 2 ^ (2 * a + 3) := by rw [← pow_add]; ring_nf
  have hN := card_le n T hn
  have hW := W_le (Fintype.card (CpG n T)) (Rc T) a ha1 hN hRc
  have hdel := delta_le_W n T hn
  rw [← ha_def] at hdel
  generalize (Fintype.card (CpG n T) + 1) * Rc T * Fintype.card (CpG n T) +
    ∑ m ∈ range (Rc T), Fintype.card (CpG n T) ^ m + 1 = W at hW hdel
  -- natural core
  have hX : 2 * T * Dn T * (Ld T + 1) * Kf n T * (T + 1) ^ 2 * W ≤ 2 ^ (40 * a ^ 2) := by
    calc 2 * T * Dn T * (Ld T + 1) * Kf n T * (T + 1) ^ 2 * W
        ≤ 2 * 2 ^ a * 2 ^ a * 2 ^ a * 2 ^ (2 * a + 3) * (2 ^ a) ^ 2 * 2 ^ (2 * a ^ 2 + 3 * a + 3) := by
          gcongr <;> first | omega | assumption
      _ = 2 ^ (2 * a ^ 2 + 10 * a + 7) := by
          rw [← pow_mul]; simp only [← pow_add, ← pow_succ']; ring_nf
      _ ≤ 2 ^ (40 * a ^ 2) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hXr : (2 : ℝ) * T * Dn T * ((Ld T : ℝ) + 1) * Kf n T * ((T : ℝ) + 1) ^ 2 * (W : ℝ) ≤
      (2 : ℝ) ^ (40 * a ^ 2) := by exact_mod_cast hX
  have hexp : (2 : ℝ) ^ (40 * a ^ 2) * Real.exp (-(32 * (a : ℝ) ^ 2)) ≤ 1 := by
    have h := two_pow_le_exp a
    have : Real.exp (32 * (a : ℝ) ^ 2) * Real.exp (-(32 * (a : ℝ) ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    calc (2 : ℝ) ^ (40 * a ^ 2) * Real.exp (-(32 * (a : ℝ) ^ 2))
        ≤ Real.exp (32 * (a : ℝ) ^ 2) * Real.exp (-(32 * (a : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = 1 := this
  have h1 := part1_le n T hn
  have hpos : (0 : ℝ) < 2 * ((T : ℝ) + 1) ^ 2 := by positivity
  have h2 : (T : ℝ) * Dn T * ((Ld T : ℝ) + 1) * Kf n T *
      Pool.P0042.delta (Fintype.card (CpG n T)) (qf n T) (Rc T) (kk n T) (M0 n T) ≤
      1 / (2 * ((T : ℝ) + 1) ^ 2) := by
    rw [le_div_iff₀ hpos]
    have hc : (0 : ℝ) ≤ (T : ℝ) * Dn T * ((Ld T : ℝ) + 1) * Kf n T := by positivity
    calc (T : ℝ) * Dn T * ((Ld T : ℝ) + 1) * Kf n T *
          Pool.P0042.delta (Fintype.card (CpG n T)) (qf n T) (Rc T) (kk n T) (M0 n T) * (2 * ((T : ℝ) + 1) ^ 2)
        ≤ (T : ℝ) * Dn T * ((Ld T : ℝ) + 1) * Kf n T * ((W : ℝ) * Real.exp (-(32 * (a : ℝ) ^ 2))) *
            (2 * ((T : ℝ) + 1) ^ 2) := by gcongr
      _ = ((2 : ℝ) * T * Dn T * ((Ld T : ℝ) + 1) * Kf n T * ((T : ℝ) + 1) ^ 2 * (W : ℝ)) *
            Real.exp (-(32 * (a : ℝ) ^ 2)) := by ring
      _ ≤ (2 : ℝ) ^ (40 * a ^ 2) * Real.exp (-(32 * (a : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hXr (Real.exp_pos _).le
      _ ≤ 1 := hexp
  have : 1 / (2 * ((T : ℝ) + 1) ^ 2) + 1 / (2 * ((T : ℝ) + 1) ^ 2) = 1 / ((T : ℝ) + 1) ^ 2 := by
    field_simp; ring
  linarith

end Pool.P0287
