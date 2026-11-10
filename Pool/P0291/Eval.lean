import Pool.P0290.Instance

/-!
# The ALG term of the one-level machine is `Õ(√(nT/q))` (arithmetic of P0281's right-hand side at P0284's family)
-/

namespace Pool.P0291
open Finset Pool.P0261 Pool.P0284 Pool.P0194 Pool.P0290
open scoped Pool.P0290
variable (n T : ℕ) [NeZero n] (q : ℝ)

/-- The polylog scale (P0284's `BB = Lam n Tp + 3`) as a real. -/
noncomputable abbrev Λ : ℝ := (BB n T : ℝ)
theorem Λ_ge : 1 ≤ Λ n T := by unfold Λ; exact_mod_cast BB_pos n T
theorem Dn_le : (Dn (Tp T) : ℝ) ≤ Λ n T := by unfold Λ; exact_mod_cast Dn_le' NeZero.one_le
theorem Lv_le : (Lv (Tp T) : ℝ) ≤ Λ n T := by unfold Λ; exact_mod_cast Lv_le' NeZero.one_le
theorem Ld_le : (Ld (Tp T) : ℝ) ≤ Λ n T := by unfold Λ; exact_mod_cast Ld_le' NeZero.one_le
theorem Rc_le : (Rc (Tp T) : ℝ) ≤ Λ n T := by unfold Λ; exact_mod_cast Rc_le' NeZero.one_le
theorem LA_le : (LA T : ℝ) ≤ Λ n T + 1 := by
  unfold Λ LA; have := clog_le_BB n T; push_cast; exact_mod_cast (show Nat.clog 2 T + 1 ≤ BB n T + 1 by omega)
theorem Sl_le_r : (Sl n (Tp T) : ℝ) ≤ 600000 * Λ n T ^ 11 := by
  unfold Λ; exact_mod_cast Sl_le NeZero.one_le
theorem Sp_le_r : (Sp n (Tp T) : ℝ) ≤ 196918 * Λ n T ^ 8 := by
  unfold Λ; exact_mod_cast Sp_le NeZero.one_le
theorem s0_le_r : (s0 n (Tp T) : ℝ) ≤ 6 * Λ n T := by unfold Λ; exact_mod_cast s0_le
theorem Ns_le_r : (Dn (Tp T) : ℝ) * Sl n (Tp T) ≤ 600000 * Λ n T ^ 12 := by
  unfold Λ; exact_mod_cast Ns_le NeZero.one_le

/-- `log X ≤ k` when `X ≤ 2^k` (natural logarithm, `log 2 ≤ 1`). -/
theorem log_le_of_le_pow {x : ℝ} {k : ℕ} (hx : 0 < x) (h : x ≤ 2 ^ k) : Real.log x ≤ k := by
  have h1 : Real.log x ≤ Real.log ((2 : ℝ) ^ k) := Real.log_le_log hx h
  rw [Real.log_pow] at h1
  have h2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have h3 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith
theorem Lx_le : Lx n T ≤ 12 * Λ n T := by
  have hB := BB_pos n T
  have hT := Tp_le_pow n T
  have hc := card_ι_le n T
  unfold Lx
  have h1 : Real.log ((Tp T : ℝ) + 1) ≤ (BB n T + 1 : ℕ) := by
    apply log_le_of_le_pow (by positivity)
    have : Tp T + 1 ≤ 2 ^ (BB n T + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := BB n T); omega
    exact_mod_cast this
  have h2 : Real.log (4 * (Fintype.card (CpG n (Tp T)) : ℝ) + 4) ≤ (3 * BB n T + 3 : ℕ) := by
    apply log_le_of_le_pow (by positivity)
    have : 4 * Fintype.card (CpG n (Tp T)) + 4 ≤ 2 ^ (3 * BB n T + 3) := by
      rw [pow_add]; have := Nat.one_le_two_pow (n := 3 * BB n T); omega
    exact_mod_cast this
  unfold Λ; push_cast at h1 h2
  have : (1 : ℝ) ≤ BB n T := by exact_mod_cast hB
  linarith
theorem logSpec_le :
    Real.log (Fintype.card (Pool.P0089.Spec (Option (CpG n (Tp T))) (LA T))) ≤ 12 * Λ n T := by
  have hB := BB_pos n T
  have hc := card_ι_le n T
  have hL : LA T ≤ BB n T + 1 := by unfold LA; have := clog_le_BB n T; omega
  have hcard : Fintype.card (Pool.P0089.Spec (Option (CpG n (Tp T))) (LA T)) ≤ 2 ^ (6 * BB n T + 4) := by
    simp only [Pool.P0089.Spec, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    have h1 : Fintype.card (CpG n (Tp T)) + 1 ≤ 2 ^ (3 * BB n T + 1) := by
      rw [pow_succ]; have := Nat.one_le_two_pow (n := 3 * BB n T); omega
    have h2 : LA T + 1 ≤ 2 ^ (BB n T + 2) := by
      have := (Nat.lt_two_pow_self (n := BB n T + 2)); omega
    have h3 : 2 ^ LA T ≤ 2 ^ (BB n T + 1) := Nat.pow_le_pow_right (by norm_num) hL
    calc (Fintype.card (CpG n (Tp T)) + 1) * ((LA T + 1) * 2 ^ LA T)
        ≤ 2 ^ (3 * BB n T + 1) * (2 ^ (BB n T + 2) * 2 ^ (BB n T + 1)) := by gcongr
      _ = 2 ^ (5 * BB n T + 4) := by rw [← pow_add, ← pow_add]; ring_nf
      _ ≤ 2 ^ (6 * BB n T + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : (0 : ℝ) < Fintype.card (Pool.P0089.Spec (Option (CpG n (Tp T))) (LA T)) := by
    exact_mod_cast Fintype.card_pos
  have := log_le_of_le_pow hpos (by exact_mod_cast hcard)
  unfold Λ; push_cast at this
  have : (1 : ℝ) ≤ BB n T := by exact_mod_cast hB
  linarith

section Scale
variable (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (hnq : (n : ℝ) / T ≤ q)
include hn hnT hq hq1 hnq

/-- The target scale `Q = √(nT/q)` (P0278's). -/
noncomputable abbrev Q : ℝ := Real.sqrt (n * T / q)
theorem n_div_q_le : (n : ℝ) / q ≤ Q n T q := by
  have hT : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnq' : (n : ℝ) ≤ q * T := by rw [div_le_iff₀ hT] at hnq; linarith
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, show (n : ℝ) * T / q = n * T * q / q ^ 2 by field_simp]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith
theorem one_div_q_le : 1 / q ≤ Q n T q := by
  have h := n_div_q_le n T q hn hnT hq hq1 hnq
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : 1 / q ≤ (n : ℝ) / q := div_le_div_of_nonneg_right hn' hq.le
  linarith
theorem Q_ge_one : 1 ≤ Q n T q := by
  have h := one_div_q_le n T q hn hnT hq hq1 hnq
  have : 1 ≤ 1 / q := by rw [le_div_iff₀ hq]; linarith
  linarith

/-- `√(n·X) ≤ √2·Q` for `X ≤ Tp/q` (with `Tp ≤ 2T`). -/
theorem sqrt_le_Q {X : ℝ} (hX : X ≤ (Tp T : ℝ) / q) : Real.sqrt (n * X) ≤ 2 * Q n T q := by
  have hT1 : 1 ≤ T := le_trans hn hnT
  have hTp : (Tp T : ℝ) ≤ 2 * T := by exact_mod_cast Tp_le T hT1
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc Real.sqrt (n * X) ≤ Real.sqrt (4 * (n * T / q)) := by
        apply Real.sqrt_le_sqrt
        have : (Tp T : ℝ) / q ≤ 2 * T / q := div_le_div_of_nonneg_right hTp hq.le
        have h2 : (n : ℝ) * X ≤ n * (2 * T / q) := mul_le_mul_of_nonneg_left (hX.trans this) hn'
        have h3 : (n : ℝ) * (2 * T / q) ≤ 4 * (n * T / q) := by
          rw [show (n : ℝ) * (2 * T / q) = 2 * (n * T / q) by ring]
          have : 0 ≤ (n : ℝ) * T / q := by positivity
          linarith
        linarith
    _ = 2 * Q n T q := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `s = √(qTp/n)`: `n·s ≤ 2Q`, `s ≤ 2Q`, `Tp/s ≤ 2Q`, `√(Tp/n) ≤ 2Q`, `n√(Tp/n) ≤ 2Q`. -/
theorem s_facts : n * sA n T q ≤ 2 * Q n T q ∧ sA n T q ≤ 2 * Q n T q ∧ (Tp T : ℝ) / sA n T q ≤ 2 * Q n T q ∧
    Real.sqrt ((Tp T : ℝ) / n) ≤ 2 * Q n T q ∧ n * Real.sqrt ((Tp T : ℝ) / n) ≤ 2 * Q n T q := by
  have hT1 : 1 ≤ T := le_trans hn hnT
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTp0 : (0 : ℝ) < Tp T := by exact_mod_cast Tp_pos T
  have hs1 := one_le_sA n T q hT1 hnq
  have hsq : sA n T q ^ 2 = q * Tp T / n := Real.sq_sqrt (by positivity)
  -- n·s = √(n·(q·Tp))
  have e1 : (n : ℝ) * sA n T q = Real.sqrt (n * (q * Tp T)) := by
    unfold Pool.P0284.sA
    rw [show (n : ℝ) * (q * Tp T) = n ^ 2 * (q * Tp T / n) by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hn'.le]
  have hqT : q * Tp T ≤ (Tp T : ℝ) / q := by
    rw [le_div_iff₀ hq]
    have hqq : q * q ≤ 1 := by nlinarith
    calc q * Tp T * q = (q * q) * Tp T := by ring
      _ ≤ 1 * Tp T := mul_le_mul_of_nonneg_right hqq hTp0.le
      _ = Tp T := one_mul _
  have k1 : (n : ℝ) * sA n T q ≤ 2 * Q n T q := by rw [e1]; exact sqrt_le_Q n T q hn hnT hq hq1 hnq hqT
  have k2 : sA n T q ≤ 2 * Q n T q := by
    have : sA n T q ≤ n * sA n T q := by nlinarith
    linarith
  have k3 : (Tp T : ℝ) / sA n T q ≤ 2 * Q n T q := by
    have hQ0 : 0 ≤ Q n T q := Real.sqrt_nonneg _
    have hTp2 : (Tp T : ℝ) ≤ 2 * T := by exact_mod_cast Tp_le T hT1
    have hsq2 : ((Tp T : ℝ) / sA n T q) ^ 2 ≤ (2 * Q n T q) ^ 2 := by
      rw [div_pow, hsq, mul_pow, Real.sq_sqrt (by positivity)]
      rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
      have hT0 : (0 : ℝ) ≤ T := by linarith
      have : (Tp T : ℝ) ^ 2 * n ≤ 2 ^ 2 * (n * T / q) * (q * Tp T) := by
        rw [show (2 : ℝ) ^ 2 * (n * T / q) * (q * Tp T) = 4 * (n * T * Tp T) by field_simp; norm_num]
        have := mul_le_mul_of_nonneg_right hTp2 (by positivity : (0 : ℝ) ≤ (Tp T : ℝ) * n)
        nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hsq2
  have hTn : (Tp T : ℝ) / n ≤ (Tp T : ℝ) / q := by
    apply div_le_div_of_nonneg_left hTp0.le hq; linarith
  have e5 : (n : ℝ) * Real.sqrt ((Tp T : ℝ) / n) = Real.sqrt (n * Tp T) := by
    rw [show (n : ℝ) * Tp T = n ^ 2 * (Tp T / n) by field_simp, Real.sqrt_mul (by positivity), Real.sqrt_sq hn'.le]
  have hTq : (Tp T : ℝ) ≤ (Tp T : ℝ) / q := by
    rw [le_div_iff₀ hq]; nlinarith
  have k5 : (n : ℝ) * Real.sqrt ((Tp T : ℝ) / n) ≤ 2 * Q n T q := by
    rw [e5]; exact sqrt_le_Q n T q hn hnT hq hq1 hnq hTq
  have k4 : Real.sqrt ((Tp T : ℝ) / n) ≤ 2 * Q n T q := by
    have : Real.sqrt ((Tp T : ℝ) / n) ≤ n * Real.sqrt ((Tp T : ℝ) / n) := by
      have := Real.sqrt_nonneg ((Tp T : ℝ) / n); nlinarith
    linarith
  exact ⟨k1, k2, k3, k4, k5⟩

end Scale

section Consts
variable (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (hnq : (n : ℝ) / T ≤ q)
include hn hnT hq hq1 hnq
theorem KcF_le_r : (KcF n T q : ℝ) ≤ 4800000 * Λ n T ^ 13 / q := by
  have hK1 : (Kq q : ℝ) ≤ 2 / q := by
    have h1 : (Kq q : ℝ) < 1 / q + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 1 ≤ 1 / q := by rw [le_div_iff₀ hq]; linarith
    have : 1 / q + 1 ≤ 2 / q := by rw [show (2 : ℝ) / q = 1 / q + 1 / q by ring]; linarith
    linarith
  have hD := Dn_le n T
  have hS := Sl_le_r n T
  have hΛ := Λ_ge n T
  have e : (KcF n T q : ℝ) = 4 * (Dn (Tp T) : ℝ) ^ 2 * Sl n (Tp T) * Kq q := by unfold KcF Kc; push_cast; ring
  rw [e]
  have hD0 : (0 : ℝ) ≤ Dn (Tp T) := Nat.cast_nonneg _
  calc 4 * (Dn (Tp T) : ℝ) ^ 2 * Sl n (Tp T) * Kq q ≤ 4 * Λ n T ^ 2 * (600000 * Λ n T ^ 11) * (2 / q) := by
        gcongr
    _ = 4800000 * Λ n T ^ 13 / q := by ring
theorem Bm_le_r : (Bm n (Tp T) : ℝ) ≤ Real.sqrt ((Tp T : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply Real.le_sqrt_of_sq_le
  rcases Bm_sq_le n (Tp T) with h | h
  · have h1 : ((Bm n (Tp T) * Bm n (Tp T) : ℕ) : ℝ) ≤ ((Tp T / n : ℕ) : ℝ) := by exact_mod_cast h
    have h2 : ((Tp T / n : ℕ) : ℝ) ≤ (Tp T : ℝ) / n := Nat.cast_div_le
    push_cast at h1; nlinarith
  · have hB : Bm n (Tp T) = 1 := by unfold Bm; rw [h]; simp
    rw [hB, le_div_iff₀ hn']; push_cast
    have : n ≤ Tp T := hnT.trans (le_Tp T)
    have : (n : ℝ) ≤ Tp T := by exact_mod_cast this
    linarith
theorem θc_le_r : (θc n (Tp T) (Kq q) : ℝ) ≤ 4800000 * Λ n T ^ 13 / q + Real.sqrt ((Tp T : ℝ) / n) := by
  have h1 := KcF_le_r n T q hn hnT hq hq1 hnq
  have h2 := Bm_le_r n T q hn hnT hq hq1 hnq
  have e : (θc n (Tp T) (Kq q) : ℝ) = max (KcF n T q : ℝ) (Bm n (Tp T) : ℝ) := by
    unfold θc KcF; push_cast; rfl
  rw [e]
  have h0 : (0 : ℝ) ≤ Real.sqrt ((Tp T : ℝ) / n) := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) ≤ 4800000 * Λ n T ^ 13 / q := by have := Λ_ge n T; positivity
  exact max_le (by linarith) (by linarith)

end Consts
theorem comb_arith (L th s r : ℝ) (hL : 1 ≤ L) (hth : 0 ≤ th) (hs : 1 ≤ s) (hr : 0 ≤ r) :
    th + L * (164 * L ^ 2 * s) + (2 * L) * (24 * L * th + 10 * L * r) + 12 * L * s ≤
      200 * L ^ 3 * (th + s + r) := by
  have h3 : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL
  have h2 : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL (by norm_num)
  have h1 : L ≤ L ^ 3 := by simpa using pow_le_pow_right₀ hL (show 1 ≤ 3 by norm_num)
  have a1 : th ≤ L ^ 3 * th := by nlinarith
  have a2 : L * (164 * L ^ 2 * s) = 164 * L ^ 3 * s := by ring
  have a3 : (2 * L) * (24 * L * th + 10 * L * r) = 48 * L ^ 2 * th + 20 * L ^ 2 * r := by ring
  have a4 : L ^ 2 * th ≤ L ^ 3 * th := mul_le_mul_of_nonneg_right h2 hth
  have a5 : L ^ 2 * r ≤ L ^ 3 * r := mul_le_mul_of_nonneg_right h2 hr
  have a6 : L * s ≤ L ^ 3 * s := mul_le_mul_of_nonneg_right h1 (by linarith)
  rw [a2, a3]; nlinarith
theorem fin_arith (L th s r iq : ℝ) (hL : 1 ≤ L) (hth : 0 ≤ th) (hs : 0 ≤ s) (hr : 0 ≤ r) (hiq : 0 ≤ iq)
    (hθ : th ≤ 4800000 * L ^ 13 * iq + r) :
    200 * L ^ 3 * (th + s + r) ≤ 1000000000 * L ^ 16 * (iq + r + s) := by
  have h13 : (1 : ℝ) ≤ L ^ 13 := one_le_pow₀ hL
  have hX : th + s + r ≤ 4800000 * L ^ 13 * (iq + r + s) := by nlinarith
  have hL3 : 0 ≤ L ^ 3 := by positivity
  calc 200 * L ^ 3 * (th + s + r) ≤ 200 * L ^ 3 * (4800000 * L ^ 13 * (iq + r + s)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = 960000000 * L ^ 16 * (iq + r + s) := by ring
    _ ≤ 1000000000 * L ^ 16 * (iq + r + s) := by
        have : 0 ≤ L ^ 16 * (iq + r + s) := by positivity
        nlinarith

section APBP
variable (A : Pool.P0050.CoinAlg n)
variable (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (hnq : (n : ℝ) / T ≤ q)
include hn hnT hq hq1 hnq
theorem ηA_eq : ηA n T q = 1 / sA n T q := by
  have hs := one_le_sA n T q (le_trans hn hnT) hnq
  unfold ηA; rw [max_eq_right hs]
theorem αT_le : Pool.P0226.αT (ι := CpG n (Tp T)) (ηA n T q) (LA T) (Tp T) (εA n T q) ≤
    70 * Λ n T ^ 2 * sA n T q := by
  have hs := one_le_sA n T q (le_trans hn hnT) hnq
  have hη := ηA_eq n T q hn hnT hq hq1 hnq
  have hTp : (0 : ℝ) < Tp T := by exact_mod_cast Tp_pos T
  have hlog := logSpec_le n T
  have hL := LA_le n T
  have hΛ := Λ_ge n T
  have hlog0 : 0 ≤ Real.log (Fintype.card (Pool.P0089.Spec (Option (CpG n (Tp T))) (LA T))) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  unfold Pool.P0226.αT
  have e : (2 * (LA T : ℝ) + 1) * (Real.log (Fintype.card (Pool.P0089.Spec (Option (CpG n (Tp T))) (LA T))) +
      2 * εA n T q * Tp T) / ηA n T q =
      (2 * (LA T : ℝ) + 1) * (Real.log (Fintype.card (Pool.P0089.Spec (Option (CpG n (Tp T))) (LA T))) * sA n T q
        + 2) := by
    unfold εA; rw [hη]; field_simp
  rw [e]
  have h1 : (2 * (LA T : ℝ) + 1) ≤ 5 * Λ n T := by linarith
  have h2 : Real.log (Fintype.card (Pool.P0089.Spec (Option (CpG n (Tp T))) (LA T))) * sA n T q + 2 ≤
      14 * Λ n T * sA n T q := by nlinarith
  have h0 : (0 : ℝ) ≤ 2 * (LA T : ℝ) + 1 := by positivity
  calc (2 * (LA T : ℝ) + 1) * (Real.log (Fintype.card (Pool.P0089.Spec (Option (CpG n (Tp T))) (LA T))) *
        sA n T q + 2) ≤ (5 * Λ n T) * (14 * Λ n T * sA n T q) := mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 70 * Λ n T ^ 2 * sA n T q := by ring
set_option maxHeartbeats 1000000 in
theorem APF_le : APF n T q A ≤ 1000000000 * Λ n T ^ 16 * (1 / q + Real.sqrt ((Tp T : ℝ) / n) + sA n T q) := by
  have hs := one_le_sA n T q (le_trans hn hnT) hnq
  have hη := ηA_eq n T q hn hnT hq hq1 hnq
  have hα := αT_le n T q hn hnT hq hq1 hnq
  have hΛ := Λ_ge n T
  have hLx := Lx_le n T
  have hLx0 := (Lx_pos n T).le
  have hR := Rc_le n T
  have hθ := θc_le_r n T q hn hnT hq hq1 hnq
  have hw := Pool.P0284.wEA_ge n T q A hq hq1
  have hK := KcF_pos n T q hq
  have hD : (Dp (Tp T) : ℝ) ≤ Λ n T := by have := Dn_le n T; unfold Dn at this; push_cast at this; linarith
  set r := Real.sqrt ((Tp T : ℝ) / n) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  set th := (θc n (Tp T) (Kq q) : ℝ) with hth
  have hth0 : 0 ≤ th := Nat.cast_nonneg _
  have hxf : 1 / Pool.P0282.xf n (Tp T) (KcF n T q) = th := by
    rw [one_div_xf (n := n) (T' := Tp T) hK]; rfl
  -- the pieces
  have p1 : Lx n T / (2 * (wEA n T q A * ηA n T q)) ≤ 12 * Λ n T * sA n T q := by
    rw [hη, div_le_iff₀ (by have : 0 < wEA n T q A := by linarith
                            positivity)]
    have : 12 * Λ n T * sA n T q * (2 * (wEA n T q A * (1 / sA n T q))) = 24 * Λ n T * wEA n T q A := by
      field_simp; ring
    rw [this]; nlinarith
  have p2 : 2 * Lx n T / Pool.P0282.xf n (Tp T) (KcF n T q) = 2 * Lx n T * th := by
    rw [← hxf]; field_simp
  have p3 : Real.sqrt (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n))) ≤ 5 * Λ n T * r := by
    have e : Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n)) = (2 * Lx n T * Dp (Tp T)) * ((Tp T : ℝ) / n) := by ring
    rw [e, Real.sqrt_mul (by positivity), hr]
    apply mul_le_mul_of_nonneg_right _ hr0
    apply Real.sqrt_le_iff.2 ⟨by positivity, _⟩
    have : 2 * Lx n T * Dp (Tp T) ≤ 2 * (12 * Λ n T) * Λ n T :=
      mul_le_mul (by linarith) hD (Nat.cast_nonneg _) (by positivity)
    nlinarith
  have p4 : Lx n T / ηA n T q = Lx n T * sA n T q := by rw [hη]; field_simp
  have hAP : APF n T q A = th + (Rc (Tp T) : ℝ) * (2 * Pool.P0226.αT (ι := CpG n (Tp T)) (ηA n T q) (LA T) (Tp T)
      (εA n T q) + 2 * (Lx n T / (2 * (wEA n T q A * ηA n T q)))) + ((Rc (Tp T) : ℝ) + 1) *
      (2 * Lx n T / Pool.P0282.xf n (Tp T) (KcF n T q) +
        2 * Real.sqrt (Lx n T * ((Dp (Tp T) : ℝ) * (2 * (Tp T : ℝ) / n)))) + Lx n T / ηA n T q := rfl
  rw [hAP, p2, p4]
  have hR0 : (0 : ℝ) ≤ Rc (Tp T) := Nat.cast_nonneg _
  have hα0 := Pool.P0226.αT_nonneg (ι := CpG n (Tp T)) (η := ηA n T q) (L := LA T) (T := Tp T) (ηA_pos n T q)
    (δ := εA n T q) (by unfold εA; have := ηA_pos n T q; positivity)
  have hp10 : 0 ≤ Lx n T / (2 * (wEA n T q A * ηA n T q)) := by
    have : 0 < wEA n T q A := by linarith
    have := ηA_pos n T q; positivity
  have q1 : (Rc (Tp T) : ℝ) * (2 * Pool.P0226.αT (ι := CpG n (Tp T)) (ηA n T q) (LA T) (Tp T) (εA n T q) +
      2 * (Lx n T / (2 * (wEA n T q A * ηA n T q)))) ≤ Λ n T * (164 * Λ n T ^ 2 * sA n T q) := by
    apply mul_le_mul hR _ (by positivity) (by linarith)
    nlinarith
  have q2 : ((Rc (Tp T) : ℝ) + 1) * (2 * Lx n T * th + 2 * Real.sqrt (Lx n T * ((Dp (Tp T) : ℝ) *
      (2 * (Tp T : ℝ) / n)))) ≤ (2 * Λ n T) * (24 * Λ n T * th + 10 * Λ n T * r) := by
    apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
    have : 2 * Lx n T * th ≤ 24 * Λ n T * th := by nlinarith
    linarith
  have q3 : Lx n T * sA n T q ≤ 12 * Λ n T * sA n T q := by nlinarith
  -- combine: ≤ 200Λ³(th + s + r), then th ≤ 4.8e6Λ^13/q + r
  have hcomb := comb_arith (Λ n T) th (sA n T q) r hΛ hth0 hs hr0
  have hfin := fin_arith (Λ n T) th (sA n T q) r (1 / q) hΛ hth0 (by linarith) hr0 (by positivity)
    (by rw [show 4800000 * Λ n T ^ 13 / q = 4800000 * Λ n T ^ 13 * (1 / q) by ring] at hθ; exact hθ)
  linarith
theorem BPF_le : BPF n T q A ≤ 31000 * Λ n T ^ 8 * Real.sqrt (1 / q) := by
  have hΛ := Λ_ge n T
  have hLx := Lx_le n T
  have hLx0 := (Lx_pos n T).le
  have hR := Rc_le n T
  have hK := KcF_le_r n T q hn hnT hq hq1 hnq
  have hK0 : (0 : ℝ) ≤ KcF n T q := Nat.cast_nonneg _
  have hB : BPF n T q A = ((Rc (Tp T) : ℝ) + 1) * (2 * Real.sqrt (Lx n T * KcF n T q)) := rfl
  rw [hB]
  have hsq : Real.sqrt (Lx n T * KcF n T q) ≤ 7600 * Λ n T ^ 7 * Real.sqrt (1 / q) := by
    have hiq : (0 : ℝ) ≤ 1 / q := by positivity
    rw [show 7600 * Λ n T ^ 7 * Real.sqrt (1 / q) = Real.sqrt ((7600 * Λ n T ^ 7) ^ 2 * (1 / q)) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    have h1 : Lx n T * KcF n T q ≤ (12 * Λ n T) * (4800000 * Λ n T ^ 13 / q) :=
      mul_le_mul hLx hK hK0 (by positivity)
    have h2 : (12 * Λ n T) * (4800000 * Λ n T ^ 13 / q) = 57600000 * Λ n T ^ 14 * (1 / q) := by ring
    have h3 : (7600 * Λ n T ^ 7) ^ 2 * (1 / q) = 57760000 * Λ n T ^ 14 * (1 / q) := by ring
    have h4 : 0 ≤ Λ n T ^ 14 * (1 / q) := by positivity
    nlinarith
  have hs0 : 0 ≤ Real.sqrt (Lx n T * KcF n T q) := Real.sqrt_nonneg _
  calc ((Rc (Tp T) : ℝ) + 1) * (2 * Real.sqrt (Lx n T * KcF n T q))
      ≤ (2 * Λ n T) * (2 * (7600 * Λ n T ^ 7 * Real.sqrt (1 / q))) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ = 30400 * Λ n T ^ 8 * Real.sqrt (1 / q) := by ring
    _ ≤ 31000 * Λ n T ^ 8 * Real.sqrt (1 / q) := by
        have : 0 ≤ Λ n T ^ 8 * Real.sqrt (1 / q) := by positivity
        nlinarith

/-- `BP·√(n·Tp) ≤ 62000·Λ⁸·Q`. -/
theorem BPF_sqrt_le : BPF n T q A * Real.sqrt (n * Tp T) ≤ 62000 * Λ n T ^ 8 * Q n T q := by
  have hB := BPF_le n T q A hn hnT hq hq1 hnq
  have hB0 : 0 ≤ BPF n T q A := Pool.P0282.BP_nonneg _ _ _ _ _ _ _ _ _ _
  have hs0 : 0 ≤ Real.sqrt ((n : ℝ) * Tp T) := Real.sqrt_nonneg _
  have e : Real.sqrt (1 / q) * Real.sqrt ((n : ℝ) * Tp T) = Real.sqrt (n * ((Tp T : ℝ) / q)) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
  have hQ := sqrt_le_Q n T q hn hnT hq hq1 hnq (X := (Tp T : ℝ) / q) le_rfl
  calc BPF n T q A * Real.sqrt (n * Tp T) ≤ 31000 * Λ n T ^ 8 * Real.sqrt (1 / q) * Real.sqrt (n * Tp T) :=
        mul_le_mul_of_nonneg_right hB hs0
    _ = 31000 * Λ n T ^ 8 * Real.sqrt (n * ((Tp T : ℝ) / q)) := by rw [mul_assoc, e]
    _ ≤ 31000 * Λ n T ^ 8 * (2 * Q n T q) := mul_le_mul_of_nonneg_left hQ (by have := Λ_ge n T; positivity)
    _ = 62000 * Λ n T ^ 8 * Q n T q := by ring

/-- `n·AP ≤ 5·10⁹·Λ¹⁶·Q` and `AP ≤ 5·10⁹·Λ¹⁶·Q`. -/
theorem nAPF_le : (n : ℝ) * APF n T q A ≤ 5000000000 * Λ n T ^ 16 * Q n T q ∧
    APF n T q A ≤ 5000000000 * Λ n T ^ 16 * Q n T q := by
  have hA := APF_le n T q A hn hnT hq hq1 hnq
  have hA0 := APF_nonneg n T q A hq hq1
  obtain ⟨k1, k2, _, k4, k5⟩ := s_facts n T q hn hnT hq hq1 hnq
  have hnq' := n_div_q_le n T q hn hnT hq hq1 hnq
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hΛ := Λ_ge n T
  have hL0 : 0 ≤ 1000000000 * Λ n T ^ 16 := by positivity
  have h1 : (n : ℝ) * APF n T q A ≤ 1000000000 * Λ n T ^ 16 * (n * (1 / q) + n * Real.sqrt ((Tp T : ℝ) / n) +
      n * sA n T q) := by
    calc (n : ℝ) * APF n T q A ≤ n * (1000000000 * Λ n T ^ 16 * (1 / q + Real.sqrt ((Tp T : ℝ) / n) + sA n T q)) :=
          mul_le_mul_of_nonneg_left hA (by linarith)
      _ = _ := by ring
  have h2 : (n : ℝ) * (1 / q) + n * Real.sqrt ((Tp T : ℝ) / n) + n * sA n T q ≤ 5 * Q n T q := by
    rw [show (n : ℝ) * (1 / q) = n / q by ring]; linarith
  have h3 : (n : ℝ) * APF n T q A ≤ 5000000000 * Λ n T ^ 16 * Q n T q := by
    calc (n : ℝ) * APF n T q A ≤ 1000000000 * Λ n T ^ 16 * (5 * Q n T q) := h1.trans (mul_le_mul_of_nonneg_left h2 hL0)
      _ = _ := by ring
  refine ⟨h3, le_trans ?_ h3⟩
  nlinarith

end APBP
theorem cb_arith (s N w S : ℝ) (hs : 1 ≤ s) (hN : s ≤ N) (hw : 1 / 2 ≤ w) (hw1 : w ≤ 1) (hS : 0 ≤ S) :
    (S + 1) * (1 / s / 2 * ((1 + 1 / (4 * N * (1 / s))) / w) + (1 / s + 2 / N + 1 / s * (1 / w + 1 / (4 * N * (w * (1 / s))))))
      + w / N ≤ 8 * (S + 1) / s := by
  have hs0 : 0 < s := by linarith
  have hN0 : 0 < N := by linarith
  have hw0 : 0 < w := by linarith
  have e1 : 1 / (4 * N * (1 / s)) = s / (4 * N) := by field_simp
  have e2 : 1 / (4 * N * (w * (1 / s))) = s / (4 * N * w) := by field_simp
  rw [e1, e2]
  have hsN : s / N ≤ 1 := by rw [div_le_one hN0]; exact hN
  have k1 : s / (4 * N) ≤ 1 / 4 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have k2 : 1 / w ≤ 2 := by rw [div_le_iff₀ hw0]; linarith
  have k3 : s / (4 * N * w) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have k4 : 2 / N ≤ 2 / s := div_le_div_of_nonneg_left (by norm_num) hs0 hN
  have k5 : w / N ≤ 1 / s := by
    calc w / N ≤ 1 / N := div_le_div_of_nonneg_right hw1 hN0.le
      _ ≤ 1 / s := div_le_div_of_nonneg_left (by norm_num) hs0 hN
  have k6 : (1 + s / (4 * N)) / w ≤ 5 / 2 := by
    rw [div_le_iff₀ hw0]; nlinarith
  have hinv : 0 ≤ 1 / s := by positivity
  have inner : 1 / s / 2 * ((1 + s / (4 * N)) / w) + (1 / s + 2 / N + 1 / s * (1 / w + s / (4 * N * w))) ≤
      7 * (1 / s) := by
    have a1 : 1 / s / 2 * ((1 + s / (4 * N)) / w) ≤ 1 / s / 2 * (5 / 2) := mul_le_mul_of_nonneg_left k6 (by positivity)
    have a2 : 1 / s * (1 / w + s / (4 * N * w)) ≤ 1 / s * (5 / 2) := mul_le_mul_of_nonneg_left (by linarith) hinv
    have a3 : 2 / N ≤ 2 * (1 / s) := by rw [show 2 * (1 / s) = 2 / s by ring]; exact k4
    nlinarith
  have hS1 : 0 ≤ S + 1 := by linarith
  calc (S + 1) * (1 / s / 2 * ((1 + s / (4 * N)) / w) + (1 / s + 2 / N + 1 / s * (1 / w + s / (4 * N * w))))
        + w / N ≤ (S + 1) * (7 * (1 / s)) + (S + 1) * (1 / s) := by
          have : 1 / s ≤ (S + 1) * (1 / s) := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left inner hS1]
    _ = 8 * (S + 1) / s := by ring
theorem coarse_term (A B nn Tp b b' : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : 1 ≤ nn) (hTp : 0 < Tp) (hb : 0 < b)
    (hbb : b ≤ b') (hbT : b ≤ Tp) (hcz : Tp ≤ nn * b) :
    (Tp + b') * (2 * (A + B * Real.sqrt b) / b') ≤ 4 * nn * A + 4 * B * Real.sqrt (nn * Tp) := by
  have hb' : 0 < b' := by linarith
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsb2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have r1 : Tp / b' ≤ nn := by rw [div_le_iff₀ hb']; nlinarith
  have e : (Tp + b') * (2 * (A + B * Real.sqrt b) / b') = 2 * (Tp / b' + 1) * A + 2 * B * (Tp * Real.sqrt b / b' + Real.sqrt b) := by
    field_simp
  rw [e]
  have k1 : 2 * (Tp / b' + 1) * A ≤ 4 * nn * A := by nlinarith
  have hsnT : Real.sqrt b ≤ Real.sqrt (nn * Tp) := Real.sqrt_le_sqrt (by nlinarith)
  -- Tp·√b/b' ≤ Tp/√b ≤ √(nn·Tp)
  have k2 : Tp * Real.sqrt b / b' ≤ Real.sqrt (nn * Tp) := by
    have s1 : Tp * Real.sqrt b / b' ≤ Tp * Real.sqrt b / b := div_le_div_of_nonneg_left (by positivity) hb hbb
    have s2 : Tp * Real.sqrt b / b = Tp / Real.sqrt b := by
      rw [div_eq_div_iff hb.ne' hsb.ne']; nlinarith
    have s3 : Tp / Real.sqrt b ≤ Real.sqrt (nn * Tp) := by
      rw [div_le_iff₀ hsb, ← Real.sqrt_mul (by positivity)]
      apply Real.le_sqrt_of_sq_le
      nlinarith
    linarith
  nlinarith

/-- The final combination of the ALG term's pieces (abstract). -/
theorem alg_final_arith (w L Q A B s c cnt D ov cb tl Mw Tp sT nn : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hL : 1 ≤ L)
    (hQ : 1 ≤ Q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hTp : 0 < Tp) (hsT : B * sT ≤ B * s)
    (hY : nn * A + B * s ≤ 5100000000 * L ^ 16 * Q) (hAn : A ≤ nn * A)
    (hc : c ≤ L * (4 * nn * A + 4 * B * s)) (hMw0 : 0 ≤ Mw) (hsT0 : 0 < sT) (hsT2 : sT ^ 2 = Tp) (hMwc : Mw * cnt ≤ 800000 * L ^ 12 * (nn * A + B * s))
    (hMw : Mw ≤ 2 * (A + B * s)) (hD : 0 ≤ D) (hDL : D ≤ L) (hov0 : 0 ≤ ov) (hTov : Tp * ov ≤ 1)
    (hcb : Tp * cb ≤ 10000000 * L ^ 12 * Q) (htl : Tp * tl ≤ 5 / 4) (hcnt : 0 ≤ cnt) (hc0 : 0 ≤ c)
    (hcb0 : 0 ≤ cb) (htl0 : 0 ≤ tl) :
    w * (Tp * (A / Tp + B / sT) + (c + Mw * (cnt + D * Tp * ov))) + w * (Tp * cb) + w * Tp * (2 * ov + tl) ≤
      5000000000000000 * L ^ 28 * Q := by
  have e1 : Tp * (A / Tp + B / sT) = A + B * sT := by
    rw [← hsT2]; field_simp
  rw [e1]
  set Y := nn * A + B * s with hYdef
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ B * sT := mul_nonneg hB hsT0.le
    linarith
  have hL12 : (1 : ℝ) ≤ L ^ 12 := one_le_pow₀ hL
  have hLL : L ≤ L ^ 12 := by simpa using pow_le_pow_right₀ hL (show 1 ≤ 12 by norm_num)
  have k1 : A + B * sT ≤ Y := by linarith
  have k2 : c ≤ 4 * L * Y := by nlinarith
  have k3 : Mw * (D * Tp * ov) ≤ 2 * L * Y := by
    have : D * Tp * ov ≤ L := by
      calc D * Tp * ov = D * (Tp * ov) := by ring
        _ ≤ L * 1 := mul_le_mul hDL hTov (by positivity) (by linarith)
        _ = L := mul_one L
    have h2 : Mw ≤ 2 * Y := by linarith
    calc Mw * (D * Tp * ov) ≤ (2 * Y) * L := mul_le_mul h2 this (by positivity) (by positivity)
      _ = 2 * L * Y := by ring
  have k4 : A + B * sT + (c + Mw * (cnt + D * Tp * ov)) ≤ 800007 * L ^ 12 * Y := by
    have : Mw * (cnt + D * Tp * ov) = Mw * cnt + Mw * (D * Tp * ov) := by ring
    rw [this]
    have hLY : L * Y ≤ L ^ 12 * Y := mul_le_mul_of_nonneg_right hLL hY0
    have hY12 : Y ≤ L ^ 12 * Y := by
      have := mul_le_mul_of_nonneg_right hL12 hY0; linarith
    linarith
  have k5 : Tp * (2 * ov + tl) ≤ 13 / 4 := by
    have : Tp * (2 * ov + tl) = 2 * (Tp * ov) + Tp * tl := by ring
    linarith
  have hbr1 : 0 ≤ A + B * sT + (c + Mw * (cnt + D * Tp * ov)) := by positivity
  have hbr2 : 0 ≤ Tp * cb := by positivity
  have hbr3 : 0 ≤ Tp * (2 * ov + tl) := by positivity
  have w1 : w * (A + B * sT + (c + Mw * (cnt + D * Tp * ov))) ≤ A + B * sT + (c + Mw * (cnt + D * Tp * ov)) :=
    mul_le_of_le_one_left hbr1 hw1
  have w2 : w * (Tp * cb) ≤ Tp * cb := mul_le_of_le_one_left hbr2 hw1
  have w3 : w * Tp * (2 * ov + tl) ≤ Tp * (2 * ov + tl) := by
    rw [mul_assoc]; exact mul_le_of_le_one_left hbr3 hw1
  have hYQ : 800007 * L ^ 12 * Y ≤ 800007 * L ^ 12 * (5100000000 * L ^ 16 * Q) :=
    mul_le_mul_of_nonneg_left hY (by positivity)
  have e2 : 800007 * L ^ 12 * (5100000000 * L ^ 16 * Q) = 4080035700000000 * L ^ 28 * Q := by ring
  have hL28 : L ^ 12 ≤ L ^ 28 := pow_le_pow_right₀ hL (by norm_num)
  have hL28' : (1 : ℝ) ≤ L ^ 28 := one_le_pow₀ hL
  have hQ0 : 0 ≤ Q := by linarith
  have m1 : 10000000 * L ^ 12 * Q ≤ 10000000 * L ^ 28 * Q := by
    have := mul_le_mul_of_nonneg_right hL28 hQ0; linarith
  have m2 : (13 : ℝ) / 4 ≤ 4 * L ^ 28 * Q := by
    have : (1 : ℝ) ≤ L ^ 28 * Q := by nlinarith
    linarith
  linarith

section Terms
attribute [local instance] Pool.P0082.coinFintype
variable (A : Pool.P0050.CoinAlg n)
variable (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (hnq : (n : ℝ) / T ≤ q)
include hn hnT hq hq1 hnq
theorem countF_le : countF n T q A ≤ 400000 * n * Λ n T ^ 12 := by
  have hΛ := Λ_ge n T
  have hD := Dn_le n T
  have hLv := Lv_le n T
  have hs0 := s0_le_r n T
  have hSp := Sp_le_r n T
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hdiv : Tp T / 2 ^ Ld (Tp T) = 0 := Nat.div_eq_of_lt (by
    unfold Ld; exact Nat.lt_pow_succ_log_self (by norm_num) _)
  -- the filter factor
  have hE : (1 - qf n (Tp T)) ^ (Kf n (Tp T) * (Dn (Tp T) * (2 * Ld (Tp T) + Tp T / 2 ^ Ld (Tp T) + 1))) ≥ 1 / 2 := by
    rw [hdiv, add_zero]
    have hQd : (Qd n (Tp T) : ℝ) = 64 * Rc (Tp T) * Kf n (Tp T) * Dn (Tp T) * (2 * Ld (Tp T) + 1) := by
      unfold Qd; push_cast; ring
    have hR1 : (1 : ℝ) ≤ Rc (Tp T) := by exact_mod_cast Rc_pos (Tp T)
    have hKf : (0 : ℝ) < Kf n (Tp T) := by
      have : 0 < Kf n (Tp T) := by unfold Kf; have := Rc_pos (Tp T); positivity
      exact_mod_cast this
    have hDn : (0 : ℝ) < Dn (Tp T) := by exact_mod_cast (show 0 < Dn (Tp T) by unfold Dn; omega)
    have hb := one_add_mul_le_pow (a := -qf n (Tp T)) (by have := (qf_mem n (Tp T)); linarith [this.2])
      (Kf n (Tp T) * (Dn (Tp T) * (2 * Ld (Tp T) + 1)))
    have hm : ((Kf n (Tp T) * (Dn (Tp T) * (2 * Ld (Tp T) + 1)) : ℕ) : ℝ) * qf n (Tp T) = 1 / (64 * Rc (Tp T)) := by
      unfold qf; rw [hQd]; push_cast; field_simp
    have h64 : 1 / (64 * (Rc (Tp T) : ℝ)) ≤ 1 / 64 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    rw [show (1 : ℝ) - qf n (Tp T) = 1 + -qf n (Tp T) by ring]
    have : (1 : ℝ) + ((Kf n (Tp T) * (Dn (Tp T) * (2 * Ld (Tp T) + 1)) : ℕ) : ℝ) * -qf n (Tp T) ≥ 1 / 2 := by
      rw [mul_neg, hm]; linarith
    linarith
  have hnum : ((Dn (Tp T) : ℝ) * Lv (Tp T) * (s0 n (Tp T) + Dn (Tp T) * Lv (Tp T) * Sp n (Tp T) + 1)) ≤
      200000 * Λ n T ^ 12 := by
    have hDL : (Dn (Tp T) : ℝ) * Lv (Tp T) ≤ Λ n T ^ 2 := by
      rw [sq]; exact mul_le_mul hD hLv (Nat.cast_nonneg _) (by linarith)
    have hDL0 : (0 : ℝ) ≤ (Dn (Tp T) : ℝ) * Lv (Tp T) := by positivity
    have hin : (s0 n (Tp T) : ℝ) + Dn (Tp T) * Lv (Tp T) * Sp n (Tp T) + 1 ≤ 199920 * Λ n T ^ 10 := by
      have h1 : (Dn (Tp T) : ℝ) * Lv (Tp T) * Sp n (Tp T) ≤ Λ n T ^ 2 * (196918 * Λ n T ^ 8) :=
        mul_le_mul hDL hSp (Nat.cast_nonneg _) (by positivity)
      have h2 : Λ n T ≤ Λ n T ^ 10 := by simpa using pow_le_pow_right₀ hΛ (show 1 ≤ 10 by norm_num)
      have h3 : (1 : ℝ) ≤ Λ n T ^ 10 := one_le_pow₀ hΛ
      nlinarith
    calc (Dn (Tp T) : ℝ) * Lv (Tp T) * (s0 n (Tp T) + Dn (Tp T) * Lv (Tp T) * Sp n (Tp T) + 1)
        ≤ Λ n T ^ 2 * (199920 * Λ n T ^ 10) := mul_le_mul hDL hin (by positivity) (by positivity)
      _ = 199920 * Λ n T ^ 12 := by ring
      _ ≤ 200000 * Λ n T ^ 12 := by
          have : 0 ≤ Λ n T ^ 12 := by positivity
          linarith
  have hc : countF n T q A = ((Dn (Tp T) : ℝ) * Lv (Tp T) * (s0 n (Tp T) + Dn (Tp T) * Lv (Tp T) * Sp n (Tp T) + 1))
      / ((1 / (n : ℝ)) * (1 - qf n (Tp T)) ^ (Kf n (Tp T) * (Dn (Tp T) * (2 * Ld (Tp T) + Tp T / 2 ^ Ld (Tp T) + 1)))) := by
    unfold countF; push_cast; rfl
  rw [hc, div_le_iff₀ (by positivity)]
  have hnum0 : (0 : ℝ) ≤ (Dn (Tp T) : ℝ) * Lv (Tp T) * (s0 n (Tp T) + Dn (Tp T) * Lv (Tp T) * Sp n (Tp T) + 1) := by
    positivity
  have : 400000 * n * Λ n T ^ 12 * ((1 / (n : ℝ)) * (1 / 2)) = 200000 * Λ n T ^ 12 := by field_simp; ring
  have hpos : 0 ≤ 400000 * n * Λ n T ^ 12 * (1 / (n : ℝ)) := by positivity
  calc _ ≤ 200000 * Λ n T ^ 12 := hnum
    _ = 400000 * n * Λ n T ^ 12 * ((1 / (n : ℝ)) * (1 / 2)) := this.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity)
theorem NA_ge : sA n T q ≤ (NA n T q : ℝ) := by
  have h1 : sA n T q ≤ (⌈sA n T q⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈sA n T q⌉₊ : ℝ) ≤ NA n T q := by unfold NA; exact_mod_cast le_max_right _ _
  linarith
theorem wEA_le_one : wEA n T q A ≤ 1 := by
  have h := (slot_weights_le n T q hq).1
  have h0 : 0 ≤ ∑ j : Fin (Dn (Tp T)), (Sl n (Tp T) : ℝ) * xr n (Tp T) (KcF n T q) j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (xr_pos (KcF_pos n T q hq) j).le
  show 1 - q / 2 - ∑ j : Fin (Dn (Tp T)), (Sl n (Tp T) : ℝ) * xr n (Tp T) (KcF n T q) j ≤ 1
  linarith
theorem TCbF_le : (Tp T : ℝ) * CbF n T q A ≤ 10000000 * Λ n T ^ 12 * Q n T q := by
  have hs := one_le_sA n T q (le_trans hn hnT) hnq
  have hη := ηA_eq n T q hn hnT hq hq1 hnq
  have hN := NA_ge n T q hn hnT hq hq1 hnq
  have hw := Pool.P0284.wEA_ge n T q A hq hq1
  have hw1 := wEA_le_one n T q A hn hnT hq hq1 hnq
  have hS : (∑ j : Fin (QM n T q A).D, ((QM n T q A).sl j : ℝ)) = (Dn (Tp T) : ℝ) * Sl n (Tp T) := by
    show (∑ _j : Fin (Dn (Tp T)), (Sl n (Tp T) : ℝ)) = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNs := Ns_le_r n T
  have hS0 : (0 : ℝ) ≤ (Dn (Tp T) : ℝ) * Sl n (Tp T) := by positivity
  have hcb : CbF n T q A ≤ 8 * ((Dn (Tp T) : ℝ) * Sl n (Tp T) + 1) / sA n T q := by
    unfold CbF Pool.P0243.Cb; rw [hS, hη]
    exact cb_arith (sA n T q) (NA n T q) (wEA n T q A) _ hs hN hw hw1 hS0
  obtain ⟨_, _, k3, _, _⟩ := s_facts n T q hn hnT hq hq1 hnq
  have hΛ := Λ_ge n T
  have hTp0 : (0 : ℝ) ≤ Tp T := Nat.cast_nonneg _
  calc (Tp T : ℝ) * CbF n T q A ≤ Tp T * (8 * ((Dn (Tp T) : ℝ) * Sl n (Tp T) + 1) / sA n T q) :=
        mul_le_mul_of_nonneg_left hcb hTp0
    _ = 8 * ((Dn (Tp T) : ℝ) * Sl n (Tp T) + 1) * ((Tp T : ℝ) / sA n T q) := by ring
    _ ≤ 8 * (600001 * Λ n T ^ 12) * (2 * Q n T q) := by
        apply mul_le_mul _ k3 (by positivity) (by positivity)
        have : (1 : ℝ) ≤ Λ n T ^ 12 := one_le_pow₀ hΛ
        linarith
    _ ≤ 10000000 * Λ n T ^ 12 * Q n T q := by
        have : 0 ≤ Λ n T ^ 12 * Q n T q := by have := Q_ge_one n T q hn hnT hq hq1 hnq; positivity
        nlinarith

/-- The exponential tails: `Tp·tail ≤ 5/4`. -/
theorem TtailF_le : (Tp T : ℝ) * tailF n T ≤ 5 / 4 := by
  set c := (Fintype.card (CpG n (Tp T)) : ℝ)
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ Tp T := Nat.cast_nonneg _
  have he : Real.exp (-Lx n T) = 1 / (((Tp T : ℝ) + 1) ^ 3 * (4 * c + 4)) := by
    unfold Lx
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, ← Real.log_rpow (by positivity),
      Real.exp_log (by positivity), Real.exp_log (by positivity)]
    rw [show ((Tp T : ℝ) + 1) ^ (3 : ℝ) = ((Tp T : ℝ) + 1) ^ (3 : ℕ) by norm_cast]
    field_simp
    rfl
  have e : tailF n T = (5 * c + 4) * ((Tp T : ℝ) + 1) ^ 2 * Real.exp (-Lx n T) := by unfold tailF; ring
  rw [e, he]
  have hpos : (0 : ℝ) < ((Tp T : ℝ) + 1) ^ 3 * (4 * c + 4) := by positivity
  rw [show (Tp T : ℝ) * ((5 * c + 4) * ((Tp T : ℝ) + 1) ^ 2 * (1 / (((Tp T : ℝ) + 1) ^ 3 * (4 * c + 4)))) =
    (Tp T : ℝ) * (5 * c + 4) * ((Tp T : ℝ) + 1) ^ 2 / (((Tp T : ℝ) + 1) ^ 3 * (4 * c + 4)) by ring]
  rw [div_le_iff₀ hpos]
  have h1 : (Tp T : ℝ) * ((Tp T : ℝ) + 1) ^ 2 ≤ ((Tp T : ℝ) + 1) ^ 3 := by nlinarith
  have h2 : (5 * c + 4) ≤ 5 / 4 * (4 * c + 4) := by linarith
  have := mul_le_mul h1 h2 (by positivity) (by positivity)
  nlinarith

/-- P0287's overflow closed form: `ovfB ≤ 1/(Tp+1)²`. -/
theorem ovfBF_le : ovfBF n T q A ≤ 1 / ((Tp T : ℝ) + 1) ^ 2 :=
  Pool.P0287.ovfB_le n (Tp T) hn (Tp_pos T)
theorem coarseF_le : coarseF n T q A ≤
    Λ n T * (4 * n * APF n T q A + 4 * BPF n T q A * Real.sqrt (n * Tp T)) := by
  have hA := APF_nonneg n T q A hq hq1
  have hB : 0 ≤ BPF n T q A := Pool.P0282.BP_nonneg _ _ _ _ _ _ _ _ _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTp : (0 : ℝ) < Tp T := by exact_mod_cast Tp_pos T
  set X := 4 * n * APF n T q A + 4 * BPF n T q A * Real.sqrt (n * Tp T) with hX
  have hX0 : 0 ≤ X := by positivity
  unfold coarseF Pool.P0259.coarseSum
  calc _ ≤ ∑ _j ∈ Finset.Ico 1 (QM n T q A).D, X := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_Ico] at hj
        split_ifs with hcz
        · unfold Pool.P0266.aW
          rw [if_neg (by omega)]
          show ((Tp T : ℝ) + (Bt (Tp T) (j - 1) : ℕ)) * (2 * (APF n T q A + BPF n T q A *
            Real.sqrt ((Bt (Tp T) j : ℕ) : ℝ)) / ((Bt (Tp T) (j - 1) : ℕ) : ℝ)) ≤ X
          have hcz' : (Tp T : ℝ) ≤ n * (Bt (Tp T) j : ℕ) := by
            unfold czF at hcz; exact_mod_cast hcz
          have hb : (0 : ℝ) < (Bt (Tp T) j : ℕ) := by exact_mod_cast Nat.two_pow_pos _
          have hbb : ((Bt (Tp T) j : ℕ) : ℝ) ≤ (Bt (Tp T) (j - 1) : ℕ) := by
            exact_mod_cast Bt_anti (Tp T) (show j - 1 ≤ j by omega)
          have hbT : ((Bt (Tp T) j : ℕ) : ℝ) ≤ Tp T := by
            have := Bt_anti (Tp T) (Nat.zero_le j); rw [Bt0_Tp] at this; exact_mod_cast this
          exact coarse_term _ _ _ _ _ _ hA hB hn1 hTp hb hbb hbT hcz'
        · exact hX0
    _ = ((Finset.Ico 1 (QM n T q A).D).card : ℝ) * X := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Λ n T * X := by
        apply mul_le_mul_of_nonneg_right _ hX0
        rw [Nat.card_Ico]
        have h1 : ((Dn (Tp T) - 1 : ℕ) : ℝ) ≤ Dn (Tp T) := by exact_mod_cast Nat.sub_le _ _
        exact h1.trans (Dn_le n T)
theorem CbF_nonneg : 0 ≤ CbF n T q A := by
  have hη := ηA_pos n T q
  have hN : (0 : ℝ) < NA n T q := by exact_mod_cast (show 0 < NA n T q by unfold NA; omega)
  have hw : 0 < wEA n T q A := by have := Pool.P0284.wEA_ge n T q A hq hq1; linarith
  have hS : (0 : ℝ) ≤ ∑ j : Fin (QM n T q A).D, ((QM n T q A).sl j : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  unfold CbF Pool.P0243.Cb; positivity
theorem coarseF_nonneg : 0 ≤ coarseF n T q A := by
  have hA := APF_nonneg n T q A hq hq1
  have hB : 0 ≤ BPF n T q A := Pool.P0282.BP_nonneg _ _ _ _ _ _ _ _ _ _
  unfold coarseF Pool.P0259.coarseSum
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · exact mul_nonneg (by positivity) (Pool.P0266.aW_nonneg hA hB (by norm_num) _ j)
  · exact le_rfl
open Classical in
/-- **The ALG term of the one-level machine is `Õ(√(nT/q))`** (P0281's bound at P0284's family, evaluated):
`E_arr[algT] ≤ 5·10¹⁵·Λ²⁸·√(nT/q) + wE·Tp·E_arr[ovf]`, `Λ = Lam(n, Tp) + 3 ≤ 5·Lg(n, T)`. -/
theorem algT_famM_le (ℓ : Pool.P0001.LossSeq n) (rc₀ : RC (famM n T q A).P) (i : Fin n) :
    ∑ arr : Pool.P0116.Arr (Pool.P0201.pp (famM n T q A)) (Tp T) → Bool,
        Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
          Pool.P0217.algT (famM n T q A) (Tp T) ℓ rc₀ i arr ≤
      5000000000000000 * Λ n T ^ 28 * Q n T q +
        (M0 n T q A).P.wE * (Tp T : ℝ) * ∑ arr, Pool.P0048.wtv (Pool.P0091.pC (famM n T q A).ps (famM n T q A).q) arr *
          Pool.P0217.ovf (famM n T q A) (Tp T) ℓ rc₀ arr := by
  refine (algT_famM_raw n T q A hn hnT hq hq1 ℓ rc₀ i).trans ?_
  refine add_le_add ?_ le_rfl
  have hBt0 : ((QM n T q A).Bt 0 : ℝ) = Tp T := by
    show ((Bt (Tp T) 0 : ℕ) : ℝ) = _; rw [Bt0_Tp]
  rw [hBt0]
  have hΛ := Λ_ge n T
  have hQ := Q_ge_one n T q hn hnT hq hq1 hnq
  have hA := APF_nonneg n T q A hq hq1
  have hB : 0 ≤ BPF n T q A := Pool.P0282.BP_nonneg _ _ _ _ _ _ _ _ _ _
  have hTp : (0 : ℝ) < Tp T := by exact_mod_cast Tp_pos T
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsTp : Real.sqrt (Tp T : ℝ) ≤ Real.sqrt (n * Tp T) := Real.sqrt_le_sqrt (by nlinarith)
  have hsr : Real.sqrt ((Tp T : ℝ) / n) ≤ Real.sqrt (n * Tp T) := Real.sqrt_le_sqrt (by
    rw [div_le_iff₀ hn0]
    have h1 : (1 : ℝ) ≤ n * n := by nlinarith
    have := mul_le_mul_of_nonneg_left h1 hTp.le
    nlinarith)
  have hnr : (n : ℝ) * Real.sqrt ((Tp T : ℝ) / n) = Real.sqrt (n * Tp T) := by
    rw [show (n : ℝ) * Tp T = n ^ 2 * (Tp T / n) by field_simp, Real.sqrt_mul (by positivity), Real.sqrt_sq hn0.le]
  obtain ⟨hnA, _⟩ := nAPF_le n T q A hn hnT hq hq1 hnq
  have hBs := BPF_sqrt_le n T q A hn hnT hq hq1 hnq
  have hY : (n : ℝ) * APF n T q A + BPF n T q A * Real.sqrt (n * Tp T) ≤ 5100000000 * Λ n T ^ 16 * Q n T q := by
    have h8 : Λ n T ^ 8 ≤ Λ n T ^ 16 := pow_le_pow_right₀ hΛ (by norm_num)
    have : 62000 * Λ n T ^ 8 * Q n T q ≤ 100000000 * Λ n T ^ 16 * Q n T q := by
      have := mul_le_mul_of_nonneg_right h8 (by linarith : (0 : ℝ) ≤ Q n T q); nlinarith
    linarith
  have hcnt := countF_le n T q A hn hnT hq hq1 hnq
  have hcnt0 : 0 ≤ countF n T q A := by
    unfold countF
    have := (qf_mem n (Tp T)); have := qf_lt_one n (Tp T)
    apply div_nonneg (by positivity)
    apply mul_nonneg (by show (0 : ℝ) ≤ 1 / n; positivity)
    exact pow_nonneg (by show (0 : ℝ) ≤ 1 - qf n (Tp T); linarith) _
  have hMw0 := MwF_nonneg n T q A hq hq1
  have hMwc : MwF n T q A * countF n T q A ≤
      800000 * Λ n T ^ 12 * ((n : ℝ) * APF n T q A + BPF n T q A * Real.sqrt (n * Tp T)) := by
    calc MwF n T q A * countF n T q A ≤ MwF n T q A * (400000 * n * Λ n T ^ 12) :=
          mul_le_mul_of_nonneg_left hcnt hMw0
      _ = 800000 * Λ n T ^ 12 * ((n : ℝ) * APF n T q A + BPF n T q A * (n * Real.sqrt ((Tp T : ℝ) / n))) := by
          unfold MwF; ring
      _ = _ := by rw [hnr]
  have hMw : MwF n T q A ≤ 2 * (APF n T q A + BPF n T q A * Real.sqrt (n * Tp T)) := by
    unfold MwF; have := mul_le_mul_of_nonneg_left hsr hB; linarith
  have hov := ovfBF_le n T q A hn hnT hq hq1 hnq
  have hov0 : 0 ≤ ovfBF n T q A := by
    unfold ovfBF
    have := Pool.P0042.delta_nonneg (N := Fintype.card (CpG n (Tp T))) (qf_mem n (Tp T)).2
      (L := Rc (Tp T)) (k := kk n (Tp T)) (M0 := (Pool.P0261.M0 n (Tp T) : ℝ))
    exact add_nonneg (by positivity) (mul_nonneg (by positivity) this)
  have hTov : (Tp T : ℝ) * ovfBF n T q A ≤ 1 := by
    have : (Tp T : ℝ) * (1 / ((Tp T : ℝ) + 1) ^ 2) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; nlinarith
    exact (mul_le_mul_of_nonneg_left hov hTp.le).trans this
  have htl0 : 0 ≤ tailF n T := by unfold tailF; positivity
  have hw := Pool.P0284.wEA_ge n T q A hq hq1
  exact alg_final_arith (wEA n T q A) (Λ n T) (Q n T q) (APF n T q A) (BPF n T q A) (Real.sqrt (n * Tp T))
    (coarseF n T q A) (countF n T q A) ((QM n T q A).D : ℝ) (ovfBF n T q A) (CbF n T q A) (tailF n T) (MwF n T q A)
    (Tp T) (Real.sqrt (Tp T)) n (by linarith) (wEA_le_one n T q A hn hnT hq hq1 hnq) hΛ hQ hA hB hTp
    (mul_le_mul_of_nonneg_left hsTp hB) hY (by nlinarith) (coarseF_le n T q A hn hnT hq hq1 hnq) hMw0
    (Real.sqrt_pos.2 hTp) (Real.sq_sqrt hTp.le) hMwc hMw (Nat.cast_nonneg _) (Dn_le n T) hov0 hTov
    (TCbF_le n T q A hn hnT hq hq1 hnq) (TtailF_le n T q hn hnT hq hq1 hnq) hcnt0 (coarseF_nonneg n T q A hn hnT hq hq1 hnq)
    (CbF_nonneg n T q A hn hnT hq hq1 hnq) htl0

end Terms

end Pool.P0291