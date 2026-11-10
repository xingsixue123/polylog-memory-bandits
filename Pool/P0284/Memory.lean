import Pool.P0284.Family

/-!
# Memory of the concrete family (P0262's F8): polylog bounds on P0261's sizes
-/

namespace Pool.P0284

open Pool.P0261

variable {n T : ℕ}
/-- The polylog scale `Λ₀ = Lam n T + 3`. -/
def Λ₀ (n T : ℕ) : ℕ := Lam n T + 3
theorem Λ₀_pos : 1 ≤ Λ₀ n T := by unfold Λ₀; omega
theorem Lam_le : Lam n T ≤ Λ₀ n T := by unfold Λ₀; omega
theorem logT_le (hn : 1 ≤ n) : Nat.log 2 T ≤ Lam n T := by
  unfold Lam
  have : Nat.log 2 T ≤ Nat.log 2 (n * T) := Nat.log_mono_right (Nat.le_mul_of_pos_left _ (by omega))
  omega
theorem Dn_le' (hn : 1 ≤ n) : Dn T ≤ Λ₀ n T := by have := logT_le (T := T) hn; unfold Dn Dp Λ₀; omega
theorem Ld_le' (hn : 1 ≤ n) : Ld T ≤ Λ₀ n T := by have := logT_le (T := T) hn; unfold Ld Λ₀; omega
theorem Lv_le' (hn : 1 ≤ n) : Lv T ≤ Λ₀ n T := by have := logT_le (T := T) hn; unfold Lv Ld Λ₀; omega
theorem Rc_le' (hn : 1 ≤ n) : Rc T ≤ Λ₀ n T := by have := logT_le (T := T) hn; unfold Rc Λ₀; omega
theorem Kf_le (hn : 1 ≤ n) : Kf n T ≤ 8 * Λ₀ n T ^ 2 := by
  unfold Kf
  have h1 := Rc_le' (T := T) hn
  have h2 : Lam n T + 1 ≤ Λ₀ n T := by unfold Λ₀; omega
  calc 4 * Rc T * (2 * (Lam n T + 1)) ≤ 4 * Λ₀ n T * (2 * Λ₀ n T) := by gcongr
    _ = 8 * Λ₀ n T ^ 2 := by ring
theorem Qd_le (hn : 1 ≤ n) : Qd n T ≤ 1536 * Λ₀ n T ^ 5 := by
  unfold Qd
  have h0 := Λ₀_pos (n := n) (T := T)
  have h1 := Rc_le' (T := T) hn
  have h2 := Kf_le (T := T) hn
  have h3 := Dn_le' (T := T) hn
  have h4 : 2 * Ld T + 1 ≤ 3 * Λ₀ n T := by have := Ld_le' (T := T) hn; omega
  calc 64 * Rc T * Kf n T * Dn T * (2 * Ld T + 1) ≤ 64 * Λ₀ n T * (8 * Λ₀ n T ^ 2) * Λ₀ n T * (3 * Λ₀ n T) := by
        gcongr
    _ = 1536 * Λ₀ n T ^ 5 := by ring
theorem kk_le (hn : 1 ≤ n) : kk n T ≤ 49152 * Λ₀ n T ^ 7 := by
  unfold kk
  have h1 := Lam_le (n := n) (T := T)
  have h2 := Qd_le (T := T) hn
  calc 32 * Lam n T ^ 2 * Qd n T ≤ 32 * Λ₀ n T ^ 2 * (1536 * Λ₀ n T ^ 5) := by gcongr
    _ = 49152 * Λ₀ n T ^ 7 := by ring
theorem M0_le (hn : 1 ≤ n) : Pool.P0261.M0 n T ≤ 196912 * Λ₀ n T ^ 8 := by
  unfold Pool.P0261.M0
  have h0 := Λ₀_pos (n := n) (T := T)
  have h1 := Rc_le' (T := T) hn
  have h2 := kk_le (T := T) hn
  have h3 := Lam_le (n := n) (T := T)
  have p1 : Λ₀ n T ≤ Λ₀ n T ^ 8 := Nat.le_self_pow (by norm_num) _
  have p2 : Λ₀ n T ^ 2 ≤ Λ₀ n T ^ 8 := Nat.pow_le_pow_right h0 (by norm_num)
  calc 16 * Rc T + 4 * Rc T * kk n T + 288 * Rc T * Lam n T
      ≤ 16 * Λ₀ n T + 4 * Λ₀ n T * (49152 * Λ₀ n T ^ 7) + 288 * Λ₀ n T * Λ₀ n T := by gcongr
    _ = 16 * Λ₀ n T + 196608 * Λ₀ n T ^ 8 + 288 * Λ₀ n T ^ 2 := by ring
    _ ≤ 196912 * Λ₀ n T ^ 8 := by omega
theorem s0_le : s0 n T ≤ 6 * Λ₀ n T := by unfold s0 Λ₀; omega
theorem Sp_le (hn : 1 ≤ n) : Sp n T ≤ 196918 * Λ₀ n T ^ 8 := by
  unfold Sp
  have h1 := M0_le (T := T) hn
  have h2 := s0_le (n := n) (T := T)
  have p1 : Λ₀ n T ≤ Λ₀ n T ^ 8 := Nat.le_self_pow (by norm_num) _
  omega
theorem Sl_le (hn : 1 ≤ n) : Sl n T ≤ 600000 * Λ₀ n T ^ 11 := by
  unfold Sl
  have h0 := Λ₀_pos (n := n) (T := T)
  have hD := Dn_le' (T := T) hn
  have hL := Lv_le' (T := T) hn
  have hS := Sp_le (T := T) hn
  have hs := s0_le (n := n) (T := T)
  have hL1 : Lv T - 1 ≤ Λ₀ n T := by omega
  have p1 : Λ₀ n T ^ 2 ≤ Λ₀ n T ^ 11 := Nat.pow_le_pow_right h0 (by norm_num)
  have p2 : Λ₀ n T ^ 10 ≤ Λ₀ n T ^ 11 := Nat.pow_le_pow_right h0 (by norm_num)
  have p3 : 1 ≤ Λ₀ n T ^ 11 := Nat.one_le_pow _ _ h0
  calc Dn T * ((s0 n T + Dn T * Lv T * Sp n T) + (Lv T - 1) * Sp n T) + Dn T * s0 n T + 1
      ≤ Λ₀ n T * ((6 * Λ₀ n T + Λ₀ n T * Λ₀ n T * (196918 * Λ₀ n T ^ 8)) + Λ₀ n T * (196918 * Λ₀ n T ^ 8)) +
          Λ₀ n T * (6 * Λ₀ n T) + 1 := by gcongr
    _ = 6 * Λ₀ n T ^ 2 + 196918 * Λ₀ n T ^ 11 + 196918 * Λ₀ n T ^ 10 + 6 * Λ₀ n T ^ 2 + 1 := by ring
    _ ≤ 600000 * Λ₀ n T ^ 11 := by omega
theorem Ns_le (hn : 1 ≤ n) : Dn T * Sl n T ≤ 600000 * Λ₀ n T ^ 12 := by
  have h1 := Dn_le' (T := T) hn
  have h2 := Sl_le (T := T) hn
  calc Dn T * Sl n T ≤ Λ₀ n T * (600000 * Λ₀ n T ^ 11) := Nat.mul_le_mul h1 h2
    _ = 600000 * Λ₀ n T ^ 12 := by ring
theorem lt_two_pow_Λ₀ : n * T < 2 ^ Λ₀ n T := by
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n * T)
  calc n * T < 2 ^ (Nat.log 2 (n * T) + 1) := this
    _ ≤ 2 ^ Λ₀ n T := Nat.pow_le_pow_right (by norm_num) (by unfold Λ₀ Lam; omega)
theorem n_le_pow (hT : 1 ≤ T) : n ≤ 2 ^ Λ₀ n T := by
  have := lt_two_pow_Λ₀ (n := n) (T := T); nlinarith
theorem T_le_pow (hn : 1 ≤ n) : T ≤ 2 ^ Λ₀ n T := by
  have := lt_two_pow_Λ₀ (n := n) (T := T); nlinarith
theorem Λ₀_le_pow : Λ₀ n T ≤ 2 ^ Λ₀ n T := (Nat.lt_two_pow_self).le
/-- `Λ^k ≤ 2^(k·Λ)`. -/
theorem pow_le_pow_Λ₀ (k : ℕ) : Λ₀ n T ^ k ≤ 2 ^ (k * Λ₀ n T) := by
  rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left Λ₀_le_pow k
/-- `log₂ x ≤ k` from `x ≤ 2^k`. -/
theorem logb_le_of_le_pow {x : ℝ} {k : ℕ} (hx : 0 < x) (h : x ≤ 2 ^ k) : Real.logb 2 x ≤ k := by
  rw [Real.logb_le_iff_le_rpow (by norm_num) hx, Real.rpow_natCast]; exact h

section Family

open Pool.P0284

variable (n T : ℕ) [NeZero n] (q : ℝ)
/-- The polylog scale of the family. -/
def BB : ℕ := Λ₀ n (Tp T)
theorem BB_pos : 1 ≤ BB n T := Λ₀_pos
theorem Tp_le_pow : Tp T ≤ 2 ^ BB n T := T_le_pow (NeZero.one_le)
theorem n_le_pow' : n ≤ 2 ^ BB n T := n_le_pow (Tp_pos T)
theorem card_ι_le : Fintype.card (CpG n (Tp T)) ≤ 2 ^ (3 * BB n T) := by
  have h1 : Fintype.card (CpG n (Tp T)) ≤ Tp T * Dn (Tp T) * n := by
    calc Fintype.card (CpG n (Tp T)) ≤ Fintype.card (Pool.P0121.TM.Cp n (Tp T) (Dn (Tp T))) :=
          Fintype.card_subtype_le _
      _ = Tp T * Dn (Tp T) * n := Fintype.card_fin _
  have h2 := Tp_le_pow n T
  have h3 : Dn (Tp T) ≤ 2 ^ BB n T := (Dn_le' NeZero.one_le).trans Λ₀_le_pow
  have h4 := n_le_pow' n T
  calc Fintype.card (CpG n (Tp T)) ≤ Tp T * Dn (Tp T) * n := h1
    _ ≤ 2 ^ BB n T * 2 ^ BB n T * 2 ^ BB n T := by gcongr
    _ = 2 ^ (3 * BB n T) := by rw [← pow_add, ← pow_add]; ring_nf
theorem Kq_le (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hnq : (n : ℝ) / T ≤ q) : Kq q ≤ Tp T := by
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast le_trans hn hnT
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / q ≤ T := by
    rw [div_le_iff₀ hq]; rw [div_le_iff₀ (by linarith)] at hnq; nlinarith
  have : Kq q ≤ T := Nat.ceil_le.2 h1
  exact this.trans (le_Tp T)
theorem KcF_le (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hnq : (n : ℝ) / T ≤ q) :
    KcF n T q ≤ 2 ^ (36 * BB n T) := by
  have hB := BB_pos n T
  have hD : Dn (Tp T) ≤ BB n T := Dn_le' hn
  have hS : Sl n (Tp T) ≤ 600000 * BB n T ^ 11 := Sl_le hn
  have hK : Kq q ≤ 2 ^ BB n T := (Kq_le n T q hn hnT hq hnq).trans (Tp_le_pow n T)
  have hP : BB n T ^ 13 ≤ 2 ^ (13 * BB n T) := pow_le_pow_Λ₀ 13
  have hc : (4 * 600000 : ℕ) ≤ 2 ^ (22 * BB n T) :=
    le_trans (show (4 * 600000 : ℕ) ≤ 2 ^ 22 by norm_num)
      (Nat.pow_le_pow_right (by norm_num) (show 22 ≤ 22 * BB n T by omega))
  unfold KcF Kc
  calc 4 * Dn (Tp T) ^ 2 * Sl n (Tp T) * Kq q ≤ 4 * BB n T ^ 2 * (600000 * BB n T ^ 11) * 2 ^ BB n T := by gcongr
    _ = (4 * 600000) * BB n T ^ 13 * 2 ^ BB n T := by ring
    _ ≤ 2 ^ (22 * BB n T) * 2 ^ (13 * BB n T) * 2 ^ BB n T := by gcongr
    _ = 2 ^ (36 * BB n T) := by rw [← pow_add, ← pow_add]; ring_nf
theorem Bm_le_Tp : Bm n (Tp T) ≤ Tp T := by
  rcases Bm_sq_le n (Tp T) with h | h
  · have h1 : Bm n (Tp T) ≤ Bm n (Tp T) * Bm n (Tp T) := Nat.le_mul_self _
    exact h1.trans (h.trans (Nat.div_le_self _ _))
  · unfold Bm; rw [h]; simp; exact Tp_pos T
theorem TT_le (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hnq : (n : ℝ) / T ≤ q) :
    Tp T * (KcF n T q + Bm n (Tp T) + 1) + 1 ≤ 2 ^ (40 * BB n T) := by
  have hB := BB_pos n T
  have h1 := KcF_le n T q hn hnT hq hnq
  have h2 := (Bm_le_Tp n T).trans (Tp_le_pow n T)
  have h3 := Tp_le_pow n T
  have e1 : 2 ^ BB n T ≤ 2 ^ (36 * BB n T) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : 1 ≤ 2 ^ (36 * BB n T) := Nat.one_le_two_pow
  calc Tp T * (KcF n T q + Bm n (Tp T) + 1) + 1 ≤ 2 ^ BB n T * (3 * 2 ^ (36 * BB n T)) + 2 ^ BB n T := by
        have : KcF n T q + Bm n (Tp T) + 1 ≤ 3 * 2 ^ (36 * BB n T) := by omega
        have h1' : 1 ≤ 2 ^ BB n T := Nat.one_le_two_pow
        exact Nat.add_le_add (Nat.mul_le_mul h3 this) h1'
    _ = 2 ^ BB n T * (3 * 2 ^ (36 * BB n T) + 1) := by ring
    _ ≤ 2 ^ BB n T * (4 * 2 ^ (36 * BB n T)) := Nat.mul_le_mul_left _ (by omega)
    _ = 2 ^ (BB n T + 36 * BB n T + 2) := by rw [pow_add, pow_add]; ring
    _ ≤ 2 ^ (40 * BB n T) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Family

section Real

open Pool.P0284

variable (n T : ℕ) [NeZero n] (q : ℝ)
theorem wEA_ge (A : Pool.P0050.CoinAlg n) (hq : 0 < q) (hq1 : q ≤ 1 / 32) : 1 / 2 ≤ wEA n T q A := by
  have h := (slot_weights_le n T q hq).1
  show 1 / 2 ≤ 1 - q / 2 - ∑ j : Fin (Dn (Tp T)), (Sl n (Tp T) : ℝ) * xr n (Tp T) (KcF n T q) j
  linarith
theorem sA_le (hq0 : 0 ≤ q) (hq : q ≤ 1) : sA n T q ≤ Tp T := by
  have hT : (1 : ℝ) ≤ Tp T := by exact_mod_cast Tp_pos T
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  unfold sA
  calc Real.sqrt (q * Tp T / n) ≤ Real.sqrt ((Tp T : ℝ) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [div_le_iff₀ (by linarith)]; nlinarith
    _ = Tp T := Real.sqrt_sq (by linarith)

theorem max_sA_le (hq0 : 0 ≤ q) (hq : q ≤ 1) : max 1 (sA n T q) ≤ Tp T := by
  have hT : (1 : ℝ) ≤ Tp T := by exact_mod_cast Tp_pos T
  exact max_le hT (sA_le n T q hq0 hq)

theorem NA_le (hq0 : 0 ≤ q) (hq : q ≤ 1) : NA n T q ≤ Tp T + 1 := by
  unfold NA
  have h1 : ⌈sA n T q⌉₊ ≤ Tp T + 1 := by
    have := Nat.ceil_le_floor_add_one (sA n T q)
    have h2 : ⌊sA n T q⌋₊ ≤ Tp T := Nat.floor_le_of_le (sA_le n T q hq0 hq) |> fun h => by exact_mod_cast h
    omega
  have := Tp_pos T
  omega

theorem NA_le_real (hq0 : 0 ≤ q) (hq : q ≤ 1) : (NA n T q : ℝ) ≤ Tp T + 1 := by
  exact_mod_cast NA_le n T q hq0 hq

theorem ηA_pos : 0 < ηA n T q := by unfold ηA; have : (0 : ℝ) < max 1 (sA n T q) := lt_max_of_lt_left one_pos; positivity

/-- ALG's bound cap `Bmx = ⌊G/(wE·γ)⌋ ≤ 4·Tp²`. -/
theorem Bmx_le (A : Pool.P0050.CoinAlg n) (hq : 0 < q) (hq1 : q ≤ 1 / 32) :
    Pool.P0236.Bmx (NA n T q) (ηA n T q) (wEA n T q A) ≤ 4 * Tp T ^ 2 := by
  have hw := wEA_ge n T q A hq hq1
  have hT : (1 : ℝ) ≤ Tp T := by exact_mod_cast Tp_pos T
  have hs := max_sA_le n T q hq.le (by linarith)
  have hN := NA_le_real n T q hq.le (by linarith)
  have hm1 : (1 : ℝ) ≤ max 1 (sA n T q) := le_max_left _ _
  unfold Pool.P0236.Bmx
  apply Nat.floor_le_of_le
  have e : (NA n T q : ℝ) / (wEA n T q A * ηA n T q) = NA n T q * max 1 (sA n T q) / wEA n T q A := by
    unfold ηA; field_simp
  rw [e, div_le_iff₀ (by linarith)]
  push_cast
  have hN0 : (0 : ℝ) ≤ NA n T q := Nat.cast_nonneg _
  calc (NA n T q : ℝ) * max 1 (sA n T q) ≤ (Tp T + 1) * Tp T := mul_le_mul hN hs (by linarith) (by linarith)
    _ ≤ 4 * (Tp T : ℝ) ^ 2 * (1 / 2) := by nlinarith
    _ ≤ 4 * (Tp T : ℝ) ^ 2 * wEA n T q A := by gcongr

/-- ALG's increment cap `Imx = ⌊η/G·Bmx/ε⌋ ≤ 4·Tp³` (`ε = η/Tp`). -/
theorem Imx_le (A : Pool.P0050.CoinAlg n) (hq : 0 < q) (hq1 : q ≤ 1 / 32) :
    Pool.P0236.Imx (ηA n T q) (εA n T q) (NA n T q) (ηA n T q) (wEA n T q A) ≤ 4 * Tp T ^ 3 := by
  have hB := Bmx_le n T q A hq hq1
  have hT : (1 : ℝ) ≤ Tp T := by exact_mod_cast Tp_pos T
  have hη := ηA_pos n T q
  have hN1 : (1 : ℝ) ≤ NA n T q := by exact_mod_cast (show 1 ≤ NA n T q by unfold NA; omega)
  unfold Pool.P0236.Imx
  apply Nat.floor_le_of_le
  have e : ηA n T q / NA n T q * (Pool.P0236.Bmx (NA n T q) (ηA n T q) (wEA n T q A) : ℝ) / εA n T q =
      Tp T * (Pool.P0236.Bmx (NA n T q) (ηA n T q) (wEA n T q A) : ℝ) / NA n T q := by
    unfold εA; field_simp
  rw [e, div_le_iff₀ (by linarith)]
  have hB' : (Pool.P0236.Bmx (NA n T q) (ηA n T q) (wEA n T q A) : ℝ) ≤ 4 * (Tp T : ℝ) ^ 2 := by exact_mod_cast hB
  have hB0 : (0 : ℝ) ≤ Pool.P0236.Bmx (NA n T q) (ηA n T q) (wEA n T q A) := Nat.cast_nonneg _
  push_cast
  have hT0 : (0 : ℝ) ≤ Tp T := by linarith
  calc (Tp T : ℝ) * (Pool.P0236.Bmx (NA n T q) (ηA n T q) (wEA n T q A) : ℝ) ≤ Tp T * (4 * (Tp T : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hB' hT0
    _ = 4 * (Tp T : ℝ) ^ 3 * 1 := by ring
    _ ≤ 4 * (Tp T : ℝ) ^ 3 * NA n T q := by gcongr

end Real

section Logs

/-- `log₂` of a natural number `≤ 2^k`. -/
theorem logb_nat_le {x k : ℕ} (hx : 1 ≤ x) (h : x ≤ 2 ^ k) : Real.logb 2 (x : ℝ) ≤ k :=
  logb_le_of_le_pow (by exact_mod_cast hx) (by exact_mod_cast h)

theorem pow_mono2 {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

/-- The pool term's argument. -/
theorem log_pool_le {c e tb B : ℕ} (hB : 1 ≤ B) (hc : c ≤ 2 ^ (3 * B)) (he : e ≤ B ^ 2) (htb : tb ≤ 2 ^ B) :
    Real.logb 2 ((c : ℝ) * 2 ^ e * (2 * ((tb : ℝ) + 1)) + 1) ≤ 10 * B ^ 2 := by
  have h1 : c * 2 ^ e * (2 * (tb + 1)) + 1 ≤ 2 ^ (10 * B ^ 2) := by
    have htb' : tb + 1 ≤ 2 ^ (B + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := B); omega
    calc c * 2 ^ e * (2 * (tb + 1)) + 1 ≤ 2 ^ (3 * B) * 2 ^ (B ^ 2) * (2 * 2 ^ (B + 1)) + 2 ^ (3 * B) * 2 ^ (B ^ 2) * (2 * 2 ^ (B + 1)) := by
          have hp : 1 ≤ 2 ^ (3 * B) * 2 ^ (B ^ 2) * (2 * 2 ^ (B + 1)) := Nat.one_le_iff_ne_zero.2 (by positivity)
          have := Nat.mul_le_mul (Nat.mul_le_mul hc (pow_mono2 he)) (Nat.mul_le_mul_left 2 htb')
          omega
      _ = 2 ^ (3 * B + B ^ 2 + B + 3) := by rw [pow_add, pow_add, pow_add, pow_add]; ring
      _ ≤ 2 ^ (10 * B ^ 2) := pow_mono2 (by nlinarith)
  have := logb_nat_le (by omega) h1
  push_cast at this; exact this

/-- A generic `log₂(X + 1)` with `X ≤ 2^k`. -/
theorem log_succ_le {x k : ℕ} (h : x ≤ 2 ^ k) : Real.logb 2 ((x : ℝ) + 1) ≤ k + 1 := by
  have h1 : x + 1 ≤ 2 ^ (k + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := k); omega
  have := logb_nat_le (by omega) h1
  push_cast at this; exact this

/-- The twin's table term: `log₂((c+1)·((a+1)(b+1))^(L+1) + 1) ≤ 50B²` for `c ≤ 2^(3B)`, `a ≤ 2^(3B+2)`,
`b ≤ 2^(4B+2)`, `L + 1 ≤ 3B`. -/
theorem log_twin_le {c a b L B : ℕ} (hB : 1 ≤ B) (hc : c ≤ 2 ^ (3 * B)) (ha : a ≤ 2 ^ (3 * B + 2))
    (hb : b ≤ 2 ^ (4 * B + 2)) (hL : L + 1 ≤ 3 * B) :
    Real.logb 2 (((c : ℝ) + 1) * (((a : ℝ) + 1) * ((b : ℝ) + 1)) ^ (L + 1) + 1) ≤ 50 * B ^ 2 := by
  have hc' : c + 1 ≤ 2 ^ (3 * B + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := 3 * B); omega
  have ha' : a + 1 ≤ 2 ^ (3 * B + 3) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := 3 * B + 2); omega
  have hb' : b + 1 ≤ 2 ^ (4 * B + 3) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := 4 * B + 2); omega
  have hab : (a + 1) * (b + 1) ≤ 2 ^ (13 * B) := by
    calc (a + 1) * (b + 1) ≤ 2 ^ (3 * B + 3) * 2 ^ (4 * B + 3) := Nat.mul_le_mul ha' hb'
      _ = 2 ^ (7 * B + 6) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (13 * B) := pow_mono2 (by omega)
  have hpow : ((a + 1) * (b + 1)) ^ (L + 1) ≤ 2 ^ (39 * B ^ 2) := by
    calc ((a + 1) * (b + 1)) ^ (L + 1) ≤ (2 ^ (13 * B)) ^ (3 * B) :=
          le_trans (Nat.pow_le_pow_left hab _) (Nat.pow_le_pow_right (Nat.one_le_two_pow) hL)
      _ = 2 ^ (39 * B ^ 2) := by rw [← pow_mul]; ring_nf
  have h1 : (c + 1) * ((a + 1) * (b + 1)) ^ (L + 1) + 1 ≤ 2 ^ (50 * B ^ 2) := by
    calc (c + 1) * ((a + 1) * (b + 1)) ^ (L + 1) + 1 ≤ 2 ^ (3 * B + 1) * 2 ^ (39 * B ^ 2) + 2 ^ (3 * B + 1) * 2 ^ (39 * B ^ 2) := by
          have := Nat.mul_le_mul hc' hpow
          have hp : 1 ≤ 2 ^ (3 * B + 1) * 2 ^ (39 * B ^ 2) := Nat.one_le_iff_ne_zero.2 (by positivity)
          omega
      _ = 2 ^ (3 * B + 2 + 39 * B ^ 2) := by rw [pow_add, pow_add, pow_add]; ring
      _ ≤ 2 ^ (50 * B ^ 2) := pow_mono2 (by nlinarith)
  have := logb_nat_le (by omega) h1
  push_cast at this; exact this

end Logs

section Main

open Pool.P0284

variable (n T : ℕ) [NeZero n] (q : ℝ) (A : Pool.P0050.CoinAlg n)

/-- The arithmetic of the memory sum. -/
theorem mem_arith (a b : ℝ) (ha : 0 ≤ a) (hb : 1 ≤ b) (hab : a ≤ 600000 * b ^ 12) :
    a * (10 * b ^ 2) + a * a * (40 * b) + (b + 1) + ((b + 1) + (4 * b + 3) + (a + 1) * (50 * b ^ 2))
      + (b + 1) + 40 * b + (b + 1) ≤ 160 * 600001 ^ 2 * b ^ 26 := by
  have hB2 : b ≤ b ^ 2 := by nlinarith
  have hB1 : (1 : ℝ) ≤ b ^ 2 := by nlinarith
  have hA1 : (1 : ℝ) ≤ (a + 1) ^ 2 := by nlinarith
  have hA2 : a ≤ (a + 1) ^ 2 := by nlinarith
  have hA3 : a * a ≤ (a + 1) ^ 2 := by nlinarith
  have hA4 : a + 1 ≤ (a + 1) ^ 2 := by nlinarith
  have hb0 : (0 : ℝ) ≤ b ^ 2 := by positivity
  have e1 : a * (10 * b ^ 2) ≤ 10 * ((a + 1) ^ 2 * b ^ 2) := by
    have := mul_le_mul_of_nonneg_right hA2 hb0; linarith
  have e2 : a * a * (40 * b) ≤ 40 * ((a + 1) ^ 2 * b ^ 2) := by
    have := mul_le_mul hA3 hB2 (by positivity) (by positivity); linarith
  have e3 : (a + 1) * (50 * b ^ 2) ≤ 50 * ((a + 1) ^ 2 * b ^ 2) := by
    have := mul_le_mul_of_nonneg_right hA4 hb0; linarith
  have e4 : b ^ 2 ≤ (a + 1) ^ 2 * b ^ 2 := by
    have := mul_le_mul_of_nonneg_right hA1 hb0; linarith
  have hsum : a * (10 * b ^ 2) + a * a * (40 * b) + (b + 1) + ((b + 1) + (4 * b + 3) + (a + 1) * (50 * b ^ 2))
      + (b + 1) + 40 * b + (b + 1) ≤ 160 * (a + 1) ^ 2 * b ^ 2 := by linarith
  have h1 : a + 1 ≤ 600001 * b ^ 12 := by
    have : (1 : ℝ) ≤ b ^ 12 := one_le_pow₀ hb
    linarith
  have h2 : (a + 1) ^ 2 ≤ (600001 * b ^ 12) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  calc _ ≤ 160 * (a + 1) ^ 2 * b ^ 2 := hsum
    _ ≤ 160 * (600001 * b ^ 12) ^ 2 * b ^ 2 := by gcongr
    _ = 160 * 600001 ^ 2 * b ^ 26 := by ring


theorem clog_le_BB : Nat.clog 2 T ≤ BB n T := by
  have h := Tp_le_pow n T
  unfold Tp at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

theorem card_Kd_le (hn : 1 ≤ n) :
    Fintype.card (Pool.P0194.Kd (Pool.P0245.mTwin (M0 n T q A) (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q)
      (ηA n T q) (wEA n T q A) (Tp T)).P) ≤ 2 ^ (40 * BB n T) := by
  have hc : Fintype.card (Pool.P0194.Kd (Pool.P0245.mTwin (M0 n T q A) (ηA n T q) (εA n T q) (LA T) (NA n T q)
      (NA n T q) (ηA n T q) (wEA n T q A) (Tp T)).P) = 2 + Dn (Tp T) * Sl n (Tp T) := by
    show Fintype.card (Option (Option (Σ j : Fin (Dn (Tp T)), Fin (Sl n (Tp T))))) = _
    simp only [Fintype.card_option, Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
    ring
  rw [hc]
  have hB := BB_pos n T
  have h1 : Dn (Tp T) * Sl n (Tp T) ≤ 600000 * BB n T ^ 12 := Ns_le hn
  have h2 : BB n T ^ 12 ≤ 2 ^ (12 * BB n T) := pow_le_pow_Λ₀ 12
  have h3 : (600000 : ℕ) ≤ 2 ^ 20 := by norm_num
  have h4 : 600000 * BB n T ^ 12 ≤ 2 ^ (20 + 12 * BB n T) := by rw [pow_add]; exact Nat.mul_le_mul h3 h2
  have h5 : 2 ^ (20 + 12 * BB n T) + 2 ≤ 2 ^ (40 * BB n T) := by
    have : 2 ^ (20 + 12 * BB n T) * 2 ≤ 2 ^ (40 * BB n T) := by rw [← pow_succ]; exact pow_mono2 (by omega)
    have : 2 ≤ 2 ^ (20 + 12 * BB n T) := le_trans (by norm_num) (pow_mono2 (show 1 ≤ 20 + 12 * BB n T by omega))
    omega
  omega

/-- **The memory of the one-level machine (P0262's F8)**, in the polylog scale `BB = Lam n Tp + 3`:
`memBits ≤ bits(A) + 160·600001²·BB²⁶`. -/
theorem memBits_machF_le (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (hnq : (n : ℝ) / T ≤ q) :
    (machF n T q A).toMachine.memBits ≤ A.toMachine.memBits + 160 * 600001 ^ 2 * (BB n T : ℝ) ^ 26 := by
  have h := Pool.P0245.memBits_mTwin_le (M0 n T q A) (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q)
    (wEA n T q A) (Tp T)
  refine h.trans ?_
  clear h
  have eAB : (Pool.P0245.mTwin (M0 n T q A) (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q)
      (wEA n T q A) (Tp T)).P.AB = A := rfl
  rw [eAB]
  refine add_le_add le_rfl ?_
  set B := BB n T with hBdef
  have hB : 1 ≤ B := BB_pos n T
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hT : Tp T ≤ 2 ^ B := Tp_le_pow n T
  have hNs : (M0 n T q A).Ns ≤ 600000 * B ^ 12 := Ns_le hn
  set Ns := (M0 n T q A).Ns with hNsdef
  have hNsr : (Ns : ℝ) ≤ 600000 * (B : ℝ) ^ 12 := by exact_mod_cast hNs
  have hNs0 : (0 : ℝ) ≤ Ns := Nat.cast_nonneg _
  -- the terms
  have t1 : Real.logb 2 ((Fintype.card (CpG n (Tp T)) : ℝ) * 2 ^ ((Pool.P0201.pp (Pool.P0245.mTwin (M0 n T q A)
      (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (Tp T))).Lt + 1) *
      (2 * (((M0 n T q A).TB : ℕ) + 1)) + 1) ≤ 10 * (B : ℝ) ^ 2 := by
    have := log_pool_le (c := Fintype.card (CpG n (Tp T))) (e := (Pool.P0201.pp (Pool.P0245.mTwin (M0 n T q A)
      (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (Tp T))).Lt + 1)
      (tb := (M0 n T q A).TB) hB (card_ι_le n T) (by
        show Dn (Tp T) * Lv (Tp T) - 1 + 1 ≤ B ^ 2
        have h1 : Dn (Tp T) ≤ B := Dn_le' hn
        have h2 : Lv (Tp T) ≤ B := Lv_le' hn
        have : Dn (Tp T) * Lv (Tp T) ≤ B * B := Nat.mul_le_mul h1 h2
        have hBB : 1 ≤ B * B := Nat.one_le_iff_ne_zero.2 (by positivity)
        rw [sq]; omega) hT
    exact_mod_cast this
  have t2 : Real.logb 2 (((M0 n T q A).TT : ℝ) + 1) ≤ 40 * B := by
    have := logb_nat_le (x := (M0 n T q A).TT + 1) (by omega) (TT_le n T q hn hnT hq hnq)
    push_cast at this; exact this
  have t3 : Real.logb 2 (((M0 n T q A).TB : ℝ) + 1) ≤ B + 1 := by
    have := log_succ_le (x := (M0 n T q A).TB) hT; exact_mod_cast this
  have hImx := Imx_le n T q A hq hq1
  have hBmx := Bmx_le n T q A hq hq1
  have hTI : Tp T * Pool.P0236.Imx (ηA n T q) (εA n T q) (NA n T q) (ηA n T q) (wEA n T q A) ≤ 2 ^ (4 * B + 2) := by
    calc _ ≤ 2 ^ B * (4 * (2 ^ B) ^ 3) := Nat.mul_le_mul hT (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hT 3) |>.trans' hImx)
      _ = 2 ^ (4 * B + 2) := by rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]; ring_nf
  have hTB : Tp T * Pool.P0236.Bmx (NA n T q) (ηA n T q) (wEA n T q A) ≤ 2 ^ (3 * B + 2) := by
    calc _ ≤ 2 ^ B * (4 * (2 ^ B) ^ 2) := Nat.mul_le_mul hT (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hT 2) |>.trans' hBmx)
      _ = 2 ^ (3 * B + 2) := by rw [← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, ← pow_add]; ring_nf
  have t4 : Real.logb 2 ((Tp T : ℝ) + 1) ≤ B + 1 := by have := log_succ_le (x := Tp T) hT; exact_mod_cast this
  have t5 : Real.logb 2 ((Tp T : ℝ) * (Pool.P0236.Imx (ηA n T q) (εA n T q) (NA n T q) (ηA n T q) (wEA n T q A) : ℕ)
      + 1) ≤ 4 * B + 3 := by
    have := log_succ_le hTI; push_cast at this ⊢; linarith
  have t6 : Real.logb 2 (((Fintype.card (CpG n (Tp T)) : ℕ) : ℝ) + 1) * 0 = 0 := by ring
  have t7 := log_twin_le (c := Fintype.card (CpG n (Tp T))) (L := LA T) hB (card_ι_le n T) hTB hTI
    (by have := clog_le_BB n T; unfold LA; omega)
  push_cast at t7
  have t8 : Real.logb 2 (((M0 n T q A).Tc : ℝ) + 1) ≤ B + 1 := by
    have := log_succ_le (x := (M0 n T q A).Tc) hT; exact_mod_cast this
  have t9 : Real.logb 2 (Fintype.card (Pool.P0194.Kd (Pool.P0245.mTwin (M0 n T q A) (ηA n T q) (εA n T q) (LA T)
      (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (Tp T)).P) : ℝ) ≤ 40 * B :=
    by have := logb_nat_le Fintype.card_pos (card_Kd_le n T q A hn); push_cast at this; exact this
  have t10 : Real.logb 2 (NA n T q : ℝ) ≤ B + 1 := by
    have h1 : NA n T q ≤ 2 ^ (B + 1) := by
      have := NA_le n T q hq.le (by linarith); rw [pow_succ]; have := Nat.one_le_two_pow (n := B); omega
    have := logb_nat_le (by unfold NA; omega) h1; push_cast at this; exact this
  have hNN : ((Ns * Ns : ℕ) : ℝ) = (Ns : ℝ) * Ns := by push_cast; ring
  rw [hNN]
  have hl1 : 0 ≤ Real.logb 2 (((M0 n T q A).TT : ℝ) + 1) := Real.logb_nonneg (by norm_num) (by
    have : (0 : ℝ) ≤ (M0 n T q A).TT := Nat.cast_nonneg _; linarith)
  -- assemble: everything ≤ 150·(Ns+1)²·B²
  have hsum := mem_arith (Ns : ℝ) (B : ℝ) hNs0 hBr hNsr
  have k1 := mul_le_mul_of_nonneg_left t1 hNs0
  have k2 := mul_le_mul_of_nonneg_left t2 (mul_nonneg hNs0 hNs0)
  have k3 := mul_le_mul_of_nonneg_left t7 (by linarith : (0 : ℝ) ≤ Ns + 1)
  calc _ ≤ (Ns : ℝ) * (10 * B ^ 2) + Ns * Ns * (40 * B) + (B + 1) + ((B + 1) + (4 * B + 3) + (Ns + 1) * (50 * B ^ 2))
      + (B + 1) + 40 * B + (B + 1) := by
        push_cast at k3 t5 ⊢
        linarith
    _ ≤ _ := hsum

/-- The polylog scale is `≤ 5·Lg n T` (P0161's `Lg = log(nT) + 1`). -/
theorem BB_le_Lg (hn : 1 ≤ n) (hnT : n ≤ T) : (BB n T : ℝ) ≤ 5 * Pool.P0161.Lg n T := by
  have hT : 1 ≤ T := le_trans hn hnT
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTp : (Tp T : ℝ) ≤ 2 * T := by exact_mod_cast Tp_le T hT
  have hTp1 : (1 : ℝ) ≤ Tp T := by exact_mod_cast Tp_pos T
  have h1 : (Nat.log 2 (n * Tp T) : ℝ) ≤ Real.logb 2 ((n * Tp T : ℕ) : ℝ) := Real.natLog_le_logb _ _
  have hnT0 : (0 : ℝ) < n * T := by positivity
  have h2 : Real.logb 2 ((n * Tp T : ℕ) : ℝ) ≤ Real.logb 2 (2 * (n * T)) := by
    push_cast
    apply Real.logb_le_logb_of_le (by norm_num) (by positivity)
    nlinarith
  have h3 : Real.logb 2 (2 * (n * T)) = 1 + Real.log (n * T) / Real.log 2 := by
    rw [Real.logb, Real.log_mul (by norm_num) hnT0.ne']; field_simp
  have hl2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlnT : 0 ≤ Real.log (n * T) := Real.log_nonneg (by nlinarith)
  have h4 : Real.log (n * T) / Real.log 2 ≤ 3 / 2 * Real.log (n * T) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hB : (BB n T : ℝ) = Nat.log 2 (n * Tp T) + 4 := by
    unfold BB Λ₀ Lam; push_cast; ring
  rw [hB]; unfold Pool.P0161.Lg
  push_cast at h1 h2 ⊢
  linarith

/-- **The memory of the one-level machine (P0262's F8)**: `memBits ≤ bits(A) + Cmem·Lg(n,T)^26`. -/
theorem memBits_machF_Lg (hn : 1 ≤ n) (hnT : n ≤ T) (hq : 0 < q) (hq1 : q ≤ 1 / 32) (hnq : (n : ℝ) / T ≤ q) :
    (machF n T q A).toMachine.memBits ≤
      A.toMachine.memBits + 160 * 600001 ^ 2 * 5 ^ 26 * Pool.P0161.Lg n T ^ 26 := by
  refine (memBits_machF_le n T q A hn hnT hq hq1 hnq).trans (add_le_add le_rfl ?_)
  have h := BB_le_Lg n T hn hnT
  have h0 : (0 : ℝ) ≤ BB n T := Nat.cast_nonneg _
  have := pow_le_pow_left₀ h0 h 26
  rw [mul_pow] at this
  calc 160 * 600001 ^ 2 * (BB n T : ℝ) ^ 26 ≤ 160 * 600001 ^ 2 * (5 ^ 26 * Pool.P0161.Lg n T ^ 26) := by gcongr
    _ = _ := by ring

end Main

end Pool.P0284
