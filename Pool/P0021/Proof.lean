import Pool.P0021.Statement
import Pool.P0015.Reduction

/-!
# Proof of `blockRate_of_kQueryLearners`

For `2 ≤ n ≤ T`, the block length is `B = max n ⌈(T/n)^{1/3}⌉` and `T' = T / B` blocks fit in `T` rounds.
* If `n ≤ T'`, the machine is the homogeneous block machine (`Pool.P0015.blockMachine`, with P0001's
  `withClock T`) built from the hypothesised learner for `(n, T')`. Its regret is at most
  `B · R(T') + K · T' + (T − T' B)` (`Pool.P0015.regret_blockMachine_le`, `regret_le_regret_add`), which is
  bounded by `main_bound`.
* Otherwise (`n = 1`, or fewer than `n` blocks fit), the machine is `trivialMachine` (one state, always
  arm `0`). With one arm every machine has regret `0` (`regret_one`). If fewer than `n` blocks fit, then
  `T ≤ 3 n √T` (`fallback_bound`).
-/

open scoped ENNReal
open Pool.P0001 Pool.P0015

namespace Pool.P0021

/-- The trivial machine: one state, always pulls arm `0`. -/
noncomputable abbrev trivialMachine (n : ℕ) [NeZero n] : Machine n where
  State := Unit
  init := PMF.pure ()
  act _ _ := PMF.pure 0
  next _ _ _ _ := PMF.pure ()

lemma trivialMachine_isHomogeneous (n : ℕ) [NeZero n] : (trivialMachine n).IsHomogeneous :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

lemma trivialMachine_memBits (n : ℕ) [NeZero n] : (trivialMachine n).memBits = 0 := by
  simp [Machine.memBits]

/-- With one arm every machine has regret `0`. -/
lemma regret_one (M : Machine 1) (ℓ : LossSeq 1) (T : ℕ) : regret M ℓ T = 0 := by
  have hexp : ∀ t, M.expLoss ℓ t = ((ℓ t 0).toNat : ℝ) := by
    intro t
    have h := Machine.expLoss_le_one M ℓ t
    simp only [Machine.expLoss, Fin.sum_univ_one]
    have : (M.armDist ℓ t 0) = 1 := by
      have := (M.armDist ℓ t).tsum_coe
      rwa [tsum_fintype (L := .unconditional _), Fin.sum_univ_one] at this
    rw [this]; simp
  have hbest : bestLoss ℓ T = cumLoss ℓ T 0 := by
    simp [bestLoss]
  rw [regret, hbest, cumLoss]
  simp [hexp]

end Pool.P0021

namespace Pool.P0021

lemma cube_rpow {y : ℝ} (hy : 0 ≤ y) : (y ^ ((1 : ℝ) / 3)) ^ 3 = y := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num

lemma rpow_two_thirds {y : ℝ} (hy : 0 ≤ y) : y ^ ((2 : ℝ) / 3) = (y ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num

/-- The real-number core: with `a = n^{1/3}`, `b = T^{1/3}` and `x = b / a`. -/
lemma sqrt_nTx {n T : ℝ} (hn : 0 < n) (hT : 0 ≤ T) :
    Real.sqrt (n * T * (T / n) ^ ((1 : ℝ) / 3)) = n ^ ((1 : ℝ) / 3) * T ^ ((2 : ℝ) / 3) := by
  set a := n ^ ((1 : ℝ) / 3)
  set b := T ^ ((1 : ℝ) / 3)
  have ha : 0 < a := Real.rpow_pos_of_pos hn _
  have hb : 0 ≤ b := Real.rpow_nonneg hT _
  have hx : (T / n) ^ ((1 : ℝ) / 3) = b / a := Real.div_rpow hT hn.le _
  have hn3 : n = a ^ 3 := (cube_rpow hn.le).symm
  have hT3 : T = b ^ 3 := (cube_rpow hT).symm
  rw [hx, rpow_two_thirds hT]
  rw [show n * T * (b / a) = (a * b ^ 2) ^ 2 by rw [hn3, hT3]; field_simp]
  exact Real.sqrt_sq (by positivity)

lemma T_div_x {n T : ℝ} (hn : 0 < n) (hT : 0 < T) :
    T / (T / n) ^ ((1 : ℝ) / 3) = n ^ ((1 : ℝ) / 3) * T ^ ((2 : ℝ) / 3) := by
  set a := n ^ ((1 : ℝ) / 3)
  set b := T ^ ((1 : ℝ) / 3)
  have ha : 0 < a := Real.rpow_pos_of_pos hn _
  have hb : 0 < b := Real.rpow_pos_of_pos hT _
  have hx : (T / n) ^ ((1 : ℝ) / 3) = b / a := Real.div_rpow hT.le hn.le _
  have hT3 : T = b ^ 3 := (cube_rpow hT.le).symm
  rw [hx, rpow_two_thirds hT.le]
  conv_lhs => rw [hT3]
  field_simp
  rfl

end Pool.P0021

namespace Pool.P0021

/-- `x = (T/n)^{1/3}`. -/
noncomputable def xr (n T : ℕ) : ℝ := ((T : ℝ) / n) ^ ((1 : ℝ) / 3)

/-- The block length `B = max n ⌈(T/n)^{1/3}⌉`. -/
noncomputable def Bn (n T : ℕ) : ℕ := max n ⌈xr n T⌉₊

lemma one_le_xr {n T : ℕ} (hn : 1 ≤ n) (hnT : n ≤ T) : 1 ≤ xr n T := by
  unfold xr
  have : (1 : ℝ) ≤ (T : ℝ) / n := by
    rw [le_div_iff₀ (by exact_mod_cast hn)]; simpa using (show (n : ℝ) ≤ T by exact_mod_cast hnT)
  exact Real.one_le_rpow this (by norm_num)

lemma le_Bn (n T : ℕ) : n ≤ Bn n T := le_max_left _ _

lemma xr_le_Bn (n T : ℕ) : xr n T ≤ Bn n T :=
  (Nat.le_ceil _).trans (by exact_mod_cast le_max_right n ⌈xr n T⌉₊)

lemma Bn_le {n T : ℕ} (hn : 1 ≤ n) (hnT : n ≤ T) : (Bn n T : ℝ) ≤ n + xr n T + 1 := by
  have hx := one_le_xr hn hnT
  have h1 : (⌈xr n T⌉₊ : ℝ) < xr n T + 1 := Nat.ceil_lt_add_one (by linarith)
  unfold Bn
  rcases le_total n ⌈xr n T⌉₊ with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

lemma sqrt_add3_le (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a + b + c) ≤ Real.sqrt a + Real.sqrt b + Real.sqrt c := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt ha; have := Real.sq_sqrt hb; have := Real.sq_sqrt hc
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, Real.sqrt_nonneg c,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg c),
    mul_nonneg (Real.sqrt_nonneg b) (Real.sqrt_nonneg c)]

/-- The main inequality of the reduction case. -/
lemma main_bound {n T : ℕ} (hn : 2 ≤ n) (hnT : n ≤ T) (c cK L : ℝ) (j kK K : ℕ) (hL : 1 ≤ L)
    (hK : (K : ℝ) ≤ |cK| * L ^ kK) (lj : ℝ) (hlj0 : 0 ≤ lj) (hlj : lj ≤ L) :
    (Bn n T : ℝ) * (c * Real.sqrt (n * (T / Bn n T : ℕ)) * lj ^ j) + K * (T / Bn n T : ℕ) +
      ((T - (T / Bn n T) * Bn n T : ℕ) : ℝ) ≤
      (2 * |c| + |cK| + 3) * ((n : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) + n * Real.sqrt T) *
        L ^ (j + kK) := by
  set B := Bn n T with hBdef
  set T' := T / B with hT'def
  set x := xr n T with hxdef
  set P := (n : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) with hPdef
  set Q := (n : ℝ) * Real.sqrt T with hQdef
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hT0 : (0 : ℝ) < T := by linarith
  have hx1 : 1 ≤ x := one_le_xr (by omega) hnT
  have hxB : x ≤ B := xr_le_Bn n T
  have hBle : (B : ℝ) ≤ n + x + 1 := Bn_le (by omega) hnT
  have hB0 : (0 : ℝ) < B := by linarith
  have hP0 : 0 ≤ P := by positivity
  have hsqT : 1 ≤ Real.sqrt T := by rw [Real.one_le_sqrt]; exact hT1
  have hQ : n ≤ Q := by rw [hQdef]; nlinarith
  -- T' B ≤ T
  have hTB : ((T' * B : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.div_mul_le_self T B
  have hT'B : (T' : ℝ) * B ≤ T := by exact_mod_cast Nat.div_mul_le_self T B
  have hT'0 : (0 : ℝ) ≤ T' := by positivity
  -- (1) B √(n T') ≤ √(n T B)
  have h1 : (B : ℝ) * Real.sqrt (n * T') ≤ Real.sqrt (n * T * B) := by
    rw [show (B : ℝ) * Real.sqrt (n * T') = Real.sqrt ((B : ℝ) ^ 2 * (n * T')) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hB0.le]]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hT'B (show (0 : ℝ) ≤ n * B by positivity)
    nlinarith
  -- (2) √(n T B) ≤ 2Q + P
  have hsqx : Real.sqrt (n * T * x) = P := by rw [hxdef, xr]; exact sqrt_nTx hn0 hT0.le
  have h2 : Real.sqrt (n * T * B) ≤ 2 * Q + P := by
    calc Real.sqrt (n * T * B) ≤ Real.sqrt (n * T * n + n * T * x + n * T) := by
          apply Real.sqrt_le_sqrt
          have := mul_le_mul_of_nonneg_left hBle (show (0 : ℝ) ≤ n * T by positivity)
          nlinarith
      _ ≤ Real.sqrt (n * T * n) + Real.sqrt (n * T * x) + Real.sqrt (n * T) :=
          sqrt_add3_le _ _ _ (by positivity) (by positivity) (by positivity)
      _ ≤ Q + P + Q := by
          gcongr
          · rw [show (n : ℝ) * T * n = n ^ 2 * T by ring, Real.sqrt_mul (by positivity),
              Real.sqrt_sq hn0.le]
          · exact hsqx.le
          · rw [Real.sqrt_mul hn0.le]
            calc Real.sqrt n * Real.sqrt T ≤ n * Real.sqrt T := by
                  gcongr
                  calc Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by
                        have : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact hn1
                        nlinarith
                    _ = n := Real.mul_self_sqrt hn0.le
              _ = Q := rfl
      _ = 2 * Q + P := by ring
  -- (3) T' ≤ P
  have h3 : (T' : ℝ) ≤ P := by
    calc (T' : ℝ) ≤ T / B := Nat.cast_div_le
      _ ≤ T / x := div_le_div_of_nonneg_left hT0.le (by linarith) hxB
      _ = P := by rw [hxdef, xr]; exact T_div_x hn0 hT0
  -- (4) the leftover rounds
  have hx2 : x ≤ P := by
    have hx3 : x ^ 3 * n = T := by rw [hxdef, xr, cube_rpow (by positivity)]; field_simp
    have hxx : x * x ≤ x ^ 3 := by nlinarith
    have hx3n : x ^ 3 ≤ x ^ 3 * n := le_mul_of_one_le_right (by positivity) hn1
    have : x * x ≤ T := by linarith
    calc x ≤ T / x := by rw [le_div_iff₀ (by linarith)]; linarith
      _ = P := by rw [hxdef, xr]; exact T_div_x hn0 hT0
  have h4 : ((T - T' * B : ℕ) : ℝ) ≤ 2 * Q + P := by
    have hlt : T - T' * B < B := by
      have hB0' : 0 < B := lt_of_lt_of_le (by omega) (le_Bn n T)
      have h0 := Nat.lt_div_mul_add (a := T) hB0'
      have h' : T / B * B = T' * B := rfl
      omega
    have : ((T - T' * B : ℕ) : ℝ) ≤ B := by exact_mod_cast hlt.le
    linarith
  -- assemble
  have hLj : L ^ j ≤ L ^ (j + kK) := pow_le_pow_right₀ hL (by omega)
  have hLk : L ^ kK ≤ L ^ (j + kK) := pow_le_pow_right₀ hL (by omega)
  have hL1 : 1 ≤ L ^ (j + kK) := one_le_pow₀ hL
  have hLj0 : 0 ≤ L ^ j := by positivity
  have hljL : lj ^ j ≤ L ^ j := pow_le_pow_left₀ hlj0 hlj j
  have hsq0 : 0 ≤ Real.sqrt (n * T') := Real.sqrt_nonneg _
  have hA : (B : ℝ) * (c * Real.sqrt (n * T') * lj ^ j) ≤ |c| * (2 * Q + P) * L ^ (j + kK) := by
    calc (B : ℝ) * (c * Real.sqrt (n * T') * lj ^ j)
        ≤ (B : ℝ) * (|c| * Real.sqrt (n * T') * L ^ j) := by
          gcongr
          · exact le_abs_self c
      _ = |c| * ((B : ℝ) * Real.sqrt (n * T')) * L ^ j := by ring
      _ ≤ |c| * (2 * Q + P) * L ^ (j + kK) := by
          gcongr
          exact h1.trans h2
  have hKT : (K : ℝ) * T' ≤ |cK| * P * L ^ (j + kK) := by
    calc (K : ℝ) * T' ≤ (|cK| * L ^ kK) * P := by gcongr
      _ = |cK| * P * L ^ kK := by ring
      _ ≤ |cK| * P * L ^ (j + kK) := by gcongr
  have hQ0 : 0 ≤ Q := by linarith
  have hΛ : 0 ≤ L ^ (j + kK) := by positivity
  have h4' : ((T - T' * B : ℕ) : ℝ) ≤ (2 * Q + P) * L ^ (j + kK) :=
    h4.trans (le_mul_of_one_le_right (by linarith) hL1)
  have e : |c| * (2 * Q + P) + |cK| * P + (2 * Q + P) ≤ (2 * |c| + |cK| + 3) * (P + Q) := by
    have h5 := mul_nonneg (abs_nonneg c) hP0
    have h6 := mul_nonneg (abs_nonneg cK) hQ0
    nlinarith
  have e' := mul_le_mul_of_nonneg_right e hΛ
  calc (B : ℝ) * (c * Real.sqrt (n * T') * lj ^ j) + K * T' + ((T - T' * B : ℕ) : ℝ)
      ≤ |c| * (2 * Q + P) * L ^ (j + kK) + |cK| * P * L ^ (j + kK) + (2 * Q + P) * L ^ (j + kK) := by
        linarith
    _ = (|c| * (2 * Q + P) + |cK| * P + (2 * Q + P)) * L ^ (j + kK) := by ring
    _ ≤ _ := e'

/-- The fallback case: if fewer than `n` blocks fit, then `T ≤ 3 n √T`. -/
lemma fallback_bound {n T : ℕ} (hn : 1 ≤ n) (hnT : n ≤ T) (h : T / Bn n T < n) :
    (T : ℝ) ≤ 3 * (n * Real.sqrt T) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
  have hsqT : 1 ≤ Real.sqrt T := by rw [Real.one_le_sqrt]; exact hT1
  have hx1 := one_le_xr hn hnT
  have hB0 : 0 < Bn n T := lt_of_lt_of_le (by omega) (le_Bn n T)
  have hlt : T < n * Bn n T := by
    have := Nat.lt_div_mul_add (a := T) (b := Bn n T) hB0
    have : T / Bn n T + 1 ≤ n := h
    nlinarith
  have hltR : (T : ℝ) < n * Bn n T := by exact_mod_cast hlt
  have hsq := Real.mul_self_sqrt (show (0 : ℝ) ≤ T by linarith)
  unfold Bn at hltR
  rcases le_total n ⌈xr n T⌉₊ with hm | hm
  · rw [max_eq_right hm] at hltR
    have hc : (⌈xr n T⌉₊ : ℝ) < xr n T + 1 := Nat.ceil_lt_add_one (by linarith)
    have h2 : (T : ℝ) < 2 * n * xr n T := by nlinarith
    have hx3 : xr n T ^ 3 * n = T := by
      unfold xr; rw [cube_rpow (by positivity)]; field_simp
    -- T^3 < 8 n^3 x^3 = 8 n^2 T, so T^2 < 8 n^2 and T < 3 n
    have h3 : (T : ℝ) ^ 3 < (2 * n * xr n T) ^ 3 := by
      exact pow_lt_pow_left₀ h2 (by linarith) (by norm_num)
    have h4 : (T : ℝ) ^ 2 < 8 * n ^ 2 := by
      have : (2 * n * xr n T) ^ 3 = 8 * n ^ 2 * T := by rw [mul_pow, mul_pow, ← hx3]; ring
      rw [this] at h3
      nlinarith
    have h5 : (T : ℝ) ≤ 3 * n := by nlinarith
    nlinarith
  · rw [max_eq_left hm] at hltR
    -- T < n², so √T < n
    have : Real.sqrt T ≤ n := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    nlinarith

end Pool.P0021

namespace Pool.P0021

lemma logb_two_le {y : ℝ} (hy : 1 ≤ y) : Real.logb 2 y ≤ 2 * Real.log y := by
  have h2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hy0 : 0 ≤ Real.log y := Real.log_nonneg hy
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

lemma one_le_log_nT {n T : ℕ} (hn : 2 ≤ n) (hnT : n ≤ T) : 1 ≤ Real.log (n * T) := by
  have h4 : (4 : ℝ) ≤ n * T := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have : (2 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
    nlinarith
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

end Pool.P0021

namespace Pool.P0021

lemma mul_pow_le_abs {a x L : ℝ} (m : ℕ) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    a * x ^ m ≤ |a| * L ^ m :=
  (mul_le_mul_of_nonneg_right (le_abs_self a) (pow_nonneg hx0 m)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hxL m) (abs_nonneg a))

/-- **Main theorem.** If `K`-query learners with polylogarithmic `K`, polylogarithmic memory and
regret `Õ(√(n T))` exist, then homogeneous single-query machines with polylogarithmic memory and regret
`Õ(n^{1/3} T^{2/3} + n √T)` exist. -/
theorem blockRate_of_kQueryLearners (H : KQueryLearners) : BlockRate := by
  obtain ⟨cK, C, c, kK, k, j, hH⟩ := H
  choose K A hK hMem hReg using hH
  have hBpos : ∀ n T : ℕ, 2 ≤ n → 0 < Bn n T := fun n T h => lt_of_lt_of_le (by omega) (le_Bn n T)
  let G : (n T : ℕ) → (h : 2 ≤ n ∧ n ≤ T / Bn n T) → Machine n := fun n T h =>
    (blockMachine (le_Bn n T) (hBpos n T h.1)
      (A n (T / Bn n T) (by have := h.1; omega) h.2)).withClock T
  let F : Family := fun n T hn =>
    if h : 2 ≤ n ∧ n ≤ T / Bn n T then G n T h else @trivialMachine n ⟨by omega⟩
  refine ⟨F, ?_, ⟨|C| + 3 * |cK| + 7, k + kK + 1, ?_⟩, ⟨2 * |c| + |cK| + 3, j + kK, ?_⟩⟩
  · intro n T hn
    simp only [F]
    split_ifs with h
    · exact Machine.withClock_isHomogeneous _ _
    · exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  · intro n T hn hnT
    have hL0 : 0 ≤ Real.log (n * T) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have : (1 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
      nlinarith)
    simp only [F]
    split_ifs with h
    · simp only [G]
      obtain ⟨hn2, hnT'⟩ := h
      set B := Bn n T with hBdef
      set T' := T / B with hT'def
      set L := Real.log (n * T) with hLdef
      have hL : 1 ≤ L := one_le_log_nT hn2 hnT
      have hT'1 : 1 ≤ T' := by omega
      have hBT : B ≤ T := le_trans (Nat.le_mul_of_pos_left B (by omega)) (Nat.div_mul_le_self T B)
      have hT'T : T' ≤ T := Nat.div_le_self T B
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hlj0 : 0 ≤ Real.log (n * T') := Real.log_nonneg (by
        have : (1 : ℝ) ≤ T' := by exact_mod_cast hT'1
        nlinarith)
      have hljL : Real.log (n * T') ≤ L := Real.log_le_log (by
        have : (1 : ℝ) ≤ T' := by exact_mod_cast hT'1
        nlinarith) (by
        have : (T' : ℝ) ≤ T := by exact_mod_cast hT'T
        nlinarith)
      rw [Machine.memBits_withClock, memBits_blockMachine _ _ _ (by omega)]
      have hA := (hMem n T' (by omega) hnT').trans (mul_pow_le_abs (a := C) k hlj0 hljL)
      have hKb := (hK n T' (by omega) hnT').trans (mul_pow_le_abs (a := cK) kK hlj0 hljL)
      have hlogn : Real.logb 2 n ≤ 2 * L := (logb_two_le hn1).trans (by
        have := Real.log_le_log (by linarith) (show (n : ℝ) ≤ n * T by
          have : (1 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
          nlinarith)
        linarith)
      have hlogB : Real.logb 2 B ≤ 2 * L := (logb_two_le (by
        have : 1 ≤ B := le_trans (by omega) (le_Bn n T)
        exact_mod_cast this)).trans (by
        have := Real.log_le_log (by
          have : 1 ≤ B := le_trans (by omega) (le_Bn n T)
          have : (1 : ℝ) ≤ B := by exact_mod_cast this
          linarith) (show (B : ℝ) ≤ n * T by
          have : (B : ℝ) ≤ T := by exact_mod_cast hBT
          nlinarith)
        linarith)
      have hlogT : Real.logb 2 ((T : ℝ) + 1) ≤ 2 * L := (logb_two_le (by
        have : (0 : ℝ) ≤ T := by positivity
        linarith)).trans (by
        have := Real.log_le_log (by positivity) (show (T : ℝ) + 1 ≤ n * T by
          have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
          have : (1 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
          nlinarith)
        linarith)
      set Λ := L ^ (k + kK + 1) with hΛ
      have hk : L ^ k ≤ Λ := pow_le_pow_right₀ hL (by omega)
      have hkK : L ^ kK * L ≤ Λ := by rw [← pow_succ]; exact pow_le_pow_right₀ hL (by omega)
      have hkK' : L ^ kK ≤ Λ := pow_le_pow_right₀ hL (by omega)
      have hL1 : L ≤ Λ := by
        calc L = L ^ 1 := (pow_one L).symm
          _ ≤ Λ := pow_le_pow_right₀ hL (by omega)
      have hΛ1 : 1 ≤ Λ := one_le_pow₀ hL
      have hcK := abs_nonneg cK
      have hC := abs_nonneg C
      have hKn : ((K n T' (by omega) hnT' : ℕ) : ℝ) + 1 ≤ |cK| * L ^ kK + 1 := by linarith
      have hlogn0 : 0 ≤ Real.logb 2 n := Real.logb_nonneg (by norm_num) hn1
      calc (A n T' _ hnT').memBits + ((K n T' _ hnT' : ℕ) + 1 : ℝ) * Real.logb 2 n +
            Real.logb 2 B + ((K n T' _ hnT' : ℕ) + 1 : ℝ) + Real.logb 2 ((T : ℝ) + 1)
          ≤ |C| * L ^ k + (|cK| * L ^ kK + 1) * (2 * L) + 2 * L + (|cK| * L ^ kK + 1) + 2 * L := by
            have : (0 : ℝ) ≤ |cK| * L ^ kK + 1 := by positivity
            have hprod : ((K n T' (by omega) hnT' : ℕ) + 1 : ℝ) * Real.logb 2 n ≤
                (|cK| * L ^ kK + 1) * (2 * L) :=
              (mul_le_mul_of_nonneg_right hKn hlogn0).trans (mul_le_mul_of_nonneg_left hlogn this)
            linarith
        _ = |C| * L ^ k + 2 * |cK| * (L ^ kK * L) + 2 * L + |cK| * L ^ kK + 1 + 2 * L + 2 * L := by ring
        _ ≤ |C| * Λ + 2 * |cK| * Λ + 2 * Λ + |cK| * Λ + Λ + 2 * Λ + 2 * Λ := by
            gcongr
        _ = (|C| + 3 * |cK| + 7) * Λ := by ring
    · have : (@trivialMachine n ⟨by omega⟩).memBits = 0 := by simp [Machine.memBits]
      rw [this]
      positivity
  · intro n T hn hnT ℓ
    simp only [F]
    split_ifs with h
    · simp only [G]
      obtain ⟨hn2, hnT'⟩ := h
      haveI : NeZero n := ⟨by omega⟩
      set B := Bn n T with hBdef
      set T' := T / B with hT'def
      have hT'1 : 1 ≤ T' := by omega
      have hT'T : T' ≤ T := Nat.div_le_self T B
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hL := one_le_log_nT hn2 hnT
      have hlj0 : 0 ≤ Real.log (n * T') := Real.log_nonneg (by
        have : (1 : ℝ) ≤ T' := by exact_mod_cast hT'1
        nlinarith)
      have hljL : Real.log (n * T') ≤ Real.log (n * T) := Real.log_le_log (by
        have : (1 : ℝ) ≤ T' := by exact_mod_cast hT'1
        nlinarith) (by
        have : (T' : ℝ) ≤ T := by exact_mod_cast hT'T
        nlinarith)
      rw [regret_withClock]
      have h1 := regret_le_regret_add
        (M := blockMachine (le_Bn n T) (hBpos n T hn2) (A n T' (by omega) hnT')) ℓ
        (Nat.div_mul_le_self T B)
      have h2 := regret_blockMachine_le (le_Bn n T) (hBpos n T hn2) (A n T' (by omega) hnT') T' _
        (hReg n T' (by omega) hnT') ℓ
      have hKb := (hK n T' (by omega) hnT').trans (mul_pow_le_abs (a := cK) kK hlj0 hljL)
      have h3 := main_bound hn2 hnT c cK (Real.log (n * T)) j kK (K n T' (by omega) hnT') hL hKb
        (Real.log (n * T')) hlj0 hljL
      linarith
    · rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · obtain rfl : n = 1 := by omega
        rw [regret_one]
        have : 0 ≤ Real.log ((1 : ℕ) * T : ℝ) := Real.log_nonneg (by
          have : (1 : ℝ) ≤ T := by exact_mod_cast hnT
          simpa using this)
        positivity
      · have hlt : T / Bn n T < n := by
          by_contra hc; exact h ⟨hn2, by omega⟩
        have hfb := fallback_bound (by omega) hnT hlt
        have hreg := regret_le (@trivialMachine n ⟨by omega⟩) ℓ T
        have hL := one_le_log_nT hn2 hnT
        have hΛ : 1 ≤ Real.log (n * T) ^ (j + kK) := one_le_pow₀ hL
        have hP : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) := by positivity
        have hQ : 0 ≤ (n : ℝ) * Real.sqrt T := by positivity
        have hc : 3 ≤ 2 * |c| + |cK| + 3 := by have := abs_nonneg c; have := abs_nonneg cK; linarith
        have e1 : 3 * ((n : ℝ) * Real.sqrt T) ≤
            (2 * |c| + |cK| + 3) * ((n : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) + n * Real.sqrt T) := by
          nlinarith
        have e2 := mul_le_mul_of_nonneg_left hΛ (le_trans (by positivity) e1)
        nlinarith

end Pool.P0021
