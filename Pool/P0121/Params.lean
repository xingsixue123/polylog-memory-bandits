import Pool.P0121.Pad
import Pool.P0079.Params

/-!
# Parameters for the threaded machine (all polynomial in `Λn = ⌊log₂ (n T)⌋ + 1`)
-/

open Finset

namespace Pool.P0121.TPar

variable (n T : ℕ)

/-- The master logarithm. -/
def Λn : ℕ := Nat.log 2 (n * T) + 1
/-- Threads. -/
def Dp : ℕ := Nat.log 2 (T / n) + 1
/-- Coarsest epoch length. -/
def B0 : ℕ := 2 ^ (Dp n T - 1)
/-- Thread epoch lengths. -/
def Btp (j : ℕ) : ℕ := 2 ^ (Dp n T - 1 - j)
/-- Units. -/
def NEp : ℕ := B0 n T * (T / B0 n T + 1)
/-- Dyadic levels (= merge cap). -/
def Lp : ℕ := Nat.log 2 (NEp n T) + 1
/-- Cover chain length. -/
def Rp : ℕ := Nat.log 2 (NEp n T) + 2
/-- Levels per thread. -/
def Lvp : ℕ := Lp n T + 2
/-- Merge iterations. -/
def Kp : ℕ := 4 * Rp n T * (2 * Λn n T)
/-- Inverse filter rate. -/
def Qd : ℕ := 64 * Rp n T * Kp n T * Dp n T * (2 * Lp n T + 1)
/-- P0042's `k`. -/
def kkp : ℕ := 32 * Λn n T ^ 2 * Qd n T
/-- P0042's `M0`. -/
def M0p : ℕ := 16 * Rp n T + 4 * Rp n T * kkp n T + 288 * Rp n T * Λn n T
/-- Sample cap. -/
def s0p : ℕ := 4 * Λn n T + 2
/-- Sub-pool cap. -/
def Sp : ℕ := M0p n T + s0p n T
/-- Copy cap (= queries per day). -/
def Nsp : ℕ := Dp n T * Lvp n T * (s0p n T + Dp n T * Lvp n T * Sp n T) + Dp n T * s0p n T
/-- Grid cap. -/
def Mp : ℕ := NEp n T * NEp n T

variable {n T}

section Facts

variable (hn : 2 ≤ n) (hnT : n ≤ T)
include hn hnT

theorem nT_ge : 4 ≤ n * T := by nlinarith

theorem Λn_ge : 3 ≤ Λn n T := by
  unfold Λn
  have h4 := nT_ge hn hnT
  have : 2 ≤ Nat.log 2 (n * T) := by
    exact Nat.le_log_of_pow_le (by norm_num) (by simpa using h4)
  omega

omit hn hnT in
theorem nT_lt : n * T < 2 ^ Λn n T := Nat.lt_pow_succ_log_self (by norm_num) _

theorem Tn_pos : 1 ≤ T / n := (Nat.one_le_div_iff (by omega)).2 hnT

omit hn hnT in
theorem Dp_pos : 1 ≤ Dp n T := by unfold Dp; omega

theorem Dp_le : Dp n T ≤ Λn n T := by
  unfold Dp Λn
  have : T / n ≤ n * T := (Nat.div_le_self T n).trans (by nlinarith)
  have := Nat.log_mono_right (b := 2) this
  omega

theorem B0_le : B0 n T ≤ T / n := by
  unfold B0 Dp
  simp only [Nat.add_sub_cancel]
  exact Nat.pow_log_le_self 2 (by have := Tn_pos hn hnT; omega)

omit hn hnT in
theorem B0_pos : 0 < B0 n T := Nat.two_pow_pos _

theorem T_lt_B0 : T < 2 * n * B0 n T := by
  have h1 : T / n < 2 ^ Dp n T := by unfold Dp; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : 2 ^ Dp n T = 2 * B0 n T := by
    unfold B0
    have := Dp_pos (n := n) (T := T)
    rw [← pow_succ']; congr 1
  rw [h2] at h1
  have := (Nat.div_lt_iff_lt_mul (by omega)).1 h1
  linarith

theorem NEp_gt : T < NEp n T := by
  unfold NEp
  have := Nat.lt_div_mul_add (a := T) (B0_pos (n := n) (T := T))
  rw [Nat.mul_comm] at this
  have e : B0 n T * (T / B0 n T + 1) = B0 n T * (T / B0 n T) + B0 n T := by ring
  rw [e]; linarith

theorem NEp_le : NEp n T ≤ 2 * T := by
  unfold NEp
  have h1 : B0 n T * (T / B0 n T) ≤ T := Nat.mul_div_le T (B0 n T)
  have h2 := B0_le hn hnT
  have h3 : T / n ≤ T := Nat.div_le_self T n
  have e : B0 n T * (T / B0 n T + 1) = B0 n T * (T / B0 n T) + B0 n T := by ring
  rw [e]; omega

theorem NEp_div : NEp n T / B0 n T ≤ 2 * n := by
  unfold NEp
  rw [Nat.mul_div_cancel_left _ (B0_pos (n := n) (T := T))]
  have := T_lt_B0 hn hnT
  have : T / B0 n T < 2 * n := (Nat.div_lt_iff_lt_mul (B0_pos (n := n) (T := T))).2 (by linarith)
  omega

theorem NEp_pos : 0 < NEp n T := by have := NEp_gt hn hnT; omega

theorem NEp_le_nT : NEp n T ≤ n * T := (NEp_le hn hnT).trans (by nlinarith)

omit hn hnT in
theorem NE_lt_Lp : NEp n T < 2 ^ Lp n T := Nat.lt_pow_succ_log_self (by norm_num) _

theorem Lp_le : Lp n T ≤ Λn n T := by
  unfold Lp Λn
  have := Nat.log_mono_right (b := 2) (NEp_le_nT hn hnT)
  omega

omit hn hnT in
theorem Rp_eq : Rp n T = Lp n T + 1 := by unfold Rp Lp; rfl

theorem NE_le_Rp : NEp n T ≤ 2 ^ (Rp n T - 1) := by
  rw [Rp_eq]; simp only [Nat.add_sub_cancel]; exact NE_lt_Lp.le

omit hn hnT in
theorem Rp_pos : 1 ≤ Rp n T := by rw [Rp_eq]; omega

omit hn hnT in
theorem B0_dvd : B0 n T ∣ NEp n T := Nat.dvd_mul_right _ _

theorem btHyp : Pool.P0065.BtHyp (Dp n T) (Btp n T) where
  hD := Dp_pos (n := n) (T := T)
  pos _ := Nat.two_pow_pos _
  dvd r hr := by
    unfold Btp
    apply Nat.pow_dvd_pow; omega
  last := by unfold Btp; simp

omit hn hnT in
theorem Btp_zero : Btp n T 0 = B0 n T := by unfold Btp B0; simp

omit hn hnT in
theorem Btp_ratio (j : ℕ) (hj : j + 1 < Dp n T) : (Btp n T j : ℝ) ≤ 2 * Btp n T (j + 1) := by
  unfold Btp
  have : Dp n T - 1 - j = (Dp n T - 1 - (j + 1)) + 1 := by omega
  rw [this, pow_succ]; push_cast; linarith

end Facts

section Poly

variable (hn : 2 ≤ n) (hnT : n ≤ T)
include hn hnT

theorem pow_mono_Λ {a b : ℕ} (hab : a ≤ b) : (Λn n T : ℝ) ^ a ≤ (Λn n T : ℝ) ^ b := by
  have : (1 : ℝ) ≤ Λn n T := by have := Λn_ge hn hnT; exact_mod_cast (by omega : 1 ≤ Λn n T)
  exact pow_le_pow_right₀ this hab

/-- **All parameters are polynomial in `Λ`.** -/
theorem params_poly :
    let Λ := (Λn n T : ℝ)
    (Dp n T : ℝ) ≤ Λ ∧ (Lp n T : ℝ) ≤ Λ ∧ (Rp n T : ℝ) ≤ 2 * Λ ∧ (Lvp n T : ℝ) ≤ 2 * Λ ∧
      (Kp n T : ℝ) ≤ 16 * Λ ^ 2 ∧ (Qd n T : ℝ) ≤ 6144 * Λ ^ 5 ∧ (kkp n T : ℝ) ≤ 196608 * Λ ^ 7 ∧
      (M0p n T : ℝ) ≤ 1600000 * Λ ^ 8 ∧ (s0p n T : ℝ) ≤ 5 * Λ ∧ (Sp n T : ℝ) ≤ 1700000 * Λ ^ 8 ∧
      (Nsp n T : ℝ) ≤ 7000000 * Λ ^ 12 := by
  intro Λ
  have hΛdef : Λ = (Λn n T : ℝ) := rfl
  have hΛ3 : (3 : ℝ) ≤ Λ := by rw [hΛdef]; exact_mod_cast Λn_ge hn hnT
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have hD : (Dp n T : ℝ) ≤ Λ := by rw [hΛdef]; exact_mod_cast Dp_le hn hnT
  have hL : (Lp n T : ℝ) ≤ Λ := by rw [hΛdef]; exact_mod_cast Lp_le hn hnT
  have hR : (Rp n T : ℝ) ≤ 2 * Λ := by
    have : (Rp n T : ℝ) = Lp n T + 1 := by rw [Rp_eq]; push_cast; ring
    linarith
  have hLv : (Lvp n T : ℝ) ≤ 2 * Λ := by unfold Lvp; push_cast; linarith
  have hK : (Kp n T : ℝ) ≤ 16 * Λ ^ 2 := by
    unfold Kp; push_cast
    have : (0 : ℝ) ≤ Rp n T := Nat.cast_nonneg _
    nlinarith
  have hQd : (Qd n T : ℝ) ≤ 6144 * Λ ^ 5 := by
    unfold Qd; push_cast
    have h1 : (0 : ℝ) ≤ Rp n T := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ Kp n T := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ Dp n T := Nat.cast_nonneg _
    have h4 : (2 * (Lp n T : ℝ) + 1) ≤ 3 * Λ := by linarith
    calc 64 * (Rp n T : ℝ) * Kp n T * Dp n T * (2 * Lp n T + 1)
        ≤ 64 * (2 * Λ) * (16 * Λ ^ 2) * Λ * (3 * Λ) := by gcongr
      _ = 6144 * Λ ^ 5 := by ring
  have hkk : (kkp n T : ℝ) ≤ 196608 * Λ ^ 7 := by
    unfold kkp; push_cast
    calc 32 * Λ ^ 2 * (Qd n T : ℝ) ≤ 32 * Λ ^ 2 * (6144 * Λ ^ 5) := by gcongr
      _ = 196608 * Λ ^ 7 := by ring
  have hM0 : (M0p n T : ℝ) ≤ 1600000 * Λ ^ 8 := by
    unfold M0p; push_cast
    have h1 : (0 : ℝ) ≤ Rp n T := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ kkp n T := Nat.cast_nonneg _
    have e1 : 16 * (Rp n T : ℝ) ≤ 32 * Λ ^ 8 := by
      have := pow_mono_Λ hn hnT (show 1 ≤ 8 by norm_num); simp only [pow_one] at this; nlinarith
    have e2 : 4 * (Rp n T : ℝ) * kkp n T ≤ 4 * (2 * Λ) * (196608 * Λ ^ 7) := by gcongr
    have e3 : 288 * (Rp n T : ℝ) * Λ ≤ 576 * Λ ^ 8 := by
      have := pow_mono_Λ hn hnT (show 2 ≤ 8 by norm_num)
      have : 288 * (Rp n T : ℝ) * Λ ≤ 288 * (2 * Λ) * Λ := by gcongr
      nlinarith
    nlinarith
  have hs0 : (s0p n T : ℝ) ≤ 5 * Λ := by unfold s0p; push_cast; linarith
  have hS : (Sp n T : ℝ) ≤ 1700000 * Λ ^ 8 := by
    unfold Sp; push_cast
    have := pow_mono_Λ hn hnT (show 1 ≤ 8 by norm_num); simp only [pow_one] at this
    nlinarith
  have hNs : (Nsp n T : ℝ) ≤ 7000000 * Λ ^ 12 := by
    unfold Nsp; push_cast
    have h1 : (0 : ℝ) ≤ Dp n T := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ Lvp n T := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ s0p n T := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ Sp n T := Nat.cast_nonneg _
    have hDL : (Dp n T : ℝ) * Lvp n T ≤ 2 * Λ ^ 2 := by nlinarith
    have hDL0 : (0 : ℝ) ≤ Dp n T * Lvp n T := by positivity
    have hin : (s0p n T : ℝ) + Dp n T * Lvp n T * Sp n T ≤ 5 * Λ + 2 * Λ ^ 2 * (1700000 * Λ ^ 8) := by
      have : (Dp n T : ℝ) * Lvp n T * Sp n T ≤ 2 * Λ ^ 2 * (1700000 * Λ ^ 8) := by gcongr
      linarith
    have hin0 : (0 : ℝ) ≤ s0p n T + Dp n T * Lvp n T * Sp n T := by positivity
    have e1 : (Dp n T : ℝ) * Lvp n T * (s0p n T + Dp n T * Lvp n T * Sp n T) ≤
        2 * Λ ^ 2 * (5 * Λ + 2 * Λ ^ 2 * (1700000 * Λ ^ 8)) := by gcongr
    have e2 : (Dp n T : ℝ) * s0p n T ≤ Λ * (5 * Λ) := by gcongr
    have p3 := pow_mono_Λ hn hnT (show 3 ≤ 12 by norm_num)
    have p2 := pow_mono_Λ hn hnT (show 2 ≤ 12 by norm_num)
    nlinarith
  exact ⟨hD, hL, hR, hLv, hK, hQd, hkk, hM0, hs0, hS, hNs⟩

end Poly

section Card

open Pool.P0121.TM

/-- The copies entering at unit `a` on thread `r`: exactly `n`. -/
theorem card_entT {n NE D : ℕ} [NeZero n] (hNE : 0 < NE) (hD : 0 < D) {a r : ℕ} (ha : a < NE) (hr : r < D) :
    (univ.filter (fun c : Cp n NE D => Pool.P0121.TM.E n NE D c = a ∧ thr0 n NE D c = r)).card = n := by
  classical
  have himg : univ.filter (fun c : Cp n NE D => Pool.P0121.TM.E n NE D c = a ∧ thr0 n NE D c = r) =
      univ.image (fun i : Fin n => Pool.P0121.TA.cop hNE hD r a i) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨arm n NE D c, ?_⟩
      apply Fin.ext
      unfold Pool.P0121.TA.cop arm
      unfold Pool.P0121.TM.E at h1
      unfold thr0 at h2
      simp only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hr]
      have e2 : c.1 / (D * n) = c.1 / n / D := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm n D]
      have key : (c.1 / (D * n) * D + c.1 / n % D) * n + c.1 % n = c.1 := by
        rw [e2, Nat.div_add_mod', Nat.div_add_mod']
      rw [← h1, ← h2]; exact key
    · rintro ⟨i, rfl⟩
      exact ⟨Pool.P0121.TA.E_cop hNE hD hr ha i, Pool.P0121.TA.thr0_cop hNE hD hr ha i⟩
  rw [himg, card_image_of_injective _ (fun i j h => by
    have := congrArg (arm n NE D) h
    rwa [Pool.P0121.TA.arm_cop hNE hD hr ha, Pool.P0121.TA.arm_cop hNE hD hr ha] at this), card_univ, Fintype.card_fin]

end Card

section Concrete

open Pool.P0121.TM Pool.P0121.TA

variable (n T : ℕ) [NeZero n]

/-- Filter rate. -/
noncomputable def qp : ℝ := 1 / (Qd n T : ℝ)
/-- Grid step. -/
noncomputable def εp : ℝ := 1 / (NEp n T : ℝ)
/-- Learner constant `R·(2L+1)·(log|Spec| + 2)`. -/
noncomputable def Qp : ℝ := (Rp n T : ℝ) * (2 * Lp n T + 1) *
  (Real.log (Fintype.card (Pool.P0089.Spec (Cp n (NEp n T) (Dp n T)) (Lp n T))) + 2)
/-- `s0 + D·Lv·S + 1`. -/
noncomputable def Sb : ℝ := ((s0p n T + Dp n T * Lvp n T * Sp n T + 1 : ℕ) : ℝ)
/-- `2n + 4n·D·Lv·Sb`. -/
noncomputable def Gp : ℝ := 2 * n + 4 * n * (Dp n T * Lvp n T * Sb n T)
/-- Learning rate. -/
noncomputable def ηp : ℝ := min 1 (Real.sqrt (2 * Gp n T * Qp n T / NEp n T))

theorem Rp_ge : 1 ≤ Rp n T := by rw [Rp_eq]; omega

theorem Qd_ge : 64 ≤ Qd n T := by
  unfold Qd Kp Λn
  have h1 := Rp_ge n T
  have h2 : 1 ≤ Dp n T := by unfold Dp; omega
  have h3 : 1 ≤ 4 * Rp n T * (2 * (Nat.log 2 (n * T) + 1)) := by
    have : 1 ≤ 2 * (Nat.log 2 (n * T) + 1) := by omega
    nlinarith
  have h4 : 1 ≤ 2 * Lp n T + 1 := by omega
  calc 64 = 64 * 1 * 1 * 1 * 1 := by norm_num
    _ ≤ _ := by gcongr

theorem qp_mem : 0 ≤ qp n T ∧ qp n T ≤ 1 := by
  unfold qp
  have : (64 : ℝ) ≤ Qd n T := by exact_mod_cast Qd_ge n T
  constructor
  · positivity
  · rw [div_le_one (by linarith)]; linarith

theorem ps_mem : 0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  constructor
  · positivity
  · rw [div_le_one (by linarith)]; exact this

/-- **The concrete threaded K-query machine.** -/
noncomputable def tmP : Pool.P0015.QMachine n (Nsp n T) :=
  (tmach (n := n) (NE := NEp n T) (D := Dp n T) (Lv := Lvp n T) (L := Lp n T) (M := Mp n T) (Lt := Lp n T)
    (K := Kp n T) (R := Rp n T) (Btp n T) (Pool.P0085.levTh (Lp n T) (Btp n T)) 1 (ηp n T) (εp n T) (Nsp n T)
    (ps_mem n) (qp_mem n T)).toQ

theorem four_pow_ge (x : ℕ) (hx : 2 ≤ x) : x * x + 2 * x + 2 ≤ 4 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih => rw [pow_succ]; nlinarith

/-- The failure scale. -/
noncomputable def Fbp : ℝ :=
  NEp n T * Dp n T * Real.exp (Real.exp 1 - 1 - (s0p n T + 1)) +
    NEp n T * Dp n T * (Lp n T + 1) * Kp n T *
      Pool.P0042.delta (Fintype.card (Cp n (NEp n T) (Dp n T))) (qp n T) (Rp n T) (kkp n T) (M0p n T)

open Classical in
/-- **Step A**: the concrete machine's regret is at most `regret_le`'s bound at the concrete parameters. -/
theorem regret_tmP_E (hn : 2 ≤ n) (hnT : n ≤ T) (ℓ : Pool.P0001.LossSeq n) :
    (tmP n T).regret ℓ T ≤
      1 + ((1 + Rp n T * αL n (NEp n T) (Dp n T) (Lp n T) (ηp n T) (εp n T)) * (NEp n T / Btp n T 0) +
        ηp n T / 2 * NEp n T + ((1 + Rp n T * αL n (NEp n T) (Dp n T) (Lp n T) (ηp n T) (εp n T)) * 2 + 1) *
        ((Dp n T * Lvp n T * (s0p n T + Dp n T * Lvp n T * Sp n T + 1) : ℝ) /
          (1 / (n : ℝ) * (1 - qp n T) ^ (Kp n T * (Dp n T * (2 * Lp n T + NEp n T / 2 ^ Lp n T + 1)))) +
          Dp n T * NEp n T * Fbp n T)) + NEp n T * Fbp n T := by
  have hNE := NEp_pos hn hnT
  have hR1 := Rp_ge n T
  have hΛ3 := Λn_ge hn hnT
  -- positivity of the learning rate
  have hQ0 : 0 < Qp n T := by
    unfold Qp
    have h1 : (1 : ℝ) ≤ Rp n T := by exact_mod_cast hR1
    have hc : 1 ≤ Fintype.card (Pool.P0089.Spec (Cp n (NEp n T) (Dp n T)) (Lp n T)) := by
      have : Nonempty (Pool.P0089.Spec (Cp n (NEp n T) (Dp n T)) (Lp n T)) :=
        ⟨(⟨0, Nat.mul_pos (Nat.mul_pos hNE (by have := Dp_pos (n := n) (T := T); omega)) (NeZero.pos n)⟩, 0,
          ⟨0, Nat.two_pow_pos _⟩)⟩
      exact Fintype.card_pos
    have h2 : 0 ≤ Real.log (Fintype.card (Pool.P0089.Spec (Cp n (NEp n T) (Dp n T)) (Lp n T))) :=
      Real.log_nonneg (by exact_mod_cast hc)
    positivity
  have hG0 : 0 < Gp n T := by
    unfold Gp Sb
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (0 : ℝ) ≤ Dp n T * Lvp n T * ((s0p n T + Dp n T * Lvp n T * Sp n T + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hη : 0 < ηp n T := by
    unfold ηp
    apply lt_min one_pos
    apply Real.sqrt_pos.2
    have : (0 : ℝ) < NEp n T := by exact_mod_cast hNE
    positivity
  have hη1 : ηp n T ≤ 1 := min_le_left _ _
  have hε : 0 < εp n T := by
    unfold εp
    have : (0 : ℝ) < NEp n T := (by exact_mod_cast hNE)
    positivity
  have hM : NEp n T * ⌊ηp n T / εp n T⌋₊ ≤ Mp n T := by
    unfold Mp
    apply Nat.mul_le_mul_left
    apply Nat.floor_le_of_le
    unfold εp
    have : (0 : ℝ) < NEp n T := by exact_mod_cast hNE
    rw [div_div_eq_mul_div, div_one]
    nlinarith
  have hNL : NEp n T ≤ 2 ^ Lp n T := (NE_lt_Lp (n := n) (T := T)).le
  have hTm : (NEp n T : ℝ) ≤ 2 ^ (Rp n T - 1) * 1 := by
    rw [mul_one]; exact_mod_cast NE_le_Rp hn hnT
  have hM0 : 16 * (Rp n T : ℝ) ≤ M0p n T := by unfold M0p; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) (kkp n T)]
  have hk : 4 * (Rp n T : ℝ) * kkp n T ≤ M0p n T := by unfold M0p; push_cast; nlinarith
  have hp : qp n T * (Real.exp 1 - 1) ≤ 1 / (32 * Rp n T) := by
    unfold qp
    have hQd : (64 : ℝ) * Rp n T ≤ Qd n T := by
      unfold Qd; push_cast
      have h1 : (1 : ℝ) ≤ Kp n T := by
        unfold Kp; have : 1 ≤ 4 * Rp n T * (2 * Λn n T) := by nlinarith
        exact_mod_cast this
      have h2 : (1 : ℝ) ≤ Dp n T := by exact_mod_cast Dp_pos (n := n) (T := T)
      have h3 : (1 : ℝ) ≤ 2 * Lp n T + 1 := by have : (0 : ℝ) ≤ Lp n T := Nat.cast_nonneg _; linarith
      have hR : (0 : ℝ) ≤ Rp n T := Nat.cast_nonneg _
      calc 64 * (Rp n T : ℝ) = 64 * Rp n T * 1 * 1 * 1 := by ring
        _ ≤ 64 * Rp n T * Kp n T * Dp n T * (2 * Lp n T + 1) := by gcongr
    have he : Real.exp 1 - 1 ≤ 2 := by have := Real.exp_one_lt_d9; linarith
    have hR : (1 : ℝ) ≤ Rp n T := by exact_mod_cast hR1
    have hQpos : (0 : ℝ) < Qd n T := by linarith
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hQpos (by positivity)]
    nlinarith [Real.exp_pos 1]
  have hs : ∀ a r : ℕ, a < NEp n T → r < Dp n T →
      ∑ F ∈ (Finset.univ.filter fun c => Pool.P0121.TM.E n (NEp n T) (Dp n T) c = a ∧
          thr0 n (NEp n T) (Dp n T) c = r).powerset,
        (1 / (n : ℝ)) ^ F.card * (1 - 1 / (n : ℝ)) ^ ((Finset.univ.filter fun c =>
          Pool.P0121.TM.E n (NEp n T) (Dp n T) c = a ∧ thr0 n (NEp n T) (Dp n T) c = r).card - F.card) *
          (if s0p n T < F.card then 1 else 0) ≤ Real.exp (Real.exp 1 - 1 - (s0p n T + 1)) := by
    intro a r ha hr
    refine (Pool.P0063.sample_tail_le (ps_mem n) _ (s0p n T)).trans (le_of_eq ?_)
    congr 1
    have hc : (Finset.univ.filter fun c => Pool.P0121.TM.E n (NEp n T) (Dp n T) c = a ∧
        thr0 n (NEp n T) (Dp n T) c = r).card = n := by
      have := card_entT (n := n) hNE (Dp_pos (n := n) (T := T)) ha hr
      convert this
    rw [hc]
    have h2n : (2 : ℝ) ≤ n := (by exact_mod_cast hn)
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hρS : (1 - 1 / (4 * Rp n T : ℝ)) ^ Kp n T * (Sp n T + (s0p n T + Dp n T * Lvp n T * Sp n T)) ≤ Sp n T := by
    have hR : (1 : ℝ) ≤ Rp n T := by exact_mod_cast hR1
    have hx0 : 0 ≤ 1 - 1 / (4 * Rp n T : ℝ) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    have hhalf := Pool.P0079.rho_half hR1
    have hpow : (1 - 1 / (4 * Rp n T : ℝ)) ^ Kp n T ≤ (1 / 2) ^ (2 * Λn n T) := by
      unfold Kp
      rw [pow_mul]
      apply pow_le_pow_left₀ (pow_nonneg hx0 _)
      push_cast; linarith
    have hDL : Dp n T * Lvp n T + 2 ≤ 4 ^ Λn n T := by
      have h1 := Dp_le hn hnT
      have h2 : Lvp n T ≤ Λn n T + 2 := by unfold Lvp; have := Lp_le hn hnT; omega
      have h3 := four_pow_ge (Λn n T) (by omega)
      have : Dp n T * Lvp n T ≤ Λn n T * (Λn n T + 2) := Nat.mul_le_mul h1 h2
      nlinarith
    have hs0S : (s0p n T : ℝ) ≤ Sp n T := by unfold Sp; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (M0p n T)]
    have hS0 : (0 : ℝ) ≤ Sp n T := Nat.cast_nonneg _
    have hsum : (Sp n T : ℝ) + (s0p n T + Dp n T * Lvp n T * Sp n T) ≤ (Dp n T * Lvp n T + 2 : ℕ) * Sp n T := by
      push_cast; nlinarith
    have h4 : ((Dp n T * Lvp n T + 2 : ℕ) : ℝ) ≤ 4 ^ Λn n T := by exact_mod_cast hDL
    have h5 : ((1 : ℝ) / 2) ^ (2 * Λn n T) * 4 ^ Λn n T = 1 := by
      rw [pow_mul, ← mul_pow]; norm_num
    have hpos : (0 : ℝ) ≤ (1 - 1 / (4 * Rp n T : ℝ)) ^ Kp n T := pow_nonneg hx0 _
    calc (1 - 1 / (4 * Rp n T : ℝ)) ^ Kp n T * (Sp n T + (s0p n T + Dp n T * Lvp n T * Sp n T))
        ≤ (1 - 1 / (4 * Rp n T : ℝ)) ^ Kp n T * (((Dp n T * Lvp n T + 2 : ℕ) : ℝ) * Sp n T) := by gcongr
      _ ≤ ((1 : ℝ) / 2) ^ (2 * Λn n T) * (4 ^ Λn n T * Sp n T) := by gcongr
      _ = Sp n T := by rw [← mul_assoc, h5, one_mul]
  have hNs : Dp n T * Lvp n T * (s0p n T + Dp n T * Lvp n T * Sp n T) + Dp n T * s0p n T ≤ Nsp n T := le_rfl
  have hps0 : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (2 : ℝ) ≤ n := (by exact_mod_cast hn)
    positivity
  have hq1 : qp n T < 1 := by
    unfold qp
    have : (64 : ℝ) ≤ Qd n T := (by exact_mod_cast Qd_ge n T)
    rw [div_lt_one (by linarith)]; linarith
  have hMS : (M0p n T : ℝ) ≤ Sp n T := by
    unfold Sp; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (s0p n T)]
  rw [Pool.P0121.TP.regret_padZ _ ℓ (show T ≤ NEp n T + 1 by have := NEp_gt hn hnT; omega)]
  have h := regret_le (Lm := Lp n T) (Btp n T) 1 (ηp n T) (εp n T) (Nsp n T) (ps_mem n) (qp_mem n T)
    (btHyp hn hnT) le_rfl le_rfl (by rw [Btp_zero]; exact B0_dvd) hNE hη hε hM hNL zero_le_one hR1
    2 (by norm_num) (fun j hj => Btp_ratio j hj) hps0 hq1
    (NEp n T) le_rfl hTm (M0p n T) (kkp n T) hM0 hk hp (s0p n T) _ hs (Sp n T) hMS hρS hNs (Pool.P0121.TP.padZ ℓ T)
  refine h.trans (le_of_eq ?_)
  unfold Fbp
  rfl

section Core

/-- The learning-rate tradeoff with `η = min 1 √(2GQ/NE)`. -/
theorem eta_core {Q G NE : ℝ} (hQ : 0 < Q) (hG : 0 < G) (hNE : 1 ≤ NE) (hGQ : 1 ≤ 2 * G * Q) :
    let η := min 1 (Real.sqrt (2 * G * Q / NE))
    Q / η * G + η / 2 * NE ≤ Real.sqrt (2 * Q * G * NE) + 2 * Q * G ∧ 1 / η ≤ 1 + Real.sqrt NE := by
  intro η
  have hNE0 : 0 < NE := by linarith
  have hx : 0 < 2 * G * Q / NE := by positivity
  set r := Real.sqrt (2 * G * Q / NE) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hx
  have hr2 : r ^ 2 = 2 * G * Q / NE := Real.sq_sqrt hx.le
  have hs : Real.sqrt (2 * Q * G * NE) = r * NE := by
    have e : 2 * Q * G * NE = (r * NE) ^ 2 := by
      rw [mul_pow, hr2]; field_simp
    rw [e]; exact Real.sqrt_sq (by positivity)
  have hη0 : 0 < η := lt_min one_pos hr0
  by_cases h : r ≤ 1
  · have hη : η = r := min_eq_right h
    rw [hη, hs]
    constructor
    · have : Q / r * G = r * NE / 2 := by
        field_simp
        have := hr2; field_simp at this; nlinarith
      rw [this]
      nlinarith [hQ, hG]
    · have hsq : 1 / r ≤ Real.sqrt NE := by
        rw [div_le_iff₀ hr0]
        have h1 : (Real.sqrt NE * r) ^ 2 = 2 * G * Q := by
          rw [mul_pow, Real.sq_sqrt hNE0.le, hr2]; field_simp
        have h3 : 0 ≤ Real.sqrt NE * r := by positivity
        nlinarith [Real.sqrt_nonneg NE, sq_nonneg (Real.sqrt NE * r - 1)]
      linarith
  · push Not at h
    have hη : η = 1 := min_eq_left h.le
    rw [hη]
    constructor
    · have hNEle : NE < 2 * G * Q := by
        have : 1 < r ^ 2 := by nlinarith
        rw [hr2, lt_div_iff₀ hNE0] at this; linarith
      have : 0 ≤ Real.sqrt (2 * Q * G * NE) := Real.sqrt_nonneg _
      rw [div_one]; nlinarith
    · have := Real.sqrt_nonneg NE; rw [div_one]; linarith

end Core

section Arith

/-- Structural algebra of the regret bound. -/
theorem arith1 {E n NE Q G η Y Z W Fb B X : ℝ} (hQη : 0 ≤ Q / η) (hY0 : 0 ≤ Y)
    (hE : E ≤ 1 + ((1 + Q / η) * B + η / 2 * NE + ((1 + Q / η) * 2 + 1) * (X + Z)) + NE * Fb)
    (hB : B ≤ 2 * n) (hX : X ≤ 2 * Y) (hG : G = 2 * n + 4 * Y)
    (hcore : Q / η * G + η / 2 * NE ≤ Real.sqrt (2 * Q * G * NE) + 2 * Q * G)
    (hZ : Z ≤ 3 * W) (hNEFb : NE * Fb ≤ 3 * W) (hQηZ : 2 * (Q / η) * Z ≤ 12 * Q * W) :
    E ≤ 1 + 2 * n + 6 * Y + 12 * W + Real.sqrt (2 * Q * G * NE) + 2 * Q * G + 12 * Q * W := by
  have h1 : (1 + Q / η) * B ≤ (1 + Q / η) * (2 * n) := mul_le_mul_of_nonneg_left hB (by linarith)
  have h2 : ((1 + Q / η) * 2 + 1) * (X + Z) ≤ ((1 + Q / η) * 2 + 1) * (2 * Y + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have e : (1 + Q / η) * (2 * n) + η / 2 * NE + ((1 + Q / η) * 2 + 1) * (2 * Y + Z) =
      2 * n + 6 * Y + 3 * Z + (Q / η * (2 * n + 4 * Y) + η / 2 * NE) + 2 * (Q / η) * Z := by ring
  rw [hG] at hcore ⊢
  linarith

/-- Polynomial bounds to `√(nT)·Λ^16`. -/
theorem arith2 {n T NE Λ Q G Y W : ℝ} (hn : 2 ≤ n) (hnT : n ≤ T) (hNE : NE ≤ 2 * T) (hNE0 : 0 ≤ NE)
    (hΛ : 3 ≤ Λ) (hQ0 : 0 ≤ Q) (hG0 : 0 ≤ G) (hQ : Q ≤ 36 * Λ ^ 3) (hG : G ≤ 28100000 * n * Λ ^ 12)
    (hY : Y ≤ 7000000 * n * Λ ^ 12) (hW0 : 0 ≤ W) (hW : W ≤ 32 * Λ ^ 5) :
    1 + 2 * n + 6 * Y + 12 * W + Real.sqrt (2 * Q * G * NE) + 2 * Q * G + 12 * Q * W ≤
      2100000000 * Real.sqrt (n * T) * Λ ^ 16 := by
  have hT0 : 0 ≤ T := by linarith
  have hsq : n ≤ Real.sqrt (n * T) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsq1 : 1 ≤ Real.sqrt (n * T) := by linarith
  have hΛ1 : 1 ≤ Λ := by linarith
  have pw : ∀ a b : ℕ, a ≤ b → Λ ^ a ≤ Λ ^ b := fun a b h => pow_le_pow_right₀ hΛ1 h
  have p16 : ∀ a : ℕ, a ≤ 16 → Λ ^ a ≤ Λ ^ 16 := fun a h => pw a 16 h
  have hS0 : 0 ≤ Real.sqrt (n * T) := Real.sqrt_nonneg _
  have hΛ16 : 0 ≤ Λ ^ 16 := by positivity
  -- the square-root term
  have hroot : Real.sqrt (2 * Q * G * NE) ≤ 64000 * Real.sqrt (n * T) * Λ ^ 16 := by
    have hin : 2 * Q * G * NE ≤ (64000 * Real.sqrt (n * T) * Λ ^ 8) ^ 2 := by
      have hsq2 : Real.sqrt (n * T) ^ 2 = n * T := Real.sq_sqrt (by nlinarith)
      have hQG : Q * G ≤ 36 * Λ ^ 3 * (28100000 * n * Λ ^ 12) := mul_le_mul hQ hG hG0 (by positivity)
      have e : (64000 * Real.sqrt (n * T) * Λ ^ 8) ^ 2 = 4096000000 * (n * T) * Λ ^ 16 := by
        rw [mul_pow, mul_pow, hsq2]; ring
      rw [e]
      have p15 := pw 15 16 (by norm_num)
      have : 2 * Q * G * NE ≤ 2 * (36 * Λ ^ 3 * (28100000 * n * Λ ^ 12)) * (2 * T) := by
        have := mul_le_mul hQG hNE hNE0 (by positivity)
        nlinarith
      have e2 : 2 * (36 * Λ ^ 3 * (28100000 * n * Λ ^ 12)) * (2 * T) = 4046400000 * (n * T) * Λ ^ 15 := by ring
      have hnT0 : 0 ≤ n * T := by nlinarith
      nlinarith
    calc Real.sqrt (2 * Q * G * NE) ≤ Real.sqrt ((64000 * Real.sqrt (n * T) * Λ ^ 8) ^ 2) := Real.sqrt_le_sqrt hin
      _ = 64000 * Real.sqrt (n * T) * Λ ^ 8 := Real.sqrt_sq (by positivity)
      _ ≤ 64000 * Real.sqrt (n * T) * Λ ^ 16 :=
          mul_le_mul_of_nonneg_left (pw 8 16 (by norm_num)) (by positivity)
  have t1 : 1 ≤ Real.sqrt (n * T) * Λ ^ 16 := by
    have : 1 ≤ Λ ^ 16 := one_le_pow₀ hΛ1
    nlinarith
  have t2 : 2 * n ≤ 2 * (Real.sqrt (n * T) * Λ ^ 16) := by
    have : 1 ≤ Λ ^ 16 := one_le_pow₀ hΛ1; nlinarith
  have t3 : 6 * Y ≤ 42000000 * (Real.sqrt (n * T) * Λ ^ 16) := by
    have := p16 12 (by norm_num); nlinarith
  have t4 : 12 * W ≤ 384 * (Real.sqrt (n * T) * Λ ^ 16) := by
    have := p16 5 (by norm_num); nlinarith
  have t5 : 2 * Q * G ≤ 2023200000 * (Real.sqrt (n * T) * Λ ^ 16) := by
    have hQG : Q * G ≤ 36 * Λ ^ 3 * (28100000 * n * Λ ^ 12) := mul_le_mul hQ hG hG0 (by positivity)
    have e : 36 * Λ ^ 3 * (28100000 * n * Λ ^ 12) = 1011600000 * n * Λ ^ 15 := by ring
    have := pw 15 16 (by norm_num)
    have hΛ15 : 0 ≤ Λ ^ 15 := by positivity
    nlinarith
  have t6 : 12 * Q * W ≤ 13824 * (Real.sqrt (n * T) * Λ ^ 16) := by
    have hQW : Q * W ≤ 36 * Λ ^ 3 * (32 * Λ ^ 5) := mul_le_mul hQ hW hW0 (by positivity)
    have e : 36 * Λ ^ 3 * (32 * Λ ^ 5) = 1152 * Λ ^ 8 := by ring
    have := p16 8 (by norm_num)
    nlinarith
  nlinarith

end Arith

section StepB

variable {n T}
variable (hn : 2 ≤ n) (hnT : n ≤ T)
include hn hnT

theorem two_pow_Λ_ge : n * T + 1 ≤ 2 ^ Λn n T := nT_lt (n := n) (T := T)

theorem NE1_le : NEp n T + 1 ≤ 2 ^ Λn n T := by
  have := NEp_le_nT hn hnT; have := two_pow_Λ_ge hn hnT; omega

omit [NeZero n] hn hnT in
theorem log_le_of_le_two_pow {x k : ℕ} (hx : x ≤ 2 ^ k) (hx1 : 1 ≤ x) : Real.log x ≤ k := by
  have h1 : Real.log x ≤ Real.log ((2 : ℝ) ^ k) :=
    Real.log_le_log (by exact_mod_cast hx1) (by exact_mod_cast hx)
  rw [Real.log_pow] at h1
  have : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)]

/-- `log (N + 1) ≤ 3Λ` for the number of copies `N`. -/
theorem logN_le : Real.log ((Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) : ℕ) + 1 : ℝ) ≤ 3 * Λn n T := by
  rw [Fintype.card_fin]
  have hNE := NEp_le_nT hn hnT
  have hD : Dp n T ≤ n * T := by
    have h1 : Dp n T ≤ T / n := by
      unfold Dp; have := Nat.log_lt_self 2 (show T / n ≠ 0 by have := Tn_pos hn hnT; omega); omega
    have h2 : T / n ≤ T := Nat.div_le_self T n
    nlinarith
  have hn' : n ≤ n * T := by nlinarith
  have hlt := two_pow_Λ_ge hn hnT
  have h3 : NEp n T * Dp n T * n + 1 ≤ 2 ^ (3 * Λn n T) := by
    have : NEp n T * Dp n T * n ≤ (n * T) * (n * T) * (n * T) := Nat.mul_le_mul (Nat.mul_le_mul hNE hD) hn'
    have h2 : (n * T) * (n * T) * (n * T) + 1 ≤ 2 ^ Λn n T * 2 ^ Λn n T * 2 ^ Λn n T := by
      have hp : n * T < 2 ^ Λn n T := by omega
      have := Nat.mul_lt_mul'' (Nat.mul_lt_mul'' hp hp) hp
      omega
    have e : 2 ^ (3 * Λn n T) = 2 ^ Λn n T * 2 ^ Λn n T * 2 ^ Λn n T := by ring
    omega
  have := log_le_of_le_two_pow h3 (by omega)
  push_cast at this ⊢
  linarith

theorem exp_s0_le : Real.exp (Real.exp 1 - 1 - (s0p n T + 1)) ≤ 1 / ((NEp n T : ℝ) + 1) ^ 4 := by
  have hNE1 : ((NEp n T : ℝ) + 1) ≤ Real.exp (Λn n T) := by
    have h1 : ((NEp n T + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ Λn n T := by exact_mod_cast NE1_le hn hnT
    have h2 : (2 : ℝ) ^ Λn n T ≤ Real.exp 1 ^ Λn n T :=
      pow_le_pow_left₀ (by norm_num) (by have := Real.add_one_le_exp (1 : ℝ); linarith) _
    rw [← Real.exp_nat_mul, mul_one] at h2
    push_cast at h1; linarith
  have hpos : (0 : ℝ) < (NEp n T : ℝ) + 1 := by positivity
  rw [le_div_iff₀ (by positivity)]
  have he : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hs : (s0p n T : ℝ) = 4 * Λn n T + 2 := by unfold s0p; push_cast; ring
  have h4 : ((NEp n T : ℝ) + 1) ^ 4 ≤ Real.exp (4 * Λn n T) := by
    rw [show (4 : ℝ) * Λn n T = (Λn n T : ℝ) * 4 by ring, Real.exp_mul]
    have : Real.exp (Λn n T) ^ (4 : ℝ) = Real.exp (Λn n T) ^ (4 : ℕ) := by norm_cast
    rw [this]
    exact pow_le_pow_left₀ hpos.le hNE1 4
  calc Real.exp (Real.exp 1 - 1 - (s0p n T + 1)) * ((NEp n T : ℝ) + 1) ^ 4
      ≤ Real.exp (-(4 * Λn n T)) * Real.exp (4 * Λn n T) := by
        apply mul_le_mul _ h4 (by positivity) (Real.exp_pos _).le
        apply Real.exp_le_exp.2
        rw [hs]; linarith
    _ = 1 := by rw [← Real.exp_add]; simp

theorem delta_le' : Pool.P0042.delta (Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T))) (qp n T) (Rp n T) (kkp n T)
    (M0p n T) ≤ 2 / ((NEp n T : ℝ) + 1) ^ 3 := by
  have hR1 := Rp_ge n T
  have hlog := logN_le hn hnT
  have hΛ : (3 : ℝ) ≤ Λn n T := by exact_mod_cast Λn_ge hn hnT
  have hR : (Rp n T : ℝ) ≤ 2 * Λn n T := by
    have : (Rp n T : ℝ) = Lp n T + 1 := by rw [Rp_eq]; push_cast; ring
    have : (Lp n T : ℝ) ≤ Λn n T := by exact_mod_cast Lp_le hn hnT
    linarith
  have hRpos : (1 : ℝ) ≤ Rp n T := by exact_mod_cast hR1
  have hqk : qp n T * kkp n T = 32 * (Λn n T : ℝ) ^ 2 := by
    unfold qp kkp
    have : (64 : ℝ) ≤ Qd n T := by exact_mod_cast Qd_ge n T
    push_cast
    field_simp
  have hk : ((Rp n T : ℝ) + 1 + 3) * Real.log ((Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) : ℕ) + 1) +
      Real.log (2 * Rp n T) ≤ qp n T * kkp n T := by
    rw [hqk]
    have hl2R : Real.log (2 * Rp n T) ≤ 2 * Rp n T := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * Rp n T by positivity); linarith
    have hlogN0 : 0 ≤ Real.log ((Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) : ℕ) + 1 : ℝ) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)));
                          linarith)
    have h1 : ((Rp n T : ℝ) + 1 + 3) * Real.log ((Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) : ℕ) + 1) ≤
        (2 * Λn n T + 4) * (3 * Λn n T) := by
      apply mul_le_mul (by linarith) hlog hlogN0 (by positivity)
    nlinarith
  have hM : 32 * (Rp n T : ℝ) * 3 * Real.log ((Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) : ℕ) + 1) ≤
      M0p n T := by
    unfold M0p; push_cast
    have h0 : (0 : ℝ) ≤ Rp n T := by linarith
    have : 32 * (Rp n T : ℝ) * 3 * Real.log ((Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) : ℕ) + 1) ≤
        96 * Rp n T * (3 * Λn n T) := by
      have := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 96 * Rp n T by positivity); linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) (kkp n T)]
  have h := Pool.P0079.delta_le hR1 (qp_mem n T).1 (qp_mem n T).2 hk hM
  refine h.trans ?_
  have hN : ((NEp n T : ℝ) + 1) ≤ (Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) : ℕ) + 1 := by
    rw [Fintype.card_fin]
    have : NEp n T ≤ NEp n T * Dp n T * n := by
      have h1 := Dp_pos (n := n) (T := T); have h2 := NeZero.one_le (n := n)
      calc NEp n T = NEp n T * 1 * 1 := by ring
        _ ≤ NEp n T * Dp n T * n := by gcongr
    push_cast; exact_mod_cast (show NEp n T + 1 ≤ NEp n T * Dp n T * n + 1 by omega)
  have hpos : (0 : ℝ) < (NEp n T : ℝ) + 1 := by positivity
  rw [← Real.log_rpow (by linarith), Real.exp_neg, Real.exp_log (by positivity)]
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply inv_anti₀ (by positivity)
  have h3 : ((Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) : ℕ) + 1 : ℝ) ^ (3 : ℝ) =
      ((Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) : ℕ) + 1 : ℝ) ^ (3 : ℕ) := by norm_cast
  rw [h3]
  exact pow_le_pow_left₀ hpos.le hN 3

theorem Fbp_le : Fbp n T ≤ 3 * Dp n T * (Lp n T + 1) * Kp n T / ((NEp n T : ℝ) + 1) ^ 2 := by
  have h1 := exp_s0_le hn hnT
  have h2 := delta_le' hn hnT
  set X := (NEp n T : ℝ) + 1 with hX
  have hX1 : 1 ≤ X := by rw [hX]; have := Nat.cast_nonneg (α := ℝ) (NEp n T); linarith
  have hX0 : 0 < X := by linarith
  have hNE : (NEp n T : ℝ) ≤ X := by rw [hX]; linarith
  have hNE0 : (0 : ℝ) ≤ NEp n T := Nat.cast_nonneg _
  have hD : (1 : ℝ) ≤ Dp n T := by exact_mod_cast Dp_pos (n := n) (T := T)
  have hL : (1 : ℝ) ≤ (Lp n T : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) (Lp n T); linarith
  have hK : (1 : ℝ) ≤ Kp n T := by
    have : 1 ≤ Kp n T := by unfold Kp; have := Rp_ge n T; have := Λn_ge hn hnT; nlinarith
    exact_mod_cast this
  have hd0 : 0 ≤ Pool.P0042.delta (Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T))) (qp n T) (Rp n T) (kkp n T)
      (M0p n T) := Pool.P0042.delta_nonneg (qp_mem n T).2
  unfold Fbp
  rw [le_div_iff₀ (by positivity)]
  have e1 : (NEp n T : ℝ) * Dp n T * Real.exp (Real.exp 1 - 1 - (s0p n T + 1)) * X ^ 2 ≤ Dp n T := by
    have : (NEp n T : ℝ) * Dp n T * Real.exp (Real.exp 1 - 1 - (s0p n T + 1)) * X ^ 2 ≤
        X * Dp n T * (1 / X ^ 4) * X ^ 2 := by
      gcongr
    calc _ ≤ X * Dp n T * (1 / X ^ 4) * X ^ 2 := this
      _ = Dp n T * (1 / X) := by field_simp
      _ ≤ Dp n T * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          rw [div_le_one hX0]; exact hX1
      _ = Dp n T := mul_one _
  have e2 : (NEp n T : ℝ) * Dp n T * (Lp n T + 1) * Kp n T *
      Pool.P0042.delta (Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T))) (qp n T) (Rp n T) (kkp n T) (M0p n T) *
      X ^ 2 ≤ 2 * (Dp n T * (Lp n T + 1) * Kp n T) := by
    have hDLK : (0 : ℝ) ≤ Dp n T * (Lp n T + 1) * Kp n T := by positivity
    calc _ ≤ X * Dp n T * (Lp n T + 1) * Kp n T * (2 / X ^ 3) * X ^ 2 := by gcongr
      _ = 2 * (Dp n T * (Lp n T + 1) * Kp n T) := by field_simp
  have e3 : (Dp n T : ℝ) ≤ Dp n T * (Lp n T + 1) * Kp n T := by
    have : (1 : ℝ) ≤ (Lp n T + 1) * Kp n T := by nlinarith
    nlinarith
  nlinarith

theorem NE_div_B0_le : (NEp n T : ℝ) / (Btp n T 0 : ℝ) ≤ 2 * n := by
  rw [Btp_zero]
  have hB := B0_pos (n := n) (T := T)
  have e : ((NEp n T / B0 n T : ℕ) : ℝ) = (NEp n T : ℝ) / B0 n T := Nat.cast_div B0_dvd (by exact_mod_cast hB.ne')
  rw [← e]
  exact_mod_cast NEp_div hn hnT

theorem NE_div_pow_L : NEp n T / 2 ^ Lp n T = 0 := Nat.div_eq_of_lt NE_lt_Lp

theorem half_le_pow : (1 : ℝ) / 2 ≤ (1 - qp n T) ^ (Kp n T * (Dp n T * (2 * Lp n T + NEp n T / 2 ^ Lp n T + 1))) := by
  rw [NE_div_pow_L hn hnT, Nat.add_zero]
  apply Pool.P0079.one_sub_pow_ge_half (qp_mem n T).1 (qp_mem n T).2
  unfold qp Qd
  have hR : (1 : ℝ) ≤ Rp n T := by exact_mod_cast Rp_ge n T
  have hpos : (0 : ℝ) < 64 * Rp n T * Kp n T * Dp n T * (2 * Lp n T + 1) := by
    have : (1 : ℝ) ≤ Kp n T := by
      have : 1 ≤ Kp n T := by unfold Kp; have := Rp_ge n T; have := Λn_ge hn hnT; nlinarith
      exact_mod_cast this
    have : (1 : ℝ) ≤ Dp n T := by exact_mod_cast Dp_pos (n := n) (T := T)
    positivity
  push_cast
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Kp n T), Nat.cast_nonneg (α := ℝ) (Dp n T), Nat.cast_nonneg (α := ℝ) (Lp n T)]

theorem logcard_le : Real.log (Fintype.card (Pool.P0089.Spec (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) (Lp n T))) ≤
    5 * Λn n T := by
  have hc : Fintype.card (Pool.P0089.Spec (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) (Lp n T)) =
      NEp n T * Dp n T * n * ((Lp n T + 1) * 2 ^ Lp n T) := by
    simp [Pool.P0089.Spec, Fintype.card_prod, Fintype.card_fin]
  have hlt := two_pow_Λ_ge hn hnT
  have hNE := NEp_le_nT hn hnT
  have hD : Dp n T ≤ n * T := by
    have h1 : Dp n T ≤ T / n := by
      unfold Dp; have := Nat.log_lt_self 2 (show T / n ≠ 0 by have := Tn_pos hn hnT; omega); omega
    have h2 : T / n ≤ T := Nat.div_le_self T n
    nlinarith
  have hn' : n ≤ n * T := by nlinarith
  have hL1 : Lp n T + 1 ≤ 2 ^ Λn n T := by
    have := Lp_le hn hnT; have := Nat.lt_two_pow_self (n := Λn n T); omega
  have hL2 : 2 ^ Lp n T ≤ 2 ^ Λn n T := Nat.pow_le_pow_right (by norm_num) (Lp_le hn hnT)
  have hb : NEp n T * Dp n T * n * ((Lp n T + 1) * 2 ^ Lp n T) ≤ 2 ^ (5 * Λn n T) := by
    have hp : n * T ≤ 2 ^ Λn n T := by omega
    have e : 2 ^ (5 * Λn n T) = 2 ^ Λn n T * 2 ^ Λn n T * 2 ^ Λn n T * (2 ^ Λn n T * 2 ^ Λn n T) := by ring
    rw [e]
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (hNE.trans hp) (hD.trans hp)) (hn'.trans hp))
      (Nat.mul_le_mul hL1 hL2)
  rw [hc]
  have := log_le_of_le_two_pow hb (Nat.one_le_iff_ne_zero.2 (by
    have := NEp_pos hn hnT; have := Dp_pos (n := n) (T := T); have := NeZero.pos n; positivity))
  push_cast at this ⊢
  linarith

theorem Qp_le : Qp n T ≤ 36 * (Λn n T : ℝ) ^ 3 := by
  have hΛ : (3 : ℝ) ≤ Λn n T := by exact_mod_cast Λn_ge hn hnT
  have hR : (Rp n T : ℝ) ≤ 2 * Λn n T := by
    have : (Rp n T : ℝ) = Lp n T + 1 := by rw [Rp_eq]; push_cast; ring
    have : (Lp n T : ℝ) ≤ Λn n T := by exact_mod_cast Lp_le hn hnT
    linarith
  have hL : 2 * (Lp n T : ℝ) + 1 ≤ 3 * Λn n T := by
    have : (Lp n T : ℝ) ≤ Λn n T := by exact_mod_cast Lp_le hn hnT
    linarith
  have hlc := logcard_le hn hnT
  have : Nonempty (Pool.P0089.Spec (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) (Lp n T)) :=
    ⟨(⟨0, Nat.mul_pos (Nat.mul_pos (NEp_pos hn hnT) (Dp_pos (n := n) (T := T))) (NeZero.pos n)⟩, 0,
      ⟨0, Nat.two_pow_pos _⟩)⟩
  have hc1 : (1 : ℝ) ≤ Fintype.card (Pool.P0089.Spec (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) (Lp n T)) := by
    exact_mod_cast Fintype.card_pos
  have hlc0 : 0 ≤ Real.log (Fintype.card (Pool.P0089.Spec (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) (Lp n T))) :=
    Real.log_nonneg hc1
  unfold Qp
  have h0 : (0 : ℝ) ≤ Rp n T := Nat.cast_nonneg _
  calc (Rp n T : ℝ) * (2 * Lp n T + 1) * (Real.log (Fintype.card (Pool.P0089.Spec (Pool.P0121.TM.Cp n (NEp n T)
        (Dp n T)) (Lp n T))) + 2) ≤ (2 * Λn n T) * (3 * Λn n T) * (5 * Λn n T + 2) := by gcongr
    _ ≤ 36 * (Λn n T : ℝ) ^ 3 := by
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (Λn n T : ℝ) - 2) (sq_nonneg (Λn n T : ℝ))]

theorem Sb_le : Sb n T ≤ 3500000 * (Λn n T : ℝ) ^ 10 := by
  obtain ⟨hD, hL, hR, hLv, hK, hQd, hkk, hM0, hs0, hS, hNs⟩ := params_poly hn hnT
  have hΛ : (3 : ℝ) ≤ Λn n T := by exact_mod_cast Λn_ge hn hnT
  unfold Sb; push_cast
  have hDLS : (Dp n T : ℝ) * Lvp n T * Sp n T ≤ 2 * (Λn n T : ℝ) ^ 2 * (1700000 * (Λn n T : ℝ) ^ 8) := by
    have := Nat.cast_nonneg (α := ℝ) (Sp n T)
    have := Nat.cast_nonneg (α := ℝ) (Dp n T); have := Nat.cast_nonneg (α := ℝ) (Lvp n T)
    have hDL : (Dp n T : ℝ) * Lvp n T ≤ 2 * (Λn n T : ℝ) ^ 2 := by nlinarith
    gcongr
  have p1 := pow_mono_Λ hn hnT (show 1 ≤ 10 by norm_num)
  have p0 := pow_mono_Λ hn hnT (show 0 ≤ 10 by norm_num)
  simp only [pow_one, pow_zero] at p1 p0
  nlinarith

theorem Gp_le : Gp n T ≤ 28100000 * n * (Λn n T : ℝ) ^ 12 := by
  obtain ⟨hD, hL, hR, hLv, hK, hQd, hkk, hM0, hs0, hS, hNs⟩ := params_poly hn hnT
  have hΛ : (3 : ℝ) ≤ Λn n T := by exact_mod_cast Λn_ge hn hnT
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hSb : Sb n T ≤ 3500000 * (Λn n T : ℝ) ^ 10 := by
    unfold Sb; push_cast
    have hDL : (Dp n T : ℝ) * Lvp n T ≤ 2 * (Λn n T : ℝ) ^ 2 := by
      have := Nat.cast_nonneg (α := ℝ) (Dp n T); have := Nat.cast_nonneg (α := ℝ) (Lvp n T); nlinarith
    have hDLS : (Dp n T : ℝ) * Lvp n T * Sp n T ≤ 2 * (Λn n T : ℝ) ^ 2 * (1700000 * (Λn n T : ℝ) ^ 8) := by
      have := Nat.cast_nonneg (α := ℝ) (Sp n T)
      have := Nat.cast_nonneg (α := ℝ) (Dp n T); have := Nat.cast_nonneg (α := ℝ) (Lvp n T)
      gcongr
    have p1 := pow_mono_Λ hn hnT (show 1 ≤ 10 by norm_num)
    have p0 := pow_mono_Λ hn hnT (show 0 ≤ 10 by norm_num)
    simp only [pow_one, pow_zero] at p1 p0
    nlinarith
  have hSb0 : 0 ≤ Sb n T := by unfold Sb; positivity
  unfold Gp
  have hDL : (Dp n T : ℝ) * Lvp n T ≤ 2 * (Λn n T : ℝ) ^ 2 := by
    have := Nat.cast_nonneg (α := ℝ) (Dp n T); have := Nat.cast_nonneg (α := ℝ) (Lvp n T); nlinarith
  have hDL0 : (0 : ℝ) ≤ Dp n T * Lvp n T := by positivity
  have e1 : (Dp n T : ℝ) * Lvp n T * Sb n T ≤ 2 * (Λn n T : ℝ) ^ 2 * (3500000 * (Λn n T : ℝ) ^ 10) := by gcongr
  have p12 := pow_mono_Λ hn hnT (show 0 ≤ 12 by norm_num)
  simp only [pow_zero] at p12
  nlinarith

theorem Λ_le_log : (Λn n T : ℝ) ≤ 3 * Real.log (n * T) := by
  have h4 : (4 : ℝ) ≤ n * T := by exact_mod_cast nT_ge hn hnT
  have hl4 : 1 ≤ Real.log (n * T : ℝ) := by
    have : Real.log 4 ≤ Real.log (n * T : ℝ) := Real.log_le_log (by norm_num) h4
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_gt_d9
    linarith
  have hb := Real.natLog_le_logb (n * T) 2
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  unfold Λn
  push_cast at hb ⊢
  rw [Real.logb] at hb
  have : Real.log (n * T : ℝ) / Real.log 2 ≤ 2 * Real.log (n * T : ℝ) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

set_option maxHeartbeats 1000000 in
open Classical in
/-- **The concrete threaded K-query machine's regret**: `≤ 10^17·√(nT)·(log nT)^16` for `2 ≤ n ≤ T`. -/
theorem regret_tmP_final (ℓ : Pool.P0001.LossSeq n) :
    (tmP n T).regret ℓ T ≤ 10 ^ 17 * Real.sqrt (n * T) * Real.log (n * T) ^ 16 := by
  have hE := regret_tmP_E n T hn hnT ℓ
  obtain ⟨hD, hL, hR, hLv, hK, hQd, hkk, hM0, hs0, hS, hNs⟩ := params_poly hn hnT
  have hΛ : (3 : ℝ) ≤ Λn n T := by exact_mod_cast Λn_ge hn hnT
  have hNE1 : (1 : ℝ) ≤ NEp n T := by exact_mod_cast NEp_pos hn hnT
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnT' : (n : ℝ) ≤ T := by exact_mod_cast hnT
  have hNE2 : (NEp n T : ℝ) ≤ 2 * T := by exact_mod_cast NEp_le hn hnT
  have hSpec : Nonempty (Pool.P0089.Spec (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) (Lp n T)) :=
    ⟨(⟨0, Nat.mul_pos (Nat.mul_pos (NEp_pos hn hnT) (Dp_pos (n := n) (T := T))) (NeZero.pos n)⟩, 0,
      ⟨0, Nat.two_pow_pos _⟩)⟩
  have hc : (1 : ℝ) ≤ Fintype.card (Pool.P0089.Spec (Pool.P0121.TM.Cp n (NEp n T) (Dp n T)) (Lp n T)) := by
    exact_mod_cast Fintype.card_pos
  have hlc := Real.log_nonneg hc
  have hR1 : (1 : ℝ) ≤ Rp n T := by exact_mod_cast Rp_ge n T
  have hQ0 : 0 < Qp n T := by unfold Qp; positivity
  have hQ2 : 2 ≤ Qp n T := by
    have h2 : (1 : ℝ) ≤ 2 * Lp n T + 1 := by have := Nat.cast_nonneg (α := ℝ) (Lp n T); linarith
    have h3 : (1 : ℝ) ≤ Rp n T * (2 * Lp n T + 1) := one_le_mul_of_one_le_of_one_le hR1 h2
    unfold Qp
    calc (2 : ℝ) = 1 * 2 := by ring
      _ ≤ Rp n T * (2 * Lp n T + 1) * (Real.log (Fintype.card (Pool.P0089.Spec (Pool.P0121.TM.Cp n (NEp n T)
          (Dp n T)) (Lp n T))) + 2) := by gcongr; linarith
  have hSb0 : 0 ≤ Sb n T := by unfold Sb; positivity
  have hG4 : 4 ≤ Gp n T := by
    unfold Gp
    have : (0 : ℝ) ≤ Dp n T * Lvp n T * Sb n T := by positivity
    nlinarith
  obtain ⟨hcore, hinv⟩ := eta_core hQ0 (by linarith) hNE1 (by nlinarith)
  have hη0 : 0 < ηp n T := by
    unfold ηp; exact lt_min one_pos (Real.sqrt_pos.2 (by positivity))
  have hRα : (Rp n T : ℝ) * αL n (NEp n T) (Dp n T) (Lp n T) (ηp n T) (εp n T) = Qp n T / ηp n T := by
    unfold αL εp Qp
    have : (NEp n T : ℝ) ≠ 0 := by positivity
    field_simp
  -- the sampling term
  have hX : ((Dp n T * Lvp n T * (s0p n T + Dp n T * Lvp n T * Sp n T + 1) : ℝ)) /
      (1 / (n : ℝ) * (1 - qp n T) ^ (Kp n T * (Dp n T * (2 * Lp n T + NEp n T / 2 ^ Lp n T + 1)))) ≤
      2 * ((n : ℝ) * (Dp n T * Lvp n T * Sb n T)) := by
    have hh := half_le_pow hn hnT
    have hpos : 0 < 1 / (n : ℝ) * (1 - qp n T) ^ (Kp n T * (Dp n T * (2 * Lp n T + NEp n T / 2 ^ Lp n T + 1))) := by
      have : (0 : ℝ) < n := by linarith
      positivity
    rw [div_le_iff₀ hpos]
    have e : (Dp n T * Lvp n T * (s0p n T + Dp n T * Lvp n T * Sp n T + 1) : ℝ) = Dp n T * Lvp n T * Sb n T := by
      unfold Sb; push_cast; ring
    rw [e]
    have h0 : (0 : ℝ) ≤ Dp n T * Lvp n T * Sb n T := by positivity
    set P := (1 - qp n T) ^ (Kp n T * (Dp n T * (2 * Lp n T + NEp n T / 2 ^ Lp n T + 1)))
    set A := (Dp n T : ℝ) * Lvp n T * Sb n T
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have e2 : 2 * ((n : ℝ) * A) * (1 / (n : ℝ) * P) = 2 * P * A := by field_simp
    rw [e2]
    nlinarith
  have hB := NE_div_B0_le hn hnT
  have hFb := Fbp_le hn hnT
  have hFb0 : 0 ≤ Fbp n T := by
    unfold Fbp
    have := Pool.P0042.delta_nonneg (N := Fintype.card (Pool.P0121.TM.Cp n (NEp n T) (Dp n T))) (p := qp n T)
      (L := Rp n T) (k := kkp n T) (M0 := (M0p n T : ℝ)) (qp_mem n T).2
    positivity
  -- the failure terms
  have hW0 : (0 : ℝ) ≤ (Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T := by positivity
  have hW32 : (Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T ≤ 32 * (Λn n T : ℝ) ^ 5 := by
    have hL1 : (Lp n T : ℝ) + 1 ≤ 2 * Λn n T := by linarith
    have hD0 : (0 : ℝ) ≤ Dp n T := Nat.cast_nonneg _
    calc (Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T ≤ (Λn n T : ℝ) ^ 2 * (2 * Λn n T) * (16 * (Λn n T : ℝ) ^ 2) := by
          gcongr
      _ = 32 * (Λn n T : ℝ) ^ 5 := by ring
  have hNEsq : (NEp n T : ℝ) / ((NEp n T : ℝ) + 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hD1 : (1 : ℝ) ≤ Dp n T := by exact_mod_cast Dp_pos (n := n) (T := T)
  have hZ : (Dp n T : ℝ) * NEp n T * Fbp n T ≤ 3 * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T) := by
    calc (Dp n T : ℝ) * NEp n T * Fbp n T ≤ Dp n T * NEp n T * (3 * Dp n T * (Lp n T + 1) * Kp n T /
          ((NEp n T : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hFb (by positivity)
      _ = 3 * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T) * ((NEp n T : ℝ) / ((NEp n T : ℝ) + 1) ^ 2) := by ring
      _ ≤ 3 * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T) * 1 := mul_le_mul_of_nonneg_left hNEsq (by positivity)
      _ = _ := mul_one _
  have hNEFb : (NEp n T : ℝ) * Fbp n T ≤ 3 * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T) := by
    have hDLK : 3 * (Dp n T : ℝ) * (Lp n T + 1) * Kp n T ≤ 3 * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T) := by
      have : (0 : ℝ) ≤ (Lp n T + 1) * Kp n T := by positivity
      nlinarith
    calc (NEp n T : ℝ) * Fbp n T ≤ NEp n T * (3 * Dp n T * (Lp n T + 1) * Kp n T / ((NEp n T : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_left hFb (by linarith)
      _ = 3 * Dp n T * (Lp n T + 1) * Kp n T * ((NEp n T : ℝ) / ((NEp n T : ℝ) + 1) ^ 2) := by ring
      _ ≤ 3 * Dp n T * (Lp n T + 1) * Kp n T * 1 := mul_le_mul_of_nonneg_left hNEsq (by positivity)
      _ ≤ _ := by linarith
  have hQηZ : 2 * (Qp n T / ηp n T) * ((Dp n T : ℝ) * NEp n T * Fbp n T) ≤
      12 * Qp n T * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T) := by
    have h1 : Qp n T / ηp n T ≤ Qp n T * (1 + Real.sqrt (NEp n T)) := by
      rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hinv hQ0.le
    have hsq : Real.sqrt (NEp n T) ≤ (NEp n T : ℝ) + 1 := by
      have := Real.sqrt_le_sqrt (show (NEp n T : ℝ) ≤ ((NEp n T : ℝ) + 1) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at this
    have h2 : (1 + Real.sqrt (NEp n T)) * ((Dp n T : ℝ) * NEp n T * Fbp n T) ≤
        6 * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T) := by
      calc (1 + Real.sqrt (NEp n T)) * ((Dp n T : ℝ) * NEp n T * Fbp n T)
          ≤ (1 + Real.sqrt (NEp n T)) * (Dp n T * NEp n T * (3 * Dp n T * (Lp n T + 1) * Kp n T /
            ((NEp n T : ℝ) + 1) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_left hFb (by positivity)
        _ = 3 * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T) *
            ((NEp n T + Real.sqrt (NEp n T) * NEp n T) / ((NEp n T : ℝ) + 1) ^ 2) := by ring
        _ ≤ 3 * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T) * 2 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_iff₀ (by positivity)]
            nlinarith [Real.sqrt_nonneg (NEp n T : ℝ)]
        _ = 6 * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T) := by ring
    have hZ0 : (0 : ℝ) ≤ (Dp n T : ℝ) * NEp n T * Fbp n T := by positivity
    calc 2 * (Qp n T / ηp n T) * ((Dp n T : ℝ) * NEp n T * Fbp n T)
        ≤ 2 * (Qp n T * (1 + Real.sqrt (NEp n T))) * ((Dp n T : ℝ) * NEp n T * Fbp n T) := by gcongr
      _ = 2 * Qp n T * ((1 + Real.sqrt (NEp n T)) * ((Dp n T : ℝ) * NEp n T * Fbp n T)) := by ring
      _ ≤ 2 * Qp n T * (6 * ((Dp n T : ℝ) ^ 2 * (Lp n T + 1) * Kp n T)) := by gcongr
      _ = _ := by ring
  rw [hRα] at hE
  have hY0 : (0 : ℝ) ≤ (n : ℝ) * (Dp n T * Lvp n T * Sb n T) := by positivity
  have hGdef : Gp n T = 2 * n + 4 * ((n : ℝ) * (Dp n T * Lvp n T * Sb n T)) := by unfold Gp; ring
  have h1 := arith1 (by positivity) hY0 hE hB hX hGdef hcore hZ hNEFb hQηZ
  have hY : (n : ℝ) * (Dp n T * Lvp n T * Sb n T) ≤ 7000000 * n * (Λn n T : ℝ) ^ 12 := by
    have hSb := Sb_le hn hnT
    have hDL : (Dp n T : ℝ) * Lvp n T ≤ 2 * (Λn n T : ℝ) ^ 2 := by
      calc (Dp n T : ℝ) * Lvp n T ≤ (Λn n T : ℝ) * (2 * Λn n T) :=
            mul_le_mul hD hLv (Nat.cast_nonneg _) (by positivity)
        _ = 2 * (Λn n T : ℝ) ^ 2 := by ring
    have hDL0 : (0 : ℝ) ≤ Dp n T * Lvp n T := by positivity
    have : (Dp n T : ℝ) * Lvp n T * Sb n T ≤ 2 * (Λn n T : ℝ) ^ 2 * (3500000 * (Λn n T : ℝ) ^ 10) := by gcongr
    have hn0 : (0 : ℝ) ≤ n := by linarith
    calc (n : ℝ) * (Dp n T * Lvp n T * Sb n T) ≤ n * (2 * (Λn n T : ℝ) ^ 2 * (3500000 * (Λn n T : ℝ) ^ 10)) := by
          gcongr
      _ = 7000000 * n * (Λn n T : ℝ) ^ 12 := by ring
  have h2 := arith2 hn2 hnT' hNE2 (by linarith) hΛ hQ0.le (by linarith) (Qp_le hn hnT) (Gp_le hn hnT) hY hW0 hW32
  have h3 : (Λn n T : ℝ) ^ 16 ≤ (3 * Real.log (n * T)) ^ 16 :=
    pow_le_pow_left₀ (by linarith) (Λ_le_log hn hnT) 16
  have hsq0 : 0 ≤ Real.sqrt ((n : ℝ) * T) := Real.sqrt_nonneg _
  calc (tmP n T).regret ℓ T ≤ 2100000000 * Real.sqrt (n * T) * (Λn n T : ℝ) ^ 16 := h1.trans h2
    _ ≤ 2100000000 * Real.sqrt (n * T) * (3 * Real.log (n * T)) ^ 16 := by gcongr
    _ = 2100000000 * 3 ^ 16 * Real.sqrt (n * T) * Real.log (n * T) ^ 16 := by ring
    _ ≤ 10 ^ 17 * Real.sqrt (n * T) * Real.log (n * T) ^ 16 := by
        have h4 : (4 : ℝ) ≤ n * T := by exact_mod_cast nT_ge hn hnT
        have hl : 0 ≤ Real.log ((n : ℝ) * T) := Real.log_nonneg (by linarith)
        have hX : 0 ≤ Real.sqrt (n * T) * Real.log (n * T) ^ 16 := by positivity
        have hc : (2100000000 : ℝ) * 3 ^ 16 ≤ 10 ^ 17 := by norm_num
        calc (2100000000 : ℝ) * 3 ^ 16 * Real.sqrt (n * T) * Real.log (n * T) ^ 16
            = (2100000000 * 3 ^ 16) * (Real.sqrt (n * T) * Real.log (n * T) ^ 16) := by ring
          _ ≤ 10 ^ 17 * (Real.sqrt (n * T) * Real.log (n * T) ^ 16) := mul_le_mul_of_nonneg_right hc hX
          _ = _ := by ring

theorem N1_le : NEp n T * Dp n T * n + 1 ≤ 2 ^ (3 * Λn n T) := by
  have hNE := NEp_le_nT hn hnT
  have hD : Dp n T ≤ n * T := by
    have h1 : Dp n T ≤ T / n := by
      unfold Dp; have := Nat.log_lt_self 2 (show T / n ≠ 0 by have := Tn_pos hn hnT; omega); omega
    have h2 : T / n ≤ T := Nat.div_le_self T n
    nlinarith
  have hn' : n ≤ n * T := by nlinarith
  have hlt := two_pow_Λ_ge hn hnT
  have : NEp n T * Dp n T * n ≤ (n * T) * (n * T) * (n * T) := Nat.mul_le_mul (Nat.mul_le_mul hNE hD) hn'
  have h2 : (n * T) * (n * T) * (n * T) + 1 ≤ 2 ^ Λn n T * 2 ^ Λn n T * 2 ^ Λn n T := by
    have hp : n * T < 2 ^ Λn n T := by omega
    have := Nat.mul_lt_mul'' (Nat.mul_lt_mul'' hp hp) hp
    omega
  have e : 2 ^ (3 * Λn n T) = 2 ^ Λn n T * 2 ^ Λn n T * 2 ^ Λn n T := by ring
  omega

theorem Zb_le : Pool.P0121.TP.Zb n (NEp n T) (Dp n T) (Lvp n T) (Lp n T) (Mp n T) ≤ 2 ^ (9 * Λn n T ^ 2) := by
  set Λ := Λn n T with hΛdef
  have hΛ3 : 3 ≤ Λ := Λn_ge hn hnT
  have ha := N1_le hn hnT
  have hb := NE1_le hn hnT
  have hc : Mp n T + 1 ≤ 2 ^ (2 * Λ) := by
    unfold Mp
    have : NEp n T * NEp n T + 1 ≤ (NEp n T + 1) * (NEp n T + 1) := by nlinarith
    have e : 2 ^ (2 * Λ) = 2 ^ Λ * 2 ^ Λ := by ring
    rw [e]; exact this.trans (Nat.mul_le_mul hb hb)
  have hL := Lp_le hn hnT
  have hd : 2 ^ Lp n T + 1 ≤ 2 ^ (Λ + 1) := by
    have : 2 ^ Lp n T ≤ 2 ^ Λ := Nat.pow_le_pow_right (by norm_num) hL
    have : 1 ≤ 2 ^ Λ := Nat.one_le_two_pow
    rw [pow_succ]; omega
  have he : (2 ^ Lp n T + 1) * (Mp n T + 1) ≤ 2 ^ (3 * Λ + 1) := by
    have e : 2 ^ (3 * Λ + 1) = 2 ^ (Λ + 1) * 2 ^ (2 * Λ) := by rw [← pow_add]; ring_nf
    rw [e]; exact Nat.mul_le_mul hd hc
  have hf : ((2 ^ Lp n T + 1) * (Mp n T + 1)) ^ (Lp n T + 1) ≤ 2 ^ ((3 * Λ + 1) * (Λ + 1)) := by
    calc ((2 ^ Lp n T + 1) * (Mp n T + 1)) ^ (Lp n T + 1) ≤ (2 ^ (3 * Λ + 1)) ^ (Lp n T + 1) :=
          Nat.pow_le_pow_left he _
      _ ≤ (2 ^ (3 * Λ + 1)) ^ (Λ + 1) := Nat.pow_le_pow_right (Nat.two_pow_pos _) (by omega)
      _ = 2 ^ ((3 * Λ + 1) * (Λ + 1)) := by rw [← pow_mul]
  have hg : 2 ^ (Dp n T * Lvp n T) ≤ 2 ^ (Λ * (Λ + 2)) := by
    apply Nat.pow_le_pow_right (by norm_num)
    have h1 := Dp_le hn hnT
    have h2 : Lvp n T ≤ Λ + 2 := by unfold Lvp; omega
    exact Nat.mul_le_mul h1 h2
  have hh : 2 ^ (Dp n T * Lvp n T) * ((2 ^ Lp n T + 1) * (Mp n T + 1)) ^ (Lp n T + 1) + 1 ≤
      2 ^ (Λ * (Λ + 2) + (3 * Λ + 1) * (Λ + 1) + 1) := by
    have hprod := Nat.mul_le_mul hg hf
    have hpos : 1 ≤ 2 ^ (Λ * (Λ + 2)) * 2 ^ ((3 * Λ + 1) * (Λ + 1)) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    have e : 2 ^ (Λ * (Λ + 2) + (3 * Λ + 1) * (Λ + 1) + 1) =
        2 * (2 ^ (Λ * (Λ + 2)) * 2 ^ ((3 * Λ + 1) * (Λ + 1))) := by
      rw [pow_succ, pow_add]; ring
    rw [e]; omega
  unfold Pool.P0121.TP.Zb
  have htot : (NEp n T * Dp n T * n + 1) * (2 ^ (Dp n T * Lvp n T) *
      ((2 ^ Lp n T + 1) * (Mp n T + 1)) ^ (Lp n T + 1) + 1) * (NEp n T + 1) * (Mp n T + 1) ≤
      2 ^ (3 * Λ) * 2 ^ (Λ * (Λ + 2) + (3 * Λ + 1) * (Λ + 1) + 1) * 2 ^ Λ * 2 ^ (2 * Λ) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul ha hh) hb) hc
  refine htot.trans ?_
  rw [← pow_add, ← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right (by norm_num)
  nlinarith

/-- **Memory of the concrete machine**: `≤ 4·10^27·log(nT)^26` bits (clock not counted; it is time-dependent). -/
theorem memBits_tmP_le : (tmP n T).memBits ≤ 4 * 10 ^ 27 * Real.log (n * T) ^ 26 := by
  obtain ⟨hD, hL, hR, hLv, hK, hQd, hkk, hM0, hs0, hS, hNs⟩ := params_poly hn hnT
  have hΛ : (3 : ℝ) ≤ Λn n T := by exact_mod_cast Λn_ge hn hnT
  have h := Pool.P0121.TP.memBits_tmach_le (n := n) (NE := NEp n T) (D := Dp n T) (Lv := Lvp n T) (L := Lp n T)
    (M := Mp n T) (Lt := Lp n T) (K := Kp n T) (R := Rp n T) (Btp n T) (Pool.P0085.levTh (Lp n T) (Btp n T)) 1
    (ηp n T) (εp n T) (Nsp n T) (ps_mem n) (qp_mem n T)
  have hZ : Real.logb 2 (Pool.P0121.TP.Zb n (NEp n T) (Dp n T) (Lvp n T) (Lp n T) (Mp n T)) ≤ 9 * (Λn n T : ℝ) ^ 2 := by
    have hz := Zb_le hn hnT
    have hz1 : 1 ≤ Pool.P0121.TP.Zb n (NEp n T) (Dp n T) (Lvp n T) (Lp n T) (Mp n T) := by
      unfold Pool.P0121.TP.Zb; exact Nat.one_le_iff_ne_zero.2 (by positivity)
    calc Real.logb 2 (Pool.P0121.TP.Zb n (NEp n T) (Dp n T) (Lvp n T) (Lp n T) (Mp n T))
        ≤ Real.logb 2 ((2 : ℝ) ^ (9 * Λn n T ^ 2)) := by
          apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hz1)
          exact_mod_cast hz
      _ = 9 * (Λn n T : ℝ) ^ 2 := by
          rw [Real.logb_pow]; simp
  have hNs1 : (1 : ℝ) ≤ Nsp n T := by
    have : 1 ≤ Nsp n T := by
      have h1 : 1 ≤ Dp n T * s0p n T :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := Dp_pos (n := n) (T := T); omega)
          (by unfold s0p; omega))
      unfold Nsp
      exact h1.trans (Nat.le_add_left _ _)
    exact_mod_cast this
  have hcnt : ((Nsp n T + Nsp n T * Nsp n T + 1 : ℕ) : ℝ) ≤ 3 * (7000000 * (Λn n T : ℝ) ^ 12) ^ 2 := by
    push_cast
    have h1 : (Nsp n T : ℝ) ^ 2 ≤ (7000000 * (Λn n T : ℝ) ^ 12) ^ 2 := pow_le_pow_left₀ (by linarith) hNs 2
    nlinarith
  have hZ0 : 0 ≤ Real.logb 2 (Pool.P0121.TP.Zb n (NEp n T) (Dp n T) (Lvp n T) (Lp n T) (Mp n T)) := by
    apply Real.logb_nonneg (by norm_num)
    have : 1 ≤ Pool.P0121.TP.Zb n (NEp n T) (Dp n T) (Lvp n T) (Lp n T) (Mp n T) := by
      unfold Pool.P0121.TP.Zb; exact Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have h3 : (Λn n T : ℝ) ^ 26 ≤ (3 * Real.log (n * T)) ^ 26 :=
    pow_le_pow_left₀ (by linarith) (Λ_le_log hn hnT) 26
  have h4 : (4 : ℝ) ≤ n * T := by exact_mod_cast nT_ge hn hnT
  have hl : 0 ≤ Real.log ((n : ℝ) * T) := Real.log_nonneg (by linarith)
  calc (tmP n T).memBits ≤ ((Nsp n T + Nsp n T * Nsp n T + 1 : ℕ) : ℝ) *
        Real.logb 2 (Pool.P0121.TP.Zb n (NEp n T) (Dp n T) (Lvp n T) (Lp n T) (Mp n T)) := h
    _ ≤ (3 * (7000000 * (Λn n T : ℝ) ^ 12) ^ 2) * (9 * (Λn n T : ℝ) ^ 2) :=
        mul_le_mul hcnt hZ hZ0 (by positivity)
    _ = 1323000000000000 * (Λn n T : ℝ) ^ 26 := by ring
    _ ≤ 1323000000000000 * (3 * Real.log (n * T)) ^ 26 := by gcongr
    _ = (1323000000000000 * 3 ^ 26) * Real.log (n * T) ^ 26 := by ring
    _ ≤ 4 * 10 ^ 27 * Real.log (n * T) ^ 26 := by
        apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

/-- **Queries per day**: `Nsp ≤ 4·10^12·log(nT)^12`. -/
theorem Nsp_le_log : (Nsp n T : ℝ) ≤ 4 * 10 ^ 12 * Real.log (n * T) ^ 12 := by
  obtain ⟨hD, hL, hR, hLv, hK, hQd, hkk, hM0, hs0, hS, hNs⟩ := params_poly hn hnT
  have hΛ : (3 : ℝ) ≤ Λn n T := by exact_mod_cast Λn_ge hn hnT
  have h3 : (Λn n T : ℝ) ^ 12 ≤ (3 * Real.log (n * T)) ^ 12 :=
    pow_le_pow_left₀ (by linarith) (Λ_le_log hn hnT) 12
  have h4 : (4 : ℝ) ≤ n * T := by exact_mod_cast nT_ge hn hnT
  have hl : 0 ≤ Real.log ((n : ℝ) * T) := Real.log_nonneg (by linarith)
  calc (Nsp n T : ℝ) ≤ 7000000 * (Λn n T : ℝ) ^ 12 := hNs
    _ ≤ 7000000 * (3 * Real.log (n * T)) ^ 12 := by gcongr
    _ = (7000000 * 3 ^ 12) * Real.log (n * T) ^ 12 := by ring
    _ ≤ 4 * 10 ^ 12 * Real.log (n * T) ^ 12 := by
        apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end StepB

end Concrete

end Pool.P0121.TPar
