import Pool.P0065.Threads
import Pool.P0121.Machine
import Pool.P0207.Assemble
import Pool.P0121.Params
import Pool.P0079.Params
import Pool.P0063.GoodRunProb
import Pool.P0191.DZConc

/-!
# C11, part 1: the thread and rate family of the one-level step (static facts)
-/

namespace Pool.P0261

/-- Number of doublings: `2^Dp ≤ T < 2^(Dp+1)` (`T ≥ 1`); `2^Dp = T` when `T` is a power of two. -/
def Dp (T : ℕ) : ℕ := Nat.log 2 T

/-- Number of threads `D = Dp + 1`, thread `j` with epoch `Bt j = 2^(Dp − j)` (`Bt 0 = 2^Dp`, `= T` for a power of two,
so P0186's `Bt 0 ∣ T` holds; `Bt Dp = 1`). -/
def Dn (T : ℕ) : ℕ := Dp T + 1

def Bt (T : ℕ) (j : ℕ) : ℕ := 2 ^ (Dp T - j)

/-- The finest (b″)-check period and rate floor `1/Bm`, `Bm = 2^⌊log₂(T/n)/2⌋ ≈ √(T/n)`. -/
def Bm (n T : ℕ) : ℕ := 2 ^ (Nat.log 2 (T / n) / 2)

/-- Integer inverse rate of thread `j`: `kx j = max Kc (min Bm ⌊T/(n·Bt j)⌋)` (cap `1/Kc`, floor `1/Bm`). -/
def kx (n T Kc : ℕ) (j : ℕ) : ℕ := max Kc (min (Bm n T) (T / (n * Bt T j)))

noncomputable def xr (n T Kc : ℕ) (j : ℕ) : ℝ := 1 / (kx n T Kc j : ℝ)

theorem btHyp (T : ℕ) : Pool.P0065.BtHyp (Dn T) (Bt T) where
  hD := by unfold Dn; omega
  pos _ := Nat.two_pow_pos _
  dvd r hr := by
    unfold Bt; apply Nat.pow_dvd_pow; unfold Dn at hr; omega
  last := by unfold Bt Dn; simp

theorem T_lt_two_Bt0 (T : ℕ) : T < 2 * Bt T 0 := by
  unfold Bt Dp
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) T
  rw [pow_succ] at this; simpa [mul_comm] using this

theorem Bt0_le (T : ℕ) (hT : 1 ≤ T) : Bt T 0 ≤ T := by
  unfold Bt Dp; simpa using Nat.pow_log_le_self 2 (show T ≠ 0 by omega)

/-- For a power of two the coarsest epoch is the whole horizon (P0186's `Bt 0 ∣ T`). -/
theorem Bt0_pow (k : ℕ) : Bt (2 ^ k) 0 = 2 ^ k := by
  unfold Bt Dp; rw [Nat.log_pow (by norm_num)]; simp

theorem Bt0_dvd_pow (k : ℕ) : Bt (2 ^ k) 0 ∣ 2 ^ k := by rw [Bt0_pow]

theorem Bm_pos (n T : ℕ) : 0 < Bm n T := Nat.two_pow_pos _

theorem Bm_sq_le (n T : ℕ) : Bm n T * Bm n T ≤ T / n ∨ T / n = 0 := by
  rcases Nat.eq_zero_or_pos (T / n) with h | h
  · exact Or.inr h
  · left
    unfold Bm
    rw [← pow_add]
    calc 2 ^ (Nat.log 2 (T / n) / 2 + Nat.log 2 (T / n) / 2) ≤ 2 ^ Nat.log 2 (T / n) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ T / n := Nat.pow_log_le_self 2 (by omega)

theorem kx_pos {n T Kc : ℕ} (hK : 1 ≤ Kc) (j : ℕ) : 0 < kx n T Kc j := lt_of_lt_of_le hK (le_max_left _ _)

theorem kx_xr {n T Kc : ℕ} (hK : 1 ≤ Kc) (j : ℕ) : (kx n T Kc j : ℝ) * xr n T Kc j = 1 := by
  unfold xr; have : (0 : ℝ) < kx n T Kc j := by exact_mod_cast kx_pos hK j
  field_simp

theorem xr_pos {n T Kc : ℕ} (hK : 1 ≤ Kc) (j : ℕ) : 0 < xr n T Kc j := by
  unfold xr; have : (0 : ℝ) < kx n T Kc j := by exact_mod_cast kx_pos hK j
  positivity

theorem xr_le_one {n T Kc : ℕ} (hK : 1 ≤ Kc) (j : ℕ) : xr n T Kc j ≤ 1 := by
  unfold xr; have : (1 : ℝ) ≤ kx n T Kc j := by exact_mod_cast kx_pos hK j
  rw [div_le_one (by linarith)]; exact this

/-- Rate cap: `x_j ≤ 1/Kc`. -/
theorem xr_le_cap {n T Kc : ℕ} (hK : 1 ≤ Kc) (j : ℕ) : xr n T Kc j ≤ 1 / Kc := by
  unfold xr
  have h1 : (0 : ℝ) < Kc := by exact_mod_cast hK
  have h2 : (Kc : ℝ) ≤ kx n T Kc j := by exact_mod_cast le_max_left _ _
  exact one_div_le_one_div_of_le h1 h2

/-- Rate floor: `x_j ≥ 1/max Kc Bm`. -/
theorem floor_le_xr {n T Kc : ℕ} (hK : 1 ≤ Kc) (j : ℕ) : 1 / (max Kc (Bm n T) : ℕ) ≤ xr n T Kc j := by
  unfold xr
  have h1 : (0 : ℝ) < kx n T Kc j := by exact_mod_cast kx_pos hK j
  have h2 : kx n T Kc j ≤ max Kc (Bm n T) := max_le_max le_rfl (min_le_left _ _)
  exact one_div_le_one_div_of_le h1 (by exact_mod_cast h2)

theorem Bt_anti (T : ℕ) {i j : ℕ} (hij : i ≤ j) : Bt T j ≤ Bt T i := by
  unfold Bt; exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem kx_mono {n T Kc : ℕ} {i j : ℕ} (hij : i ≤ j) : kx n T Kc i ≤ kx n T Kc j := by
  unfold kx
  refine max_le_max le_rfl (min_le_min le_rfl ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact Nat.div_le_div_left (Nat.mul_le_mul_left _ (Bt_anti T hij)) (Nat.mul_pos h (Nat.two_pow_pos _))

/-- Rates are antitone in the thread index (coarser threads, lower index, larger rates). -/
theorem xr_anti {n T Kc : ℕ} (hK : 1 ≤ Kc) {i j : ℕ} (hij : i ≤ j) : xr n T Kc j ≤ xr n T Kc i := by
  unfold xr
  have h1 : (0 : ℝ) < kx n T Kc i := by exact_mod_cast kx_pos hK i
  exact one_div_le_one_div_of_le h1 (by exact_mod_cast kx_mono hij)

/-- P0222's occupancy hypothesis for `i ≥ 1`: `1/x_i ≤ max(Kc, T/(n·Bt i))`. -/
theorem occ_hyp {n T Kc : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ Kc) (i : ℕ) :
    1 / xr n T Kc i ≤ max (Kc : ℝ) ((T : ℝ) / ((n : ℝ) * Bt T i)) := by
  unfold xr
  rw [one_div_one_div]
  unfold kx
  rcases le_total Kc (min (Bm n T) (T / (n * Bt T i))) with h | h
  · rw [max_eq_right h]
    have h2 : ((min (Bm n T) (T / (n * Bt T i)) : ℕ) : ℝ) ≤ ((T / (n * Bt T i) : ℕ) : ℝ) := by
      exact_mod_cast min_le_right _ _
    have h3 : ((T / (n * Bt T i) : ℕ) : ℝ) ≤ (T : ℝ) / ((n : ℝ) * Bt T i) := by
      have := Nat.cast_div_le (α := ℝ) (m := T) (n := n * Bt T i)
      push_cast at this; exact this
    exact le_max_of_le_right (h2.trans h3)
  · rw [max_eq_left h]; exact le_max_left _ _

/-- P0222's occupancy hypothesis for thread `0`: `1/x_0 = Kc` since `T/(n·Bt 0) ≤ 1 ≤ Kc` (`T < 2·Bt 0`). -/
theorem occ_hyp0 {n T Kc : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ Kc) : 1 / xr n T Kc 0 ≤ Kc := by
  unfold xr kx
  rw [one_div_one_div]
  have h0 : T / (n * Bt T 0) ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by have := Nat.two_pow_pos (Dp T - 0); unfold Bt; positivity)]
    have := T_lt_two_Bt0 T
    have : Bt T 0 ≤ n * Bt T 0 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h1 : min (Bm n T) (T / (n * Bt T 0)) ≤ Kc := (min_le_right _ _).trans (h0.trans hK)
  rw [max_eq_left h1]

theorem occSort_mem {α : Type} [LinearOrder α] {s : ℕ} {V : Finset α} {y : Fin s} {x : α}
    (h : Pool.P0095.occSort s V y = some x) : x ∈ V := by
  unfold Pool.P0095.occSort at h
  split_ifs at h with hy
  cases h
  exact (Finset.mem_sort _).1 (List.getElem_mem _)

open Pool.P0121.TM in
/-- **Grid copies**: P0121's copies whose entry round is a multiple of their entry thread's epoch (P0065 samples only
these, and P0238's entry count `N_j` then counts only grid rounds). -/
abbrev CpG (n T : ℕ) [NeZero n] := {c : Cp n T (Dn T) // Bt T (thr0 n T (Dn T) c) ∣ E n T (Dn T) c}

open Pool.P0121.TM in
theorem CpG_E_mono (n T : ℕ) [NeZero n] : Monotone (fun c : CpG n T => E n T (Dn T) c.1) :=
  fun _ _ h => E_mono n T (Dn T) h

open Pool.P0194 Pool.P0121.TM in
/-- **The process parameters of the one-level step** (C11, part 1). Copies: P0121's `Cp n T D` (every arm, every
round, every thread; entry round `c / (D·n)`, thread `c / n mod D`, arm `c mod n`; only copies on their thread's grid
are ever sampled, P0065's `sample`). Threads `j < D = Dp + 1` with epochs `Bt j = 2^(Dp − j)`, rates
`x_j = 1/kx_j` (cap `1/Kc`, floor `1/Bm`), `Sl` slots each, entry-order layout, P0085's schedule `levTh Ld`, BASE weight
`wB`, exploitation weight `wE = 1 − wB − Σ_j Sl·x_j`, `cB = 1/wB`, (b″) checks every `Bm ≈ √(T/n)` rounds. The cover
parameters `θ, R, K, Lv, Ld`, the rule margins `Λ`, BASE `AB` and ALG (`N, σA, sA0, draw, updA`) are arguments. -/
noncomputable def parC (n T : ℕ) [NeZero n] (Kc Sl : ℕ) (wB θ : ℝ) (R K Lv Ld : ℕ)
    (Λ : CpG n T → ℕ → ℝ) (AB : Pool.P0050.CoinAlg n) (N : ℕ) (σA : Type) (sA0 : σA)
    (draw : σA → Finset (CpG n T) → Fin N → Option (CpG n T))
    (updA : σA → Finset (CpG n T) → Fin N → Option (CpG n T) → Bool → σA)
    (draw_mem : ∀ σ V d x, draw σ V d = some x → x ∈ V) : ParD n (CpG n T) where
  E c := Pool.P0121.TM.E n T (Dn T) c.1
  thr0 c := Pool.P0121.TM.thr0 n T (Dn T) c.1
  θ := θ
  R := R
  K := K
  D := Dn T
  Lv := Lv
  Bt := Bt T
  lev := Pool.P0085.levTh Ld (Bt T)
  sl _ := Sl
  xr j := xr n T Kc j
  lay := Pool.P0176.sortLay (fun _ => Sl)
  arm c := Pool.P0121.TM.arm n T (Dn T) c.1
  wB := wB
  wE := 1 - wB - ∑ j : Fin (Dn T), (Sl : ℝ) * xr n T Kc j
  cB := 1 / wB
  Bmin := Bm n T
  Λ := Λ
  AB := AB
  N := N
  σA := σA
  sA0 := sA0
  draw := draw
  updA := updA
  lay_mem _ _ _ _ h := occSort_mem h
  draw_mem := draw_mem

/-- The total slot weight is at most `D·Sl/Kc`. -/
theorem sum_slot_le {n T Kc Sl : ℕ} (hK : 1 ≤ Kc) :
    ∑ j : Fin (Dn T), (Sl : ℝ) * xr n T Kc j ≤ (Dn T : ℝ) * Sl / Kc := by
  calc ∑ j : Fin (Dn T), (Sl : ℝ) * xr n T Kc j ≤ ∑ _j : Fin (Dn T), (Sl : ℝ) * (1 / Kc) :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (xr_le_cap hK j) (Nat.cast_nonneg _)
    _ = (Dn T : ℝ) * Sl / Kc := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem sum_xr_le {n T Kc : ℕ} (hK : 1 ≤ Kc) : ∑ j : Fin (Dn T), xr n T Kc j ≤ (Dn T : ℝ) / Kc := by
  calc ∑ j : Fin (Dn T), xr n T Kc j ≤ ∑ _j : Fin (Dn T), (1 / (Kc : ℝ)) :=
        Finset.sum_le_sum fun j _ => xr_le_cap hK j
    _ = (Dn T : ℝ) / Kc := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

section Facts

open Pool.P0194 Pool.P0121.TM

variable {n T : ℕ} [NeZero n] {Kc Sl : ℕ} {wB θ : ℝ} {R K Lv Ld : ℕ}
  {Λ : CpG n T → ℕ → ℝ} {AB : Pool.P0050.CoinAlg n} {N : ℕ} {σA : Type} {sA0 : σA}
  {draw : σA → Finset (CpG n T) → Fin N → Option (CpG n T)}
  {updA : σA → Finset (CpG n T) → Fin N → Option (CpG n T) → Bool → σA}
  {draw_mem : ∀ σ V d x, draw σ V d = some x → x ∈ V}

/-- **The round kinds form a law** when `wB ≥ 0` and `wB + D·Sl/Kc ≤ 1`. -/
theorem parC_isLaw (hK : 1 ≤ Kc) (hwB : 0 ≤ wB) (hsum : wB + (Dn T : ℝ) * Sl / Kc ≤ 1) :
    (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).IsLaw := by
  have h := sum_slot_le (n := n) (T := T) (Sl := Sl) hK
  refine ⟨hwB, ?_, fun j => (xr_pos hK j).le, ?_⟩
  · show 0 ≤ 1 - wB - ∑ j : Fin (Dn T), (Sl : ℝ) * xr n T Kc j
    linarith
  · show wB + (1 - wB - ∑ j : Fin (Dn T), (Sl : ℝ) * xr n T Kc j) + ∑ j : Fin (Dn T), (Sl : ℝ) * xr n T Kc j = 1
    ring

theorem parC_cw (hwB : 0 < wB) :
    (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).cB *
      (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).wB = 1 := by
  show 1 / wB * wB = 1
  field_simp

/-- **P0234's informative regime `κ ≤ wE`**, `κ = (Σ_j sl_j)(Σ_j x_j)`, when `wB ≤ 1/2` and `4·D²·Sl ≤ Kc`. -/
theorem parC_kappa_le (hK : 1 ≤ Kc) (hwB : wB ≤ 1 / 2) (hKc : 4 * (Dn T) ^ 2 * Sl ≤ Kc) :
    (∑ j : Fin (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).D,
        ((parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).sl j : ℝ)) *
      ∑ j : Fin (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).D,
        (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).xr j ≤
      (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).wE := by
  show (∑ _j : Fin (Dn T), (Sl : ℝ)) * ∑ j : Fin (Dn T), xr n T Kc j ≤
    1 - wB - ∑ j : Fin (Dn T), (Sl : ℝ) * xr n T Kc j
  have h1 := sum_slot_le (n := n) (T := T) (Sl := Sl) hK
  have h2 := sum_xr_le (n := n) (T := T) hK
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hKr : (0 : ℝ) < Kc := by exact_mod_cast hK
  have hKc' : 4 * (Dn T : ℝ) ^ 2 * Sl ≤ Kc := by exact_mod_cast hKc
  have hD1 : (1 : ℝ) ≤ Dn T := by exact_mod_cast (show 1 ≤ Dn T by unfold Dn; omega)
  have hS : (0 : ℝ) ≤ Sl := Nat.cast_nonneg _
  have hDD : (Dn T : ℝ) * Sl ≤ (Dn T : ℝ) ^ 2 * Sl :=
    mul_le_mul_of_nonneg_right (by nlinarith) hS
  have e1 : (Dn T : ℝ) * Sl * ((Dn T : ℝ) / Kc) ≤ 1 / 4 := by
    have : (Dn T : ℝ) * Sl * ((Dn T : ℝ) / Kc) = (Dn T : ℝ) ^ 2 * Sl / Kc := by ring
    rw [this, div_le_iff₀ hKr]; linarith
  have e2 : (Dn T : ℝ) * Sl / Kc ≤ 1 / 4 := by
    rw [div_le_iff₀ hKr]; linarith
  have e3 : (Dn T : ℝ) * Sl * ∑ j : Fin (Dn T), xr n T Kc j ≤ (Dn T : ℝ) * Sl * ((Dn T : ℝ) / Kc) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

end Facts


/-! ## The cover / merge / sampling parameters -/

/-- `Λ = ⌊log₂(nT)⌋ + 1`. -/
def Lam (n T : ℕ) : ℕ := Nat.log 2 (n * T) + 1
/-- Merge-level schedule depth `Ld` (`T < 2^Ld`), sub-pool levels `Lv = Ld + 2`. -/
def Ld (T : ℕ) : ℕ := Nat.log 2 T + 1
def Lv (T : ℕ) : ℕ := Ld T + 2
/-- Filter-iteration levels `R` (`T ≤ 2^(R−1)`). -/
def Rc (T : ℕ) : ℕ := Nat.log 2 T + 2
def Kf (n T : ℕ) : ℕ := 4 * Rc T * (2 * (Lam n T + 1))
def Qd (n T : ℕ) : ℕ := 64 * Rc T * Kf n T * Dn T * (2 * Ld T + 1)
def kk (n T : ℕ) : ℕ := 32 * Lam n T ^ 2 * Qd n T
def M0 (n T : ℕ) : ℕ := 16 * Rc T + 4 * Rc T * kk n T + 288 * Rc T * Lam n T
def s0 (n T : ℕ) : ℕ := 4 * Lam n T + 2
def Sp (n T : ℕ) : ℕ := M0 n T + s0 n T
/-- Slots per thread (P0207's `hsl`). -/
def Sl (n T : ℕ) : ℕ :=
  Dn T * ((s0 n T + Dn T * Lv T * Sp n T) + (Lv T - 1) * Sp n T) + Dn T * s0 n T + 1
/-- Filter-coin probability. -/
noncomputable def qf (n T : ℕ) : ℝ := 1 / (Qd n T : ℝ)

theorem Rc_pos (T : ℕ) : 1 ≤ Rc T := by unfold Rc; omega

theorem T_le_R (T : ℕ) : T ≤ 2 ^ (Rc T - 1) := by
  unfold Rc
  rw [show Nat.log 2 T + 2 - 1 = Nat.log 2 T + 1 by omega]
  exact (Nat.lt_pow_succ_log_self (by norm_num) T).le

theorem hM0 (n T : ℕ) : 16 * (Rc T : ℝ) ≤ M0 n T := by
  unfold M0; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) (kk n T), Nat.cast_nonneg (α := ℝ) (Lam n T),
    Nat.cast_nonneg (α := ℝ) (Rc T)]

theorem hk (n T : ℕ) : 4 * (Rc T : ℝ) * kk n T ≤ M0 n T := by
  unfold M0; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) (Lam n T), Nat.cast_nonneg (α := ℝ) (Rc T)]

theorem hM0S (n T : ℕ) : (M0 n T : ℝ) ≤ Sp n T := by
  unfold Sp; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (s0 n T)]

theorem Qd_ge (n T : ℕ) : 64 * (Rc T : ℝ) ≤ Qd n T := by
  unfold Qd; push_cast
  have h1 : (1 : ℝ) ≤ Kf n T := by
    unfold Kf; have := Rc_pos T; have : 1 ≤ 4 * Rc T * (2 * (Lam n T + 1)) := by nlinarith
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ Dn T := by exact_mod_cast (show 1 ≤ Dn T by unfold Dn; omega)
  have h3 : (1 : ℝ) ≤ 2 * Ld T + 1 := by have : (0 : ℝ) ≤ Ld T := Nat.cast_nonneg _; linarith
  have hR : (0 : ℝ) ≤ Rc T := Nat.cast_nonneg _
  calc 64 * (Rc T : ℝ) = 64 * Rc T * 1 * 1 * 1 := by ring
    _ ≤ 64 * Rc T * Kf n T * Dn T * (2 * Ld T + 1) := by gcongr

/-- P0221/P0207's filter-rate condition `q (e − 1) ≤ 1/(32R)`. -/
theorem hp (n T : ℕ) : qf n T * (Real.exp 1 - 1) ≤ 1 / (32 * Rc T) := by
  unfold qf
  have hQd := Qd_ge n T
  have he : Real.exp 1 - 1 ≤ 2 := by have := Real.exp_one_lt_d9; linarith
  have hR : (1 : ℝ) ≤ Rc T := by exact_mod_cast Rc_pos T
  have hQpos : (0 : ℝ) < Qd n T := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hQpos (by positivity)]
  nlinarith [Real.exp_pos 1]

theorem qf_mem (n T : ℕ) : 0 ≤ qf n T ∧ qf n T ≤ 1 := by
  unfold qf
  have h : (1 : ℝ) ≤ Rc T := by exact_mod_cast Rc_pos T
  have h2 := Qd_ge n T
  have : (64 : ℝ) ≤ Qd n T := by linarith
  exact ⟨by positivity, by rw [div_le_one (by linarith)]; linarith⟩

theorem qf_lt_one (n T : ℕ) : qf n T < 1 := by
  unfold qf
  have h : (1 : ℝ) ≤ Rc T := by exact_mod_cast Rc_pos T
  have := Qd_ge n T
  rw [div_lt_one (by linarith)]; linarith

theorem four_pow_ge (x : ℕ) (hx : 2 ≤ x) : x * x + 2 * x + 2 ≤ 4 ^ x := by
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih => rw [pow_succ]; nlinarith

theorem Dn_le {n T : ℕ} (hn : 1 ≤ n) (hT : 1 ≤ T) : Dn T ≤ Lam n T + 1 := by
  unfold Dn Dp Lam
  have : Nat.log 2 T ≤ Nat.log 2 (n * T) := Nat.log_mono_right (Nat.le_mul_of_pos_left _ (by omega))
  omega

theorem Lv_le {n T : ℕ} (hn : 1 ≤ n) (hT : 1 ≤ T) : Lv T ≤ Lam n T + 3 := by
  unfold Lv Ld Lam
  have : Nat.log 2 T ≤ Nat.log 2 (n * T) := Nat.log_mono_right (Nat.le_mul_of_pos_left _ (by omega))
  omega


/-- P0221/P0207's pool-size contraction `(1 − 1/(4R))^K·(S' + (s0 + D·Lv·S')) ≤ S'`. -/
theorem hρS {n T : ℕ} (hn : 1 ≤ n) (hT : 1 ≤ T) :
    (1 - 1 / (4 * Rc T : ℝ)) ^ Kf n T * (Sp n T + (s0 n T + Dn T * Lv T * Sp n T)) ≤ Sp n T := by
  have hR1 := Rc_pos T
  have hR : (1 : ℝ) ≤ Rc T := by exact_mod_cast hR1
  have hx0 : 0 ≤ 1 - 1 / (4 * Rc T : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have hhalf := Pool.P0079.rho_half hR1
  have hpow : (1 - 1 / (4 * Rc T : ℝ)) ^ Kf n T ≤ (1 / 2) ^ (2 * (Lam n T + 1)) := by
    unfold Kf
    rw [pow_mul]
    apply pow_le_pow_left₀ (pow_nonneg hx0 _)
    push_cast; linarith
  have hDL : Dn T * Lv T + 2 ≤ 4 ^ (Lam n T + 1) := by
    have h1 := Dn_le hn hT
    have h2 := Lv_le hn hT
    have hΛ2 : 2 ≤ Lam n T + 1 := by unfold Lam; omega
    have h3 := four_pow_ge (Lam n T + 1) hΛ2
    have : Dn T * Lv T ≤ (Lam n T + 1) * (Lam n T + 3) := Nat.mul_le_mul h1 h2
    nlinarith
  have hs0S : (s0 n T : ℝ) ≤ Sp n T := by unfold Sp; push_cast; linarith [Nat.cast_nonneg (α := ℝ) (M0 n T)]
  have hS0 : (0 : ℝ) ≤ Sp n T := Nat.cast_nonneg _
  have hsum : (Sp n T : ℝ) + (s0 n T + Dn T * Lv T * Sp n T) ≤ (Dn T * Lv T + 2 : ℕ) * Sp n T := by
    push_cast; nlinarith
  have h4 : ((Dn T * Lv T + 2 : ℕ) : ℝ) ≤ 4 ^ (Lam n T + 1) := by exact_mod_cast hDL
  have h5 : ((1 : ℝ) / 2) ^ (2 * (Lam n T + 1)) * 4 ^ (Lam n T + 1) = 1 := by
    rw [pow_mul, ← mul_pow]; norm_num
  have hpos : (0 : ℝ) ≤ (1 - 1 / (4 * Rc T : ℝ)) ^ Kf n T := pow_nonneg hx0 _
  calc (1 - 1 / (4 * Rc T : ℝ)) ^ Kf n T * (Sp n T + (s0 n T + Dn T * Lv T * Sp n T))
      ≤ (1 - 1 / (4 * Rc T : ℝ)) ^ Kf n T * (((Dn T * Lv T + 2 : ℕ) : ℝ) * Sp n T) := by gcongr
    _ ≤ ((1 : ℝ) / 2) ^ (2 * (Lam n T + 1)) * (4 ^ (Lam n T + 1) * Sp n T) := by gcongr
    _ = Sp n T := by rw [← mul_assoc, h5, one_mul]

open Pool.P0121.TM in
/-- At most `n` grid copies enter at a given round on a given thread (exactly `n` on the grid, `0` off it). -/
theorem card_entG_le {n T : ℕ} [NeZero n] (hT : 1 ≤ T) {a r : ℕ} (ha : a < T) (hr : r < Dn T) :
    (Finset.univ.filter fun c : CpG n T => E n T (Dn T) c.1 = a ∧ thr0 n T (Dn T) c.1 = r).card ≤ n := by
  classical
  have h := Pool.P0121.TPar.card_entT (n := n) (NE := T) (D := Dn T) (by omega) (show 0 < Dn T by unfold Dn; omega)
    ha hr
  calc (Finset.univ.filter fun c : CpG n T => E n T (Dn T) c.1 = a ∧ thr0 n T (Dn T) c.1 = r).card
      ≤ (Finset.univ.filter fun c : Cp n T (Dn T) => E n T (Dn T) c = a ∧ thr0 n T (Dn T) c = r).card := by
        refine Finset.card_le_card_of_injOn (fun c => c.1) (fun c hc => ?_) (fun c _ d _ hcd => Subtype.ext hcd)
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc ⊢
        exact hc
    _ = n := h

open Pool.P0121.TM in
/-- P0221/P0207's sampling tail `hs` with `ps = 1/n` over the grid copies: at most `s0` of the `≤ n` copies of an
epoch start are sampled, except with probability `≤ exp(e − 1 − (s0 + 1))`. -/
theorem hs {n T : ℕ} [NeZero n] (hT : 1 ≤ T) : ∀ a r : ℕ, a < T → r < Dn T →
    ∑ F ∈ (Finset.univ.filter fun c : CpG n T => E n T (Dn T) c.1 = a ∧ thr0 n T (Dn T) c.1 = r).powerset,
      (1 / (n : ℝ)) ^ F.card * (1 - 1 / (n : ℝ)) ^ ((Finset.univ.filter fun c : CpG n T =>
        E n T (Dn T) c.1 = a ∧ thr0 n T (Dn T) c.1 = r).card - F.card) *
        (if s0 n T < F.card then 1 else 0) ≤ Real.exp (Real.exp 1 - 1 - (s0 n T + 1)) := by
  intro a r ha hr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast NeZero.one_le
  have hps : 0 ≤ 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ 1 :=
    ⟨by positivity, by rw [div_le_one (by linarith)]; exact hn1⟩
  refine (Pool.P0063.sample_tail_le hps _ (s0 n T)).trans (Real.exp_le_exp.2 ?_)
  have hc := card_entG_le (n := n) hT ha hr
  have hc' : ((Finset.univ.filter fun c : CpG n T => E n T (Dn T) c.1 = a ∧ thr0 n T (Dn T) c.1 = r).card : ℝ)
      ≤ n := by exact_mod_cast hc
  have he : 0 ≤ Real.exp 1 - 1 := by have := Real.add_one_le_exp 1; linarith
  have h1 : 1 / (n : ℝ) * ((Finset.univ.filter fun c : CpG n T =>
      E n T (Dn T) c.1 = a ∧ thr0 n T (Dn T) c.1 = r).card : ℝ) ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]; exact hc'
  nlinarith

/-- P0207's slot condition `hsl` holds with equality-plus-one for `Sl`. -/
theorem hsl (n T : ℕ) :
    (Dn T : ℝ) * ((s0 n T + Dn T * Lv T * Sp n T) + (Lv T - 1 : ℕ) * Sp n T) + Dn T * s0 n T + 1 ≤ Sl n T := by
  unfold Sl; push_cast; exact le_rfl

/-- P0201/P0186's schedule condition: `levTh Ld` stays below `Lv − 1`. -/
theorem hlev (T : ℕ) : ∀ r a, Pool.P0085.levTh (Ld T) (Bt T) r a + 1 < Lv T := by
  intro r a
  have := Pool.P0062.levPR_le (Ld T) ((a + 1) / Bt T r - 1)
  unfold Pool.P0085.levTh Lv; omega


/-! ## The rate cap and the cover margin -/

/-- Rate cap `1/Kc` with `Kc = 4·D²·Sl·Kq` (`Kq ≥ 1`, intended `⌈1/q⌉`), so that `κ ≤ wE` and `Σ_s x_s ≤ 1/(4·D·Kq)`. -/
def Kc (n T Kq : ℕ) : ℕ := 4 * Dn T ^ 2 * Sl n T * Kq

/-- Cover margin `θ = max Kc Bm = 1/xmin` (the inverse rate floor). -/
def θc (n T Kq : ℕ) : ℕ := max (Kc n T Kq) (Bm n T)

theorem Sl_pos (n T : ℕ) : 1 ≤ Sl n T := by unfold Sl; omega

theorem Kc_pos {n T Kq : ℕ} (hKq : 1 ≤ Kq) : 1 ≤ Kc n T Kq := by
  unfold Kc
  have h1 : 1 ≤ Dn T := by unfold Dn; omega
  have h2 := Sl_pos n T
  have : 1 ≤ Dn T ^ 2 := Nat.one_le_pow _ _ (by omega)
  have : 1 ≤ 4 * Dn T ^ 2 * Sl n T := by nlinarith
  nlinarith

theorem hKc4 {n T Kq : ℕ} (hKq : 1 ≤ Kq) : 4 * Dn T ^ 2 * Sl n T ≤ Kc n T Kq := by
  unfold Kc; exact Nat.le_mul_of_pos_right _ (by omega)

/-- The slot weight is at most `1/(4·Kq)`, hence (with `wB ≤ 1/2`) the round kinds form a law. -/
theorem slot_weight_le {n T Kq : ℕ} (hKq : 1 ≤ Kq) :
    (Dn T : ℝ) * Sl n T / Kc n T Kq ≤ 1 / (4 * Kq) := by
  have hK : (0 : ℝ) < Kc n T Kq := by exact_mod_cast Kc_pos (n := n) (T := T) hKq
  have hq : (0 : ℝ) < Kq := by exact_mod_cast hKq
  rw [div_le_div_iff₀ hK (by positivity)]
  unfold Kc; push_cast
  have h1 : (1 : ℝ) ≤ Dn T := by exact_mod_cast (show 1 ≤ Dn T by unfold Dn; omega)
  have h2 : (0 : ℝ) ≤ Sl n T := Nat.cast_nonneg _
  have h3 : (Dn T : ℝ) ≤ (Dn T : ℝ) ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_right h3 (mul_nonneg h2 hq.le)
  nlinarith

/-- P0221/P0207's horizon condition `(1/xmin)·T ≤ 2^(R−1)·θ` with `xmin = 1/θ`. -/
theorem hT_cover (n T Kq : ℕ) : (θc n T Kq : ℝ) * T ≤ 2 ^ (Rc T - 1) * (θc n T Kq : ℝ) := by
  have h := T_le_R T
  have h' : (T : ℝ) ≤ 2 ^ (Rc T - 1) := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ θc n T Kq := Nat.cast_nonneg _
  nlinarith

/-- Every rate is at least `1/θ` (the floor `xmin = 1/θ` of P0221/P0222). -/
theorem xmin_le {n T Kq : ℕ} (hKq : 1 ≤ Kq) (j : ℕ) :
    1 / (θc n T Kq : ℝ) ≤ xr n T (Kc n T Kq) j := floor_le_xr (Kc_pos hKq) j


open Pool.P0121.TM in
/-- **P0238's entry count on the grid copies**: the rounds `t < T` at which some grid copy enters thread `j` are
multiples of `Bt j`, so there are at most `T/Bt j + 1` of them (with P0121's full copy type every round counts). -/
theorem entry_count_le {n T : ℕ} [NeZero n] (j : ℕ) :
    ((Finset.range T).filter (fun t => ∃ y : CpG n T, E n T (Dn T) y.1 = t ∧ thr0 n T (Dn T) y.1 = j)).card ≤
      T / Bt T j + 1 := by
  classical
  have hsub : (Finset.range T).filter (fun t => ∃ y : CpG n T, E n T (Dn T) y.1 = t ∧ thr0 n T (Dn T) y.1 = j) ⊆
      (Finset.range (T / Bt T j + 1)).image (fun k => k * Bt T j) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    obtain ⟨htT, y, hyE, hyT⟩ := ht
    have hdvd := y.2
    rw [hyT, hyE] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    simp only [Finset.mem_image, Finset.mem_range]
    refine ⟨k, ?_, by rw [hk, mul_comm]⟩
    have hpos : 0 < Bt T j := Nat.two_pow_pos _
    have : k ≤ T / Bt T j := by
      rw [Nat.le_div_iff_mul_le hpos]; rw [hk] at htT; nlinarith
    omega
  calc _ ≤ ((Finset.range (T / Bt T j + 1)).image (fun k => k * Bt T j)).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (T / Bt T j + 1)).card := Finset.card_image_le
    _ = T / Bt T j + 1 := Finset.card_range _


/-! ## Static side conditions in the consumers' exact forms -/

section Exact

open Pool.P0194 Pool.P0121.TM

variable {n T : ℕ} [NeZero n] {Kc Sl : ℕ} {wB θ : ℝ} {R K Lv Ld : ℕ}
  {Λ : CpG n T → ℕ → ℝ} {AB : Pool.P0050.CoinAlg n} {N : ℕ} {σA : Type} {sA0 : σA}
  {draw : σA → Finset (CpG n T) → Fin N → Option (CpG n T)}
  {updA : σA → Finset (CpG n T) → Fin N → Option (CpG n T) → Bool → σA}
  {draw_mem : ∀ σ V d x, draw σ V d = some x → x ∈ V}

/-- **P0194's `OneSlot` for `parC`**: the entry-order layout puts a member in at most one slot of its thread. -/
theorem parC_oneSlot : (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).OneSlot := by
  intro j V k k' x hk hk'
  change Pool.P0095.occSort Sl V k = some x at hk
  change Pool.P0095.occSort Sl V k' = some x at hk'
  unfold Pool.P0095.occSort at hk hk'
  split_ifs at hk hk' with h1 h2
  cases hk
  have hnd : (V.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  exact Fin.ext ((hnd.getElem_inj_iff).1 (Option.some.inj hk').symm)

/-- **P0222's `hx0` for `parC`** (in P0222's form, with P0191's `xrN`): `1/xrN 0 ≤ Kc`. -/
theorem parC_hx0 (hK : 1 ≤ Kc) :
    1 / Pool.P0191.xrN (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).xr 0 ≤ (Kc : ℝ) := by
  unfold Pool.P0191.xrN
  rw [dif_pos (show 0 < (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).D by
    show 0 < Dn T; unfold Dn; omega)]
  exact occ_hyp0 (NeZero.one_le) hK

/-- **P0222's `hx` for `parC`** (in P0222's form): `1/xrN i ≤ max(Kc, T/(n·Bt i))` for every `i ≥ 1` (for `i ≥ D`,
`xrN i = 1 ≤ Kc`). -/
theorem parC_hx (hK : 1 ≤ Kc) (i : ℕ) (_hi : 1 ≤ i) :
    1 / Pool.P0191.xrN (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).xr i ≤
      max (Kc : ℝ) ((T : ℝ) / ((n : ℝ) * (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).Bt i)) := by
  unfold Pool.P0191.xrN
  split_ifs with h
  · exact occ_hyp (NeZero.one_le) hK i
  · have : (1 : ℝ) ≤ Kc := by exact_mod_cast hK
    rw [div_one]; exact le_max_of_le_left this

/-- **P0222's `hρ` for `parC`** with `ρ = 2`: `Bt (i−1) ≤ 2·Bt i` for `i ≥ 1`. -/
theorem parC_hρ (i : ℕ) (_hi : 1 ≤ i) :
    ((parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).Bt (i - 1) : ℝ) ≤
      2 * (parC n T Kc Sl wB θ R K Lv Ld Λ AB N σA sA0 draw updA draw_mem).Bt i := by
  show ((Bt T (i - 1) : ℕ) : ℝ) ≤ 2 * ((Bt T i : ℕ) : ℝ)
  have : Bt T (i - 1) ≤ 2 * Bt T i := by
    unfold Bt
    rcases Nat.lt_or_ge (Dp T) i with h | h
    · rw [show Dp T - i = 0 by omega]
      have : Dp T - (i - 1) = 0 := by omega
      rw [this]; norm_num
    · rw [show Dp T - (i - 1) = (Dp T - i) + 1 by omega, pow_succ]; omega
  exact_mod_cast this

/-- **P0221's `hT` in its exact form for `parC`** with the intended cover margin `θ = θc` and `R = Rc`, at
`xmin = 1/θc`: `(1/xmin)·T ≤ 2^(R−1)·θ`. -/
theorem parC_hT {Kq : ℕ} {Λ' : CpG n T → ℕ → ℝ}
    {draw_mem' : ∀ σ V d x, draw σ V d = some x → x ∈ V} :
    1 / (1 / (θc n T Kq : ℝ)) * T ≤
      2 ^ ((parC n T (Pool.P0261.Kc n T Kq) (Pool.P0261.Sl n T) wB (θc n T Kq) (Rc T) K Lv Ld Λ' AB N σA sA0 draw updA draw_mem').R - 1) *
        (parC n T (Pool.P0261.Kc n T Kq) (Pool.P0261.Sl n T) wB (θc n T Kq) (Rc T) K Lv Ld Λ' AB N σA sA0 draw updA draw_mem').θ := by
  rw [one_div_one_div]
  exact hT_cover n T Kq

/-- **The static bundle for the intended cap** `Kc = Kc n T Kq`, `Sl = Sl n T`, for every `Kq ≥ 1` and
`0 < wB ≤ 1/2`: the round kinds form a law, `cB·wB = 1`, and `κ ≤ wE`. -/
theorem parC_static {Kq : ℕ} (hKq : 1 ≤ Kq) (hwB0 : 0 < wB) (hwB : wB ≤ 1 / 2)
    {Λ' : CpG n T → ℕ → ℝ} {draw_mem' : ∀ σ V d x, draw σ V d = some x → x ∈ V} :
    (parC n T (Pool.P0261.Kc n T Kq) (Pool.P0261.Sl n T) wB θ R K Lv Ld Λ' AB N σA sA0 draw updA draw_mem').IsLaw ∧
    (parC n T (Pool.P0261.Kc n T Kq) (Pool.P0261.Sl n T) wB θ R K Lv Ld Λ' AB N σA sA0 draw updA draw_mem').cB *
      (parC n T (Pool.P0261.Kc n T Kq) (Pool.P0261.Sl n T) wB θ R K Lv Ld Λ' AB N σA sA0 draw updA draw_mem').wB = 1 ∧
    (∑ j : Fin (parC n T (Pool.P0261.Kc n T Kq) (Pool.P0261.Sl n T) wB θ R K Lv Ld Λ' AB N σA sA0 draw updA draw_mem').D,
        ((parC n T (Pool.P0261.Kc n T Kq) (Pool.P0261.Sl n T) wB θ R K Lv Ld Λ' AB N σA sA0 draw updA draw_mem').sl j : ℝ)) *
      ∑ j : Fin (parC n T (Pool.P0261.Kc n T Kq) (Pool.P0261.Sl n T) wB θ R K Lv Ld Λ' AB N σA sA0 draw updA draw_mem').D,
        (parC n T (Pool.P0261.Kc n T Kq) (Pool.P0261.Sl n T) wB θ R K Lv Ld Λ' AB N σA sA0 draw updA draw_mem').xr j ≤
      (parC n T (Pool.P0261.Kc n T Kq) (Pool.P0261.Sl n T) wB θ R K Lv Ld Λ' AB N σA sA0 draw updA draw_mem').wE := by
  have hsw := slot_weight_le (n := n) (T := T) hKq
  have hq : (1 : ℝ) ≤ Kq := by exact_mod_cast hKq
  have h4 : 1 / (4 * (Kq : ℝ)) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  refine ⟨parC_isLaw (Kc_pos hKq) hwB0.le (by linarith), parC_cw hwB0,
    parC_kappa_le (Kc_pos hKq) hwB (hKc4 hKq)⟩

end Exact

/-! ## A limitation of this family -/

open Pool.P0121.TM in
/-- **The finest thread is dense.** `BtHyp.last` forces the finest epoch `Bt Dp = 1` ROUND (P0194's units are rounds),
and a grid copy enters the finest thread at EVERY round `t < T`; when `Kc ≤ Bm` and `1 ≤ T/n` its rate is exactly
`1/Bm`, so P0166 §1.1's per-item check cost `x·Bmin` is `1`. Hence the merged per-item accounting (P0166 §1.1, P0222's
range term `2L/xmin`) is at least linear in `T` over this thread. -/
theorem finest_thread_dense {n T Kc : ℕ} [NeZero n] :
    Bt T (Dp T) = 1 ∧
    ((Finset.range T).filter (fun t => ∃ y : CpG n T, E n T (Dn T) y.1 = t ∧ thr0 n T (Dn T) y.1 = Dp T)).card = T ∧
    (1 ≤ Kc → Kc ≤ Bm n T → 1 ≤ T / n → xr n T Kc (Dp T) * (Bm n T : ℝ) = 1) := by
  have hn : 0 < n := NeZero.pos n
  refine ⟨by unfold Bt; simp, ?_, ?_⟩
  · have hsub : (Finset.range T).filter
        (fun t => ∃ y : CpG n T, E n T (Dn T) y.1 = t ∧ thr0 n T (Dn T) y.1 = Dp T) = Finset.range T := by
      apply Finset.filter_true_of_mem
      intro t ht
      rw [Finset.mem_range] at ht
      have hD : Dn T = Dp T + 1 := rfl
      have hlt : t * (Dn T * n) + Dp T * n < T * Dn T * n := by
        have h1 : t * (Dn T * n) + Dp T * n < (t + 1) * (Dn T * n) := by rw [hD]; nlinarith
        have h2 : (t + 1) * (Dn T * n) ≤ T * (Dn T * n) := Nat.mul_le_mul_right _ ht
        nlinarith
      let c : Cp n T (Dn T) := ⟨t * (Dn T * n) + Dp T * n, hlt⟩
      have hE : E n T (Dn T) c = t := by
        show (t * (Dn T * n) + Dp T * n) / (Dn T * n) = t
        have hpos : 0 < Dn T * n := Nat.mul_pos (by rw [hD]; omega) hn
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by rw [hD]; nlinarith)]
        simp
      have hth : thr0 n T (Dn T) c = Dp T := by
        show (t * (Dn T * n) + Dp T * n) / n % Dn T = Dp T
        rw [show t * (Dn T * n) + Dp T * n = (t * Dn T + Dp T) * n by ring, Nat.mul_div_cancel _ hn,
          Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by rw [hD]; omega)]
      have hgrid : Bt T (thr0 n T (Dn T) c) ∣ E n T (Dn T) c := by
        rw [hth]; unfold Bt; simp
      exact ⟨⟨c, hgrid⟩, hE, hth⟩
    rw [hsub, Finset.card_range]
  · intro hK hKB hTn
    have hBt : Bt T (Dp T) = 1 := by unfold Bt; simp
    have hBm : Bm n T ≤ T / n := by
      rcases Bm_sq_le n T with h | h
      · have := Bm_pos n T; nlinarith
      · omega
    have hk : kx n T Kc (Dp T) = Bm n T := by
      unfold kx; rw [hBt, mul_one, min_eq_left hBm, max_eq_right hKB]
    unfold xr; rw [hk]
    have : (0 : ℝ) < Bm n T := by exact_mod_cast Bm_pos n T
    field_simp

end Pool.P0261
