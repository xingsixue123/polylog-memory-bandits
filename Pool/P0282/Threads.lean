import Pool.P0261.Params
import Pool.P0238.Count

/-!
# Thread-level arithmetic for P0261's family (P0262's F7, part 1)
-/

namespace Pool.P0282

open Finset Pool.P0261

/-- The rate floor of P0261's family: `1/max(Kc, Bm)` (P0261's `floor_le_xr`). -/
noncomputable def xf (n T Kc : ℕ) : ℝ := 1 / (max Kc (Bm n T) : ℕ)

/-- Multiples of `b` below `T`: at most `T/b + 1`. -/
theorem card_dvd_le (T b : ℕ) (hb : 0 < b) :
    (((range T).filter (fun t => b ∣ t)).card : ℝ) ≤ (T : ℝ) / b + 1 := by
  have h : ((range T).filter (fun t => b ∣ t)).card ≤ T / b + 1 := by
    calc ((range T).filter (fun t => b ∣ t)).card ≤ (range (T / b + 1)).card := by
          refine Finset.card_le_card_of_injOn (fun t => t / b) (fun t ht => ?_) (fun t ht t' ht' he => ?_)
          · simp only [coe_filter, Set.mem_setOf_eq, mem_range] at ht
            simp only [coe_range, Set.mem_Iio]
            exact Nat.lt_succ_of_le (Nat.div_le_div_right ht.1.le)
          · simp only [coe_filter, Set.mem_setOf_eq, mem_range] at ht ht'
            obtain ⟨a, rfl⟩ := ht.2; obtain ⟨a', rfl⟩ := ht'.2
            simp only [Nat.mul_div_cancel_left _ hb] at he; rw [he]
      _ = T / b + 1 := card_range _
  have h2 : ((T / b : ℕ) : ℝ) ≤ (T : ℝ) / b := Nat.cast_div_le
  calc (((range T).filter (fun t => b ∣ t)).card : ℝ) ≤ ((T / b + 1 : ℕ) : ℝ) := by exact_mod_cast h
    _ ≤ (T : ℝ) / b + 1 := by push_cast; linarith

/-- The finest epoch of P0261's family is one round. -/
theorem Bt_last (T : ℕ) : Bt T (Dn T - 1) = 1 := by
  unfold Bt Dn; simp

/-- A round whose canonical thread is `j` is a multiple of `Bt j`. -/
theorem dvd_of_canonT {T a j : ℕ} (h : Pool.P0065.canonT (Dn T) (Bt T) a = j) : Bt T j ∣ a := by
  have hs := Nat.find_spec (⟨Dn T - 1, Or.inr le_rfl⟩ : ∃ r, Bt T r ∣ a ∨ Dn T - 1 ≤ r)
  have hj : Pool.P0065.canonT (Dn T) (Bt T) a = Nat.find (⟨Dn T - 1, Or.inr le_rfl⟩ :
      ∃ r, Bt T r ∣ a ∨ Dn T - 1 ≤ r) := rfl
  rw [← hj, h] at hs
  rcases hs with hs | hs
  · exact hs
  · have hle := Pool.P0065.canonT_le (D := Dn T) (Bt := Bt T) a
    rw [h] at hle
    rw [show j = Dn T - 1 by omega, Bt_last]; exact one_dvd a

/-- **P0238's `C_j` for P0261's family**: `#{t < T' : canonT t = j} ≤ T'/Bt_j + 1`. -/
theorem card_canon_le (T T' j : ℕ) :
    ((((range T').filter (fun t => Pool.P0065.canonT (Dn T) (Bt T) t = j)).card : ℕ) : ℝ) ≤
      (T' : ℝ) / Bt T j + 1 := by
  refine le_trans ?_ (card_dvd_le T' (Bt T j) (Nat.two_pow_pos _))
  exact_mod_cast Finset.card_le_card (Finset.monotone_filter_right _ fun t _ h => dvd_of_canonT h)

/-- **P0238's `N_j` for P0261's grid copies**: rounds with an entry of thread `j` are multiples of `Bt_j`. -/
theorem card_entry_le (n T T' : ℕ) [NeZero n] (j : ℕ) :
    ((((range T').filter (fun t => ∃ y : CpG n T, Pool.P0121.TM.E n T (Dn T) y.1 = t ∧
        Pool.P0121.TM.thr0 n T (Dn T) y.1 = j)).card : ℕ) : ℝ) ≤ (T' : ℝ) / Bt T j + 1 := by
  refine le_trans ?_ (card_dvd_le T' (Bt T j) (Nat.two_pow_pos _))
  have hsub := Finset.card_le_card (Finset.monotone_filter_right (range T')
    (p := fun t => ∃ y : CpG n T, Pool.P0121.TM.E n T (Dn T) y.1 = t ∧ Pool.P0121.TM.thr0 n T (Dn T) y.1 = j)
    (q := fun t => Bt T j ∣ t) fun t _ h => by
      obtain ⟨y, hE, hthr⟩ := h
      have := y.2; rw [hthr, hE] at this; exact this)
  exact_mod_cast hsub

/-- **Above the floor, a thread costs `≤ 2n` per unit rate·epochs**: `xf < x_j ⇒ x_j·T/Bt_j ≤ 2n`. -/
theorem xr_mul_le {n T Kc : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ Kc) (j : ℕ) (hj : xf n T Kc < xr n T Kc j) :
    xr n T Kc j * ((T : ℝ) / Bt T j) ≤ 2 * n := by
  have hkx := kx_pos (n := n) (T := T) hK j
  have hk : kx n T Kc j < max Kc (Bm n T) := by
    unfold xf xr at hj
    have h0 : (0 : ℝ) < kx n T Kc j := by exact_mod_cast hkx
    have hm : (0 : ℝ) < ((max Kc (Bm n T) : ℕ) : ℝ) := by exact_mod_cast lt_of_lt_of_le hK (le_max_left _ _)
    rw [one_div_lt_one_div hm h0] at hj
    exact_mod_cast hj
  set a := T / (n * Bt T j)
  have ha : a ≤ kx n T Kc j := by
    unfold kx at hk ⊢
    by_contra hcon
    push Not at hcon
    have : min (Bm n T) a = Bm n T := by
      rcases le_total (Bm n T) a with h | h
      · exact min_eq_left h
      · exfalso; have := le_max_right Kc (min (Bm n T) a); rw [min_eq_right h] at this; omega
    rw [this] at hk; omega
  have hBt : (0 : ℝ) < Bt T j := by exact_mod_cast Nat.two_pow_pos _
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- T/(n·Bt) < a + 1 ≤ 2·kx
  have hlt : (T : ℝ) / (n * Bt T j) < a + 1 := by
    have := Nat.lt_div_mul_add (a := T) (b := n * Bt T j) (Nat.mul_pos (by omega) (Nat.two_pow_pos _))
    rw [div_lt_iff₀ (by positivity)]
    have h' : (T : ℝ) < (T / (n * Bt T j) : ℕ) * (n * Bt T j) + n * Bt T j := by exact_mod_cast this
    simp only [a]; push_cast at h' ⊢; linarith
  have hk1 : (1 : ℝ) ≤ kx n T Kc j := by exact_mod_cast hkx
  have ha' : (a : ℝ) ≤ kx n T Kc j := by exact_mod_cast ha
  have hT : (T : ℝ) / Bt T j ≤ 2 * n * kx n T Kc j := by
    have : (T : ℝ) / Bt T j = n * ((T : ℝ) / (n * Bt T j)) := by field_simp
    rw [this]; nlinarith
  unfold xr
  rw [one_div_mul_eq_div, div_le_iff₀ (by linarith)]
  linarith

/-- `T < 4n·Bm²` (P0261's `Bm = 2^(⌊log₂(T/n)⌋/2)`). -/
theorem T_lt_Bm_sq (n T : ℕ) (hn : 1 ≤ n) : T < 4 * n * (Bm n T * Bm n T) := by
  set m := Nat.log 2 (T / n)
  have h1 : T / n < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : 2 ^ (m + 1) ≤ 4 * (Bm n T * Bm n T) := by
    unfold Bm; rw [← pow_add, show 4 = 2 ^ 2 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : T < (T / n + 1) * n := by
    have := Nat.lt_div_mul_add (a := T) (b := n) (by omega); linarith
  nlinarith

/-- **The floor's total cost is `Õ(√(nT))`**: `xf·T ≤ 2√(nT)`. -/
theorem xf_mul_T_le {n T Kc : ℕ} (hn : 1 ≤ n) : xf n T Kc * T ≤ 2 * Real.sqrt (n * T) := by
  have hB : (0 : ℝ) < Bm n T := by exact_mod_cast Bm_pos n T
  have hxf : xf n T Kc ≤ 1 / (Bm n T : ℝ) := by
    unfold xf
    apply one_div_le_one_div_of_le hB; exact_mod_cast le_max_right _ _
  have hT : (T : ℝ) < 4 * n * ((Bm n T : ℝ) * Bm n T) := by exact_mod_cast T_lt_Bm_sq n T hn
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  -- T/Bm ≤ 2√(nT): (T/Bm)² = T·T/Bm² ≤ 4nT
  have hsq : ((T : ℝ) / Bm n T) ^ 2 ≤ (2 * Real.sqrt (n * T)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), div_le_iff₀ (by positivity)]
    nlinarith
  have hle : (T : ℝ) / Bm n T ≤ 2 * Real.sqrt (n * T) :=
    (pow_le_pow_iff_left₀ (div_nonneg hT0 hB.le) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hsq
  calc xf n T Kc * T ≤ 1 / (Bm n T : ℝ) * T := mul_le_mul_of_nonneg_right hxf hT0
    _ = (T : ℝ) / Bm n T := by ring
    _ ≤ _ := hle

/-- Per-thread core: above the floor, `2x(T/Bt + 1)(α + β√Bt) ≤ (4n+2)α + 5β√(nT/Kc)`. -/
theorem thread_term_le {n T Kc : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ Kc) (hT : 1 ≤ T) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (j : ℕ) (hj : xf n T Kc < xr n T Kc j) :
    2 * xr n T Kc j * ((T : ℝ) / Bt T j + 1) * (α + β * Real.sqrt (Bt T j)) ≤
      (4 * n + 2) * α + 5 * β * Real.sqrt (n * T / Kc) := by
  set x := xr n T Kc j
  set b : ℝ := (Bt T j : ℝ)
  have hx0 : 0 < x := xr_pos hK j
  have hx1 : x ≤ 1 / Kc := xr_le_cap hK j
  have hKr : (1 : ℝ) ≤ Kc := by exact_mod_cast hK
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hx1' : x ≤ 1 := hx1.trans (by rw [div_le_one (by linarith)]; exact hKr)
  have hb0 : 0 < b := by
    have : 0 < Bt T j := Nat.two_pow_pos _
    simp only [b]; exact_mod_cast this
  have hbT : b ≤ T := by
    have h1 := Bt_anti T (Nat.zero_le j); have h2 := Bt0_le T hT
    have : Bt T j ≤ T := h1.trans h2
    simp only [b]; exact_mod_cast this
  have hxT : x * ((T : ℝ) / b) ≤ 2 * n := xr_mul_le hn hK j hj
  set s := Real.sqrt (n * T / Kc)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = n * T / Kc := Real.sq_sqrt (by positivity)
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hsb0 : 0 < Real.sqrt b := Real.sqrt_pos.2 hb0
  -- (c) x·T/√b ≤ 1.5·s
  have hc : x * ((T : ℝ) / b) * Real.sqrt b ≤ 3 / 2 * s := by
    have e : x * ((T : ℝ) / b) * Real.sqrt b = x * T / Real.sqrt b := by
      field_simp; rw [hsb]
    rw [e]
    have hsq : (x * T / Real.sqrt b) ^ 2 ≤ (3 / 2 * s) ^ 2 := by
      have : (x * T / Real.sqrt b) ^ 2 = (x * ((T : ℝ) / b)) * (x * T) := by
        rw [div_pow, hsb]; field_simp
      rw [this, mul_pow, hs2]
      have hxTK : x * T ≤ T / Kc := by
        calc x * T ≤ 1 / Kc * T := mul_le_mul_of_nonneg_right hx1 (by linarith)
          _ = T / Kc := by ring
      have h0 : 0 ≤ x * (T : ℝ) := by positivity
      calc (x * ((T : ℝ) / b)) * (x * T) ≤ (2 * n) * (T / Kc) :=
            mul_le_mul hxT hxTK h0 (by positivity)
        _ ≤ (3 / 2) ^ 2 * (n * T / Kc) := by
            have : (0 : ℝ) ≤ n * T / Kc := by positivity
            rw [show (2 : ℝ) * n * (T / Kc) = 2 * (n * T / Kc) by ring]; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (2 : ℕ) ≠ 0)).1 hsq
  -- (d) x·√b ≤ s
  have hd : x * Real.sqrt b ≤ s := by
    have hsq : (x * Real.sqrt b) ^ 2 ≤ s ^ 2 := by
      rw [mul_pow, hsb, hs2]
      have hx2 : x ^ 2 ≤ 1 / Kc := by
        calc x ^ 2 = x * x := sq x
          _ ≤ (1 / Kc) * 1 := mul_le_mul hx1 hx1' hx0.le (by positivity)
          _ = 1 / Kc := by ring
      calc x ^ 2 * b ≤ (1 / Kc) * T := mul_le_mul hx2 hbT hb0.le (by positivity)
        _ ≤ n * T / Kc := by rw [div_mul_eq_mul_div, one_mul]; exact div_le_div_of_nonneg_right (by nlinarith) (by linarith)
    exact (pow_le_pow_iff_left₀ (by positivity) hs0 (by norm_num : (2 : ℕ) ≠ 0)).1 hsq
  have e : 2 * x * ((T : ℝ) / b + 1) * (α + β * Real.sqrt b) =
      2 * α * (x * ((T : ℝ) / b)) + 2 * α * x + 2 * β * (x * ((T : ℝ) / b) * Real.sqrt b) +
        2 * β * (x * Real.sqrt b) := by ring
  rw [e]
  have h1 : 2 * α * (x * ((T : ℝ) / b)) ≤ 2 * α * (2 * n) := mul_le_mul_of_nonneg_left hxT (by linarith)
  have h2 : 2 * α * x ≤ 2 * α * 1 := mul_le_mul_of_nonneg_left hx1' (by linarith)
  have h3 : 2 * β * (x * ((T : ℝ) / b) * Real.sqrt b) ≤ 2 * β * (3 / 2 * s) := mul_le_mul_of_nonneg_left hc (by linarith)
  have h4 : 2 * β * (x * Real.sqrt b) ≤ 2 * β * s := mul_le_mul_of_nonneg_left hd (by linarith)
  nlinarith

/-- **The above-floor part of P0255's `restD2_le` for P0261's family** (counts `C_j`, `N_j` on the horizon `T`, any
per-thread charges `Mb_j ≤ α + β√Bt_j` above the floor): at most `S'·D·((4n+2)α + 5β√(nT/Kc))`. -/
theorem thread_sum_le {n T Kc : ℕ} [NeZero n] (hn : 1 ≤ n) (hK : 1 ≤ Kc) (hT : 1 ≤ T) {S' α β : ℝ} (hS : 0 ≤ S')
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (Mb : Fin (Dn T) → ℝ)
    (hMb : ∀ j : Fin (Dn T), xf n T Kc < xr n T Kc j → Mb j ≤ α + β * Real.sqrt (Bt T j)) :
    ∑ j : Fin (Dn T), xr n T Kc j * (S' *
        ((((range T).filter (fun t => Pool.P0065.canonT (Dn T) (Bt T) t = j)).card : ℝ)
          + ((range T).filter (fun t => ∃ y : CpG n T, Pool.P0121.TM.E n T (Dn T) y.1 = t ∧
              Pool.P0121.TM.thr0 n T (Dn T) y.1 = j)).card)) *
        (if xf n T Kc < xr n T Kc j then Mb j else 0) ≤
      S' * Dn T * ((4 * n + 2) * α + 5 * β * Real.sqrt (n * T / Kc)) := by
  have hbound : 0 ≤ (4 * n + 2) * α + 5 * β * Real.sqrt (n * T / Kc) := by
    have := Real.sqrt_nonneg ((n : ℝ) * T / Kc); positivity
  calc _ ≤ ∑ _j : Fin (Dn T), S' * ((4 * n + 2) * α + 5 * β * Real.sqrt (n * T / Kc)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        split_ifs with hj
        · have hx0 : 0 < xr n T Kc j := xr_pos hK j
          have hC := card_canon_le T T j
          have hN := card_entry_le n T T j
          set C := (((range T).filter (fun t => Pool.P0065.canonT (Dn T) (Bt T) t = j)).card : ℝ)
          set N := (((range T).filter (fun t => ∃ y : CpG n T, Pool.P0121.TM.E n T (Dn T) y.1 = t ∧
              Pool.P0121.TM.thr0 n T (Dn T) y.1 = j)).card : ℝ)
          have hC0 : 0 ≤ C := Nat.cast_nonneg _
          have hN0 : 0 ≤ N := Nat.cast_nonneg _
          have hcore := thread_term_le hn hK hT hα hβ j hj
          have hMbj := hMb j hj
          have hsq := Real.sqrt_nonneg ((Bt T j : ℕ) : ℝ)
          have hpos : 0 ≤ xr n T Kc j * (S' * (C + N)) := by positivity
          calc xr n T Kc j * (S' * (C + N)) * Mb j ≤ xr n T Kc j * (S' * (C + N)) * (α + β * Real.sqrt (Bt T j)) :=
                mul_le_mul_of_nonneg_left hMbj hpos
            _ ≤ xr n T Kc j * (S' * (2 * ((T : ℝ) / Bt T j + 1))) * (α + β * Real.sqrt (Bt T j)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                apply mul_le_mul_of_nonneg_left _ hx0.le
                apply mul_le_mul_of_nonneg_left _ hS
                linarith
            _ = S' * (2 * xr n T Kc j * ((T : ℝ) / Bt T j + 1) * (α + β * Real.sqrt (Bt T j))) := by ring
            _ ≤ S' * ((4 * n + 2) * α + 5 * β * Real.sqrt (n * T / Kc)) := mul_le_mul_of_nonneg_left hcore hS
        · rw [mul_zero]; positivity
    _ = S' * Dn T * ((4 * n + 2) * α + 5 * β * Real.sqrt (n * T / Kc)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `x_j·Cp_j ≤ 2n + 1` for P0255's `Cp` (zero at the floor) on P0261's family. -/
theorem xr_Cp_le {n T Kc : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ Kc) (j : ℕ) :
    xr n T Kc j * ((if xr n T Kc j ≤ xf n T Kc then 0 else
      ((range T).filter (fun t => Pool.P0065.canonT (Dn T) (Bt T) t = j)).card : ℕ) : ℝ) ≤ 2 * n + 1 := by
  split_ifs with h
  · simp; positivity
  · push Not at h
    have hC := card_canon_le T T j
    have hx := xr_mul_le hn hK j h
    have hx1 : xr n T Kc j ≤ 1 := xr_le_one hK j
    have hx0 := (xr_pos (n := n) (T := T) hK j).le
    calc xr n T Kc j * (((range T).filter (fun t => Pool.P0065.canonT (Dn T) (Bt T) t = j)).card : ℝ)
        ≤ xr n T Kc j * ((T : ℝ) / Bt T j + 1) := mul_le_mul_of_nonneg_left hC hx0
      _ = xr n T Kc j * ((T : ℝ) / Bt T j) + xr n T Kc j := by ring
      _ ≤ 2 * n + 1 := by linarith

/-- **The per-copy-budget part of P0255's `restD2_le` for P0261's family**: with `Cp_j` zero at the floor,
`Σ_j x_j(S'ρ₀(2S'Cp_j+1) + S'V + S'c√T√(2S'Cp_j+1) + S'Cp_jρ₁ + S'V)` is at most
`D·(S'ρ₀(2S'(2n+1)+1) + 2S'V + S'c√T√(2S'(2n+1)+1) + S'(2n+1)ρ₁)`. -/
theorem rest_sum_le {n T Kc : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ Kc) {S' ρ₀ V c ρ₁ : ℝ} (hS : 0 ≤ S') (hρ₀ : 0 ≤ ρ₀)
    (hV : 0 ≤ V) (hc : 0 ≤ c) (hρ₁ : 0 ≤ ρ₁) :
    ∑ j : Fin (Dn T), xr n T Kc j * (S' * ρ₀ * (2 * (S' * ((if xr n T Kc j ≤ xf n T Kc then 0 else
        ((range T).filter (fun t => Pool.P0065.canonT (Dn T) (Bt T) t = j)).card : ℕ) : ℝ)) + 1)
      + S' * V
      + S' * c * (Real.sqrt T * Real.sqrt (2 * (S' * ((if xr n T Kc j ≤ xf n T Kc then 0 else
        ((range T).filter (fun t => Pool.P0065.canonT (Dn T) (Bt T) t = j)).card : ℕ) : ℝ)) + 1))
      + S' * ((if xr n T Kc j ≤ xf n T Kc then 0 else
        ((range T).filter (fun t => Pool.P0065.canonT (Dn T) (Bt T) t = j)).card : ℕ) : ℝ) * ρ₁
      + S' * V) ≤
    Dn T * (S' * ρ₀ * (2 * S' * (2 * n + 1) + 1) + 2 * (S' * V)
      + S' * c * (Real.sqrt T * Real.sqrt (2 * S' * (2 * n + 1) + 1)) + S' * (2 * n + 1) * ρ₁) := by
  calc _ ≤ ∑ _j : Fin (Dn T), (S' * ρ₀ * (2 * S' * (2 * n + 1) + 1) + 2 * (S' * V)
      + S' * c * (Real.sqrt T * Real.sqrt (2 * S' * (2 * n + 1) + 1)) + S' * (2 * n + 1) * ρ₁) := by
        refine Finset.sum_le_sum fun j _ => ?_
        set C : ℝ := ((if xr n T Kc j ≤ xf n T Kc then 0 else
          ((range T).filter (fun t => Pool.P0065.canonT (Dn T) (Bt T) t = j)).card : ℕ) : ℝ)
        set x := xr n T Kc j
        have hC0 : 0 ≤ C := Nat.cast_nonneg _
        have hxC : x * C ≤ 2 * n + 1 := xr_Cp_le hn hK j
        have hx0 : 0 ≤ x := (xr_pos hK j).le
        have hx1 : x ≤ 1 := xr_le_one hK j
        have hsq : x * Real.sqrt (2 * (S' * C) + 1) ≤ Real.sqrt (2 * S' * (2 * n + 1) + 1) := by
          rw [← Real.sqrt_sq hx0, ← Real.sqrt_mul (sq_nonneg x)]
          apply Real.sqrt_le_sqrt
          have : x ^ 2 * (2 * (S' * C) + 1) = 2 * S' * x * (x * C) + x ^ 2 := by ring
          rw [this]
          have h1 : 2 * S' * x * (x * C) ≤ 2 * S' * 1 * (2 * n + 1) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hx1 (by linarith)) hxC (by positivity) (by positivity)
          have h2 : x ^ 2 ≤ 1 := by nlinarith
          linarith
        have e : x * (S' * ρ₀ * (2 * (S' * C) + 1) + S' * V + S' * c * (Real.sqrt T * Real.sqrt (2 * (S' * C) + 1))
            + S' * C * ρ₁ + S' * V) = S' * ρ₀ * (2 * S' * (x * C) + x) + x * (2 * (S' * V)) +
              S' * c * Real.sqrt T * (x * Real.sqrt (2 * (S' * C) + 1)) + S' * (x * C) * ρ₁ := by ring
        rw [e]
        have hsT := Real.sqrt_nonneg (T : ℝ)
        have k1 : S' * ρ₀ * (2 * S' * (x * C) + x) ≤ S' * ρ₀ * (2 * S' * (2 * n + 1) + 1) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
        have k2 : x * (2 * (S' * V)) ≤ 1 * (2 * (S' * V)) := mul_le_mul_of_nonneg_right hx1 (by positivity)
        have k3 : S' * c * Real.sqrt T * (x * Real.sqrt (2 * (S' * C) + 1)) ≤
            S' * c * Real.sqrt T * Real.sqrt (2 * S' * (2 * n + 1) + 1) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        have k4 : S' * (x * C) * ρ₁ ≤ S' * (2 * n + 1) * ρ₁ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxC hS) hρ₁
        nlinarith
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Geometric epochs: `Σ_{j ≤ i ≤ j−1+d} Bt(i−1) + 2^(Dp−(j−1+d)+1) = 2^(Dp−j+2)` while `j − 1 + d ≤ Dp` (`1 ≤ j ≤ Dp`). -/
theorem sum_Bt_geom (T j : ℕ) (hj : 1 ≤ j) (hjD : j ≤ Dp T) : ∀ d, j - 1 + d ≤ Dp T →
    ∑ i ∈ Icc j (j - 1 + d), Bt T (i - 1) + 2 ^ (Dp T - (j - 1 + d) + 1) = 2 ^ (Dp T - j + 2)
  | 0, h => by
      have : Icc j (j - 1 + 0) = ∅ := Finset.Icc_eq_empty (by omega)
      rw [this, Finset.sum_empty, zero_add, show Dp T - (j - 1 + 0) + 1 = Dp T - j + 2 by omega]
  | d + 1, h => by
      have ih := sum_Bt_geom T j hj hjD d (by omega)
      have hs : Icc j (j - 1 + (d + 1)) = insert (j - 1 + (d + 1)) (Icc j (j - 1 + d)) := by
        ext i; simp only [mem_insert, mem_Icc]; omega
      rw [hs, Finset.sum_insert (by simp only [mem_Icc]; omega)]
      have e1 : Bt T (j - 1 + (d + 1) - 1) = 2 ^ (Dp T - (j - 1 + (d + 1)) + 1) := by
        unfold Bt; congr 1; omega
      have e2 : 2 ^ (Dp T - (j - 1 + d) + 1) = 2 * 2 ^ (Dp T - (j - 1 + (d + 1)) + 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [e1]; omega

/-- **P0238's thread lifetime for P0261's family**: `lenOf Θn T' (Bt T) j ≤ 4·Bt_j` for `1 ≤ j`, `Θn ≤ Dp T`
(thread `0` is handled by `lenOf_le'` below, at `T' = T`). -/
theorem lenOf_le (T T' Θn : ℕ) (hΘ : Θn ≤ Dp T) (j : ℕ) (hj : 1 ≤ j) :
    Pool.P0238.lenOf Θn T' (Bt T) j ≤ 4 * Bt T j := by
  unfold Pool.P0238.lenOf
  rw [ite_eq_left_of_eq_true _ _ (eq_true hj)]
  by_cases hjΘ : j ≤ Θn
  · have h := sum_Bt_geom T j hj (by omega) (Θn - (j - 1)) (by omega)
    rw [show j - 1 + (Θn - (j - 1)) = Θn by omega] at h
    have e : 2 ^ (Dp T - j + 2) = 4 * Bt T j := by
      unfold Bt; rw [pow_add]; ring
    rw [← e, ← h]; exact Nat.le_add_right _ _
  · have : Icc j Θn = ∅ := by ext i; simp; omega
    rw [this, Finset.sum_empty]; exact Nat.zero_le _

theorem lenOf_le' (T Θn : ℕ) (hT : 1 ≤ T) (hΘ : Θn ≤ Dp T) (j : ℕ) :
    Pool.P0238.lenOf Θn T (Bt T) j ≤ 4 * Bt T j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · unfold Pool.P0238.lenOf; rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    have := T_lt_two_Bt0 T; omega
  · exact lenOf_le T T Θn hΘ j hj

end Pool.P0282
