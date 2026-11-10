import Pool.P0245.Glue
import Pool.P0275.Margins
import Pool.P0282.Threads

/-!
# The concrete one-level family (P0262's F7: the parameter choice)

For `n, T, q` and a coin algorithm `A` (BASE): process horizon `Tp = 2^⌈log₂T⌉`, P0261's threads and rates with
`Kq = ⌈1/q⌉`, BASE weight `wB = q/2`, P0275's margins `margP`, and P0236's finite twin ALG (P0245's `mTwin`) with
learning rates `η = γ = 1/s`, resolutions `N = G = ⌈s⌉`, `s = √(q·Tp/n)`.
-/

namespace Pool.P0284

open Finset Pool.P0261 Pool.P0194

variable (n T : ℕ) [NeZero n] (q : ℝ)

/-- The process horizon: the least power of two `≥ T`. -/
def Tp : ℕ := 2 ^ Nat.clog 2 T

theorem le_Tp : T ≤ Tp T := Nat.le_pow_clog (by norm_num) T

theorem Tp_le (hT : 1 ≤ T) : Tp T ≤ 2 * T := by
  unfold Tp
  rcases Nat.lt_or_ge T 2 with h | h
  · interval_cases T; simp
  · have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) h
    have hc : 0 < Nat.clog 2 T := Nat.clog_pos (by norm_num) h
    calc 2 ^ Nat.clog 2 T = 2 * 2 ^ (Nat.clog 2 T - 1) := by rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * T := by rw [← Nat.pred_eq_sub_one]; omega

theorem Tp_pos : 1 ≤ Tp T := Nat.one_le_two_pow

/-- `Bt 0 = Tp` (P0261's coarsest epoch is the whole process horizon). -/
theorem Bt0_Tp : Bt (Tp T) 0 = Tp T := Bt0_pow _

/-- `Kq = ⌈1/q⌉`. -/
noncomputable def Kq : ℕ := ⌈1 / q⌉₊

/-- The rate cap `Kc = 4·D²·Sl·Kq` of P0261 at the process horizon. -/
noncomputable def KcF : ℕ := Kc n (Tp T) (Kq q)

/-- The ALG scale `s = √(q·Tp/n)` (`≥ 1` when `n/T ≤ q`). -/
noncomputable def sA : ℝ := Real.sqrt (q * Tp T / n)

/-- ALG's resolutions `N = G = ⌈s⌉ ≥ 1`. -/
noncomputable def NA : ℕ := max 1 ⌈sA n T q⌉₊

scoped instance : NeZero (NA n T q) := ⟨by unfold NA; omega⟩

/-- ALG's learner levels `L` with `Tp ≤ 2^L`. -/
def LA : ℕ := Nat.clog 2 T + 1

/-- ALG's learning rate, IX parameter and tail parameter `η = γ = κ = 1/s`. -/
noncomputable def ηA : ℝ := 1 / max 1 (sA n T q)

/-- The rounding `ε = η/Tp`. -/
noncomputable def εA : ℝ := ηA n T q / Tp T

/-- The confidence level `Lx = 3·log(Tp+1) + log(4|ι| + 4)` (P0276's choice, with `|ι|` the grid copies). -/
noncomputable def Lx : ℝ := 3 * Real.log (Tp T + 1) + Real.log (4 * Fintype.card (CpG n (Tp T)) + 4)

/-- The process parameters before margins and ALG (P0261's `parC`, a placeholder ALG on `Unit`). -/
noncomputable def P0 (A : Pool.P0050.CoinAlg n) : ParD n (CpG n (Tp T)) :=
  parC n (Tp T) (KcF n T q) (Sl n (Tp T)) (q / 2) (θc n (Tp T) (Kq q)) (Rc (Tp T)) (Kf n (Tp T)) (Lv (Tp T))
    (Ld (Tp T)) (fun _ _ => 0) A 1 Unit () (fun _ _ _ => none) (fun _ _ _ _ _ => ()) (fun _ _ _ _ h => by cases h)

/-- The exploitation weight `wE = 1 − wB − Σ_j Sl·x_j`. -/
noncomputable def wEA (A : Pool.P0050.CoinAlg n) : ℝ := (P0 n T q A).wE

/-- **The process parameters with P0275's margins** (record margins of the self-rounding ALG's walk, P0250/P0268). -/
noncomputable def P1 (A : Pool.P0050.CoinAlg n) : ParD n (CpG n (Tp T)) :=
  Pool.P0275.margP (P0 n T q A) (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A)
    (Pool.P0225.ρStar (ηA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (εA n T q))
    (Tp T) (εA n T q) (Lx n T) (Lx n T) (Lx n T) (Lx n T) (ηA n T q) (Pool.P0282.xf n (Tp T) (KcF n T q))
    (KcF n T q) 2 n (Tp T) (Dp (Tp T)) (Dp (Tp T))

theorem Kq_pos (hq : 0 < q) : 1 ≤ Kq q := by
  unfold Kq; exact Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [Nat.ceil_eq_zero] at h; have : 0 < 1 / q := by positivity
    linarith)

theorem KcF_pos (hq : 0 < q) : 1 ≤ KcF n T q := Kc_pos (Kq_pos q hq)

/-- **The round kinds form a law** for `0 < q ≤ 1/32`. -/
theorem P0_isLaw (A : Pool.P0050.CoinAlg n) (hq : 0 < q) (hq1 : q ≤ 1 / 32) : (P0 n T q A).IsLaw := by
  have hK := KcF_pos n T q hq
  refine parC_isLaw hK (by linarith) ?_
  have hKc := hKc4 (n := n) (T := Tp T) (Kq_pos q hq)
  have hKr : (0 : ℝ) < KcF n T q := by exact_mod_cast hK
  have hD1 : (1 : ℝ) ≤ Dn (Tp T) := by exact_mod_cast (show 1 ≤ Dn (Tp T) by unfold Dn; omega)
  have hKc' : 4 * (Dn (Tp T) : ℝ) ^ 2 * Sl n (Tp T) ≤ KcF n T q := by unfold KcF; exact_mod_cast hKc
  have hS : (0 : ℝ) ≤ Sl n (Tp T) := Nat.cast_nonneg _
  have : (Dn (Tp T) : ℝ) * Sl n (Tp T) / KcF n T q ≤ 1 / 4 := by
    rw [div_le_iff₀ hKr]; nlinarith
  show q / 2 + (Dn (Tp T) : ℝ) * Sl n (Tp T) / (KcF n T q : ℕ) ≤ 1
  linarith

theorem sum_wK_ennreal {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (hL : P.IsLaw) :
    ∑ κ, ENNReal.ofReal (wK P κ) = 1 := by
  have h0 : ∀ κ : Kd P, 0 ≤ wK P κ := by
    obtain ⟨h1, h2, h3, _⟩ := hL
    intro κ; rcases κ with _ | _ | s
    · exact h1
    · exact h2
    · exact h3 _
  rw [← ENNReal.ofReal_sum_of_nonneg (fun κ _ => h0 κ), sum_wK, hL.2.2.2]; simp

open Classical in
/-- The round-kind law: `wK` when the weights form a law (always, for `0 < q ≤ 1/32`). -/
noncomputable def κlaw {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) : PMF (Kd P) :=
  if h : P.IsLaw then PMF.ofFintype (fun κ => ENNReal.ofReal (wK P κ)) (sum_wK_ennreal n P h) else PMF.pure none

/-- The machine parameters before the ALG swap (P0201's `MPar` on `P1`). NB: the field `q` is P0261's FILTER rate
`qf`, not the family's BASE rate `q` (`wB = q/2`). -/
noncomputable def M0 (A : Pool.P0050.CoinAlg n) : Pool.P0201.MPar n (CpG n (Tp T)) where
  P := P1 n T q A
  kx j := kx n (Tp T) (KcF n T q) j
  κl := κlaw n (P1 n T q A)
  Lf := Ld (Tp T)
  Ns := Dn (Tp T) * Sl n (Tp T)
  TT := Tp T * (KcF n T q + Bm n (Tp T) + 1)
  TB := Tp T
  Tc := Tp T
  ps := 1 / n
  q := qf n (Tp T)
  hps := ⟨by positivity, by rw [div_le_one (by exact_mod_cast NeZero.pos n)]; exact_mod_cast NeZero.one_le⟩
  hq := qf_mem n (Tp T)
  fA := (inferInstance : Fintype Unit)
  nN := ⟨one_ne_zero⟩

/-- **The one-level machine parameters** (P0245's `mTwin`: P0236's finite twin ALG on `M0`); `(famM …).q` is the
filter rate `qf` (see `M0`). -/
noncomputable def famM (A : Pool.P0050.CoinAlg n) : Pool.P0201.MPar n (CpG n (Tp T)) :=
  Pool.P0245.mTwin (M0 n T q A) (ηA n T q) (εA n T q) (LA T) (NA n T q) (NA n T q) (ηA n T q) (wEA n T q A) (Tp T)

/-- **The one-level machine**: P0201's coin algorithm on `famM` (decidable equality from the order, as in P0245). -/
noncomputable def machF (A : Pool.P0050.CoinAlg n) : Pool.P0050.CoinAlg n :=
  @Pool.P0201.mach n (CpG n (Tp T)) _ (fun a b => LinearOrder.toDecidableEq a b) _ (famM n T q A)

theorem machF_hom (A : Pool.P0050.CoinAlg n) : Pool.P0173.CoinHom (machF n T q A) :=
  @Pool.P0201.mach_hom n (CpG n (Tp T)) _ (fun a b => LinearOrder.toDecidableEq a b) _ (famM n T q A)

/-- `s ≥ 1` when `n/T ≤ q` (`1 ≤ n ≤ T`). -/
theorem one_le_sA (hT : 1 ≤ T) (hq : (n : ℝ) / T ≤ q) : 1 ≤ sA n T q := by
  unfold sA; rw [Real.one_le_sqrt]
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h1 : (n : ℝ) ≤ q * T := by rw [div_le_iff₀ hT'] at hq; exact hq
  have h2 : (T : ℝ) ≤ Tp T := by exact_mod_cast le_Tp T
  rw [le_div_iff₀ hn]; nlinarith [hq, (div_nonneg hn.le hT'.le).trans hq]

/-- So `N = G = ⌈s⌉` when `n/T ≤ q`. -/
theorem NA_eq (hT : 1 ≤ T) (hq : (n : ℝ) / T ≤ q) : NA n T q = ⌈sA n T q⌉₊ := by
  have h := one_le_sA n T q hT hq
  unfold NA; exact max_eq_right (Nat.one_le_ceil_iff.2 (by linarith))

section Facts

variable (A : Pool.P0050.CoinAlg n)

theorem famM_isLaw (hq : 0 < q) (hq1 : q ≤ 1 / 32) : (famM n T q A).P.IsLaw := P0_isLaw n T q A hq hq1

theorem famM_wB : (famM n T q A).P.wB = q / 2 := rfl

/-- Slot capacity, true BY CONSTRUCTION (`Ns = D·Sl`); not a guarantee that the pool members fit (P0217's `ovf`). -/
theorem famM_cap : ∑ j, (famM n T q A).P.sl j ≤ (famM n T q A).Ns := by
  show ∑ _j : Fin (Dn (Tp T)), Sl n (Tp T) ≤ Dn (Tp T) * Sl n (Tp T)
  simp

theorem one_div_Kq_le (hq : 0 < q) : 1 / (Kq q : ℝ) ≤ q := by
  have h1 : 1 / q ≤ Kq q := Nat.le_ceil _
  have hK : (0 : ℝ) < Kq q := by exact_mod_cast Kq_pos q hq
  rw [div_le_iff₀ hK]; rw [div_le_iff₀ hq] at h1; linarith

/-- `Σ_j Sl·x_j ≤ q/4` and `(Σ_j Sl)(Σ_j x_j) ≤ q/4` (so BASE's coefficient `wB + X₁ + κ ≤ q = 2·wB`). -/
theorem slot_weights_le (hq : 0 < q) :
    ∑ j : Fin (Dn (Tp T)), (Sl n (Tp T) : ℝ) * xr n (Tp T) (KcF n T q) j ≤ q / 4 ∧
    (∑ _j : Fin (Dn (Tp T)), (Sl n (Tp T) : ℝ)) * ∑ j : Fin (Dn (Tp T)), xr n (Tp T) (KcF n T q) j ≤ q / 4 := by
  have hK := KcF_pos n T q hq
  have h1 := sum_slot_le (n := n) (T := Tp T) (Sl := Sl n (Tp T)) hK
  have h2 := sum_xr_le (n := n) (T := Tp T) hK
  have hKq := one_div_Kq_le q hq
  have hKq0 : (0 : ℝ) < Kq q := by exact_mod_cast Kq_pos q hq
  have hD1 : (1 : ℝ) ≤ Dn (Tp T) := by exact_mod_cast (show 1 ≤ Dn (Tp T) by unfold Dn; omega)
  have hS1 : (1 : ℝ) ≤ Sl n (Tp T) := by exact_mod_cast Sl_pos n (Tp T)
  have hKe : (KcF n T q : ℝ) = 4 * (Dn (Tp T) : ℝ) ^ 2 * Sl n (Tp T) * Kq q := by
    unfold KcF Kc; push_cast; ring
  have hKr : (0 : ℝ) < KcF n T q := by exact_mod_cast hK
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  constructor
  · refine h1.trans ?_
    rw [hKe]
    have : (Dn (Tp T) : ℝ) * Sl n (Tp T) / (4 * (Dn (Tp T) : ℝ) ^ 2 * Sl n (Tp T) * Kq q) =
        1 / (4 * Dn (Tp T) * Kq q) := by field_simp
    rw [this]
    calc 1 / (4 * (Dn (Tp T) : ℝ) * Kq q) ≤ 1 / (4 * Kq q) := by
          apply one_div_le_one_div_of_le (by positivity); nlinarith
      _ = (1 / Kq q) / 4 := by field_simp
      _ ≤ q / 4 := by linarith
  · calc (Dn (Tp T) : ℝ) * Sl n (Tp T) * ∑ j : Fin (Dn (Tp T)), xr n (Tp T) (KcF n T q) j
        ≤ (Dn (Tp T) : ℝ) * Sl n (Tp T) * ((Dn (Tp T) : ℝ) / KcF n T q) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 1 / (4 * Kq q) := by rw [hKe]; field_simp
      _ = (1 / Kq q) / 4 := by field_simp
      _ ≤ q / 4 := by linarith

/-- **P0201's intended regime** for the process horizon `Tp`. -/
theorem famM_intended (hq : 0 < q) (hq1 : q ≤ 1 / 32) : (famM n T q A).Intended (Tp T) where
  kx_pos j := kx_pos (KcF_pos n T q hq) j
  kx_xr j := kx_xr (KcF_pos n T q hq) j
  κl_eq κ := by
    have hL := P0_isLaw n T q A hq hq1
    have e2 : wK (famM n T q A).P κ = wK (P1 n T q A) κ := by
      rcases κ with _ | _ | s <;> rfl
    have e3 : (famM n T q A).κl κ = κlaw n (P1 n T q A) κ := rfl
    have hL1 : (P1 n T q A).IsLaw := by
      unfold P1 Pool.P0275.margP Pool.P0275.withMarg Pool.P0275.withΛ
      exact hL
    rw [e2, e3]
    unfold κlaw
    rw [dif_pos hL1]
    show (ENNReal.ofReal (wK (P1 n T q A) κ)).toReal = _
    rw [ENNReal.toReal_ofReal]
    obtain ⟨h1, h2, h3, _⟩ := hL
    rcases κ with _ | _ | s
    · exact h1
    · exact h2
    · exact h3 _
  hD := by show 0 < Dn (Tp T); unfold Dn; omega
  hLv := by show 0 < Lv (Tp T); unfold Lv; omega
  hlev := hlev (Tp T)
  hLf r a := by
    show Pool.P0085.levTh (Ld (Tp T)) (Bt (Tp T)) r a ≤ Ld (Tp T)
    have := Pool.P0062.levPR_le (Ld (Tp T)) ((a + 1) / Bt (Tp T) r - 1)
    unfold Pool.P0085.levTh; omega
  hTc := le_rfl
  hTB := le_rfl
  hTT j := by
    show Tp T * (kx n (Tp T) (KcF n T q) j + 1) ≤ Tp T * (KcF n T q + Bm n (Tp T) + 1)
    apply Nat.mul_le_mul_left
    unfold kx
    have := min_le_left (Bm n (Tp T)) (Tp T / (n * Bt (Tp T) j))
    omega

end Facts

end Pool.P0284
