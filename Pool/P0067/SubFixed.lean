import Pool.P0055.Subsample
import Pool.P0018.Exp3

/-!
# Subsampling fixed-horizon learners (P0055 without an anytime hypothesis)

P0055's `Sub A γ` plays `A`'s policy every round and updates `A` with probability `γ`; its regret is at most
`(1/γ)·E[R(Binomial(T, γ))]` when `A`'s regret on every sequence of length `m ≤ T` is at most `R m`.
Its square-root corollary needs an *anytime* bound `R m ≤ c√m`. Here we only need a bound `ρ` for horizons `m ≤ H`
(a learner tuned for horizon `H`), plus the trivial bound `regret ≤ m`, and an exponential tail of the binomial.

* `sum_wt_two_pow`: `E[2^{cnt}] = (1 + γ)^T` for the number of learning rounds `cnt ~ Binomial(T, γ)`.
* `sum_wt_cnt_gt`: `P(cnt > H) ≤ (1 + γ)^T / 2^(H+1)`; `tail_le_exp`: this is `≤ e^{−x}` when `2(γT + x) ≤ H + 1`.
* `regret_Sub_le_fixed`: `regret (Sub A γ) ≤ (1/γ)·(ρ + T (1+γ)^T / 2^(H+1))`.
* `exp3M_regret_prefix`, `exp3M_regret_prefix_sqrt`: P0018's EXP3 tuned for horizon `T` has, on every prefix of
  `m ≤ T` rounds, regret at most `(1/η) log n + m δc ≤ (3/2)√((1+log n)(2n+1)(T+1)) + 1/2`.
* `regret_Sub_exp3M`: subsampled EXP3, regret `≤ (1/γ)((3/2)√((1+log n)(2n+1)(H+1)) + 1/2 + T e^{−x})`; with
  `H + 1 ≈ 2(γT + x)` this is `O(√((1+log n) n T/γ) + (1 + T e^{−x})/γ)`.
-/

open Finset
open scoped ENNReal

namespace Pool.P0067

open Pool.P0001 Pool.P0055

variable {n : ℕ}

/-- `cnt f t` reads only `f` below `t`. -/
theorem cnt_congr {f g : ℕ → Bool} : ∀ t, (∀ k, k < t → f k = g k) → cnt f t = cnt g t
  | 0, _ => rfl
  | t + 1, h => by
    simp only [cnt]
    rw [cnt_congr t (fun k hk => h k (by omega)), h t (by omega)]

/-- Exponential moment of the number of flags: `E[2^{cnt}] = (1 + γ)^T`. -/
theorem sum_wt_two_pow (γ : ℝ) : ∀ T, ∑ F : Fin T → Bool, wt γ F * (2 : ℝ) ^ cnt (ext F) T = (1 + γ) ^ T
  | 0 => by simp [wt, cnt]
  | T + 1 => by
    rw [sum_fin_succ_bool]
    have hc : ∀ (F : Fin T → Bool) (b : Bool),
        cnt (ext (Fin.snoc F b : Fin (T + 1) → Bool)) (T + 1) = cnt (ext F) T + (if b then 1 else 0) := by
      intro F b
      simp only [cnt]
      rw [ext_snoc_last, cnt_congr T (fun k hk => ext_snoc_lt F b k hk)]
      cases b <;> simp
    simp only [wt_snoc, hc]
    rw [pow_succ, ← sum_wt_two_pow γ T, Finset.sum_mul]
    refine Finset.sum_congr rfl fun F _ => ?_
    simp only [if_true, Bool.false_eq_true, if_false, add_zero, pow_add, pow_one]
    ring

/-- Tail of the number of flags: `P(cnt > H) ≤ (1 + γ)^T / 2^(H+1)`. -/
theorem sum_wt_cnt_gt {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (T H : ℕ) :
    ∑ F : Fin T → Bool, wt γ F * (if H < cnt (ext F) T then (1 : ℝ) else 0) ≤ (1 + γ) ^ T / 2 ^ (H + 1) := by
  rw [← sum_wt_two_pow γ T, Finset.sum_div]
  refine Finset.sum_le_sum fun F _ => ?_
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (wt_nonneg h0 h1 F)
  split_ifs with h
  · rw [le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_right₀ (by norm_num) h
  · positivity

/-- **Subsampling a fixed-horizon learner.** If `A` (homogeneous) has regret at most `ρ` on every loss sequence of
every length `m ≤ min T H`, then `Sub A γ` has regret at most `(1/γ)·(ρ + T (1+γ)^T / 2^(H+1))` over `T` rounds. -/
theorem regret_Sub_le_fixed [NeZero n] (A : Machine n) (hA : A.IsHomogeneous) {γ : ℝ} (hγ : 0 < γ) (h1 : γ ≤ 1)
    (ℓ : LossSeq n) (T H : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hR : ∀ (ℓ' : LossSeq n) m, m ≤ T → m ≤ H → regret A ℓ' m ≤ ρ) :
    regret (Sub A γ hγ.le h1) ℓ T ≤ (1 / γ) * (ρ + T * ((1 + γ) ^ T / 2 ^ (H + 1))) := by
  set R : ℕ → ℝ := fun m => if m ≤ H then ρ else (m : ℝ) with hRdef
  have hR' : ∀ (ℓ' : LossSeq n) m, m ≤ T → regret A ℓ' m ≤ R m := by
    intro ℓ' m hm
    simp only [hRdef]
    split_ifs with hH
    · exact hR ℓ' m hm hH
    · exact regret_le A ℓ' m
  refine (regret_Sub_le A hA hγ h1 ℓ T R hR').trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hpt : ∀ F : Fin T → Bool, wt γ F * R (cnt (ext F) T) ≤
      wt γ F * ρ + (T : ℝ) * (wt γ F * (if H < cnt (ext F) T then (1 : ℝ) else 0)) := by
    intro F
    have hw := wt_nonneg hγ.le h1 F
    simp only [hRdef]
    split_ifs with hH hH'
    · omega
    · nlinarith [mul_nonneg hw (Nat.cast_nonneg T : (0 : ℝ) ≤ T)]
    · have hc : (cnt (ext F) T : ℝ) ≤ T := by exact_mod_cast cnt_le _ T
      nlinarith [mul_nonneg hw hρ]
    · omega
  calc _ ≤ ∑ F : Fin T → Bool, (wt γ F * ρ + (T : ℝ) * (wt γ F * (if H < cnt (ext F) T then (1 : ℝ) else 0))) :=
        Finset.sum_le_sum fun F _ => hpt F
    _ = ρ + T * ∑ F : Fin T → Bool, wt γ F * (if H < cnt (ext F) T then (1 : ℝ) else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_wt, one_mul, ← Finset.mul_sum]
    _ ≤ _ := by
        have := sum_wt_cnt_gt hγ.le h1 T H
        nlinarith [(Nat.cast_nonneg T : (0 : ℝ) ≤ T)]

/-- `(1 + γ)^T / 2^(H+1) ≤ e^{−x}` as soon as `2(γT + x) ≤ H + 1`. -/
theorem tail_le_exp {γ : ℝ} (h0 : 0 ≤ γ) (T H : ℕ) {x : ℝ} (hH : 2 * (γ * T + x) ≤ H + 1) :
    (1 + γ) ^ T / 2 ^ (H + 1) ≤ Real.exp (-x) := by
  have h1 : (1 + γ) ^ T ≤ Real.exp (γ * T) := by
    rw [mul_comm, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp γ]) T
  have hh : Real.exp (1 / 2) ≤ 2 := by
    have he : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h3 := Real.exp_one_lt_d9
    nlinarith [Real.exp_pos (1 / 2)]
  have h2 : Real.exp (((H + 1 : ℕ) : ℝ) / 2) ≤ 2 ^ (H + 1) := by
    rw [div_eq_mul_one_div, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hh _
  rw [div_le_iff₀ (by positivity)]
  calc (1 + γ) ^ T ≤ Real.exp (γ * T) := h1
    _ = Real.exp (-x) * Real.exp (((H + 1 : ℕ) : ℝ) / 2) * Real.exp (γ * T + x - ((H + 1 : ℕ) : ℝ) / 2) := by
        rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-x) * Real.exp (((H + 1 : ℕ) : ℝ) / 2) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Real.exp_le_one_iff]
        push_cast; linarith
    _ ≤ Real.exp (-x) * 2 ^ (H + 1) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le


end Pool.P0067

namespace Pool.P0067

open Pool.P0001 Pool.P0018 Real

variable {n : ℕ} [NeZero n] {T : ℕ}

/-- **Prefix regret of P0018's EXP3**: for every `m ≤ T`, the machine tuned for horizon `T` has regret at most
`(1/η) log n + m·δc` over the first `m` rounds. -/
theorem exp3M_regret_prefix (ℓ : LossSeq n) {m : ℕ} (hm : m ≤ T) :
    regret (exp3M n T) ℓ m ≤ (1 / eta n T) * Real.log n + m * δc n T := by
  have hη := eta_pos n T
  set Gbig : ℝ := (1 / eta n T) * Real.log n + Kcap n T + 1
  let Cond : St n (Kcap n T) → Prop := fun s => ∀ a, (s a : ℕ) + ⌊iw (eta n T) (gam T) s a⌋₊ + 1 ≤ Kcap n T
  classical
  refine Pool.P0012.regret_le_of_potential (exp3M n T) ℓ (fun i _ s => Φ (eta n T) i s)
    (fun _ _ s => if Cond s then δc n T else Gbig) m _ (fun i s => Φ_nonneg hη i s) ?_ ?_
  · intro i t _ s
    by_cases hc : Cond s
    · simp only [hc, if_true]
      exact step_le hη (gam_pos T) (gam_le T) i s (ℓ t) hc
    · simp only [hc, if_false]
      have hup : Pool.P0012.stepExp (exp3M n T) ℓ t s (Φ (eta n T) i) ≤
          (1 / eta n T) * Real.log n + Kcap n T := by
        change pexp (actPMF (η := eta n T) (gam_pos T) (gam_le_one T) s)
          (fun a => pexp (nextPMF (eta n T) (gam T) s a (ℓ t a)) (Φ (eta n T) i)) ≤ _
        calc _ ≤ pexp (actPMF (η := eta n T) (gam_pos T) (gam_le_one T) s)
              (fun _ => (1 / eta n T) * Real.log n + Kcap n T) :=
              pexp_mono _ fun a _ => (pexp_mono _ fun s' _ => Φ_le hη i s').trans
                (pexp_const _ _).le
          _ = _ := pexp_const _ _
      have h1 := stateLoss_le_one (T := T) ℓ t s
      have h2 := Φ_nonneg hη i s
      have h3 : (0 : ℝ) ≤ ((ℓ t i).toNat : ℝ) := Nat.cast_nonneg _
      linarith
  · intro i
    have h0 : Pool.P0012.expect (exp3M n T) ℓ 0 (Φ (eta n T) i) = (1 / eta n T) * Real.log n := by
      change pexp (PMF.pure fun _ => (0 : Fin (Kcap n T + 1))) (Φ (eta n T) i) = _
      rw [pexp_pure]
      simp [Φ, W, wt]
    have ht : ∀ t ∈ Finset.range m, Pool.P0012.expect (exp3M n T) ℓ t
        (fun s => if Cond s then δc n T else Gbig) = δc n T := by
      intro t ht
      have ht' : t < T := lt_of_lt_of_le (Finset.mem_range.1 ht) hm
      change pexp ((exp3M n T).stateDist ℓ t) _ = _
      rw [pexp_congr _ (g := fun _ => δc n T) fun s hs => by
        have hc : Cond s := fun a => noSat_of_good ht' (good_reachable ℓ t s hs) a
        simp only [hc, if_true]]
      exact pexp_const _ _
    rw [h0, Finset.sum_congr rfl ht, Finset.sum_const, Finset.card_range, nsmul_eq_mul]


/-- P0018's closed-form arithmetic: `(1/η) log n + T·δc ≤ (3/2)√((1+log n)(2n+1)(T+1)) + 1/2`. -/
theorem closed_form (n T : ℕ) [NeZero n] :
    (1 / eta n T) * Real.log n + T * δc n T ≤
      3 / 2 * Real.sqrt ((1 + Real.log n) * ((2 * n + 1) * (T + 1))) + 1 / 2 := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
  set A : ℝ := 1 + Real.log n with hA
  set Bc : ℝ := (2 * n + 1) * (T + 1) with hBc
  have hA0 : 0 < A := by rw [hA]; linarith
  have hB0 : 0 < Bc := by rw [hBc]; positivity
  have hη := eta_pos n T
  set S : ℝ := Real.sqrt (A * Bc) with hS
  have hηdef : eta n T = Real.sqrt (A / Bc) := rfl
  have hη2 : eta n T ^ 2 = A / Bc := by rw [hηdef]; exact Real.sq_sqrt (div_nonneg hA0.le hB0.le)
  have hηB : eta n T * Bc = S := by
    rw [hS, ← Real.sqrt_sq (mul_nonneg hη.le hB0.le)]
    congr 1
    rw [mul_pow, hη2]; field_simp
  have hSpos : 0 < S := by rw [hS]; positivity
  have h1 : (1 / eta n T) * Real.log n ≤ S := by
    have : (1 / eta n T) * Real.log n ≤ A / eta n T := by
      rw [one_div_mul_eq_div]; exact div_le_div_of_nonneg_right (by rw [hA]; linarith) hη.le
    have hAS : A = S * eta n T := by
      rw [← hηB]
      have : eta n T * Bc * eta n T = eta n T ^ 2 * Bc := by ring
      rw [this, hη2]; field_simp
    have h' : A / eta n T = S := by rw [hAS]; field_simp
    linarith
  have h2 : (T : ℝ) * (eta n T * (2 * n + 1) / 2) ≤ S / 2 := by
    have : (T : ℝ) * (eta n T * (2 * n + 1)) ≤ eta n T * Bc := by
      rw [hBc]; nlinarith [hη, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [hηB] at this; linarith
  have h3 : (T : ℝ) * gam T ≤ 1 / 2 := by
    unfold gam; rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  unfold δc
  nlinarith

theorem δc_nonneg (n T : ℕ) [NeZero n] : 0 ≤ δc n T := by
  unfold δc
  have := eta_pos n T
  have := gam_pos T
  positivity

/-- Prefix regret in closed form: every `m ≤ T` rounds, regret `≤ (3/2)√((1+log n)(2n+1)(T+1)) + 1/2`. -/
theorem exp3M_regret_prefix_sqrt (ℓ : LossSeq n) {m : ℕ} (hm : m ≤ T) :
    regret (exp3M n T) ℓ m ≤ 3 / 2 * Real.sqrt ((1 + Real.log n) * ((2 * n + 1) * (T + 1))) + 1 / 2 := by
  refine (exp3M_regret_prefix ℓ hm).trans (le_trans ?_ (closed_form n T))
  have := δc_nonneg n T
  have : (m : ℝ) ≤ T := by exact_mod_cast hm
  nlinarith

/-- **Subsampled EXP3.** Run P0018's EXP3 tuned for horizon `H` inside P0055's `Sub` with update probability `γ`.
Over `T` rounds, if `2(γT + x) ≤ H + 1`, the regret is at most
`(1/γ)·((3/2)√((1+log n)(2n+1)(H+1)) + 1/2 + T e^{−x})`. -/
theorem regret_Sub_exp3M {γ : ℝ} (hγ : 0 < γ) (h1 : γ ≤ 1) (ℓ : LossSeq n) (T H : ℕ) {x : ℝ}
    (hH : 2 * (γ * T + x) ≤ H + 1) :
    regret (Pool.P0055.Sub (exp3M n H) γ hγ.le h1) ℓ T ≤
      (1 / γ) * (3 / 2 * Real.sqrt ((1 + Real.log n) * ((2 * n + 1) * (H + 1))) + 1 / 2 + T * Real.exp (-x)) := by
  have hρ : 0 ≤ 3 / 2 * Real.sqrt ((1 + Real.log n) * ((2 * n + 1) * (H + 1))) + 1 / 2 := by positivity
  refine (regret_Sub_le_fixed (exp3M n H) exp3M_isHomogeneous hγ h1 ℓ T H _ hρ
    (fun ℓ' m _ hmH => exp3M_regret_prefix_sqrt ℓ' hmH)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := tail_le_exp hγ.le T H hH
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  nlinarith

end Pool.P0067
