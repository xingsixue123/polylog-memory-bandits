import Pool.P0069.Restart
import Pool.P0055.Subsample
import Pool.P0121.Proof


/-!
# Anytime and subsampled base learner from P0121's checked family (P0136's open step S3)

* `padZ`, `regret_padZ`, `regret_prefix_le`: zero padding (causality): a regret bound at horizon `H` for every
  loss sequence bounds the regret at every prefix `m ≤ H`.
* `rate n m = n^{1/3} m^{2/3} + n √m` (the shape of P0021's `BlockRate`), monotone and concave in `m`
  (`rate_mono`, `rate_concave`).
* `anyM F n T hn`: P0069's doubling `chain` of the machines `F n (2^j)` (or `F n n` while `2^j < n`), with a clock
  (homogeneous, `anyM_isHomogeneous`).
  - `anyM_regret_le`: if `F` has a fixed-horizon bound `C'·rate(n,T)·log(nT)^k'`, then for every prefix `m ≤ T`
    the regret of `anyM` is `≤ (log₂T + 1)·(max C' 0·rate(n,m)·log(nT)^k' + n)`.
  - `sub_anyM_regret_le`: P0055's subsampled machine `Sub (anyM …) γ` has regret over `T` rounds
    `≤ (1/γ)·(log₂T + 1)·(max C' 0·rate(n, γT)·log(nT)^k' + n)` (P0055's `regret_Sub_le` + Jensen for the
    concave `rate`).
  - `anyM_memBits_le`: `log₂(log₂T + 1) + max C 0·log(nT)^k + log₂(T + 1)` bits.
* `SubBaseRate`, `subBaseRate`: instantiated with P0121's `singleQueryRate`, with `L = log(nT) + 1`.
-/

open Pool.P0001 Pool.P0069 Pool.P0055 Finset

namespace Pool.P0144

variable {n : ℕ}

/-- Zero padding after round `m`. -/
def padZ (ℓ : LossSeq n) (m : ℕ) : LossSeq n := fun t => if t < m then ℓ t else fun _ => false

lemma expLoss_padZ (M : Machine n) (ℓ : LossSeq n) (m t : ℕ) :
    M.expLoss (padZ ℓ m) t = if t < m then M.expLoss ℓ t else 0 := by
  split_ifs with h
  · unfold Machine.expLoss Machine.armDist
    rw [stateDist_congr M (ℓ := padZ ℓ m) (ℓ' := ℓ) t (fun k hk => by simp [padZ, show k < m by omega])]
    simp [padZ, h]
  · unfold Machine.expLoss; simp [padZ, h]

lemma cumLoss_padZ (ℓ : LossSeq n) {m H : ℕ} (h : m ≤ H) (i : Fin n) :
    cumLoss (padZ ℓ m) H i = cumLoss ℓ m i := by
  unfold cumLoss
  rw [← Finset.sum_range_add_sum_Ico _ h]
  have h2 : ∑ t ∈ Finset.Ico m H, ((padZ ℓ m t i).toNat : ℝ) = 0 :=
    Finset.sum_eq_zero fun t ht => by
      rw [Finset.mem_Ico] at ht; simp [padZ, show ¬ t < m by omega]
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun t ht => by
    rw [Finset.mem_range] at ht; simp [padZ, ht]

/-- **Zero padding** (causality): the regret over `m` rounds is the regret over any longer horizon on the
zero-padded sequence. -/
theorem regret_padZ (M : Machine n) (ℓ : LossSeq n) {m H : ℕ} (h : m ≤ H) :
    regret M ℓ m = regret M (padZ ℓ m) H := by
  unfold regret bestLoss
  have hsum : ∑ t ∈ Finset.range H, M.expLoss (padZ ℓ m) t = ∑ t ∈ Finset.range m, M.expLoss ℓ t := by
    rw [← Finset.sum_range_add_sum_Ico _ h]
    have h2 : ∑ t ∈ Finset.Ico m H, M.expLoss (padZ ℓ m) t = 0 :=
      Finset.sum_eq_zero fun t ht => by
        rw [Finset.mem_Ico] at ht; rw [expLoss_padZ]; simp [show ¬ t < m by omega]
    rw [h2, add_zero]
    exact Finset.sum_congr rfl fun t ht => by
      rw [Finset.mem_range] at ht; rw [expLoss_padZ]; simp [ht]
  rw [hsum]
  congr 1
  exact congrArg _ (funext fun i => (cumLoss_padZ ℓ h i).symm)

/-- A regret bound at horizon `H` (for every sequence) bounds the regret at every prefix `m ≤ H`. -/
theorem regret_prefix_le (M : Machine n) {H : ℕ} {b : ℝ} (hb : ∀ ℓ : LossSeq n, regret M ℓ H ≤ b)
    (ℓ : LossSeq n) {m : ℕ} (hm : m ≤ H) : regret M ℓ m ≤ b := by
  rw [regret_padZ M ℓ hm]; exact hb _


/-! ## Anytime machine: P0069's doubling chain over a fixed-horizon family -/

/-- The rate shape of P0021's `BlockRate`. -/
noncomputable def rate (n m : ℝ) : ℝ := n ^ ((1 : ℝ) / 3) * m ^ ((2 : ℝ) / 3) + n * Real.sqrt m

lemma rate_nonneg {n m : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m) : 0 ≤ rate n m := by
  unfold rate; positivity

lemma rate_mono {n a b : ℝ} (hn : 0 ≤ n) (ha : 0 ≤ a) (hab : a ≤ b) : rate n a ≤ rate n b := by
  unfold rate
  have h1 : a ^ ((2 : ℝ) / 3) ≤ b ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow ha hab (by norm_num)
  have h2 : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have h3 : 0 ≤ n ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hn _
  nlinarith

lemma rate_concave {n : ℝ} (hn : 0 ≤ n) : ConcaveOn ℝ (Set.Ici 0) (rate n) := by
  have h1 : ConcaveOn ℝ (Set.Ici (0 : ℝ)) fun m : ℝ => m ^ ((2 : ℝ) / 3) :=
    (Real.strictConcaveOn_rpow (by norm_num) (by norm_num)).concaveOn
  have h2 : ConcaveOn ℝ (Set.Ici (0 : ℝ)) fun m : ℝ => Real.sqrt m := Real.strictConcaveOn_sqrt.concaveOn
  have := (h1.smul (Real.rpow_nonneg hn ((1 : ℝ) / 3))).add (h2.smul hn)
  have e : rate n = (fun m : ℝ => n ^ ((1 : ℝ) / 3) • m ^ ((2 : ℝ) / 3)) + fun m : ℝ => n • Real.sqrt m := by
    funext m; simp only [rate, Pi.add_apply, smul_eq_mul]
  rw [e]; exact this

variable (F : Family)

/-- Epoch `j` machine: `F n (2^j)` once `n ≤ 2^j`, otherwise `F n n` (charged trivially). -/
noncomputable def epM (n : ℕ) (hn : 1 ≤ n) (j : ℕ) : Machine n :=
  if n ≤ 2 ^ j then F n (2 ^ j) hn else F n n hn

/-- The anytime machine for horizon `T`: doubling epochs, then a clock (homogeneous). -/
noncomputable def anyM (n T : ℕ) (hn : 1 ≤ n) : Machine n :=
  (chain (epM F n hn) (fun i => 2 ^ i) (Nat.log 2 T) 0).withClock T

lemma anyM_isHomogeneous (n T : ℕ) (hn : 1 ≤ n) : (anyM F n T hn).IsHomogeneous :=
  Machine.withClock_isHomogeneous _ _

/-- Regret of the zero sequence is `0`, so any regret bound is nonnegative. -/
lemma regret_zero_seq (M : Machine n) (T : ℕ) : regret M (fun _ _ => false) T = 0 := by
  unfold regret Machine.expLoss bestLoss cumLoss; simp

/-- **Anytime regret** of `anyM`: every prefix `m ≤ T` costs at most `(log₂ T + 1)` times
`C'·rate(n, m)·log(nT)^k' + n`, when `F` has P0021's fixed-horizon bound (any `C'`). -/
theorem anyM_regret_le (C' : ℝ) (k' : ℕ)
    (hF : RegretBound F fun n T => C' * rate n T * Real.log (n * T) ^ k')
    (n T : ℕ) (hn : 1 ≤ n) (hnT : n ≤ T) (ℓ : LossSeq n) (m : ℕ) (hm : m ≤ T) :
    regret (anyM F n T hn) ℓ m ≤
      (Nat.log 2 T + 1) * (max C' 0 * rate n m * Real.log (n * T) ^ k' + n) := by
  haveI : NeZero n := ⟨by omega⟩
  set X : ℝ := max C' 0 * rate n m * Real.log (n * T) ^ k' + n with hX
  set b : ℕ → ℝ := fun j => if n ≤ 2 ^ j then C' * rate n (2 ^ j) * Real.log (n * 2 ^ j) ^ k'
    else (2 ^ j : ℝ) with hb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : ∀ H : ℕ, 1 ≤ H → 0 ≤ Real.log (n * H) := fun H hH =>
    Real.log_nonneg (by
      have : (1 : ℝ) ≤ H := by exact_mod_cast hH
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith)
  -- every per-epoch bound is a valid bound (prefix), and is nonnegative
  have hbj : ∀ j (ℓ' : LossSeq n) m', m' ≤ 2 ^ j → regret (epM F n hn j) ℓ' m' ≤ b j := by
    intro j ℓ' m' hm'
    simp only [epM, hb]
    split_ifs with h
    · exact regret_prefix_le _ (fun ℓ'' => by
        have := hF n (2 ^ j) hn h ℓ''
        simpa using this) ℓ' hm'
    · exact (regret_le _ ℓ' m').trans (by exact_mod_cast hm')
  have hb0 : ∀ j, 0 ≤ b j := by
    intro j
    have h := hbj j (fun _ _ => false) 0 (Nat.zero_le _)
    simp only [hb]
    split_ifs with h'
    · have h2 := hF n (2 ^ j) hn h' (fun _ _ => false)
      rw [regret_zero_seq] at h2
      simpa using h2
    · positivity
  unfold anyM
  rw [regret_withClock_of_le _ _ _ _ (by omega)]
  have hcov : m ≤ start (fun i => 2 ^ i) 0 (Nat.log 2 T + 1) := by
    have h1 := start_pow (Nat.log 2 T + 1)
    have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) T
    omega
  refine (regret_chain_le (epM F n hn) (fun i => 2 ^ i) b hb0 hbj (Nat.log 2 T) 0 ℓ m hcov).trans ?_
  -- each charged term is ≤ X
  have hterm : ∀ j ∈ Finset.range (Nat.log 2 T + 1),
      (if start (fun i => 2 ^ i) 0 j < m then b (0 + j) else 0) ≤ X := by
    intro j hj
    have hX0 : 0 ≤ X := by
      have := rate_nonneg hn0.le (Nat.cast_nonneg m (α := ℝ))
      have := hlogpos T (by omega)
      rw [hX]; positivity
    split_ifs with hs
    · have hjm : 2 ^ j ≤ m := by have := start_pow j; omega
      rw [zero_add]; simp only [hb]
      split_ifs with h
      · -- big epoch: monotone in the horizon
        have hjT : (2 : ℝ) ^ j ≤ T := by exact_mod_cast (le_trans hjm hm)
        have hlog : Real.log (n * 2 ^ j) ≤ Real.log (n * T) :=
          Real.log_le_log (by positivity) (by nlinarith)
        have hl0 : 0 ≤ Real.log (n * 2 ^ j) := by
          have := hlogpos (2 ^ j) (Nat.one_le_two_pow); simpa using this
        have hr : rate n (2 ^ j) ≤ rate n m :=
          rate_mono hn0.le (by positivity) (by exact_mod_cast hjm)
        have hr0 : 0 ≤ rate n (2 ^ j) := rate_nonneg hn0.le (by positivity)
        have hp : Real.log (n * 2 ^ j) ^ k' ≤ Real.log (n * T) ^ k' := pow_le_pow_left₀ hl0 hlog k'
        have hp0 : 0 ≤ Real.log (n * 2 ^ j) ^ k' := pow_nonneg hl0 k'
        calc C' * rate n (2 ^ j) * Real.log (n * 2 ^ j) ^ k'
            ≤ max C' 0 * rate n (2 ^ j) * Real.log (n * 2 ^ j) ^ k' := by
              have := le_max_left C' 0; gcongr
          _ ≤ max C' 0 * rate n m * Real.log (n * T) ^ k' := by
              have hm0 := le_max_right C' 0
              exact mul_le_mul (mul_le_mul_of_nonneg_left hr hm0) hp hp0
                (mul_nonneg hm0 (rate_nonneg hn0.le (Nat.cast_nonneg m)))
          _ ≤ X := by rw [hX]; linarith
      · have : (2 : ℝ) ^ j ≤ n := by exact_mod_cast (le_of_lt (not_le.1 h))
        have := rate_nonneg hn0.le (Nat.cast_nonneg m (α := ℝ))
        have := hlogpos T (by omega)
        have : 0 ≤ max C' 0 * rate n m * Real.log (n * T) ^ k' := by positivity
        rw [hX]; linarith
    · exact hX0
  calc _ ≤ ∑ _j ∈ Finset.range (Nat.log 2 T + 1), X := Finset.sum_le_sum hterm
    _ = (Nat.log 2 T + 1) * X := by simp


/-! ## Subsampled anytime base (P0055) via Jensen -/

/-- **Subsampled base**: playing `anyM` every round and updating it only with probability `γ`
(P0055's `Sub`) has regret at most `(1/γ)·(log₂ T + 1)·(C'₊·rate(n, γT)·log(nT)^k' + n)`. -/
theorem sub_anyM_regret_le (C' : ℝ) (k' : ℕ)
    (hF : RegretBound F fun n T => C' * rate n T * Real.log (n * T) ^ k')
    (n T : ℕ) (hn : 1 ≤ n) (hnT : n ≤ T) {γ : ℝ} (hγ : 0 < γ) (h1 : γ ≤ 1) (ℓ : LossSeq n) :
    regret (Sub (anyM F n T hn) γ hγ.le h1) ℓ T ≤
      (1 / γ) * ((Nat.log 2 T + 1) * (max C' 0 * rate n (γ * T) * Real.log (n * T) ^ k' + n)) := by
  haveI : NeZero n := ⟨by omega⟩
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : 0 ≤ Real.log (n * T) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
    nlinarith)
  set f : ℝ → ℝ := fun x => (Nat.log 2 T + 1) * (max C' 0 * rate n x * Real.log (n * T) ^ k' + n) with hf
  have hreg := regret_Sub_le (anyM F n T hn) (anyM_isHomogeneous F n T hn) hγ h1 ℓ T
    (fun m => f m) (fun ℓ' m hm => anyM_regret_le F C' k' hF n T hn hnT ℓ' m hm)
  refine hreg.trans ?_
  gcongr
  -- Jensen
  have hconc : ConcaveOn ℝ (Set.Ici 0) f := by
    have hc : 0 ≤ max C' 0 * Real.log (n * T) ^ k' := mul_nonneg (le_max_right _ _) (pow_nonneg hL _)
    have h2 := ((rate_concave hn0).smul hc).add_const (n : ℝ)
    have h3 := h2.smul (show (0 : ℝ) ≤ (Nat.log 2 T + 1 : ℝ) by positivity)
    have e : f = (Nat.log 2 T + 1 : ℝ) • ((max C' 0 * Real.log (n * T) ^ k') • rate n + fun _ => (n : ℝ)) := by
      funext x; simp only [hf, Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring
    rw [e]; exact h3
  have hw0 : ∀ F' ∈ (Finset.univ : Finset (Fin T → Bool)), 0 ≤ wt γ F' := fun F' _ => wt_nonneg hγ.le h1 F'
  have hj := hconc.le_map_sum hw0 (sum_wt γ T) (p := fun F' => (cnt (ext F') T : ℝ))
    (fun F' _ => Set.mem_Ici.2 (Nat.cast_nonneg _))
  simp only [smul_eq_mul] at hj
  rw [sum_wt_cnt] at hj
  exact hj


/-! ## Memory -/

lemma card_le_two_rpow (M : Machine n) {b : ℝ} (h : M.memBits ≤ b) :
    (Fintype.card M.State : ℝ) ≤ (2 : ℝ) ^ b := by
  have hpos : 0 < Fintype.card M.State := by
    obtain ⟨s, -⟩ := M.init.support_nonempty
    exact Fintype.card_pos_iff.2 ⟨s⟩
  have hc : (0 : ℝ) < Fintype.card M.State := by exact_mod_cast hpos
  calc (Fintype.card M.State : ℝ) = (2 : ℝ) ^ M.memBits := by
        rw [Machine.memBits, Real.rpow_logb (by norm_num) (by norm_num) hc]
    _ ≤ (2 : ℝ) ^ b := Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- **Memory** of `anyM`: `log₂(log₂ T + 1) + C₊·log(nT)^k + log₂(T + 1)` bits. -/
theorem anyM_memBits_le (C : ℝ) (k : ℕ) (hM : MemoryBound F C k)
    (n T : ℕ) (hn : 1 ≤ n) (hnT : n ≤ T) :
    (anyM F n T hn).memBits ≤
      Real.logb 2 (Nat.log 2 T + 1) + max C 0 * Real.log (n * T) ^ k + Real.logb 2 (T + 1) := by
  haveI : NeZero n := ⟨by omega⟩
  set r := Nat.log 2 T
  set B : ℝ := max C 0 * Real.log (n * T) ^ k with hB
  have hL : 0 ≤ Real.log (n * T) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
    nlinarith)
  have hE : ∀ j ≤ r, (Fintype.card (epM F n hn j).State : ℝ) ≤ (2 : ℝ) ^ B := by
    intro j hj
    apply card_le_two_rpow
    have hH : ∀ H : ℕ, n ≤ H → H ≤ T → (F n H hn).memBits ≤ B := by
      intro H hnH hHT
      have h1 := hM n H hn hnH
      have hl0 : 0 ≤ Real.log (n * H) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have : (n : ℝ) ≤ H := by exact_mod_cast hnH
        nlinarith)
      have hl : Real.log (n * H) ≤ Real.log (n * T) := Real.log_le_log (by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        have : (n : ℝ) ≤ H := by exact_mod_cast hnH
        nlinarith) (by
        have : (H : ℝ) ≤ T := by exact_mod_cast hHT
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith)
      calc (F n H hn).memBits ≤ C * Real.log (n * H) ^ k := h1
        _ ≤ max C 0 * Real.log (n * H) ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hl0 _)
        _ ≤ B := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 hl k) (le_max_right _ _)
    simp only [epM]
    split_ifs with h
    · exact hH _ h (le_trans (Nat.pow_le_pow_right (by norm_num) hj) (Nat.pow_log_le_self 2 (by omega)))
    · exact hH n le_rfl hnT
  have hcard : (Fintype.card (chain (epM F n hn) (fun i => 2 ^ i) r 0).State : ℝ) ≤ (r + 1) * (2 : ℝ) ^ B := by
    rw [card_chain]
    push_cast
    calc ∑ j ∈ Finset.range (r + 1), (Fintype.card (epM F n hn (0 + j)).State : ℝ)
        ≤ ∑ _j ∈ Finset.range (r + 1), (2 : ℝ) ^ B :=
          Finset.sum_le_sum fun j hj => by
            rw [zero_add]; exact hE j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      _ = (r + 1) * (2 : ℝ) ^ B := by simp
  have hpos : 0 < Fintype.card (chain (epM F n hn) (fun i => 2 ^ i) r 0).State := by
    obtain ⟨s, -⟩ := (chain (epM F n hn) (fun i => 2 ^ i) r 0).init.support_nonempty
    exact Fintype.card_pos_iff.2 ⟨s⟩
  unfold anyM
  rw [Machine.memBits_withClock, Machine.memBits]
  have : Real.logb 2 (Fintype.card (chain (epM F n hn) (fun i => 2 ^ i) r 0).State) ≤
      Real.logb 2 (r + 1) + B := by
    calc _ ≤ Real.logb 2 ((r + 1) * (2 : ℝ) ^ B) :=
          Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos) hcard
      _ = Real.logb 2 (r + 1) + B := by
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_rpow (by norm_num) (by norm_num)]
  linarith


/-! ## Logarithmic bookkeeping and the packaged statement -/

lemma logb_two_le (n T : ℕ) (hn : 1 ≤ n) (hnT : n ≤ T) :
    Real.logb 2 T ≤ 2 * Real.log (n * T) := by
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hle : Real.log T ≤ Real.log (n * T) := Real.log_le_log (by linarith) (by nlinarith)
  rw [Real.logb, div_le_iff₀ (by linarith)]
  nlinarith

lemma natLog_add_one_le (n T : ℕ) (hn : 1 ≤ n) (hnT : n ≤ T) :
    ((Nat.log 2 T : ℕ) + 1 : ℝ) ≤ 2 * (Real.log (n * T) + 1) := by
  have h1 : ((Nat.log 2 T : ℕ) : ℝ) ≤ Real.logb 2 T := by exact_mod_cast Real.natLog_le_logb T 2
  have h2 := logb_two_le n T hn hnT
  have h3 : 0 ≤ Real.log (n * T) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
    nlinarith)
  linarith

lemma logb_succ_le (n T : ℕ) (hn : 1 ≤ n) (hnT : n ≤ T) :
    Real.logb 2 (T + 1) ≤ 2 * (Real.log (n * T) + 1) := by
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
  have h1 : Real.logb 2 (T + 1) ≤ Real.logb 2 (2 * T) :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num)] at h1
  have h2 := logb_two_le n T hn hnT
  linarith

/-- **S3 of P0136 (anytime and subsampled base), unconditional**: for all `1 ≤ n ≤ T` there is a
homogeneous single-query machine `A` with polylog memory, regret `≤ c·L^k·(n^{1/3}m^{2/3} + n√m + n)`
at **every** prefix `m ≤ T`, and whose subsampled version `Sub A γ` (P0055: play `A` every round,
update it only with probability `γ`) has regret `≤ c·L^k·(n^{1/3}(γT)^{2/3} + n√(γT) + n)/γ` over `T`
rounds, where `L = log(nT) + 1`. -/
def SubBaseRate : Prop :=
  ∃ (c : ℝ) (k : ℕ), ∀ (n T : ℕ) (hn : 1 ≤ n), n ≤ T → ∃ A : Machine n, A.IsHomogeneous ∧
    A.memBits ≤ c * (Real.log (n * T) + 1) ^ k ∧
    (∀ (ℓ : LossSeq n) (m : ℕ), m ≤ T → regret A ℓ m ≤
      c * (Real.log (n * T) + 1) ^ k *
        ((n : ℝ) ^ ((1 : ℝ) / 3) * (m : ℝ) ^ ((2 : ℝ) / 3) + n * Real.sqrt m + n)) ∧
    ∀ (γ : ℝ) (hγ : 0 < γ) (h1 : γ ≤ 1) (ℓ : LossSeq n), regret (Sub A γ hγ.le h1) ℓ T ≤
      c * (Real.log (n * T) + 1) ^ k *
        ((n : ℝ) ^ ((1 : ℝ) / 3) * (γ * T) ^ ((2 : ℝ) / 3) + n * Real.sqrt (γ * T) + n) / γ

theorem subBaseRate : SubBaseRate := by
  obtain ⟨F, -, ⟨C, k, hM⟩, C', k', hR⟩ := Pool.P0121.TClaim.singleQueryRate
  have hF : RegretBound F fun n T => C' * rate n T * Real.log (n * T) ^ k' := by
    intro n T hn hnT ℓ; have := hR n T hn hnT ℓ; simpa [rate, mul_assoc] using this
  set Cp := max C' 0 with hCp
  set Cm := max C 0 with hCm
  refine ⟨2 * (Cp + 1) + 4 + Cm, k + k' + 1, fun n T hn hnT => ⟨anyM F n T hn, anyM_isHomogeneous F n T hn,
    ?_, ?_, ?_⟩⟩
  all_goals
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
    have hl0 : 0 ≤ Real.log (n * T) := Real.log_nonneg (by nlinarith)
    set L := Real.log (n * T) + 1 with hLdef
    have hL1 : 1 ≤ L := by linarith
    have hLk : ∀ j ≤ k + k' + 1, L ^ j ≤ L ^ (k + k' + 1) := fun j hj => pow_le_pow_right₀ hL1 hj
    have hlk : ∀ j, Real.log (n * T) ^ j ≤ L ^ j := fun j => pow_le_pow_left₀ hl0 (by linarith) j
    have hCp0 : 0 ≤ Cp := le_max_right _ _
    have hCm0 : 0 ≤ Cm := le_max_right _ _
    have hN := natLog_add_one_le n T hn hnT
  · -- memory
    have h := anyM_memBits_le F C k hM n T hn hnT
    have h1 : Real.logb 2 ((Nat.log 2 T : ℕ) + 1) ≤ Real.logb 2 (T + 1) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) (by
        have : ((Nat.log 2 T : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.log_le_self 2 T
        linarith)
    have h2 := logb_succ_le n T hn hnT
    have h3 : Cm * Real.log (n * T) ^ k ≤ Cm * L ^ (k + k' + 1) :=
      mul_le_mul_of_nonneg_left ((hlk k).trans (hLk k (by omega))) hCm0
    have h4 : L ≤ L ^ (k + k' + 1) := by
      have := hLk 1 (by omega); simpa using this
    have h5 : 0 ≤ L ^ (k + k' + 1) := by positivity
    rw [← hCm] at h
    nlinarith
  · intro ℓ m hm
    have h := anyM_regret_le F C' k' hF n T hn hnT ℓ m hm
    rw [← hCp] at h
    have hr0 : 0 ≤ rate n m := rate_nonneg (by positivity) (Nat.cast_nonneg m)
    have hX : Cp * rate n m * Real.log (n * T) ^ k' + n ≤ (Cp + 1) * L ^ k' * (rate n m + n) := by
      have := mul_le_mul_of_nonneg_left (hlk k') (mul_nonneg hCp0 hr0)
      have hLk1 : 1 ≤ L ^ k' := one_le_pow₀ hL1
      have : (n : ℝ) ≤ L ^ k' * n := by nlinarith
      nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ L) k']
    have hX0 : 0 ≤ Cp * rate n m * Real.log (n * T) ^ k' + n := by positivity
    have hstep : ((Nat.log 2 T : ℕ) + 1 : ℝ) * (Cp * rate n m * Real.log (n * T) ^ k' + n) ≤
        2 * L * ((Cp + 1) * L ^ k' * (rate n m + n)) :=
      mul_le_mul hN hX hX0 (by positivity)
    have hfin : 2 * L * ((Cp + 1) * L ^ k' * (rate n m + n)) ≤
        (2 * (Cp + 1) + 4 + Cm) * L ^ (k + k' + 1) * (rate n m + n) := by
      have hp : L * L ^ k' ≤ L ^ (k + k' + 1) := by
        rw [← pow_succ']; exact hLk (k' + 1) (by omega)
      have hrn : 0 ≤ rate n m + n := by positivity
      have : 2 * L * ((Cp + 1) * L ^ k' * (rate n m + n)) = 2 * (Cp + 1) * (L * L ^ k') * (rate n m + n) := by ring
      rw [this]
      have h6 : 2 * (Cp + 1) * (L * L ^ k') ≤ (2 * (Cp + 1) + 4 + Cm) * L ^ (k + k' + 1) := by
        have h7 : 0 ≤ L ^ (k + k' + 1) := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_right h6 hrn
    have := (h.trans hstep).trans hfin
    simpa [rate, add_assoc] using this
  · intro γ hγ h1 ℓ
    have h := sub_anyM_regret_le F C' k' hF n T hn hnT hγ h1 ℓ
    rw [← hCp] at h
    have hγT : 0 ≤ γ * T := by positivity
    have hr0 : 0 ≤ rate n (γ * T) := rate_nonneg (by positivity) hγT
    have hX : Cp * rate n (γ * T) * Real.log (n * T) ^ k' + n ≤ (Cp + 1) * L ^ k' * (rate n (γ * T) + n) := by
      have := mul_le_mul_of_nonneg_left (hlk k') (mul_nonneg hCp0 hr0)
      have hLk1 : 1 ≤ L ^ k' := one_le_pow₀ hL1
      have : (n : ℝ) ≤ L ^ k' * n := by nlinarith
      nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ L) k']
    have hX0 : 0 ≤ Cp * rate n (γ * T) * Real.log (n * T) ^ k' + n := by positivity
    have hstep : ((Nat.log 2 T : ℕ) + 1 : ℝ) * (Cp * rate n (γ * T) * Real.log (n * T) ^ k' + n) ≤
        2 * L * ((Cp + 1) * L ^ k' * (rate n (γ * T) + n)) :=
      mul_le_mul hN hX hX0 (by positivity)
    have hfin : 2 * L * ((Cp + 1) * L ^ k' * (rate n (γ * T) + n)) ≤
        (2 * (Cp + 1) + 4 + Cm) * L ^ (k + k' + 1) * (rate n (γ * T) + n) := by
      have hp : L * L ^ k' ≤ L ^ (k + k' + 1) := by
        rw [← pow_succ']; exact hLk (k' + 1) (by omega)
      have hrn : 0 ≤ rate n (γ * T) + n := by positivity
      have : 2 * L * ((Cp + 1) * L ^ k' * (rate n (γ * T) + n)) =
          2 * (Cp + 1) * (L * L ^ k') * (rate n (γ * T) + n) := by ring
      rw [this]
      have h6 : 2 * (Cp + 1) * (L * L ^ k') ≤ (2 * (Cp + 1) + 4 + Cm) * L ^ (k + k' + 1) := by
        have h7 : 0 ≤ L ^ (k + k' + 1) := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_right h6 hrn
    have hmain := mul_le_mul_of_nonneg_left ((hstep.trans hfin)) (by positivity : (0 : ℝ) ≤ 1 / γ)
    have := h.trans hmain
    rw [div_eq_mul_one_div _ γ]
    have e : (2 * (Cp + 1) + 4 + Cm) * L ^ (k + k' + 1) *
        ((n : ℝ) ^ ((1 : ℝ) / 3) * (γ * T) ^ ((2 : ℝ) / 3) + n * Real.sqrt (γ * T) + n) * (1 / γ) =
        1 / γ * ((2 * (Cp + 1) + 4 + Cm) * L ^ (k + k' + 1) * (rate n (γ * T) + n)) := by
      simp only [rate]; ring
    rw [e]; exact this

end Pool.P0144
