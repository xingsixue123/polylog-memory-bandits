import Pool.P0018.Exp3
import Pool.P0055.Subsample
import Pool.P0067.SubFixed

/-!
# Restarts (running machines one after another) and an anytime EXP3

* `seq A B L`: play `A` on the rounds `t < L`, then a fresh copy of `B` (started from `B.init`)
  on the shifted loss sequence `shift ℓ L = fun t ↦ ℓ (t + L)`. State type `A.State ⊕ B.State`.
  - `stateDist_seq_lt`, `stateDist_seq_ge`, `expLoss_seq_lt`, `expLoss_seq_ge`: before the switch
    the run is `A`'s run; from the switch on it is `B`'s run on the shifted sequence.
  - `regret_seq_of_le`, `regret_seq_le`: regret is that of `A` up to the switch, and is
    subadditive across it: `regret (seq A B L) ℓ (L + m) ≤ regret A ℓ L + regret B (shift ℓ L) m`.
* `chain E len r k`: epochs `k, k+1, …, k+r` of lengths `len j`, machine `E j` restarted in epoch
  `j` (the last one runs forever). `regret_chain_le`: if every `E j` has regret `≤ b j` on every
  prefix of at most `len j` rounds, the chain's regret over `m` rounds is at most the sum of `b j`
  over the epochs that start before round `m`. `card_chain`: the state count is the sum.
* `anytimeExp3 n T`: P0018's EXP3 tuned for horizon `2^j` in epoch `j` (doubling trick),
  with a clock (homogeneous).
  - `anytimeExp3_regret_le`: for every loss sequence and **every** `m ≤ T`,
    `regret ≤ (2 + √2) C √m` with `C = dblC n = (3/2) √(2 (1 + log n)(2n + 1)) + 1/2`.
  - `anytimeExp3_memBits_le`: `memBits ≤ n log₂ (Kcap n T + 1) + 2 log₂ (T + 1)`.
  - `regret_Sub_anytimeExp3_le`: with P0055's subsampled play,
    `regret (Sub (anytimeExp3 n T) γ) ℓ T ≤ (2 + √2) C √(T / γ)`.
-/

open scoped ENNReal

namespace Pool.P0069

open Pool.P0001

variable {n : ℕ}

/-- The loss sequence seen from round `L` on. -/
def shift (ℓ : LossSeq n) (L : ℕ) : LossSeq n := fun t => ℓ (t + L)

/-- Play `A` on rounds `t < L`, then a fresh `B` on the rounds `t ≥ L`. -/
@[reducible] noncomputable def seq (A B : Machine n) (L : ℕ) : Machine n where
  State := A.State ⊕ B.State
  init := if L = 0 then B.init.map Sum.inr else A.init.map Sum.inl
  act t s := Sum.elim (A.act t) (B.act (t - L)) s
  next t s a b := match s with
    | Sum.inl s => if t + 1 = L then B.init.map Sum.inr else (A.next t s a b).map Sum.inl
    | Sum.inr s => (B.next (t - L) s a b).map Sum.inr

lemma card_seq (A B : Machine n) (L : ℕ) :
    Fintype.card (seq A B L).State = Fintype.card A.State + Fintype.card B.State :=
  Fintype.card_sum

/-- Before the switch, `seq A B L` is `A`. -/
lemma stateDist_seq_lt (A B : Machine n) (L : ℕ) (ℓ : LossSeq n) :
    ∀ t, t < L → (seq A B L).stateDist ℓ t = (A.stateDist ℓ t).map Sum.inl := by
  intro t
  induction t with
  | zero =>
    intro h
    simp [Machine.stateDist, seq, show L ≠ 0 by omega]
  | succ t ih =>
    intro h
    simp only [Machine.stateDist]
    rw [ih (by omega)]
    simp only [PMF.bind_map, PMF.map_bind, Function.comp_def]
    congr 1; funext s
    simp only [seq, Sum.elim_inl, show t + 1 ≠ L by omega, if_false]

/-- From the switch on, `seq A B L` is a fresh `B` on the shifted sequence. -/
lemma stateDist_seq_ge (A B : Machine n) (L : ℕ) (ℓ : LossSeq n) :
    ∀ u, (seq A B L).stateDist ℓ (u + L) = (B.stateDist (shift ℓ L) u).map Sum.inr := by
  intro u
  induction u with
  | zero =>
    rcases Nat.eq_zero_or_pos L with hL | hL
    · subst hL; simp [Machine.stateDist, seq]
    · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
      rw [Nat.zero_add]
      conv_lhs => rw [Machine.stateDist]
      rw [stateDist_seq_lt A B (L' + 1) ℓ L' (by omega)]
      simp only [PMF.bind_map, Function.comp_def, seq, Sum.elim_inl, if_true]
      simp [PMF.bind_const]
      rfl
  | succ u ih =>
    rw [show u + 1 + L = (u + L) + 1 by omega]
    simp only [Machine.stateDist]
    rw [ih]
    simp only [PMF.bind_map, PMF.map_bind, Function.comp_def]
    congr 1; funext s
    simp only [Sum.elim_inr, show u + L - L = u by omega, shift]

lemma armDist_seq_lt (A B : Machine n) (L : ℕ) (ℓ : LossSeq n) (t : ℕ) (h : t < L) :
    (seq A B L).armDist ℓ t = A.armDist ℓ t := by
  rw [Machine.armDist, stateDist_seq_lt A B L ℓ t h, PMF.bind_map]
  rfl

lemma armDist_seq_ge (A B : Machine n) (L : ℕ) (ℓ : LossSeq n) (u : ℕ) :
    (seq A B L).armDist ℓ (u + L) = B.armDist (shift ℓ L) u := by
  rw [Machine.armDist, stateDist_seq_ge A B L ℓ u, PMF.bind_map]
  simp only [Machine.armDist, Function.comp_def, seq, Sum.elim_inr, show u + L - L = u by omega]

lemma expLoss_seq_lt (A B : Machine n) (L : ℕ) (ℓ : LossSeq n) (t : ℕ) (h : t < L) :
    (seq A B L).expLoss ℓ t = A.expLoss ℓ t := by
  simp only [Machine.expLoss, armDist_seq_lt A B L ℓ t h]

lemma expLoss_seq_ge (A B : Machine n) (L : ℕ) (ℓ : LossSeq n) (u : ℕ) :
    (seq A B L).expLoss ℓ (u + L) = B.expLoss (shift ℓ L) u := by
  simp only [Machine.expLoss, armDist_seq_ge A B L ℓ u, shift]


/-! ### Regret across a switch -/

lemma cumLoss_add (ℓ : LossSeq n) (L m : ℕ) (i : Fin n) :
    cumLoss ℓ (L + m) i = cumLoss ℓ L i + cumLoss (shift ℓ L) m i := by
  simp only [cumLoss, shift, Finset.sum_range_add, add_comm _ L]

lemma bestLoss_add_le [NeZero n] (ℓ : LossSeq n) (L m : ℕ) :
    bestLoss ℓ L + bestLoss (shift ℓ L) m ≤ bestLoss ℓ (L + m) := by
  unfold bestLoss
  refine le_ciInf fun i => ?_
  rw [cumLoss_add]
  exact add_le_add (bestLoss_le_cumLoss ℓ L i) (bestLoss_le_cumLoss _ m i)

lemma regret_seq_of_le (A B : Machine n) (L : ℕ) (ℓ : LossSeq n) (m : ℕ) (hm : m ≤ L) :
    regret (seq A B L) ℓ m = regret A ℓ m := by
  unfold regret
  congr 1
  exact Finset.sum_congr rfl fun t ht => expLoss_seq_lt A B L ℓ t (by
    have := Finset.mem_range.1 ht; omega)

/-- Regret is subadditive across the switch. -/
theorem regret_seq_le [NeZero n] (A B : Machine n) (L : ℕ) (ℓ : LossSeq n) (m : ℕ) :
    regret (seq A B L) ℓ (L + m) ≤ regret A ℓ L + regret B (shift ℓ L) m := by
  have hsum : ∑ t ∈ Finset.range (L + m), (seq A B L).expLoss ℓ t =
      ∑ t ∈ Finset.range L, A.expLoss ℓ t + ∑ u ∈ Finset.range m, B.expLoss (shift ℓ L) u := by
    rw [Finset.sum_range_add]
    congr 1
    · exact Finset.sum_congr rfl fun t ht => expLoss_seq_lt A B L ℓ t (Finset.mem_range.1 ht)
    · exact Finset.sum_congr rfl fun u _ => by rw [add_comm L u, expLoss_seq_ge]
  have := bestLoss_add_le ℓ L m
  unfold regret
  rw [hsum]
  linarith

/-! ### Chains of epochs -/

/-- `chain E len r k` plays `E k` for `len k` rounds, then `E (k+1)` for `len (k+1)` rounds, …,
and finally `E (k + r)` forever (each machine started fresh at the start of its epoch). -/
noncomputable def chain (E : ℕ → Machine n) (len : ℕ → ℕ) : ℕ → ℕ → Machine n
  | 0, k => E k
  | r + 1, k => seq (E k) (chain E len r (k + 1)) (len k)

lemma regret_zero (M : Machine n) [NeZero n] (ℓ : LossSeq n) : regret M ℓ 0 = 0 := by
  simp [regret, bestLoss, cumLoss]

/-- Start of epoch `j` of `chain E len _ k`, relative to the start of the chain. -/
def start (len : ℕ → ℕ) (k j : ℕ) : ℕ := ∑ i ∈ Finset.range j, len (k + i)

/-- Regret of a chain: only the epochs that have started before round `m` are charged, each
with its per-epoch bound. -/
theorem regret_chain_le [NeZero n] (E : ℕ → Machine n) (len : ℕ → ℕ) (b : ℕ → ℝ)
    (hb0 : ∀ j, 0 ≤ b j) (hb : ∀ j (ℓ : LossSeq n) m, m ≤ len j → regret (E j) ℓ m ≤ b j) :
    ∀ r k (ℓ : LossSeq n) m, m ≤ start len k (r + 1) →
      regret (chain E len r k) ℓ m ≤
        ∑ j ∈ Finset.range (r + 1), if start len k j < m then b (k + j) else 0 := by
  intro r
  induction r with
  | zero =>
    intro k ℓ m hm
    simp only [start, Finset.range_one, Finset.sum_singleton, add_zero, zero_add,
      Finset.range_zero, Finset.sum_empty] at hm ⊢
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp [chain, regret_zero]
    · simp only [hpos, if_true]; exact hb k ℓ m hm
  | succ r ih =>
    intro k ℓ m hm
    have hsplit : ∀ j, start len k (j + 1) = len k + start len (k + 1) j := by
      intro j
      simp only [start]
      rw [Finset.sum_range_succ']
      simp only [add_zero, Nat.add_assoc, Nat.add_comm 1]
      ring
    rw [Finset.sum_range_succ']
    have hrest : 0 ≤ ∑ j ∈ Finset.range (r + 1),
        (if start len k (j + 1) < m then b (k + (j + 1)) else 0) :=
      Finset.sum_nonneg fun j _ => by split_ifs <;> simp [hb0]
    by_cases hmk : m ≤ len k
    · rw [show chain E len (r + 1) k = seq (E k) (chain E len r (k + 1)) (len k) from rfl,
        regret_seq_of_le _ _ _ _ _ hmk]
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · subst h0; rw [regret_zero]; simp
      · have : start len k 0 < m := by simp [start, hpos]
        simp only [this, ite_true, add_zero]
        have := hb k ℓ m hmk
        linarith
    · obtain ⟨m', rfl⟩ : ∃ m', m = len k + m' := ⟨m - len k, by omega⟩
      rw [show chain E len (r + 1) k = seq (E k) (chain E len r (k + 1)) (len k) from rfl]
      refine (regret_seq_le _ _ _ ℓ m').trans ?_
      have h1 := hb k ℓ (len k) le_rfl
      have hm' : m' ≤ start len (k + 1) (r + 1) := by
        have := hsplit (r + 1); omega
      have h2 := ih (k + 1) (shift ℓ (len k)) m' hm'
      have e : ∀ j ∈ Finset.range (r + 1),
          (if start len k (j + 1) < len k + m' then b (k + (j + 1)) else 0) =
          (if start len (k + 1) j < m' then b (k + 1 + j) else 0) := by
        intro j _
        rw [hsplit j, show k + (j + 1) = k + 1 + j by omega]
        simp only [Nat.add_lt_add_iff_left]
      rw [Finset.sum_congr rfl e]
      have : start len k 0 < len k + m' := by simp [start]; omega
      simp only [this, ite_true, add_zero]
      linarith


/-! ### Clock -/

lemma regret_withClock_of_le (M : Machine n) (T : ℕ) (ℓ : LossSeq n) (m : ℕ) (hm : m ≤ T + 1) :
    regret (M.withClock T) ℓ m = regret M ℓ m := by
  unfold regret
  congr 1
  exact Finset.sum_congr rfl fun t ht =>
    M.withClock_expLoss T ℓ t (by have := Finset.mem_range.1 ht; omega)

/-! ### Doubling EXP3 -/

section Doubling

variable [NeZero n]

/-- Epoch `j` runs P0018's EXP3 tuned for horizon `2^j`. -/
noncomputable def dblE (n : ℕ) [NeZero n] (j : ℕ) : Machine n := Pool.P0018.exp3M n (2 ^ j)

/-- The constant of the per-epoch bound `C √(2^j)`. -/
noncomputable def dblC (n : ℕ) : ℝ :=
  3 / 2 * Real.sqrt (2 * ((1 + Real.log n) * (2 * n + 1))) + 1 / 2

omit [NeZero n] in
lemma dblC_nonneg : 0 ≤ dblC n := by unfold dblC; positivity

lemma dbl_epoch_le (j : ℕ) (ℓ : LossSeq n) (m : ℕ) (hm : m ≤ 2 ^ j) :
    regret (dblE n j) ℓ m ≤ dblC n * Real.sqrt (2 ^ j) := by
  refine (Pool.P0067.exp3M_regret_prefix_sqrt (n := n) (T := 2 ^ j) ℓ hm).trans ?_
  have hlog : 0 ≤ Real.log n :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n))
  have h2j : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hs1 : 1 ≤ Real.sqrt (2 ^ j) := by rw [Real.one_le_sqrt]; exact h2j
  have key : Real.sqrt ((1 + Real.log n) * ((2 * n + 1) * (((2 ^ j : ℕ) : ℝ) + 1))) ≤
      Real.sqrt (2 * ((1 + Real.log n) * (2 * n + 1))) * Real.sqrt (2 ^ j) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    push_cast
    have hA : 0 ≤ (1 + Real.log n) * (2 * n + 1) := by positivity
    nlinarith
  unfold dblC
  nlinarith

/-- `start` for the doubling lengths: epoch `j` starts at round `2^j - 1`. -/
lemma start_pow (j : ℕ) : start (fun i => 2 ^ i) 0 j + 1 = 2 ^ j := by
  induction j with
  | zero => simp [start]
  | succ j ih =>
    simp only [start, Finset.sum_range_succ, zero_add] at ih ⊢
    rw [pow_succ]; omega

/-- Geometric sum: `Σ_{j ≤ J} √(2^j) ≤ (2 + √2) √(2^J)`. -/
lemma sum_sqrt_pow_le (J : ℕ) :
    ∑ j ∈ Finset.range (J + 1), Real.sqrt (2 ^ j) ≤ (2 + Real.sqrt 2) * Real.sqrt (2 ^ J) := by
  induction J with
  | zero => simp; nlinarith [Real.sqrt_nonneg 2]
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have e : Real.sqrt (2 ^ (J + 1)) = Real.sqrt 2 * Real.sqrt (2 ^ J) := by
      rw [pow_succ, mul_comm, Real.sqrt_mul (by norm_num)]
    rw [e]
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hs : 0 ≤ Real.sqrt (2 ^ J) := Real.sqrt_nonneg _
    nlinarith [Real.sqrt_nonneg 2]

lemma sum_dbl_le (r m : ℕ) :
    ∑ j ∈ Finset.range (r + 1),
        (if start (fun i => 2 ^ i) 0 j < m then dblC n * Real.sqrt (2 ^ j) else 0) ≤
      (2 + Real.sqrt 2) * dblC n * Real.sqrt m := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp
  set J := Nat.log 2 m
  have hJ : (2 : ℝ) ^ J ≤ m := by exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
  have hterm : ∀ j ∈ Finset.range (r + 1),
      (if start (fun i => 2 ^ i) 0 j < m then dblC n * Real.sqrt (2 ^ j) else 0) ≤
        if j ∈ Finset.range (J + 1) then dblC n * Real.sqrt (2 ^ j) else 0 := by
    intro j _
    split_ifs with h1 h2
    · exact le_rfl
    · exfalso; apply h2
      have := start_pow j
      have hjm : 2 ^ j ≤ m := by omega
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.le_log_of_pow_le (by norm_num) hjm
    · exact mul_nonneg dblC_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter]
  have hsub : (Finset.range (r + 1)).filter (fun j => j ∈ Finset.range (J + 1)) ⊆
      Finset.range (J + 1) := fun j hj => (Finset.mem_filter.1 hj).2
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
    mul_nonneg dblC_nonneg (Real.sqrt_nonneg _)).trans ?_
  rw [← Finset.mul_sum]
  have h1 := sum_sqrt_pow_le J
  have h2 : Real.sqrt (2 ^ J) ≤ Real.sqrt m := Real.sqrt_le_sqrt hJ
  have hC := dblC_nonneg (n := n)
  have h3 : (2 + Real.sqrt 2) * Real.sqrt (2 ^ J) ≤ (2 + Real.sqrt 2) * Real.sqrt m :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  calc dblC n * ∑ j ∈ Finset.range (J + 1), Real.sqrt (2 ^ j)
      ≤ dblC n * ((2 + Real.sqrt 2) * Real.sqrt m) :=
        mul_le_mul_of_nonneg_left (h1.trans h3) hC
    _ = _ := by ring

/-- The anytime EXP3 machine for horizons up to `T`: doubling epochs, with a clock (homogeneous). -/
noncomputable def anytimeExp3 (n : ℕ) [NeZero n] (T : ℕ) : Machine n :=
  (chain (dblE n) (fun i => 2 ^ i) (Nat.log 2 T) 0).withClock T

lemma anytimeExp3_isHomogeneous (T : ℕ) : (anytimeExp3 n T).IsHomogeneous :=
  Machine.withClock_isHomogeneous _ _

/-- **Anytime regret**: for every loss sequence and every `m ≤ T`,
`regret ≤ (2 + √2) C √m` with `C = (3/2) √(2 (1 + log n)(2n + 1)) + 1/2`. -/
theorem anytimeExp3_regret_le (T : ℕ) (ℓ : LossSeq n) (m : ℕ) (hm : m ≤ T) :
    regret (anytimeExp3 n T) ℓ m ≤ (2 + Real.sqrt 2) * dblC n * Real.sqrt m := by
  unfold anytimeExp3
  rw [regret_withClock_of_le _ _ _ _ (by omega)]
  have hcov : m ≤ start (fun i => 2 ^ i) 0 (Nat.log 2 T + 1) := by
    have h1 := start_pow (Nat.log 2 T + 1)
    have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) T
    omega
  refine (regret_chain_le (dblE n) (fun i => 2 ^ i) (fun j => dblC n * Real.sqrt (2 ^ j))
    (fun j => mul_nonneg dblC_nonneg (Real.sqrt_nonneg _))
    (fun j ℓ m hm => by simpa using dbl_epoch_le j ℓ m hm) (Nat.log 2 T) 0 ℓ m hcov).trans ?_
  simpa using sum_dbl_le (n := n) (Nat.log 2 T) m


lemma card_chain (E : ℕ → Machine n) (len : ℕ → ℕ) :
    ∀ r k, Fintype.card (chain E len r k).State =
      ∑ j ∈ Finset.range (r + 1), Fintype.card (E (k + j)).State := by
  intro r
  induction r with
  | zero => intro k; rw [zero_add, Finset.sum_range_one, add_zero]; rfl
  | succ r ih =>
    intro k
    rw [show chain E len (r + 1) k = seq (E k) (chain E len r (k + 1)) (len k) from rfl,
      card_seq, ih, Finset.sum_range_succ' _ (r + 1)]
    simp only [add_zero, Nat.add_assoc, Nat.add_comm 1]
    ring

lemma card_dblE (j : ℕ) :
    Fintype.card (dblE n j).State = (Pool.P0018.Kcap n (2 ^ j) + 1) ^ n := by
  change Fintype.card (Pool.P0018.St n (Pool.P0018.Kcap n (2 ^ j))) = _
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

omit [NeZero n] in
lemma Kcap_mono {a b : ℕ} (h : a ≤ b) : Pool.P0018.Kcap n a ≤ Pool.P0018.Kcap n b := by
  unfold Pool.P0018.Kcap Pool.P0018.Dinc
  exact Nat.mul_le_mul h (by have := Nat.mul_le_mul_left n (show 2 * a + 2 ≤ 2 * b + 2 by omega); omega)

/-- **Memory**: `n · log₂ (Kcap n T + 1) + 2 log₂ (T + 1)` bits, i.e. the memory of P0018's
EXP3 for horizon `T` plus `O(log T)` bits. -/
theorem anytimeExp3_memBits_le (T : ℕ) (hT : 1 ≤ T) :
    (anytimeExp3 n T).memBits ≤
      n * Real.logb 2 (Pool.P0018.Kcap n T + 1) + 2 * Real.logb 2 (T + 1) := by
  set r := Nat.log 2 T
  have hcard : Fintype.card (chain (dblE n) (fun i => 2 ^ i) r 0).State ≤
      (r + 1) * (Pool.P0018.Kcap n T + 1) ^ n := by
    rw [card_chain]
    calc ∑ j ∈ Finset.range (r + 1), Fintype.card (dblE n (0 + j)).State
        ≤ ∑ _j ∈ Finset.range (r + 1), (Pool.P0018.Kcap n T + 1) ^ n := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [zero_add, card_dblE]
          have hj' : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          have : 2 ^ j ≤ T := le_trans (Nat.pow_le_pow_right (by norm_num) hj')
            (Nat.pow_log_le_self 2 (by omega))
          exact Nat.pow_le_pow_left (by have := Kcap_mono (n := n) this; omega) n
      _ = (r + 1) * (Pool.P0018.Kcap n T + 1) ^ n := by simp
  have hr : r + 1 ≤ T + 1 := by have := Nat.log_le_self 2 T; omega
  have hpos : 0 < Fintype.card (chain (dblE n) (fun i => 2 ^ i) r 0).State := by
    have : Nonempty (chain (dblE n) (fun i => 2 ^ i) r 0).State := by
      obtain ⟨s, -⟩ := (chain (dblE n) (fun i => 2 ^ i) r 0).init.support_nonempty
      exact ⟨s⟩
    exact Fintype.card_pos
  unfold anytimeExp3
  rw [Machine.memBits_withClock, Machine.memBits]
  have hK : (0 : ℝ) < (Pool.P0018.Kcap n T : ℝ) + 1 := by positivity
  have hlog : Real.logb 2 (Fintype.card (chain (dblE n) (fun i => 2 ^ i) r 0).State) ≤
      Real.logb 2 ((T : ℝ) + 1) + n * Real.logb 2 ((Pool.P0018.Kcap n T : ℝ) + 1) := by
    rw [← Real.logb_pow, ← Real.logb_mul (by positivity) (by positivity)]
    apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos)
    have h1 : ((Fintype.card (chain (dblE n) (fun i => 2 ^ i) r 0).State : ℕ) : ℝ) ≤
        ((r + 1) * (Pool.P0018.Kcap n T + 1) ^ n : ℕ) := by exact_mod_cast hcard
    push_cast at h1
    have h2 : ((r : ℝ) + 1) ≤ (T : ℝ) + 1 := by exact_mod_cast hr
    calc _ ≤ ((r : ℝ) + 1) * ((Pool.P0018.Kcap n T : ℝ) + 1) ^ n := h1
      _ ≤ ((T : ℝ) + 1) * ((Pool.P0018.Kcap n T : ℝ) + 1) ^ n :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
  linarith

/-- **Use with P0055's subsampled play**: the subsampled anytime EXP3 has regret
`≤ (2 + √2) C √(T / γ)`. -/
theorem regret_Sub_anytimeExp3_le (T : ℕ) {γ : ℝ} (hγ : 0 < γ) (h1 : γ ≤ 1) (ℓ : LossSeq n) :
    regret (Pool.P0055.Sub (anytimeExp3 n T) γ hγ.le h1) ℓ T ≤
      (2 + Real.sqrt 2) * dblC n * Real.sqrt (T / γ) :=
  Pool.P0055.regret_Sub_le_sqrt (anytimeExp3 n T) (anytimeExp3_isHomogeneous T) hγ h1 ℓ T
    (by have := dblC_nonneg (n := n); positivity)
    (fun ℓ' m hm => anytimeExp3_regret_le T ℓ' m hm)

end Doubling

end Pool.P0069
