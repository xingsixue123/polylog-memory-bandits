import Pool.Prelude

/-!
# The single-query bandit model with bounded memory

The model of the problem: `n` arms, an oblivious adversary that fixes the losses
`ℓ t i ∈ {0, 1}` in advance, one pull per round, and only the pulled arm's loss is observed.
An algorithm is a randomized finite state machine:

* at the start of round `t` it is in a state `s` (the only information kept between rounds);
* it draws the arm `a` from `act t s` (fresh coins);
* it observes the bit `ℓ t a` and moves to a state drawn from `next t s a (ℓ t a)` (fresh coins).

Coins are fresh in every round and cost nothing; whatever persists is in the state, so the memory
of the machine is `log₂` of the number of states (`Machine.memBits`).
Since the adversary is oblivious, the loss sequence is a fixed function and the law of the state
at round `t` is given exactly by the forward recursion `Machine.stateDist` (the state process is a
Markov chain whose kernel at round `t` is `s ↦ (act t s).bind (fun a ↦ next t s a (ℓ t a))`).

The transition kernels may depend on the round `t` (a free clock). `Machine.IsHomogeneous` singles
out machines that do not use the round number; `Machine.withClock` turns any machine into a
homogeneous one with the same behaviour on rounds `t ≤ T`, at the cost of a factor `T + 1` in the
number of states (`Machine.card_withClock`), i.e. `log₂ (T + 1)` bits.

## Main definitions

* `LossSeq n`: an oblivious loss sequence, `ℕ → Fin n → Bool` (`true` = loss `1`).
* `Machine n`: a randomized state machine with a finite state type.
* `Machine.stateDist`, `Machine.armDist`, `Machine.expLoss`: the law of the state and of the
  pulled arm at round `t`, and the expected loss at round `t`.
* `Machine.memBits`: `log₂ |State|`.
* `cumLoss ℓ T i`, `bestLoss ℓ T`: the loss of arm `i` over the rounds `0, …, T-1` and the
  smallest of these losses.
* `regret M ℓ T`: expected loss of `M` over rounds `0, …, T-1` minus `bestLoss ℓ T`.
-/

open scoped ENNReal

namespace Pool.P0001

/-- An oblivious loss sequence on `n` arms: `ℓ t i = true` means that arm `i` has loss `1` at
round `t` (rounds are numbered `0, 1, 2, …`; with horizon `T` only the rounds `t < T` count). -/
abbrev LossSeq (n : ℕ) := ℕ → Fin n → Bool

/-- A randomized state machine playing the single-query bandit game on `n` arms.
`init` is the law of the initial state; in state `s` at round `t` the machine pulls an arm drawn
from `act t s`; after observing the loss bit `b` of the pulled arm `a`, its next state is drawn
from `next t s a b`. Fresh randomness is used in every draw. -/
structure Machine (n : ℕ) where
  /-- The states of the machine: everything that is kept from one round to the next. -/
  State : Type
  /-- The state set is finite. -/
  [fintypeState : Fintype State]
  /-- Law of the initial state. -/
  init : PMF State
  /-- Law of the arm pulled at round `t` in state `s`. -/
  act : ℕ → State → PMF (Fin n)
  /-- Law of the next state, given the round, the state, the pulled arm and its observed loss. -/
  next : ℕ → State → Fin n → Bool → PMF State

attribute [scoped instance] Machine.fintypeState

namespace Machine

/-- Law of the state of `M` at the start of round `t` against the loss sequence `ℓ`. -/
noncomputable def stateDist {n : ℕ} (M : Machine n) (ℓ : LossSeq n) : ℕ → PMF M.State
  | 0 => M.init
  | t + 1 => (M.stateDist ℓ t).bind fun s => (M.act t s).bind fun a => M.next t s a (ℓ t a)

/-- Law of the arm pulled by `M` at round `t` against the loss sequence `ℓ`. -/
noncomputable def armDist {n : ℕ} (M : Machine n) (ℓ : LossSeq n) (t : ℕ) : PMF (Fin n) :=
  (M.stateDist ℓ t).bind (M.act t)

/-- Expected loss of `M` at round `t` against the loss sequence `ℓ`. -/
noncomputable def expLoss {n : ℕ} (M : Machine n) (ℓ : LossSeq n) (t : ℕ) : ℝ :=
  ∑ a, (M.armDist ℓ t a).toReal * ((ℓ t a).toNat : ℝ)

/-- Memory of `M` in bits: `log₂` of the number of states. -/
noncomputable def memBits {n : ℕ} (M : Machine n) : ℝ := Real.logb 2 (Fintype.card M.State)

/-- `M` does not use the round number: its kernels at every round are those of round `0`. -/
def IsHomogeneous {n : ℕ} (M : Machine n) : Prop :=
  (∀ t s, M.act t s = M.act 0 s) ∧ (∀ t s a b, M.next t s a b = M.next 0 s a b)

/-- Successor on `Fin (T + 1)`, saturating at `T`. -/
def clockSucc {T : ℕ} (c : Fin (T + 1)) : Fin (T + 1) :=
  if h : c.val + 1 ≤ T then ⟨c.val + 1, by omega⟩ else c

/-- The machine `M` with its round number stored in the state (saturating at `T`): a homogeneous
machine that behaves like `M` on the rounds `t ≤ T`. -/
noncomputable def withClock {n : ℕ} (M : Machine n) (T : ℕ) : Machine n where
  State := M.State × Fin (T + 1)
  init := M.init.map fun s => (s, 0)
  act _ p := M.act p.2 p.1
  next _ p a b := (M.next p.2 p.1 a b).map fun s => (s, clockSucc p.2)

lemma withClock_isHomogeneous {n : ℕ} (M : Machine n) (T : ℕ) :
    (M.withClock T).IsHomogeneous :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

lemma withClock_stateDist {n : ℕ} (M : Machine n) (T : ℕ) (ℓ : LossSeq n) :
    ∀ t (ht : t ≤ T), (M.withClock T).stateDist ℓ t =
      (M.stateDist ℓ t).map fun s => (s, (⟨t, by omega⟩ : Fin (T + 1))) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    simp only [stateDist]
    rw [ih (by omega)]
    have hc : clockSucc (⟨t, by omega⟩ : Fin (T + 1)) = ⟨t + 1, by omega⟩ := by
      simp [clockSucc, show t + 1 ≤ T by omega]
    simp only [withClock, PMF.bind_map, PMF.map_bind, Function.comp_def, hc]

lemma withClock_armDist {n : ℕ} (M : Machine n) (T : ℕ) (ℓ : LossSeq n) (t : ℕ) (ht : t ≤ T) :
    (M.withClock T).armDist ℓ t = M.armDist ℓ t := by
  rw [armDist, withClock_stateDist M T ℓ t ht]
  simp only [withClock, PMF.bind_map, Function.comp_def]
  rfl

lemma withClock_expLoss {n : ℕ} (M : Machine n) (T : ℕ) (ℓ : LossSeq n) (t : ℕ) (ht : t ≤ T) :
    (M.withClock T).expLoss ℓ t = M.expLoss ℓ t := by
  simp only [expLoss, withClock_armDist M T ℓ t ht]

lemma card_withClock {n : ℕ} (M : Machine n) (T : ℕ) :
    Fintype.card (M.withClock T).State = Fintype.card M.State * (T + 1) :=
  (Fintype.card_prod M.State (Fin (T + 1))).trans (by rw [Fintype.card_fin])

lemma memBits_withClock {n : ℕ} (M : Machine n) (T : ℕ) :
    (M.withClock T).memBits = M.memBits + Real.logb 2 (T + 1) := by
  have h1 : (0 : ℝ) < Fintype.card M.State := by
    have : Nonempty M.State := by
      obtain ⟨s, -⟩ := M.init.support_nonempty
      exact ⟨s⟩
    exact_mod_cast Fintype.card_pos
  rw [memBits, memBits, card_withClock, Nat.cast_mul, Real.logb_mul h1.ne' (by positivity)]
  push_cast
  ring

lemma expLoss_nonneg {n : ℕ} (M : Machine n) (ℓ : LossSeq n) (t : ℕ) : 0 ≤ M.expLoss ℓ t :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (by positivity)

lemma expLoss_le_one {n : ℕ} (M : Machine n) (ℓ : LossSeq n) (t : ℕ) : M.expLoss ℓ t ≤ 1 := by
  calc M.expLoss ℓ t ≤ ∑ a, (M.armDist ℓ t a).toReal := by
        refine Finset.sum_le_sum fun a _ => ?_
        have : ((ℓ t a).toNat : ℝ) ≤ 1 := by cases ℓ t a <;> simp
        exact mul_le_of_le_one_right ENNReal.toReal_nonneg this
    _ = 1 := by
        rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top _ a)]
        rw [← tsum_fintype (L := .unconditional _) (fun a => M.armDist ℓ t a), PMF.tsum_coe, ENNReal.toReal_one]

end Machine

/-- Loss of arm `i` over the rounds `0, …, T - 1`. -/
def cumLoss {n : ℕ} (ℓ : LossSeq n) (T : ℕ) (i : Fin n) : ℝ :=
  ∑ t ∈ Finset.range T, ((ℓ t i).toNat : ℝ)

/-- Loss of the best single arm in hindsight over the rounds `0, …, T - 1`. -/
noncomputable def bestLoss {n : ℕ} (ℓ : LossSeq n) (T : ℕ) : ℝ := ⨅ i, cumLoss ℓ T i

/-- Expected regret of `M` against the oblivious loss sequence `ℓ` over the rounds
`0, …, T - 1`. -/
noncomputable def regret {n : ℕ} (M : Machine n) (ℓ : LossSeq n) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, M.expLoss ℓ t - bestLoss ℓ T

lemma cumLoss_nonneg {n : ℕ} (ℓ : LossSeq n) (T : ℕ) (i : Fin n) : 0 ≤ cumLoss ℓ T i :=
  Finset.sum_nonneg fun _ _ => by positivity

lemma bestLoss_le_cumLoss {n : ℕ} (ℓ : LossSeq n) (T : ℕ) (i : Fin n) :
    bestLoss ℓ T ≤ cumLoss ℓ T i :=
  ciInf_le (Set.finite_range _).bddBelow i

lemma exists_bestLoss_eq {n : ℕ} [NeZero n] (ℓ : LossSeq n) (T : ℕ) :
    ∃ i, bestLoss ℓ T = cumLoss ℓ T i := by
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => cumLoss ℓ T i)
  exact ⟨i, hi.symm⟩

lemma bestLoss_nonneg {n : ℕ} (ℓ : LossSeq n) (T : ℕ) : 0 ≤ bestLoss ℓ T :=
  Real.iInf_nonneg fun i => cumLoss_nonneg ℓ T i

lemma regret_le {n : ℕ} (M : Machine n) (ℓ : LossSeq n) (T : ℕ) : regret M ℓ T ≤ T := by
  have h : ∑ t ∈ Finset.range T, M.expLoss ℓ t ≤ T := by
    calc ∑ t ∈ Finset.range T, M.expLoss ℓ t ≤ ∑ _t ∈ Finset.range T, (1 : ℝ) :=
          Finset.sum_le_sum fun t _ => M.expLoss_le_one ℓ t
      _ = T := by simp
  have := bestLoss_nonneg ℓ T
  rw [regret]
  linarith

lemma regret_withClock {n : ℕ} (M : Machine n) (T : ℕ) (ℓ : LossSeq n) :
    regret (M.withClock T) ℓ T = regret M ℓ T := by
  rw [regret, regret]
  congr 1
  exact Finset.sum_congr rfl fun t ht =>
    M.withClock_expLoss T ℓ t (Finset.mem_range.1 ht).le

end Pool.P0001
