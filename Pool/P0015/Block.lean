import Pool.P0015.Expect
/-!
# `K`-query machines and the block machine

* `QMachine n K`: a randomized finite state machine for the `K`-query game on `n` arms. Each day,
  before seeing the day's losses, it draws an action `(i, Q) : Fin n × (Fin K → Fin n)` from its
  state (fresh coins); it incurs the loss of the played arm `i`, observes the loss bits of `i` and
  of the `K` queried arms `Q k` (free observations), and moves to a new state (fresh coins).
  Same conventions as P0001's `Machine` (PMF kernels, may depend on the day number, memory
  `log₂ |State|`, regret against the best arm in hindsight).
* `blockMachine hB hB0 A` (for `n ≤ B`, `0 < B`): a P0001 single-query machine that simulates `A`,
  one day of `A` per block of `B` rounds. At the start of every block it draws a fresh offset
  `u` uniform in `Fin B`; arm `i` gets the position `pos i u = i + u mod B` of the block (distinct
  arms get distinct positions since `n ≤ B`). In the block it pulls each queried arm at its
  position and the played arm at every other round; at the end of the block it feeds `A` the
  loss bits read at the positions of the played and queried arms, i.e. the coordinates of the
  *virtual loss vector* `virt ℓ b u i = ℓ (b * B + pos i u) i`.
* `stateDist_blockMachine`: the exact law of the state of the block machine at every round, in
  terms of `avgA`, the law of the state of `A` driven by the virtual vectors with fresh offsets.
-/

open scoped ENNReal

namespace Pool.P0015

open Pool.P0001

/-- A day's action of a `K`-query machine: the played arm and `K` arms observed for free. -/
abbrev QAct (n K : ℕ) := Fin n × (Fin K → Fin n)

/-- A day's observation: the loss bit of the played arm and of each queried arm. -/
abbrev QObs (K : ℕ) := Bool × (Fin K → Bool)

/-- What a `K`-query machine observes when it takes action `a` against the loss vector `v`. -/
def qobs {n K : ℕ} (a : QAct n K) (v : Fin n → Bool) : QObs K := (v a.1, fun k => v (a.2 k))

/-- A randomized state machine for the `K`-query game: every day it chooses, before seeing the
day's losses, an arm to play and `K` arms to observe for free; it incurs the loss of the played
arm and observes the loss bits of the played arm and of the `K` queried arms. -/
structure QMachine (n K : ℕ) where
  /-- The states: everything kept from one day to the next. -/
  State : Type
  /-- The state set is finite. -/
  [fintypeState : Fintype State]
  /-- Law of the initial state. -/
  init : PMF State
  /-- Law of the action (played arm, queried arms) on day `t` in state `s`. -/
  act : ℕ → State → PMF (QAct n K)
  /-- Law of the next state given the day, the state, the action and the observed bits. -/
  next : ℕ → State → QAct n K → QObs K → PMF State

attribute [scoped instance] QMachine.fintypeState

namespace QMachine

variable {n K : ℕ}

/-- Law of the state of `A` at the start of day `t` against the loss sequence `ℓ`. -/
noncomputable def stateDist (A : QMachine n K) (ℓ : LossSeq n) : ℕ → PMF A.State
  | 0 => A.init
  | t + 1 => (A.stateDist ℓ t).bind fun s => (A.act t s).bind fun a => A.next t s a (qobs a (ℓ t))

/-- Law of the arm played by `A` on day `t` (the queried arms are not played). -/
noncomputable def armDist (A : QMachine n K) (ℓ : LossSeq n) (t : ℕ) : PMF (Fin n) :=
  ((A.stateDist ℓ t).bind (A.act t)).map Prod.fst

/-- Expected loss of `A` on day `t`: only the played arm's loss counts. -/
noncomputable def expLoss (A : QMachine n K) (ℓ : LossSeq n) (t : ℕ) : ℝ :=
  ∑ a, (A.armDist ℓ t a).toReal * ((ℓ t a).toNat : ℝ)

/-- Memory of `A` in bits: `log₂ |State|`. -/
noncomputable def memBits (A : QMachine n K) : ℝ := Real.logb 2 (Fintype.card A.State)

/-- Expected regret of `A` over days `0, …, T - 1` against the best single arm (P0001's
`bestLoss`). -/
noncomputable def regret (A : QMachine n K) (ℓ : LossSeq n) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, A.expLoss ℓ t - bestLoss ℓ T

lemma expLoss_eq (A : QMachine n K) (ℓ : LossSeq n) (t : ℕ) :
    A.expLoss ℓ t = E (A.stateDist ℓ t) (fun s => E (A.act t s) (fun a => ((ℓ t a.1).toNat : ℝ))) := by
  change E (A.armDist ℓ t) _ = _
  rw [armDist, E_map, E_bind]

lemma stateDist_congr (A : QMachine n K) {ℓ₁ ℓ₂ : LossSeq n} :
    ∀ b, (∀ t < b, ℓ₁ t = ℓ₂ t) → A.stateDist ℓ₁ b = A.stateDist ℓ₂ b
  | 0, _ => rfl
  | b + 1, h => by
    simp only [stateDist]
    rw [stateDist_congr A b (fun t ht => h t (by omega)), h b (by omega)]

end QMachine

/-! ## The block machine -/

section Block

variable {n K B : ℕ} (hB : n ≤ B)

/-- Position of arm `i` in a block with offset `u`. -/
def pos (i : Fin n) (u : Fin B) : Fin B := Fin.castLE hB i + u

/-- The arms of an action: index `0` is the played arm, index `k+1` the `k`-th query. -/
def armOf (a : QAct n K) : Fin (K + 1) → Fin n := Fin.cons a.1 a.2

open Classical in
/-- The arm pulled at position `p` of a block with action `a` and offset `u`: the queried arm
whose position is `p` if there is one, otherwise the played arm. -/
noncomputable def pulled (a : QAct n K) (u p : Fin B) : Fin n :=
  if h : (p - u).val < n then
    if ∃ k, a.2 k = (⟨(p - u).val, h⟩ : Fin n) then ⟨(p - u).val, h⟩ else a.1
  else a.1

/-- The virtual loss vector of block `b` with offset `u`. -/
def virt (ℓ : LossSeq n) (b : ℕ) (u : Fin B) : Fin n → Bool :=
  fun i => ℓ (b * B + (pos hB i u).val) i

/-- The bits collected in block `b` before position `p`. -/
def collect (ℓ : LossSeq n) (b : ℕ) (a : QAct n K) (u : Fin B) (p : ℕ) : Fin (K + 1) → Bool :=
  fun j => if (pos hB (armOf a j) u).val < p then ℓ (b * B + (pos hB (armOf a j) u).val) (armOf a j)
    else false

/-- The observation handed to the `K`-query machine. -/
def obsOf (c : Fin (K + 1) → Bool) : QObs K := (c 0, fun k => c k.succ)

lemma pulled_pos (hB0 : 0 < B) (a : QAct n K) (u : Fin B) (j : Fin (K + 1)) :
    pulled a u (pos hB (armOf a j) u) = armOf a j := by
  have : NeZero B := ⟨hB0.ne'⟩
  have hsub : pos hB (armOf a j) u - u = Fin.castLE hB (armOf a j) := by
    simp [pos]
  have hlt : (pos hB (armOf a j) u - u).val < n := by rw [hsub]; simp
  have heq : (⟨(pos hB (armOf a j) u - u).val, hlt⟩ : Fin n) = armOf a j := by
    ext; simp [hsub]
  unfold pulled
  rw [dif_pos hlt]
  split_ifs with hex
  · exact heq
  · induction j using Fin.cases with
    | zero => simp [armOf]
    | succ k => exact absurd ⟨k, by rw [heq]; simp [armOf]⟩ hex

lemma pulled_ne (hB0 : 0 < B) (a : QAct n K) (u p : Fin B) (h : pulled a u p ≠ a.1) :
    ∃ k, pos hB (a.2 k) u = p := by
  have : NeZero B := ⟨hB0.ne'⟩
  unfold pulled at h
  split_ifs at h with h1 h2
  · obtain ⟨k, hk⟩ := h2
    refine ⟨k, ?_⟩
    rw [hk]
    have : Fin.castLE hB (⟨(p - u).val, h1⟩ : Fin n) = p - u := by ext; simp
    simp [pos, this]
  · exact absurd rfl h
  · exact absurd rfl h

end Block

section Machine

variable {n K B : ℕ} (hB : n ≤ B) (hB0 : 0 < B) (A : QMachine n K)

/-- The state of the block machine: the state of `A`, the current action of `A`, the offset
of the current block and the bits collected so far in the block. -/
abbrev BState (A : QMachine n K) (B : ℕ) := A.State × QAct n K × Fin B × (Fin (K + 1) → Bool)

/-- Start a new block (day `b` of `A`) from the state `s` of `A`. -/
noncomputable def fresh (b : ℕ) (s : A.State) : PMF (BState A B) :=
  (A.act b s).bind fun a => (unif B hB0).map fun u => (s, a, u, fun _ => false)

/-- The bit vector after observing `y` at position `p`. -/
def upd (a : QAct n K) (u : Fin B) (p : ℕ) (y : Bool) (c : Fin (K + 1) → Bool) :
    Fin (K + 1) → Bool :=
  fun j => if (pos hB (armOf a j) u).val = p then y else c j

/-- The single-query machine simulating `A`, one day of `A` per block of `B` rounds. -/
noncomputable abbrev blockMachine : Machine n where
  State := BState A B
  init := A.init.bind (fresh hB0 A 0)
  act t st := PMF.pure (pulled st.2.1 st.2.2.1 ⟨t % B, Nat.mod_lt _ hB0⟩)
  next t st _ y :=
    if t % B + 1 < B then PMF.pure (st.1, st.2.1, st.2.2.1, upd hB st.2.1 st.2.2.1 (t % B) y st.2.2.2)
    else (A.next (t / B) st.1 st.2.1 (obsOf (upd hB st.2.1 st.2.2.1 (t % B) y st.2.2.2))).bind
      (fresh hB0 A (t / B + 1))

/-- The law of the state of `A` at the start of block `b`, averaged over the offsets. -/
noncomputable def avgA (ℓ : LossSeq n) : ℕ → PMF A.State
  | 0 => A.init
  | b + 1 => (avgA ℓ b).bind fun s => (A.act b s).bind fun a =>
      (unif B hB0).bind fun u => A.next b s a (qobs a (virt hB ℓ b u))

/-- The claimed law of the block machine at position `p` of block `b`. -/
noncomputable def rep (ℓ : LossSeq n) (b p : ℕ) : PMF (BState A B) :=
  (avgA hB hB0 A ℓ b).bind fun s => (A.act b s).bind fun a =>
    (unif B hB0).map fun u => (s, a, u, collect hB ℓ b a u p)

lemma collect_zero (ℓ : LossSeq n) (b : ℕ) (a : QAct n K) (u : Fin B) :
    collect hB ℓ b a u 0 = fun _ => false := by
  funext j; simp [collect]

lemma obsOf_collect_B (ℓ : LossSeq n) (b : ℕ) (a : QAct n K) (u : Fin B) :
    obsOf (collect hB ℓ b a u B) = qobs a (virt hB ℓ b u) := by
  simp only [obsOf, qobs, collect, Fin.is_lt, if_true, virt]
  refine Prod.ext ?_ ?_
  · simp [armOf]
  · funext k; simp [armOf]

lemma upd_collect (hB0 : 0 < B) (ℓ : LossSeq n) (b r : ℕ) (hr : r < B) (a : QAct n K) (u : Fin B) :
    upd hB a u r (ℓ (b * B + r) (pulled a u ⟨r, hr⟩)) (collect hB ℓ b a u r) =
      collect hB ℓ b a u (r + 1) := by
  funext j
  simp only [upd, collect]
  by_cases hj : (pos hB (armOf a j) u).val = r
  · have hp : (⟨r, hr⟩ : Fin B) = pos hB (armOf a j) u := by ext; exact hj.symm
    rw [if_pos hj, if_pos (by omega), hp, pulled_pos hB hB0, hj]
  · rw [if_neg hj]
    by_cases h2 : (pos hB (armOf a j) u).val < r
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

lemma divmod_aux (q r : ℕ) (hr : r < B) : (q * B + r) / B = q ∧ (q * B + r) % B = r := by
  have hB0 : 0 < B := by omega
  exact (Nat.div_mod_unique hB0).2 ⟨by ring, hr⟩

theorem stateDist_blockMachine (ℓ : LossSeq n) :
    ∀ t, (blockMachine hB hB0 A).stateDist ℓ t = rep hB hB0 A ℓ (t / B) (t % B) := by
  intro t
  induction t with
  | zero =>
    simp only [Nat.zero_div, Nat.zero_mod]
    simp only [Machine.stateDist, blockMachine, rep, avgA, collect_zero]
    rfl
  | succ t ih =>
    obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < B ∧ t = q * B + r :=
      ⟨t / B, t % B, Nat.mod_lt _ hB0, by rw [mul_comm]; exact (Nat.div_add_mod t B).symm⟩
    obtain ⟨hq, hr'⟩ := divmod_aux q r hr
    rw [Machine.stateDist, ih, hq, hr']
    simp only [rep, PMF.bind_bind, PMF.bind_map]
    by_cases hlt : r + 1 < B
    · obtain ⟨hq1, hr1⟩ := divmod_aux q (r + 1) hlt
      rw [show q * B + r + 1 = q * B + (r + 1) by ring, hq1, hr1]
      refine congrArg (fun f => PMF.bind _ f) (funext fun s => ?_)
      refine congrArg (fun f => PMF.bind _ f) (funext fun a => ?_)
      rw [← PMF.bind_pure_comp]
      refine congrArg (fun f => PMF.bind _ f) (funext fun u => ?_)
      simp only [Function.comp_apply, blockMachine, PMF.pure_bind, hr', hq, if_pos hlt]
      rw [upd_collect hB hB0 ℓ q r hr]
    · have hrB : r + 1 = B := by omega
      obtain ⟨hq1, hr1⟩ := divmod_aux (B := B) (q + 1) 0 hB0
      rw [show q * B + r + 1 = (q + 1) * B + 0 by rw [← hrB]; ring, hq1, hr1]
      simp only [avgA, PMF.bind_bind]
      refine congrArg (fun f => PMF.bind _ f) (funext fun s => ?_)
      refine congrArg (fun f => PMF.bind _ f) (funext fun a => ?_)
      refine congrArg (fun f => PMF.bind _ f) (funext fun u => ?_)
      simp only [Function.comp_apply, blockMachine, PMF.pure_bind, hr', hq, if_neg hlt]
      rw [upd_collect hB hB0 ℓ q r hr, hrB, obsOf_collect_B]
      refine congrArg (fun f => PMF.bind _ f) (funext fun s' => ?_)
      simp only [fresh, collect_zero]

end Machine

end Pool.P0015
