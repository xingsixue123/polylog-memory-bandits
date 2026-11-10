import Pool.P0015.Block

/-!
# K-query algorithms with action-oblivious updates, driven by fresh coins (bridge to `QMachine`)

A complement to P0051 (whose `CoinProc` draws the action from a coin with a **fixed** per-round law `μA t`, so a
state-dependent play law such as Hedge over the current pool can only be approximated by discretization). Here the
play law is an arbitrary state-dependent PMF, at the price of an **action-oblivious** update. This is the class of
Peng–Rubinstein-type pool learners in the `K`-query setting of P0015 / P0045 §2:
* on day `t` in state `s` the queried arms `query t s : Fin K → Fin n` are a function of the state;
* the played arm is drawn from a state-dependent law `play t s : PMF (Fin n)` (real probabilities allowed, e.g. Hedge
  over the pool; nothing about it is stored);
* the next state `upd t s bits z` depends only on the state, the `K` queried loss bits and a fresh update coin
  `z ∼ ν` (e.g. sampling and filter bits). It does **not** read the played arm or its loss.

`QCoinAlg.toQ` is the corresponding `Pool.P0015.QMachine` (state set `S`, so memory `log₂ |S|`, `memBits_toQ`).
Because the update ignores the played arm, the state process is the deterministic run `runFin` driven by the update
coins alone:
* `E_stateDist`: the expectation of any function of the state under `stateDist` at day `t` is the coin-weighted average
  `Σ_ω W ω · f (runFin ℓ t ω)` over update-coin sequences `ω : Fin t → Z`, `W ω = Π_j ν(ω j)` (`sum_W`: total mass 1);
* `expLoss_eq`: the expected loss on day `t` is the coin-weighted expected loss of `play t` at the realized state;
* `regret_eq`: the regret is the coin-weighted sum of these expected losses minus the best arm's loss.
So regret analyses can argue pathwise on deterministic runs with explicit coins (e.g. compare a run with and without a
passive copy, P0052 `pools_erase_of_passive`), with the played arm averaged out by its law.
-/

open Finset Pool.P0001 Pool.P0015
open scoped ENNReal

namespace Pool.P0064

/-- A `K`-query algorithm whose queries are a function of the state, whose played arm is drawn from a
state-dependent law, and whose update reads only the queried bits and a fresh update coin. -/
structure QCoinAlg (n K : ℕ) where
  S : Type
  [fS : Fintype S]
  [dS : DecidableEq S]
  Z : Type
  [fZ : Fintype Z]
  ν : PMF Z
  s0 : S
  play : ℕ → S → PMF (Fin n)
  query : ℕ → S → Fin K → Fin n
  upd : ℕ → S → (Fin K → Bool) → Z → S

attribute [scoped instance] QCoinAlg.fS QCoinAlg.dS QCoinAlg.fZ

variable {n K : ℕ} (A : QCoinAlg n K)

/-- The `K`-query machine of `A`. -/
noncomputable def QCoinAlg.toQ : QMachine n K where
  State := A.S
  init := PMF.pure A.s0
  act t s := (A.play t s).map fun i => (i, A.query t s)
  next t s _ o := A.ν.map fun z => A.upd t s o.2 z

/-- The queried bits in state `s` on day `t`. -/
def QCoinAlg.bits (ℓ : LossSeq n) (t : ℕ) (s : A.S) : Fin K → Bool := fun k => ℓ t (A.query t s k)

/-- Realized state on day `t` from the update coins of days `< t`. -/
def QCoinAlg.runFin (ℓ : LossSeq n) : (t : ℕ) → (Fin t → A.Z) → A.S
  | 0, _ => A.s0
  | t + 1, ω => A.upd t (QCoinAlg.runFin ℓ t (Fin.init ω))
      (A.bits ℓ t (QCoinAlg.runFin ℓ t (Fin.init ω))) (ω (Fin.last t))

/-- Weight of a coin sequence. -/
noncomputable def QCoinAlg.W {t : ℕ} (ω : Fin t → A.Z) : ℝ := ∏ j, (A.ν (ω j)).toReal

theorem E_map' {α β : Type} [Fintype α] [Fintype β] (μ : PMF α) (g : α → β) (f : β → ℝ) :
    E (μ.map g) f = E μ (fun a => f (g a)) := by
  classical
  exact E_map μ g f

theorem E_pure' {α : Type} [Fintype α] (a : α) (f : α → ℝ) : E (PMF.pure a) f = f a := by
  classical
  exact E_pure a f

theorem sum_split {X : Type} [Fintype X] {t : ℕ} (f : (Fin (t + 1) → X) → ℝ) :
    ∑ ω, f ω = ∑ x : X, ∑ ω' : Fin t → X, f (Fin.snoc ω' x) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv fun _ => X) _ _ (fun q => rfl)).symm

theorem W_snoc {t : ℕ} (ω : Fin t → A.Z) (z : A.Z) :
    A.W (Fin.snoc ω z) = A.W ω * (A.ν z).toReal := by
  unfold QCoinAlg.W; rw [Fin.prod_univ_castSucc]; simp

theorem sum_W (t : ℕ) : ∑ ω : Fin t → A.Z, A.W ω = 1 := by
  induction t with
  | zero => simp [QCoinAlg.W]
  | succ t ih =>
    rw [sum_split]
    simp only [W_snoc, ← Finset.sum_mul, ih, one_mul]
    exact sum_toReal A.ν

/-- **State law = coin-weighted realized run.** -/
theorem E_stateDist (ℓ : LossSeq n) : ∀ (t : ℕ) (f : A.toQ.State → ℝ),
    E (A.toQ.stateDist ℓ t) f = ∑ ω : Fin t → A.Z, A.W ω * f (A.runFin ℓ t ω) := by
  intro t
  induction t with
  | zero =>
    intro f
    refine (E_pure' (α := A.toQ.State) A.s0 f).trans ?_
    simp [QCoinAlg.W, QCoinAlg.runFin]
  | succ t ih =>
    intro f
    show E ((A.toQ.stateDist ℓ t).bind fun s => (A.toQ.act t s).bind fun a =>
      A.toQ.next t s a (qobs a (ℓ t))) f = _
    rw [E_bind]
    have hstep : ∀ s : A.toQ.State, E ((A.toQ.act t s).bind fun a => A.toQ.next t s a (qobs a (ℓ t))) f =
        ∑ z, (A.ν z).toReal * f (A.upd t s (A.bits ℓ t s) z) := by
      intro s
      rw [E_bind]
      show E ((A.play t s).map fun i => (i, A.query t s))
        (fun a => E (A.ν.map fun z => A.upd t s (qobs a (ℓ t)).2 z) f) = _
      rw [E_map' (β := QAct n K)]
      simp only [qobs]
      rw [E_const]
      exact E_map' (α := A.Z) (β := A.toQ.State) A.ν _ f
    simp only [hstep]
    rw [ih, sum_split]
    simp only [W_snoc, QCoinAlg.runFin, Fin.init_snoc, Fin.snoc_last]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => by ring

/-- **Expected loss** on day `t`: coin-weighted expected loss of the play law at the realized state. -/
theorem expLoss_eq (ℓ : LossSeq n) (t : ℕ) :
    A.toQ.expLoss ℓ t =
      ∑ ω : Fin t → A.Z, A.W ω * E (A.play t (A.runFin ℓ t ω)) (fun i => ((ℓ t i).toNat : ℝ)) := by
  rw [QMachine.expLoss_eq, E_stateDist]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  exact E_map' (β := QAct n K) _ _ _

/-- Memory of the machine: `log₂ |S|`. -/
theorem memBits_toQ : A.toQ.memBits = Real.logb 2 (Fintype.card A.S) := rfl

/-- **Regret** as a coin-weighted sum of the play laws' expected losses at the realized states. -/
theorem regret_eq (ℓ : LossSeq n) (T : ℕ) :
    A.toQ.regret ℓ T = ∑ t ∈ range T, ∑ ω : Fin t → A.Z,
      A.W ω * E (A.play t (A.runFin ℓ t ω)) (fun i => ((ℓ t i).toNat : ℝ)) - bestLoss ℓ T := by
  unfold QMachine.regret
  simp only [expLoss_eq]

end Pool.P0064
