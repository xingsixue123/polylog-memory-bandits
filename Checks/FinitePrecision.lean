import Pool.P0294.Statement

/-!
# Finite precision and explicitness: a fair-coin reference model, and the bridge to it

This file has four parts: (1) a reference model of bandit algorithms as fair-coin machines, defined with
Mathlib only; (2) the construction behind `Pool.P0294.main` written down as definitions (`Audit3E.famE`);
(3) a rounding theorem: any family meeting the target of `Pool.P0001` can be rounded to fair coins;
(4) the bridge `Audit3.pool_refModel : Audit3.StrictTarget`.

## Part 1: the reference model

A bandit algorithm for `n` arms and horizon `T` is a *coin machine*:

* a finite state type `S` (memory = `log₂ |S|`, the whole state set, so the bound holds on every
  execution path and every persistent quantity -- clocks, counters, pools, seeds -- must live in `S`);
* a deterministic initial state `init`;
* a number `b` of fresh fair coin flips drawn in every round (finite precision: every probability the
  machine ever realises is a multiple of `2^{-b}`);
* time-homogeneous maps `act : S → coins → arm` and `next : S → coins → observed loss → S`.
  The day index is *not* an input: a machine that needs a clock must store it in `S`.

Drawing the round's coins before the loss is observed is without loss of generality: the adversary is
oblivious, so coins drawn after the observation could be drawn before it.

The expectation is a plain finite average over all `2^{bT}` coin tapes: no measure theory, no reals
inside the machine.

## Readings of the requirements

* **Finite precision.** (F1) Storage: every persistent quantity (weights, estimates, counters, clocks,
  pools, seeds, recursion level) is an element of the finite state set `S`, and `log₂|S|` is the
  memory; no real number is stored. (F2) Randomness: each round's randomisation is a function of
  finitely many (`b`) fresh fair coins, so every transition probability is a dyadic rational with
  denominator `2^b`. Strict reading: `b ≤ C·log(nT)^k`; lenient reading (random bits are
  free): any finite `b`. (F3) No free clock: transitions do not take the day index.
  A machine whose transition laws are arbitrary reals does not literally meet (F2); it meets it only
  after a rounding argument (exact dyadic, or approximate with a bounded regret loss).
* **Explicit.** The algorithm is given by a construction one can write down as pseudocode: state set,
  initial state and per-round update given by definitions (parameters closed-form in `n, T`), not
  selected by choice from an existence proof. Brute-force search over all finite machines is
  computable once existence is known (with dyadic laws everything is finite), so "computable" alone
  is too weak a reading; we require a definitional, uniform construction whose per-round update is
  effectively computable from `(n, T, state, coins, observed loss)`.
-/

namespace Audit3

/-- Reference model of a bandit algorithm with finite state, finite fresh randomness per round,
and time-homogeneous transitions. -/
structure CoinMachine (n : ℕ) where
  S : Type
  [instFin : Fintype S]
  b : ℕ
  init : S
  act : S → (Fin b → Bool) → Fin n
  next : S → (Fin b → Bool) → Bool → S

attribute [instance] CoinMachine.instFin

/-- Loss table: `ℓ t i = true` iff arm `i` has loss `1` on day `t` (oblivious adversary). -/
abbrev Losses (n T : ℕ) := Fin T → Fin n → Bool

/-- A coin tape: `b` fresh fair coins for each of the `T` rounds. -/
abbrev Tape (b T : ℕ) := Fin T → Fin b → Bool

/-- `0/1` value of a loss bit. -/
def lv (x : Bool) : ℕ := if x then 1 else 0

lemma lv_le_one (x : Bool) : lv x ≤ 1 := by cases x <;> simp [lv]

variable {n T : ℕ}

/-- State before round `t` along coin tape `ω` (frozen after the horizon). -/
def stateAt (M : CoinMachine n) (ℓ : Losses n T) (ω : Tape M.b T) : ℕ → M.S
  | 0 => M.init
  | t + 1 =>
    if h : t < T then
      M.next (stateAt M ℓ ω t) (ω ⟨t, h⟩) (ℓ ⟨t, h⟩ (M.act (stateAt M ℓ ω t) (ω ⟨t, h⟩)))
    else stateAt M ℓ ω t

/-- The arm pulled on day `t`. -/
def armAt (M : CoinMachine n) (ℓ : Losses n T) (ω : Tape M.b T) (t : Fin T) : Fin n :=
  M.act (stateAt M ℓ ω t) (ω t)

/-- The algorithm's cumulative loss along coin tape `ω`. -/
def algLoss (M : CoinMachine n) (ℓ : Losses n T) (ω : Tape M.b T) : ℕ :=
  ∑ t : Fin T, lv (ℓ t (armAt M ℓ ω t))

/-- Expected cumulative loss: uniform average over all `2^{bT}` coin tapes (fresh fair coins). -/
noncomputable def expLoss (M : CoinMachine n) (ℓ : Losses n T) : ℝ :=
  (∑ ω : Tape M.b T, (algLoss M ℓ ω : ℝ)) / (Fintype.card (Tape M.b T) : ℝ)

/-- Cumulative loss of a fixed arm. -/
def armLoss (ℓ : Losses n T) (i : Fin n) : ℕ := ∑ t : Fin T, lv (ℓ t i)

/-- Polylog in `nT` (natural log). -/
noncomputable def plog (n T : ℕ) (k : ℕ) : ℝ := Real.log ((n : ℝ) * T) ^ k

/-- **Strict reference target** (positive resolution, finite-precision reading of the model):
one machine per `(n,T)`, `n ≥ 1` arms (indexed as `m+1`), `T ≥ n`,
`log₂|S| ≤ C·log(nT)^k`, fresh coins per round `b ≤ C·log(nT)^k` (finite precision with a polylog
number of fair coins per round), and expected regret against every fixed arm
`≤ c·√(nT)·log(nT)^d` for every oblivious `{0,1}` loss table. -/
def StrictTarget : Prop :=
  ∃ (C : ℝ) (k : ℕ) (c : ℝ) (d : ℕ), 0 < C ∧ 1 ≤ k ∧
    ∃ M : (m T : ℕ) → CoinMachine (m + 1),
      ∀ m T : ℕ, m + 1 ≤ T →
        Real.logb 2 (Fintype.card (M m T).S) ≤ C * plog (m + 1) T k ∧
        ((M m T).b : ℝ) ≤ C * plog (m + 1) T k ∧
        ∀ (ℓ : Losses (m + 1) T) (i : Fin (m + 1)),
          expLoss (M m T) ℓ - armLoss ℓ i ≤ c * Real.sqrt (((m + 1 : ℕ) : ℝ) * T) * plog (m + 1) T d

/-- **Coin target**: as `StrictTarget` but the number of fresh coins per round is only required
to be finite (random bits themselves are free). Still finite precision: every transition
probability is a multiple of `2^{-b}`. -/
def CoinTarget : Prop :=
  ∃ (C : ℝ) (k : ℕ) (c : ℝ) (d : ℕ), 0 < C ∧ 1 ≤ k ∧
    ∃ M : (m T : ℕ) → CoinMachine (m + 1),
      ∀ m T : ℕ, m + 1 ≤ T →
        Real.logb 2 (Fintype.card (M m T).S) ≤ C * plog (m + 1) T k ∧
        ∀ (ℓ : Losses (m + 1) T) (i : Fin (m + 1)),
          expLoss (M m T) ℓ - armLoss ℓ i ≤ c * Real.sqrt (((m + 1 : ℕ) : ℝ) * T) * plog (m + 1) T d

theorem StrictTarget.toCoin : StrictTarget → CoinTarget := by
  rintro ⟨C, k, c, d, hC, hk, M, hM⟩
  exact ⟨C, k, c, d, hC, hk, M, fun m T h => ⟨(hM m T h).1, (hM m T h).2.2⟩⟩

/-! ## Sanity checks: the model is non-vacuous and behaves as expected -/

/-- Expected loss lies in `[0, T]`. -/
lemma expLoss_le (M : CoinMachine n) (ℓ : Losses n T) : expLoss M ℓ ≤ T := by
  unfold expLoss
  have hcard : (0 : ℝ) < Fintype.card (Tape M.b T) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hcard]
  have : ∀ ω : Tape M.b T, (algLoss M ℓ ω : ℝ) ≤ T := by
    intro ω
    have : algLoss M ℓ ω ≤ T := by
      unfold algLoss
      calc ∑ t : Fin T, lv (ℓ t (armAt M ℓ ω t)) ≤ ∑ _t : Fin T, 1 :=
            Finset.sum_le_sum fun t _ => lv_le_one _
        _ = T := by simp
    exact_mod_cast this
  calc ∑ ω : Tape M.b T, (algLoss M ℓ ω : ℝ) ≤ ∑ _ω : Tape M.b T, (T : ℝ) :=
        Finset.sum_le_sum fun ω _ => this ω
    _ = T * Fintype.card (Tape M.b T) := by simp [mul_comm]

lemma expLoss_nonneg (M : CoinMachine n) (ℓ : Losses n T) : 0 ≤ expLoss M ℓ := by
  unfold expLoss; positivity

/-- The one-state, zero-coin machine that always pulls arm `0`. -/
def constMachine (m : ℕ) : CoinMachine (m + 1) where
  S := Unit
  b := 0
  init := ()
  act := fun _ _ => 0
  next := fun _ _ _ => ()

/-- Its expected loss is exactly the loss of arm `0` (the coin average is computed correctly). -/
lemma expLoss_const (m : ℕ) (ℓ : Losses (m + 1) T) :
    expLoss (constMachine m) ℓ = armLoss ℓ 0 := by
  have h1 : Fintype.card (Tape 0 T) = 1 := Fintype.card_unique
  unfold expLoss
  change (∑ ω : Tape 0 T, (algLoss (constMachine m) ℓ ω : ℝ)) / (Fintype.card (Tape 0 T) : ℝ) = _
  rw [h1, Fintype.sum_unique]
  simp [algLoss, armAt, armLoss, constMachine]

/-- The model is not trivially satisfiable: a regret bound of `0` fails already for one fixed
machine family when losses favour another arm (here: the constant machine, 2 arms, 1 day). -/
example : ¬ ∀ ℓ : Losses 2 1, ∀ i, expLoss (constMachine 1) ℓ - armLoss ℓ i ≤ 0 := by
  intro h
  have := h (fun _ j => decide (j = 0)) 1
  rw [expLoss_const] at this
  simp [armLoss, lv] at this
  norm_num at this

/-- A one-coin machine for two arms that pulls the arm named by its coin. Its expected loss is the
average of the two arms' losses (fresh coins are averaged correctly). -/
def coinFlip : CoinMachine 2 where
  S := Unit
  b := 1
  init := ()
  act := fun _ c => if c 0 then 1 else 0
  next := fun _ _ _ => ()

example : expLoss (T := 1) coinFlip (fun _ j => decide (j = 0)) = 1 / 2 := by
  unfold expLoss
  change (∑ ω : Tape 1 1, (algLoss coinFlip (fun _ j => decide (j = 0)) ω : ℝ)) /
    (Fintype.card (Tape 1 1) : ℝ) = 1 / 2
  let e : Tape 1 1 ≃ Bool :=
    (Equiv.funUnique (Fin 1) (Fin 1 → Bool)).trans (Equiv.funUnique (Fin 1) Bool)
  rw [← Equiv.sum_comp e.symm]
  simp [algLoss, armAt, coinFlip, lv, stateAt, e]
  simp [Finset.filter_insert, Finset.filter_singleton]

end Audit3

/-!
# Part 2: the EXPLICIT family behind `Pool.P0294.main`

`Pool.P0294.main` obtains its machines with `Classical.choose` (P0173's `minimax_of_StepAtIn`) from an existence
statement whose levels are themselves only asserted to exist (`StepAtIn`, `FamHyp`). This file writes the algorithm
down as definitions and re-proves P0001's three properties for it:

* `stepE n hn H A`: P0284's one-level machine `machF n H q A` at P0161's rate `q = qOf cE kE n H`, with the constants
  of the final proof (`Cg = 10¹⁷·5³⁰`, `kg = 30`, `cE = max (CF Cg) 0 + 6`, `kE = max 28 30`).
* `algR c k n hn step H`: the horizon recursion (well-founded on `H`): the trivial coin algorithm (always arm `0`)
  when `H = 0` or `H ≤ (12 Λ²)² n`, else `step H (algR … ⌈4 q H⌉)` (the `min … (H - 1)` only makes termination
  syntactic; it is inactive in the recursive case, `hnext`).
* `famE n T hn`: `(algR cE kE n hn (stepE n hn) T).toMachine` for `2 ≤ n ≤ T`, P0161's trivial machine otherwise.
* `famE_spec`: `famE` is homogeneous, has P0001's `MemoryBound` and the `Õ(√(nT))` `RegretBound`.

The proofs are the pool's own (P0292's `famHyp_of_good`, P0278's `stepAtIn_of_famHypAt`, P0173's `exists_machineIn`
and `minimax_of_StepAtIn`), copied with the witness fixed instead of existentially quantified.
-/

namespace Audit3E

open Pool.P0001

/-- `Cg` of `Pool.P0294.goodBound`. -/
noncomputable def Cg0 : ℝ := 100000000000000000 * 5 ^ 30
/-- The step constants of the final proof: `c = max (CF Cg) 0 + 6`, `k = max 28 30`. -/
noncomputable def cE : ℝ := max (Pool.P0292.CF Cg0) 0 + 6
def kE : ℕ := max 28 30

/-- P0278's `FamHyp C k` with the witness fixed to P0284's `machF`. -/
def FamHypE (C : ℝ) (k : ℕ) : Prop :=
  ∀ (n T : ℕ) [NeZero n] (q : ℝ), 1 ≤ n → n ≤ T → (n : ℝ) / T ≤ q → q ≤ 1 / 32 →
    ∀ A : Pool.P0050.CoinAlg n, Pool.P0173.CoinHom A →
      Pool.P0173.CoinHom (Pool.P0284.machF n T q A) ∧
      (Pool.P0284.machF n T q A).toMachine.memBits ≤ A.toMachine.memBits + C * Pool.P0161.Lg n T ^ k ∧
        ∃ (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (β : ℝ) (Tb : ℕ), 0 < γ ∧ γ * Tb ≤ q * T ∧ Tb ≤ 2 * T ∧
          0 ≤ β ∧ β ≤ 2 * γ ∧
          ∀ ℓ : LossSeq n, ∃ ℓ' : LossSeq n,
            regret (Pool.P0284.machF n T q A).toMachine ℓ T ≤
              C * Pool.P0161.Lg n T ^ k * Real.sqrt (n * T / q) +
                β * regret (Pool.P0055.Sub A.toMachine γ h0 h1) ℓ' Tb

section Fam

open Finset Pool.P0261 Pool.P0284 Pool.P0194 Pool.P0290 Pool.P0292
open scoped Pool.P0290 Pool.P0201 Pool.P0287 Pool.P0050
open Classical

set_option maxHeartbeats 8000000 in
/-- P0292's `famHyp_of_good` with the witness `machF n T q A` fixed (same proof). -/
theorem famHypE {Cg : ℝ} {kg : ℕ} (hG : GoodBound Cg kg) : FamHypE (CF Cg) (max 28 kg) := by
  intro n T _ q hn hnT hnq hq1 A hA
  have hT1 : 1 ≤ T := le_trans hn hnT
  have hTr : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq : 0 < q := lt_of_lt_of_le (div_pos hn0 hTr) hnq
  have hLg := Pool.P0161.one_le_Lg hn hT1
  set k := max 28 kg with hk
  have hLk : ∀ a, a ≤ k → Pool.P0161.Lg n T ^ a ≤ Pool.P0161.Lg n T ^ k := fun a ha => pow_le_pow_right₀ hLg ha
  have hLk1 : 1 ≤ Pool.P0161.Lg n T ^ k := one_le_pow₀ hLg
  have hCF : CF Cg = 6 + 5000000000000000 * 5 ^ 28 + max Cg 0 + 160 * 600001 ^ 2 * 5 ^ 26 := rfl
  refine ⟨machF_hom n T q A, ?_, q / 2, by positivity, by linarith, ?_⟩
  · -- memory
    refine (memBits_machF_Lg n T q A hn hnT hq hq1 hnq).trans (add_le_add le_rfl ?_)
    have h26 := hLk 26 (by omega)
    have : 160 * 600001 ^ 2 * 5 ^ 26 ≤ CF Cg := by rw [hCF]; have := le_max_right Cg 0; norm_num; linarith
    have hC0 : 0 ≤ CF Cg := by rw [hCF]; have := le_max_right Cg 0; positivity
    exact mul_le_mul this h26 (by positivity) hC0
  · -- the regret
    have hK := KcF_pos n T q hq
    have hsw := slot_weights_le n T q hq
    have hX1 : (∑ s : Σ j : Fin (famM n T q A).P.D, Fin ((famM n T q A).P.sl j), (famM n T q A).P.xr s.1) ≤ q / 4 := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact hsw.1
    have hκ : (∑ j : Fin (famM n T q A).P.D, ((famM n T q A).P.sl j : ℝ)) *
        ∑ j : Fin (famM n T q A).P.D, (famM n T q A).P.xr j ≤ q / 4 := hsw.2
    have hκ0 : 0 ≤ (∑ j : Fin (famM n T q A).P.D, ((famM n T q A).P.sl j : ℝ)) *
        ∑ j : Fin (famM n T q A).P.D, (famM n T q A).P.xr j :=
      mul_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) (Finset.sum_nonneg fun j _ => (xr_pos hK j).le)
    have hX10 : 0 ≤ (∑ s : Σ j : Fin (famM n T q A).P.D, Fin ((famM n T q A).P.sl j), (famM n T q A).P.xr s.1) :=
      Finset.sum_nonneg fun s _ => (xr_pos hK s.1).le
    have hwB : (famM n T q A).P.wB = q / 2 := rfl
    refine ⟨(famM n T q A).P.wB + ∑ s : Σ j : Fin (famM n T q A).P.D, Fin ((famM n T q A).P.sl j),
        (famM n T q A).P.xr s.1 + (∑ j : Fin (famM n T q A).P.D, ((famM n T q A).P.sl j : ℝ)) *
          ∑ j : Fin (famM n T q A).P.D, (famM n T q A).P.xr j, Tp T, by positivity, ?_, Tp_le T hT1,
        by rw [hwB]; positivity, by rw [hwB]; linarith, fun ℓ => ?_⟩
    · have : (Tp T : ℝ) ≤ 2 * T := by exact_mod_cast Tp_le T hT1
      nlinarith
    · refine ⟨Pool.P0206.sh (Pool.P0140.zeroAfter ℓ T), ?_⟩
      -- coins to start from
      have hNA : 0 < (famM n T q A).P.N := NeZero.pos _
      let y : A.Y := A.μ.support_nonempty.some
      let z : A.Z := A.ν.support_nonempty.some
      let rc₀ : RC (famM n T q A).P := (none, ⟨0, hNA⟩, y, z)
      let ω₀ : Pool.P0201.Yc (famM n T q A) × Pool.P0201.Zc (famM n T q A) :=
        ((none, ⟨0, hNA⟩, y), (z, fun _ => false))
      have hle : T ≤ Tp T + 1 := (le_Tp T).trans (Nat.le_succ _)
      rw [← Pool.P0140.regret_zeroAfter (machF n T q A).toMachine ℓ hle]
      have hR := regret_famM_le n T q A hn hnT hq hq1 hnq (Pool.P0140.zeroAfter ℓ T) ω₀ rc₀
      have hgood := hG n T q A hA hn hnT hq hq1 hnq (Pool.P0140.zeroAfter ℓ T) rc₀
      have eM : regret (machF n T q A).toMachine (Pool.P0140.zeroAfter ℓ T) (Tp T + 1) =
          regret (Pool.P0201.mach (famM n T q A)).toMachine (Pool.P0140.zeroAfter ℓ T) (Tp T + 1) := rfl
      rw [eM]
      refine hR.trans ?_
      set Q := Real.sqrt ((n : ℝ) * T / q) with hQ
      have hQ1 : 1 ≤ Q := Pool.P0291.Q_ge_one n T q hn hnT hq hq1 hnq
      have hΛ := Pool.P0284.BB_le_Lg n T hn hnT
      have hΛ0 : (0 : ℝ) ≤ Pool.P0291.Λ n T := by unfold Pool.P0291.Λ; positivity
      have hΛ28 : Pool.P0291.Λ n T ^ 28 ≤ 5 ^ 28 * Pool.P0161.Lg n T ^ k := by
        have h1 : Pool.P0291.Λ n T ^ 28 ≤ (5 * Pool.P0161.Lg n T) ^ 28 := pow_le_pow_left₀ hΛ0 hΛ 28
        rw [mul_pow] at h1
        have h2 := hLk 28 (le_max_left _ _)
        nlinarith
      have hQ0 : 0 ≤ Q := by linarith
      have k1 : 5000000000000000 * Pool.P0291.Λ n T ^ 28 * Pool.P0291.Q n T q ≤
          5000000000000000 * 5 ^ 28 * Pool.P0161.Lg n T ^ k * Q := by
        have := mul_le_mul_of_nonneg_right hΛ28 hQ0
        show 5000000000000000 * Pool.P0291.Λ n T ^ 28 * Q ≤ _
        nlinarith
      have k2 : Cg * Pool.P0161.Lg n T ^ kg * Q ≤ max Cg 0 * Pool.P0161.Lg n T ^ k * Q := by
        have hkg := hLk kg (le_max_right _ _)
        have h0 : 0 ≤ Pool.P0161.Lg n T ^ kg := by positivity
        have : Cg * Pool.P0161.Lg n T ^ kg ≤ max Cg 0 * Pool.P0161.Lg n T ^ k :=
          (mul_le_mul_of_nonneg_right (le_max_left Cg 0) h0).trans
            (mul_le_mul_of_nonneg_left hkg (le_max_right Cg 0))
        exact mul_le_mul_of_nonneg_right this hQ0
      have k3 : (6 : ℝ) ≤ 6 * Pool.P0161.Lg n T ^ k * Q := by nlinarith
      have k4 : 0 ≤ 160 * 600001 ^ 2 * 5 ^ 26 * Pool.P0161.Lg n T ^ k * Q := by positivity
      have eS : regret (Pool.P0055.Sub (famM n T q A).P.AB.toMachine (famM n T q A).P.wB (famM_isLaw n T q A hq hq1).1
          (Pool.P0202.wB_le_one _ (famM_isLaw n T q A hq hq1))) (Pool.P0206.sh (Pool.P0140.zeroAfter ℓ T)) (Tp T) =
          regret (Pool.P0055.Sub A.toMachine (q / 2) (by positivity) (by linarith))
            (Pool.P0206.sh (Pool.P0140.zeroAfter ℓ T)) (Tp T) := rfl
      rw [eS] at hR ⊢
      have eC : CF Cg * Pool.P0161.Lg n T ^ k * Q = (6 * Pool.P0161.Lg n T ^ k * Q) +
          5000000000000000 * 5 ^ 28 * Pool.P0161.Lg n T ^ k * Q + max Cg 0 * Pool.P0161.Lg n T ^ k * Q +
          160 * 600001 ^ 2 * 5 ^ 26 * Pool.P0161.Lg n T ^ k * Q := by rw [hCF]; ring
      rw [eC]
      linarith

end Fam

section Step

open Pool.P0050 Pool.P0055 Pool.P0161 Pool.P0173 Pool.P0278

/-- P0278's `stepAtIn_of_famHypAt` with the witness `machF` fixed (same proof). -/
theorem stepE_gen {C : ℝ} {k : ℕ} (hF : FamHypE C k) (n T : ℕ) [NeZero n] (hn : 1 ≤ n) (hnT : n ≤ T)
    (hq : (n : ℝ) / T ≤ qOf (max C 0 + 6) k n T) (A : CoinAlg n) (hA : CoinHom A) (RB : ℝ)
    (hRB : ∀ ℓ : LossSeq n, regret A.toMachine ℓ ⌈4 * qOf (max C 0 + 6) k n T * T⌉₊ ≤ RB) :
    CoinHom (Pool.P0284.machF n T (qOf (max C 0 + 6) k n T) A) ∧
      (Pool.P0284.machF n T (qOf (max C 0 + 6) k n T) A).toMachine.memBits ≤
        A.toMachine.memBits + (max C 0 + 6) * Lg n T ^ k ∧
      ∀ ℓ : LossSeq n, regret (Pool.P0284.machF n T (qOf (max C 0 + 6) k n T) A).toMachine ℓ T ≤
        (max C 0 + 6) * Lg n T ^ k * (Real.sqrt (n * T / qOf (max C 0 + 6) k n T) + RB) := by
  have hT : 1 ≤ T := le_trans hn hnT
  set c := max C 0 + 6 with hc
  set q := qOf c k n T with hqdef
  have hq0 : 0 < q := qOf_pos c k n T hn hT
  obtain ⟨hM, hmem, γ, h0, h1, β, Tb, hγ, hγT, hTb, hβ0, hβ, hreg⟩ :=
    hF n T q hn hnT hq (qOf_le c k n T hn hT) A hA
  have hL1 : 1 ≤ Lg n T := Pool.P0161.one_le_Lg hn hT
  have hLk : 1 ≤ Lg n T ^ k := one_le_pow₀ hL1
  have hCc : C ≤ c := by rw [hc]; linarith [le_max_left C 0]
  have hc6 : max C 0 + 4 ≤ c := by rw [hc]; linarith
  refine ⟨hM, ?_, fun ℓ => ?_⟩
  · refine hmem.trans ?_
    have : C * Lg n T ^ k ≤ c * Lg n T ^ k := mul_le_mul_of_nonneg_right hCc (by linarith)
    linarith
  · obtain ⟨ℓ', hℓ⟩ := hreg ℓ
    set H := ⌈4 * q * T⌉₊ with hH
    have hRB0 : 0 ≤ RB := by
      have := hRB (fun _ _ => false)
      rwa [Pool.P0144.regret_zero_seq] at this
    have hsub := Pool.P0067.regret_Sub_le_fixed A.toMachine (toMachine_isHomogeneous hA) hγ h1 ℓ' Tb H RB hRB0
      (fun ℓ'' m _ hmH => Pool.P0140.regret_prefix_le _ hRB ℓ'' hmH)
    have hHq : 4 * q * T ≤ H := Nat.le_ceil _
    have htail := Pool.P0067.tail_le_exp h0 Tb H (x := q * T) (by linarith)
    have hTb' : (Tb : ℝ) ≤ 2 * T := by exact_mod_cast hTb
    have hexp : (Tb : ℝ) * Real.exp (-(q * T)) ≤ 2 / q := by
      have := T_exp_le hq0 T
      have he := (Real.exp_pos (-(q * T))).le
      calc (Tb : ℝ) * Real.exp (-(q * T)) ≤ (2 * T) * Real.exp (-(q * T)) := mul_le_mul_of_nonneg_right hTb' he
        _ = 2 * (T * Real.exp (-(q * T))) := by ring
        _ ≤ 2 * (1 / q) := by linarith
        _ = 2 / q := by ring
    have hS : regret (Sub A.toMachine γ h0 h1) ℓ' Tb ≤ (1 / γ) * (RB + 2 / q) := by
      refine hsub.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      have : (Tb : ℝ) * ((1 + γ) ^ Tb / 2 ^ (H + 1)) ≤ Tb * Real.exp (-(q * T)) :=
        mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
      linarith
    have hβS : β * regret (Sub A.toMachine γ h0 h1) ℓ' Tb ≤ 2 * (RB + 2 / q) := by
      have hpos : 0 ≤ RB + 2 / q := by positivity
      calc β * regret (Sub A.toMachine γ h0 h1) ℓ' Tb ≤ β * ((1 / γ) * (RB + 2 / q)) :=
            mul_le_mul_of_nonneg_left hS hβ0
        _ = (β / γ) * (RB + 2 / q) := by ring
        _ ≤ 2 * (RB + 2 / q) := by
            apply mul_le_mul_of_nonneg_right _ hpos
            rw [div_le_iff₀ hγ]; linarith
    have hinv := inv_le_sqrt hn hT hq0 hq
    set s := Real.sqrt (n * T / q)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have h2q : 2 / q = 2 * (1 / q) := by ring
    -- assemble
    have hfin : C * Lg n T ^ k * s + 2 * (RB + 2 / q) ≤ c * Lg n T ^ k * (s + RB) := by
      have e1 : C * Lg n T ^ k * s ≤ max C 0 * Lg n T ^ k * s :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)) hs0
      have e2 : 4 * s ≤ 4 * Lg n T ^ k * s := by nlinarith
      have e3 : 2 * RB ≤ 6 * Lg n T ^ k * RB := by nlinarith
      have e4 : 0 ≤ max C 0 * Lg n T ^ k * RB :=
        mul_nonneg (mul_nonneg (le_max_right _ _) (by linarith)) hRB0
      rw [hc, h2q]
      nlinarith
    linarith

/-- **The one-level step, written down**: P0284's `machF` at horizon `H` and rate `qOf cE kE n H`, on BASE `A`. -/
noncomputable def stepE (n : ℕ) (hn : 1 ≤ n) (H : ℕ) (A : CoinAlg n) : CoinAlg n :=
  @Pool.P0284.machF n H ⟨by omega⟩ (qOf cE kE n H) A

theorem stepE_spec (n : ℕ) (hn : 1 ≤ n) : ∀ T, n ≤ T → (n : ℝ) / T ≤ qOf cE kE n T →
    ∀ A : CoinAlg n, CoinHom A → ∀ RB : ℝ,
      (∀ ℓ : LossSeq n, regret A.toMachine ℓ ⌈4 * qOf cE kE n T * T⌉₊ ≤ RB) →
      CoinHom (stepE n hn T A) ∧
      (stepE n hn T A).toMachine.memBits ≤ A.toMachine.memBits + cE * Lg n T ^ kE ∧
      ∀ ℓ : LossSeq n, regret (stepE n hn T A).toMachine ℓ T ≤
        cE * Lg n T ^ kE * (Real.sqrt (n * T / qOf cE kE n T) + RB) := by
  intro T hnT hq A hA RB hRB
  haveI : NeZero n := ⟨by omega⟩
  exact stepE_gen (famHypE Pool.P0294.goodBound) n T hn hnT hq A hA RB hRB

end Step

section Rec

open Pool.P0050 Pool.P0161 Pool.P0173

/-- **The horizon recursion, written down.** -/
noncomputable def algR (c : ℝ) (k n : ℕ) (hn : 1 ≤ n) (step : ℕ → CoinAlg n → CoinAlg n) : ℕ → CoinAlg n
  | H =>
    if h : H = 0 ∨ (H : ℝ) ≤ (12 * Lam c k n H ^ 2) ^ 2 * n then trivCoin n hn
    else step H (algR c k n hn step (min ⌈4 * qOf c k n H * H⌉₊ (H - 1)))
termination_by H => H
decreasing_by
  have : H ≠ 0 := fun h0 => h (Or.inl h0)
  exact lt_of_le_of_lt (min_le_right _ _) (by omega)

theorem trivCoin_hom (n : ℕ) (hn : 1 ≤ n) : CoinHom (trivCoin n hn) := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

theorem trivCoin_memBits (n : ℕ) (hn : 1 ≤ n) : (trivCoin n hn).toMachine.memBits ≤ 0 := by
  show Real.logb 2 (Fintype.card (Unit × Unit)) ≤ 0
  simp

/-- P0173's `exists_machineIn` for the explicit recursion (same proof). -/
theorem algR_spec {c : ℝ} {k n : ℕ} (hn : 1 ≤ n) (step : ℕ → CoinAlg n → CoinAlg n)
    (hstep : ∀ T : ℕ, n ≤ T → (n : ℝ) / T ≤ qOf c k n T →
      ∀ A : CoinAlg n, CoinHom A → ∀ RB : ℝ,
        (∀ ℓ : LossSeq n, regret A.toMachine ℓ ⌈4 * qOf c k n T * T⌉₊ ≤ RB) →
        CoinHom (step T A) ∧
        (step T A).toMachine.memBits ≤ A.toMachine.memBits + c * Lg n T ^ k ∧
        ∀ ℓ : LossSeq n, regret (step T A).toMachine ℓ T ≤
          c * Lg n T ^ k * (Real.sqrt (n * T / qOf c k n T) + RB)) :
    ∀ H, 1 ≤ H → CoinHom (algR c k n hn step H) ∧
      (algR c k n hn step H).toMachine.memBits ≤ (Nat.log 2 H : ℝ) * Lam c k n H ∧
      ∀ ℓ : LossSeq n, regret (algR c k n hn step H).toMachine ℓ H ≤ 12 * Lam c k n H ^ 2 * Real.sqrt (n * H) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  intro H
  induction H using Nat.strong_induction_on with
  | _ H ih =>
  intro hH1
  set Λ := Lam c k n H with hΛdef
  have hΛ : 1 ≤ Λ := one_le_Lam hn hH1
  by_cases hsmall : (H : ℝ) ≤ (12 * Λ ^ 2) ^ 2 * n
  · have hdef : algR c k n hn step H = trivCoin n hn := by
      rw [algR, dif_pos (Or.inr hsmall)]
    rw [hdef]
    refine ⟨trivCoin_hom n hn, ?_, fun ℓ => ?_⟩
    · exact (trivCoin_memBits n hn).trans (by positivity)
    · calc regret (trivCoin n hn).toMachine ℓ H ≤ H := regret_le _ _ _
        _ = Real.sqrt H * Real.sqrt H := (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ (12 * Λ ^ 2 * Real.sqrt n) * Real.sqrt H := by
            apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
            rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by positivity)]
            exact hsmall
        _ = 12 * Λ ^ 2 * Real.sqrt (n * H) := by rw [Real.sqrt_mul (by positivity)]; ring
  · push Not at hsmall
    set q : ℝ := qOf c k n H with hqdef
    have hq : q = 1 / (32 * Λ ^ 2) := rfl
    have hqpos : 0 < q := by rw [hq]; positivity
    have hHbig : (144 : ℝ) * Λ ^ 4 * n < H := by nlinarith
    have hΛ4 : (1 : ℝ) ≤ Λ ^ 4 := one_le_pow₀ hΛ
    have hΛ2 : (1 : ℝ) ≤ Λ ^ 2 := one_le_pow₀ hΛ
    have hH144 : (144 : ℝ) < H := by nlinarith
    have hnH : n ≤ H := by exact_mod_cast (show (n : ℝ) ≤ H by nlinarith)
    -- the inner horizon
    set H' := ⌈4 * q * H⌉₊ with hH'
    have h4q : 4 * q * H = H / (8 * Λ ^ 2) := by rw [hq]; field_simp; ring
    have h4q1 : 1 ≤ 4 * q * H := by
      rw [h4q, le_div_iff₀ (by positivity)]; nlinarith
    have hH'1 : 1 ≤ H' := by
      rw [hH']; exact Nat.one_le_iff_ne_zero.mpr (by
        intro h0; rw [Nat.ceil_eq_zero] at h0; linarith)
    have hH'le : (H' : ℝ) ≤ 8 * q * H := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 4 * q * H by positivity)
      linarith
    have hH'half : 2 * H' ≤ H := by
      have h8 : 8 * q * H ≤ H / 4 := by
        rw [show 8 * q * H = 2 * (4 * q * H) by ring, h4q]
        have : (H : ℝ) / (8 * Λ ^ 2) ≤ H / 8 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) (by nlinarith)
        linarith
      have : (2 * H' : ℝ) ≤ H := by linarith
      exact_mod_cast this
    have hH'lt : H' < H := by omega
    -- the explicit recursion takes exactly this step
    have hnext : min ⌈4 * qOf c k n H * H⌉₊ (H - 1) = H' := by
      rw [← hqdef, ← hH']; exact min_eq_left (by omega)
    have hdef : algR c k n hn step H = step H (algR c k n hn step H') := by
      have hns : ¬ (H = 0 ∨ (H : ℝ) ≤ (12 * Lam c k n H ^ 2) ^ 2 * n) := by
        rintro (h0 | h0)
        · omega
        · rw [← hΛdef] at h0; linarith
      rw [algR, dif_neg hns, hnext]
    obtain ⟨hMBc, hMBm, hMBr⟩ := ih H' hH'lt hH'1
    have hLm : Lam c k n H' ≤ Λ := Lam_mono hn hH'1 hH'lt.le
    have hLm0 : 0 ≤ Lam c k n H' := le_trans zero_le_one (one_le_Lam hn hH'1)
    have hMBr' : ∀ ℓ : LossSeq n, regret (algR c k n hn step H').toMachine ℓ ⌈4 * qOf c k n H * H⌉₊ ≤
        12 * Λ ^ 2 * Real.sqrt (n * H') := by
      intro ℓ
      calc regret (algR c k n hn step H').toMachine ℓ ⌈4 * qOf c k n H * H⌉₊
            = regret (algR c k n hn step H').toMachine ℓ H' := rfl
        _ ≤ 12 * Lam c k n H' ^ 2 * Real.sqrt (n * H') := hMBr ℓ
        _ ≤ 12 * Λ ^ 2 * Real.sqrt (n * H') := by
            gcongr
    have hnq : (n : ℝ) / H ≤ qOf c k n H := by
      rw [← hqdef, hq, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
    obtain ⟨hMc, hMm, hMr⟩ := hstep H hnH hnq (algR c k n hn step H') hMBc
      (12 * Λ ^ 2 * Real.sqrt (n * H')) hMBr'
    have hle := cLg_le_Lam (c := c) (k := k) hn hH1 (le_refl H)
    rw [hdef]
    refine ⟨hMc, ?_, fun ℓ => ?_⟩
    · -- memory: log₂ H' + 1 ≤ log₂ H
      have hlog : (Nat.log 2 H' : ℝ) + 1 ≤ Nat.log 2 H := by
        have : Nat.log 2 H' + 1 ≤ Nat.log 2 H := by
          calc Nat.log 2 H' + 1 = Nat.log 2 (H' * 2) :=
                (Nat.log_mul_base (by norm_num) (by omega)).symm
            _ ≤ Nat.log 2 H := Nat.log_mono_right (by omega)
        exact_mod_cast this
      calc (step H (algR c k n hn step H')).toMachine.memBits
            ≤ (algR c k n hn step H').toMachine.memBits + c * Lg n H ^ k := hMm
        _ ≤ (Nat.log 2 H' : ℝ) * Lam c k n H' + Λ := add_le_add hMBm hle
        _ ≤ (Nat.log 2 H' : ℝ) * Λ + Λ := by
            gcongr
        _ = ((Nat.log 2 H' : ℝ) + 1) * Λ := by ring
        _ ≤ (Nat.log 2 H : ℝ) * Λ := mul_le_mul_of_nonneg_right hlog (by linarith)
    · have hX : 0 ≤ Real.sqrt (n * H / q) + 12 * Λ ^ 2 * Real.sqrt (n * H') := by positivity
      calc regret (step H (algR c k n hn step H')).toMachine ℓ H
            ≤ c * Lg n H ^ k * (Real.sqrt (n * H / q) + 12 * Λ ^ 2 * Real.sqrt (n * H')) := hMr ℓ
        _ ≤ Λ * (Real.sqrt (n * H / q) + 12 * Λ ^ 2 * Real.sqrt (n * H')) :=
            mul_le_mul_of_nonneg_right hle hX
        _ ≤ 12 * Λ ^ 2 * Real.sqrt (n * H) := by
            apply step_arith hΛ (by positivity) (by positivity) hq
            calc (n : ℝ) * H' ≤ n * (8 * q * H) := mul_le_mul_of_nonneg_left hH'le (by positivity)
              _ = 8 * q * (n * H) := by ring

/-- **The explicit family**: the explicit recursion at horizon `T` for `2 ≤ n ≤ T`, P0161's one-state machine
otherwise. -/
noncomputable def famR (c : ℝ) (k : ℕ) (step : ∀ n : ℕ, 1 ≤ n → ℕ → CoinAlg n → CoinAlg n) : Family :=
  fun n T hn => if 2 ≤ n ∧ n ≤ T then (algR c k n hn (step n hn) T).toMachine else triv n hn

/-- P0173's `minimax_of_StepAtIn` for the explicit family (same proof). -/
theorem famR_spec {c : ℝ} {k : ℕ} (step : ∀ n : ℕ, 1 ≤ n → ℕ → CoinAlg n → CoinAlg n)
    (hstep : ∀ (n : ℕ) (hn : 1 ≤ n) (T : ℕ), n ≤ T → (n : ℝ) / T ≤ qOf c k n T →
      ∀ A : CoinAlg n, CoinHom A → ∀ RB : ℝ,
        (∀ ℓ : LossSeq n, regret A.toMachine ℓ ⌈4 * qOf c k n T * T⌉₊ ≤ RB) →
        CoinHom (step n hn T A) ∧
        (step n hn T A).toMachine.memBits ≤ A.toMachine.memBits + c * Lg n T ^ k ∧
        ∀ ℓ : LossSeq n, regret (step n hn T A).toMachine ℓ T ≤
          c * Lg n T ^ k * (Real.sqrt (n * T / qOf c k n T) + RB)) :
    (∀ n T hn, (famR c k step n T hn).IsHomogeneous) ∧
      MemoryBound (famR c k step) (2 * max c 1 * 2 ^ k) (k + 1) ∧
      RegretBound (famR c k step) fun n T => 12 * max c 1 ^ 2 * 4 ^ k * Real.sqrt (n * T) *
        Real.log (n * T) ^ (2 * k) := by
  classical
  set F := famR c k step
  have hspec : ∀ n T (hn : 1 ≤ n) (h : 2 ≤ n ∧ n ≤ T), F n T hn = (algR c k n hn (step n hn) T).toMachine := by
    intro n T hn h; simp only [F, famR, if_pos h]
  have htriv : ∀ n T (hn : 1 ≤ n) (h : ¬ (2 ≤ n ∧ n ≤ T)), F n T hn = triv n hn := by
    intro n T hn h; simp only [F, famR, if_neg h]
  have hR := fun n (hn : 1 ≤ n) T (hT : 1 ≤ T) => algR_spec hn (step n hn) (hstep n hn) T hT
  set c₁ := max c 1 with hc₁
  have hc₁1 : 1 ≤ c₁ := le_max_right _ _
  have hLam : ∀ n T, 2 ≤ n → n ≤ T →
      Lam c k n T ≤ c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ k := by
    intro n T h2 hnT
    have hl := one_le_log h2 hnT
    unfold Lam Lg
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) k)
      (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · intro n T hn
    by_cases h : 2 ≤ n ∧ n ≤ T
    · rw [hspec n T hn h]
      exact toMachine_isHomogeneous (hR n hn T (by omega)).1
    · rw [htriv n T hn h]; exact triv_isHomogeneous n hn
  · intro n T hn hnT
    have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := Lg_nonneg hn (le_trans hn hnT)
    by_cases h : 2 ≤ n ∧ n ≤ T
    · rw [hspec n T hn h]
      have hm := (hR n hn T (by omega)).2.1
      have hΛ0 : 0 ≤ Lam c k n T := le_trans zero_le_one (one_le_Lam hn (le_trans hn hnT))
      calc _ ≤ (Nat.log 2 T : ℝ) * Lam c k n T := hm
        _ ≤ (2 * Real.log ((n : ℝ) * T)) * (c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ k) :=
            mul_le_mul (natLog_le_two_log hn hnT) (hLam n T h.1 hnT) hΛ0 (by positivity)
        _ = 2 * c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ (k + 1) := by ring
    · rw [htriv n T hn h, triv_memBits]; positivity
  · intro n T hn hnT ℓ
    have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := Lg_nonneg hn (le_trans hn hnT)
    by_cases h : 2 ≤ n ∧ n ≤ T
    · rw [hspec n T hn h]
      have hr := (hR n hn T (by omega)).2.2 ℓ
      have hΛ1 := one_le_Lam (c := c) (k := k) hn (le_trans hn hnT)
      have hΛ2 : Lam c k n T ^ 2 ≤ c₁ ^ 2 * 4 ^ k * Real.log ((n : ℝ) * T) ^ (2 * k) := by
        calc Lam c k n T ^ 2 ≤ (c₁ * 2 ^ k * Real.log ((n : ℝ) * T) ^ k) ^ 2 :=
              pow_le_pow_left₀ (by linarith) (hLam n T h.1 hnT) 2
          _ = c₁ ^ 2 * 4 ^ k * Real.log ((n : ℝ) * T) ^ (2 * k) := by
              rw [show (4 : ℝ) ^ k = (2 ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul]; norm_num,
                pow_mul]; ring
      calc _ ≤ 12 * Lam c k n T ^ 2 * Real.sqrt (n * T) := hr
        _ ≤ 12 * (c₁ ^ 2 * 4 ^ k * Real.log ((n : ℝ) * T) ^ (2 * k)) * Real.sqrt (n * T) := by
            gcongr
        _ = 12 * c₁ ^ 2 * 4 ^ k * Real.sqrt (n * T) * Real.log ((n : ℝ) * T) ^ (2 * k) := by ring
    · have hn1 : n = 1 := by omega
      subst hn1
      rw [regret_one]; positivity

end Rec

/-- **The explicit family of the final proof.** -/
noncomputable def famE : Family := famR cE kE stepE

/-- **`famE` meets P0001's target with explicit constants** (no `Classical.choose` at the level of the family or
of the recursion). -/
theorem famE_spec :
    (∀ n T hn, (famE n T hn).IsHomogeneous) ∧
      MemoryBound famE (2 * max cE 1 * 2 ^ kE) (kE + 1) ∧
      RegretBound famE fun n T => 12 * max cE 1 ^ 2 * 4 ^ kE * Real.sqrt (n * T) *
        Real.log (n * T) ^ (2 * kE) :=
  famR_spec stepE stepE_spec

theorem famE_minimax : MinimaxPolylogAchievable :=
  ⟨famE, famE_spec.1, ⟨_, _, famE_spec.2.1⟩, ⟨_, _, famE_spec.2.2⟩⟩

end Audit3E

#print axioms Audit3E.famE_spec
#print axioms Audit3E.famE_minimax

/-!
# Part 3: finite precision is free for P0001's model (generic rounding theorem)

P0001's `Machine` has real-valued (`PMF`) transition laws. The problem requires finite precision and fresh
fair coins. This file proves, for P0001's model and independently of the pool's construction:

* `Dyadic M b`: every law of `M` (initial law, every action law, every next-state law) is EXACTLY the image of
  `b` fresh fair coins (`coins b`, uniform on `Fin b → Bool`) under a deterministic map; so every transition
  probability is a multiple of `2^{-b}`.
* `StrictMinimax`: P0001's `MinimaxPolylogAchievable` with, in addition, a polylog bound `b ≤ Cb·log(nT)^kb` on the
  number of fair coins drawn per law.
* `strict_of_minimax : MinimaxPolylogAchievable → StrictMinimax`: any family meeting P0001's target can be rounded
  to dyadic laws with `O(log(nT) + memBits)` coins per draw, the SAME state set (so the same memory), the same
  homogeneity, and regret larger by at most `1`.

The rounding: the law `p` on a finite set `X` is replaced by `cnt x / 2^b` with `cnt x = ⌊2^b p x⌋` off one point
`x0` and the remainder at `x0`; it is the image of `b` fair coins (`exists_sampler`), at `ℓ¹` distance
`≤ 2|X|/2^b` from `p` (`d1_rnd_le`). The `ℓ¹` error of the state law grows by at most the per-round kernel error
per round (`d1_bind_le`), so the regret grows by at most `T²·(2n + 2|S|)/2^b < 1`.
-/

open scoped ENNReal
open Finset Pool.P0001

namespace Audit3

/-! ### Fair coins, coin-realisable laws, the strict target -/

/-- `b` fresh fair coins. -/
noncomputable def coins (b : ℕ) : PMF (Fin b → Bool) :=
  PMF.ofFintype (fun _ => ((Fintype.card (Fin b → Bool) : ℕ) : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _))

theorem coins_apply (b : ℕ) (ω : Fin b → Bool) : coins b ω = ((2 ^ b : ℕ) : ℝ≥0∞)⁻¹ := by
  simp [coins, PMF.ofFintype_apply]

/-- The law `p` is exactly the image of `b` fresh fair coins under a deterministic map. -/
def CoinReal {X : Type} (b : ℕ) (p : PMF X) : Prop := ∃ f : (Fin b → Bool) → X, p = (coins b).map f

/-- Every law of `M` (initial law, every action law, every next-state law) is realised by `b` fresh fair coins. -/
def Dyadic {n : ℕ} (M : Machine n) (b : ℕ) : Prop :=
  CoinReal b M.init ∧ (∀ t s, CoinReal b (M.act t s)) ∧ ∀ t s a l, CoinReal b (M.next t s a l)

/-- **Strict finite-precision target**: P0001's `MinimaxPolylogAchievable` plus: every law of `F n T` is realised
by `b ≤ Cb·log(nT)^kb` fresh fair coins. -/
def StrictMinimax : Prop :=
  ∃ F : Family, (∀ n T hn, (F n T hn).IsHomogeneous) ∧
    (∃ (C : ℝ) (k : ℕ), MemoryBound F C k) ∧
    (∃ (Cb : ℝ) (kb : ℕ), ∀ (n T : ℕ) (hn : 1 ≤ n), n ≤ T →
        ∃ b : ℕ, (b : ℝ) ≤ Cb * Real.log (n * T) ^ kb ∧ Dyadic (F n T hn) b) ∧
    ∃ (C' : ℝ) (k' : ℕ), RegretBound F fun n T => C' * Real.sqrt (n * T) * Real.log (n * T) ^ k'

theorem minimax_of_strict : StrictMinimax → MinimaxPolylogAchievable := by
  rintro ⟨F, h1, h2, -, h4⟩
  exact ⟨F, h1, h2, h4⟩

/-! ### Real-valued facts about laws on finite types -/

theorem sum_toReal {X : Type} [Fintype X] (p : PMF X) : ∑ x, (p x).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a),
    ← tsum_fintype (L := .unconditional _) (fun a => p a), PMF.tsum_coe, ENNReal.toReal_one]

theorem bind_toReal' {α β : Type} [Fintype α] (p : PMF α) (q : α → PMF β) (b : β) :
    ((p.bind q) b).toReal = ∑ a, (p a).toReal * (q a b).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp [ENNReal.toReal_mul]
  · intro a _; exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)

/-- `ℓ¹` distance of two laws on a finite type. -/
noncomputable def d1 {X : Type} [Fintype X] (p q : PMF X) : ℝ := ∑ x, |(p x).toReal - (q x).toReal|

/-- Composition with kernels: the `ℓ¹` error adds the worst kernel error. -/
theorem d1_bind_le {α β : Type} [Fintype α] [Fintype β] (p p' : PMF α) (K K' : α → PMF β) (ε : ℝ)
    (hK : ∀ a, d1 (K a) (K' a) ≤ ε) : d1 (p.bind K) (p'.bind K') ≤ d1 p p' + ε := by
  unfold d1
  simp only [bind_toReal']
  have key : ∀ x, |∑ a, (p a).toReal * (K a x).toReal - ∑ a, (p' a).toReal * (K' a x).toReal| ≤
      ∑ a, |(p a).toReal - (p' a).toReal| * (K a x).toReal +
        ∑ a, (p' a).toReal * |(K a x).toReal - (K' a x).toReal| := by
    intro x
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    have e : (p a).toReal * (K a x).toReal - (p' a).toReal * (K' a x).toReal =
        ((p a).toReal - (p' a).toReal) * (K a x).toReal +
          (p' a).toReal * ((K a x).toReal - (K' a x).toReal) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg (ENNReal.toReal_nonneg (a := K a x)),
      abs_of_nonneg (ENNReal.toReal_nonneg (a := p' a))]
  calc ∑ x, |∑ a, (p a).toReal * (K a x).toReal - ∑ a, (p' a).toReal * (K' a x).toReal|
      ≤ ∑ x, (∑ a, |(p a).toReal - (p' a).toReal| * (K a x).toReal +
          ∑ a, (p' a).toReal * |(K a x).toReal - (K' a x).toReal|) := Finset.sum_le_sum fun x _ => key x
    _ = ∑ a, |(p a).toReal - (p' a).toReal| * ∑ x, (K a x).toReal +
          ∑ a, (p' a).toReal * ∑ x, |(K a x).toReal - (K' a x).toReal| := by
        rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (f := fun x a => (p' a).toReal * _)]
        simp only [Finset.mul_sum]
    _ = ∑ a, |(p a).toReal - (p' a).toReal| + ∑ a, (p' a).toReal * d1 (K a) (K' a) := by
        simp only [sum_toReal, mul_one, d1]
    _ ≤ ∑ a, |(p a).toReal - (p' a).toReal| + ∑ a, (p' a).toReal * ε := by
        gcongr with a
        exact hK a
    _ = ∑ a, |(p a).toReal - (p' a).toReal| + ε := by rw [← Finset.sum_mul, sum_toReal, one_mul]

/-! ### Rounding a law to multiples of `2^{-b}` -/

section Round

variable {X : Type} [Fintype X]

open Classical in
/-- Integer counts: `⌊2^b p x⌋` off `x0`, the remainder at `x0`. -/
noncomputable def cnt (b : ℕ) (p : PMF X) (x0 x : X) : ℕ :=
  if x = x0 then 2 ^ b - ∑ y ∈ univ.erase x0, ⌊(2 : ℝ) ^ b * (p y).toReal⌋₊
  else ⌊(2 : ℝ) ^ b * (p x).toReal⌋₊

open Classical in
theorem sum_floor_le (b : ℕ) (p : PMF X) (x0 : X) :
    ∑ y ∈ univ.erase x0, ⌊(2 : ℝ) ^ b * (p y).toReal⌋₊ ≤ 2 ^ b := by
  have h : ((∑ y ∈ univ.erase x0, ⌊(2 : ℝ) ^ b * (p y).toReal⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ b := by
    push_cast
    calc ∑ y ∈ univ.erase x0, (⌊(2 : ℝ) ^ b * (p y).toReal⌋₊ : ℝ)
        ≤ ∑ y ∈ univ.erase x0, (2 : ℝ) ^ b * (p y).toReal :=
          Finset.sum_le_sum fun y _ => Nat.floor_le (by positivity)
      _ ≤ ∑ y, (2 : ℝ) ^ b * (p y).toReal :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun y _ _ => by positivity)
      _ = (2 : ℝ) ^ b := by rw [← Finset.mul_sum, sum_toReal, mul_one]
  exact_mod_cast h

open Classical in
theorem sum_cnt (b : ℕ) (p : PMF X) (x0 : X) : ∑ x, cnt b p x0 x = 2 ^ b := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x0)]
  have h2 : ∑ x ∈ univ.erase x0, cnt b p x0 x = ∑ y ∈ univ.erase x0, ⌊(2 : ℝ) ^ b * (p y).toReal⌋₊ :=
    Finset.sum_congr rfl fun x hx => by simp [cnt, Finset.ne_of_mem_erase hx]
  rw [h2]
  simp only [cnt, if_true]
  have := sum_floor_le b p x0
  omega

open Classical in
/-- The rounded law is within `2|X|/2^b` of `p` in `ℓ¹`. -/
theorem cnt_err (b : ℕ) (p : PMF X) (x0 : X) :
    ∑ x, |(cnt b p x0 x : ℝ) / 2 ^ b - (p x).toReal| ≤ 2 * Fintype.card X / 2 ^ b := by
  set N : ℝ := (2 : ℝ) ^ b with hN
  have hN0 : 0 < N := by positivity
  set e : X → ℝ := fun x => (cnt b p x0 x : ℝ) / N - (p x).toReal with he
  have hsum0 : ∑ x, e x = 0 := by
    have h1 : ∑ x, (cnt b p x0 x : ℝ) = N := by
      rw [hN]; exact_mod_cast sum_cnt b p x0
    simp only [he, Finset.sum_sub_distrib, ← Finset.sum_div, h1, div_self hN0.ne', sum_toReal, sub_self]
  have hoff : ∀ y ∈ univ.erase x0, |e y| ≤ 1 / N := by
    intro y hy
    have hy' : y ≠ x0 := Finset.ne_of_mem_erase hy
    have hc : (cnt b p x0 y : ℝ) = ⌊N * (p y).toReal⌋₊ := by simp [cnt, hy', hN]
    have h1 : (⌊N * (p y).toReal⌋₊ : ℝ) ≤ N * (p y).toReal := Nat.floor_le (by positivity)
    have h2 : N * (p y).toReal < ⌊N * (p y).toReal⌋₊ + 1 := Nat.lt_floor_add_one _
    have key : |(⌊N * (p y).toReal⌋₊ : ℝ) - N * (p y).toReal| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have ee : e y = ((⌊N * (p y).toReal⌋₊ : ℝ) - N * (p y).toReal) / N := by
      simp only [he, hc]; field_simp
    rw [ee, abs_div, abs_of_pos hN0]
    exact div_le_div_of_nonneg_right key hN0.le
  have hx0 : e x0 = -∑ y ∈ univ.erase x0, e y := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x0)] at hsum0
    linarith
  have hoffsum : ∑ y ∈ univ.erase x0, |e y| ≤ Fintype.card X * (1 / N) := by
    calc ∑ y ∈ univ.erase x0, |e y| ≤ ∑ _y ∈ univ.erase x0, 1 / N := Finset.sum_le_sum hoff
      _ = ((univ.erase x0).card : ℝ) * (1 / N) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card X * (1 / N) := by
          gcongr
          exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
  show ∑ x, |e x| ≤ _
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x0), hx0, abs_neg]
  have := Finset.abs_sum_le_sum_abs e (univ.erase x0)
  calc |∑ y ∈ univ.erase x0, e y| + ∑ y ∈ univ.erase x0, |e y|
      ≤ Fintype.card X * (1 / N) + Fintype.card X * (1 / N) := by linarith
    _ = 2 * Fintype.card X / N := by ring

/-- Any integer counts summing to `2^b` are realised exactly by `b` fair coins. -/
theorem exists_sampler (b : ℕ) (c : X → ℕ) (hc : ∑ x, c x = 2 ^ b) :
    ∃ f : (Fin b → Bool) → X, ∀ x, (((coins b).map f) x).toReal = (c x : ℝ) / 2 ^ b := by
  classical
  have hcard : Fintype.card (Fin b → Bool) = Fintype.card (Σ x, Fin (c x)) := by
    simp [Fintype.card_sigma, hc]
  let e := Fintype.equivOfCardEq hcard
  refine ⟨fun ω => (e ω).1, fun x => ?_⟩
  have hfib : (univ.filter fun ω : Fin b → Bool => x = (e ω).1).card = c x := by
    have h1 : (univ.filter fun ω : Fin b → Bool => x = (e ω).1).card =
        Fintype.card {ω : Fin b → Bool // (e ω).1 = x} := by
      rw [Fintype.card_subtype]; congr 1; ext ω; simp [eq_comm]
    rw [h1, Fintype.card_congr (e.subtypeEquiv (p := fun ω => (e ω).1 = x)
      (q := fun σ : (Σ x, Fin (c x)) => σ.1 = x) (fun ω => Iff.rfl)),
      Fintype.card_congr (Equiv.sigmaSubtype x), Fintype.card_fin]
  rw [PMF.map_apply, tsum_fintype]
  simp only [coins_apply]
  rw [← Finset.sum_filter, Finset.sum_const, hfib, nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_mul_inv]

/-- The rounded law: the image of `b` fair coins with counts `cnt b p x0`, `x0` a point of the support. -/
noncomputable def rnd (b : ℕ) (p : PMF X) : PMF X :=
  (coins b).map (Classical.choose (exists_sampler b (cnt b p p.support_nonempty.some)
    (sum_cnt b p p.support_nonempty.some)))

theorem rnd_coinReal (b : ℕ) (p : PMF X) : CoinReal b (rnd b p) := ⟨_, rfl⟩

theorem d1_rnd_le (b : ℕ) (p : PMF X) : d1 (rnd b p) p ≤ 2 * Fintype.card X / 2 ^ b := by
  have h := Classical.choose_spec (exists_sampler b (cnt b p p.support_nonempty.some)
    (sum_cnt b p p.support_nonempty.some))
  unfold d1 rnd
  simp only [h]
  exact cnt_err b p _

end Round

/-! ### Rounding a machine -/

section Machine

variable {n : ℕ}

/-- `M` with every law replaced by its `b`-coin rounding; same state set. -/
noncomputable def roundM (M : Machine n) (b : ℕ) : Machine n where
  State := M.State
  fintypeState := M.fintypeState
  init := rnd b M.init
  act t s := rnd b (M.act t s)
  next t s a l := rnd b (M.next t s a l)

theorem roundM_dyadic (M : Machine n) (b : ℕ) : Dyadic (roundM M b) b :=
  ⟨rnd_coinReal b _, fun _ _ => rnd_coinReal b _, fun _ _ _ _ => rnd_coinReal b _⟩

theorem roundM_hom (M : Machine n) (b : ℕ) (h : M.IsHomogeneous) : (roundM M b).IsHomogeneous := by
  refine ⟨fun t s => ?_, fun t s a l => ?_⟩
  · show rnd b (M.act t s) = rnd b (M.act 0 s)
    rw [h.1 t s]
  · show rnd b (M.next t s a l) = rnd b (M.next 0 s a l)
    rw [h.2 t s a l]

theorem roundM_memBits (M : Machine n) (b : ℕ) : (roundM M b).memBits = M.memBits := rfl

/-- The state law of the rounded machine drifts by at most `(t+1)·(εA + εS) - εA` after `t` rounds. -/
theorem d1_stateDist (M : Machine n) (b : ℕ) (ℓ : LossSeq n) :
    ∀ t : ℕ, d1 (X := M.State) ((roundM M b).stateDist ℓ t) (M.stateDist ℓ t) ≤
      2 * Fintype.card M.State / 2 ^ b + t * (2 * n / 2 ^ b + 2 * Fintype.card M.State / 2 ^ b) := by
  intro t
  induction t with
  | zero =>
    simp only [CharP.cast_eq_zero, zero_mul, add_zero]
    exact d1_rnd_le b M.init
  | succ t ih =>
    have hstep : ∀ s : M.State,
        d1 ((rnd b (M.act t s)).bind fun a => rnd b (M.next t s a (ℓ t a)))
          ((M.act t s).bind fun a => M.next t s a (ℓ t a)) ≤
          2 * n / 2 ^ b + 2 * Fintype.card M.State / 2 ^ b := by
      intro s
      refine (d1_bind_le _ _ _ _ _ fun a => d1_rnd_le b (M.next t s a (ℓ t a))).trans ?_
      have := d1_rnd_le b (M.act t s)
      simp only [Fintype.card_fin] at this
      linarith
    have := d1_bind_le (α := M.State) (β := M.State) ((roundM M b).stateDist ℓ t) (M.stateDist ℓ t) _ _ _ hstep
    refine this.trans ?_
    have h' := ih
    push_cast
    linarith

/-- Per-round expected losses differ by at most the `ℓ¹` error of the arm law. -/
theorem expLoss_round_le (M : Machine n) (b : ℕ) (ℓ : LossSeq n) (t : ℕ) :
    (roundM M b).expLoss ℓ t - M.expLoss ℓ t ≤ (t + 1) * (2 * n / 2 ^ b + 2 * Fintype.card M.State / 2 ^ b) := by
  have harm : d1 ((roundM M b).armDist ℓ t) (M.armDist ℓ t) ≤
      2 * Fintype.card M.State / 2 ^ b + t * (2 * n / 2 ^ b + 2 * Fintype.card M.State / 2 ^ b) +
        2 * n / 2 ^ b := by
    have h1 : ∀ s : M.State, d1 (rnd b (M.act t s)) (M.act t s) ≤ 2 * n / 2 ^ b := by
      intro s
      have := d1_rnd_le b (M.act t s)
      simpa only [Fintype.card_fin] using this
    have h2 := d1_bind_le (α := M.State) ((roundM M b).stateDist ℓ t) (M.stateDist ℓ t)
      (fun s => rnd b (M.act t s)) (fun s => M.act t s) _ h1
    have h3 := d1_stateDist M b ℓ t
    exact h2.trans (by linarith)
  have hdiff : (roundM M b).expLoss ℓ t - M.expLoss ℓ t ≤ d1 ((roundM M b).armDist ℓ t) (M.armDist ℓ t) := by
    unfold Machine.expLoss d1
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← sub_mul]
    have h01 : ((ℓ t a).toNat : ℝ) ≤ 1 := by cases ℓ t a <;> simp
    have h00 : (0 : ℝ) ≤ ((ℓ t a).toNat : ℝ) := by positivity
    calc (((roundM M b).armDist ℓ t a).toReal - (M.armDist ℓ t a).toReal) * ((ℓ t a).toNat : ℝ)
        ≤ |((roundM M b).armDist ℓ t a).toReal - (M.armDist ℓ t a).toReal| * ((ℓ t a).toNat : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h00
      _ ≤ |((roundM M b).armDist ℓ t a).toReal - (M.armDist ℓ t a).toReal| * 1 :=
          mul_le_mul_of_nonneg_left h01 (abs_nonneg _)
      _ = _ := mul_one _
  refine hdiff.trans (harm.trans (le_of_eq ?_))
  ring

/-- **Regret of the rounded machine**: at most the original regret plus `T²(2n + 2|S|)/2^b`. -/
theorem regret_round_le (M : Machine n) (b : ℕ) (ℓ : LossSeq n) (T : ℕ) :
    regret (roundM M b) ℓ T ≤ regret M ℓ T + (T : ℝ) ^ 2 * ((2 * n + 2 * Fintype.card M.State) / 2 ^ b) := by
  unfold regret
  have hsum : ∑ t ∈ Finset.range T, (roundM M b).expLoss ℓ t - ∑ t ∈ Finset.range T, M.expLoss ℓ t ≤
      (T : ℝ) ^ 2 * ((2 * n + 2 * Fintype.card M.State) / 2 ^ b) := by
    rw [← Finset.sum_sub_distrib]
    set E : ℝ := 2 * n / 2 ^ b + 2 * Fintype.card M.State / 2 ^ b with hE
    have hE0 : 0 ≤ E := by positivity
    calc ∑ t ∈ Finset.range T, ((roundM M b).expLoss ℓ t - M.expLoss ℓ t)
        ≤ ∑ _t ∈ Finset.range T, (T : ℝ) * E := by
          refine Finset.sum_le_sum fun t ht => (expLoss_round_le M b ℓ t).trans ?_
          have : (t : ℝ) + 1 ≤ T := by
            have := Finset.mem_range.1 ht
            exact_mod_cast this
          exact mul_le_mul_of_nonneg_right this hE0
      _ = (T : ℝ) ^ 2 * ((2 * n + 2 * Fintype.card M.State) / 2 ^ b) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hE]; ring
  linarith

end Machine

/-! ### The transfer theorem -/

/-- The one-state machine pulling arm `0`, with `0` coins. -/
noncomputable def trivM (n : ℕ) (hn : 1 ≤ n) : Machine n where
  State := Unit
  init := PMF.pure ()
  act _ _ := PMF.pure ⟨0, hn⟩
  next _ _ _ _ := PMF.pure ()

theorem pure_coinReal {X : Type} (x : X) : CoinReal 0 (PMF.pure x) :=
  ⟨fun _ => x, (PMF.map_const (coins 0) x).symm⟩

theorem trivM_dyadic (n : ℕ) (hn : 1 ≤ n) : Dyadic (trivM n hn) 0 :=
  ⟨pure_coinReal _, fun _ _ => pure_coinReal _, fun _ _ _ _ => pure_coinReal _⟩

theorem trivM_hom (n : ℕ) (hn : 1 ≤ n) : (trivM n hn).IsHomogeneous := ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem trivM_memBits (n : ℕ) (hn : 1 ≤ n) : (trivM n hn).memBits = 0 := by
  show Real.logb 2 (Fintype.card Unit) = 0
  simp

/-- With one arm every machine has regret `0` (as in P0161's `regret_one`). -/
theorem regret_one' (M : Machine 1) (ℓ : LossSeq 1) (T : ℕ) : regret M ℓ T = 0 := by
  have hE : ∀ t, M.expLoss ℓ t = ((ℓ t 0).toNat : ℝ) := by
    intro t
    rw [Machine.expLoss, Fin.sum_univ_one]
    have h1 : (M.armDist ℓ t 0) = 1 := by
      have := (M.armDist ℓ t).tsum_coe
      rwa [tsum_fintype, Fin.sum_univ_one] at this
    rw [h1]; simp
  have hB : bestLoss ℓ T = cumLoss ℓ T 0 := by
    rw [bestLoss]
    exact le_antisymm (ciInf_le (Set.finite_range _).bddBelow 0)
      (le_ciInf fun i => by rw [Fin.fin_one_eq_zero i])
  rw [regret, hB, cumLoss]
  simp only [hE]
  ring

/-- The number of coins used for `(n, T)` and a machine with state set `S`. -/
noncomputable def bitsOf (n T cS : ℕ) : ℕ := Nat.log 2 (T ^ 2 * (2 * n + 2 * cS)) + 1

theorem lt_two_pow_bitsOf (n T cS : ℕ) : T ^ 2 * (2 * n + 2 * cS) < 2 ^ bitsOf n T cS :=
  Nat.lt_pow_succ_log_self (by norm_num) _

/-- `log(nT) ≥ 1` once `2 ≤ n ≤ T`. -/
theorem one_le_log {n T : ℕ} (h2 : 2 ≤ n) (hnT : n ≤ T) : 1 ≤ Real.log ((n : ℝ) * T) := by
  have h4 : (4 : ℝ) ≤ (n : ℝ) * T := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast h2
    have : (n : ℝ) ≤ T := by exact_mod_cast hnT
    nlinarith
  have he : Real.exp 1 ≤ 4 := by
    have := Real.exp_one_lt_d9; linarith
  calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log ((n : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) (he.trans h4)

/-- The coin count is `≤ 3 + 4·log(nT) + memBits`. -/
theorem bitsOf_le {n T cS : ℕ} (h2 : 2 ≤ n) (hnT : n ≤ T) (hS : 1 ≤ cS) :
    (bitsOf n T cS : ℝ) ≤ 3 + 4 * Real.log ((n : ℝ) * T) + Real.logb 2 cS := by
  have hT : 1 ≤ T := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hS0 : (0 : ℝ) < cS := by exact_mod_cast hS
  set m : ℕ := T ^ 2 * (2 * n + 2 * cS) with hm
  have hm0 : (0 : ℝ) < m := by rw [hm]; push_cast; positivity
  have hlog : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := by exact_mod_cast Real.natLog_le_logb m 2
  -- m ≤ 4·(nT)²·|S|
  have hmle : (m : ℝ) ≤ 4 * ((n : ℝ) * T) ^ 2 * cS := by
    rw [hm]; push_cast
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hS1 : (1 : ℝ) ≤ cS := by exact_mod_cast hS
    have h1 : 2 * (n : ℝ) + 2 * cS ≤ 4 * n * cS := by nlinarith
    have h2 : (T : ℝ) ^ 2 * (2 * n + 2 * cS) ≤ T ^ 2 * (4 * n * cS) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (T : ℝ) ^ 2 * (4 * n * cS) ≤ 4 * ((n : ℝ) * T) ^ 2 * cS := by
      have : (T : ℝ) ^ 2 * n ≤ ((n : ℝ) * T) ^ 2 := by nlinarith
      nlinarith
    linarith
  have hlb : Real.logb 2 m ≤ 2 + 2 * Real.logb 2 ((n : ℝ) * T) + Real.logb 2 cS := by
    calc Real.logb 2 m ≤ Real.logb 2 (4 * ((n : ℝ) * T) ^ 2 * cS) :=
          Real.logb_le_logb_of_le (by norm_num) hm0 hmle
      _ = Real.logb 2 4 + 2 * Real.logb 2 ((n : ℝ) * T) + Real.logb 2 cS := by
          rw [Real.logb_mul (by positivity) hS0.ne', Real.logb_mul (by norm_num) (by positivity),
            Real.logb_pow]
          push_cast; ring
      _ = 2 + 2 * Real.logb 2 ((n : ℝ) * T) + Real.logb 2 cS := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.logb_pow]
          simp
  have hl2 : Real.logb 2 ((n : ℝ) * T) ≤ 2 * Real.log ((n : ℝ) * T) := by
    have hl0 : 0 ≤ Real.log ((n : ℝ) * T) := (zero_le_one.trans (one_le_log h2 hnT))
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    nlinarith
  unfold bitsOf
  push_cast
  rw [← hm]
  linarith

/-- The rounded family: for `2 ≤ n ≤ T`, `F n T` with every law rounded to `bitsOf n T |S|` fair coins; the
one-state machine otherwise. -/
noncomputable def roundFam (F : Family) : Family := fun n T hn =>
  if 2 ≤ n ∧ n ≤ T then roundM (F n T hn) (bitsOf n T (Fintype.card (F n T hn).State)) else trivM n hn

/-- **Rounding a family.** Homogeneity is kept, memory is kept (`max C 0`), every law becomes a `b`-coin law with
`b ≤ (7 + max C 0)·log(nT)^(k+1)`, and the regret constant grows from `C'` to `max C' 0 + 1`. -/
theorem roundFam_spec (F : Family) (hhom : ∀ n T hn, (F n T hn).IsHomogeneous) {C : ℝ} {k : ℕ}
    (hmem : MemoryBound F C k) {C' : ℝ} {k' : ℕ}
    (hreg : RegretBound F fun n T => C' * Real.sqrt (n * T) * Real.log (n * T) ^ k') :
    (∀ n T hn, (roundFam F n T hn).IsHomogeneous) ∧ MemoryBound (roundFam F) (max C 0) k ∧
      (∀ (n T : ℕ) (hn : 1 ≤ n), n ≤ T →
        ∃ b : ℕ, (b : ℝ) ≤ (7 + max C 0) * Real.log (n * T) ^ (k + 1) ∧ Dyadic (roundFam F n T hn) b) ∧
      RegretBound (roundFam F) fun n T => (max C' 0 + 1) * Real.sqrt (n * T) * Real.log (n * T) ^ k' := by
  classical
  set G := roundFam F
  have hG1 : ∀ n T hn (h : 2 ≤ n ∧ n ≤ T),
      G n T hn = roundM (F n T hn) (bitsOf n T (Fintype.card (F n T hn).State)) := by
    intro n T hn h; simp only [G, roundFam, if_pos h]
  have hG2 : ∀ n T hn (h : ¬ (2 ≤ n ∧ n ≤ T)), G n T hn = trivM n hn := by
    intro n T hn h; simp only [G, roundFam, if_neg h]
  have hlog0 : ∀ n T : ℕ, 1 ≤ n → n ≤ T → 0 ≤ Real.log ((n : ℝ) * T) := by
    intro n T hn hnT
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) ≤ T := by exact_mod_cast (le_trans hn hnT)
    nlinarith
  have hcard : ∀ {m : ℕ} (M : Machine m), 1 ≤ Fintype.card M.State := by
    intro m M
    obtain ⟨s, -⟩ := M.init.support_nonempty
    exact Fintype.card_pos_iff.2 ⟨s⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- homogeneity
    intro n T hn
    by_cases h : 2 ≤ n ∧ n ≤ T
    · rw [hG1 n T hn h]; exact roundM_hom _ _ (hhom n T hn)
    · rw [hG2 n T hn h]; exact trivM_hom n hn
  · -- memory: unchanged
    intro n T hn hnT
    have hL := pow_nonneg (hlog0 n T hn hnT) k
    by_cases h : 2 ≤ n ∧ n ≤ T
    · rw [hG1 n T hn h, roundM_memBits]
      exact (hmem n T hn hnT).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hL)
    · rw [hG2 n T hn h, trivM_memBits]; exact mul_nonneg (le_max_right _ _) hL
  · -- coins per law
    intro n T hn hnT
    by_cases h : 2 ≤ n ∧ n ≤ T
    · refine ⟨bitsOf n T (Fintype.card (F n T hn).State), ?_, ?_⟩
      · have hb := bitsOf_le h.1 hnT (hcard (F n T hn))
        have hm := hmem n T hn hnT
        have hL1 := one_le_log h.1 hnT
        set L := Real.log ((n : ℝ) * T)
        have hLk : L ^ k ≤ L ^ (k + 1) := pow_le_pow_right₀ hL1 (Nat.le_succ k)
        have hL1k : 1 ≤ L ^ (k + 1) := one_le_pow₀ hL1
        have hLL : L ≤ L ^ (k + 1) := by
          calc L = L ^ 1 := (pow_one L).symm
            _ ≤ L ^ (k + 1) := pow_le_pow_right₀ hL1 (by omega)
        have hmb : Real.logb 2 (Fintype.card (F n T hn).State) ≤ max C 0 * L ^ (k + 1) := by
          have : (F n T hn).memBits = Real.logb 2 (Fintype.card (F n T hn).State) := rfl
          rw [← this]
          refine hm.trans ?_
          calc C * L ^ k ≤ max C 0 * L ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _)
                (pow_nonneg (by linarith) k)
            _ ≤ max C 0 * L ^ (k + 1) := mul_le_mul_of_nonneg_left hLk (le_max_right _ _)
        nlinarith
      · rw [hG1 n T hn h]; exact roundM_dyadic _ _
    · refine ⟨0, ?_, ?_⟩
      · have := pow_nonneg (hlog0 n T hn hnT) (k + 1)
        simp only [CharP.cast_eq_zero]
        exact mul_nonneg (by positivity) this
      · rw [hG2 n T hn h]; exact trivM_dyadic n hn
  · -- regret: + 1
    intro n T hn hnT ℓ
    by_cases h : 2 ≤ n ∧ n ≤ T
    · rw [hG1 n T hn h]
      have hr := regret_round_le (F n T hn) (bitsOf n T (Fintype.card (F n T hn).State)) ℓ T
      have hlt := lt_two_pow_bitsOf n T (Fintype.card (F n T hn).State)
      have hsmall : (T : ℝ) ^ 2 * ((2 * n + 2 * Fintype.card (F n T hn).State) /
          2 ^ bitsOf n T (Fintype.card (F n T hn).State)) ≤ 1 := by
        rw [mul_div_assoc', div_le_one (by positivity)]
        exact_mod_cast hlt.le
      have hR := hreg n T hn hnT ℓ
      have hL1 := one_le_log h.1 hnT
      have hsq : 1 ≤ Real.sqrt ((n : ℝ) * T) := by
        rw [Real.one_le_sqrt]
        have : (2 : ℝ) ≤ n := by exact_mod_cast h.1
        have : (n : ℝ) ≤ T := by exact_mod_cast hnT
        nlinarith
      have hX : 1 ≤ Real.sqrt ((n : ℝ) * T) * Real.log ((n : ℝ) * T) ^ k' :=
        one_le_mul_of_one_le_of_one_le hsq (one_le_pow₀ hL1)
      have hC : C' * Real.sqrt (n * T) * Real.log (n * T) ^ k' ≤
          max C' 0 * (Real.sqrt ((n : ℝ) * T) * Real.log ((n : ℝ) * T) ^ k') := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
      calc regret (roundM (F n T hn) _) ℓ T ≤ regret (F n T hn) ℓ T + 1 := by linarith
        _ ≤ max C' 0 * (Real.sqrt ((n : ℝ) * T) * Real.log ((n : ℝ) * T) ^ k') +
              1 * (Real.sqrt ((n : ℝ) * T) * Real.log ((n : ℝ) * T) ^ k') := by linarith
        _ = (max C' 0 + 1) * Real.sqrt (n * T) * Real.log (n * T) ^ k' := by ring
    · rw [hG2 n T hn h]
      have hn1 : n = 1 := by omega
      subst hn1
      rw [regret_one']
      have h0 := hlog0 1 T le_rfl hnT
      exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (pow_nonneg h0 k')

end Audit3

namespace Audit3

/-- **Transfer theorem.** P0001's target (real-valued laws) implies the strict finite-precision target. -/
theorem strict_of_minimax : MinimaxPolylogAchievable → StrictMinimax := by
  rintro ⟨F, hhom, ⟨C, k, hmem⟩, C', k', hreg⟩
  obtain ⟨h1, h2, h3, h4⟩ := roundFam_spec F hhom hmem hreg
  exact ⟨roundFam F, h1, ⟨_, _, h2⟩, ⟨_, _, h3⟩, ⟨_, _, h4⟩⟩

/-- **The pool's final theorem, upgraded**: the strict finite-precision target holds. -/
theorem pool_strict : StrictMinimax := strict_of_minimax Pool.P0294.main

end Audit3

#print axioms Audit3.strict_of_minimax
#print axioms Audit3.pool_strict

/-! ## The explicit family of the final proof, rounded to fair coins -/

namespace Audit3

open Pool.P0001

/-- **The explicit construction meets the strict model.** `roundFam Audit3E.famE` (the pool's algorithm written
down as definitions, every law rounded to `b`-bit dyadic) is homogeneous, has polylogarithmic memory, uses
`b ≤ C·log(nT)^(kE+2)` fresh fair coins per law, and has `Õ(√(nT))` regret, for all `1 ≤ n ≤ T`. -/
theorem famE_strict :
    (∀ n T hn, (roundFam Audit3E.famE n T hn).IsHomogeneous) ∧
      MemoryBound (roundFam Audit3E.famE) (max (2 * max Audit3E.cE 1 * 2 ^ Audit3E.kE) 0) (Audit3E.kE + 1) ∧
      (∀ (n T : ℕ) (hn : 1 ≤ n), n ≤ T →
        ∃ b : ℕ, (b : ℝ) ≤ (7 + max (2 * max Audit3E.cE 1 * 2 ^ Audit3E.kE) 0) *
          Real.log (n * T) ^ (Audit3E.kE + 1 + 1) ∧ Dyadic (roundFam Audit3E.famE n T hn) b) ∧
      RegretBound (roundFam Audit3E.famE) fun n T =>
        (max (12 * max Audit3E.cE 1 ^ 2 * 4 ^ Audit3E.kE) 0 + 1) * Real.sqrt (n * T) *
          Real.log (n * T) ^ (2 * Audit3E.kE) :=
  roundFam_spec Audit3E.famE Audit3E.famE_spec.1 Audit3E.famE_spec.2.1 Audit3E.famE_spec.2.2

theorem famE_strict_target : StrictMinimax :=
  ⟨roundFam Audit3E.famE, famE_strict.1, ⟨_, _, famE_strict.2.1⟩, ⟨_, _, famE_strict.2.2.1⟩,
    ⟨_, _, famE_strict.2.2.2⟩⟩

end Audit3

#print axioms Audit3.famE_strict
#print axioms Audit3.famE_strict_target

/-! ## Choice scan -/

/-!
# Choice scan: does the one-level machine `machF` (and what it is built from) pick anything by choice?

Walks the definitional closure of a root definition, following only constants in the `Pool` namespace that are
definitions (`defnInfo`, i.e. data, not theorems), and reports every direct use of a witness-choice primitive
(`Classical.choose`, `Classical.epsilon`, `Exists.choose`, `Nonempty.some`, `Set.Nonempty.some`,
`Classical.arbitrary`, `Classical.indefiniteDescription`, `Fintype.equivOfCardEq`, `Classical.choice` used directly).
Classical *decidability* (`Classical.propDecidable`, `Classical.dec*`) is reported separately: it does not pick a
witness (the value of an `if` is determined), it only makes the definition non-executable.
-/

open Lean Meta Elab Command

def witnessChoice : List Name :=
  [``Classical.choose, ``Classical.epsilon, ``Exists.choose, ``Nonempty.some, ``Set.Nonempty.some,
   ``Classical.arbitrary, ``Classical.indefiniteDescription, ``Fintype.equivOfCardEq, ``Classical.choice,
   ``Classical.indefiniteDescription]

def classicalDec : List Name :=
  [``Classical.propDecidable, ``Classical.dec, ``Classical.decEq, ``Classical.decPred, ``Classical.decRel,
   ``Classical.typeDecidableEq, ``Classical.typeDecidable]

def isPool (n : Name) : Bool := n.getRoot == `Pool || n.getRoot == `Audit3E || n.getRoot == `Audit3

def scan (root : Name) : CoreM (Nat × Array (Name × Name) × Array (Name × Name)) := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut stack : Array Name := #[root]
  let mut hits : Array (Name × Name) := #[]
  let mut dec : Array (Name × Name) := #[]
  let mut ndefs := 0
  while stack.size > 0 do
    let c := stack.back!
    stack := stack.pop
    if visited.contains c then continue
    visited := visited.insert c
    match env.find? c with
    | some (.defnInfo d) =>
      ndefs := ndefs + 1
      let used := d.value.getUsedConstants ++ d.type.getUsedConstants
      for u in used do
        if witnessChoice.contains u then hits := hits.push (c, u)
        if classicalDec.contains u then dec := dec.push (c, u)
        if isPool u && !visited.contains u then stack := stack.push u
    | some (.opaqueInfo d) =>
      ndefs := ndefs + 1
      for u in d.value.getUsedConstants do
        if witnessChoice.contains u then hits := hits.push (c, u)
        if isPool u && !visited.contains u then stack := stack.push u
    | some (.ctorInfo _) | some (.inductInfo _) | some (.recInfo _) | some (.thmInfo _)
    | some (.axiomInfo _) | some (.quotInfo _) | none => pure ()
  return (ndefs, hits, dec)

elab "audit3_choice_scan " id:ident : command => do
  let root := id.getId
  let (nd, hits, dec) ← liftCoreM (scan root)
  logInfo m!"root {root}: {nd} Pool definitions in the definitional closure"
  logInfo m!"witness-choice uses ({hits.size}): {hits.toList}"
  let decDefs := (dec.map (·.1)).toList.eraseDups
  logInfo m!"classical-decidability uses in {decDefs.length} definitions"

audit3_choice_scan Pool.P0284.machF
audit3_choice_scan Pool.P0284.famM
audit3_choice_scan Pool.P0201.mach
audit3_choice_scan Pool.P0050.CoinAlg.toMachine
audit3_choice_scan Audit3E.famE
audit3_choice_scan Audit3.roundFam

/-! ## With the proof's constants the explicit machine is "always pull arm 0" for every `T ≤ 10^150` -/

namespace Audit3E

open Pool.P0001 Pool.P0050 Pool.P0161 Pool.P0173

theorem cE_ge : (10 : ℝ) ^ 37 ≤ cE := by
  have h1 : (10 : ℝ) ^ 37 ≤ Pool.P0292.CF Cg0 := by
    unfold Pool.P0292.CF Cg0
    rw [max_eq_left (by positivity)]
    norm_num
  exact h1.trans (by unfold cE; linarith [le_max_left (Pool.P0292.CF Cg0) 0])

theorem famE_trivial {n T : ℕ} (hn : 1 ≤ n) (h2 : 2 ≤ n) (hnT : n ≤ T) (hT : (T : ℝ) ≤ 10 ^ 150) :
    famE n T hn = (trivCoin n hn).toMachine := by
  have hL : (10 : ℝ) ^ 37 ≤ Lam cE kE n T := by
    unfold Lam
    have hLg : 1 ≤ Lg n T ^ kE := one_le_pow₀ (one_le_Lg hn (by omega))
    calc (10 : ℝ) ^ 37 ≤ cE := cE_ge
      _ ≤ max cE 1 := le_max_left _ _
      _ = max cE 1 * 1 := (mul_one _).symm
      _ ≤ max cE 1 * Lg n T ^ kE := mul_le_mul_of_nonneg_left hLg (by positivity)
  have hsmall : (T : ℝ) ≤ (12 * Lam cE kE n T ^ 2) ^ 2 * n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : (10 : ℝ) ^ 74 ≤ Lam cE kE n T ^ 2 := by
      calc (10 : ℝ) ^ 74 = ((10 : ℝ) ^ 37) ^ 2 := by norm_num
        _ ≤ Lam cE kE n T ^ 2 := pow_le_pow_left₀ (by positivity) hL 2
    have h2' : (10 : ℝ) ^ 150 ≤ (12 * Lam cE kE n T ^ 2) ^ 2 := by
      calc (10 : ℝ) ^ 150 ≤ (12 * (10 : ℝ) ^ 74) ^ 2 := by norm_num
        _ ≤ (12 * Lam cE kE n T ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h3 : (12 * Lam cE kE n T ^ 2) ^ 2 ≤ (12 * Lam cE kE n T ^ 2) ^ 2 * n := by
      have : (0 : ℝ) ≤ (12 * Lam cE kE n T ^ 2) ^ 2 := by positivity
      nlinarith
    linarith
  show (if 2 ≤ n ∧ n ≤ T then (algR cE kE n hn (stepE n hn) T).toMachine else triv n hn) = _
  rw [if_pos ⟨h2, hnT⟩, algR, dif_pos (Or.inr hsmall)]

end Audit3E

#print axioms Audit3E.famE_trivial

/-! ## Sanity: `CoinReal` really means "dyadic with denominator `2^b`", and it is a real restriction -/

namespace Audit3

open Finset

theorem coinReal_dyadic {X : Type} [Fintype X] {b : ℕ} {p : PMF X} (h : CoinReal b p) (x : X) :
    ∃ m : ℕ, (p x).toReal = m / 2 ^ b := by
  classical
  obtain ⟨f, rfl⟩ := h
  refine ⟨(univ.filter fun ω : Fin b → Bool => x = f ω).card, ?_⟩
  rw [PMF.map_apply, tsum_fintype]
  simp only [coins_apply]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
  simp [div_eq_mul_inv]

/-- A coin of bias `1/3` is not realisable by any finite number of fair coins (so `Dyadic` is a genuine
restriction on P0001's real-valued laws). -/
theorem not_coinReal_third (p : PMF Bool) (hp : (p true).toReal = 1 / 3) (b : ℕ) : ¬ CoinReal b p := by
  intro h
  obtain ⟨m, hm⟩ := coinReal_dyadic h true
  rw [hp] at hm
  have h2 : (0 : ℝ) < 2 ^ b := by positivity
  have hr : ((2 ^ b : ℕ) : ℝ) = ((3 * m : ℕ) : ℝ) := by
    push_cast
    field_simp at hm
    linarith
  have hn : 2 ^ b = 3 * m := by exact_mod_cast hr
  have h3 : 3 ∣ 2 ^ b := ⟨m, hn⟩
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

end Audit3

#print axioms Audit3.coinReal_dyadic
#print axioms Audit3.not_coinReal_third

/-! ## Part 4: bridge to the fair-coin reference model

`StrictMinimax` (P0001 semantics, every law the image of `b` fair coins) implies `StrictTarget` of `RefModel`
: one deterministic initial state, time-homogeneous maps driven by `b' = 3b` fresh
fair coins per round, expectation = plain average over all coin tapes. The machine for `(n, T)` has state set
`Option S` (`none` = before the first round; the first round draws the initial state from its own coins).
-/

namespace Audit3

open Pool.P0001 Finset

/-! ### Tape lemmas -/

theorem sum_resample {X : Type} [Fintype X] {T : ℕ} (f : (Fin T → X) → ℝ) (t : Fin T) :
    (Fintype.card X : ℝ) * ∑ ω, f ω = ∑ ω, ∑ x, f (Function.update ω t x) := by
  classical
  let e := Equiv.funSplitAt t X
  have hupd : ∀ (y x : X) (g : {j // j ≠ t} → X),
      Function.update (e.symm (y, g)) t x = e.symm (x, g) := by
    intro y x g; funext j
    by_cases hj : j = t
    · subst hj; simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, Function.update, hj]
  rw [← e.symm.sum_comp, ← e.symm.sum_comp (fun ω => ∑ x, f (Function.update ω t x))]
  simp only [Fintype.sum_prod_type, hupd]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm]

variable {n T : ℕ}

theorem stateAt_update (C : CoinMachine n) (ℓ : Losses n T) (ω : Tape C.b T) (t' : Fin T)
    (x : Fin C.b → Bool) : ∀ t, t ≤ t'.val → stateAt C ℓ (Function.update ω t' x) t = stateAt C ℓ ω t
  | 0, _ => rfl
  | s + 1, h => by
    have ih := stateAt_update C ℓ ω t' x s (by omega)
    simp only [stateAt]
    split_ifs with hs
    · have hne : (⟨s, hs⟩ : Fin T) ≠ t' := by
        intro e; rw [← e] at h; simp at h
      rw [ih, Function.update_of_ne hne]
    · exact ih

/-- Average over one round's coins. -/
noncomputable def avgC (b : ℕ) (g : (Fin b → Bool) → ℝ) : ℝ := (∑ c, g c) / Fintype.card (Fin b → Bool)

/-- The law of the state, as an expectation functional, by forward recursion. -/
noncomputable def lawE (C : CoinMachine n) (ℓ : Losses n T) : ℕ → (C.S → ℝ) → ℝ
  | 0, Φ => Φ C.init
  | t + 1, Φ =>
    if h : t < T then lawE C ℓ t (fun s => avgC C.b (fun c => Φ (C.next s c (ℓ ⟨t, h⟩ (C.act s c)))))
    else lawE C ℓ t Φ

theorem sum_eq_card_avg (b : ℕ) (g : (Fin b → Bool) → ℝ) :
    ∑ c, g c = (Fintype.card (Fin b → Bool) : ℝ) * avgC b g := by
  unfold avgC
  have : (0 : ℝ) < Fintype.card (Fin b → Bool) := by exact_mod_cast Fintype.card_pos
  field_simp

/-- **Tape average = forward recursion** (Markov property of fresh coins). -/
theorem tape_law (C : CoinMachine n) (ℓ : Losses n T) :
    ∀ t, t ≤ T → ∀ Φ : C.S → ℝ,
      ∑ ω : Tape C.b T, Φ (stateAt C ℓ ω t) = (Fintype.card (Tape C.b T) : ℝ) * lawE C ℓ t Φ := by
  intro t
  induction t with
  | zero => intro _ Φ; simp [stateAt, lawE, Finset.sum_const, Finset.card_univ]
  | succ t ih =>
    intro hT Φ
    have ht : t < T := by omega
    set tt : Fin T := ⟨t, ht⟩
    have hX : (0 : ℝ) < Fintype.card (Fin C.b → Bool) := by exact_mod_cast Fintype.card_pos
    have key : (Fintype.card (Fin C.b → Bool) : ℝ) * ∑ ω : Tape C.b T, Φ (stateAt C ℓ ω (t + 1)) =
        (Fintype.card (Fin C.b → Bool) : ℝ) * ∑ ω : Tape C.b T,
          avgC C.b (fun c => Φ (C.next (stateAt C ℓ ω t) c (ℓ tt (C.act (stateAt C ℓ ω t) c)))) := by
      have e1 : ∀ ω : Tape C.b T, stateAt C ℓ ω (t + 1) =
          C.next (stateAt C ℓ ω t) (ω tt) (ℓ tt (C.act (stateAt C ℓ ω t) (ω tt))) := by
        intro ω; simp [stateAt, ht, tt]
      simp only [e1]
      rw [sum_resample (fun ω => Φ (C.next (stateAt C ℓ ω t) (ω tt) (ℓ tt (C.act (stateAt C ℓ ω t) (ω tt))))) tt]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [← sum_eq_card_avg]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [stateAt_update C ℓ ω tt x t le_rfl, Function.update_self]
    have key' := mul_left_cancel₀ hX.ne' key
    have h2 := ih (by omega) (fun s => avgC C.b (fun c => Φ (C.next s c (ℓ tt (C.act s c)))))
    rw [key']
    refine h2.trans ?_
    rw [lawE, dif_pos ht]

/-- Expected loss of round `t` through the forward recursion. -/
theorem tape_round (C : CoinMachine n) (ℓ : Losses n T) (tt : Fin T) :
    ∑ ω : Tape C.b T, (lv (ℓ tt (armAt C ℓ ω tt)) : ℝ) =
      (Fintype.card (Tape C.b T) : ℝ) * lawE C ℓ tt (fun s => avgC C.b (fun c => (lv (ℓ tt (C.act s c)) : ℝ))) := by
  have hX : (0 : ℝ) < Fintype.card (Fin C.b → Bool) := by exact_mod_cast Fintype.card_pos
  have key : (Fintype.card (Fin C.b → Bool) : ℝ) * ∑ ω : Tape C.b T, (lv (ℓ tt (armAt C ℓ ω tt)) : ℝ) =
      (Fintype.card (Fin C.b → Bool) : ℝ) * ∑ ω : Tape C.b T,
        avgC C.b (fun c => (lv (ℓ tt (C.act (stateAt C ℓ ω tt) c)) : ℝ)) := by
    unfold armAt
    rw [sum_resample (fun ω => (lv (ℓ tt (C.act (stateAt C ℓ ω tt) (ω tt))) : ℝ)) tt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [← sum_eq_card_avg]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [stateAt_update C ℓ ω tt x tt le_rfl, Function.update_self]
  rw [mul_left_cancel₀ hX.ne' key]
  exact tape_law C ℓ tt (le_of_lt tt.2) (fun s => avgC C.b (fun c => (lv (ℓ tt (C.act s c)) : ℝ)))

/-! ### From a dyadic P0001 machine to a fair-coin coin machine -/

/-- Split `m + k` coins into `m` and `k`. -/
def split2 (m k : ℕ) : (Fin (m + k) → Bool) ≃ (Fin m → Bool) × (Fin k → Bool) :=
  (finSumFinEquiv.symm.arrowCongr (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)

/-- Split `3b` coins into three blocks of `b`. -/
def split3 (b : ℕ) : (Fin (b + b + b) → Bool) ≃ ((Fin b → Bool) × (Fin b → Bool)) × (Fin b → Bool) :=
  (split2 (b + b) b).trans (Equiv.prodCongr (split2 b b) (Equiv.refl _))

theorem card_coins (b : ℕ) : (Fintype.card (Fin b → Bool) : ℝ) = 2 ^ b := by
  simp [Fintype.card_fun]

theorem avgC_split3 (b : ℕ) (g : (Fin b → Bool) → (Fin b → Bool) → (Fin b → Bool) → ℝ) :
    avgC (b + b + b) (fun c => g (split3 b c).1.1 (split3 b c).1.2 (split3 b c).2) =
      avgC b (fun c0 => avgC b (fun c1 => avgC b (fun c2 => g c0 c1 c2))) := by
  unfold avgC
  rw [← (split3 b).symm.sum_comp]
  simp only [Equiv.apply_symm_apply, Fintype.sum_prod_type]
  rw [card_coins, card_coins]
  simp only [← Finset.sum_div]
  rw [div_div, div_div]
  congr 1
  ring

/-- Resolve the stored state (`none` = draw the initial state from coins). -/
def res {S : Type} {b : ℕ} (fi : (Fin b → Bool) → S) : Option S → (Fin b → Bool) → S
  | none, c0 => fi c0
  | some s, _ => s

/-- The fair-coin coin machine of a dyadic P0001 machine with samplers `fi`, `fa`, `fn`. -/
noncomputable def toCoinM {S : Type} [Fintype S] (b : ℕ) (fi : (Fin b → Bool) → S)
    (fa : S → (Fin b → Bool) → Fin n) (fn : S → Fin n → Bool → (Fin b → Bool) → S) : CoinMachine n where
  S := Option S
  b := b + b + b
  init := none
  act s c := fa (res fi s (split3 b c).1.1) (split3 b c).1.2
  next s c l := some (fn (res fi s (split3 b c).1.1) (fa (res fi s (split3 b c).1.1) (split3 b c).1.2) l
    (split3 b c).2)

/-- Extension of a finite loss table to P0001's loss sequences (zero after the horizon). -/
def extL (ℓ : Losses n T) : LossSeq n := fun t i => if h : t < T then ℓ ⟨t, h⟩ i else false

theorem coins_toReal (b : ℕ) (c : Fin b → Bool) : (coins b c).toReal = 1 / 2 ^ b := by
  rw [coins_apply]; simp

/-- Expectation under the image of fair coins is the coin average. -/
theorem exp_map_coins {X : Type} [Fintype X] (b : ℕ) (f : (Fin b → Bool) → X) (F : X → ℝ) :
    ∑ x, (((coins b).map f) x).toReal * F x = avgC b (fun c => F (f c)) := by
  rw [Pool.P0050.sum_map_toReal]
  unfold avgC
  simp only [coins_toReal, card_coins]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun c _ => by ring

section Dy

variable (M : Machine n) (b : ℕ) (fi : (Fin b → Bool) → M.State)
  (fa : M.State → (Fin b → Bool) → Fin n) (fn : M.State → Fin n → Bool → (Fin b → Bool) → M.State)

/-- Lift of a function on states to `Option S` (the `none` value is the initial-law average). -/
noncomputable def liftΦ (Φ : M.State → ℝ) : Option M.State → ℝ
  | none => avgC b (fun c0 => Φ (fi c0))
  | some s => Φ s

theorem lawE_toCoinM (hi : M.init = (coins b).map fi) (ha : ∀ t s, M.act t s = (coins b).map (fa s))
    (hn : ∀ t s a l, M.next t s a l = (coins b).map (fn s a l)) (ℓ : Losses n T) :
    ∀ t, t ≤ T → ∀ Φ : M.State → ℝ,
      lawE (toCoinM b fi fa fn) ℓ t (liftΦ M b fi Φ) =
        ∑ s, (M.stateDist (extL ℓ) t s).toReal * Φ s := by
  intro t
  induction t with
  | zero =>
    intro _ Φ
    simp only [lawE, toCoinM, liftΦ, Machine.stateDist]
    rw [hi, exp_map_coins]
  | succ t ih =>
    intro hT Φ
    have ht : t < T := by omega
    -- the one-step kernel
    set K : M.State → ℝ := fun s => avgC b (fun c1 => avgC b (fun c2 => Φ (fn s (fa s c1) (ℓ ⟨t, ht⟩ (fa s c1)) c2)))
      with hK
    have hstep : (fun s' => avgC (toCoinM b fi fa fn).b (fun c => liftΦ M b fi Φ
        ((toCoinM b fi fa fn).next s' c (ℓ ⟨t, ht⟩ ((toCoinM b fi fa fn).act s' c))))) = liftΦ M b fi K := by
      funext s'
      show avgC (b + b + b) (fun c => Φ (fn (res fi s' (split3 b c).1.1)
          (fa (res fi s' (split3 b c).1.1) (split3 b c).1.2)
          (ℓ ⟨t, ht⟩ (fa (res fi s' (split3 b c).1.1) (split3 b c).1.2)) (split3 b c).2)) = _
      rw [avgC_split3 b (fun c0 c1 c2 => Φ (fn (res fi s' c0) (fa (res fi s' c0) c1)
          (ℓ ⟨t, ht⟩ (fa (res fi s' c0) c1)) c2))]
      cases s' with
      | none => rfl
      | some s =>
        show avgC b (fun _ => K s) = K s
        unfold avgC
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have : (0 : ℝ) < Fintype.card (Fin b → Bool) := by exact_mod_cast Fintype.card_pos
        field_simp
    simp only [lawE, ht, dif_pos]
    rw [hstep, ih (by omega)]
    -- one step of P0001's forward recursion
    have e := Pool.P0012.expect_succ M (extL ℓ) t Φ
    unfold Pool.P0012.expect at e
    rw [e]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    rw [hK]
    unfold Pool.P0012.stepExp
    beta_reduce
    rw [ha t s, exp_map_coins]
    congr 1
    funext c1
    beta_reduce
    have hl : extL ℓ t (fa s c1) = ℓ ⟨t, ht⟩ (fa s c1) := by simp [extL, ht]
    rw [hl, hn t s, exp_map_coins]

theorem lv_eq_toNat (x : Bool) : (lv x : ℝ) = (x.toNat : ℝ) := by cases x <;> simp [lv]

/-- **Expected loss of the fair-coin machine = P0001's expected loss, summed over the rounds.** -/
theorem expLoss_toCoinM (hi : M.init = (coins b).map fi) (ha : ∀ t s, M.act t s = (coins b).map (fa s))
    (hn : ∀ t s a l, M.next t s a l = (coins b).map (fn s a l)) (ℓ : Losses n T) :
    expLoss (toCoinM b fi fa fn) ℓ = ∑ t ∈ Finset.range T, M.expLoss (extL ℓ) t := by
  have hcard : (0 : ℝ) < Fintype.card (Tape (toCoinM b fi fa fn).b T) := by exact_mod_cast Fintype.card_pos
  unfold expLoss algLoss
  push_cast
  rw [Finset.sum_comm, Finset.sum_div, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun tt _ => ?_
  rw [tape_round, mul_div_cancel_left₀ _ hcard.ne']
  -- the round function is a lift
  have hlift : (fun s' => avgC (toCoinM b fi fa fn).b (fun c => (lv (ℓ tt ((toCoinM b fi fa fn).act s' c)) : ℝ))) =
      liftΦ M b fi (fun s => avgC b (fun c1 => (lv (ℓ tt (fa s c1)) : ℝ))) := by
    funext s'
    show avgC (b + b + b) (fun c => (lv (ℓ tt (fa (res fi s' (split3 b c).1.1) (split3 b c).1.2)) : ℝ)) = _
    rw [avgC_split3 b (fun c0 c1 _ => (lv (ℓ tt (fa (res fi s' c0) c1)) : ℝ))]
    have hconst : ∀ x : ℝ, avgC b (fun _ => x) = x := by
      intro x; unfold avgC
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have : (0 : ℝ) < Fintype.card (Fin b → Bool) := by exact_mod_cast Fintype.card_pos
      field_simp
    cases s' with
    | none => simp only [res, hconst]; rfl
    | some s => simp only [res, hconst]; rfl
  rw [hlift, lawE_toCoinM M b fi fa fn hi ha hn ℓ tt (le_of_lt tt.2)]
  rw [Pool.P0012.expLoss_eq_expect]
  unfold Pool.P0012.expect
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  beta_reduce
  rw [ha, exp_map_coins]
  congr 1
  funext c
  have hl : extL ℓ tt (fa s c) = ℓ tt (fa s c) := by simp [extL, tt.2]
  rw [hl, lv_eq_toNat]

end Dy

theorem armLoss_eq_cumLoss (ℓ : Losses n T) (i : Fin n) : (armLoss ℓ i : ℝ) = cumLoss (extL ℓ) T i := by
  unfold armLoss cumLoss
  push_cast
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [lv_eq_toNat]
  simp [extL, t.2]

/-- One machine: a homogeneous dyadic P0001 machine gives a fair-coin coin machine with one more state, `3b` coins
per round and fair-coin regret at most P0001's regret. -/
theorem exists_coinMachine (M : Machine n) (hH : M.IsHomogeneous) (b : ℕ) (hD : Dyadic M b) (T : ℕ) :
    ∃ CM : CoinMachine n, Fintype.card CM.S = Fintype.card M.State + 1 ∧ CM.b = b + b + b ∧
      ∀ (ℓ : Losses n T) (i : Fin n), expLoss CM ℓ - armLoss ℓ i ≤ regret M (extL ℓ) T := by
  classical
  obtain ⟨⟨fi, hi⟩, ha, hn⟩ := hD
  let fa : M.State → (Fin b → Bool) → Fin n := fun s => Classical.choose (ha 0 s)
  let fn : M.State → Fin n → Bool → (Fin b → Bool) → M.State := fun s a l => Classical.choose (hn 0 s a l)
  have ha' : ∀ t s, M.act t s = (coins b).map (fa s) := by
    intro t s; rw [hH.1 t s]; exact Classical.choose_spec (ha 0 s)
  have hn' : ∀ t s a l, M.next t s a l = (coins b).map (fn s a l) := by
    intro t s a l; rw [hH.2 t s a l]; exact Classical.choose_spec (hn 0 s a l)
  refine ⟨toCoinM b fi fa fn, ?_, rfl, fun ℓ i => ?_⟩
  · show Fintype.card (Option M.State) = _
    exact Fintype.card_option
  · rw [expLoss_toCoinM M b fi fa fn hi ha' hn' ℓ, armLoss_eq_cumLoss, regret]
    have := bestLoss_le_cumLoss (extL ℓ) T i
    linarith

/-- **Bridge**: the strict target in P0001 semantics implies the fair-coin strict target. -/
theorem strictTarget_of_strictMinimax : StrictMinimax → StrictTarget := by
  classical
  rintro ⟨F, hhom, ⟨C, k, hmem⟩, ⟨Cb, kb, hbits⟩, ⟨C', k', hreg⟩⟩
  set K := k + kb + 1 with hK
  set C1 := max C 0 + 3 * max Cb 0 + 1 with hC1
  have hlog1 : ∀ m T : ℕ, 1 ≤ m → m + 1 ≤ T → 1 ≤ Real.log (((m + 1 : ℕ) : ℝ) * T) :=
    fun m T h1 h2 => one_le_log (by omega) h2
  have hlog0 : ∀ m T : ℕ, m + 1 ≤ T → 0 ≤ Real.log (((m + 1 : ℕ) : ℝ) * T) := by
    intro m T h
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
    have : (1 : ℝ) ≤ T := by exact_mod_cast (show 1 ≤ T by omega)
    nlinarith
  have hex : ∀ m T : ℕ, 1 ≤ m ∧ m + 1 ≤ T → ∃ CM : CoinMachine (m + 1),
      Real.logb 2 (Fintype.card CM.S) ≤ C1 * plog (m + 1) T K ∧ (CM.b : ℝ) ≤ C1 * plog (m + 1) T K ∧
      ∀ (ℓ : Losses (m + 1) T) (i : Fin (m + 1)),
        expLoss CM ℓ - armLoss ℓ i ≤ max C' 0 * Real.sqrt (((m + 1 : ℕ) : ℝ) * T) * plog (m + 1) T k' := by
    intro m T h
    have hn : 1 ≤ m + 1 := by omega
    obtain ⟨b, hb, hD⟩ := hbits (m + 1) T hn h.2
    obtain ⟨CM, hcard, hbCM, hreg'⟩ := exists_coinMachine (F (m + 1) T hn) (hhom _ _ _) b hD T
    have hL1 := hlog1 m T h.1 h.2
    set L := Real.log (((m + 1 : ℕ) : ℝ) * T) with hL
    have hLK1 : 1 ≤ L ^ K := one_le_pow₀ hL1
    have hLk : L ^ k ≤ L ^ K := pow_le_pow_right₀ hL1 (by omega)
    have hLkb : L ^ kb ≤ L ^ K := pow_le_pow_right₀ hL1 (by omega)
    have hpl : ∀ j, plog (m + 1) T j = L ^ j := fun j => rfl
    refine ⟨CM, ?_, ?_, fun ℓ i => ?_⟩
    · -- memory: one more state
      have hS1 : 1 ≤ Fintype.card (F (m + 1) T hn).State := by
        obtain ⟨s, -⟩ := (F (m + 1) T hn).init.support_nonempty
        exact Fintype.card_pos_iff.2 ⟨s⟩
      have hS : (1 : ℝ) ≤ Fintype.card (F (m + 1) T hn).State := by exact_mod_cast hS1
      have h1 : Real.logb 2 (Fintype.card CM.S) ≤ Real.logb 2 (Fintype.card (F (m + 1) T hn).State) + 1 := by
        rw [hcard]
        push_cast
        calc Real.logb 2 ((Fintype.card (F (m + 1) T hn).State : ℝ) + 1)
            ≤ Real.logb 2 (2 * (Fintype.card (F (m + 1) T hn).State : ℝ)) :=
              Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
          _ = Real.logb 2 (Fintype.card (F (m + 1) T hn).State) + 1 := by
              rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]; ring
      have h2 : Real.logb 2 (Fintype.card (F (m + 1) T hn).State) ≤ C * L ^ k := hmem (m + 1) T hn h.2
      have h3 : C * L ^ k ≤ max C 0 * L ^ K :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
          (mul_le_mul_of_nonneg_left hLk (le_max_right _ _))
      have h4 : 0 ≤ 3 * max Cb 0 * L ^ K := by positivity
      rw [hpl, hC1]
      nlinarith
    · -- coins: three blocks of `b`
      rw [hbCM]
      push_cast
      have h3 : Cb * L ^ kb ≤ max Cb 0 * L ^ K :=
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
          (mul_le_mul_of_nonneg_left hLkb (le_max_right _ _))
      have h4 : 0 ≤ max C 0 * L ^ K := by positivity
      rw [hpl, hC1]
      nlinarith
    · have hr := hreg (m + 1) T hn h.2 (extL ℓ)
      have hsq : 0 ≤ Real.sqrt (((m + 1 : ℕ) : ℝ) * T) * L ^ k' := by positivity
      have : C' * Real.sqrt (((m + 1 : ℕ) : ℝ) * T) * L ^ k' ≤
          max C' 0 * Real.sqrt (((m + 1 : ℕ) : ℝ) * T) * L ^ k' := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hsq
      rw [hpl]
      exact (hreg' ℓ i).trans (hr.trans this)
  let G : (m T : ℕ) → CoinMachine (m + 1) := fun m T =>
    if h : 1 ≤ m ∧ m + 1 ≤ T then Classical.choose (hex m T h) else constMachine m
  refine ⟨C1, K, max C' 0, k', by positivity, by omega, G, fun m T hmT => ?_⟩
  by_cases h : 1 ≤ m ∧ m + 1 ≤ T
  · have hG : G m T = Classical.choose (hex m T h) := dif_pos h
    rw [hG]
    exact Classical.choose_spec (hex m T h)
  · -- one arm: the constant machine
    have hm : m = 0 := by omega
    subst hm
    have hG : G 0 T = constMachine 0 := dif_neg h
    rw [hG]
    have hpl0 : ∀ j, 0 ≤ plog (0 + 1) T j := fun j => pow_nonneg (hlog0 0 T hmT) j
    refine ⟨?_, ?_, fun ℓ i => ?_⟩
    · show Real.logb 2 (Fintype.card Unit) ≤ _
      simp only [Fintype.card_unit, Nat.cast_one, Real.logb_one]
      exact mul_nonneg (by positivity) (hpl0 K)
    · show ((0 : ℕ) : ℝ) ≤ _
      simp only [Nat.cast_zero]
      exact mul_nonneg (by positivity) (hpl0 K)
    · rw [expLoss_const, Fin.fin_one_eq_zero i, sub_self]
      exact mul_nonneg (mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) (hpl0 k')

/-- **The construction behind `Pool.P0294.main` meets the strict fair-coin model.** -/
theorem pool_refModel : StrictTarget := strictTarget_of_strictMinimax pool_strict

/-- The explicit family, rounded, meets it too (same theorem, explicit input). -/
theorem famE_refModel : StrictTarget := strictTarget_of_strictMinimax famE_strict_target

end Audit3

#print axioms Audit3.strictTarget_of_strictMinimax
#print axioms Audit3.pool_refModel
#print axioms Audit3.famE_refModel

/-! ## The one-level machine's round-kind law has the real weight `q/2 = 1/(64 Λ²)` on BASE rounds -/

namespace Audit3E

open Pool.P0001 Pool.P0161

/-- At the rate the explicit recursion uses, the probability of a BASE round is `1/(64·Λ²)` with
`Λ = max cE 1 · (log(nH) + 1)^30`, a real number involving `log(nH)` (transcendental for `nH ≥ 2`, by
Lindemann–Weierstrass; not proved here). So the pool's machines are not dyadic as built. -/
theorem base_round_prob (n H : ℕ) [NeZero n] (hn : 1 ≤ n) (hH : 1 ≤ H) (A : Pool.P0050.CoinAlg n) :
    ((Pool.P0284.famM n H (qOf cE kE n H) A).κl none).toReal =
      1 / (64 * (max cE 1 * (Real.log ((n : ℝ) * H) + 1) ^ 30) ^ 2) := by
  have hq := Pool.P0278.qOf_pos cE kE n H hn hH
  have hq1 := Pool.P0278.qOf_le cE kE n H hn hH
  rw [(Pool.P0284.famM_intended n H _ A hq hq1).κl_eq none]
  show (Pool.P0284.famM n H (qOf cE kE n H) A).P.wB = _
  rw [Pool.P0284.famM_wB]
  unfold qOf Lam Lg kE
  norm_num
  ring

end Audit3E

#print axioms Audit3E.base_round_prob
