import Pool.P0012.Potential

/-!
# Explicit-coin algorithms: P0001 machines driven by fresh discrete coins, and their realized runs

A `CoinAlg` is an algorithm written as deterministic rules driven by fresh finite coins: in round `t` from state
`s`, an action coin `y ∼ μ` chooses the pulled arm `act t s y`; after the loss bit `b` is observed, a fresh update
coin `z ∼ ν` gives the next state `upd t s y b z`. `CoinAlg.toMachine` turns it into a `Pool.P0001.Machine` whose
state stores the current action coin (the coin is shared by the action and the update, so it must persist through
the round). The memory is `log₂ (|S| · |Y|)`.

Main result (`expect_eq_coins`): under the state law of `A.toMachine` at round `t`, the expectation of any function
of (state, action coin) is the coin-weighted average over explicit coin sequences `ω : Fin (t+1) → Y × Z` of its value
at the **realized deterministic run** `A.runFin ℓ t (Fin.init ω)`, with weight `A.W ω = Π_j μ(y_j) ν(z_j)` (total
mass `sum_W`). Corollary `expLoss_eq_coins`: the expected loss at round `t` is the coin-weighted realized loss.
So expected-regret analyses of such algorithms can argue pathwise, on deterministic runs with explicit coins. For
example, the counterfactual "same run with a passive copy inserted" of Peng–Rubinstein-type arguments can be
compared pathwise.
-/

open Finset Pool.P0001 Pool.P0012
open scoped ENNReal

namespace Pool.P0050

/-- An algorithm given by deterministic rules driven by fresh coins: in round `t`, from state `s`, with an
action coin `y ∼ μ` it pulls `act t s y`; after observing the loss bit `b`, with a fresh update coin
`z ∼ ν` it moves to `upd t s y b z`. -/
structure CoinAlg (n : ℕ) where
  S : Type
  [fS : Fintype S]
  Y : Type
  [fY : Fintype Y]
  Z : Type
  [fZ : Fintype Z]
  μ : PMF Y
  ν : PMF Z
  s0 : S
  act : ℕ → S → Y → Fin n
  upd : ℕ → S → Y → Bool → Z → S

attribute [scoped instance] CoinAlg.fS CoinAlg.fY CoinAlg.fZ

variable {n : ℕ} (A : CoinAlg n)

/-- The P0001 machine of a coin algorithm: its state stores the action coin of the current round. -/
noncomputable def CoinAlg.toMachine : Machine n where
  State := A.S × A.Y
  init := A.μ.map fun y => (A.s0, y)
  act t p := PMF.pure (A.act t p.1 p.2)
  next t p _ b := A.ν.bind fun z => A.μ.map fun y' => (A.upd t p.1 p.2 b z, y')

/-- Realized state at round `t` from the coins of rounds `< t` (coins as functions on `ℕ`). -/
def CoinAlg.run (ℓ : LossSeq n) (ω : ℕ → A.Y × A.Z) : ℕ → A.S
  | 0 => A.s0
  | t + 1 => A.upd t (CoinAlg.run ℓ ω t) (ω t).1 (ℓ t (A.act t (CoinAlg.run ℓ ω t) (ω t).1)) (ω t).2

/-- Realized state at round `t` from finitely many coins (rounds `0, …, t-1`). -/
def CoinAlg.runFin (ℓ : LossSeq n) : (t : ℕ) → (Fin t → A.Y × A.Z) → A.S
  | 0, _ => A.s0
  | t + 1, ω => A.upd t (CoinAlg.runFin ℓ t (Fin.init ω)) (ω (Fin.last t)).1
      (ℓ t (A.act t (CoinAlg.runFin ℓ t (Fin.init ω)) (ω (Fin.last t)).1)) (ω (Fin.last t)).2

/-- Weight of a finite coin sequence. -/
noncomputable def CoinAlg.W {t : ℕ} (ω : Fin t → A.Y × A.Z) : ℝ := ∏ j, (A.μ (ω j).1).toReal * (A.ν (ω j).2).toReal

theorem pmf_sum_toReal {α : Type} [Fintype α] (q : PMF α) : ∑ a, (q a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top q a),
    ← tsum_fintype (L := .unconditional _) (fun a => q a), PMF.tsum_coe, ENNReal.toReal_one]

/-- Splitting off the last coin. -/
theorem sum_split {X : Type} [Fintype X] {t : ℕ} (f : (Fin (t + 1) → X) → ℝ) :
    ∑ ω, f ω = ∑ x : X, ∑ ω' : Fin t → X, f (Fin.snoc ω' x) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv fun _ => X) _ _ (fun q => rfl)).symm

theorem W_snoc {t : ℕ} (ω : Fin t → A.Y × A.Z) (x : A.Y × A.Z) :
    A.W (Fin.snoc ω x) = A.W ω * ((A.μ x.1).toReal * (A.ν x.2).toReal) := by
  unfold CoinAlg.W; rw [Fin.prod_univ_castSucc]; simp

/-- Expectation under a pushforward PMF, on finite types. -/
theorem sum_map_toReal {α β : Type} [Fintype α] [Fintype β] (q : PMF α) (φ : α → β) (F : β → ℝ) :
    ∑ b, ((q.map φ) b).toReal * F b = ∑ a, (q a).toReal * F (φ a) := by
  classical
  have : ∀ b, ((q.map φ) b).toReal = ∑ a, (q a).toReal * (if b = φ a then 1 else 0) := by
    intro b
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
    · refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp
    · intro a _; split_ifs <;> simp [PMF.apply_ne_top]
  simp only [this, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Finset.sum_ite_eq']

theorem stepExp_toMachine (ℓ : LossSeq n) (t : ℕ) (p : A.S × A.Y) (f : A.S × A.Y → ℝ) :
    stepExp A.toMachine ℓ t p f =
      ∑ z, (A.ν z).toReal * ∑ y', (A.μ y').toReal *
        f (A.upd t p.1 p.2 (ℓ t (A.act t p.1 p.2)) z, y') := by
  classical
  have hact : ∀ a, (A.toMachine.act t p a).toReal = if a = A.act t p.1 p.2 then 1 else 0 := by
    intro a
    show ((PMF.pure (A.act t p.1 p.2)) a).toReal = _
    by_cases h : a = A.act t p.1 p.2 <;> simp [PMF.pure_apply, h]
  unfold stepExp
  rw [Finset.sum_eq_single (A.act t p.1 p.2)]
  · rw [hact, if_pos rfl, one_mul]
    show ∑ s' : A.S × A.Y, ((A.ν.bind fun z => A.μ.map fun y' =>
        (A.upd t p.1 p.2 (ℓ t (A.act t p.1 p.2)) z, y')) s').toReal * f s' = _
    simp only [bind_toReal, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    rw [sum_map_toReal]
  · intro a _ ha; rw [hact, if_neg ha, zero_mul]
  · simp

/-- Both ways of using the last round's update coin give the same weighted sum. -/
theorem sum_W_last {t : ℕ} (G : (Fin t → A.Y × A.Z) → A.Y → A.Z → ℝ) :
    ∑ ω : Fin (t + 1) → A.Y × A.Z, A.W ω * G (Fin.init ω) (ω (Fin.last t)).1 (ω (Fin.last t)).2 =
      ∑ ω : Fin (t + 1) → A.Y × A.Z, A.W ω *
        ∑ z, (A.ν z).toReal * G (Fin.init ω) (ω (Fin.last t)).1 z := by
  rw [sum_split, sum_split]
  simp only [W_snoc, Fin.init_snoc, Fin.snoc_last]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  -- left: Σ_z Σ_ω0 W ω0 μ y ν z G ω0 y z ; right: Σ_z' Σ_ω0 W ω0 μ y ν z' Σ_z ν z G ω0 y z
  have hν := pmf_sum_toReal A.ν
  calc ∑ z, ∑ ω0 : Fin t → A.Y × A.Z, A.W ω0 * ((A.μ y).toReal * (A.ν z).toReal) * G ω0 y z
      = ∑ ω0 : Fin t → A.Y × A.Z, A.W ω0 * (A.μ y).toReal * ∑ z, (A.ν z).toReal * G ω0 y z := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ω0 _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => by ring
    _ = ∑ z', ∑ ω0 : Fin t → A.Y × A.Z, A.W ω0 * ((A.μ y).toReal * (A.ν z').toReal) *
          ∑ z, (A.ν z).toReal * G ω0 y z := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ω0 _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, hν]
        ring

/-- **Coin representation of the state law.** Under the law of the state of `A.toMachine` at round `t`,
the expectation of any `f` equals the coin-weighted average of `f` at the realized state and action coin. -/
theorem expect_eq_coins (ℓ : LossSeq n) : ∀ (t : ℕ) (f : A.S × A.Y → ℝ),
    expect A.toMachine ℓ t f =
      ∑ ω : Fin (t + 1) → A.Y × A.Z, A.W ω * f (A.runFin ℓ t (Fin.init ω), (ω (Fin.last t)).1) := by
  intro t
  induction t with
  | zero =>
    intro f
    unfold Pool.P0012.expect
    show ∑ p : A.S × A.Y, ((A.μ.map fun y => (A.s0, y)) p).toReal * f p = _
    rw [sum_map_toReal, sum_split]
    simp only [W_snoc, Fin.snoc_last, Fintype.sum_prod_type]
    simp only [Finset.univ_unique, Finset.sum_singleton]
    unfold CoinAlg.W CoinAlg.runFin
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul, ← Finset.mul_sum, pmf_sum_toReal A.ν]; ring
  | succ t ih =>
    intro f
    have h1 : expect A.toMachine ℓ (t + 1) f =
        expect A.toMachine ℓ t (fun p => stepExp A.toMachine ℓ t p f) := expect_succ A.toMachine ℓ t f
    rw [h1]
    refine (ih (fun p => stepExp A.toMachine ℓ t p f)).trans ?_
    simp only [stepExp_toMachine]
    rw [sum_split (t := t + 1) (fun ω => A.W ω * f (A.runFin ℓ (t + 1) (Fin.init ω), (ω (Fin.last (t + 1))).1))]
    simp only [W_snoc, Fin.init_snoc, Fin.snoc_last, Fintype.sum_prod_type]
    -- right side: Σ_y' Σ_z' Σ_ω W ω μ y' ν z' f(runFin (t+1) ω, y')
    have hR : ∀ y' : A.Y, ∑ z' : A.Z, ∑ ω : Fin (t + 1) → A.Y × A.Z,
        A.W ω * ((A.μ y').toReal * (A.ν z').toReal) * f (A.runFin ℓ (t + 1) ω, y') =
        ∑ ω : Fin (t + 1) → A.Y × A.Z, A.W ω * ((A.μ y').toReal * f (A.runFin ℓ (t + 1) ω, y')) := by
      intro y'
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, pmf_sum_toReal A.ν]; ring
    simp only [hR]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    -- now both sides are Σ_ω W ω * (...)
    have := sum_W_last A (t := t) (fun ω0 y z => ∑ y', (A.μ y').toReal *
      f (A.upd t (A.runFin ℓ t ω0) y (ℓ t (A.act t (A.runFin ℓ t ω0) y)) z, y'))
    simp only [CoinAlg.runFin] at this ⊢
    rw [this]

theorem sum_W (t : ℕ) : ∑ ω : Fin t → A.Y × A.Z, A.W ω = 1 := by
  induction t with
  | zero => simp [CoinAlg.W]
  | succ t ih =>
    rw [sum_split]
    simp only [W_snoc, Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_mul, ih, one_mul]
    rw [pmf_sum_toReal, pmf_sum_toReal, one_mul]

/-- **Expected loss of a coin algorithm** = coin-weighted realized loss of round `t`. -/
theorem expLoss_eq_coins (ℓ : LossSeq n) (t : ℕ) :
    A.toMachine.expLoss ℓ t =
      ∑ ω : Fin (t + 1) → A.Y × A.Z, A.W ω *
        ((ℓ t (A.act t (A.runFin ℓ t (Fin.init ω)) (ω (Fin.last t)).1)).toNat : ℝ) := by
  rw [expLoss_eq_expect]
  have h : (fun s : A.toMachine.State => ∑ a, (A.toMachine.act t s a).toReal * ((ℓ t a).toNat : ℝ)) =
      fun p : A.S × A.Y => ((ℓ t (A.act t p.1 p.2)).toNat : ℝ) := by
    funext p
    classical
    show ∑ a, ((PMF.pure (A.act t p.1 p.2)) a).toReal * ((ℓ t a).toNat : ℝ) = _
    rw [Finset.sum_eq_single (A.act t p.1 p.2)]
    · simp
    · intro b _ hb; simp [PMF.pure_apply, hb]
    · simp
  rw [h]
  exact expect_eq_coins A ℓ t _

/-- The ℕ-indexed run agrees with `runFin` on the first `t` coins: `runFin ℓ t (ω restricted to Fin t)` is
`run ℓ ω t`. -/
theorem runFin_eq_run (ℓ : LossSeq n) (ω : ℕ → A.Y × A.Z) :
    ∀ t, A.runFin ℓ t (fun j => ω j) = A.run ℓ ω t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [CoinAlg.runFin, CoinAlg.run]
    have h : (Fin.init fun j : Fin (t + 1) => ω j) = fun j : Fin t => ω j := by
      funext j; simp [Fin.init]
    rw [h, ih]
    simp [Fin.last]

/-- Corollary of `expLoss_eq_coins` in terms of the ℕ-indexed run (coins extended arbitrarily beyond `t`
do not matter): for any `ω₀`, the expected loss at round `t` is the coin-weighted realized loss of `run`. -/
theorem expLoss_eq_coins_run (ℓ : LossSeq n) (t : ℕ) (ω₀ : ℕ → A.Y × A.Z) :
    A.toMachine.expLoss ℓ t =
      ∑ ω : Fin (t + 1) → A.Y × A.Z, A.W ω *
        ((ℓ t (A.act t (A.run ℓ (fun j => if h : j < t + 1 then ω ⟨j, h⟩ else ω₀ j) t)
          (ω (Fin.last t)).1)).toNat : ℝ) := by
  rw [expLoss_eq_coins]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← runFin_eq_run]
  congr 6
  funext j
  simp [Fin.init, show (j : ℕ) < t + 1 by omega]; rfl

end Pool.P0050
