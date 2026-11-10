import Pool.P0015.Block
import Pool.P0027.Statement
/-!
# Coin processes as `K`-query machines (P0045 component C7, generic part)

A `CoinProc n K` is a *deterministic* `K`-query process driven by fresh coins: in round `t`, in
state `s`, it draws an action coin `ra ~ μA t` and takes the action `actF t s ra`; after observing
the bits `o` of the played and queried arms it draws an update coin `rn ~ μN t` and moves to
`nextF t s a o rn`. Action coins are used only by the action and update coins only by the update,
so no coin has to be stored: the machine `toQMachine` has exactly the process states.

Main results:
* `stateDist_eq`: the state law of `toQMachine` at round `t` is the push-forward, under the
  deterministic run `runF ℓ t`, of `coinLaw t`, the law of the first `t` rounds' coins.
* `coinLaw_apply`, `pairLaw_apply`: `coinLaw` is the product of the per-round laws.
* `E_coinLaw_restrict`: marginals (the first `t` rounds' coins of `coinLaw T` have law `coinLaw t`).
* `sum_expLoss_eq_E_pathLoss`, `regret_eq_E`: expected cumulative loss and regret equal the
  expectation, over the coin product of the whole horizon, of the pathwise loss / regret.
* `memBits_toQMachine`, `playBlind_toQMachine` (P0027's `PlayBlind` when the update ignores the
  played arm's bit), and `bernVec`: independent Bernoulli bits with coordinate-dependent
  probabilities, as a PMF with its product weight `bernWt`.
-/

open scoped ENNReal

namespace Pool.P0051

open Pool.P0001 Pool.P0015

/-- A deterministic `K`-query process driven by fresh coins: states `State`, action coins `RA`
with law `μA t` in round `t`, update coins `RN` with law `μN t`, initial state `init`, action
`actF t s ra` and update `nextF t s a o rn`. -/
structure CoinProc (n K : ℕ) where
  State : Type
  [fintypeState : Fintype State]
  RA : Type
  [fintypeRA : Fintype RA]
  RN : Type
  [fintypeRN : Fintype RN]
  init : State
  μA : ℕ → PMF RA
  μN : ℕ → PMF RN
  actF : ℕ → State → RA → QAct n K
  nextF : ℕ → State → QAct n K → QObs K → RN → State

attribute [scoped instance] CoinProc.fintypeState CoinProc.fintypeRA CoinProc.fintypeRN

namespace CoinProc

variable {n K : ℕ} (P : CoinProc n K)

/-- The `K`-query machine of a coin process: it draws the action coin to act and the update coin
to update; its states are the process states. -/
noncomputable abbrev toQMachine : QMachine n K where
  State := P.State
  init := PMF.pure P.init
  act t s := (P.μA t).map (P.actF t s)
  next t s a o := (P.μN t).map (P.nextF t s a o)

/-- The law of one round's pair of coins. -/
noncomputable def pairLaw (t : ℕ) : PMF (P.RA × P.RN) :=
  (P.μA t).bind fun a => (P.μN t).map fun b => (a, b)

/-- Law of the coins of the first `t` rounds (the coins of round `i` are `ω i`). -/
noncomputable def coinLaw : (t : ℕ) → PMF (Fin t → P.RA × P.RN)
  | 0 => PMF.pure (fun i => i.elim0)
  | t + 1 => (coinLaw t).bind fun ω => (P.pairLaw t).map fun r => Fin.snoc ω r

/-- The process state after the first `t` rounds, driven by the coins `ω` (deterministic). -/
def runF (ℓ : LossSeq n) : (t : ℕ) → (Fin t → P.RA × P.RN) → P.State
  | 0, _ => P.init
  | t + 1, ω =>
    P.nextF t (runF ℓ t (Fin.init ω)) (P.actF t (runF ℓ t (Fin.init ω)) (ω (Fin.last t)).1)
      (qobs (P.actF t (runF ℓ t (Fin.init ω)) (ω (Fin.last t)).1) (ℓ t)) (ω (Fin.last t)).2

theorem stateDist_eq (ℓ : LossSeq n) (t : ℕ) :
    P.toQMachine.stateDist ℓ t = (P.coinLaw t).map (P.runF ℓ t) := by
  induction t with
  | zero =>
    show PMF.pure P.init = _
    simp [coinLaw, runF, PMF.pure_map]
  | succ t ih =>
    show (P.toQMachine.stateDist ℓ t).bind (fun (s : P.State) =>
      ((P.μA t).map (P.actF t s)).bind fun a => (P.μN t).map (P.nextF t s a (qobs a (ℓ t)))) = _
    rw [ih, coinLaw, PMF.map_bind, PMF.bind_map]
    congr 1
    funext ω
    simp only [Function.comp_apply, pairLaw, PMF.map_bind, PMF.bind_map, PMF.map_comp]
    congr 1
    funext a
    simp only [Function.comp_apply, PMF.map_comp]
    congr 1
    funext b
    simp [runF, Fin.init_snoc, Fin.snoc_last]

/-- The pair of coins of a round has the product law. -/
theorem pairLaw_apply (t : ℕ) (r : P.RA × P.RN) :
    (P.pairLaw t r).toReal = (P.μA t r.1).toReal * (P.μN t r.2).toReal := by
  classical
  rw [pairLaw, toReal_bind_apply, Finset.sum_eq_single r.1]
  · congr 1
    rw [← PMF.bind_pure_comp, toReal_bind_apply, Finset.sum_eq_single r.2]
    · simp
    · intro b _ hb
      simp [PMF.pure_apply, Prod.ext_iff, Ne.symm hb]
    · simp
  · intro a _ ha
    rw [← PMF.bind_pure_comp, toReal_bind_apply]
    simp [PMF.pure_apply, Prod.ext_iff, Ne.symm ha]
  · simp

/-- Product formula: the coins of different rounds are independent. -/
theorem coinLaw_apply : (t : ℕ) → (ω : Fin t → P.RA × P.RN) →
    (P.coinLaw t ω).toReal = ∏ i : Fin t, (P.pairLaw (i : ℕ) (ω i)).toReal
  | 0, ω => by
    have : ω = fun i => i.elim0 := funext fun i => i.elim0
    subst this
    simp [coinLaw]
  | t + 1, ω => by
    classical
    rw [coinLaw, toReal_bind_apply, Finset.sum_eq_single (Fin.init ω)]
    · rw [coinLaw_apply t, Fin.prod_univ_castSucc]
      congr 1
      rw [← PMF.bind_pure_comp, toReal_bind_apply, Finset.sum_eq_single (ω (Fin.last t))]
      · simp [Fin.snoc_init_self]
      · intro r _ hr
        simp only [Function.comp_apply, PMF.pure_apply]
        split_ifs with h
        · exact absurd (by rw [h, Fin.snoc_last]) hr
        · simp
      · simp
    · intro ω' _ hω'
      rw [← PMF.bind_pure_comp, toReal_bind_apply]
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
      simp only [Function.comp_apply, PMF.pure_apply]
      split_ifs with h
      · exact absurd (by rw [h, Fin.init_snoc]) hω'
      · simp
    · simp

/-- Restriction of a coin path to its first `t` rounds. -/
def restrict {T t : ℕ} (h : t ≤ T) (ω : Fin T → P.RA × P.RN) : Fin t → P.RA × P.RN :=
  fun i => ω (Fin.castLE h i)

/-- Marginals: the first `t` rounds' coins of `coinLaw T` have law `coinLaw t`. -/
theorem E_coinLaw_restrict {t : ℕ} (g : (Fin t → P.RA × P.RN) → ℝ) :
    ∀ T (h : t ≤ T), E (P.coinLaw T) (fun ω => g (P.restrict h ω)) = E (P.coinLaw t) g := by
  classical
  intro T h
  induction T, h using Nat.le_induction with
  | base => rfl
  | succ T hT ih =>
    rw [coinLaw, E_bind]
    rw [← ih]
    congr 1
    funext ω
    rw [E_map]
    have : ∀ r, P.restrict (Nat.le_succ_of_le hT) (Fin.snoc ω r) = P.restrict hT ω := by
      intro r
      funext i
      simp only [restrict]
      have : (Fin.castLE (Nat.le_succ_of_le hT) i : Fin (T + 1)) = Fin.castSucc (Fin.castLE hT i) := by
        ext; simp
      rw [this, Fin.snoc_castSucc]
    simp only [this, E_const]

/-- The loss at round `t` along a coin path of length `t + 1`. -/
def lossAt (ℓ : LossSeq n) (t : ℕ) (ω : Fin (t + 1) → P.RA × P.RN) : ℝ :=
  ((ℓ t (P.actF t (P.runF ℓ t (Fin.init ω)) (ω (Fin.last t)).1).1).toNat : ℝ)

/-- The total loss over the first `T` rounds along a coin path. -/
def pathLoss (ℓ : LossSeq n) (T : ℕ) (ω : Fin T → P.RA × P.RN) : ℝ :=
  ∑ t : Fin T, P.lossAt ℓ t (P.restrict (Nat.succ_le_of_lt t.2) ω)

theorem expLoss_eq_E (ℓ : LossSeq n) (t : ℕ) :
    P.toQMachine.expLoss ℓ t = E (P.coinLaw (t + 1)) (P.lossAt ℓ t) := by
  classical
  rw [QMachine.expLoss_eq, stateDist_eq, E_map, coinLaw, E_bind]
  congr 1
  funext ω
  simp only [E_map, pairLaw, E_bind]
  congr 1
  funext a
  simp [lossAt, Fin.init_snoc, Fin.snoc_last, E_const]

/-- The expected cumulative loss of the machine is the expected pathwise loss over the coin
product of the whole horizon. -/
theorem sum_expLoss_eq_E_pathLoss (ℓ : LossSeq n) (T : ℕ) :
    ∑ t ∈ Finset.range T, P.toQMachine.expLoss ℓ t = E (P.coinLaw T) (P.pathLoss ℓ T) := by
  unfold pathLoss
  rw [E_sum, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [expLoss_eq_E, E_coinLaw_restrict]

theorem regret_eq_E (ℓ : LossSeq n) (T : ℕ) :
    P.toQMachine.regret ℓ T = E (P.coinLaw T) (fun ω => P.pathLoss ℓ T ω - bestLoss ℓ T) := by
  rw [QMachine.regret, sum_expLoss_eq_E_pathLoss]
  unfold E
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_toReal, one_mul]

/-- Memory of the machine: `log₂` of the number of process states (no coin is stored). -/
theorem memBits_toQMachine : P.toQMachine.memBits = Real.logb 2 (Fintype.card P.State) := rfl

/-- If the update never reads the played arm's bit, the one-query machine is play-blind (P0027). -/
theorem playBlind_toQMachine (P : CoinProc n 1)
    (h : ∀ t s a (y y' : Bool) (o : Fin 1 → Bool) r, P.nextF t s a (y, o) r = P.nextF t s a (y', o) r) :
    Pool.P0027.PlayBlind P.toQMachine := by
  intro t s a y y' o
  show (P.μN t).map (P.nextF t s a (y, o)) = (P.μN t).map (P.nextF t s a (y', o))
  congr 1
  funext r
  exact h t s a y y' o r

end CoinProc

/-! ## Independent Bernoulli bits with coordinate-dependent probabilities -/

section BernVec

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Weight of a bit vector under independent Bernoulli(`p i`) coordinates. -/
noncomputable def bernWt (p : ι → ℝ) (ω : ι → Bool) : ℝ := ∏ i, if ω i then p i else 1 - p i

theorem bernWt_nonneg {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (ω : ι → Bool) : 0 ≤ bernWt p ω :=
  Finset.prod_nonneg fun i _ => by
    split_ifs
    · exact (hp i).1
    · linarith [(hp i).2]

theorem sum_bernWt (p : ι → ℝ) : ∑ ω : ι → Bool, bernWt p ω = 1 := by
  classical
  unfold bernWt
  have h := Fintype.prod_sum (fun (i : ι) (b : Bool) => if b = true then p i else 1 - p i)
  rw [← h]
  simp

/-- The law of independent Bernoulli(`p i`) bits. -/
noncomputable def bernVec (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : PMF (ι → Bool) :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (bernWt p ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => bernWt_nonneg hp ω), sum_bernWt, ENNReal.ofReal_one])

theorem bernVec_apply {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (ω : ι → Bool) :
    (bernVec p hp ω).toReal = bernWt p ω := by
  simp [bernVec, ENNReal.toReal_ofReal (bernWt_nonneg hp ω)]

end BernVec

end Pool.P0051
