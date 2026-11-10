import Pool.P0144.AnyBase

/-!
# One-level boosting step interfaces `DZStep`, `DZStepAt` (definitions)

* `Lg n T = log(nT) + 1`, the polylog factor.
* `DZStep c k`: from any homogeneous base machine with regret `≤ RB` on every loss sequence over
  horizon `⌈4qT⌉`, build a homogeneous machine for horizon `T` with at most `c·Lg^k` more bits
  and regret `≤ c·Lg^k·(√(nT/q) + RB)`, for every `q` with `n/T ≤ q` and `q·c·Lg^k ≤ 1`.
* `DZStepAt c k`: the same, required only at the single rate `q = qOf c k n T = 1/(32·Λ²)`,
  `Λ = Lam c k n T = max c 1 · Lg n T ^ k`. `DZStep c k → DZStepAt c k` (`dzstepAt_of_dzstep`).
* The names are historical: these are generic one-level boosting interfaces; nothing here links them to
  P0136's Design Z.
* `triv n`: the one-state machine pulling arm `0` (zero bits, regret `≤ T`).
* `regret_one`: with one arm every machine has regret `0`.
-/

open Pool.P0001 Real

namespace Pool.P0161


/-- The polylog factor `log(nT) + 1`. -/
noncomputable def Lg (n T : ℕ) : ℝ := Real.log ((n : ℝ) * T) + 1

/-- **One-level boosting step, for every admissible rate** (a generic interface; the form CLAIMED, not proved,
for P0136's Design Z with P0150's changes). From any homogeneous base machine with regret `≤ RB` on every
sequence over horizon `⌈4qT⌉`, build a homogeneous machine for horizon `T` with at most `c·Lg^k` more bits and
regret `≤ c·Lg^k·(√(nT/q) + RB)`, for every real `q` with `n/T ≤ q` and `q·(c·Lg^k) ≤ 1` (for `c > 0` this is
`q ≤ 1/(c·Lg^k)`; for `c ≤ 0` the second condition is void, and `DZStep` is then false, cf. `not_dzstep_zero`). -/
def DZStep (c : ℝ) (k : ℕ) : Prop :=
  ∀ (n T : ℕ), 1 ≤ n → n ≤ T → ∀ q : ℝ, (n : ℝ) / T ≤ q → q * (c * Lg n T ^ k) ≤ 1 →
    ∀ (MB : Machine n), MB.IsHomogeneous → ∀ RB : ℝ,
      (∀ ℓ : LossSeq n, regret MB ℓ ⌈4 * q * T⌉₊ ≤ RB) →
      ∃ M : Machine n, M.IsHomogeneous ∧ M.memBits ≤ MB.memBits + c * Lg n T ^ k ∧
        ∀ ℓ : LossSeq n, regret M ℓ T ≤ c * Lg n T ^ k * (Real.sqrt (n * T / q) + RB)

/-- The constant `Λ = max c 1 · Lg(n,T)^k` (`≥ 1`). -/
noncomputable def Lam (c : ℝ) (k n T : ℕ) : ℝ := max c 1 * Lg n T ^ k

/-- The single value of `q` that the recursion uses at horizon `T`: `q = 1/(32·Λ²)`, a `1/polylog` constant. -/
noncomputable def qOf (c : ℝ) (k n T : ℕ) : ℝ := 1 / (32 * Lam c k n T ^ 2)

/-- **One-level boosting step at the single rate `q = qOf c k n T = 1/(32Λ²)`** (weaker than `DZStep`, which
asks for every `q` in `[n/T, 1/(c·Lg^k)]`). From any homogeneous base machine with regret `≤ RB` on every
sequence over horizon `⌈4qT⌉`, build a homogeneous machine for horizon `T` with at most `c·Lg^k` more bits and
regret `≤ c·Lg^k·(√(nT/q) + RB)`; required only when `n/T ≤ q`. -/
def DZStepAt (c : ℝ) (k : ℕ) : Prop :=
  ∀ (n T : ℕ), 1 ≤ n → n ≤ T → (n : ℝ) / T ≤ qOf c k n T →
    ∀ (MB : Machine n), MB.IsHomogeneous → ∀ RB : ℝ,
      (∀ ℓ : LossSeq n, regret MB ℓ ⌈4 * qOf c k n T * T⌉₊ ≤ RB) →
      ∃ M : Machine n, M.IsHomogeneous ∧ M.memBits ≤ MB.memBits + c * Lg n T ^ k ∧
        ∀ ℓ : LossSeq n, regret M ℓ T ≤ c * Lg n T ^ k * (Real.sqrt (n * T / qOf c k n T) + RB)

/-- The one-state machine that always pulls arm `0`. -/
noncomputable def triv (n : ℕ) (hn : 1 ≤ n) : Machine n where
  State := Unit
  init := PMF.pure ()
  act _ _ := PMF.pure ⟨0, hn⟩
  next _ _ _ _ := PMF.pure ()

lemma triv_isHomogeneous (n : ℕ) (hn : 1 ≤ n) : (triv n hn).IsHomogeneous :=
  ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩

lemma triv_memBits (n : ℕ) (hn : 1 ≤ n) : (triv n hn).memBits = 0 := by
  show Real.logb 2 (Fintype.card Unit) = 0
  simp

/-- With one arm every machine has regret `0`. -/
lemma regret_one (M : Machine 1) (ℓ : LossSeq 1) (T : ℕ) : regret M ℓ T = 0 := by
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


end Pool.P0161
