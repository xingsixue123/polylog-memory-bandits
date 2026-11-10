import Mathlib

/-!
# The main result restated with Mathlib definitions only

This file imports only Mathlib and does not depend on any definition of the `Pool` library, so the
statement can be read without reading `Pool/P0001/Model.lean` and `Pool/P0001/Targets.lean`.

`Restated.Achievable` says: there are constants `C, k, C', k'` such that for all `1 ≤ n ≤ T` there is
a time-homogeneous randomized finite-state machine on `n` arms (state type `S`, initial law `init`,
arm law `act`, transition law `next` that sees only the pulled arm's loss bit; fresh coins in every
draw) with `log₂ |S| ≤ C (log (n T))^k` and, against every loss table `ℓ : ℕ → Fin n → Bool` fixed in
advance, expected regret over rounds `0, …, T-1` at most `C' √(n T) (log (n T))^k'`.

`Checks/Bridge.lean` derives `Restated.Achievable` from the main theorem `Pool.P0294.main`.
-/

namespace Restated

/-- Law of the state at the start of round `t`, with fresh coins in every draw. -/
noncomputable def stLaw {n : ℕ} {S : Type} (init : PMF S) (act : S → PMF (Fin n))
    (next : S → Fin n → Bool → PMF S) (ℓ : ℕ → Fin n → Bool) : ℕ → PMF S
  | 0 => init
  | t + 1 => (stLaw init act next ℓ t).bind fun s => (act s).bind fun a => next s a (ℓ t a)

/-- Expected loss over rounds `0, …, T-1` minus the loss of the best single arm in hindsight. -/
noncomputable def expRegret {n : ℕ} {S : Type} (init : PMF S) (act : S → PMF (Fin n))
    (next : S → Fin n → Bool → PMF S) (ℓ : ℕ → Fin n → Bool) (T : ℕ) : ℝ :=
  (∑ t ∈ Finset.range T, ∑ a : Fin n,
      (((stLaw init act next ℓ t).bind act) a).toReal * (if ℓ t a then (1 : ℝ) else 0))
  - ⨅ i : Fin n, ∑ t ∈ Finset.range T, (if ℓ t i then (1 : ℝ) else 0)

/-- The positive resolution, stated with Mathlib constants only. -/
def Achievable : Prop :=
  ∃ (C : ℝ) (k : ℕ) (C' : ℝ) (k' : ℕ),
    ∀ n T : ℕ, 1 ≤ n → n ≤ T →
      ∃ (S : Type) (_ : Fintype S) (init : PMF S) (act : S → PMF (Fin n))
        (next : S → Fin n → Bool → PMF S),
        Real.logb 2 (Fintype.card S) ≤ C * Real.log ((n : ℝ) * (T : ℝ)) ^ k ∧
        ∀ ℓ : ℕ → Fin n → Bool,
          expRegret init act next ℓ T ≤ C' * Real.sqrt ((n : ℝ) * (T : ℝ)) * Real.log ((n : ℝ) * (T : ℝ)) ^ k'

end Restated
