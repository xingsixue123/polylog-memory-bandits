import Pool.P0161.Recursion

/-!
# Statement: the target is equivalent to a one-level boosting step (a reformulation, not a reduction)

* `Pool.P0161.DZStep c k` (in `Pool.P0161.Defs`): from ANY homogeneous base machine `MB` with regret `≤ RB`
  over horizon `⌈4qT⌉` (on every loss sequence), there is a homogeneous machine `M` for horizon `T` with
  `memBits M ≤ memBits MB + c·Lg^k` and regret `≤ c·Lg^k·(√(nT/q) + RB)` on every loss sequence,
  for all `1 ≤ n ≤ T` and every `q` with `n/T ≤ q` and `q·c·Lg^k ≤ 1` (`Lg = log(nT) + 1`).
* `DZStepAt c k`: the same step required only at the single rate `q = qOf c k n T = 1/(32·Λ²)`,
  `Λ = max c 1 · Lg n T ^ k` (and only when `n/T ≤ q`). `DZStep c k → DZStepAt c k`.
* `mainAt`: `DZStepAt c k → MinimaxPolylogAchievable`; `main`: `DZStep c k → MinimaxPolylogAchievable`
  (P0001's positive resolution: homogeneous machines, `MemoryBound`, regret `C'·√(nT)·log(nT)^k'`, `1 ≤ n ≤ T`).
* `converse`, `converseAt`: `MinimaxPolylogAchievable → ∃ c k, DZStep c k` (resp. `DZStepAt c k`). So both
  hypotheses are EQUIVALENT to the target: the hypothesis is as hard as the conclusion. They are one-level
  statements (one base, one horizon extension by the factor `1/(4q)`); nothing links them to P0136's Design Z.
-/

open Pool.P0001

namespace Pool.P0161

/-- The conditional resolution from the step at the single rate `q = 1/(32Λ²)` (the weakest hypothesis here). -/
theorem mainAt {c : ℝ} {k : ℕ} (h : DZStepAt c k) : MinimaxPolylogAchievable :=
  minimax_of_DZStepAt h

theorem main {c : ℝ} {k : ℕ} (h : DZStep c k) : MinimaxPolylogAchievable :=
  minimax_of_DZStep h

/-- `DZStepAt` is also equivalent to the target. -/
theorem converseAt (h : MinimaxPolylogAchievable) : ∃ (c : ℝ) (k : ℕ), DZStepAt c k := by
  obtain ⟨c, k, hc⟩ := dzstep_of_minimax h
  exact ⟨c, k, dzstepAt_of_dzstep hc⟩

theorem converse (h : MinimaxPolylogAchievable) : ∃ (c : ℝ) (k : ℕ), DZStep c k :=
  dzstep_of_minimax h

end Pool.P0161
