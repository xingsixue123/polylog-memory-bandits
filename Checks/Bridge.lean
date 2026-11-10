import Pool.P0294.Statement
import Checks.Statement

/-!
# Bridge: the main theorem implies the Mathlib-only restatement

`Restated.of_pool : Pool.P0001.MinimaxPolylogAchievable → Restated.Achievable` and
`Restated.achievable : Restated.Achievable := of_pool Pool.P0294.main`.
-/

open Pool.P0001

namespace Restated

/-- For a homogeneous machine, the state law of `Pool.P0001` is `stLaw` with the round-0 kernels. -/
theorem stateDist_eq {n : ℕ} (M : Machine n) (hM : M.IsHomogeneous) (ℓ : LossSeq n) :
    ∀ t, M.stateDist ℓ t = @stLaw n M.State M.init (M.act 0) (M.next 0) ℓ t
  | 0 => rfl
  | t + 1 => by
    show (M.stateDist ℓ t).bind (fun s => (M.act t s).bind fun a => M.next t s a (ℓ t a)) =
      (stLaw M.init (M.act 0) (M.next 0) ℓ t).bind
        (fun s => (M.act 0 s).bind fun a => M.next 0 s a (ℓ t a))
    rw [stateDist_eq M hM ℓ t]
    congr 1
    funext s
    rw [hM.1 t s]
    congr 1
    funext a
    rw [hM.2 t s a]

/-- For a homogeneous machine, `Pool.P0001.regret` is `expRegret`. -/
theorem regret_eq {n : ℕ} (M : Machine n) (hM : M.IsHomogeneous) (ℓ : LossSeq n) (T : ℕ) :
    regret M ℓ T = @expRegret n M.State M.init (M.act 0) (M.next 0) ℓ T := by
  have h1 : ∀ t, M.armDist ℓ t = (stLaw M.init (M.act 0) (M.next 0) ℓ t).bind (M.act 0) := by
    intro t
    show (M.stateDist ℓ t).bind (M.act t) = _
    rw [stateDist_eq M hM ℓ t]
    congr 1
    funext s
    exact hM.1 t s
  have hb : ∀ b : Bool, ((b.toNat : ℕ) : ℝ) = if b then (1 : ℝ) else 0 := by
    intro b; cases b <;> simp
  simp only [regret, expRegret, bestLoss, cumLoss, Machine.expLoss, h1, hb]

/-- The target of `Pool.P0001` implies the restatement. -/
theorem of_pool (h : MinimaxPolylogAchievable) : Achievable := by
  obtain ⟨F, hom, ⟨C, k, hmem⟩, C', k', hreg⟩ := h
  refine ⟨C, k, C', k', fun n T hn hnT => ?_⟩
  refine ⟨(F n T hn).State, (F n T hn).fintypeState, (F n T hn).init, (F n T hn).act 0,
    (F n T hn).next 0, ?_, ?_⟩
  · exact hmem n T hn hnT
  · intro ℓ
    rw [← regret_eq (F n T hn) (hom n T hn) ℓ T]
    exact hreg n T hn hnT ℓ

/-- The main theorem, restated with the Mathlib-only definitions of `Checks/Statement.lean`. -/
theorem achievable : Achievable := of_pool Pool.P0294.main

end Restated

#print axioms Restated.achievable
