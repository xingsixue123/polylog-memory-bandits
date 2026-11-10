import Pool.P0046.Coins
import Pool.P0034.Coins

/-!
# Bridge to P0034's constant-probability coin model, and a concrete-type usage check
-/

namespace Pool.P0046

open Finset

/-- At a constant probability, `bw` is P0034's `wt`. -/
theorem bw_const_eq_wt {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (ω : ι → Bool) :
    bw (fun _ => p) ω = Pool.P0034.wt p ω := rfl

/-- At a constant probability, `bprob` is P0034's `prob`. -/
theorem bprob_const_eq_prob {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (A : (ι → Bool) → Prop) :
    bprob (fun _ => p) A = Pool.P0034.prob p A := by
  classical
  unfold bprob Pool.P0034.prob
  apply sum_congr rfl; intro ω _
  by_cases h : A ω
  · rw [Pool.P0034.ind_pos h]; simp [h]; rfl
  · rw [Pool.P0034.ind_neg h]; simp [h]

/-- Usage check at concrete types: `fresh_slot_set` applies with `exact` (no `convert`). -/
example (p : ℝ) :
    (∑ ω : Fin 1 → Fin 2 → Bool, bw2 (fun (_ : Fin 1) (_ : Fin 2) => p) ω *
      (((Finset.univ : Finset (Fin 2)).filter (fun c => ω 0 c = true)).card : ℝ)) =
    ∑ ω : Fin 1 → Fin 2 → Bool, bw2 (fun (_ : Fin 1) (_ : Fin 2) => p) ω *
        ∑ F ∈ (Finset.univ : Finset (Fin 2)).powerset,
          p ^ F.card * (1 - p) ^ ((Finset.univ : Finset (Fin 2)).card - F.card) * (F.card : ℝ) :=
  fresh_slot_set (σ := Fin 1) (κ := Fin 2) (fun _ _ => p) 0 p (fun _ => rfl)
    (fun _ => (Finset.univ : Finset (Fin 2))) (fun _ _ _ => rfl) (fun _ F => (F.card : ℝ))

/-- Usage check: `sum_bw2` applies with `exact` at concrete types. -/
example : ∑ ω : Fin 2 → Fin 3 → Bool, bw2 (fun (_ : Fin 2) (_ : Fin 3) => (1 / 3 : ℝ)) ω = 1 :=
  sum_bw2 _

end Pool.P0046
