import Pool.P0292.Assembly

/-!
# Statement

* `Pool.P0292.GoodBound Cg kg` (in `Assembly.lean`): at P0284's one-level machine `famM n T q A` (process horizon
  `Tp`), the probing remainder of P0258's machine bound, averaged over the sampling/filter arrays, with P0243's ALG
  budgets (`vF`, `ρF`, `0`, `rF`) and P0282's rate floor `xf`, is at most `Cg·Lg(n,T)^kg·√(nT/q)`, for all
  `1 ≤ n ≤ T`, `n/T ≤ q ≤ 1/32`, every BASE `A`, loss sequence and initial coin.
* `famHyp`: `GoodBound Cg kg` gives P0278's `FamHyp (CF Cg) (max 28 kg)` (with P0284's machine `machF`).
* `main`: `GoodBound Cg kg` gives P0001's `MinimaxPolylogAchievable`.
-/

open Pool.P0001

namespace Pool.P0292

theorem famHyp {Cg : ℝ} {kg : ℕ} (hG : GoodBound Cg kg) : Pool.P0278.FamHyp (CF Cg) (max 28 kg) :=
  famHyp_of_good hG

theorem main {Cg : ℝ} {kg : ℕ} (hG : GoodBound Cg kg) : MinimaxPolylogAchievable :=
  Pool.P0278.main (famHyp_of_good hG)

end Pool.P0292
