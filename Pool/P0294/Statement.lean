import Pool.P0294.Probing

/-!
# Statement

* `Pool.P0294.goodBound` (in `Probing.lean`): P0292's open hypothesis `GoodBound` holds with `Cg = 10¹⁷·5³⁰`,
  `kg = 30`: at P0284's one-level machine the array-averaged probing remainder of P0258's machine bound is
  `≤ Cg·Lg(n,T)³⁰·√(nT/q)`.
* `main`: P0001's `MinimaxPolylogAchievable` (homogeneous single-query machines with `C·log(nT)^k` bits and regret
  `C'·√(nT)·log(nT)^k'` for all `1 ≤ n ≤ T`), via P0292's `main`, P0278 and P0173.
-/

open Pool.P0001

namespace Pool.P0294

/-- **Adversarial bandits with one pull per round and polylogarithmic memory achieve `Õ(√(nT))` regret.** -/
theorem main : MinimaxPolylogAchievable := Pool.P0292.main goodBound

end Pool.P0294
