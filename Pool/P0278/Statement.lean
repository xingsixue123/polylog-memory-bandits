import Pool.P0278.Family

/-!
# Statement

* `Pool.P0278.FamHyp C k` (in `Family.lean`): for every `1 ≤ n ≤ T`, every rate `n/T ≤ q ≤ 1/32` and every
  homogeneous coin algorithm `A`, a homogeneous coin algorithm with `≤ C·Lg^k` extra bits and regret over `T` rounds
  `≤ C·Lg^k·√(nT/q) + β·regret(Sub(A, γ), ℓ', Tb)`, with `0 < γ`, `0 ≤ β ≤ 2γ`, `γ·Tb ≤ q·T` and `Tb ≤ 2T`.
* `Pool.P0278.FamHypAt C k` (in `Family.lean`): the same at the single rate `q = qOf (max C 0 + 6) k n T` (required
  only when `n/T ≤ q`); this is all the proof uses. `famHypAt_of_famHyp`: `FamHyp → FamHypAt`.
* `stepAtIn_at`, `main_at`: from `FamHypAt C k`.
* `stepAtIn`: `FamHyp C k` gives P0173's `StepAtIn CoinCls (max C 0 + 6) k`.
* `main`: `FamHyp C k` gives P0001's `MinimaxPolylogAchievable`.
-/

open Pool.P0001

namespace Pool.P0278

theorem stepAtIn {C : ℝ} {k : ℕ} (hF : FamHyp C k) :
    Pool.P0173.StepAtIn (fun {n} M => Pool.P0173.CoinCls (n := n) M) (max C 0 + 6) k :=
  stepAtIn_of_famHyp hF

theorem main {C : ℝ} {k : ℕ} (hF : FamHyp C k) : MinimaxPolylogAchievable :=
  Pool.P0173.mainCoin (stepAtIn_of_famHyp hF)

theorem stepAtIn_at {C : ℝ} {k : ℕ} (hF : FamHypAt C k) :
    Pool.P0173.StepAtIn (fun {n} M => Pool.P0173.CoinCls (n := n) M) (max C 0 + 6) k :=
  stepAtIn_of_famHypAt hF

theorem main_at {C : ℝ} {k : ℕ} (hF : FamHypAt C k) : MinimaxPolylogAchievable :=
  Pool.P0173.mainCoin (stepAtIn_of_famHypAt hF)

end Pool.P0278
