import Pool.P0173.StepClass

/-!
# Statement

* `Pool.P0173.StepAtIn Cls c k`: P0161's one-level step at the rate `qOf c k n T` with bases and outputs in `Cls`.
* `mainIn`: a class with a homogeneous zero-bit member for every `n ≥ 1` + `StepAtIn Cls c k` ⟹ P0001's
  `MinimaxPolylogAchievable`.
* `mainCoin`: the same for `Cls = CoinCls` (machines `A.toMachine` of homogeneous P0050 coin algorithms).
-/

open Pool.P0001

namespace Pool.P0173

theorem mainIn {Cls : ∀ {n : ℕ}, Machine n → Prop} {c : ℝ} {k : ℕ} (hstep : StepAtIn Cls c k)
    (hzero : ∀ (n : ℕ), 1 ≤ n → ∃ M0 : Machine n, Cls M0 ∧ M0.IsHomogeneous ∧ M0.memBits ≤ 0) :
    MinimaxPolylogAchievable :=
  minimax_of_StepAtIn hstep hzero

theorem mainCoin {c : ℝ} {k : ℕ} (hstep : StepAtIn (fun {n} M => CoinCls (n := n) M) c k) :
    MinimaxPolylogAchievable :=
  minimax_of_StepAtCoin hstep

end Pool.P0173
