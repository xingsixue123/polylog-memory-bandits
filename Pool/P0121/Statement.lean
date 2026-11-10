import Pool.P0021.Statement

/-!
# Statements: K-query learners with explicit polylog constants, and the single-query rate (via P0021)

* `KQueryRate`: for all `1 ≤ n ≤ T` there is a P0015 `K`-query machine (time-dependent; P0015's `memBits` counts
  its states, no clock) with `K ≤ 4·10^12·log(nT)^12` queries per day, `memBits ≤ 4·10^27·log(nT)^26` and
  expected regret `≤ 10^17·√(nT)·log(nT)^16` against every oblivious loss sequence over `T` rounds.
* `SingleQueryRate` is P0021's `BlockRate`: a P0001 `Family` of homogeneous single-query machines with
  `MemoryBound F C k` and `RegretBound F` for `C'·(n^{1/3}T^{2/3} + n√T)·log(nT)^{k'}`, for all `1 ≤ n ≤ T`.
-/

open Pool.P0001 Pool.P0015

namespace Pool.P0121

/-- `K`-query learners with explicit polylogarithmic constants. -/
def KQueryRate : Prop :=
  ∀ n T : ℕ, 1 ≤ n → n ≤ T → ∃ (K : ℕ) (A : QMachine n K),
    (K : ℝ) ≤ 4 * 10 ^ 12 * Real.log (n * T) ^ 12 ∧
    A.memBits ≤ 4 * 10 ^ 27 * Real.log (n * T) ^ 26 ∧
    ∀ ℓ : LossSeq n, A.regret ℓ T ≤ 10 ^ 17 * Real.sqrt (n * T) * Real.log (n * T) ^ 16

/-- The single-query rate of P0021: homogeneous single-query machines, polylog bits,
regret `Õ(n^{1/3}T^{2/3} + n√T)` for all `1 ≤ n ≤ T`. -/
abbrev SingleQueryRate : Prop := Pool.P0021.BlockRate

end Pool.P0121
