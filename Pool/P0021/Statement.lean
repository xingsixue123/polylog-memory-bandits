import Pool.P0015.Block
import Pool.P0001.Targets

/-!
# Statement: the block rate, conditional on `K`-query learners

* `KQueryLearners`: the hypothesis. For all `1 ≤ n ≤ T` there are a `K` with `K ≤ cK (log (n T))^kK` and a
  `K`-query machine (`Pool.P0015.QMachine n K`) with at most `C (log (n T))^k` bits of memory and regret at most
  `c √(n T) (log (n T))^j` on every loss sequence. The constants `cK C c kK k j` are fixed and independent of
  `n, T`.
* `BlockRate`: the conclusion. A family of homogeneous single-query P0001 machines with polylogarithmic
  memory (P0001's `MemoryBound`) and, for all `1 ≤ n ≤ T`, regret at most
  `C' (n^{1/3} T^{2/3} + n √T) (log (n T))^k'` (P0001's `RegretBound`).
* The main theorem `Pool.P0021.blockRate_of_kQueryLearners : KQueryLearners → BlockRate` is in `Proof.lean`.
-/

namespace Pool.P0021

open Pool.P0001 Pool.P0015

/-- Hypothesis: `K`-query learners (`K` polylogarithmic) with polylogarithmic memory and regret
`c √(n T) (log (n T))^j` exist for all `1 ≤ n ≤ T`. -/
def KQueryLearners : Prop :=
  ∃ (cK C c : ℝ) (kK k j : ℕ), ∀ n T : ℕ, 1 ≤ n → n ≤ T →
    ∃ (K : ℕ) (A : QMachine n K), (K : ℝ) ≤ cK * Real.log (n * T) ^ kK ∧
      A.memBits ≤ C * Real.log (n * T) ^ k ∧
      ∀ ℓ : LossSeq n, A.regret ℓ T ≤ c * Real.sqrt (n * T) * Real.log (n * T) ^ j

/-- The conclusion: homogeneous single-query machines with polylogarithmic memory and regret
`C' (n^{1/3} T^{2/3} + n √T) (log (n T))^k'` for all `1 ≤ n ≤ T`. -/
def BlockRate : Prop :=
  ∃ F : Family, (∀ n T hn, (F n T hn).IsHomogeneous) ∧ (∃ (C : ℝ) (k : ℕ), MemoryBound F C k) ∧
    ∃ (C' : ℝ) (k' : ℕ), RegretBound F fun n T =>
      C' * ((n : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) + n * Real.sqrt T) *
        Real.log (n * T) ^ k'

end Pool.P0021
