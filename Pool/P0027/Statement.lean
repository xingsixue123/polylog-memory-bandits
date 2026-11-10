import Pool.P0015.Block
import Pool.P0001.Targets

/-!
# Statement: the single-probe block rate, conditional on play-blind one-query learners

* `PlayBlind A`: the one-query machine `A` (a `Pool.P0015.QMachine n 1`) never uses the loss bit of its
  played arm: its next-state law is the same whatever that bit is.
* `PlayBlindLearners` (hypothesis): for all `1 ≤ n ≤ T` there is a play-blind one-query machine with at most
  `C (log (n T))^k` bits and regret at most `c √(n T) (log (n T))^j` on every loss sequence (fixed constants).
* `ProbeRate` (conclusion): homogeneous single-query P0001 machines with polylogarithmic memory and regret at
  most `C' n^{1/3} T^{2/3} (log (n T))^k'` for all `1 ≤ n ≤ T`.
* The main theorem `Pool.P0027.probeRate_of_playBlindLearners : PlayBlindLearners → ProbeRate` is in
  `Proof.lean`.
-/

namespace Pool.P0027

open Pool.P0001 Pool.P0015

/-- `A` never uses the loss bit of its played arm. -/
def PlayBlind {n : ℕ} (A : QMachine n 1) : Prop :=
  ∀ t s a (y y' : Bool) (o : Fin 1 → Bool), A.next t s a (y, o) = A.next t s a (y', o)

/-- Hypothesis: play-blind one-free-query learners with polylogarithmic memory and regret
`c √(n T) (log (n T))^j` exist for all `1 ≤ n ≤ T`. -/
def PlayBlindLearners : Prop :=
  ∃ (C c : ℝ) (k j : ℕ), ∀ n T : ℕ, 1 ≤ n → n ≤ T →
    ∃ A : QMachine n 1, PlayBlind A ∧ A.memBits ≤ C * Real.log (n * T) ^ k ∧
      ∀ ℓ : LossSeq n, A.regret ℓ T ≤ c * Real.sqrt (n * T) * Real.log (n * T) ^ j

/-- Conclusion: homogeneous single-query machines with polylogarithmic memory and regret
`C' n^{1/3} T^{2/3} (log (n T))^k'` for all `1 ≤ n ≤ T`. -/
def ProbeRate : Prop :=
  ∃ F : Family, (∀ n T hn, (F n T hn).IsHomogeneous) ∧ (∃ (C : ℝ) (k : ℕ), MemoryBound F C k) ∧
    ∃ (C' : ℝ) (k' : ℕ), RegretBound F fun n T =>
      C' * ((n : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3)) * Real.log (n * T) ^ k'

end Pool.P0027
