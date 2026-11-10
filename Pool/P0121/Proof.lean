import Pool.P0121.Params
import Pool.P0121.Statement
import Pool.P0021.Proof

/-!
# P0021's hypothesis `KQueryLearners`, from the concrete threaded machine
-/

open Pool.P0001 Pool.P0015

namespace Pool.P0121.TClaim

/-- A one-state `0`-query machine that always plays arm `0`. -/
noncomputable def trivQ (n : ℕ) [NeZero n] : QMachine n 0 where
  State := Unit
  init := PMF.pure ()
  act _ _ := PMF.pure (0, Fin.elim0)
  next _ _ _ _ := PMF.pure ()

theorem trivQ_memBits (n : ℕ) [NeZero n] : (trivQ n).memBits = 0 := by
  show Real.logb 2 (Fintype.card Unit) = 0
  rw [Fintype.card_unit]; simp

/-- With one arm every `K`-query machine has regret `0`. -/
theorem regret_one {K : ℕ} (A : QMachine 1 K) (ℓ : LossSeq 1) (T : ℕ) : A.regret ℓ T = 0 := by
  have hexp : ∀ t, A.expLoss ℓ t = ((ℓ t 0).toNat : ℝ) := by
    intro t
    unfold QMachine.expLoss
    rw [Fin.sum_univ_one]
    have : (A.armDist ℓ t 0) = 1 := by
      have := (A.armDist ℓ t).tsum_coe
      rwa [tsum_fintype (L := .unconditional _), Fin.sum_univ_one] at this
    rw [this]; simp
  have hbest : bestLoss ℓ T = cumLoss ℓ T 0 := by simp [bestLoss]
  rw [QMachine.regret, hbest, cumLoss]
  simp [hexp]

/-- **The explicit K-query rate.** -/
theorem kQueryRate : Pool.P0121.KQueryRate := by
  intro n T hn hnT
  have hT1 : 1 ≤ T := le_trans hn hnT
  have hl : 0 ≤ Real.log ((n : ℝ) * T) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    nlinarith)
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · -- one arm
    have hn1 : n = 1 := by omega
    subst hn1
    refine ⟨0, trivQ 1, by simp; positivity, by rw [trivQ_memBits]; positivity, fun ℓ => ?_⟩
    rw [regret_one]
    positivity
  · have : NeZero n := ⟨by omega⟩
    exact ⟨Pool.P0121.TPar.Nsp n T, Pool.P0121.TPar.tmP n T, Pool.P0121.TPar.Nsp_le_log h2 hnT,
      Pool.P0121.TPar.memBits_tmP_le h2 hnT, fun ℓ => Pool.P0121.TPar.regret_tmP_final h2 hnT ℓ⟩

/-- **P0021's hypothesis holds.** -/
theorem kQueryLearners : Pool.P0021.KQueryLearners :=
  ⟨4 * 10 ^ 12, 4 * 10 ^ 27, 10 ^ 17, 12, 26, 16, kQueryRate⟩

/-- **Single-query rate** (P0021's `blockRate_of_kQueryLearners`). -/
theorem singleQueryRate : Pool.P0121.SingleQueryRate := Pool.P0021.blockRate_of_kQueryLearners kQueryLearners

end Pool.P0121.TClaim
