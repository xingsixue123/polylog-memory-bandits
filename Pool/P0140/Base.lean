import Pool.P0067.SubFixed
import Pool.P0121.Proof

/-!
# Prefix regret by zero padding, and a subsampled kernel-checked base learner (P0136's BASE, step S3)

* `zeroAfter ℓ m`: the loss sequence `ℓ` on rounds `< m`, then all losses `0` (`false`).
* `regret_zeroAfter`: for `m ≤ H`, the regret of any P0001 machine over `H` rounds on `zeroAfter ℓ m` equals its
  regret over the first `m` rounds on `ℓ`. The machine's state law before round `m` reads only `ℓ` before `m`
  (P0055's `stateDist_congr`), and padded rounds cost `0` to the machine and to every arm.
* `regret_prefix_le`: a bound `ρ` on the regret over `H` rounds against **every** sequence bounds the regret on
  every prefix `m ≤ H` (against every sequence). This is the prefix hypothesis of P0067's `regret_Sub_le_fixed`, for
  any fixed-horizon learner.
* `memBits_Sub`: P0055's subsampled machine has the same states, hence the same memory.
* `subBase_regret`: P0121's kernel-checked homogeneous single-query family `F` (polylog bits, regret
  `C'(n^{1/3}T^{2/3} + n√T)log(nT)^{k'}`), tuned for horizon `H ≥ n` and updated with probability `γ` per round
  (P0055's `Sub`), has regret over `T` rounds
  `≤ (1/γ)·(max 0 (C'(n^{1/3}H^{2/3} + n√H)log(nH)^{k'}) + T·e^{−x})` whenever `2(γT + x) ≤ H + 1`.
  This is the BASE learner of P0136 §1 (BASE plays every round and learns only on its own `q_B` rounds), with
  `γ = q_B`, and it discharges P0136's open step S3 (no anytime hypothesis is needed).
-/

open Finset
open scoped ENNReal

namespace Pool.P0140

open Pool.P0001 Pool.P0055

variable {n : ℕ}

/-- `ℓ` up to round `m`, then all losses `0`. -/
def zeroAfter (ℓ : LossSeq n) (m : ℕ) : LossSeq n := fun t a => if t < m then ℓ t a else false

lemma expLoss_zeroAfter_lt (M : Machine n) (ℓ : LossSeq n) {m t : ℕ} (ht : t < m) :
    M.expLoss (zeroAfter ℓ m) t = M.expLoss ℓ t := by
  have hs : M.stateDist (zeroAfter ℓ m) t = M.stateDist ℓ t :=
    stateDist_congr M t (fun k hk => by funext a; simp [zeroAfter, show k < m by omega])
  simp only [Machine.expLoss, Machine.armDist, hs, zeroAfter, ht, ite_true]

lemma expLoss_zeroAfter_ge (M : Machine n) (ℓ : LossSeq n) {m t : ℕ} (ht : m ≤ t) :
    M.expLoss (zeroAfter ℓ m) t = 0 := by
  simp [Machine.expLoss, zeroAfter, show ¬ t < m by omega]

lemma cumLoss_zeroAfter (ℓ : LossSeq n) {m H : ℕ} (hm : m ≤ H) (i : Fin n) :
    cumLoss (zeroAfter ℓ m) H i = cumLoss ℓ m i := by
  unfold cumLoss
  rw [← Finset.sum_range_add_sum_Ico _ hm]
  have h2 : ∑ t ∈ Finset.Ico m H, (((zeroAfter ℓ m) t i).toNat : ℝ) = 0 :=
    Finset.sum_eq_zero fun t ht => by
      simp [zeroAfter, show ¬ t < m by simp at ht; omega]
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun t ht => by simp [zeroAfter, Finset.mem_range.mp ht]

/-- The regret on a prefix of `m ≤ H` rounds is the regret over `H` rounds of the zero-padded sequence. -/
theorem regret_zeroAfter (M : Machine n) (ℓ : LossSeq n) {m H : ℕ} (hm : m ≤ H) :
    regret M (zeroAfter ℓ m) H = regret M ℓ m := by
  unfold regret bestLoss
  congr 1
  · rw [← Finset.sum_range_add_sum_Ico _ hm]
    have h2 : ∑ t ∈ Finset.Ico m H, M.expLoss (zeroAfter ℓ m) t = 0 :=
      Finset.sum_eq_zero fun t ht => expLoss_zeroAfter_ge M ℓ (by simp at ht; omega)
    rw [h2, add_zero]
    exact Finset.sum_congr rfl fun t ht => expLoss_zeroAfter_lt M ℓ (Finset.mem_range.mp ht)
  · congr 1
    funext i
    exact cumLoss_zeroAfter ℓ hm i

/-- A bound on the regret over `H` rounds against every sequence bounds the regret on every prefix. -/
theorem regret_prefix_le (M : Machine n) {H : ℕ} {ρ : ℝ} (hR : ∀ ℓ : LossSeq n, regret M ℓ H ≤ ρ)
    (ℓ : LossSeq n) {m : ℕ} (hm : m ≤ H) : regret M ℓ m ≤ ρ := by
  rw [← regret_zeroAfter M ℓ hm]
  exact hR _

end Pool.P0140

namespace Pool.P0140

open Pool.P0001 Pool.P0055

/-- The memory of `Sub A γ` is that of `A` (same states). -/
lemma memBits_Sub {n : ℕ} (A : Machine n) (γ : ℝ) (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (Sub A γ h0 h1).memBits = A.memBits := rfl

/-- **Subsampled base learner.** There is a family `F` of homogeneous single-query machines with polylog memory
(the witness is P0121's family, but the statement only asserts the listed properties) such that `F n H`, tuned for
horizon `H` and updated only with probability `γ` each round (P0055's `Sub`), has regret over `T` rounds at most
`(1/γ)·(max 0 (C'(n^{1/3}H^{2/3} + n√H) log(nH)^{k'}) + T e^{−x})` whenever `2(γT + x) ≤ H + 1`, for every
`1 ≤ n ≤ H`. See `subBase` for the same bound packaged with the properties of the subsampled machines themselves. -/
theorem subBase_regret :
    ∃ F : Family, (∀ n T hn, (F n T hn).IsHomogeneous) ∧ (∃ (C : ℝ) (k : ℕ), MemoryBound F C k) ∧
      ∃ (C' : ℝ) (k' : ℕ), ∀ (n H : ℕ) (hn : 1 ≤ n), n ≤ H →
        ∀ {γ : ℝ} (hγ : 0 < γ) (h1 : γ ≤ 1) (ℓ : LossSeq n) (T : ℕ) {x : ℝ},
          2 * (γ * T + x) ≤ H + 1 →
          regret (Sub (F n H hn) γ hγ.le h1) ℓ T ≤
            (1 / γ) * (max 0 (C' * ((n : ℝ) ^ ((1 : ℝ) / 3) * (H : ℝ) ^ ((2 : ℝ) / 3) + n * Real.sqrt H) *
              Real.log (n * H) ^ k') + T * Real.exp (-x)) := by
  obtain ⟨F, hhom, hmem, C', k', hreg⟩ := Pool.P0121.TClaim.singleQueryRate
  refine ⟨F, hhom, hmem, C', k', ?_⟩
  intro n H hn hnH γ hγ h1 ℓ T x hx
  have : NeZero n := ⟨by omega⟩
  set ρ := max 0 (C' * ((n : ℝ) ^ ((1 : ℝ) / 3) * (H : ℝ) ^ ((2 : ℝ) / 3) + n * Real.sqrt H) *
    Real.log (n * H) ^ k')
  have hR : ∀ (ℓ' : LossSeq n) m, m ≤ T → m ≤ H → regret (F n H hn) ℓ' m ≤ ρ := by
    intro ℓ' m _ hmH
    exact regret_prefix_le (F n H hn) (fun ℓ'' => (hreg n H hn hnH ℓ'').trans (le_max_right _ _)) ℓ' hmH
  refine (Pool.P0067.regret_Sub_le_fixed (F n H hn) (hhom n H hn) hγ h1 ℓ T H ρ (le_max_left _ _) hR).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have ht := Pool.P0067.tail_le_exp hγ.le T H hx
  have hT : (0 : ℝ) ≤ T := by positivity
  nlinarith [mul_le_mul_of_nonneg_left ht hT]

/-- **The subsampled machines themselves.** For the family of `subBase_regret`: every `Sub (F n H) γ` with
`1 ≤ n ≤ H` is homogeneous, uses at most `C·log(nH)^k` bits (polylog in the TUNING horizon `H`; this is polylog in
`nT` when `H ≤ poly(T)`, e.g. `H ≤ T`), and has the regret bound of `subBase_regret` over every horizon `T` with
`2(γT + x) ≤ H + 1`. -/
theorem subBase :
    ∃ (F : Family) (C : ℝ) (k : ℕ) (C' : ℝ) (k' : ℕ), ∀ (n H : ℕ) (hn : 1 ≤ n), n ≤ H →
      ∀ {γ : ℝ} (hγ : 0 < γ) (h1 : γ ≤ 1),
        (Sub (F n H hn) γ hγ.le h1).IsHomogeneous ∧
        (Sub (F n H hn) γ hγ.le h1).memBits ≤ C * Real.log (n * H) ^ k ∧
        ∀ (ℓ : LossSeq n) (T : ℕ) {x : ℝ}, 2 * (γ * T + x) ≤ H + 1 →
          regret (Sub (F n H hn) γ hγ.le h1) ℓ T ≤
            (1 / γ) * (max 0 (C' * ((n : ℝ) ^ ((1 : ℝ) / 3) * (H : ℝ) ^ ((2 : ℝ) / 3) + n * Real.sqrt H) *
              Real.log (n * H) ^ k') + T * Real.exp (-x)) := by
  obtain ⟨F, _, ⟨C, k, hmem⟩, C', k', hreg⟩ := subBase_regret
  refine ⟨F, C, k, C', k', fun n H hn hnH γ hγ h1 => ⟨⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩, ?_,
    fun ℓ T x hx => hreg n H hn hnH hγ h1 ℓ T hx⟩⟩
  rw [memBits_Sub]
  exact hmem n H hn hnH

end Pool.P0140
