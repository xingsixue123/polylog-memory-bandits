import Pool.P0015.Block
/-!
# The loss of the block machine

* `sum_block_pulled_le`: inside one block, the pulled arms lose at most `K` more than the played
  arm (only the `K` query positions deviate from it).
* `sum_block_eq`: the loss of an arm over a block is `B` times the mean of its virtual loss over
  the offset.
* `sum_expLoss_blockMachine_le`: the expected loss of the block machine over `T'` blocks is at
  most `∑_b (B * E[virtual loss of A's played arm on day b] + K)`.
-/

open scoped ENNReal

namespace Pool.P0015

open Pool.P0001

variable {n K B : ℕ} (hB : n ≤ B) (hB0 : 0 < B) (A : QMachine n K)

/-- Loss bit as a real number. -/
abbrev φ (b : Bool) : ℝ := (b.toNat : ℝ)

lemma φ_le_one (b : Bool) : φ b ≤ 1 := by cases b <;> simp [φ]
lemma φ_nonneg (b : Bool) : 0 ≤ φ b := by positivity

/-! ### Losses inside one block -/

lemma sum_block_eq (ℓ : LossSeq n) (q : ℕ) (i : Fin n) :
    ∑ r : Fin B, φ (ℓ (q * B + r) i) = B * E (unif B hB0) (fun u => φ (virt hB ℓ q u i)) := by
  rw [E_unif]
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB0.ne'
  rw [← mul_assoc, mul_one_div_cancel hB', one_mul]
  have : NeZero B := ⟨hB0.ne'⟩
  simp only [virt, pos]
  exact (Fintype.sum_equiv (Equiv.addLeft (Fin.castLE hB i)) _ _ (fun u => rfl)).symm

lemma sum_block_pulled_le (hB : n ≤ B) (hB0 : 0 < B) (ℓ : LossSeq n) (q : ℕ) (a : QAct n K) (u : Fin B) :
    ∑ r : Fin B, φ (ℓ (q * B + r) (pulled a u r)) ≤ ∑ r : Fin B, φ (ℓ (q * B + r) a.1) + K := by
  classical
  set S : Finset (Fin B) := Finset.univ.image fun k => pos hB (a.2 k) u
  have hS : (S.card : ℝ) ≤ K := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin K))) (f := fun k => pos hB (a.2 k) u)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    exact_mod_cast this
  have key : ∀ r : Fin B, φ (ℓ (q * B + r) (pulled a u r)) ≤
      φ (ℓ (q * B + r) a.1) + (if r ∈ S then 1 else 0) := by
    intro r
    by_cases h : pulled a u r = a.1
    · rw [h]; split_ifs <;> linarith
    · obtain ⟨k, hk⟩ := pulled_ne hB hB0 a u r h
      have hr : r ∈ S := Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩
      rw [if_pos hr]
      linarith [φ_le_one (ℓ (q * B + r) (pulled a u r)), φ_nonneg (ℓ (q * B + r) a.1)]
  calc ∑ r : Fin B, φ (ℓ (q * B + r) (pulled a u r))
      ≤ ∑ r : Fin B, (φ (ℓ (q * B + r) a.1) + (if r ∈ S then 1 else 0)) :=
        Finset.sum_le_sum fun r _ => key r
    _ = ∑ r : Fin B, φ (ℓ (q * B + r) a.1) + S.card := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          nsmul_eq_mul, mul_one]
    _ ≤ _ := by linarith

/-- Expected loss of the block machine at position `r` of block `q`. -/
lemma expLoss_blockMachine (ℓ : LossSeq n) (q : ℕ) (r : Fin B) :
    (blockMachine hB hB0 A).expLoss ℓ (q * B + r) =
      E (avgA hB hB0 A ℓ q) (fun s => E (A.act q s) (fun a => E (unif B hB0) (fun u =>
        φ (ℓ (q * B + r) (pulled a u r))))) := by
  classical
  obtain ⟨hq, hr⟩ := divmod_aux (B := B) q r r.is_lt
  change E ((blockMachine hB hB0 A).armDist ℓ (q * B + r)) _ = _
  rw [Machine.armDist, E_bind, stateDist_blockMachine, hq, hr, rep, E_bind]
  refine congrArg _ (funext fun s => ?_)
  rw [E_bind]
  refine congrArg _ (funext fun a => ?_)
  rw [E_map]
  refine congrArg _ (funext fun u => ?_)
  simp only [E_pure, hr]

lemma sum_range_mul_eq (f : ℕ → ℝ) (T' : ℕ) :
    ∑ t ∈ Finset.range (T' * B), f t = ∑ q ∈ Finset.range T', ∑ r : Fin B, f (q * B + r) := by
  induction T' with
  | zero => simp
  | succ T' ih =>
    rw [show (T' + 1) * B = T' * B + B by ring, Finset.sum_range_add, ih, Finset.sum_range_succ,
      Fin.sum_univ_eq_sum_range (fun r => f (T' * B + r))]

/-- The total expected loss of the block machine over `T'` blocks. -/
lemma sum_expLoss_blockMachine_le (ℓ : LossSeq n) (T' : ℕ) :
    ∑ t ∈ Finset.range (T' * B), (blockMachine hB hB0 A).expLoss ℓ t ≤
      ∑ q ∈ Finset.range T', (B * E (avgA hB hB0 A ℓ q) (fun s => E (A.act q s) (fun a =>
        E (unif B hB0) (fun u => φ (virt hB ℓ q u a.1)))) + K) := by
  rw [sum_range_mul_eq]
  refine Finset.sum_le_sum fun q _ => ?_
  simp only [expLoss_blockMachine]
  rw [← E_sum, ← E_smul, ← E_const (avgA hB hB0 A ℓ q) (K : ℝ), ← E_add]
  refine E_mono _ fun s => ?_
  rw [← E_sum, ← E_smul, ← E_const (A.act q s) (K : ℝ), ← E_add]
  refine E_mono _ fun a => ?_
  rw [← E_sum, ← sum_block_eq hB hB0]
  calc E (unif B hB0) (fun u => ∑ r : Fin B, φ (ℓ (q * B + r) (pulled a u r)))
      ≤ E (unif B hB0) (fun _ => ∑ r : Fin B, φ (ℓ (q * B + r) a.1) + K) :=
        E_mono _ fun u => sum_block_pulled_le hB hB0 ℓ q a u
    _ = _ := E_const _ _

end Pool.P0015
