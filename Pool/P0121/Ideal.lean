import Pool.P0102.Learner

/-!
# The ideal learner recursion along given presence sets (P0102's `Rec` with unbounded integers)
-/

open Finset

namespace Pool.P0121.TMI

variable {ι : Type} [Fintype ι] [DecidableEq ι] (L : ℕ) (prs : ℕ → Finset ι) (b : ℕ → ι → ℕ) (η ε : ℝ)

/-- The ideal learner data: grid index and per-copy, per-level (loss since wake, index at wake). -/
noncomputable def ideal : ℕ → ℕ × (ι → ℕ → ℕ × ℕ)
  | 0 => (0, fun _ _ => (0, 0))
  | u + 1 =>
    let k' := (ideal u).1 + Pool.P0102.inc L prs b η ε (fun _ => (ideal u).1) (fun _ => (ideal u).2) u
    (k', fun f ℓ => if f ∈ prs u ∧ ¬ 2 ^ ℓ ∣ u + 1 then (((ideal u).2 f ℓ).1 + b u f, ((ideal u).2 f ℓ).2)
      else (0, k'))

/-- The ideal data satisfies P0102's recursion. -/
theorem ideal_rec : Pool.P0102.Rec L prs b η ε (fun u => (ideal L prs b η ε u).1) (fun u => (ideal L prs b η ε u).2) where
  k0 := rfl
  kS _ := rfl
  w0 _ _ _ := rfl
  wS _ _ _ _ := rfl

/-- Losses since wake are below the block offset. -/
theorem ideal_C_le (hb : ∀ u f, b u f ≤ 1) : ∀ u, ∀ f ∈ prs u, ∀ ℓ,
    ((ideal L prs b η ε u).2 f ℓ).1 ≤ u - Pool.P0102.blk ℓ u
  | 0, f, _, ℓ => by simp [ideal]
  | u + 1, f, hf, ℓ => by
    show (if f ∈ prs u ∧ ¬ 2 ^ ℓ ∣ u + 1 then _ else _ : ℕ × ℕ).1 ≤ _
    split_ifs with h
    · have ih := ideal_C_le hb u f h.1 ℓ
      rw [Pool.P0102.blk_succ ℓ u h.2]
      have := Pool.P0102.blk_le ℓ u
      have := hb u f
      simp only
      omega
    · exact Nat.zero_le _

theorem ideal_C_lt (hb : ∀ u f, b u f ≤ 1) (u : ℕ) (f : ι) (hf : f ∈ prs u) (ℓ : ℕ) :
    ((ideal L prs b η ε u).2 f ℓ).1 < 2 ^ ℓ := by
  have h1 := ideal_C_le L prs b η ε hb u f hf ℓ
  have h2 := Pool.P0102.lt_blk_add ℓ u
  have h3 := Pool.P0102.blk_le ℓ u
  omega

/-- Wake indices are at most the current grid index. -/
theorem ideal_k_le : ∀ u f ℓ, ((ideal L prs b η ε u).2 f ℓ).2 ≤ (ideal L prs b η ε u).1
  | 0, f, ℓ => by simp [ideal]
  | u + 1, f, ℓ => by
    show (if f ∈ prs u ∧ ¬ 2 ^ ℓ ∣ u + 1 then _ else _ : ℕ × ℕ).2 ≤ _
    split_ifs with h
    · have := ideal_k_le u f ℓ
      show ((ideal L prs b η ε u).2 f ℓ).2 ≤ (ideal L prs b η ε u).1 + _
      omega
    · exact le_rfl

end Pool.P0121.TMI
