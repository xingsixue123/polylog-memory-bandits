import Pool.P0194.Proc
import Pool.P0196.Probing
import Pool.P0154.Credit

open Finset Pool.P0001 Pool.P0050 Pool.P0194

/-!
# Probing term of P0194's per-thread process at thread-dependent rates, pathwise

P0196 bounds the probing term of P0181's process for one-slot, uniform-rate layouts. In P0194's per-thread process a
member's probe rate is the weight of its slot's thread, and it grows when the member is inherited into a coarser
thread (P0150 §1). Here:

* `Pool.P0209.member_rate_le`: one member at a nonnegative, nondecreasing rate with (b″)-type checks every `Bmin`
  rounds (P0154's Abel + P0196's `sum_le_of_checks`): `Σ r·g ≤ r_last·(M + Bmin) + Σ (rate jump)·(lead)⁺`.
* `Pool.P0209.rateD`, `Pool.P0209.sum_probeD_eq`: the slot part of P0194's round loss minus BASE,
  `Σ_s x_{thread s}·(slotVal_s − bPol) = Σ_x rate_x·(ℓ_u(x) − bPol)`, exactly (no layout hypothesis).
* **`Pool.P0209.probe_totalD_le`**: over `T` rounds, the probing term is at most
  `Σ_x [rate_x(b x − 1)·(M x + Bmin) + credit_x]` when each copy's rate vanishes outside a window `[E x, b x)`, is
  nondecreasing on it, and the true gap since entry is `≤ M x` at the check boundaries inside.

The credit terms are P0154/P0162's input (bounded there against ALG's interval guarantees). Not done here: deriving
the window, the monotonicity (placement in the current thread, `xr` monotone in the thread) and the check bound
(rule (b″) did not fire + P0203's concentration) for P0194's run.
-/

namespace Pool.P0209

/-- **One member at a nondecreasing rate, checks every `Bmin` rounds.** If the gaps are `≤ 1`, the partial gap is
`≤ M` at every check boundary inside `(a, b)`, and the rate is nonnegative and nondecreasing on `[a, b)`, then
`Σ_{[a,b)} r·g ≤ r(b-1)·(M + Bmin) + Σ_{t∈[a+1,b)} (r t − r (t-1))·(−G[a,t))⁺`. -/
theorem member_rate_le (r g : ℕ → ℝ) (hg : ∀ t, g t ≤ 1) (a b Bmin : ℕ) (hab : a ≤ b) (hB : 0 < Bmin)
    (M : ℝ) (hM : 0 ≤ M) (hr0 : ∀ t, 0 ≤ r t)
    (hmono : ∀ t, a + 1 ≤ t → t < b → r (t - 1) ≤ r t)
    (hcheck : ∀ m, a < m → m < b → Bmin ∣ m → ∑ t ∈ Ico a m, g t ≤ M) :
    ∑ t ∈ Ico a b, r t * g t ≤
      r (b - 1) * (M + Bmin) + ∑ t ∈ Ico (a + 1) b, (r t - r (t - 1)) * max 0 (-Pool.P0154.isum g a t) := by
  rcases Nat.eq_or_lt_of_le hab with rfl | hlt
  · simp only [Finset.Ico_self, Finset.sum_empty]
    have : (Finset.Ico (a + 1) a) = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this, Finset.sum_empty, add_zero]
    exact mul_nonneg (hr0 _) (by positivity)
  have h1 := Pool.P0154.abel_le r g a b hlt hmono
  have h2 := Pool.P0196.sum_le_of_checks g hg a b Bmin hab hB M hM hcheck
  have h3 : r (b - 1) * Pool.P0154.isum g a b ≤ r (b - 1) * (M + Bmin) :=
    mul_le_mul_of_nonneg_left h2 (hr0 _)
  linarith

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- Total probe rate of copy `x` at round `u`: the sum of the rates of the slots it occupies (actively). -/
noncomputable def rateD (ω : ℕ → RC P) (u : ℕ) (x : ι) : ℝ :=
  ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), if occAtS P ℓ ω ωs φ u s = some x then P.xr s.1 else 0

/-- The probing term of round `u` (the slot part of P0194's `condLoss` minus BASE), member by member:
`Σ_s x_{thread s}·(slotVal_s − bPol) = Σ_x rate_x·(ℓ_u(x) − bPol_u)`. -/
theorem sum_probeD_eq (ω : ℕ → RC P) (u : ℕ) :
    ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - bPol P ℓ ω u) =
      ∑ x : ι, rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) := by
  have hs : ∀ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - bPol P ℓ ω u) =
      ∑ x : ι, (if occAtS P ℓ ω ωs φ u s = some x then P.xr s.1 else 0) * (ℓr P ℓ u x - bPol P ℓ ω u) := by
    intro s
    unfold slotVal
    rcases h : occAtS P ℓ ω ωs φ u s with _ | x
    · simp
    · simp only [Option.some.injEq]
      rw [Finset.sum_eq_single x]
      · simp [ℓr]
      · intro y _ hy; simp [Ne.symm hy]
      · simp
  rw [Finset.sum_congr rfl fun s _ => hs s, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold rateD
  rw [Finset.sum_mul]

/-- **Probing term of P0194's process at thread-dependent rates, pathwise.** Suppose every copy `x` that enters
before the horizon (`E x < T`) has a window `[E x, b x)` with `b x ≤ T` outside which its rate is `0` on `[0, T)`,
its rate is nondecreasing on the window (it follows the current thread, P0150 §1), and its true gap against BASE since
entry is `≤ M x` (`M x ≥ 0`) at every check boundary inside the window. Then
`Σ_{u<T} Σ_s x_{thread s}·(slotVal_s − bPol) ≤ Σ_{x : E x < T} [rate_x(b x − 1)·(M x + Bmin) + credit_x]`, with
`credit_x = Σ_{t∈[E x+1, b x)} (rate_x t − rate_x (t−1))·(−G_x[E x, t))⁺` (P0154/P0162's input). Copies entering
at or after `T` need no hypothesis beyond `hout` (their rate is `0` before `T`) and do not appear on the right. -/
theorem probe_totalD_le (ω : ℕ → RC P) (T : ℕ) (b : ι → ℕ) (M : ι → ℝ) (hB : 0 < P.Bmin)
    (hM : ∀ x, P.E x < T → 0 ≤ M x) (hEb : ∀ x, P.E x < T → P.E x ≤ b x)
    (hbT : ∀ x, P.E x < T → b x ≤ T)
    (hxr : ∀ j, 0 ≤ P.xr j)
    (hout : ∀ x u, u < T → (u < P.E x ∨ b x ≤ u) → rateD P ℓ ωs φ ω u x = 0)
    (hmono : ∀ x, P.E x < T → ∀ t, P.E x + 1 ≤ t → t < b x →
      rateD P ℓ ωs φ ω (t - 1) x ≤ rateD P ℓ ωs φ ω t x)
    (hcheck : ∀ x, P.E x < T → ∀ m, P.E x < m → m < b x → P.Bmin ∣ m →
      ∑ t ∈ Ico (P.E x) m, (ℓr P ℓ t x - bPol P ℓ ω t) ≤ M x) :
    ∑ u ∈ range T, ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - bPol P ℓ ω u) ≤
      ∑ x ∈ Finset.univ.filter (fun x => P.E x < T), (rateD P ℓ ωs φ ω (b x - 1) x * (M x + P.Bmin) +
        ∑ t ∈ Ico (P.E x + 1) (b x), (rateD P ℓ ωs φ ω t x - rateD P ℓ ωs φ ω (t - 1) x) *
          max 0 (-Pool.P0154.isum (fun t => ℓr P ℓ t x - bPol P ℓ ω t) (P.E x) t)) := by
  simp only [sum_probeD_eq]
  rw [Finset.sum_comm]
  -- copies entering at or after `T` contribute nothing
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => P.E x < T)]
  have hlate : ∑ x ∈ Finset.univ.filter (fun x => ¬ P.E x < T),
      ∑ u ∈ range T, rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) = 0 := by
    refine Finset.sum_eq_zero fun x hx => Finset.sum_eq_zero fun u hu => ?_
    have h1 := (Finset.mem_filter.1 hx).2
    have h2 := Finset.mem_range.1 hu
    rw [hout x u h2 (Or.inl (by omega)), zero_mul]
  rw [hlate, add_zero]
  refine Finset.sum_le_sum fun x hx => ?_
  have hxT : P.E x < T := (Finset.mem_filter.1 hx).2
  -- restrict to the window
  have hwin : ∑ u ∈ range T, rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) =
      ∑ u ∈ Ico (P.E x) (b x), rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) := by
    rw [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le (P.E x)) ((hEb x hxT).trans (hbT x hxT)),
      ← Finset.sum_Ico_consecutive _ (hEb x hxT) (hbT x hxT)]
    have h1 : ∑ u ∈ Ico 0 (P.E x), rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) = 0 :=
      Finset.sum_eq_zero fun u hu => by
        have := Finset.mem_Ico.1 hu
        rw [hout x u (by omega) (Or.inl this.2), zero_mul]
    have h2 : ∑ u ∈ Ico (b x) T, rateD P ℓ ωs φ ω u x * (ℓr P ℓ u x - bPol P ℓ ω u) = 0 :=
      Finset.sum_eq_zero fun u hu => by
        have := Finset.mem_Ico.1 hu
        rw [hout x u this.2 (Or.inr this.1), zero_mul]
    rw [h1, h2, zero_add, add_zero]
  rw [hwin]
  have hg : ∀ t, ℓr P ℓ t x - bPol P ℓ ω t ≤ 1 := by
    intro t
    have h1 : ℓr P ℓ t x ≤ 1 := by unfold ℓr; cases ℓ t (P.arm x) <;> simp
    have h2 : 0 ≤ bPol P ℓ ω t := by
      unfold bPol
      exact Finset.sum_nonneg fun yB _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)
    linarith
  have hr0 : ∀ t, 0 ≤ rateD P ℓ ωs φ ω t x := fun t =>
    Finset.sum_nonneg fun s _ => by split_ifs <;> simp [hxr]
  exact member_rate_le (fun t => rateD P ℓ ωs φ ω t x) (fun t => ℓr P ℓ t x - bPol P ℓ ω t) hg
    (P.E x) (b x) P.Bmin (hEb x hxT) hB (M x) (hM x hxT) hr0 (hmono x hxT) (hcheck x hxT)

end Pool.P0209
