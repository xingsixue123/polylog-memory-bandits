import Pool.P0078.Machine
import Pool.P0046.Coins

/-!
# The K-query pool learner of P0078: its expected loss is bounded by Hedge on P0052's start pools under P0063's
# coin-array law; memory bound

Scope notes. `mach` is a **K-query** machine (`Ns` free queries per day, full information on its pool), not a
single-query machine. It is **time-dependent**: its update reads the day index, so `memBits_mach_le` does not count a
clock. A homogeneous machine (P0001's `IsHomogeneous`) needs `withClock`, which adds `log₂(T + 1)` bits for horizon `T`.
The hypothesis `lev a < Lt + 1` of `path_le`/`sum_expLoss_le` is all the proofs need, but if `lev a = Lt` for some
`a < NE`, merges can put copies at level `Lt + 1`, P0078's `Good` can fail on every path, `Ψ = NE·B`, and the bound is
trivial. A useful bound needs `lev a + 1 ≤ Lt` (or a separate bound on `P(¬Good)`).

For P0078's machine `mach` (Peng–Rubinstein K-query baseline with `Ns` queries per day):
* `dayLoss_eq`: on a day of a good run (P0078 `Inv`, nonempty pool), the play law's expected loss is the
  corresponding term of P0061's `hedgeLoss` over the epoch's start pool.
* `path_le`: pathwise, the play laws' expected losses over days `1, …, NE·B` are at most `Ψ` of the slot array read
  off the coins (`Ψ ω = Σ_a cost a ω` if every epoch is `Good`, `NE·B` otherwise; `cost` = `hedgeLoss` over the
  start pool, or `B` if it is empty).
* `sum_W_restrict`, `sum_bw_comp`, `σ`/`σ_inj`, `Φ_ext`, `W_eq_bw`: the machine's update coins (P0064 product of
  P0051 `bernVec`) induce P0063's slot-array law `bw2 (qOf K ps p)` on the bits that `Φ` reads.
* **`sum_expLoss_le`**: `Σ_{t ≤ NE·B} expLoss ≤ 1 + Σ_ω bw2 (qOf K ps p) ω · Ψ ω`.
* **`memBits_mach_le`**: `memBits ≤ Ns·log₂(NE·n·2^(Lt+1)·(B+1) + 1) + Ns²·log₂(NE·B + 1)`.
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0030 Pool.P0042 Pool.P0052 Pool.P0078

namespace Pool.P0084

section Marginal

open Pool.P0046

variable {J Y : Type} [Fintype J] [DecidableEq J] [Fintype Y] [DecidableEq Y]

/-- **Marginal under an injective relabelling.** -/
theorem sum_bw_comp (q : J → ℝ) (σ : Y → J) (hσ : Function.Injective σ) (G : (Y → Bool) → ℝ) :
    ∑ y : J → Bool, bw q y * G (y ∘ σ) = ∑ ω : Y → Bool, bw (q ∘ σ) ω * G ω := by
  classical
  let J' := {j // ¬ j ∈ Set.range σ}
  let e : Y ⊕ J' ≃ J :=
    (Equiv.sumCongr (Equiv.ofInjective σ hσ) (Equiv.refl J')).trans (Equiv.sumCompl (· ∈ Set.range σ))
  have he : ∀ x : Y, e (Sum.inl x) = σ x := fun x => rfl
  let w : J → Bool → ℝ := fun j b => if b then q j else 1 - q j
  -- reindex the coordinates by `Y ⊕ J'`
  let A : (J → Bool) ≃ (Y ⊕ J' → Bool) := e.arrowCongr (Equiv.refl Bool) |>.symm
  rw [← A.symm.sum_comp]
  have hA : ∀ z : Y ⊕ J' → Bool, A.symm z = z ∘ e.symm := fun z => rfl
  have hw : ∀ z : Y ⊕ J' → Bool, bw q (A.symm z) =
      (∏ x : Y, w (σ x) (z (Sum.inl x))) * ∏ j : J', w (e (Sum.inr j)) (z (Sum.inr j)) := by
    intro z
    unfold bw
    rw [hA, ← e.prod_comp, Fintype.prod_sum_type]
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rfl
  have hG : ∀ z : Y ⊕ J' → Bool, (A.symm z) ∘ σ = fun x => z (Sum.inl x) := by
    intro z; funext x
    rw [hA]; simp only [Function.comp_apply, ← he, Equiv.symm_apply_apply]
  simp only [hw, hG]
  -- split `Y ⊕ J' → Bool` as a product
  let S : (Y ⊕ J' → Bool) ≃ (Y → Bool) × (J' → Bool) := Equiv.sumArrowEquivProdArrow Y J' Bool
  rw [← S.symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro ω _
  have h1 : ∀ b : J' → Bool, (S.symm (ω, b)) = Sum.elim ω b := fun b => rfl
  simp only [h1, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hsum : ∑ b : J' → Bool, ∏ j : J', w (e (Sum.inr j)) (b j) = 1 := by
    have := sum_bw (fun j : J' => q (e (Sum.inr j)))
    unfold bw at this
    exact this
  rw [hsum, mul_one]
  rfl


end Marginal

variable {n NE B Lt K R : ℕ} [NeZero n]

section DayLoss

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) (ℓs : LossSeq n)

/-- In-epoch losses of epoch `a`: `xa a r j` is the loss bit of copy `j` on day `r` of the epoch. -/
def xa (a : ℕ) (r : ℕ) (j : Cp n NE) : ℝ := (lv ℓs (a * B + r) (arm n NE j) : ℝ)

theorem E_playL (x : Raw (Cp n NE) Lt (NE * B) B) (hne : (U x).Nonempty) (f : Fin n → ℝ) :
    Pool.P0015.E (playL η x) f = (∑ c ∈ U x, wt η x c * f (arm n NE c)) / ∑ c ∈ U x, wt η x c := by
  classical
  unfold Pool.P0015.E playL
  rw [dif_pos hne]
  simp only [PMF.ofFintype_apply, ENNReal.toReal_ofReal (armW_nonneg η x _)]
  unfold armW
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_fiberwise (U x) (arm n NE) (fun c => wt η x c * f (arm n NE c))]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro c hc
  rw [(Finset.mem_filter.mp hc).2]

/-- **One day's expected loss is Hedge's**: on a good day `aB + r` of the run, the play law's expected loss equals
the `r`-th term of P0061's `hedgeLoss` over the pool of epoch `a`. -/
theorem dayLoss_eq {x : Raw (Cp n NE) Lt (NE * B) B} {ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool} {a r : ℕ}
    (hinv : Inv θ lev ℓs (R := R) ω a r x) (hne : (U x).Nonempty) :
    Pool.P0015.E (playL η x) (fun i => (lv ℓs (a * B + r) i : ℝ)) =
      ∑ j : U x, Pool.P0009.prob (fun _ => (1 : ℝ)) η (fun r' (j : U x) => xa (B := B) ℓs a r' j.1) r j *
        xa (B := B) ℓs a r j.1 := by
  classical
  rw [E_playL η x hne]
  have hw : ∀ c (hc : c ∈ U x), wt η x c = Real.exp (-η * Pool.P0009.cum (fun r' (j : U x) => xa (B := B) ℓs a r' j.1) r
      ⟨c, hc⟩) := by
    intro c hc
    unfold wt Pool.P0009.cum xa
    rw [if_pos hc, hinv.2.2 c hc, Finset.sum_Ico_eq_sum_range]
    simp only [add_tsub_cancel_left]
    push_cast; rfl
  unfold Pool.P0009.prob Pool.P0009.weight
  simp only [one_mul, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  · rw [← Finset.sum_coe_sort (U x)]
    apply Finset.sum_congr rfl; intro j _
    rw [hw j.1 j.2]
    rfl
  · rw [← Finset.sum_coe_sort (U x)]
    apply Finset.sum_congr rfl; intro j _
    exact hw j.1 j.2

end DayLoss


section Total

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp : 0 ≤ p ∧ p ≤ 1)

theorem sum_range_regroup (g : ℕ → ℝ) : ∀ N, ∑ t ∈ range (N * B), g t = ∑ a ∈ range N, ∑ r ∈ range B, g (a * B + r)
  | 0 => by simp
  | N + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_regroup g N, Finset.sum_range_succ]

theorem E_le_one {α : Type} [Fintype α] (μ : PMF α) (f : α → ℝ) (hf : ∀ a, f a ≤ 1) : Pool.P0015.E μ f ≤ 1 := by
  unfold Pool.P0015.E
  calc ∑ a, (μ a).toReal * f a ≤ ∑ a, (μ a).toReal * 1 :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hf a) ENNReal.toReal_nonneg
    _ = 1 := by simp only [mul_one]; exact Pool.P0015.sum_toReal μ

/-- The pool of epoch `a` in the run of the slot array `ω`. -/
noncomputable def poolOf (ℓs : LossSeq n) (ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool) (a : ℕ) : Finset (Cp n NE) :=
  univ.biUnion fun ℓ : Fin (Lt + 1) => SP (B := B) (R := R) θ lev ℓs ω a ℓ

open Classical in
/-- Cost of epoch `a`: Hedge over the epoch's pool (P0061's `hedgeLoss`), or `B` if the pool is empty. -/
noncomputable def cost (ℓs : LossSeq n) (ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool) (a : ℕ) : ℝ :=
  if (poolOf (B := B) (R := R) θ lev ℓs ω a).Nonempty then
    Pool.P0061.hedgeLoss (poolOf (B := B) (R := R) θ lev ℓs ω a) η B (xa (B := B) ℓs a)
  else B

open Classical in
/-- The pathwise cost of a slot array: the epoch costs if every epoch is good, `NE · B` otherwise. -/
noncomputable def Ψ (ℓs : LossSeq n) (ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool) : ℝ :=
  if ∀ a < NE, Good (B := B) Ns θ lev ℓs (R := R) ω a then
    ∑ a ∈ range NE, cost (B := B) (R := R) θ η lev ℓs ω a
  else NE * B

/-- **Pathwise loss of the machine** on days `1, …, NE·B` for update coins `zf`: at most `Ψ` of the slot array. -/
theorem path_le (hB : 0 < B) (hlev : ∀ a < NE, lev a < Lt + 1) (ℓ : LossSeq n) (zf : ℕ → Jd n NE Lt K → Bool) :
    ∑ t ∈ range (NE * B), Pool.P0015.E ((mach (B := B) (R := R) Ns θ η lev hps hp).play (t + 1)
        ((mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ (t + 1) (fun i => zf i)))
        (fun i => ((ℓ (t + 1) i).toNat : ℝ)) ≤
      Ψ (B := B) (R := R) Ns θ η lev (fun u => ℓ (u + 1))
        (Φ (B := B) (fun c => zf 0 (Sum.inr c)) (fun u => zf (u + 1))) := by
  classical
  set ℓs : LossSeq n := fun u => ℓ (u + 1)
  set ω := Φ (B := B) (fun c => zf 0 (Sum.inr c)) (fun u => zf (u + 1))
  have hle1 : ∀ t, Pool.P0015.E ((mach (B := B) (R := R) Ns θ η lev hps hp).play (t + 1)
      ((mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ (t + 1) (fun i => zf i)))
      (fun i => ((ℓ (t + 1) i).toNat : ℝ)) ≤ 1 := by
    intro t
    apply E_le_one
    intro i; cases ℓ (t + 1) i <;> simp
  unfold Ψ
  split_ifs with hg
  · rw [sum_range_regroup _ NE]
    apply Finset.sum_le_sum; intro a ha
    have ha' : a < NE := Finset.mem_range.mp ha
    have hinv : ∀ r < B, Inv θ lev ℓs (R := R) ω a r
        ((mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ (a * B + r + 1) (fun i => zf i)).1 := by
      intro r hr
      have hdm : (a * B + r) / B = a ∧ (a * B + r) % B = r :=
        (Nat.div_mod_unique hB).mpr ⟨by ring, hr⟩
      have h := run_inv (B := B) (R := R) Ns θ η lev hps hp hB hlev ℓ zf (a * B + r)
        (by
          have := Nat.mul_le_mul_right B (Nat.succ_le_of_lt ha')
          rw [Nat.succ_mul] at this; omega)
        (fun a' ha'' => hg a' (by rw [hdm.1] at ha''; omega))
      rw [hdm.1, hdm.2] at h
      exact h
    have hU : ∀ r < B, U ((mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ (a * B + r + 1)
        (fun i => zf i)).1 = poolOf (B := B) (R := R) θ lev ℓs ω a := fun r hr => U_of_P θ lev ℓs (hinv r hr).1
    unfold cost
    split_ifs with hne
    · unfold Pool.P0061.hedgeLoss
      apply le_of_eq
      apply Finset.sum_congr rfl; intro r hr
      have hr' := Finset.mem_range.mp hr
      have hne' : (U ((mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ (a * B + r + 1)
          (fun i => zf i)).1).Nonempty := by rw [hU r hr']; exact hne
      have h := dayLoss_eq θ η lev ℓs (hinv r hr') hne'
      show Pool.P0015.E (playL η _) _ = _
      have hl : (fun i => ((ℓ (a * B + r + 1) i).toNat : ℝ)) = fun i => (lv ℓs (a * B + r) i : ℝ) := rfl
      rw [hl, h]
      have key : ∀ P : Finset (Cp n NE), P = U ((mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ
          (a * B + r + 1) (fun i => zf i)).1 →
          ∑ j : U ((mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ (a * B + r + 1) (fun i => zf i)).1,
            Pool.P0009.prob (fun _ => (1 : ℝ)) η (fun r' (j : U ((mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ
              (a * B + r + 1) (fun i => zf i)).1) => xa (B := B) ℓs a r' j.1) r j * xa (B := B) ℓs a r j.1 =
          ∑ j : P, Pool.P0009.prob (fun _ => (1 : ℝ)) η (fun r' (j : P) => xa (B := B) ℓs a r' j.1) r j *
            xa (B := B) ℓs a r j.1 := by
        intro P hP; subst hP; rfl
      exact key _ (hU r hr').symm
    · calc ∑ r ∈ range B, _ ≤ ∑ _r ∈ range B, (1 : ℝ) := Finset.sum_le_sum fun r _ => hle1 _
        _ = B := by simp
  · calc _ ≤ ∑ _t ∈ range (NE * B), (1 : ℝ) := Finset.sum_le_sum fun t _ => hle1 t
      _ = NE * B := by simp

end Total


section Transfer

open Pool.P0046
open scoped Pool.P0064

/-- Future update coins integrate out (P0064's coin weights). -/
theorem sum_W_restrict {nn KK : ℕ} (A : Pool.P0064.QCoinAlg nn KK) (k : ℕ) (F : (Fin k → A.Z) → ℝ) :
    ∀ T (h : k ≤ T), ∑ ω : Fin T → A.Z, A.W ω * F (fun i => ω (Fin.castLE h i)) =
      ∑ ω : Fin k → A.Z, A.W ω * F ω := by
  intro T h
  induction T, h using Nat.le_induction with
  | base => rfl
  | succ T hkT ih =>
    rw [Pool.P0064.sum_split]
    have e : ∀ (ω' : Fin T → A.Z) (z : A.Z),
        (fun i : Fin k => (Fin.snoc ω' z : Fin (T + 1) → A.Z) (Fin.castLE (Nat.le_succ_of_le hkT) i)) =
          fun i => ω' (Fin.castLE hkT i) := by
      intro ω' z; funext i
      have : (Fin.castLE (Nat.le_succ_of_le hkT) i : Fin (T + 1)) = Fin.castSucc (Fin.castLE hkT i) := Fin.ext rfl
      rw [this, Fin.snoc_castSucc]
    simp only [Pool.P0064.W_snoc, e]
    rw [Finset.sum_comm]
    have h1 : ∑ z, (A.ν z).toReal = 1 := Pool.P0015.sum_toReal A.ν
    have h2 : ∀ ω' : Fin T → A.Z, ∑ z, A.W ω' * (A.ν z).toReal * F (fun i => ω' (Fin.castLE hkT i)) =
        A.W ω' * F (fun i => ω' (Fin.castLE hkT i)) := by
      intro ω'; rw [← Finset.sum_mul, ← Finset.mul_sum, h1, mul_one]
    simp only [h2]
    exact ih

/-- Product of independent bit vectors as one product over pairs. -/
theorem prod_bw_curry {T' J : Type} [Fintype T'] [DecidableEq T'] [Fintype J] [DecidableEq J] (q : J → ℝ)
    (ω : T' → J → Bool) : ∏ t, bw q (ω t) = bw (fun tj : T' × J => q tj.2) (fun tj => ω tj.1 tj.2) := by
  unfold bw
  rw [Fintype.prod_prod_type]

theorem bw2_eq_bw {σ κ : Type} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ] (q : σ → κ → ℝ)
    (ω : σ → κ → Bool) : bw2 q ω = bw (fun sc : σ × κ => q sc.1 sc.2) (fun sc => ω sc.1 sc.2) := by
  unfold bw2 bw
  rw [Fintype.prod_prod_type]

end Transfer


section Final

open Pool.P0046
open scoped Pool.P0064

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp : 0 ≤ p ∧ p ≤ 1)

/-- Extend a finite coin sequence by a default coin. -/
def ext {Z : Type} (d : Z) {TT : ℕ} (ω : Fin TT → Z) : ℕ → Z :=
  fun i => if h : i < TT then ω ⟨i, h⟩ else d

/-- Where each slot bit of P0063's array sits among the machine's coins: the sampling bits of epoch `a` are drawn on
day `aB`, the filter bits of epoch `a` on day `(a+1)B`. -/
def σ (hB : 0 < B) : Pool.P0063.Slot NE Lt K × Cp n NE → Fin (NE * B + 1) × Jd n NE Lt K
  | (Sum.inl a, c) => (⟨a.1 * B, Nat.lt_succ_of_le (Nat.mul_le_mul_right B a.2.le)⟩, Sum.inr c)
  | (Sum.inr (a, ℓ, k), c) => (⟨(a.1 + 1) * B, Nat.lt_succ_of_le (Nat.mul_le_mul_right B a.2)⟩, Sum.inl (ℓ, k, c))

theorem σ_inj (hB : 0 < B) : Function.Injective (σ (n := n) (NE := NE) (Lt := Lt) (K := K) hB) := by
  rintro ⟨s, c⟩ ⟨s', c'⟩ h
  rcases s with a | ⟨a, ℓ, k⟩ <;> rcases s' with a' | ⟨a', ℓ', k'⟩ <;>
    simp only [σ, Prod.mk.injEq, Fin.mk.injEq, reduceCtorEq, and_false, Sum.inr.injEq, Sum.inl.injEq] at h
  · have ha : a.1 = a'.1 := Nat.eq_of_mul_eq_mul_right hB h.1
    rw [Fin.ext ha, h.2]
  · obtain ⟨h1, h2, h3, h4⟩ := h
    have ha : a.1 + 1 = a'.1 + 1 := Nat.eq_of_mul_eq_mul_right hB h1
    rw [Fin.ext (by omega : a.1 = a'.1), h2, h3, h4]

theorem Φ_ext (hB : 0 < B) (d : Jd n NE Lt K → Bool) (ω : Fin (NE * B + 1) → Jd n NE Lt K → Bool) :
    Φ (B := B) (fun c => ext d ω 0 (Sum.inr c)) (fun u => ext d ω (u + 1)) =
      fun s c => ω (σ hB (s, c)).1 (σ hB (s, c)).2 := by
  funext s c
  rcases s with a | ⟨a, ℓ, k⟩
  · simp only [Φ, σ]
    by_cases ha : a.1 = 0
    · rw [if_pos ha]
      unfold ext
      rw [dif_pos (by omega)]
      exact congrArg (fun i => ω i (Sum.inr c)) (Fin.ext (by simp [ha]))
    · rw [if_neg ha]
      unfold ext
      have h1 : 1 ≤ a.1 * B := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero ha hB.ne')
      have hlt : a.1 * B - 1 + 1 < NE * B + 1 := by
        have := Nat.mul_le_mul_right B a.2.le; omega
      rw [dif_pos hlt]
      exact congrArg (fun i => ω i (Sum.inr c)) (Fin.ext (by simp only; omega))
  · simp only [Φ, σ]
    unfold ext
    have hlt : a.1 * B + B - 1 + 1 < NE * B + 1 := by
      have := Nat.mul_le_mul_right B a.2; rw [Nat.succ_mul] at this; omega
    rw [dif_pos hlt]
    exact congrArg (fun i => ω i (Sum.inl (ℓ, k, c))) (Fin.ext (by simp only [Nat.succ_mul]; omega))

theorem W_eq_bw (ω : Fin (NE * B + 1) → Jd n NE Lt K → Bool) :
    (mach (B := B) (R := R) Ns θ η lev hps hp).W ω =
      bw (fun tj : Fin (NE * B + 1) × Jd n NE Lt K => qd ps p tj.2) (fun tj => ω tj.1 tj.2) := by
  unfold Pool.P0064.QCoinAlg.W
  rw [← prod_bw_curry]
  apply Fintype.prod_congr; intro t
  show (Pool.P0051.bernVec (qd ps p) (qd_mem hps hp) (ω t)).toReal = _
  rw [Pool.P0051.bernVec_apply]
  rfl

/-- **Expected loss of the K-query pool learner.** Over days `0, …, NE·B`, its expected loss is at most
`1 + E_ω[Ψ ω]`, where `ω` is P0063's slot array with its product law and `Ψ ω` is the sum over epochs of Hedge's
loss on the epoch's pool of P0052's process (driven by `ω`, cover data = true cumulative epoch losses of the shifted
sequence `u ↦ ℓ (u+1)`), or `NE·B` if some epoch is not good. -/
theorem sum_expLoss_le (hB : 0 < B) (hlev : ∀ a < NE, lev a < Lt + 1) (ℓ : LossSeq n) :
    ∑ t ∈ range (NE * B + 1), (mach (NE := NE) (B := B) (Lt := Lt) (K := K) (R := R) Ns θ η lev hps hp).toQ.expLoss ℓ t ≤
      1 + ∑ ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool, bw2 (Pool.P0063.qOf K ps p) ω *
        Ψ (B := B) (R := R) Ns θ η lev (fun u => ℓ (u + 1)) ω := by
  classical
  set A := mach (n := n) (NE := NE) (B := B) (Lt := Lt) (K := K) (R := R) Ns θ η lev hps hp with hA
  have hW0 : ∀ (T : ℕ) (ω : Fin T → A.Z), 0 ≤ A.W ω := fun _ _ =>
    Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  rw [Finset.sum_range_succ', add_comm]
  apply add_le_add
  · -- day 0
    rw [Pool.P0064.expLoss_eq]
    calc _ ≤ ∑ ω : Fin 0 → A.Z, A.W ω * 1 :=
          Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
            (E_le_one _ _ fun i => by cases ℓ 0 i <;> simp) (hW0 _ ω)
      _ = 1 := by simp only [mul_one]; exact Pool.P0064.sum_W A 0
  · -- days 1..NE*B
    have hday : ∀ t ∈ range (NE * B), A.toQ.expLoss ℓ (t + 1) =
        ∑ ω : Fin (NE * B + 1) → A.Z, A.W ω * Pool.P0015.E (A.play (t + 1) (A.runFin ℓ (t + 1)
          (fun i => ext (ω ⟨0, Nat.succ_pos _⟩) ω i)))
          (fun i => ((ℓ (t + 1) i).toNat : ℝ)) := by
      intro t ht
      have ht' : t + 1 ≤ NE * B + 1 := by have := Finset.mem_range.mp ht; omega
      rw [Pool.P0064.expLoss_eq, ← sum_W_restrict A (t + 1) _ (NE * B + 1) ht']
      apply Finset.sum_congr rfl; intro ω _
      have hfun : (fun i : Fin (t + 1) => ω (Fin.castLE ht' i)) =
          fun i : Fin (t + 1) => ext (ω ⟨0, Nat.succ_pos _⟩) ω (i : ℕ) := by
        funext i; unfold ext
        rw [dif_pos (lt_of_lt_of_le i.2 ht')]
        rfl
      rw [hfun]
    rw [Finset.sum_congr rfl hday, Finset.sum_comm]
    calc ∑ ω : Fin (NE * B + 1) → A.Z, ∑ t ∈ range (NE * B), A.W ω * Pool.P0015.E
          (A.play (t + 1) (A.runFin ℓ (t + 1) (fun i => ext (ω ⟨0, Nat.succ_pos _⟩) ω i)))
            (fun i => ((ℓ (t + 1) i).toNat : ℝ))
        ≤ ∑ ω : Fin (NE * B + 1) → A.Z, A.W ω * Ψ (B := B) (R := R) Ns θ η lev (fun u => ℓ (u + 1))
            (fun s c => ω (σ hB (s, c)).1 (σ hB (s, c)).2) := by
          apply Finset.sum_le_sum; intro ω _
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (hW0 _ ω)
          have := path_le (B := B) (R := R) Ns θ η lev hps hp hB hlev ℓ (ext (ω ⟨0, Nat.succ_pos _⟩) ω)
          refine this.trans (le_of_eq ?_)
          congr 1
          exact Φ_ext hB (ω ⟨0, Nat.succ_pos _⟩) ω
      _ = ∑ y : Fin (NE * B + 1) × Jd n NE Lt K → Bool,
            bw (fun tj : Fin (NE * B + 1) × Jd n NE Lt K => qd ps p tj.2) y *
              Ψ (B := B) (R := R) Ns θ η lev (fun u => ℓ (u + 1)) (fun s c => y (σ hB (s, c))) := by
          refine Fintype.sum_equiv (Equiv.curry (Fin (NE * B + 1)) (Jd n NE Lt K) Bool).symm _ _ ?_
          intro ω
          have hWω : A.W ω = bw (fun tj : Fin (NE * B + 1) × Jd n NE Lt K => qd ps p tj.2)
              (fun tj => ω tj.1 tj.2) := W_eq_bw (R := R) Ns θ η lev hps hp ω
          rw [hWω]
          rfl
      _ = ∑ y' : Pool.P0063.Slot NE Lt K × Cp n NE → Bool,
            bw (fun sc => Pool.P0063.qOf K ps p sc.1 sc.2) y' *
              Ψ (B := B) (R := R) Ns θ η lev (fun u => ℓ (u + 1)) (fun s c => y' (s, c)) := by
          have h := sum_bw_comp (fun tj : Fin (NE * B + 1) × Jd n NE Lt K => qd ps p tj.2)
            (σ hB) (σ_inj hB) (fun y' => Ψ (B := B) (R := R) Ns θ η lev (fun u => ℓ (u + 1)) (fun s c => y' (s, c)))
          refine h.trans ?_
          apply Finset.sum_congr rfl; intro y' _
          congr 1
          congr 1
          funext sc
          rcases sc with ⟨a | ⟨a, ℓ', k⟩, c⟩ <;> rfl
      _ = ∑ ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool, bw2 (Pool.P0063.qOf K ps p) ω *
            Ψ (B := B) (R := R) Ns θ η lev (fun u => ℓ (u + 1)) ω := by
          refine Fintype.sum_equiv (Equiv.curry (Pool.P0063.Slot NE Lt K) (Cp n NE) Bool) _ _ ?_
          intro y'
          rw [bw2_eq_bw]
          rfl

end Final


section Memory

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp : 0 ≤ p ∧ p ≤ 1)

open Classical in
/-- **Memory**: `log₂ |state| ≤ Ns·log₂(NE·n·2^(Lt+1)·(B+1) + 1) + Ns²·log₂(NE·B + 1)`. -/
theorem memBits_mach_le :
    (mach (n := n) (NE := NE) (B := B) (Lt := Lt) (K := K) (R := R) Ns θ η lev hps hp).toQ.memBits ≤
      Ns * Real.logb 2 (NE * n * 2 ^ (Lt + 1) * (B + 1) + 1) + (Ns * Ns) * Real.logb 2 (NE * B + 1) := by
  rw [Pool.P0064.memBits_toQ]
  have hcard := card_PState_le (ι := Cp n NE) (Lt := Lt) (Ns := Ns) (TT := NE * B) (BB := B)
  rw [Fintype.card_fin] at hcard
  have hpos : (0 : ℝ) < Fintype.card (St (n := n) (NE := NE) (B := B) (Lt := Lt) Ns) := by
    have : Nonempty (St (n := n) (NE := NE) (B := B) (Lt := Lt) Ns) :=
      ⟨(⟨emptyRaw, valid_empty Ns⟩ : St (n := n) (NE := NE) (B := B) (Lt := Lt) Ns)⟩
    exact_mod_cast Fintype.card_pos
  show Real.logb 2 (Fintype.card (St (n := n) (NE := NE) (B := B) (Lt := Lt) Ns)) ≤ _
  calc Real.logb 2 (Fintype.card (St (n := n) (NE := NE) (B := B) (Lt := Lt) Ns))
      ≤ Real.logb 2 (((NE * n * 2 ^ (Lt + 1) * (B + 1) + 1 : ℕ) : ℝ) ^ Ns * ((NE * B + 1 : ℕ) : ℝ) ^ (Ns * Ns)) := by
        apply Real.logb_le_logb_of_le (by norm_num) hpos
        exact_mod_cast hcard
    _ = Ns * Real.logb 2 (NE * n * 2 ^ (Lt + 1) * (B + 1) + 1) + (Ns * Ns) * Real.logb 2 (NE * B + 1) := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]
        push_cast; ring

end Memory

end Pool.P0084
