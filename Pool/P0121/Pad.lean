import Pool.P0121.Assembly

/-!
# Zero padding of the horizon, and the memory of the threaded machine
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0121.TS Pool.P0121.TM

namespace Pool.P0121.TP

section Pad

variable {n K : ℕ}

/-- The loss sequence `ℓ` on rounds `< T`, zero afterwards. -/
def padZ (ℓ : LossSeq n) (T : ℕ) : LossSeq n := fun t => if t < T then ℓ t else fun _ => false

/-- **Zero padding**: the regret over `T` rounds equals the regret over any longer horizon on the zero-padded sequence
(causality). -/
theorem regret_padZ (A : QMachine n K) (ℓ : LossSeq n) {T T' : ℕ} (h : T ≤ T') :
    A.regret ℓ T = A.regret (padZ ℓ T) T' := by
  unfold QMachine.regret
  have hexp : ∀ t, A.expLoss (padZ ℓ T) t = if t < T then A.expLoss ℓ t else 0 := by
    intro t
    rw [QMachine.expLoss_eq, QMachine.expLoss_eq]
    split_ifs with ht
    · rw [A.stateDist_congr (ℓ₁ := padZ ℓ T) (ℓ₂ := ℓ) t (fun u hu => by unfold padZ; rw [if_pos (by omega)])]
      unfold padZ; rw [if_pos ht]
    · unfold padZ; rw [if_neg ht]
      simp [E_const]
  have hsum : ∑ t ∈ range T', A.expLoss (padZ ℓ T) t = ∑ t ∈ range T, A.expLoss ℓ t := by
    rw [← Finset.sum_range_add_sum_Ico _ h]
    have h1 : ∑ t ∈ Ico T T', A.expLoss (padZ ℓ T) t = 0 :=
      Finset.sum_eq_zero fun t ht => by rw [hexp t, if_neg (by rw [Finset.mem_Ico] at ht; omega)]
    rw [h1, add_zero]
    exact Finset.sum_congr rfl fun t ht => by rw [hexp t, if_pos (Finset.mem_range.1 ht)]
  have hcum : ∀ i, cumLoss (padZ ℓ T) T' i = cumLoss ℓ T i := by
    intro i
    unfold cumLoss
    rw [← Finset.sum_range_add_sum_Ico _ h]
    have h1 : ∑ t ∈ Ico T T', (((padZ ℓ T) t i).toNat : ℝ) = 0 :=
      Finset.sum_eq_zero fun t ht => by
        unfold padZ; rw [if_neg (by rw [Finset.mem_Ico] at ht; omega)]; simp
    rw [h1, add_zero]
    exact Finset.sum_congr rfl fun t ht => by unfold padZ; rw [if_pos (Finset.mem_range.1 ht)]
  have hbest : bestLoss (padZ ℓ T) T' = bestLoss ℓ T := by
    unfold bestLoss; simp only [hcum]
  rw [hsum, hbest]

end Pad

section Memory

variable {n NE D : ℕ} [NeZero n] {Lv L M Lt K R : ℕ} (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (θ η ε : ℝ) (Ns : ℕ)
  {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)

/-- The base of the memory bound. -/
def Zb (n NE D Lv L M : ℕ) : ℕ := (NE * D * n + 1) * (2 ^ (D * Lv) * ((2 ^ L + 1) * (M + 1)) ^ (L + 1) + 1) *
  (NE + 1) * (M + 1)

open Classical in
/-- **Memory**: `log₂ |state| ≤ (Ns + Ns² + 1)·log₂ Zb`. -/
theorem memBits_tmach_le :
    (tmach (n := n) (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE) (D := D) Bt lev θ η ε Ns
      hps hq).toQ.memBits ≤ ((Ns + Ns * Ns + 1 : ℕ) : ℝ) * Real.logb 2 (Zb n NE D Lv L M) := by
  rw [Pool.P0064.memBits_toQ]
  have hcard := card_GState_le (ι := Cp n NE D) (Lb := Lb D Lv L M) (G := Fin (M + 1)) (Ns := Ns) (TT := NE)
  have hLb : Fintype.card (Lb D Lv L M) = 2 ^ (D * Lv) * ((2 ^ L + 1) * (M + 1)) ^ (L + 1) := by
    simp only [Lb, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    rw [← pow_mul, Nat.mul_comm Lv D]
  rw [hLb, Fintype.card_fin, Fintype.card_fin] at hcard
  set Z := Zb n NE D Lv L M with hZ
  have hZ1 : 1 ≤ Z := by
    rw [hZ]; unfold Zb; exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have h1 : NE * D * n * (2 ^ (D * Lv) * ((2 ^ L + 1) * (M + 1)) ^ (L + 1) + 1) + 1 ≤ Z := by
    rw [hZ]; unfold Zb
    have : 1 ≤ (NE + 1) * (M + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc NE * D * n * (2 ^ (D * Lv) * ((2 ^ L + 1) * (M + 1)) ^ (L + 1) + 1) + 1
        ≤ (NE * D * n + 1) * (2 ^ (D * Lv) * ((2 ^ L + 1) * (M + 1)) ^ (L + 1) + 1) := by nlinarith
      _ = (NE * D * n + 1) * (2 ^ (D * Lv) * ((2 ^ L + 1) * (M + 1)) ^ (L + 1) + 1) * 1 := by ring
      _ ≤ _ := by rw [mul_assoc _ (NE + 1)]; exact Nat.mul_le_mul_left _ this
  have h2 : NE + 1 ≤ Z := by
    rw [hZ]; unfold Zb
    have : 1 ≤ (NE * D * n + 1) * (2 ^ (D * Lv) * ((2 ^ L + 1) * (M + 1)) ^ (L + 1) + 1) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    calc NE + 1 ≤ (NE * D * n + 1) * (2 ^ (D * Lv) * ((2 ^ L + 1) * (M + 1)) ^ (L + 1) + 1) * (NE + 1) * 1 := by
          nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
  have h3 : M + 1 ≤ Z := by
    rw [hZ]; unfold Zb
    have : 1 ≤ (NE * D * n + 1) * (2 ^ (D * Lv) * ((2 ^ L + 1) * (M + 1)) ^ (L + 1) + 1) * (NE + 1) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hcZ : Fintype.card (StT n NE D Lv L M Ns) ≤ Z ^ (Ns + Ns * Ns + 1) := by
    refine hcard.trans ?_
    have e : Z ^ (Ns + Ns * Ns + 1) = Z ^ Ns * Z ^ (Ns * Ns) * Z := by ring
    rw [e]
    exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left h1 _) (Nat.pow_le_pow_left h2 _)) h3
  have hpos : (0 : ℝ) < Fintype.card (StT n NE D Lv L M Ns) := by
    have : Nonempty (StT n NE D Lv L M Ns) := ⟨⟨emptyT, valid_emptyT Ns⟩⟩
    exact_mod_cast Fintype.card_pos
  show Real.logb 2 (Fintype.card (StT n NE D Lv L M Ns)) ≤ _
  calc Real.logb 2 (Fintype.card (StT n NE D Lv L M Ns)) ≤ Real.logb 2 ((Z : ℝ) ^ (Ns + Ns * Ns + 1)) := by
        apply Real.logb_le_logb_of_le (by norm_num) hpos
        exact_mod_cast hcZ
    _ = _ := by rw [Real.logb_pow]

end Memory

end Pool.P0121.TP
