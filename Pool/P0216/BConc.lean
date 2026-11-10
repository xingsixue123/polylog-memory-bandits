import Pool.P0203.DSlot

/-!
# Concentration of BASE's estimate `B̂` in P0194's per-thread round-level process

`B̂` grows by `cB·ℓ_u(bAct_u)` on BASE rounds. With `cB·wB = 1` it is unbiased for BASE's policy loss `bPol_u`
whatever the pool does, so no gate is needed.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0203

namespace Pool.P0216

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)

/-- `B̂`'s increment at round `u`. -/
noncomputable def incBD (ω : ℕ → RC P) (u : ℕ) : ℝ :=
  if isB P (ω u).1 then P.cB * ((ℓ u (bAct P ℓ ω u)).toNat : ℝ) else 0

/-- `B̂` is the running sum of its increments. -/
theorem Bh_sum (ω : ℕ → RC P) (a : ℕ) : ∀ m, a ≤ m → Bh P ℓ ω m - Bh P ℓ ω a = ∑ u ∈ Ico a m, incBD P ℓ ω u := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m ham ih =>
    rw [Finset.sum_Ico_succ_top ham, ← ih]
    simp only [Bh, incBD]
    ring

/-- Averaging a BASE-only quantity of the BASE action coin. -/
theorem sum_wR_baseD (hN : 0 < P.N) (G : P.AB.Y → ℝ) :
    ∑ rc : RC P, wR P rc * (if isB P rc.1 then G rc.2.2.1 else 0) = P.wB * ∑ y, (P.AB.μ y).toReal * G y := by
  have hν : ∑ zB : P.AB.Z, (P.AB.ν zB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.ν
  have hN' : (P.N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Fintype.sum_prod_type, wR, Fintype.sum_option, isB, Option.isNone_none, Option.isNone_some,
    if_true, Bool.false_eq_true, if_false, mul_zero, Finset.sum_const_zero, add_zero]
  have e : ∀ d : Fin P.N, ∑ yB : P.AB.Y, ∑ zB : P.AB.Z,
      wK P none * (1 / (P.N : ℝ)) * (P.AB.μ yB).toReal * (P.AB.ν zB).toReal * G yB
        = (1 / (P.N : ℝ)) * (P.wB * ∑ y, (P.AB.μ y).toReal * G y) := by
    intro d
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    have : ∀ zB : P.AB.Z, wK P none * (1 / (P.N : ℝ)) * (P.AB.μ y).toReal * (P.AB.ν zB).toReal * G y
        = (wK P none * (1 / (P.N : ℝ)) * (P.AB.μ y).toReal * G y) * (P.AB.ν zB).toReal := fun _ => by ring
    rw [Finset.sum_congr rfl fun zB _ => this zB, ← Finset.mul_sum, hν]
    simp only [wK]; ring
  rw [Finset.sum_congr rfl fun d _ => e d, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

variable (rc0 : RC P)

/-- The centred `B̂` increment on coin prefixes. -/
noncomputable def DB (u : ℕ) (ω : Fin (u + 1) → RC P) : ℝ :=
  incBD P ℓ (extD P rc0 ω) u - bPol P ℓ (extD P rc0 ω) u

theorem bPol_congrD {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' u) : bPol P ℓ ω u = bPol P ℓ ω' u := by
  unfold bPol; rw [sB_congr (ℓ := ℓ) u h]

theorem DB_snoc {u : ℕ} (ω : Fin u → RC P) (z : RC P) :
    DB P ℓ rc0 u (Fin.snoc ω z) =
      (if isB P z.1 then P.cB * ((ℓ u (P.AB.act 0 (sB P ℓ (extD P rc0 ω) u) z.2.2.1)).toNat : ℝ) else 0)
        - bPol P ℓ (extD P rc0 ω) u := by
  have hA := extD_snoc_agree P rc0 ω z
  have hz := extD_snoc_last P rc0 ω z
  unfold DB incBD bAct
  rw [bPol_congrD P ℓ u hA, hz, sB_congr (ℓ := ℓ) u hA]

theorem toNat_le_one (b : Bool) : ((b.toNat : ℕ) : ℝ) ≤ 1 := by cases b <;> simp

theorem bPol_mem (ω : ℕ → RC P) (u : ℕ) : 0 ≤ bPol P ℓ ω u ∧ bPol P ℓ ω u ≤ 1 := by
  unfold bPol
  refine ⟨Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _), ?_⟩
  calc _ ≤ ∑ yB : P.AB.Y, (P.AB.μ yB).toReal :=
        Finset.sum_le_sum fun yB _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (toNat_le_one _)
    _ = 1 := Pool.P0092.sum_toReal_one P.AB.μ

/-- **Conditional mean of the centred `B̂` increment** for ANY factor `cB`: `(cB·wB − 1)·bPol`. So the increment is
centred exactly when `cB·wB = 1` (or `bPol = 0`). -/
theorem mean_DB (hL : P.IsLaw) (hN : 0 < P.N) {u : ℕ} (ω : Fin u → RC P) :
    ∑ z : RC P, wR P z * DB P ℓ rc0 u (Fin.snoc ω z) = (P.cB * P.wB - 1) * bPol P ℓ (extD P rc0 ω) u := by
  simp only [DB_snoc, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sum_wR P hL hN, one_mul]
  rw [sum_wR_baseD P hN (fun y => P.cB * ((ℓ u (P.AB.act 0 (sB P ℓ (extD P rc0 ω) u) y)).toNat : ℝ))]
  simp only [bPol, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Under a law with `cB·wB = 1`: `0 < wB ≤ 1` and `cB ≥ 1`. -/
theorem cB_ge_one (hL : P.IsLaw) (hcw : P.cB * P.wB = 1) : 1 ≤ P.cB ∧ 0 < P.wB := by
  obtain ⟨hB0, hE0, hx0, hsum⟩ := hL
  have hs : 0 ≤ ∑ j, (P.sl j : ℝ) * P.xr j := Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hx0 j)
  have hB1 : P.wB ≤ 1 := by linarith
  have hBpos : 0 < P.wB := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hcw; exact absurd hcw (by norm_num)
  refine ⟨?_, hBpos⟩
  by_contra hc
  push_neg at hc
  nlinarith

/-- **`B̂`'s centred increments satisfy P0158's hypotheses** with range and variance `cB`, and are `≥ −cB`. -/
theorem incrV_DB (hL : P.IsLaw) (hN : 0 < P.N) (hcw : P.cB * P.wB = 1) :
    Pool.P0158.IncrV (nuD P hL hN) (DB P ℓ rc0) (fun _ => P.cB) (fun _ => P.cB) ∧
      ∀ u (ω : Fin u → RC P) z, -P.cB ≤ DB P ℓ rc0 u (Fin.snoc ω z) := by
  obtain ⟨hc1, hB0⟩ := cB_ge_one P hL hcw
  have hc0 : 0 ≤ P.cB := by linarith
  set m := fun (u : ℕ) (ω : Fin u → RC P) => bPol P ℓ (extD P rc0 ω) u
  set G := fun (u : ℕ) (ω : Fin u → RC P) (y : P.AB.Y) =>
    P.cB * ((ℓ u (P.AB.act 0 (sB P ℓ (extD P rc0 ω) u) y)).toNat : ℝ)
  have hX : ∀ u (ω : Fin u → RC P), ∑ z : RC P, wR P z * (if isB P z.1 then G u ω z.2.2.1 else 0) = m u ω := by
    intro u ω
    rw [sum_wR_baseD P hN]
    simp only [G, m, bPol, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    linear_combination ((P.AB.μ y).toReal * ((ℓ u (P.AB.act 0 (sB P ℓ (extD P rc0 ω) u) y)).toNat : ℝ)) * hcw
  have hGb : ∀ u ω y, 0 ≤ G u ω y ∧ G u ω y ≤ P.cB := fun u ω y =>
    ⟨mul_nonneg hc0 (Nat.cast_nonneg _), mul_le_of_le_one_right hc0 (toNat_le_one _)⟩
  have hsum1 := sum_wR P hL hN
  refine ⟨⟨fun u ω z => ?_, fun u ω => ?_, fun u ω => ?_⟩, fun u ω z => ?_⟩
  · rw [DB_snoc]
    have := (bPol_mem P ℓ (extD P rc0 ω) u).1
    split_ifs
    · linarith [(hGb u ω z.2.2.1).2]
    · linarith
  · simp only [DB_snoc, nuD_toReal, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1, one_mul]
    rw [hX u ω]; simp [m]
  · simp only [DB_snoc, nuD_toReal]
    -- E[(X − m)²] = E[X²] − m² ≤ E[X²] = wB·Σ μ G² ≤ wB·cB² = cB
    have hvar : ∑ z : RC P, wR P z * ((if isB P z.1 then G u ω z.2.2.1 else 0) - m u ω) ^ 2
        = ∑ z : RC P, wR P z * (if isB P z.1 then G u ω z.2.2.1 ^ 2 else 0) - m u ω ^ 2 := by
      have e : ∀ z : RC P, wR P z * ((if isB P z.1 then G u ω z.2.2.1 else 0) - m u ω) ^ 2
          = wR P z * (if isB P z.1 then G u ω z.2.2.1 ^ 2 else 0)
            - 2 * m u ω * (wR P z * (if isB P z.1 then G u ω z.2.2.1 else 0)) + m u ω ^ 2 * wR P z := by
        intro z; split_ifs <;> ring
      rw [Finset.sum_congr rfl fun z _ => e z, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, hX u ω, hsum1]
      ring
    have h2 : ∑ z : RC P, wR P z * (if isB P z.1 then G u ω z.2.2.1 ^ 2 else 0) ≤ P.cB := by
      rw [sum_wR_baseD P hN (fun y => G u ω y ^ 2)]
      calc P.wB * ∑ y, (P.AB.μ y).toReal * G u ω y ^ 2 ≤ P.wB * ∑ y, (P.AB.μ y).toReal * P.cB ^ 2 := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => ?_) hB0.le
            refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            exact pow_le_pow_left₀ (hGb u ω y).1 (hGb u ω y).2 2
        _ = P.cB := by
            rw [← Finset.sum_mul, Pool.P0092.sum_toReal_one P.AB.μ, one_mul]
            linear_combination P.cB * hcw
    show ∑ z : RC P, wR P z * ((if isB P z.1 then G u ω z.2.2.1 else 0) - m u ω) ^ 2 ≤ P.cB
    rw [hvar]
    nlinarith [sq_nonneg (m u ω)]
  · rw [DB_snoc]
    have := (bPol_mem P ℓ (extD P rc0 ω) u).2
    split_ifs
    · linarith [(hGb u ω z.2.2.1).1]
    · linarith

open Classical in
/-- **`B̂` is concentrated on every interval**: the two-sided good event over all intervals `[a, b) ⊆ [0, T)` fails
with probability `≤ 2(T+1)²e^{−L}` over P0194's round coins. -/
theorem prob_not_goodB (hL : P.IsLaw) (hN : 0 < P.N) (hcw : P.cB * P.wB = 1) {L : ℝ} (hLp : 0 < L) (T : ℕ) :
    (∑ ω : Fin T → RC P, Pool.P0092.wgt (nuD P hL hN) ω *
      if Pool.P0158.GoodV (DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB) (Pool.P0158.rmax1 (fun _ => P.cB)) L T ω
      then (0 : ℝ) else 1) ≤ 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
  obtain ⟨hI, hlow⟩ := incrV_DB P ℓ rc0 hL hN hcw
  have hc0 : 0 ≤ P.cB := by linarith [(cB_ge_one P hL hcw).1]
  exact Pool.P0158.prob_not_goodV _ _ _ hI hlow (fun _ => hc0) _ (fun a b => Pool.P0158.rmax1_pos _ a b)
    (fun a b s has hsb => Pool.P0158.le_rmax1 (fun _ => P.cB) has hsb) hLp T

theorem DB_pre (ω : ℕ → RC P) (u : ℕ) :
    DB P ℓ rc0 u (pre P ω (u + 1)) = incBD P ℓ ω u - bPol P ℓ ω u := by
  have hag := extD_pre_agree P rc0 ω (u + 1)
  unfold DB incBD
  rw [bPol_congrD P ℓ u (hag.mono (Nat.le_succ u)), hag u (Nat.lt_succ_self u), bAct_congr u hag]

/-- **The good event on a full coin sequence**: on every interval `[a, b) ⊆ [0, T)`, `|Σ (B̂ increment − bPol)| <
widV((b−a)·cB, max(1, cB), L)`. -/
theorem goodB_run (ω : ℕ → RC P) {L : ℝ} (T : ℕ)
    (hgood : Pool.P0158.GoodV (DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB) (Pool.P0158.rmax1 (fun _ => P.cB)) L T
      (pre P ω T)) (a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T) :
    |∑ u ∈ Ico a b, (incBD P ℓ ω u - bPol P ℓ ω u)| <
      Pool.P0158.widV (∑ _s ∈ Ico a b, P.cB) (Pool.P0158.rmax1 (fun _ => P.cB) a b) L := by
  have h := hgood a b hab hbT
  have hrun : ∀ T', Pool.P0092.runSum (Pool.P0139.gD (DB P ℓ rc0) (fun _ _ => true) a b) T' (pre P ω T') =
      ∑ u ∈ range T', if a ≤ u ∧ u < b then DB P ℓ rc0 u (pre P ω (u + 1)) else 0 := by
    intro T'
    induction T' with
    | zero => simp [Pool.P0092.runSum]
    | succ T' ih =>
      simp only [Pool.P0092.runSum, Finset.sum_range_succ]
      rw [init_pre, ih]
      congr 1
      simp only [Pool.P0139.gD, and_true]
  rw [hrun T, ← Finset.sum_filter] at h
  have hset : (range T).filter (fun u => a ≤ u ∧ u < b) = Ico a b := by
    ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hset] at h
  simpa only [DB_pre P ℓ rc0 ω] using h

end Pool.P0216
