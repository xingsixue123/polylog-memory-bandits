import Pool.P0181.Proc
import Pool.P0129.ProbeCost

open Finset Pool.P0001 Pool.P0050 Pool.P0181

namespace Pool.P0187

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : Par n ι)

lemma wR_nonneg (rc : RC P) : 0 ≤ wR P rc := by
  unfold wR
  apply mul_nonneg (mul_nonneg (mul_nonneg _ _) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg <;> positivity

lemma sum_wR (hS : 0 < P.S) (hN : 0 < P.N) : ∑ rc : RC P, wR P rc = 1 := by
  have hμ : ∑ yB : P.AB.Y, (P.AB.μ yB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.μ
  have hν : ∑ zB : P.AB.Z, (P.AB.ν zB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.ν
  simp only [wR, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hν, hμ, mul_one]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The round-coin law as a PMF. -/
noncomputable def nu (hS : 0 < P.S) (hN : 0 < P.N) : PMF (RC P) :=
  PMF.ofFintype (fun rc => ENNReal.ofReal (wR P rc)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun rc _ => wR_nonneg P rc), sum_wR P hS hN, ENNReal.ofReal_one])

lemma nu_toReal (hS : 0 < P.S) (hN : 0 < P.N) (rc : RC P) : (nu P hS hN rc).toReal = wR P rc := by
  simp [nu, ENNReal.toReal_ofReal (wR_nonneg P rc)]

/-- A finite coin prefix extended by a default coin. -/
def ext (rc0 : RC P) {t : ℕ} (ω : Fin t → RC P) : ℕ → RC P :=
  fun u => if h : u < t then ω ⟨u, h⟩ else rc0

lemma ext_snoc_agree (rc0 : RC P) {t : ℕ} (ω : Fin t → RC P) (z : RC P) :
    Agree P (ext P rc0 (Fin.snoc ω z : Fin (t + 1) → RC P)) (Function.update (ext P rc0 ω) t z) (t + 1) := by
  intro v hv
  by_cases hvt : v = t
  · subst hvt
    simp [ext, Fin.snoc]
  · have hv' : v < t := by omega
    rw [Function.update_of_ne hvt]
    simp only [ext, dif_pos hv', dif_pos hv]
    simp [Fin.snoc, hv']

lemma ext_init_agree (rc0 : RC P) {t : ℕ} (ω : Fin (t + 1) → RC P) :
    Agree P (ext P rc0 (Fin.init ω)) (ext P rc0 ω) t := by
  intro v hv
  simp only [ext, dif_pos hv, dif_pos (by omega : v < t + 1)]
  rfl

variable (ℓ : LossSeq n) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- Loss increment of round `s` on a coin prefix of length `s + 1`. -/
noncomputable def lossD (rc0 : RC P) (s : ℕ) (ω : Fin (s + 1) → RC P) : ℝ :=
  ((ℓ s (play P ℓ (ext P rc0 ω) ωs φ s)).toNat : ℝ)

/-- The run sum of `lossD` is the total loss of the extended run. -/
theorem runSum_lossD (rc0 : RC P) : ∀ (t : ℕ) (ω : Fin t → RC P),
    Pool.P0092.runSum (lossD P ℓ ωs φ rc0) t ω
      = ∑ u ∈ range t, ((ℓ u (play P ℓ (ext P rc0 ω) ωs φ u)).toNat : ℝ) := by
  intro t
  induction t with
  | zero => intro ω; simp [Pool.P0092.runSum]
  | succ t ih =>
    intro ω
    rw [Pool.P0092.runSum, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mem_range] at hu
    rw [play_congr ωs φ u ((ext_init_agree P rc0 ω).mono (by omega))]

/-- One round: averaging the round-`t` loss over a fresh coin gives `condLoss`. -/
theorem avg_lossD (hS : 0 < P.S) (hN : 0 < P.N) (rc0 : RC P) {t : ℕ} (ω' : Fin t → RC P) :
    ∑ z, (nu P hS hN z).toReal * lossD P ℓ ωs φ rc0 t (Fin.snoc ω' z)
      = condLoss P ℓ ωs φ (ext P rc0 ω') t := by
  unfold condLoss lossD
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [nu_toReal, play_congr ωs φ t (ext_snoc_agree P rc0 ω' z)]

/-- **Summed loss identity (C9a).** Over i.i.d. round coins with law `wR` (for fixed sampling and filter bits),
the expected total loss over `T` rounds equals the sum over rounds of the expected average position value
(P0181's `condLoss_eq`). -/
theorem expected_loss_eq (hS : 0 < P.S) (hN : 0 < P.N) (rc0 : RC P) (T : ℕ) :
    Pool.P0129.expect (nu P hS hN) T (fun ω =>
        ∑ u ∈ range T, ((ℓ u (play P ℓ (ext P rc0 ω) ωs φ u)).toNat : ℝ))
      = ∑ t ∈ range T, Pool.P0129.expect (nu P hS hN) t (fun ω' =>
          (1 / (P.S : ℝ)) * ∑ y : Fin P.S, posVal P ℓ ωs φ (ext P rc0 ω') t y) := by
  have hfun : (fun ω : Fin T → RC P => ∑ u ∈ range T, ((ℓ u (play P ℓ (ext P rc0 ω) ωs φ u)).toNat : ℝ))
      = Pool.P0092.runSum (lossD P ℓ ωs φ rc0) T := by
    funext ω; rw [runSum_lossD]
  rw [hfun]
  clear hfun
  induction T with
  | zero => simp [Pool.P0129.expect, Pool.P0092.runSum]
  | succ T ih =>
    rw [Pool.P0129.expect_runSum_succ, ih, Finset.sum_range_succ]
    congr 1
    unfold Pool.P0129.expect
    refine Finset.sum_congr rfl fun ω' _ => ?_
    rw [avg_lossD P ℓ ωs φ hS hN rc0 ω', condLoss_eq P ℓ ωs φ hN]

/-- Probing value of position `y` at round `u`: occupant's loss minus BASE's policy loss on an occupied active
slot, `0` elsewhere. -/
noncomputable def probeVal (ω : ℕ → RC P) (u : ℕ) (y : Fin P.S) : ℝ :=
  if P.isSlot y then
    (match occAt P ℓ ωs φ ω u y with
      | some x => ((ℓ u (P.arm x)).toNat : ℝ) - bPol P ℓ ω u
      | none => 0)
  else 0

/-- Numbers of exploitation and of slot-or-BASE positions. -/
def nExp : ℕ := (univ.filter fun y : Fin P.S => isExp P y = true).card
def nSB : ℕ := (univ.filter fun y : Fin P.S => isExp P y = false).card

/-- Exploitation positions and slot-or-BASE positions partition the `S` positions. -/
theorem nExp_add_nSB : (nExp P : ℝ) + nSB P = P.S := by
  unfold nExp nSB
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin P.S)))
    (fun y => isExp P y = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at this
  exact_mod_cast this

lemma posVal_split (ω : ℕ → RC P) (u : ℕ) (y : Fin P.S) :
    posVal P ℓ ωs φ ω u y
      = (if isExp P y then aPol P ℓ ωs φ ω u else bPol P ℓ ω u) + probeVal P ℓ ωs φ ω u y := by
  unfold posVal probeVal isExp
  by_cases h1 : P.isSlot y = true
  · have h2 : P.isBase y = false := P.slot_base y h1
    simp only [h1, h2, if_true, Bool.true_or, Bool.not_true]
    rcases occAt P ℓ ωs φ ω u y with _ | x <;> simp
  · simp only [Bool.not_eq_true] at h1
    simp only [h1, Bool.false_eq_true, if_false, Bool.false_or, add_zero]
    by_cases h3 : P.isBase y = true
    · simp [h3]
    · simp only [Bool.not_eq_true] at h3; simp [h3]

/-- **Three-term decomposition (P0166's C1, rearranged).** For any fixed arm value `g` (e.g. `ℓ_u(i*)`):
`(1/S)·Σ_y posVal − g = (nExp/S)(aPol − g) + (nSB/S)(bPol − g) + (1/S)·Σ_y probeVal`. -/
theorem posVal_decomp (hS : 0 < P.S) (ω : ℕ → RC P) (u : ℕ) (g : ℝ) :
    (1 / (P.S : ℝ)) * ∑ y : Fin P.S, posVal P ℓ ωs φ ω u y - g
      = (nExp P / (P.S : ℝ)) * (aPol P ℓ ωs φ ω u - g) + (nSB P / (P.S : ℝ)) * (bPol P ℓ ω u - g)
        + (1 / (P.S : ℝ)) * ∑ y : Fin P.S, probeVal P ℓ ωs φ ω u y := by
  have hcard : (nExp P : ℝ) + nSB P = P.S := nExp_add_nSB P
  have hsplit : ∑ y : Fin P.S, posVal P ℓ ωs φ ω u y
      = nExp P * aPol P ℓ ωs φ ω u + nSB P * bPol P ℓ ω u
        + ∑ y : Fin P.S, probeVal P ℓ ωs φ ω u y := by
    simp only [posVal_split, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun y : Fin P.S => isExp P y = true)]
    have e1 : ∑ y ∈ univ.filter (fun y : Fin P.S => isExp P y = true),
        (if isExp P y then aPol P ℓ ωs φ ω u else bPol P ℓ ω u) = nExp P * aPol P ℓ ωs φ ω u := by
      rw [Finset.sum_congr rfl (fun y hy => by rw [if_pos (Finset.mem_filter.mp hy).2]),
        Finset.sum_const, nsmul_eq_mul]; rfl
    have e2 : ∑ y ∈ univ.filter (fun y : Fin P.S => ¬ isExp P y = true),
        (if isExp P y then aPol P ℓ ωs φ ω u else bPol P ℓ ω u) = nSB P * bPol P ℓ ω u := by
      rw [Finset.sum_congr rfl (fun y hy => by rw [if_neg (Finset.mem_filter.mp hy).2]),
        Finset.sum_const, nsmul_eq_mul]
      unfold nSB; simp only [Bool.not_eq_true]
    rw [e1, e2]
  rw [hsplit]
  have hS' : (P.S : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  field_simp
  rw [← hcard]
  ring

/-- **Summed regret identity (C9a).** For a fixed arm `i`, over i.i.d. round coins and for fixed sampling/filter
bits, the expected regret against `i` over `T` rounds splits into ALG's term, BASE's term and the probing term,
each a sum over rounds of an expectation over the coins before the round. -/
theorem expected_regret_eq (hS : 0 < P.S) (hN : 0 < P.N) (rc0 : RC P) (T : ℕ) (i : Fin n) :
    Pool.P0129.expect (nu P hS hN) T (fun ω =>
        ∑ u ∈ range T, ((ℓ u (play P ℓ (ext P rc0 ω) ωs φ u)).toNat : ℝ))
      - ∑ u ∈ range T, ((ℓ u i).toNat : ℝ)
      = ∑ t ∈ range T, Pool.P0129.expect (nu P hS hN) t (fun ω' =>
          (nExp P / (P.S : ℝ)) * (aPol P ℓ ωs φ (ext P rc0 ω') t - (ℓ t i).toNat)
          + (nSB P / (P.S : ℝ)) * (bPol P ℓ (ext P rc0 ω') t - (ℓ t i).toNat)
          + (1 / (P.S : ℝ)) * ∑ y : Fin P.S, probeVal P ℓ ωs φ (ext P rc0 ω') t y) := by
  rw [expected_loss_eq P ℓ ωs φ hS hN rc0 T, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hsub : ∀ (f : (Fin t → RC P) → ℝ) (c : ℝ),
      Pool.P0129.expect (nu P hS hN) t f - c = Pool.P0129.expect (nu P hS hN) t (fun ω => f ω - c) := by
    intro f c
    unfold Pool.P0129.expect
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, Pool.P0092.sum_wgt, one_mul]
  rw [hsub]
  unfold Pool.P0129.expect
  refine Finset.sum_congr rfl fun ω' _ => ?_
  simp only []
  rw [posVal_decomp P ℓ ωs φ hS]

end Pool.P0187
