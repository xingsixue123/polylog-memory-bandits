import Pool.P0202.SubBridge
import Pool.P0194.Proc
import Pool.P0129.ProbeCost

/-!
# C2 for P0194's per-thread process: BASE's policy loss is the loss of `Sub (toMachine BASE) wB`

In P0194's round-level process on dzRun, BASE (`P.AB`) updates only on BASE rounds (round kind `none`), with the
action/update coins of the round. Under P0194's round-coin weight `wR` (kind weight `wK`, uniform draw coin, BASE's coin
laws), when the kind weights form a law (`ParD.IsLaw`), the BASE flag and BASE's coins are independent with flag
probability `wB` (`prodLaw_wR`), so the generic bridge applies.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0055 Pool.P0194 Pool.P0202

namespace Pool.P0202

attribute [local instance] CoinAlg.fS CoinAlg.fY CoinAlg.fZ

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι)

theorem wB_le_one (hL : P.IsLaw) : P.wB ≤ 1 := by
  obtain ⟨_, hE, hx, hs⟩ := hL
  have : 0 ≤ ∑ j, (P.sl j : ℝ) * P.xr j := Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (hx j)
  linarith

/-- Under `wR` with a law of round kinds, the BASE flag of the kind and BASE's two coins are independent, with flag
probability `wB`. -/
theorem prodLaw_wR (hL : P.IsLaw) (hN : 0 < P.N) :
    ProdLaw P.AB (wR P) P.wB (fun rc => isB P rc.1) (fun rc => rc.2.2.1) (fun rc => rc.2.2.2) := by
  intro g
  unfold wR
  simp only [Fintype.sum_prod_type]
  have hN' : (P.N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hd : ∀ κ : Kd P, ∑ _d : Fin P.N, ∑ yB, ∑ zB,
      wK P κ * (1 / (P.N : ℝ)) * (P.AB.μ yB).toReal * (P.AB.ν zB).toReal * g (isB P κ) yB zB =
      ∑ yB, ∑ zB, wK P κ * ((P.AB.μ yB).toReal * (P.AB.ν zB).toReal * g (isB P κ) yB zB) := by
    intro κ
    rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun yB _ => Finset.sum_congr rfl fun zB _ => ?_
    field_simp
  simp only [hd]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun yB _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun zB _ => ?_
  -- the kind sum: weight `wB` on BASE rounds, `1 - wB` on the others
  have hsplit : ∀ κ : Kd P, wK P κ * ((P.AB.μ yB).toReal * (P.AB.ν zB).toReal * g (isB P κ) yB zB) =
      (P.AB.μ yB).toReal * (P.AB.ν zB).toReal * (wK P κ * (if isB P κ then g true yB zB else g false yB zB)) := by
    intro κ
    cases h : isB P κ <;> simp <;> ring
  simp only [hsplit, ← Finset.mul_sum]
  congr 1
  have hrest : ∑ x : Pool.P0176.RT P.D P.sl, wK P (some x) = 1 - P.wB := by
    have h := sum_wK P
    rw [Fintype.sum_option] at h
    have e : wK P none = P.wB := rfl
    linarith [hL.2.2.2]
  rw [Fintype.sum_option]
  have hb : ∀ x : Pool.P0176.RT P.D P.sl, isB P (some x) = false := fun _ => rfl
  simp only [hb, show isB P none = true from rfl, if_true, Bool.false_eq_true, if_false, ← Finset.sum_mul, hrest]
  rfl

/-- P0194's BASE state, for any coin sequence `ω` agreeing with `ω'` below `t`, is the generic `baseRun`. -/
theorem sB_eq_baseRun (ℓ : LossSeq n) {t : ℕ} (ω : ℕ → RC P) (ω' : Fin t → RC P)
    (hag : ∀ v (hv : v < t), ω v = ω' ⟨v, hv⟩) :
    ∀ u (h : u ≤ t), sB P ℓ ω u =
      baseRun P.AB ℓ (fun rc => isB P rc.1) (fun rc => rc.2.2.1) (fun rc => rc.2.2.2) u (pre h ω') := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro h
    have hlast : pre h ω' (Fin.last u) = ω u := (hag u (by omega)).symm
    have hinit : Fin.init (pre h ω') = pre (Nat.le_of_succ_le h) ω' := by funext j; rfl
    simp only [sB, baseRun, hlast, hinit, ih (Nat.le_of_succ_le h)]

theorem bPol_eq_pol (ℓ : LossSeq n) {t : ℕ} (ω : ℕ → RC P) (ω' : Fin t → RC P)
    (hag : ∀ v (hv : v < t), ω v = ω' ⟨v, hv⟩) :
    bPol P ℓ ω t =
      pol P.AB ℓ t (baseRun P.AB ℓ (fun rc => isB P rc.1) (fun rc => rc.2.2.1) (fun rc => rc.2.2.2) t ω') := by
  unfold bPol pol
  rw [sB_eq_baseRun P ℓ ω ω' hag t le_rfl]
  rfl

/-- **C2, per round.** -/
theorem expect_bPol_eq_expLoss (hL : P.IsLaw) (hN : 0 < P.N) {w0 : RC P → ℝ} (hw : ∀ rc, w0 rc = wR P rc)
    (ℓ : LossSeq n) (t : ℕ) (E : (Fin t → RC P) → ℕ → RC P) (hE : ∀ ω' v (hv : v < t), E ω' v = ω' ⟨v, hv⟩) :
    ∑ ω' : Fin t → RC P, pw w0 ω' * bPol P ℓ (E ω') t =
      (Sub P.AB.toMachine P.wB hL.1 (wB_le_one P hL)).expLoss ℓ t := by
  have hw' : w0 = wR P := funext hw
  subst hw'
  rw [expLoss_Sub_eq_coins (wR P) ℓ hL.1 (wB_le_one P hL) (prodLaw_wR P hL hN) t]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [bPol_eq_pol P ℓ (E ω') ω' (hE ω')]

/-- **C2, summed.** `Σ_{t<T} E[bPol_t − ℓ_t(i)] ≤ regret (Sub P.AB.toMachine wB) ℓ T`. -/
theorem sum_expect_bPol_sub_le_regret (hL : P.IsLaw) (hN : 0 < P.N) {w0 : RC P → ℝ}
    (hw : ∀ rc, w0 rc = wR P rc) (ℓ : LossSeq n) (T : ℕ) (E : (t : ℕ) → (Fin t → RC P) → ℕ → RC P)
    (hE : ∀ t ω' v (hv : v < t), E t ω' v = ω' ⟨v, hv⟩) (i : Fin n) :
    ∑ t ∈ Finset.range T, ∑ ω' : Fin t → RC P, pw w0 ω' * (bPol P ℓ (E t ω') t - ((ℓ t i).toNat : ℝ)) ≤
      regret (Sub P.AB.toMachine P.wB hL.1 (wB_le_one P hL)) ℓ T := by
  have h1 : ∑ w, w0 w = 1 := by
    have hw' : w0 = wR P := funext hw
    subst hw'
    exact (prodLaw_wR P hL hN).sum_one
  have hsum : ∀ t, ∑ ω' : Fin t → RC P, pw w0 ω' * (bPol P ℓ (E t ω') t - ((ℓ t i).toNat : ℝ)) =
      (Sub P.AB.toMachine P.wB hL.1 (wB_le_one P hL)).expLoss ℓ t - ((ℓ t i).toNat : ℝ) := by
    intro t
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [expect_bPol_eq_expLoss P hL hN hw ℓ t (E t) (hE t), ← Finset.sum_mul, sum_pw_one h1, one_mul]
  simp only [hsum, Finset.sum_sub_distrib]
  unfold regret
  linarith [bestLoss_le_cumLoss ℓ T i, show cumLoss ℓ T i = ∑ t ∈ Finset.range T, ((ℓ t i).toNat : ℝ) from rfl]

/-- **C2 bound** (P0067), in P0129's `expect` notation, for a law of round kinds (`ParD.IsLaw`), a homogeneous BASE
(P0173's `CoinHom`) and `0 < wB`. (P0194's `ParD.Intended` implies both hypotheses; its other parts, `cB·wB = 1` and
`OneSlot`, are not needed for the BASE term.) -/
theorem sum_expect_bPol_sub_le_fixed [NeZero n] (hL : P.IsLaw) (hA : Pool.P0173.CoinHom P.AB) (hN : 0 < P.N)
    (hB : 0 < P.wB)
    (ν : PMF (RC P)) (hν : ∀ rc, (ν rc).toReal = wR P rc) (ℓ : LossSeq n) (T H : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hR : ∀ (ℓ' : LossSeq n) m, m ≤ T → m ≤ H → regret P.AB.toMachine ℓ' m ≤ ρ)
    (E : (t : ℕ) → (Fin t → RC P) → ℕ → RC P) (hE : ∀ t ω' v (hv : v < t), E t ω' v = ω' ⟨v, hv⟩) (i : Fin n) :
    ∑ t ∈ Finset.range T, Pool.P0129.expect ν t (fun ω' => bPol P ℓ (E t ω') t - ((ℓ t i).toNat : ℝ)) ≤
      (1 / P.wB) * (ρ + T * ((1 + P.wB) ^ T / 2 ^ (H + 1))) :=
  (sum_expect_bPol_sub_le_regret P hL hN (w0 := fun rc => (ν rc).toReal) hν ℓ T E hE i).trans
    (Pool.P0067.regret_Sub_le_fixed P.AB.toMachine (Pool.P0173.toMachine_isHomogeneous hA) hB
      (wB_le_one P hL) ℓ T H ρ hρ hR)

/-- A coin law with real weights `wR` exists when the round kinds form a law (`hν` of the bounds is satisfiable). -/
theorem exists_nu (hL : P.IsLaw) (hN : 0 < P.N) : ∃ ν : PMF (RC P), ∀ rc, (ν rc).toReal = wR P rc := by
  refine ⟨PMF.ofFintype (fun rc => ENNReal.ofReal (wR P rc)) ?_, fun rc => ?_⟩
  · rw [← ENNReal.ofReal_sum_of_nonneg (fun rc _ => wR_nonneg P hL rc), sum_wR P hL hN, ENNReal.ofReal_one]
  · rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (wR_nonneg P hL rc)]

/-- **C2, horizon form** (for one-horizon summed identities such as P0187/P0188's): with all rounds averaged over one
coin vector `ω : Fin T → RC P` (extended to `ℕ` by any rule `E` agreeing with `ω` below `T`), the weighted
`Σ_{u<T} (bPol_u − ℓ_u(i))` is `≤ regret (Sub P.AB.toMachine wB) ℓ T` (prefix marginalization inside). -/
theorem horizon_bPol_sub_le_regret (hL : P.IsLaw) (hN : 0 < P.N) {w0 : RC P → ℝ} (hw : ∀ rc, w0 rc = wR P rc)
    (ℓ : LossSeq n) (T : ℕ) (E : (Fin T → RC P) → ℕ → RC P) (hE : ∀ ω v (hv : v < T), E ω v = ω ⟨v, hv⟩)
    (i : Fin n) :
    ∑ ω : Fin T → RC P, pw w0 ω * ∑ u : Fin T, (bPol P ℓ (E ω) u - ((ℓ u i).toNat : ℝ)) ≤
      regret (Sub P.AB.toMachine P.wB hL.1 (wB_le_one P hL)) ℓ T := by
  have hw' : w0 = wR P := funext hw
  subst hw'
  refine le_of_eq_of_le ?_ (sum_pol_sub_le_regret (wR P) ℓ hL.1 (wB_le_one P hL) (prodLaw_wR P hL hN) T i)
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [bPol_eq_pol P ℓ (E ω) (pre u.2.le ω) (fun v hv => by rw [hE ω v (by omega)]; rfl)]

end Pool.P0202
