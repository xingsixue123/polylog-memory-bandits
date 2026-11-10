import Pool.P0050.CoinAlg
import Pool.P0055.Subsample
import Pool.P0067.SubFixed
import Pool.P0173.StepClass

/-!
# A coin-driven BASE updated only on flagged rounds is P0055's subsampled machine (P0166's component C2), generic

Round coins `w : Ω` are i.i.d. with real weights `w0 w` (a finite coin sequence `ω : Fin t → Ω` has weight
`pw w0 ω = Π_j w0 (ω j)`). A coin algorithm `A` (P0050) is updated only on rounds whose coin is flagged
(`fl w = true`), with action coin `ya w`, update coin `za w` and the loss of the arm it pulls; its realized core state
is `baseRun`. If flag, action coin and update coin are independent with laws `γ`-coin, `A.μ`, `A.ν` (`ProdLaw`):

* `expect_Sub_eq`: the state law of `Sub (A.toMachine) γ` (P0055) at round `t` is the weighted law of
  `(baseRun t ω, y)` with a fresh `y ∼ A.μ`;
* `expLoss_Sub_eq_coins`: its expected loss at round `t` is the weighted average of BASE's policy loss
  `pol t s = Σ_y μ(y)·ℓ_t(act 0 s y)` at the realized core state;
* `sum_pol_eq_cumLoss`: over a horizon `T` with coins `ω : Fin T → Ω`, the weighted `Σ_{u<T} pol u (baseRun u (ω↾u))`
  is the expected cumulative loss of `Sub (A.toMachine) γ`.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0055
open scoped ENNReal

namespace Pool.P0202

attribute [local instance] CoinAlg.fS CoinAlg.fY CoinAlg.fZ

variable {n : ℕ} (A : CoinAlg n) {Ω : Type} [Fintype Ω]

/-- Weight of a finite coin sequence. -/
def pw (w0 : Ω → ℝ) {t : ℕ} (ω : Fin t → Ω) : ℝ := ∏ j, w0 (ω j)

theorem pw_snoc (w0 : Ω → ℝ) {t : ℕ} (ω : Fin t → Ω) (w : Ω) :
    pw w0 (Fin.snoc ω w : Fin (t + 1) → Ω) = pw w0 ω * w0 w := by
  simp [pw, Fin.prod_univ_castSucc]

theorem sum_snoc_pw (w0 : Ω → ℝ) {t : ℕ} (F : (Fin (t + 1) → Ω) → ℝ) :
    ∑ ω, pw w0 ω * F ω = ∑ ω' : Fin t → Ω, pw w0 ω' * ∑ w, w0 w * F (Fin.snoc ω' w) := by
  rw [Pool.P0050.sum_split, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [pw_snoc]; ring

/-- One round coin carries an independent flag (`γ`-coin), action coin (`A.μ`) and update coin (`A.ν`). -/
def ProdLaw (w0 : Ω → ℝ) (γ : ℝ) (fl : Ω → Bool) (ya : Ω → A.Y) (za : Ω → A.Z) : Prop :=
  ∀ g : Bool → A.Y → A.Z → ℝ, ∑ w, w0 w * g (fl w) (ya w) (za w) =
    ∑ y, ∑ z, (A.μ y).toReal * (A.ν z).toReal * (γ * g true y z + (1 - γ) * g false y z)

variable {A}

theorem ProdLaw.sum_one {w0 : Ω → ℝ} {γ : ℝ} {fl : Ω → Bool} {ya : Ω → A.Y} {za : Ω → A.Z}
    (hP : ProdLaw A w0 γ fl ya za) : ∑ w, w0 w = 1 := by
  have h := hP (fun _ _ _ => 1)
  have hμ := Pool.P0050.pmf_sum_toReal A.μ
  have hν := Pool.P0050.pmf_sum_toReal A.ν
  simp only [mul_one] at h
  rw [h]
  have e1 : γ + (1 - γ) = 1 := by ring
  simp only [mul_one, e1]
  rw [← Finset.sum_mul_sum, hμ, hν, mul_one]

/-- The prefix of length `u` of a coin sequence of length `T ≥ u`. -/
def pre {u T : ℕ} (h : u ≤ T) (ω : Fin T → Ω) : Fin u → Ω := fun j => ω (Fin.castLE h j)

/-- Weighted sums of a function of a prefix: the coins after the prefix integrate out. -/
theorem sum_pw_prefix {w0 : Ω → ℝ} (h1 : ∑ w, w0 w = 1) (u : ℕ) (F : (Fin u → Ω) → ℝ) :
    ∀ T (h : u ≤ T), ∑ ω : Fin T → Ω, pw w0 ω * F (pre h ω) = ∑ ω : Fin u → Ω, pw w0 ω * F ω := by
  intro T h
  induction T, h using Nat.le_induction with
  | base => rfl
  | succ T hT ih =>
    rw [sum_snoc_pw, ← ih]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    have : ∀ w, F (pre (Nat.le_succ_of_le hT) (Fin.snoc ω' w : Fin (T + 1) → Ω)) = F (pre hT ω') := by
      intro w
      congr 1
      funext j
      simp only [pre]
      rw [show (Fin.castLE (Nat.le_succ_of_le hT) j : Fin (T + 1)) = Fin.castSucc (Fin.castLE hT j) from
        Fin.ext rfl, Fin.snoc_castSucc]
    simp only [this, ← Finset.sum_mul, h1, one_mul]

variable (A)

/-- BASE's realized core state: updated (rules at round `0`) only on flagged rounds, with the loss of the arm it
pulls. -/
def baseRun (ℓ : LossSeq n) (fl : Ω → Bool) (ya : Ω → A.Y) (za : Ω → A.Z) : (t : ℕ) → (Fin t → Ω) → A.S
  | 0, _ => A.s0
  | t + 1, ω =>
    if fl (ω (Fin.last t)) then
      A.upd 0 (baseRun ℓ fl ya za t (Fin.init ω)) (ya (ω (Fin.last t)))
        (ℓ t (A.act 0 (baseRun ℓ fl ya za t (Fin.init ω)) (ya (ω (Fin.last t))))) (za (ω (Fin.last t)))
    else baseRun ℓ fl ya za t (Fin.init ω)

/-- BASE's policy loss at round `t` from core state `s` (expectation over a fresh action coin). -/
noncomputable def pol (ℓ : LossSeq n) (t : ℕ) (s : A.S) : ℝ :=
  ∑ y, (A.μ y).toReal * ((ℓ t (A.act 0 s y)).toNat : ℝ)

variable {A}

/-- One step of `Sub (A.toMachine) γ` at round `t`, in real numbers. -/
theorem stepExp_Sub0 (ℓ : LossSeq n) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (t : ℕ) (p : A.S × A.Y)
    (F : A.S × A.Y → ℝ) :
    Pool.P0012.stepExp (Sub A.toMachine γ h0 h1) ℓ t p F =
      γ * ∑ z, (A.ν z).toReal * ∑ y', (A.μ y').toReal *
          F (A.upd 0 p.1 p.2 (ℓ t (A.act 0 p.1 p.2)) z, y') + (1 - γ) * F p := by
  classical
  unfold Pool.P0012.stepExp
  have hact : ∀ a, ((Sub A.toMachine γ h0 h1).act t p a).toReal =
      if a = A.act 0 p.1 p.2 then 1 else 0 := by
    intro a
    show ((PMF.pure (A.act 0 p.1 p.2)) a).toReal = _
    by_cases h : a = A.act 0 p.1 p.2 <;> simp [PMF.pure_apply, h]
  rw [Finset.sum_eq_single (A.act 0 p.1 p.2)]
  · rw [hact, if_pos rfl, one_mul]
    set b := ℓ t (A.act 0 p.1 p.2)
    show ∑ s', (((coin γ h0 h1).bind fun c => if c then
        (A.ν.bind fun z => A.μ.map fun y' => (A.upd 0 p.1 p.2 b z, y')) else PMF.pure p) s').toReal * F s' = _
    simp only [Pool.P0012.bind_toReal, Fintype.sum_bool, coin_toReal, if_true, Bool.false_eq_true, if_false,
      add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    congr 1
    · congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [mul_assoc, ← Finset.mul_sum]
      congr 1
      rw [Pool.P0050.sum_map_toReal]
    · congr 1
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; simp [PMF.pure_apply, hq]
      · simp
  · intro a _ ha; rw [hact, if_neg ha, zero_mul]
  · simp

/-- `stepExp_Sub0` with the machine's state type (for rewriting). -/
theorem stepExp_Sub (ℓ : LossSeq n) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) (t : ℕ) (p : A.toMachine.State)
    (F : A.toMachine.State → ℝ) :
    Pool.P0012.stepExp (Sub A.toMachine γ h0 h1) ℓ t p F =
      γ * ∑ z, (A.ν z).toReal * ∑ y', (A.μ y').toReal *
          F (A.upd 0 p.1 p.2 (ℓ t (A.act 0 p.1 p.2)) z, y') + (1 - γ) * F p :=
  stepExp_Sub0 ℓ h0 h1 t p F

/-- **Law bridge.** The state law of `Sub (A.toMachine) γ` at round `t` is the weighted law of BASE's realized
core state paired with a fresh action coin. -/
theorem expect_Sub_eq (w0 : Ω → ℝ) (ℓ : LossSeq n) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    {fl : Ω → Bool} {ya : Ω → A.Y} {za : Ω → A.Z} (hP : ProdLaw A w0 γ fl ya za) :
    ∀ (t : ℕ) (G : A.toMachine.State → ℝ),
      Pool.P0012.expect (Sub A.toMachine γ h0 h1) ℓ t G =
        ∑ ω : Fin t → Ω, pw w0 ω * ∑ y, (A.μ y).toReal * G (baseRun A ℓ fl ya za t ω, y) := by
  have hμ := Pool.P0050.pmf_sum_toReal A.μ
  have hν := Pool.P0050.pmf_sum_toReal A.ν
  intro t
  induction t with
  | zero =>
    intro G
    unfold Pool.P0012.expect
    show ∑ s, ((A.μ.map fun y => (A.s0, y)) s).toReal * G s = _
    erw [Pool.P0050.sum_map_toReal]
    conv_rhs => rw [Fintype.sum_unique]
    simp [pw, baseRun]
  | succ t ih =>
    intro G
    erw [Pool.P0012.expect_succ]
    simp only [stepExp_Sub ℓ h0 h1]
    rw [ih, sum_snoc_pw]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    congr 1
    set s := baseRun A ℓ fl ya za t ω'
    have hrun : ∀ w, baseRun A ℓ fl ya za (t + 1) (Fin.snoc ω' w) =
        if fl w then A.upd 0 s (ya w) (ℓ t (A.act 0 s (ya w))) (za w) else s := by
      intro w
      simp only [baseRun, Fin.snoc_last, Fin.init_snoc]; rfl
    simp only [hrun]
    rw [hP (fun f y0 z => ∑ y, (A.μ y).toReal *
      G (if f then A.upd 0 s y0 (ℓ t (A.act 0 s y0)) z else s, y))]
    simp only [if_true, Bool.false_eq_true, if_false]
    have hstay : ∀ y0 z, (A.μ y0).toReal * (A.ν z).toReal *
        (γ * ∑ y, (A.μ y).toReal * G (A.upd 0 s y0 (ℓ t (A.act 0 s y0)) z, y) +
          (1 - γ) * ∑ y, (A.μ y).toReal * G (s, y)) =
        γ * ((A.μ y0).toReal * ((A.ν z).toReal *
          ∑ y, (A.μ y).toReal * G (A.upd 0 s y0 (ℓ t (A.act 0 s y0)) z, y))) +
        ((A.μ y0).toReal * (A.ν z).toReal) * ((1 - γ) * ∑ y, (A.μ y).toReal * G (s, y)) := by
      intro y0 z; ring
    simp only [hstay, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hμ, hν, one_mul, one_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y0 _ => ?_
    ring

/-- **Expected loss bridge.** The expected loss of `Sub (A.toMachine) γ` at round `t` is the weighted policy loss of
BASE at its realized core state. -/
theorem expLoss_Sub_eq_coins (w0 : Ω → ℝ) (ℓ : LossSeq n) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    {fl : Ω → Bool} {ya : Ω → A.Y} {za : Ω → A.Z} (hP : ProdLaw A w0 γ fl ya za) (t : ℕ) :
    (Sub A.toMachine γ h0 h1).expLoss ℓ t =
      ∑ ω : Fin t → Ω, pw w0 ω * pol A ℓ t (baseRun A ℓ fl ya za t ω) := by
  classical
  rw [expLoss_eq_sum]
  have hp : ∀ p : A.S × A.Y, ∑ a, ((A.toMachine.act 0 p) a).toReal * ((ℓ t a).toNat : ℝ) =
      ((ℓ t (A.act 0 p.1 p.2)).toNat : ℝ) := by
    intro p
    show ∑ a, ((PMF.pure (A.act 0 p.1 p.2)) a).toReal * _ = _
    rw [Finset.sum_eq_single (A.act 0 p.1 p.2)]
    · simp
    · intro a _ ha; simp [PMF.pure_apply, ha]
    · simp
  have h := expect_Sub_eq w0 ℓ h0 h1 hP t (fun p => ((ℓ t (A.act 0 p.1 p.2)).toNat : ℝ))
  unfold Pool.P0012.expect at h
  refine Eq.trans (Finset.sum_congr rfl fun p _ => ?_) h
  congr 1
  exact hp p

/-- **Horizon form.** With coins `ω : Fin T → Ω`, the weighted sum over rounds `u < T` of BASE's policy loss at its
realized core state (read from the prefix of length `u`) is the expected cumulative loss of `Sub (A.toMachine) γ`. -/
theorem sum_pol_eq_cumLoss (w0 : Ω → ℝ) (ℓ : LossSeq n) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    {fl : Ω → Bool} {ya : Ω → A.Y} {za : Ω → A.Z} (hP : ProdLaw A w0 γ fl ya za) (T : ℕ) :
    ∑ ω : Fin T → Ω, pw w0 ω * ∑ u : Fin T, pol A ℓ u (baseRun A ℓ fl ya za u (pre u.2.le ω)) =
      ∑ u ∈ Finset.range T, (Sub A.toMachine γ h0 h1).expLoss ℓ u := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [expLoss_Sub_eq_coins w0 ℓ h0 h1 hP]
  exact sum_pw_prefix hP.sum_one (u : ℕ) (fun ω' => pol A ℓ u (baseRun A ℓ fl ya za u ω')) T u.2.le

theorem sum_pw_one {w0 : Ω → ℝ} (h1 : ∑ w, w0 w = 1) (T : ℕ) : ∑ ω : Fin T → Ω, pw w0 ω = 1 := by
  have h := sum_pw_prefix h1 0 (fun _ => 1) T (Nat.zero_le T)
  simp only [mul_one] at h
  rw [h, Fintype.sum_unique]
  simp [pw]

/-- **Regret form.** Against any fixed arm `i`, the weighted `Σ_{u<T} (pol_u(BASE) − ℓ_u(i))` is at most the regret of
`Sub (A.toMachine) γ` over `T` rounds. -/
theorem sum_pol_sub_le_regret (w0 : Ω → ℝ) (ℓ : LossSeq n) {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1)
    {fl : Ω → Bool} {ya : Ω → A.Y} {za : Ω → A.Z} (hP : ProdLaw A w0 γ fl ya za) (T : ℕ) (i : Fin n) :
    ∑ ω : Fin T → Ω, pw w0 ω * ∑ u : Fin T,
        (pol A ℓ u (baseRun A ℓ fl ya za u (pre u.2.le ω)) - ((ℓ u i).toNat : ℝ)) ≤
      regret (Sub A.toMachine γ h0 h1) ℓ T := by
  simp only [Finset.sum_sub_distrib, mul_sub]
  rw [sum_pol_eq_cumLoss w0 ℓ h0 h1 hP T, ← Finset.sum_mul, sum_pw_one hP.sum_one, one_mul]
  unfold regret
  have hc : ∑ u : Fin T, ((ℓ u i).toNat : ℝ) = cumLoss ℓ T i := by
    unfold cumLoss
    exact Fin.sum_univ_eq_sum_range (fun u => ((ℓ u i).toNat : ℝ)) T
  rw [hc]
  linarith [bestLoss_le_cumLoss ℓ T i]

/-- **C2 bound.** For a homogeneous BASE (P0173's `CoinHom`) whose machine has regret `≤ ρ` on every prefix
`m ≤ min(T, H)` of every loss sequence, the weighted `Σ_{u<T} (pol_u(BASE) − ℓ_u(i))` is at most
`(1/γ)(ρ + T(1+γ)^T/2^(H+1))` (P0067). -/
theorem sum_pol_sub_le_fixed [NeZero n] (hA : Pool.P0173.CoinHom A) (w0 : Ω → ℝ) (ℓ : LossSeq n) {γ : ℝ}
    (hγ : 0 < γ) (h1 : γ ≤ 1) {fl : Ω → Bool} {ya : Ω → A.Y} {za : Ω → A.Z}
    (hP : ProdLaw A w0 γ fl ya za) (T H : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hR : ∀ (ℓ' : LossSeq n) m, m ≤ T → m ≤ H → regret A.toMachine ℓ' m ≤ ρ) (i : Fin n) :
    ∑ ω : Fin T → Ω, pw w0 ω * ∑ u : Fin T,
        (pol A ℓ u (baseRun A ℓ fl ya za u (pre u.2.le ω)) - ((ℓ u i).toNat : ℝ)) ≤
      (1 / γ) * (ρ + T * ((1 + γ) ^ T / 2 ^ (H + 1))) :=
  (sum_pol_sub_le_regret w0 ℓ hγ.le h1 hP T i).trans
    (Pool.P0067.regret_Sub_le_fixed A.toMachine (Pool.P0173.toMachine_isHomogeneous hA) hγ h1 ℓ T H ρ hρ hR)

end Pool.P0202
