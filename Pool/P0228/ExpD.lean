import Pool.P0223.CreditD
import Pool.P0210.Split

/-!
# P0194's probing term in expectation over the round coins (P0217's `slotT` form)

P0217 reduces the machine's regret to, among others, `slotT = Σ_{u<T} E_{coins<u}[Σ_s x_s(slotVal_u(s) − bPol_u)]`
(for fixed sampling/filter bits). Here this per-round form is rewritten as one expectation over `T` round coins of
the pathwise probing sum (`marg`), and P0223's pathwise bound is applied on a good event `G` of the coin path:
`slotT ≤ κ·Σ_u E[bPol_u − aPol_u] + E[[G]·rest] + (X₁ + κ)·T·P(¬G)` with `κ = (Σ_j sl_j)(Σ_j x_j)`,
`X₁ = Σ_s x_s` (`slot_expect`). `G` bundles no overflow, the two good events and ALG's two interval guarantees.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065

namespace Pool.P0228

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

theorem slotVal_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' u) (s : Σ j : Fin P.D, Fin (P.sl j)) :
    slotVal P ℓ ωs φ ω u s = slotVal P ℓ ωs φ ω' u s := by
  unfold slotVal
  rw [occAtS_congr ωs φ u h]
  split
  · rfl
  · exact Pool.P0216.bPol_congrD P ℓ u h

theorem aPol_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' u) :
    aPol P ℓ ωs φ ω u = aPol P ℓ ωs φ ω' u := by
  unfold aPol
  rw [sA_congr ωs φ u h, active_congr ωs φ u h, sB_congr u h]

/-- The probing integrand of round `u` (P0217's `slotT` integrand). -/
noncomputable def probeU (ω : ℕ → RC P) (u : ℕ) : ℝ :=
  ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - bPol P ℓ ω u)

theorem probeU_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' u) :
    probeU P ℓ ωs φ ω u = probeU P ℓ ωs φ ω' u := by
  unfold probeU
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [slotVal_congr P ℓ ωs φ u h s, Pool.P0216.bPol_congrD P ℓ u h]

theorem slotVal_mem (ω : ℕ → RC P) (u : ℕ) (s : Σ j : Fin P.D, Fin (P.sl j)) :
    0 ≤ slotVal P ℓ ωs φ ω u s ∧ slotVal P ℓ ωs φ ω u s ≤ 1 := by
  unfold slotVal
  split
  · exact ⟨Nat.cast_nonneg _, Pool.P0216.toNat_le_one _⟩
  · exact Pool.P0216.bPol_mem P ℓ ω u

/-- The probing integrand is at most the total slot weight `X₁ = Σ_s x_s` (nonnegative weights). -/
theorem probeU_le (hx : ∀ j, 0 ≤ P.xr j) (ω : ℕ → RC P) (u : ℕ) :
    probeU P ℓ ωs φ ω u ≤ ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 := by
  unfold probeU
  refine Finset.sum_le_sum fun s _ => ?_
  have h1 := (slotVal_mem P ℓ ωs φ ω u s).2
  have h2 := (Pool.P0216.bPol_mem P ℓ ω u).1
  have := hx s.1
  nlinarith

theorem aPol_le_one (ω : ℕ → RC P) (u : ℕ) : aPol P ℓ ωs φ ω u ≤ 1 := by
  unfold aPol
  have hμ : ∑ yB : P.AB.Y, (P.AB.μ yB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.μ
  have hin : ∀ d : Fin P.N, ∑ yB : P.AB.Y, (P.AB.μ yB).toReal *
      ((ℓ u (match P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) d with
        | some x => P.arm x
        | none => P.AB.act 0 (sB P ℓ ω u) yB)).toNat : ℝ) ≤ 1 := by
    intro d
    rw [← hμ]
    exact Finset.sum_le_sum fun yB _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (Pool.P0216.toNat_le_one _)
  refine (Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hin d) (by positivity)).trans ?_
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos P.N with h | h
  · simp [h]
  · have : (0 : ℝ) < P.N := by exact_mod_cast h
    push_cast
    rw [mul_one_div_cancel this.ne']

variable (rc₀ : RC P)

/-- **Marginalization.** For a round integrand that reads only the coins before its round, the per-round prefix
averages sum to one average over `T` coins of the total. -/
theorem marg (hL : P.IsLaw) (hN : 0 < P.N) (f : (ℕ → RC P) → ℕ → ℝ)
    (hf : ∀ u (ω ω' : ℕ → RC P), Agree P ω ω' u → f ω u = f ω' u) (T : ℕ) :
    ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' * f (Pool.P0210.extR P rc₀ ω') u =
      ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * ∑ u ∈ range T, f (Pool.P0210.extR P rc₀ ω) u := by
  have h1 : ∑ rc, wR P rc = 1 := sum_wR P hL hN
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u ≤ T := (Finset.mem_range.1 hu).le
  have hpre : ∀ ω : Fin T → RC P, f (Pool.P0210.extR P rc₀ ω) u =
      f (Pool.P0210.extR P rc₀ (Pool.P0202.pre hu' ω)) u := fun ω =>
    (hf u _ _ (Pool.P0210.agree_pre P rc₀ hu' ω)).symm
  simp_rw [hpre]
  rw [Pool.P0202.sum_pw_prefix h1 u (fun ω'' => f (Pool.P0210.extR P rc₀ ω'') u) T hu']

theorem pw_nonneg (hL : P.IsLaw) {t : ℕ} (ω : Fin t → RC P) : 0 ≤ Pool.P0202.pw (wR P) ω :=
  Finset.prod_nonneg fun j _ => wR_nonneg P hL (ω j)

theorem sum_pw (hL : P.IsLaw) (hN : 0 < P.N) (T : ℕ) : ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω = 1 := by
  have h := Pool.P0202.sum_pw_prefix (sum_wR P hL hN) 0 (fun _ => (1 : ℝ)) T (Nat.zero_le T)
  simp only [mul_one] at h
  rw [h]
  simp [Pool.P0202.pw]

/-- P0203's prefix of the extended path is the path itself. -/
theorem pre_extR {T : ℕ} (ω : Fin T → RC P) : Pool.P0203.pre P (Pool.P0210.extR P rc₀ ω) T = ω := by
  funext i
  simp [Pool.P0203.pre, Pool.P0210.extR, i.2]

/-- **Expectation step (generic).** If on a good event `G` of the coin path the probing total is at most
`κ·(BASE − ALG)[0,T) + rest`, then `slotT` (per-round form) is at most `κ·Σ_u E[bPol − aPol] + E[[G]·rest]
+ (X₁ + κ)·T·P(¬G)`, with `X₁ = Σ_s x_s`. -/
theorem slot_expect_of (hL : P.IsLaw) (hN : 0 < P.N) (T : ℕ) (κ : ℝ) (hκ : 0 ≤ κ)
    (G : (Fin T → RC P) → Prop) [DecidablePred G] (rest : (Fin T → RC P) → ℝ)
    (hG : ∀ ω, G ω → ∑ u ∈ range T, probeU P ℓ ωs φ (Pool.P0210.extR P rc₀ ω) u ≤
      κ * ∑ u ∈ range T, (bPol P ℓ (Pool.P0210.extR P rc₀ ω) u - aPol P ℓ ωs φ (Pool.P0210.extR P rc₀ ω) u)
        + rest ω) :
    ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' * probeU P ℓ ωs φ (Pool.P0210.extR P rc₀ ω') u ≤
      κ * ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
          (bPol P ℓ (Pool.P0210.extR P rc₀ ω') u - aPol P ℓ ωs φ (Pool.P0210.extR P rc₀ ω') u)
        + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if G ω then rest ω else 0)
        + ((∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + κ) * T *
            ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if G ω then 0 else 1) := by
  set X1 := ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1
  have hx : ∀ j, 0 ≤ P.xr j := fun j => (hL.2.2.1 j)
  rw [marg P rc₀ hL hN (probeU P ℓ ωs φ) (fun u _ _ h => probeU_congr P ℓ ωs φ u h) T,
    marg P rc₀ hL hN (fun ω u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u)
      (fun u _ _ h => by rw [Pool.P0216.bPol_congrD P ℓ u h, aPol_congr P ℓ ωs φ u h]) T]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hpw := pw_nonneg P hL ω
  set e := Pool.P0210.extR P rc₀ ω
  -- pointwise
  have hpt : ∑ u ∈ range T, probeU P ℓ ωs φ e u ≤
      κ * ∑ u ∈ range T, (bPol P ℓ e u - aPol P ℓ ωs φ e u) + (if G ω then rest ω else 0)
        + (X1 + κ) * T * (if G ω then 0 else 1) := by
    by_cases hg : G ω
    · simp only [hg, ite_true, mul_zero, add_zero]
      exact hG ω hg
    · simp only [hg, ite_false, mul_one, add_zero]
      have h1 : ∑ u ∈ range T, probeU P ℓ ωs φ e u ≤ T * X1 := by
        calc _ ≤ ∑ _u ∈ range T, X1 := Finset.sum_le_sum fun u _ => probeU_le P ℓ ωs φ hx e u
          _ = T * X1 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have h2 : -(T : ℝ) ≤ ∑ u ∈ range T, (bPol P ℓ e u - aPol P ℓ ωs φ e u) := by
        calc -(T : ℝ) = ∑ _u ∈ range T, (-1 : ℝ) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
          _ ≤ _ := Finset.sum_le_sum fun u _ => by
              have := (Pool.P0216.bPol_mem P ℓ e u).1
              have := aPol_le_one P ℓ ωs φ e u
              linarith
      nlinarith
  calc Pool.P0202.pw (wR P) ω * ∑ u ∈ range T, probeU P ℓ ωs φ e u
      ≤ Pool.P0202.pw (wR P) ω * (κ * ∑ u ∈ range T, (bPol P ℓ e u - aPol P ℓ ωs φ e u)
          + (if G ω then rest ω else 0) + (X1 + κ) * T * (if G ω then 0 else 1)) :=
        mul_le_mul_of_nonneg_left hpt hpw
    _ = _ := by ring

end Pool.P0228

namespace Pool.P0228

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)

/-- ALG's two interval guarantees on a path (the hypotheses `hint` and `hA` of P0223's `credit_D`). -/
def AlgOK (T : ℕ) (v : ℕ → ℝ) (ρ₀ c : ℝ) (r : ι → ℕ → ℝ) (ω : ℕ → RC P) : Prop :=
  (∀ a b, a ≤ b → b ≤ T →
      -Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) a b ≤
        ρ₀ + Pool.P0154.isum v a b + c * Real.sqrt ((b : ℝ) - a)) ∧
    (∀ x t, t ≤ T → P.E x < t → (∀ u, P.E x ≤ u → u < t → x ∈ active P ℓ ω ωs φ u) →
      Pool.P0154.isum (fun u => aPol P ℓ ωs φ ω u) (P.E x) t ≤
        Pool.P0154.isum (fun u => ℓr P ℓ u x) (P.E x) t + r x t)

/-- The non-absorbed part of P0223's pathwise bound. -/
noncomputable def restD (T : ℕ) (L : ℝ) (v : ℕ → ℝ) (ρ₀ c : ℝ) (r : ι → ℕ → ℝ) (ω : ℕ → RC P) : ℝ :=
  ∑ x ∈ univ.filter (fun x => P.E x < T),
      Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x *
        (Pool.P0223.MOfW P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin)
    + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
        (2 * (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1)
      + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
      + (∑ j : Fin P.D, (P.sl j : ℝ)) * c *
        (Real.sqrt T * Real.sqrt (2 * (Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1))
      + ∑ i ∈ Pool.P0223.Wj P ℓ ωs φ hD hLv hlev ω T j, max 0 (r i.1 i.2))

variable (rc₀ : RC P)

theorem wgt_eq_pw (hL : P.IsLaw) (hN : 0 < P.N) {t : ℕ} (ω : Fin t → RC P) :
    Pool.P0092.wgt (Pool.P0203.nuD P hL hN) ω = Pool.P0202.pw (wR P) ω := by
  unfold Pool.P0092.wgt Pool.P0202.pw
  exact Finset.prod_congr rfl fun j _ => Pool.P0203.nuD_toReal P hL hN (ω j)

open Classical in
/-- **P0194's probing term in expectation (P0217's `slotT` form, fixed sampling/filter bits).** With
`κ = (Σ_j sl_j)(Σ_j x_j)` and `X₁ = Σ_s x_s`:
`slotT ≤ κ·Σ_u E[bPol_u − aPol_u] + E[[G]·restD] + (X₁ + κ)·T·(P(overflow) + |ι|·2(T+1)²e^{−L} + 2(T+1)²e^{−L}
+ P(¬AlgOK))`, where `G` = no overflow ∧ P0203's slot good event (all copies) ∧ P0216's `B̂` good event ∧ `AlgOK`. -/
theorem slot_expect (hL : P.IsLaw) (hN : 0 < P.N) (T : ℕ) (hT : 1 ≤ T) {L : ℝ} (hLp : 0 < L)
    (hB : 0 < P.Bmin) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j) (hxr1 : ∀ j, P.xr j ≤ 1)
    (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i) (hcw : P.cB * P.wB = 1) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (v : ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c) (r : ι → ℕ → ℝ) :
    ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' * probeU P ℓ ωs φ (Pool.P0210.extR P rc₀ ω') u ≤
      ((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          ∑ u ∈ range T, ∑ ω' : Fin u → RC P, Pool.P0202.pw (wR P) ω' *
            (bPol P ℓ (Pool.P0210.extR P rc₀ ω') u - aPol P ℓ ωs φ (Pool.P0210.extR P rc₀ ω') u)
        + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
            (if (∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t)) ∧
                (∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc₀ x) (Pool.P0203.gateS P ℓ ωs φ rc₀ x)
                  (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T ω) ∧
                Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc₀) (fun _ _ => true) (fun _ => P.cB)
                  (Pool.P0158.rmax1 (fun _ => P.cB)) L T ω ∧
                AlgOK P ℓ ωs φ T v ρ₀ c r (Pool.P0210.extR P rc₀ ω)
              then restD P ℓ ωs φ hD hLv hlev T L v ρ₀ c r (Pool.P0210.extR P rc₀ ω) else 0)
        + ((∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + (∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j)
            * T * ((∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
                (if ∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t) then 0 else 1))
              + Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L))
              + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)
              + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω *
                (if AlgOK P ℓ ωs φ T v ρ₀ c r (Pool.P0210.extR P rc₀ ω) then 0 else 1)) := by
  set κ := (∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j with hκdef
  have hκ : 0 ≤ κ := mul_nonneg (Finset.sum_nonneg fun j _ => Nat.cast_nonneg _)
    (Finset.sum_nonneg fun j _ => (hxr j).le)
  have hcB : 0 ≤ P.cB := by linarith [(Pool.P0216.cB_ge_one P hL hcw).1]
  set Fit : (Fin T → RC P) → Prop := fun ω => ∀ t < T, Fits P.Lv P.sl (sp P ℓ (Pool.P0210.extR P rc₀ ω) ωs φ t)
  set GS : (Fin T → RC P) → Prop := fun ω => ∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc₀ x)
    (Pool.P0203.gateS P ℓ ωs φ rc₀ x) (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T ω
  set GB : (Fin T → RC P) → Prop := fun ω => Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc₀) (fun _ _ => true)
    (fun _ => P.cB) (Pool.P0158.rmax1 (fun _ => P.cB)) L T ω
  set GA : (Fin T → RC P) → Prop := fun ω => AlgOK P ℓ ωs φ T v ρ₀ c r (Pool.P0210.extR P rc₀ ω)
  have hstep := slot_expect_of P ℓ ωs φ rc₀ hL hN T κ hκ (fun ω => Fit ω ∧ GS ω ∧ GB ω ∧ GA ω)
    (fun ω => restD P ℓ ωs φ hD hLv hlev T L v ρ₀ c r (Pool.P0210.extR P rc₀ ω)) ?_
  · refine hstep.trans ?_
    have hX : 0 ≤ (∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + κ :=
      add_nonneg (Finset.sum_nonneg fun s _ => (hxr s.1).le) hκ
    have hcoef : 0 ≤ ((∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1) + κ) * T := mul_nonneg hX (Nat.cast_nonneg _)
    -- union bound for the bad event
    have hunion : ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if Fit ω ∧ GS ω ∧ GB ω ∧ GA ω then 0 else 1) ≤
        (∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if Fit ω then 0 else 1))
          + Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L))
          + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)
          + ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if GA ω then 0 else 1) := by
      have hS : ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if GS ω then 0 else 1) ≤
          Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) := by
        have h := Pool.P0203.prob_not_goodDS_all P ℓ ωs φ rc₀ hL hN hD hLv hlev hlay hxr hxr1 hLp T
        simp_rw [wgt_eq_pw P hL hN] at h
        exact h
      have hBd : ∑ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if GB ω then 0 else 1) ≤
          2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
        have h := Pool.P0216.prob_not_goodB P ℓ rc₀ hL hN hcw hLp T
        simp_rw [wgt_eq_pw P hL hN] at h
        exact h
      have hpt : ∀ ω : Fin T → RC P, Pool.P0202.pw (wR P) ω * (if Fit ω ∧ GS ω ∧ GB ω ∧ GA ω then 0 else 1) ≤
          Pool.P0202.pw (wR P) ω * (if Fit ω then 0 else 1) + Pool.P0202.pw (wR P) ω * (if GS ω then 0 else 1)
            + Pool.P0202.pw (wR P) ω * (if GB ω then 0 else 1) + Pool.P0202.pw (wR P) ω * (if GA ω then 0 else 1) := by
        intro ω
        have hp := pw_nonneg P hL ω
        rw [← mul_add, ← mul_add, ← mul_add]
        refine mul_le_mul_of_nonneg_left ?_ hp
        by_cases h1 : Fit ω <;> by_cases h2 : GS ω <;> by_cases h3 : GB ω <;> by_cases h4 : GA ω <;>
          simp only [h1, h2, h3, h4, and_self, and_true, and_false, ite_true, ite_false] <;>
          norm_num
      have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin T → RC P))) fun ω _ => hpt ω
      simp only [Finset.sum_add_distrib] at hsum
      linarith
    have := mul_le_mul_of_nonneg_left hunion hcoef
    linarith
  · -- the pathwise bound on the good event
    rintro ω ⟨hfit, hgS, hgB, hint, hA⟩
    have hpre := pre_extR P rc₀ ω
    have h := Pool.P0223.probe_credit_pathD P ℓ ωs φ hD hLv hlev rc₀ (Pool.P0210.extR P rc₀ ω) T hT hLp hB hlay
      hxr hanti hcB hΛ0 hfit (by rw [hpre]; exact hgS) (by rw [hpre]; exact hgB) v ρ₀ c hv hρ₀ hc hint r hA
    unfold probeU restD
    unfold Pool.P0154.isum at h ⊢
    beta_reduce at h
    rw [Finset.range_eq_Ico] at h ⊢
    rw [hκdef]
    linarith

end Pool.P0228
