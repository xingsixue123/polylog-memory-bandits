import Pool.P0200.ExtCount
import Pool.P0194.Proc

/-!
# The bad-point count for P0194's round-level process (rule (b″) reads B̂)

P0194's pool is P0176's `dzRun` (`B = 1`, `Bm = 1`) with the rule `rhD`, which reads BASE's estimate `Bh`, a function
of the round coins. This file instantiates P0200's external-rule count:
* the external part of a round coin `(κ, d, yB, zB)` is `(isB κ, yB, zB)` (`extR`), its slot part is `κ.getD none`
  (`zOfR`, P0194's `zc`);
* BASE's state, estimate and rule are recomputed from the external history (`sBE`, `BhE`, `rhXR`), and agree with
  P0194's `sB`, `Bh`, `rhD` (`sB_eq`, `Bh_eq`, `rhD_eq`); the rule family is causal (`causal_rhXR`);
* the blockwise slot permutations act on round coins by permuting slot kinds (`permR`), preserving P0194's weights
  `wR`, the external part and `zOfR`;
* `pool_eq`: on a coin prefix of length `NE`, every `dzRun` with P0194's rule and slot coins (in particular P0194's
  `pool` for any layout) is the run with the rule of the prefix's external history, up to unit `NE`.
-/

namespace Pool.P0207

open Pool.P0200
open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)

/-- The external part of a round coin: BASE flag and BASE's two coins. -/
def extR (rc : RC P) : Option (Bool × P.AB.Y × P.AB.Z) := some (isB P rc.1, rc.2.2.1, rc.2.2.2)

/-- The slot part of a round coin (P0194's `zc`). -/
def zOfR (rc : RC P) : Fin 1 → RT P.D P.sl := fun _ => rc.1.getD none

/-- BASE's state recomputed from an external history. -/
def sBE (e : ℕ → Option (Bool × P.AB.Y × P.AB.Z)) : ℕ → P.AB.S
  | 0 => P.AB.s0
  | u + 1 => match e u with
    | some (true, yb, zb) => P.AB.upd 0 (sBE e u) yb (ℓ u (P.AB.act 0 (sBE e u) yb)) zb
    | _ => sBE e u

/-- BASE's estimate recomputed from an external history. -/
noncomputable def BhE (e : ℕ → Option (Bool × P.AB.Y × P.AB.Z)) : ℕ → ℝ
  | 0 => 0
  | u + 1 => BhE e u + match e u with
    | some (true, yb, _) => P.cB * ((ℓ u (P.AB.act 0 (sBE P ℓ e u) yb)).toNat : ℝ)
    | _ => 0

/-- Rule (b″) of P0194 with B̂ recomputed from an external history. -/
noncomputable def rhXR (e : ℕ → Option (Bool × P.AB.Y × P.AB.Z)) (u : ℕ) (x : ι) (h : ℕ → ℝ) : Bool :=
  decide (P.E x ≤ u) && decide (P.Bmin ∣ u + 1) && decide (P.Λ x u ≤ h (u + 1) - h (P.E x) -
    (BhE P ℓ e (u + 1) - BhE P ℓ e (P.E x)))

theorem sBE_congr {e e' : ℕ → Option (Bool × P.AB.Y × P.AB.Z)} : ∀ u, (∀ v < u, e v = e' v) →
    sBE P ℓ e u = sBE P ℓ e' u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro h
    simp only [sBE]
    rw [ih (fun v hv => h v (by omega)), h u (by omega)]

theorem BhE_congr {e e' : ℕ → Option (Bool × P.AB.Y × P.AB.Z)} : ∀ u, (∀ v < u, e v = e' v) →
    BhE P ℓ e u = BhE P ℓ e' u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro h
    simp only [BhE]
    rw [ih (fun v hv => h v (by omega)), h u (by omega), sBE_congr P ℓ u (fun v hv => h v (by omega))]

/-- The recomputed rule reads the external history only up to its unit. -/
theorem causal_rhXR : Causal (rhXR P ℓ) := by
  intro e e' a h
  funext x hh
  simp only [rhXR]
  by_cases hx : P.E x ≤ a
  · rw [BhE_congr P ℓ (a + 1) (fun v hv => h v (by omega)), BhE_congr P ℓ (P.E x) (fun v hv => h v (by omega))]
  · simp [hx]

theorem sB_eq (ω : ℕ → RC P) : ∀ u, sB P ℓ ω u = sBE P ℓ (fun v => extR P (ω v)) u := by
  intro u
  induction u with
  | zero => rfl
  | succ u ih =>
    simp only [sB, sBE, extR] at ih ⊢
    rw [ih]
    cases isB P (ω u).1 <;> rfl

theorem Bh_eq (ω : ℕ → RC P) : ∀ u, Bh P ℓ ω u = BhE P ℓ (fun v => extR P (ω v)) u := by
  intro u
  induction u with
  | zero => rfl
  | succ u ih =>
    have hs := sB_eq P ℓ ω u
    simp only [Bh, BhE, extR, bAct] at ih hs ⊢
    rw [ih, hs]
    cases isB P (ω u).1 <;> rfl

theorem rhD_eq (ω : ℕ → RC P) : rhD P ℓ ω = rhXR P ℓ (fun v => extR P (ω v)) := by
  funext u x h
  simp only [rhD, rhXR, Bh_eq]

/-- Blockwise slot permutations act on round coins by permuting slot kinds. -/
def permR (τ : (j : Fin P.D) → Equiv.Perm (Fin (P.sl j))) : Equiv.Perm (RC P) :=
  Equiv.prodCongr (Equiv.optionCongr (permRT P.sl τ)) (Equiv.refl _)

/-- The action is compatible with the slot part, the external part and P0194's weights. -/
def permActR : PermAct P.sl 1 (zOfR P) (extR P) (wR P) where
  act := permR P
  zOf_act := by
    intro τ rc
    rcases rc with ⟨_ | r, rest⟩
    · rfl
    · rfl
  ext_act := by
    intro τ rc
    rcases rc with ⟨_ | r, rest⟩
    · rfl
    · rfl
  μ_act := by
    intro τ rc
    rcases rc with ⟨_ | _ | ⟨j, k⟩, rest⟩
    · rfl
    · rfl
    · rfl

/-- A finite coin prefix extended by a default coin. -/
def extω {NE : ℕ} (rc0 : RC P) (yy : Fin NE → RC P) : ℕ → RC P := fun u => if h : u < NE then yy ⟨u, h⟩ else rc0

variable (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- **Bridge.** On a coin prefix `yy` of length `NE` (extended by any coin), `dzRun` with P0194's rule and slot coins
is, up to unit `NE`, the run with the rule `rhXR` of the prefix's external history and the slot coins `zE` of the
prefix; for `lay = P.lay` the left side is P0194's `pool`. -/
theorem dzRun_eq {NE : ℕ} (rc0 : RC P) (yy : Fin NE → RC P)
    (lay : (j : Fin P.D) → Finset ι → Fin (P.sl j) → Option ι) (u : ℕ) (hu : u ≤ NE) :
    dzRun P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ (extω P rc0 yy)) P.E P.thr0 P.θ P.R P.K P.Bt P.lev lay
        (zc P (extω P rc0 yy)) ωs φ u =
      dzRun P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) P.E P.thr0 P.θ P.R P.K P.Bt P.lev lay
        (zE P.sl 1 (zOfR P) yy) ωs φ u := by
  rw [dzRun_congr_z P.Lv P.sl 1 1 P.xr (ℓr P ℓ) _ P.E P.thr0 P.θ P.R P.K P.Bt P.lev ωs φ lay u
    (z' := zE P.sl 1 (zOfR P) yy) (fun v hv => by
      funext t
      simp only [zc, zE, extZ, extω, dif_pos (show v < NE by omega), zOfR])]
  refine dzRun_congr_rh P.Lv P.sl 1 1 P.xr (ℓr P ℓ) P.E P.thr0 P.θ P.R P.K P.Bt P.lev ωs φ lay _ u
    fun a' ha' => ?_
  rw [rhD_eq]
  exact causal_rhXR P ℓ _ _ a' fun v hv => by
    simp only [extE, extω, dif_pos (show v < NE by omega)]

theorem pool_eq {NE : ℕ} (rc0 : RC P) (yy : Fin NE → RC P) (u : ℕ) (hu : u ≤ NE) :
    pool P ℓ (extω P rc0 yy) ωs φ u =
      dzRun P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) P.E P.thr0 P.θ P.R P.K P.Bt P.lev P.lay
        (zE P.sl 1 (zOfR P) yy) ωs φ u :=
  dzRun_eq P ℓ ωs φ rc0 yy P.lay u hu

/-- **The identification used downstream.** If P0194's layout is the entry-order layout and its level schedule is
P0085's `levTh Ld`, P0194's pool on the extended prefix is, up to unit `NE`, the entry-order run (`sortLay`, schedule
`levTh Ld P.Bt`, prefix rule `rhXR`, prefix slot coins `zE`) that `count_bad_round`, `exp_walkRHS_round` and
`hrule_round` are about. For any other layout or schedule those theorems are about a different run. -/
theorem pool_eq_sort {Ld NE : ℕ} (hlay : P.lay = sortLay P.sl) (hlev : P.lev = Pool.P0085.levTh Ld P.Bt)
    (rc0 : RC P) (yy : Fin NE → RC P) (u : ℕ) (hu : u ≤ NE) :
    pool P ℓ (extω P rc0 yy) ωs φ u =
      dzRun P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) P.E P.thr0 P.θ P.R P.K P.Bt
        (Pool.P0085.levTh Ld P.Bt) (sortLay P.sl) (zE P.sl 1 (zOfR P) yy) ωs φ u := by
  rw [pool_eq P ℓ ωs φ rc0 yy u hu, hlay, hlev]


section Count

attribute [local instance] Pool.P0082.coinFintype

open Pool.P0082 Pool.P0048 Pool.P0065 Pool.P0156 Pool.P0185

theorem ℓr_mem (u : ℕ) (x : ι) : 0 ≤ ℓr P ℓ u x ∧ ℓr P ℓ u x ≤ 1 := by
  unfold ℓr; cases ℓ u (P.arm x) <;> simp

open Classical in
/-- **Bad walk points of P0194's round-level process, closed form** (P0185's `count_bad_DZ_closed` for P0194's rule
(b″), which reads B̂). Over P0091's sampling/filter coin law `pC ps q` and `NE` independent round coins with P0194's
weights `wR` (a law under `ParD.IsLaw`), the expected number of grid opportunities whose comparator copy is not
sampled and, forced into its own copy-last-within-thread run (rule and slot coins of the same round coins), is never
evicted before `NE` is at most `D·Lv·S/(ps(1−q)^{K·D(2Ld+NE/2^Ld+1)}) + D·NE·(NE·D·δs + NE·D·(Lt+1)·K·delta)`
with `S = s0 + D·Lv·S' + 1`. The counted runs use the copy-last layout (`lastLay`) and the schedule `levTh Ld P.Bt`,
with the prefix rule `rhXR` and prefix slot coins; they correspond to P0194's process only when `P.lay = sortLay P.sl`
and `P.lev = levTh Ld P.Bt` (then `pool_eq_sort` identifies P0194's pool with the matching entry-order run, and
`dzRun_eq` the rule and slot coins with P0194's `rhD` and `zc`, up to unit `NE`). -/
theorem count_bad_round (hL : P.IsLaw) (hN : 0 < P.N) (hB : Pool.P0065.BtHyp P.D P.Bt) {Ld NE Lt : ℕ}
    (hLv2 : Ld + 2 ≤ P.Lv) (hLt : Ld ≤ Lt)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ P.D - 1 → P.Bt j ∣ a → a < NE → P.E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ P.D - 1 → P.Bt j ∣ a → a < NE → P.thr0 (cstar j a) = j)
    {ps q : ℝ} (hps0 : 0 < ps) (hps1 : ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hEm : Monotone P.E) {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ P.xr j) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hR : 1 ≤ P.R) (hT : 1 / xmin * NE ≤ 2 ^ (P.R - 1) * P.θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * P.R ≤ M0)
    (hk : 4 * P.R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * P.R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < P.D →
      ∑ F ∈ (Finset.univ.filter fun c => P.E c = a ∧ P.thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => P.E c = a ∧ P.thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S') (hρS : (1 - 1 / (4 * P.R : ℝ)) ^ P.K * ((S' : ℝ) + (s0 + P.D * P.Lv * S')) ≤ S')
    (hsl : ∀ j, (P.D : ℝ) * ((s0 + P.D * P.Lv * S') + (P.Lv - 1 : ℕ) * S') + P.D * s0 + 1 ≤ P.sl j) :
    ∑ ω, wtv (Pool.P0091.pC (NE := NE) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω *
      ∑ yy : Fin NE → RC P, Pool.P0070.wR (wR P) yy *
      (#{ja : Fin P.D × Fin NE | P.Bt ja.1 ∣ ja.2 ∧ ωsC P.E NE P.D Lt P.K ω (cstar ja.1 ja.2) = false ∧
        evict P.E P.thr0 (gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt (Pool.P0085.levTh Ld P.Bt)
          (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (lastLay P.sl (cstar ja.1 ja.2))
            (zE P.sl 1 (zOfR P) yy)) ∅
          (forceS (ωsC P.E NE P.D Lt P.K ω) (cstar ja.1 ja.2)) (forceF P.K (φC NE P.D Lt P.K ω) (cstar ja.1 ja.2)))
          P.θ P.R P.K P.D P.Lv P.Bt (Pool.P0085.levTh Ld P.Bt) NE cstar (ωsC P.E NE P.D Lt P.K ω)
          (φC NE P.D Lt P.K ω) ja.1 ja.2 = none} : ℝ)
      ≤ (P.D * P.Lv * (s0 + P.D * P.Lv * S' + 1) : ℝ) /
          (ps * (1 - q) ^ (P.K * (P.D * (2 * Ld + NE / 2 ^ Ld + 1)))) +
        P.D * NE * (NE * P.D * δs + NE * P.D * (Lt + 1) * P.K * Pool.P0042.delta (Fintype.card ι) q P.R kk M0) := by
  have hB1 : ((1 : ℕ) : ℝ) / xmin = 1 / xmin := by norm_num
  exact count_bad_X_closed P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.sl 1 1 P.xr (ℓr P ℓ) (zOfR P) (extR P) none
    (rhXR P ℓ) (wR P) (causal_rhXR P ℓ) (permActR P) (wR_nonneg P hL) (sum_wR P hL hN) hB hLv2 hLt cstar hE hthr
    hps0 hps1 hq0 hq1 hEm hxmin hx (fun u x => (ℓr_mem P ℓ u x).1) (fun u x => (ℓr_mem P ℓ u x).2) zero_le_one
    (by rw [hB1]; exact hBm) hR (by rw [hB1]; exact hT) M0 kk hM0 hk hp s0 δs hs S' hM0S hρS hsl

end Count

end Pool.P0207
