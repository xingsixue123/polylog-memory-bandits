import Pool.P0226.Run
import Pool.P0227.HTrue
import Pool.P0222.OccW

/-!
# P0186's `ActHyp` and per-run bound for P0194's process with P0212's ALG at the √(nT)-compatible scale
-/

namespace Pool.P0235

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0220 Pool.P0226

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (withAlg P η L N G γ wE ρr).K → ι → Bool) (T : ℕ)
  (rc0 : RC (withAlg P η L N G γ wE ρr))

local notation "QQ" => withAlg P η L N G γ wE ρr

/-- The positive part of P0227's slack, truncated after `T`. -/
noncomputable def slT (κ : ℝ) (u : ℕ) : ℝ :=
  if u < T then max (Pool.P0227.slack P η L N G γ wE ρr ℓ ωs φ rc0 κ ω u) 0 else 0

theorem slT_nonneg (κ : ℝ) (u : ℕ) : 0 ≤ slT P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u := by
  unfold slT; split_ifs
  · exact le_max_right _ _
  · exact le_rfl

/-- **Learner hypothesis with the slack added to both sides** (P0186's `hL`/`hLB` for `A := AR + slT`,
`V := (η/2)·VR + slT`). -/
theorem learner_sl (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) (hρr : ∀ σ V, |ρr σ V| ≤ δ) (hγ : 0 < γ) (hwE : 0 < wE)
    (hTL : T ≤ 2 ^ L) (κ : ℝ) (f : Option ι) (s s' : ℕ) (hss : s ≤ s')
    (hpres : ∀ u, s ≤ u → u < s' → u < T → gE P η L N G γ wE ρr ω u = true →
      presOf (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) f = true) :
    ∑ u ∈ Ico s s', (AR P η L N G γ wE ρr ℓ ω ωs φ T u + slT P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u) ≤
      ∑ u ∈ Ico s s', cuR P η L N G γ wE ρr ℓ ω ωs φ T u f + αT (ι := ι) η L T δ +
        ∑ u ∈ Ico s s', (η / 2 * VR P η L N G γ wE ρr ℓ ω ωs φ T u + slT P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u) :=
  Pool.P0227.shift_learner _ _ _ _
    (learner_all P η L N G γ wE ρr ℓ ω ωs φ T hη hδ hρr hγ hwE hTL f s s' hss hpres)

/-- **`htrue` on every interval with the constant `Ψ = Lc/κ`** (P0186's `htrue` for `A := AR + slT`), on P0227's
good event. -/
theorem htrue_sl {κ Lc : ℝ} (hκ : 0 < κ) (hLc : 0 ≤ Lc) (hTL : T ≤ 2 ^ L)
    (hgood : Pool.P0149.StepGood (Pool.P0227.DT P η L N G γ wE ρr ℓ ωs φ rc0 κ) (fun _ _ => true) (Lc / κ) T
      (Pool.P0203.pre _ ω T))
    (s s' : ℕ) (hss : s ≤ s') :
    ∑ u ∈ Ico s s', aPt P η L N G γ wE ρr ℓ ω ωs φ T u ≤
      ∑ u ∈ Ico s s', (AR P η L N G γ wE ρr ℓ ω ωs φ T u + slT P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u) + Lc / κ := by
  rw [sum_trunc T _ (fun u hu => by unfold aPt; rw [if_neg (by omega)]) s s',
    sum_trunc T _ (fun u hu => by
      rw [AR_zero_ge P η L N G γ wE ρr ℓ ω ωs φ T hu]; unfold slT; rw [if_neg (by omega)]; simp) s s']
  have hΨ : 0 ≤ Lc / κ := div_nonneg hLc hκ.le
  by_cases hsm : s ≤ min s' T
  · have h := Pool.P0227.htrue_run P η L N G γ wE ρr ℓ ωs φ rc0 hTL ω hgood hsm (min_le_right _ _)
    have e1 : ∑ u ∈ Ico s (min s' T), aPt P η L N G γ wE ρr ℓ ω ωs φ T u =
        ∑ u ∈ Ico s (min s' T), aPol (withAlg P η L N G γ wE ρr) ℓ ωs φ ω u :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold aPt; rw [if_pos (by omega)]
    have e2 : ∑ u ∈ Ico s (min s' T), (AR P η L N G γ wE ρr ℓ ω ωs φ T u +
        Pool.P0227.slack P η L N G γ wE ρr ℓ ωs φ rc0 κ ω u) ≤
        ∑ u ∈ Ico s (min s' T), (AR P η L N G γ wE ρr ℓ ω ωs φ T u + slT P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u) :=
      Finset.sum_le_sum fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold slT; rw [if_pos (by omega)]
        linarith [le_max_left (Pool.P0227.slack P η L N G γ wE ρr ℓ ωs φ rc0 κ ω u) 0]
    rw [e1]; linarith
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp only [Finset.sum_empty, zero_add]
    exact hΨ

/-- **Slot lower tail on every interval with the occupancy width** (P0186's `hlo` with P0222's `Wocc`). -/
theorem lo_occ_all (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    {Ls xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (QQ).xr j)
    (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < (QQ).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((QQ).Bt (i - 1) : ℝ) ≤ ρ * (QQ).Bt i) (hx0 : 1 / Pool.P0191.xrN (QQ).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QQ).xr i ≤ max M (TT / (nn * (QQ).Bt i)))
    (hΘ : ∀ f, ((QQ).thr0 f : ℝ) ≤ Θ)
    (hgood : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (QQ) ℓ ωs φ rc0 f) (Pool.P0203.gateS (QQ) ℓ ωs φ rc0 f)
      (Pool.P0203.rS (QQ) f) (Pool.P0158.rmax1 (Pool.P0203.rS (QQ) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (QQ).Lv (QQ).sl (sp (QQ) ℓ ω ωs φ u))
    (f : ι) (s s' : ℕ) (hss : s ≤ s')
    (hP : Pool.P0186.PresAct (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
      (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (QQ) ℓ) (rhD (QQ) ℓ ω) (QQ).lay (zc (QQ) ω)) ∅ ωs φ
      f s s') :
    ∑ u ∈ Ico s s', ℓt P η L N G γ wE ρr ℓ T u f ≤
      ∑ u ∈ Ico s s', Pool.P0105.incrOf (Pool.P0208.dat (QQ) ℓ ω ωs φ) u f +
        Pool.P0222.Wocc Ls xmin M ρ nn TT Θ (s' - s) := by
  have hWm := Pool.P0222.Wocc_mono (xmin := xmin) (ρ := ρ) (nn := nn) (TT := TT) (Θ := Θ) hLs hM
  have hinc := incr_nonneg P η L N G γ wE ρr ℓ ω ωs φ hxm hxm1 hxr
  have hW0 : ∀ m, 0 ≤ Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m := fun m => by
    unfold Pool.P0222.Wocc; have := Real.sqrt_nonneg (Ls * ((m : ℝ) * M + Θ * (ρ * TT / nn))); positivity
  rw [sum_trunc T _ (fun u hu => by unfold ℓt; rw [if_neg (by omega)]) s s']
  have hmono : ∑ u ∈ Ico s (min s' T), Pool.P0105.incrOf (Pool.P0208.dat (QQ) ℓ ω ωs φ) u f ≤
      ∑ u ∈ Ico s s', Pool.P0105.incrOf (Pool.P0208.dat (QQ) ℓ ω ωs φ) u f :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right (min_le_left _ _)) fun u _ _ => hinc u f
  by_cases hsm : s ≤ min s' T
  · have hP' : Pool.P0186.PresAct (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
        (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (QQ) ℓ) (rhD (QQ) ℓ ω) (QQ).lay (zc (QQ) ω)) ∅ ωs φ
        f s (min s' T) :=
      ⟨fun u h1 h2 => hP.1 u h1 (by omega), fun u h1 h2 => hP.2 u h1 (by omega)⟩
    have h := Pool.P0222.hlo_occ (QQ) ℓ ω ωs φ hD hLv hlev rc0 hLs hxm hxm1 hxr hn hTT hM hρ0 hB hρ hx0 hx hΘ T hgood
      hfit f hsm (min_le_right _ _) hP'
    have e1 : ∑ u ∈ Ico s (min s' T), ℓt P η L N G γ wE ρr ℓ T u f =
        ∑ u ∈ Ico s (min s' T), ℓr (QQ) ℓ u f :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold ℓt; rw [if_pos (by omega)]
    have hW : Pool.P0222.Wocc Ls xmin M ρ nn TT Θ (min s' T - s) ≤ Pool.P0222.Wocc Ls xmin M ρ nn TT Θ (s' - s) :=
      hWm (by omega)
    rw [e1]
    linarith
  · rw [Finset.Ico_eq_empty_of_le (by omega)]
    simp only [Finset.sum_empty]
    exact add_nonneg (Finset.sum_nonneg fun u _ => hinc u f) (hW0 _)


/-- **P0186's `ActHyp` for P0194's process with P0212's ALG, √(nT)-compatible constants.** As P0226's `actHyp_alg`,
except: the learner's loss and variance budget carry P0227's slack (`A := AR + slT`, `V := (η/2)·VR + slT`, so `htrue`
holds with the DETERMINISTIC constant `Ψ = Lt/κ` on P0227's good event), and the slot width is P0222's thread-aware
`Wocc` instead of the rate-floor width. -/
theorem actHyp_occ (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    (hL : (QQ).IsLaw) (hN : 0 < (QQ).N) (hη : 0 < η) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρr : ∀ σ V, |ρr σ V| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (QQ).cB)
    {Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (QQ).xr j)
    (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hBt : ∀ i, 0 < (QQ).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((QQ).Bt (i - 1) : ℝ) ≤ ρ * (QQ).Bt i) (hx0 : 1 / Pool.P0191.xrN (QQ).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QQ).xr i ≤ max M (TT / (nn * (QQ).Bt i)))
    (hΘ : ∀ f, ((QQ).thr0 f : ℝ) ≤ Θ)
    (hS : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (QQ) ℓ ωs φ rc0 f) (Pool.P0203.gateS (QQ) ℓ ωs φ rc0 f)
      (Pool.P0203.rS (QQ) f) (Pool.P0158.rmax1 (Pool.P0203.rS (QQ) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (QQ).Lv (QQ).sl (sp (QQ) ℓ ω ωs φ u))
    (hB : Pool.P0158.GoodV (Pool.P0216.DB (QQ) ℓ rc0) (fun _ _ => true)
      (fun _ => (QQ).cB) (Pool.P0158.rmax1 (fun _ => (QQ).cB)) Lb T (Pool.P0203.pre _ ω T))
    (hX : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (QQ) hL hN) (lossX P η L N G γ wE ρr ℓ x)
      (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (hXm : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (QQ) hL hN)
      (YB P η L N G γ wE ρr ℓ rc0) (bPolX P η L N G γ wE ρr ℓ rc0) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (hA : Pool.P0149.StepGood (Pool.P0227.DT P η L N G γ wE ρr ℓ ωs φ rc0 κ) (fun _ _ => true) (Lt / κ) T
      (Pool.P0203.pre _ ω T)) :
    Pool.P0186.ActHyp (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
      (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (QQ) ℓ) (rhD (QQ) ℓ ω) (QQ).lay (zc (QQ) ω)) ∅ ωs φ
      (ℓt P η L N G γ wE ρr ℓ T) (fun u x => cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some x))
      (fun u => AR P η L N G γ wE ρr ℓ ω ωs φ T u + slT P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u)
      (aPt P η L N G γ wE ρr ℓ ω ωs φ T)
      (fun u => η / 2 * VR P η L N G γ wE ρr ℓ ω ωs φ T u + slT P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u)
      (fun u => cuR P η L N G γ wE ρr ℓ ω ωs φ T u none)
      (bPt P η L N G γ wE ρr ℓ ω T) (bPt P η L N G γ wE ρr ℓ ω T) (Pool.P0216.incBD (QQ) ℓ ω)
      (αT (ι := ι) η L T δ) (Lc / (2 * (wE * γ))) (Lt / κ)
      (Pool.P0222.Wocc Ls xmin M ρ nn TT Θ) (fun _ => 0)
      (fun m : ℕ => Pool.P0158.widV (m * (QQ).cB) (max 1 (QQ).cB) Lb) where
  hL := fun f s s' hss hP => by
    have hact := (Pool.P0208.presAct_iff (QQ) ℓ ω ωs φ hD hLv hlev f s s').1 hP
    exact learner_sl P η L N G γ wE ρr ℓ ω ωs φ T rc0 hη hδ hρr hγ hwE0 hTL κ (some f) s s' hss
      (fun u h1 h2 _ _ => by simp [presOf, hact u h1 h2])
  hIX := fun f s s' hss hP => by
    have hact := (Pool.P0208.presAct_iff (QQ) ℓ ω ωs φ hD hLv hlev f s s').1 hP
    exact ix_all P η L N G γ wE ρr ℓ ω ωs φ T rc0 hL hN hγ hwE0 hwE hTL hLc hX f s s' hss hact
  hlo := fun f s s' hss hP =>
    lo_occ_all P η L N G γ wE ρr ℓ ω ωs φ T rc0 hD hLv hlev hLs hxm hxm1 hxr hn hTT hM hρ0 hBt hρ hx0 hx hΘ hS hfit
      f s s' hss hP
  hLB := fun s s' hss =>
    learner_sl P η L N G γ wE ρr ℓ ω ωs φ T rc0 hη hδ hρr hγ hwE0 hTL κ none s s' hss (fun _ _ _ _ _ => rfl)
  hIXB := fun s s' hss => ixm_all P η L N G γ wE ρr ℓ ω ωs φ T rc0 hL hN hγ hwE0 hwE hTL hLc hXm s s' hss
  hDr := fun s s' _ => by simp
  hBh := fun s s' hss => bh_all P η L N G γ wE ρr ℓ ω T rc0 hcB0 hLb hB s s' hss
  htrue := fun s s' hss => htrue_sl P η L N G γ wE ρr ℓ ω ωs φ T rc0 hκ hLt hTL hA s s' hss
  hfake := fun f u hf => by
    rw [Pool.P0207.dz_incr_retired (hf := hf)]
    unfold bPt; split_ifs
    · exact (Pool.P0216.bPol_mem (QQ) ℓ ω u).2
    · exact zero_le_one
  haux := fun u => Pool.P0215.aux_succ (QQ) ℓ ω ωs φ u


/-- **Per-run ALG-term bound for P0194's process with P0212's ALG, with `Wocc` and `Ψ = Lt/κ`** (P0186's
`run_bound_mix` applied to this file's `actHyp_occ`). HYPOTHESES (not discharged here): the good events of
`actHyp_occ` (P0203's slot event `hS`, P0216's B̂ event `hB`, P0220's IX events `hX`, `hXm`, P0227's `DT` event `hA`),
no overflow (`hfit`), P0218's forced-run events and no overflow for unsampled comparator copies (`hgF`, `hfF`), the
entry-order layout, comparator copies of arm `i` on the grid, the rule's margins dominating P0186's `Λ'`, and P0186's
shape conditions on `f a c w Λ'`. Conclusion:
`Σ_{u<T}(aPol − ℓ_u(i) − ((η/2)·VR + slT)) ≤ T·a 0 + Σ_{1≤j<D} Bt(j−1)·nBad(j−1)·a j + nBad(D−1)·c`.
The left side subtracts the slack `slT` (moved into `V`); bounding `Σ_{u<T} slT` (e.g. by P0227's `slack_le` per
round) is a separate step, not done here. -/
theorem run_bound_occ (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N) (hη : 0 < η) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρr : ∀ σ V, |ρr σ V| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (withAlg P η L N G γ wE ρr).cB)
    {Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (withAlg P η L N G γ wE ρr).xr j)
    (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hBt0 : ∀ i, 0 < (QQ).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((QQ).Bt (i - 1) : ℝ) ≤ ρ * (QQ).Bt i) (hx0 : 1 / Pool.P0191.xrN (QQ).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QQ).xr i ≤ max M (TT / (nn * (QQ).Bt i)))
    (hΘ : ∀ f, ((QQ).thr0 f : ℝ) ≤ Θ)
    (hlay : (withAlg P η L N G γ wE ρr).lay = Pool.P0176.sortLay (withAlg P η L N G γ wE ρr).sl)
    (hS : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (withAlg P η L N G γ wE ρr) ℓ ωs φ rc0 f)
      (Pool.P0203.gateS (withAlg P η L N G γ wE ρr) ℓ ωs φ rc0 f) (Pool.P0203.rS (withAlg P η L N G γ wE ρr) f)
      (Pool.P0158.rmax1 (Pool.P0203.rS (withAlg P η L N G γ wE ρr) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl
      (sp (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u))
    (hB : Pool.P0158.GoodV (Pool.P0216.DB (withAlg P η L N G γ wE ρr) ℓ rc0) (fun _ _ => true)
      (fun _ => (withAlg P η L N G γ wE ρr).cB) (Pool.P0158.rmax1 (fun _ => (withAlg P η L N G γ wE ρr).cB)) Lb T
      (Pool.P0203.pre _ ω T))
    (hX : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (lossX P η L N G γ wE ρr ℓ x)
      (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (hXm : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
      (YB P η L N G γ wE ρr ℓ rc0) (bPolX P η L N G γ wE ρr ℓ rc0) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (hA : Pool.P0149.StepGood (Pool.P0227.DT P η L N G γ wE ρr ℓ ωs φ rc0 κ) (fun _ _ => true) (Lt / κ) T
      (Pool.P0203.pre _ ω T))
    (hθ : 0 ≤ (QQ).θ) (hR1 : 1 ≤ (QQ).R) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hT : (QQ).Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    (i : Fin n) (harm : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).arm (cstar j a) = i)
    (hgF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false →
      Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (withAlg P η L N G γ wE ρr).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.gateS (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (withAlg P η L N G γ wE ρr).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.rS (withAlg P η L N G γ wE ρr) (cstar j a))
        (Pool.P0158.rmax1 (Pool.P0203.rS (withAlg P η L N G γ wE ρr) (cstar j a))) Ls T
        (Pool.P0203.pre (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ω T))
    (hfF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false → ∀ u, u < T →
      Pool.P0176.Fits (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl
        (sp (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ℓ ω (Pool.P0065.forceS ωs (cstar j a))
          (Pool.P0065.forceF (withAlg P η L N G γ wE ρr).K φ (cstar j a)) u))
    (Λ' : ℕ → ℕ → ℝ) (hΛ' : ∀ c u, Λ' (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤
      (QQ).Λ c u)
    (ff aa : ℕ → ℝ) (cc : ℝ) (w : ℕ → ℝ) (ha : ∀ j < (QQ).D, 0 ≤ aa j) (hc0 : 0 ≤ cc)
    (hbig : ∀ j < (QQ).D, ∀ m : ℕ, (QQ).Bt j ≤ m → ff m ≤ m * aa j)
    (hsmall : ∀ m : ℕ, m < (QQ).Bt ((QQ).D - 1) → ff m ≤ cc)
    (hf : ∀ m : ℕ, (QQ).θ + (QQ).R * (2 * αT (ι := ι) η L T δ + 2 * (Lc / (2 * (wE * γ))) +
        Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m) + Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m + Lt / κ ≤ ff m)
    (hfB : (1 : ℝ) * (QQ).Bt ((QQ).D - 1) ≤ ff ((QQ).Bt ((QQ).D - 1)))
    (hΛ : ∀ j (m : ℕ), Lt / κ + αT (ι := ι) η L T δ + Lc / (2 * (wE * γ)) + 0 +
        Pool.P0158.widV (m * (withAlg P η L N G γ wE ρr).cB) (max 1 (withAlg P η L N G γ wE ρr).cB) Lb +
        Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m + w j ≤ Λ' j m)
    (hw : ∀ i < (QQ).D, ∑ j ∈ Finset.Ico 1 (QQ).D, (if i ≤ j - 1 then ((QQ).Bt (j - 1) : ℝ) * aa j else 0) +
      (if i ≤ (QQ).D - 1 then cc else 0) ≤ w i) :
    ∑ u ∈ Finset.range T, (aPt P η L N G γ wE ρr ℓ ω ωs φ T u - gT ℓ T i u -
        (η / 2 * VR P η L N G γ wE ρr ℓ ω ωs φ T u + slT P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u)) ≤
      T * aa 0 + ∑ j ∈ Finset.Ico 1 (QQ).D, ((QQ).Bt (j - 1) : ℝ) *
          (Pool.P0135.nBadB T (QQ).Bt (fun τ r => Pool.P0186.outMix (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
            (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (QQ).lay (zc (withAlg P η L N G γ wE ρr) ω)) ∅
            (fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (Pool.P0176.lastLay (QQ).sl c') (zc (withAlg P η L N G γ wE ρr) ω))
            (fun _ => ∅) ((QQ).D - 1) T ωs φ (cstar r τ)) (j - 1) : ℝ) * aa j +
        (Pool.P0135.nBadB T (QQ).Bt (fun τ r => Pool.P0186.outMix (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
            (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (QQ).lay (zc (withAlg P η L N G γ wE ρr) ω)) ∅
            (fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (Pool.P0176.lastLay (QQ).sl c') (zc (withAlg P η L N G γ wE ρr) ω))
            (fun _ => ∅) ((QQ).D - 1) T ωs φ (cstar r τ)) ((QQ).D - 1) : ℝ) * cc := by
  have H := actHyp_occ P η L N G γ wE ρr ℓ ω ωs φ T rc0 hD hLv hlev hL hN hη hδ hρr hγ hwE0 hwE hTL hcB0 hLs hLb
    hLc hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hS hfit hB hX hXm hA
  have hWm := Pool.P0222.Wocc_mono (xmin := xmin) (ρ := ρ) (nn := nn) (TT := TT) (Θ := Θ) hLs hM
  have hW0 : ∀ m, 0 ≤ Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m := fun m => by
    unfold Pool.P0222.Wocc; have := Real.sqrt_nonneg (Ls * ((m : ℝ) * M + Θ * (ρ * TT / nn))); positivity
  refine Pool.P0186.run_bound_mix (U := fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr
      (ℓr (withAlg P η L N G γ wE ρr) ℓ) (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (Pool.P0176.lastLay (QQ).sl c')
      (zc (withAlg P η L N G γ wE ρr) ω)) (A0 := fun _ => ∅) (Bep := 1) hBt hLv hlev hT cstar hE hthr ?hcoup
    (ℓt P η L N G γ wE ρr ℓ T) (fun u x => cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some x)) (gT ℓ T i) ?hg
    _ _ _ _ _ _ _ _ _ _ Λ' (αT_nonneg (ι := ι) η L T hη hδ) (div_nonneg hLc (by positivity)) hW0 hWm ?hθ ?hR1 H
    ?hup ?hrule ?hBep ff aa cc w ha hc0 hbig hsmall hf hfB hΛ hw
  case hcoup =>
    intro j a hj hdv haT hc
    have := Pool.P0197.coup_dz (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
      (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).Bt (QQ).lev (zc (withAlg P η L N G γ wE ρr) ω) hc φ
    rw [hlay]
    exact this
  case hg =>
    intro j a u hj hdv haT
    unfold ℓt gT ℓr
    rw [show (withAlg P η L N G γ wE ρr).arm (cstar j a) = i from harm j a hj hdv haT]
  case hθ => exact hθ
  case hR1 => exact hR1
  case hBep =>
    intro u
    have h1 : aPt P η L N G γ wE ρr ℓ ω ωs φ T u ≤ 1 := by
      unfold aPt; split_ifs
      · exact aPol_le_one P η L N G γ wE ρr ℓ ω ωs φ u
      · exact zero_le_one
    have h2 : 0 ≤ gT ℓ T i u := by unfold gT; split_ifs <;> positivity
    have h3 : 0 ≤ η / 2 * VR P η L N G γ wE ρr ℓ ω ωs φ T u :=
      mul_nonneg (by positivity) (VR_nonneg P η L N G γ wE ρr ℓ ω ωs φ T u)
    have h4 := slT_nonneg P η L N G γ wE ρr ℓ ω ωs φ T rc0 κ u
    linarith
  case hup =>
    intro j a hj hdv haT e hae heT hnr
    have hEa := hE j a hj hdv haT
    have h := Pool.P0222.hup_occ (withAlg P η L N G γ wE ρr) ℓ ω ωs φ hD hLv hlev rc0 (cstar j a) hLs hxm hxm1 hxr
      hn hTT hM hρ0 hBt0 hρ hx0 hx (hΘ (cstar j a)) T
      (fun _ => hS (cstar j a)) (fun hs u hu => hfit u hu) (hgF j a hj hdv haT) (hfF j a hj hdv haT) e (by omega) heT
      (by rw [hEa]; exact hnr)
    rw [hEa] at h
    have e1 : ∑ u ∈ Ico a e, ℓr (withAlg P η L N G γ wE ρr) ℓ u (cstar j a) =
        ∑ u ∈ Ico a e, ℓt P η L N G γ wE ρr ℓ T u (cstar j a) :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold ℓt; rw [if_pos (by omega)]
    rw [e1] at h
    exact h
  case hrule =>
    intro j a hj hdv haT e hret
    have hEa := hE j a hj hdv haT
    have h := Pool.P0207.dz_hrule (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ) (QQ).E (QQ).thr0
      (QQ).θ (QQ).R (QQ).K (QQ).Bt (QQ).lev (zc (withAlg P η L N G γ wE ρr) ω) (QQ).Bmin (QQ).Λ
      (Bh (withAlg P η L N G γ wE ρr) ℓ ω) hD hLv hlev T ωs φ Λ' hΛ' (cstar j a) e (by rw [← hlay]; exact hret)
    rw [← hlay, hEa] at h
    have e1 : ∑ u ∈ Ico a e, (Bh (withAlg P η L N G γ wE ρr) ℓ ω (u + 1) - Bh (withAlg P η L N G γ wE ρr) ℓ ω u) =
        ∑ u ∈ Ico a e, Pool.P0216.incBD (withAlg P η L N G γ wE ρr) ℓ ω u :=
      Finset.sum_congr rfl fun u _ => by
        rw [Pool.P0216.Bh_sum (withAlg P η L N G γ wE ρr) ℓ ω u (u + 1) (Nat.le_succ u)]
        simp
    rw [e1] at h
    exact h

end Pool.P0235
