import Pool.P0212.Proc
import Pool.P0212.Reindex

/-!
# The learner hypotheses (P0186's `hL`, `hLB`) for the concrete ALG of P0194's process, pathwise
-/

namespace Pool.P0212

open Finset Pool.P0089 Pool.P0194 Pool.P0001

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (withAlg P η L N G γ wE ρr).K → ι → Bool) (T : ℕ)

/-- Exploitation flags. -/
noncomputable def gE (u : ℕ) : Bool := isE (withAlg P η L N G γ wE ρr) (ω u).1

theorem kE_eq_cntF : kE P η L N G γ wE ρr ω = cntF (gE P η L N G γ wE ρr ω) := rfl

/-- The learner state at the horizon. -/
noncomputable abbrev SF : AState ι := sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ T

/-- Learner presence read from the horizon state (every expert counts as present after the last learner time). -/
noncomputable def prF (t : ℕ) (f : Option ι) : Bool :=
  if t < (SF P η L N G γ wE ρr ℓ ω ωs φ T).k then (SF P η L N G γ wE ρr ℓ ω ωs φ T).pr t f else true

/-- The learner's loss and second moment at learner time `t` (zero after the last learner time). -/
noncomputable def Ap (t : ℕ) : ℝ :=
  if t < (SF P η L N G γ wE ρr ℓ ω ωs φ T).k then
    palgLoss (fun _ => (1 : ℝ)) η (specAw (L := L) (fun t f => prF P η L N G γ wE ρr ℓ ω ωs φ T t f = true))
      (specLoss (L := L) (SF P η L N G γ wE ρr ℓ ω ωs φ T).c) (SF P η L N G γ wE ρr ℓ ω ωs φ T).ρ t
  else 0

noncomputable def Vp (t : ℕ) : ℝ :=
  if t < (SF P η L N G γ wE ρr ℓ ω ωs φ T).k then
    palgVar (fun _ => (1 : ℝ)) η (specAw (L := L) (fun t f => prF P η L N G γ wE ρr ℓ ω ωs φ T t f = true))
      (specLoss (L := L) (SF P η L N G γ wE ρr ℓ ω ωs φ T).c) (SF P η L N G γ wE ρr ℓ ω ωs φ T).ρ t
  else 0

/-- Real-time IX data of expert `f` (zero off exploitation rounds). -/
noncomputable def cuR (u : ℕ) (f : Option ι) : ℝ :=
  if gE P η L N G γ wE ρr ω u = true then (SF P η L N G γ wE ρr ℓ ω ωs φ T).c (kE P η L N G γ wE ρr ω u) f else 0

/-- Real-time learner loss and second moment (zero off exploitation rounds). -/
noncomputable def AR (u : ℕ) : ℝ :=
  if gE P η L N G γ wE ρr ω u = true then Ap P η L N G γ wE ρr ℓ ω ωs φ T (kE P η L N G γ wE ρr ω u) else 0

noncomputable def VR (u : ℕ) : ℝ :=
  if gE P η L N G γ wE ρr ω u = true then Vp P η L N G γ wE ρr ℓ ω ωs φ T (kE P η L N G γ wE ρr ω u) else 0

/-- **The learner hypothesis, pathwise** (P0138's variance form, in learner time, reindexed to real time): for every
expert `f` (a copy, or the meta-arm `none`) present at every exploitation round of `[s, s')`, with `s' ≤ T ≤ 2^L`,
`Σ_{[s,s')} AR ≤ Σ_{[s,s')} cuR f + (2L+1)(log|Spec| + 2δ·k_T)/η + (η/2)·Σ_{[s,s')} VR`. -/
theorem learner_hyp (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) (hρr : ∀ σ V, |ρr σ V| ≤ δ) (hγ : 0 < γ) (hwE : 0 < wE)
    (hTL : T ≤ 2 ^ L) (f : Option ι) (s s' : ℕ) (hss' : s ≤ s') (hs'T : s' ≤ T)
    (hpres : ∀ u, s ≤ u → u < s' → gE P η L N G γ wE ρr ω u = true →
      presOf (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) f = true) :
    ∑ u ∈ Ico s s', AR P η L N G γ wE ρr ℓ ω ωs φ T u ≤
      ∑ u ∈ Ico s s', cuR P η L N G γ wE ρr ℓ ω ωs φ T u f +
        (2 * L + 1) * (Real.log (Fintype.card (Spec (Option ι) L)) + 2 * δ * (SF P η L N G γ wE ρr ℓ ω ωs φ T).k) / η +
        η / 2 * ∑ u ∈ Ico s s', VR P η L N G γ wE ρr ℓ ω ωs φ T u := by
  set K := (SF P η L N G γ wE ρr ℓ ω ωs φ T).k with hK
  have hKT : K = kE P η L N G γ wE ρr ω T := sA_k P η L N G γ wE ρr ℓ ω ωs φ T
  have hKL : K ≤ 2 ^ L := by
    have : kE P η L N G γ wE ρr ω T ≤ T := by
      unfold kE; exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  have hc0 : ∀ t g, 0 ≤ (SF P η L N G γ wE ρr ℓ ω ωs φ T).c t g :=
    sA_c_nonneg P η L N G γ wE ρr ℓ ω ωs φ hγ hwE T
  have hρ : ∀ t, |(SF P η L N G γ wE ρr ℓ ω ωs φ T).ρ t| ≤ δ := sA_ρ_bound P η L N G γ wE ρr ℓ ω ωs φ hδ hρr T
  have hpresL : ∀ t, kE P η L N G γ wE ρr ω s ≤ t → t < kE P η L N G γ wE ρr ω s' →
      prF P η L N G γ wE ρr ℓ ω ωs φ T t f = true := by
    intro t h1 h2
    obtain ⟨u, hu1, hu2, hgu, hku0⟩ := exists_flag (gE P η L N G γ wE ρr ω) s' hss' t h1 h2
    have hku : kE P η L N G γ wE ρr ω u = t := hku0
    have hkuT : kE P η L N G γ wE ρr ω u < K := by
      rw [hKT]; exact cntF_lt_of_flag _ (by omega) hgu
    have hw := sA_written P η L N G γ wE ρr ℓ ω ωs φ hgu
    have hk_u : (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k = kE P η L N G γ wE ρr ω u := sA_k P η L N G γ wE ρr ℓ ω ωs φ u
    have hfz := (sA_frozen P η L N G γ wE ρr ℓ ω ωs φ (u + 1) T (by omega) (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k
      (by rw [hw.1]; exact Nat.lt_succ_self _)).2.1
    unfold prF
    rw [← hku, if_pos hkuT, ← hk_u]
    show (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ T).pr (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k f = true
    rw [hfz, hw.2.2.1]
    exact hpres u hu1 hu2 hgu
  have key := Pool.P0138.hedge_interval_hyp_var (ι₀ := Option ι) (L := L)
    (fun t g => prF P η L N G γ wE ρr ℓ ω ωs φ T t g = true) (SF P η L N G γ wE ρr ℓ ω ωs φ T).c hc0 hη hδ
    (SF P η L N G γ wE ρr ℓ ω ωs φ T).ρ hρ K hKL f _ _ (cntF_mono _ hss') hpresL
  simp only at key
  have h1 := sum_flag_reindex (gE P η L N G γ wE ρr ω) (Ap P η L N G γ wE ρr ℓ ω ωs φ T) s' hss'
  have h2 := sum_flag_reindex (gE P η L N G γ wE ρr ω)
    (fun t => (SF P η L N G γ wE ρr ℓ ω ωs φ T).c t f) s' hss'
  have h3 := sum_flag_reindex (gE P η L N G γ wE ρr ω) (Vp P η L N G γ wE ρr ℓ ω ωs φ T) s' hss'
  unfold AR cuR VR
  rw [kE_eq_cntF, h1, h2, h3]
  exact key

end Pool.P0212

namespace Pool.P0212

open Finset Pool.P0089 Pool.P0194 Pool.P0001

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (withAlg P η L N G γ wE ρr).K → ι → Bool) (T : ℕ)

/-- **The learner's play at an exploitation round is P0089's distribution on the horizon data at that learner time.** -/
theorem pprob_round {u : ℕ} (hu : u < T) (hg : gE P η L N G γ wE ρr ω u = true) :
    pprob (fun _ => (1 : ℝ)) η (specAw (L := L) (fun t f => prF P η L N G γ wE ρr ℓ ω ωs φ T t f = true))
      (specLoss (L := L) (SF P η L N G γ wE ρr ℓ ω ωs φ T).c) (SF P η L N G γ wE ρr ℓ ω ωs φ T).ρ
      (kE P η L N G γ wE ρr ω u) =
    pprob (fun _ => (1 : ℝ)) η
      (specAw (L := L) (prAt (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
        (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)))
      (specLoss (L := L) (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).c)
      (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).ρ (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k := by
  have hk_u : (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k = kE P η L N G γ wE ρr ω u :=
    sA_k P η L N G γ wE ρr ℓ ω ωs φ u
  have hw := sA_written P η L N G γ wE ρr ℓ ω ωs φ hg
  have hKT : (SF P η L N G γ wE ρr ℓ ω ωs φ T).k = kE P η L N G γ wE ρr ω T := sA_k P η L N G γ wE ρr ℓ ω ωs φ T
  have hlt : kE P η L N G γ wE ρr ω u < (SF P η L N G γ wE ρr ℓ ω ωs φ T).k := by
    rw [hKT]; exact cntF_lt_of_flag _ hu hg
  -- frozen data from `u` (times `< k_u`) and from `u + 1` (time `k_u`) to `T`
  have hfz0 := sA_frozen P η L N G γ wE ρr ℓ ω ωs φ u T hu.le
  have hfz1 := sA_frozen P η L N G γ wE ρr ℓ ω ωs φ (u + 1) T hu (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k
    (by rw [hw.1]; exact Nat.lt_succ_self _)
  rw [← hk_u]
  refine Pool.P0134.pprob_congr _ η _ (fun t ht => ⟨?_, ?_, ?_⟩) ?_
  · funext s
    simp only [specAw]
    congr 1
    simp only [prF, prAt, if_pos ht, show t < (SF P η L N G γ wE ρr ℓ ω ωs φ T).k by omega, if_true,
      (hfz0 t ht).2.1]
  · funext s
    simp only [specLoss, (hfz0 t ht).1]
  · exact (hfz0 t ht).2.2
  · funext s
    simp only [specAw]
    congr 1
    simp only [prF, prAt, lt_irrefl, if_false, show (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k <
      (SF P η L N G γ wE ρr ℓ ω ωs φ T).k by omega, if_true, hfz1.2.1, hw.2.2.1]

end Pool.P0212

namespace Pool.P0212

open Finset Pool.P0089 Pool.P0194 Pool.P0001

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (withAlg P η L N G γ wE ρr).K → ι → Bool) (T : ℕ)

/-- The IX data of an exploitation round are the IX estimates of that round's draw. -/
theorem cuR_eq {u : ℕ} (hu : u < T) (hg : gE P η L N G γ wE ρr ω u = true) (f : Option ι) :
    cuR P η L N G γ wE ρr ℓ ω ωs φ T u f =
      ixA η L N G γ wE (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
        (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
        (ℓ u (armOf (withAlg P η L N G γ wE ρr) ℓ ω u (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u))) f := by
  have hk_u : (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k = kE P η L N G γ wE ρr ω u :=
    sA_k P η L N G γ wE ρr ℓ ω ωs φ u
  have hw := sA_written P η L N G γ wE ρr ℓ ω ωs φ hg
  have hfz1 := sA_frozen P η L N G γ wE ρr ℓ ω ωs φ (u + 1) T hu (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u).k
    (by rw [hw.1]; exact Nat.lt_succ_self _)
  unfold cuR
  rw [if_pos hg, ← hk_u, hfz1.1, hw.2.1]

/-- Marginalizing P0089's specialists over the copy. -/
theorem sum_spec_marg (p : Spec (Option ι) L → ℝ) (g : Option ι → ℝ) :
    ∑ s, p s * g s.1 = ∑ f, (∑ s ∈ univ.filter (fun s : Spec (Option ι) L => s.1 = f), p s) * g f := by
  rw [← Finset.sum_fiberwise (s := univ) (g := fun s : Spec (Option ι) L => s.1)]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [Finset.mem_filter] at hs
  rw [hs.2]

/-- **The learner's loss at an exploitation round is its Hedge marginal (before P0179's rounding) against the
round's IX data.** ALG actually plays the rounded law `ptA`; the played-loss rounding term is not bounded here. -/
theorem AR_eq {u : ℕ} (hu : u < T) (hg : gE P η L N G γ wE ρr ω u = true) :
    AR P η L N G γ wE ρr ℓ ω ωs φ T u =
      ∑ f, pmarg η L (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) f *
        cuR P η L N G γ wE ρr ℓ ω ωs φ T u f := by
  have hKT : (SF P η L N G γ wE ρr ℓ ω ωs φ T).k = kE P η L N G γ wE ρr ω T := sA_k P η L N G γ wE ρr ℓ ω ωs φ T
  have hlt : kE P η L N G γ wE ρr ω u < (SF P η L N G γ wE ρr ℓ ω ωs φ T).k := by
    rw [hKT]; exact cntF_lt_of_flag _ hu hg
  unfold AR Ap palgLoss
  rw [if_pos hg, if_pos hlt, pprob_round P η L N G γ wE ρr ℓ ω ωs φ T hu hg]
  unfold specLoss pmarg
  rw [sum_spec_marg L]
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  unfold cuR
  rw [if_pos hg]

/-- Same for the second moment (Hedge marginal before rounding). -/
theorem VR_eq {u : ℕ} (hu : u < T) (hg : gE P η L N G γ wE ρr ω u = true) :
    VR P η L N G γ wE ρr ℓ ω ωs φ T u =
      ∑ f, pmarg η L (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) f *
        cuR P η L N G γ wE ρr ℓ ω ωs φ T u f ^ 2 := by
  have hKT : (SF P η L N G γ wE ρr ℓ ω ωs φ T).k = kE P η L N G γ wE ρr ω T := sA_k P η L N G γ wE ρr ℓ ω ωs φ T
  have hlt : kE P η L N G γ wE ρr ω u < (SF P η L N G γ wE ρr ℓ ω ωs φ T).k := by
    rw [hKT]; exact cntF_lt_of_flag _ hu hg
  unfold VR Vp palgVar
  rw [if_pos hg, if_pos hlt, pprob_round P η L N G γ wE ρr ℓ ω ωs φ T hu hg]
  unfold specLoss pmarg
  rw [sum_spec_marg L (g := fun f => (SF P η L N G γ wE ρr ℓ ω ωs φ T).c (kE P η L N G γ wE ρr ω u) f ^ 2)]
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  unfold cuR
  rw [if_pos hg]

end Pool.P0212
