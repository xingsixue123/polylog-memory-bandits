import Pool.P0225.Rho
import Pool.P0102.Learner
import Pool.P0134.Tools

/-!
# A self-rounding perturbation IS P0102's rounding error

For presence sets `pr` and natural grid losses `b` (real losses `b/G`), if the perturbation sequence `ρ` of P0089's
Hedge is self-rounding (`ρ t = selfRho ε (pw … t) (aw t) η (c t)`, P0225's rule) on learner times `< K ≤ 2^L`, then
it equals P0102's `rho` for the explicit integer run `stS` (with `η/G` and the integer losses `b`), and P0089's
weights equal P0102's integer machine weights `mw`.
-/

namespace Pool.P0230

open Real Finset Pool.P0019 Pool.P0089 Pool.P0102

section scale

variable {κ : Type} [Fintype κ]

/-- P0089's weights read `η` and the losses only through their products. -/
theorem pw_scale (q : κ → ℝ) {η η' : ℝ} (aw : ℕ → κ → Bool) {c c' : ℕ → κ → ℝ} (ρ : ℕ → ℝ)
    (h : ∀ t i, η * c t i = η' * c' t i) : ∀ t, pw q η aw c ρ t = pw q η' aw c' ρ t := by
  have he : ∀ t i, -η * c t i = -η' * c' t i := fun t i => by rw [neg_mul, neg_mul, h]
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    funext i
    simp only [pw, ih, expMass, he]

end scale

variable {κ : Type} [Fintype κ] [DecidableEq κ] (L : ℕ) (pr : ℕ → Finset κ) (b : ℕ → κ → ℕ) (G : ℕ) (η ε : ℝ)

/-- The real losses `b/G`. -/
noncomputable def cR (t : ℕ) (f : κ) : ℝ := (b t f : ℝ) / G

/-- P0102's explicit integer run with learning rate `η/G` and integer losses `b`. -/
noncomputable abbrev kLr (u : ℕ) : ℕ := (stS L pr b (η / G) ε u).1
noncomputable abbrev lwr (u : ℕ) : κ → ℕ → ℕ × ℕ := (stS L pr b (η / G) ε u).2

theorem scale_eq (hG : 0 < G) (t : ℕ) (i : Spec κ L) :
    η * specLoss (L := L) (cR b G) t i = η / G * cs L b t i := by
  simp only [specLoss, cR, cs]
  have : (G : ℝ) ≠ 0 := by exact_mod_cast hG.ne'
  field_simp

variable {L pr b G η ε}

/-- **A self-rounding perturbation is P0102's rounding error**, and P0089's weights are P0102's integer weights. -/
theorem selfRound_eq (hG : 0 < G)
    (hent : ∀ u, ∀ f ∈ pr (u + 1), f ∉ pr u → ∀ u' ≤ u, f ∉ pr u')
    (ρ : ℕ → ℝ) (K : ℕ) (hK : K ≤ 2 ^ L)
    (hρ : ∀ t < K, ρ t = Pool.P0225.selfRho ε (pw (fun _ => (1 : ℝ)) η (aw L pr) (specLoss (L := L) (cR b G)) ρ t)
      (aw L pr t) η (specLoss (L := L) (cR b G) t)) :
    ∀ t < K, ρ t = rho L pr b (η / G) ε (kLr L pr b G η ε) (lwr L pr b G η ε) t := by
  have hrec := rec_stS (L := L) (pr := pr) (b := b) (η := η / G) (ε := ε)
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    have htL : t < 2 ^ L := by omega
    -- the weights at `t` are P0102's
    have hw : pw (fun _ => (1 : ℝ)) η (aw L pr) (specLoss (L := L) (cR b G)) ρ t =
        pw (fun _ => (1 : ℝ)) (η / G) (aw L pr) (cs L b) (rho L pr b (η / G) ε (kLr L pr b G η ε) (lwr L pr b G η ε)) t := by
      rw [pw_scale _ (aw L pr) ρ (scale_eq L b G η hG) t]
      exact Pool.P0134.pw_congr _ _ t fun s hs => ⟨rfl, rfl, ih s hs (by omega)⟩
    have hmw := pw_eq_mw hrec hent t htL
    have hmass : awakeMass (pw (fun _ => (1 : ℝ)) η (aw L pr) (specLoss (L := L) (cR b G)) ρ t) (aw L pr t) =
        mA L pr (η / G) ε (kLr L pr b G η ε) (lwr L pr b G η ε) t := by
      rw [hw]
      unfold awakeMass mA
      rw [sum_awake htL]
      exact Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun ℓ' _ => hmw g hg ℓ'
    have hexp : expMass (pw (fun _ => (1 : ℝ)) η (aw L pr) (specLoss (L := L) (cR b G)) ρ t) (aw L pr t) η
        (specLoss (L := L) (cR b G) t) = mA' L pr b (η / G) ε (kLr L pr b G η ε) (lwr L pr b G η ε) t := by
      rw [hw]
      unfold expMass mA'
      rw [sum_awake htL]
      refine Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun ℓ' _ => ?_
      rw [hmw g hg ℓ', neg_mul, scale_eq L b G η hG, ← neg_mul]
      rfl
    rw [hρ t ht]
    unfold Pool.P0225.selfRho Pool.P0225.logFac rho inc
    rw [hmass, hexp]
    split_ifs with hne
    · rfl
    · have h0 : mA L pr (η / G) ε (kLr L pr b G η ε) (lwr L pr b G η ε) t = 0 := by
        unfold mA; rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.sum_empty]
      rw [h0, zero_div, log_zero, zero_div, Nat.floor_zero]; simp

/-- **P0089's weights with a self-rounding perturbation are P0102's integer machine weights**, at every learner time
`t ≤ K` (`t < 2^L`) and every present copy and level. -/
theorem selfRound_pw (hG : 0 < G)
    (hent : ∀ u, ∀ f ∈ pr (u + 1), f ∉ pr u → ∀ u' ≤ u, f ∉ pr u')
    (ρ : ℕ → ℝ) (K : ℕ) (hK : K ≤ 2 ^ L)
    (hρ : ∀ t < K, ρ t = Pool.P0225.selfRho ε (pw (fun _ => (1 : ℝ)) η (aw L pr) (specLoss (L := L) (cR b G)) ρ t)
      (aw L pr t) η (specLoss (L := L) (cR b G) t))
    (t : ℕ) (htK : t ≤ K) (htL : t < 2 ^ L) (f : κ) (hf : f ∈ pr t) (ℓ : Fin (L + 1)) :
    pw (fun _ => (1 : ℝ)) η (aw L pr) (specLoss (L := L) (cR b G)) ρ t (spc htL f ℓ) =
      mw (η / G) ε (kLr L pr b G η ε) (lwr L pr b G η ε) t f ℓ := by
  have hrec := rec_stS (L := L) (pr := pr) (b := b) (η := η / G) (ε := ε)
  rw [pw_scale _ (aw L pr) ρ (scale_eq L b G η hG) t,
    Pool.P0134.pw_congr _ _ t fun s hs => ⟨rfl, rfl, selfRound_eq hG hent ρ K hK hρ s (by omega)⟩]
  exact pw_eq_mw hrec hent t htL f hf ℓ

/-- P0102's explicit run at time `u` reads the presence sets and losses of times `< u` only. -/
theorem stS_congr {pr pr' : ℕ → Finset κ} {b b' : ℕ → κ → ℕ} (η ε : ℝ) :
    ∀ u, (∀ s < u, pr s = pr' s ∧ b s = b' s) → stS L pr b η ε u = stS L pr' b' η ε u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro h
    obtain ⟨h1, h2⟩ := h u (Nat.lt_succ_self u)
    have ih' := ih (fun s hs => h s (by omega))
    simp only [stS, stepS, inc, mA, mA', mw, ih', h1, h2]

/-- The awake mass of the self-rounding weights is P0102's `mA` (at `t ≤ K`). -/
theorem selfRound_awakeMass (hG : 0 < G)
    (hent : ∀ u, ∀ f ∈ pr (u + 1), f ∉ pr u → ∀ u' ≤ u, f ∉ pr u')
    (ρ : ℕ → ℝ) (K : ℕ) (hK : K ≤ 2 ^ L)
    (hρ : ∀ t < K, ρ t = Pool.P0225.selfRho ε (pw (fun _ => (1 : ℝ)) η (aw L pr) (specLoss (L := L) (cR b G)) ρ t)
      (aw L pr t) η (specLoss (L := L) (cR b G) t))
    (t : ℕ) (htK : t ≤ K) (htL : t < 2 ^ L) :
    awakeMass (pw (fun _ => (1 : ℝ)) η (aw L pr) (specLoss (L := L) (cR b G)) ρ t) (aw L pr t) =
      mA L pr (η / G) ε (kLr L pr b G η ε) (lwr L pr b G η ε) t := by
  unfold awakeMass mA
  rw [sum_awake htL]
  exact Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun ℓ' _ =>
    selfRound_pw hG hent ρ K hK hρ t htK htL g hg ℓ'

end Pool.P0230
