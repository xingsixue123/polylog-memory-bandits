import Pool.P0194.Proc
import Pool.P0138.VarHyp
import Pool.P0134.Tools
import Pool.P0179.Round

/-!
# A concrete ALG for P0194's round-level process: the dyadic sleeping Hedge of P0089 in learner time

Experts are the copies (`some x`, awake while active) and BASE's meta-arm (`none`, always awake). The learner runs
P0089's normaliser-perturbed dyadic-specialist Hedge in its OWN time (the number of exploitation rounds so far), since
P0194's ALG is only updated on exploitation rounds. It draws from P0179's 1/N-rounding of its marginal distribution
(the missing mass on the meta-arm) and is fed IX estimates `bit/(wE·(p̃ + γ))` of the drawn expert.
-/

namespace Pool.P0212

open Finset Pool.P0089

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The learner state: learner time `k`, and the learner losses, presence flags and normaliser perturbations of the
learner times `< k`. -/
structure AState (ι : Type) where
  k : ℕ
  c : ℕ → Option ι → ℝ
  pr : ℕ → Option ι → Bool
  ρ : ℕ → ℝ

/-- Presence of the experts given the active set: the meta-arm is always present. -/
def presOf (V : Finset ι) : Option ι → Bool
  | none => true
  | some x => decide (x ∈ V)

/-- Presence at learner time `t` as seen from state `σ` with current active set `V`. -/
def prAt (σ : AState ι) (V : Finset ι) (t : ℕ) (f : Option ι) : Prop :=
  (if t < σ.k then σ.pr t f else presOf V f) = true

variable (η : ℝ) (L : ℕ)

/-- The learner's marginal distribution over experts at the current learner time. -/
noncomputable def pmarg (σ : AState ι) (V : Finset ι) (f : Option ι) : ℝ :=
  ∑ s ∈ univ.filter (fun s : Spec (Option ι) L => s.1 = f),
    pprob (fun _ => (1 : ℝ)) η (specAw (L := L) (prAt σ V)) (specLoss (L := L) σ.c) σ.ρ σ.k s

variable (N : ℕ)

/-- The rounded draw law (P0179, missing mass on the meta-arm). -/
noncomputable def ptA (σ : AState ι) (V : Finset ι) (f : Option ι) : ℝ :=
  Pool.P0179.pt N none (pmarg η L σ V) f

/-- The draw: P0179's coin realization of the rounded law (the meta-arm if the marginal is not a distribution). -/
noncomputable def drawA (σ : AState ι) (V : Finset ι) (d : Fin N) : Option ι :=
  open Classical in
  if h : (∀ f, 0 ≤ pmarg η L σ V f) ∧ ∑ f, pmarg η L σ V f = 1 then
    Pool.P0179.draw (N := N) (b := (none : Option ι)) h.1 h.2 d
  else none

variable (G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ)

/-- The IX estimate of expert `f` after drawing `ch` with loss bit `bit`, rounded down to the grid `1/G` (so that a
finite-state learner can store it). **Intended parameters:** `G ≥ 1` (with `G = 0` every estimate is `0`; for
`G ≥ 1` the rounding loses less than `1/G` per exploitation round, `ixA_grid`), and `wE` equal to the process's
exploitation weight (`P.wE` in `withAlg`), for which the unrounded estimate is unbiased; neither is enforced. -/
noncomputable def ixA (σ : AState ι) (V : Finset ι) (ch : Option ι) (bit : Bool) (f : Option ι) : ℝ :=
  if f = ch then (⌊(G : ℝ) * ((bit.toNat : ℝ) / (wE * (ptA η L N σ V f + γ)))⌋₊ : ℝ) / G else 0

/-- **Grid rounding error**: for `G ≥ 1` the drawn expert's estimate is within `1/G` below its unrounded IX value. -/
theorem ixA_grid (hG : 1 ≤ G) (σ : AState ι) (V : Finset ι) (ch : Option ι) (bit : Bool)
    (hden : 0 < wE * (ptA η L N σ V ch + γ)) :
    (bit.toNat : ℝ) / (wE * (ptA η L N σ V ch + γ)) - 1 / G ≤ ixA η L N G γ wE σ V ch bit ch ∧
      ixA η L N G γ wE σ V ch bit ch ≤ (bit.toNat : ℝ) / (wE * (ptA η L N σ V ch + γ)) := by
  unfold ixA
  rw [if_pos rfl]
  set x := (bit.toNat : ℝ) / (wE * (ptA η L N σ V ch + γ)) with hx
  have hx0 : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) hden.le
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  have h1 : (⌊(G : ℝ) * x⌋₊ : ℝ) ≤ G * x := Nat.floor_le (by positivity)
  have h2 : (G : ℝ) * x < ⌊(G : ℝ) * x⌋₊ + 1 := Nat.lt_floor_add_one _
  constructor
  · have h3 : x - 1 / G = (G * x - 1) / G := by field_simp
    rw [h3]
    exact div_le_div_of_nonneg_right (by linarith) hGr.le
  · rw [div_le_iff₀ hGr]; nlinarith

/-- The update on an exploitation round. -/
noncomputable def updA (σ : AState ι) (V : Finset ι) (_d : Fin N) (ch : Option ι) (bit : Bool) : AState ι :=
  { k := σ.k + 1
    c := Function.update σ.c σ.k (ixA η L N G γ wE σ V ch bit)
    pr := Function.update σ.pr σ.k (presOf V)
    ρ := Function.update σ.ρ σ.k (ρr σ V) }

/-- The initial state. -/
def s0A : AState ι := ⟨0, fun _ _ => 0, fun _ _ => true, fun _ => 0⟩

end Pool.P0212

namespace Pool.P0212

open Finset Pool.P0089

variable {ι : Type} [Fintype ι] [DecidableEq ι] (η : ℝ) (L N : ℕ)

theorem pmarg_eq_zero (σ : AState ι) (V : Finset ι) {x : ι} (hx : x ∉ V) : pmarg η L σ V (some x) = 0 := by
  unfold pmarg
  refine Finset.sum_eq_zero fun s hs => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  unfold pprob
  rw [if_neg]
  simp only [specAw, prAt, lt_irrefl, if_false, hs, presOf, decide_eq_true_eq, not_and]
  intro _ _ _ h
  exact hx h

/-- ALG draws only active members or the meta-arm. -/
theorem drawA_mem (σ : AState ι) (V : Finset ι) (d : Fin N) (x : ι) (h : drawA η L N σ V d = some x) : x ∈ V := by
  classical
  by_contra hx
  unfold drawA at h
  split_ifs at h with hp
  have hcard := Pool.P0179.card_draw_fiber (N := N) (b := (none : Option ι)) hp.1 hp.2 (some x)
  have hc0 : Pool.P0179.cnt N none (pmarg η L σ V) (some x) = 0 := by
    unfold Pool.P0179.cnt
    rw [if_neg (by simp), pmarg_eq_zero η L σ V hx, zero_mul, Nat.floor_zero]
  rw [hc0, Finset.card_eq_zero] at hcard
  have : d ∈ (univ.filter fun k : Fin N => Pool.P0179.draw (N := N) (b := (none : Option ι)) hp.1 hp.2 k = some x) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; convert h
  rw [hcard] at this
  simp at this

end Pool.P0212

namespace Pool.P0212

open Finset Pool.P0089

variable {ι : Type} [Fintype ι] [DecidableEq ι] (η : ℝ) (L N : ℕ)

theorem pmarg_nonneg (σ : AState ι) (V : Finset ι) (f : Option ι) : 0 ≤ pmarg η L σ V f :=
  Finset.sum_nonneg fun s _ => pprob_nonneg (fun _ => one_pos) _ s

/-- Before learner time `2^L` the marginal is a distribution (the meta-arm's level-0 specialist is awake). -/
theorem pmarg_sum (σ : AState ι) (V : Finset ι) (hk : σ.k < 2 ^ L) : ∑ f, pmarg η L σ V f = 1 := by
  classical
  unfold pmarg
  rw [Finset.sum_fiberwise (s := univ) (g := fun s : Spec (Option ι) L => s.1)
    (f := fun s => pprob (fun _ => (1 : ℝ)) η (specAw (L := L) (prAt σ V)) (specLoss (L := L) σ.c) σ.ρ σ.k s)]
  refine sum_pprob (fun _ => one_pos) σ.k (i := (none, (⟨0, by omega⟩, ⟨σ.k, hk⟩))) ?_
  simp [specAw, prAt, presOf]

/-- Before learner time `2^L` the draw is P0179's coin realization of the rounded marginal. -/
theorem drawA_eq (σ : AState ι) (V : Finset ι) (hk : σ.k < 2 ^ L) (d : Fin N) :
    drawA η L N σ V d = Pool.P0179.draw (N := N) (b := (none : Option ι)) (pmarg_nonneg η L σ V)
      (pmarg_sum η L σ V hk) d := by
  unfold drawA
  rw [dif_pos ⟨pmarg_nonneg η L σ V, pmarg_sum η L σ V hk⟩]

end Pool.P0212
