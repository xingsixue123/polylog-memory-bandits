import Pool.P0194.Proc

/-!
# Swapping the ALG of P0194's process: a simulation lemma

Two parameter sets that differ only in the ALG fields (`σA`, `sA0`, `draw`, `updA`, `draw_mem`) run the same pool.
If a relation between the two ALG states holds at the start, makes the draws agree and is preserved by the updates
whenever a predicate `Good` holds at the round, then along every run on which `Good` holds before `T` the two ALGs
stay related, and their choices, plays and policy losses agree before `T`.
-/

namespace Pool.P0236

open Finset Pool.P0194 Pool.P0001

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]

/-- `P` with another ALG (same draw grid `P.N`). -/
def swapA (P : ParD n ι) (σ2 : Type) (s2 : σ2) (dr : σ2 → Finset ι → Fin P.N → Option ι)
    (up : σ2 → Finset ι → Fin P.N → Option ι → Bool → σ2) (hm : ∀ σ V d x, dr σ V d = some x → x ∈ V) :
    ParD n ι :=
  { P with σA := σ2, sA0 := s2, draw := dr, updA := up, draw_mem := hm }

variable (P : ParD n ι) {σ2 : Type} {s2 : σ2} {dr : σ2 → Finset ι → Fin P.N → Option ι}
  {up : σ2 → Finset ι → Fin P.N → Option ι → Bool → σ2} {hm : ∀ σ V d x, dr σ V d = some x → x ∈ V}
  (ℓ : LossSeq n) (ω : ℕ → RC P) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

theorem sB_swap (u : ℕ) : sB (swapA P σ2 s2 dr up hm) ℓ ω u = sB P ℓ ω u := by
  induction u with
  | zero => rfl
  | succ u ih => simp only [sB, ih]; rfl

theorem bAct_swap (u : ℕ) : bAct (swapA P σ2 s2 dr up hm) ℓ ω u = bAct P ℓ ω u := by
  unfold bAct; rw [sB_swap]; rfl

theorem Bh_swap (u : ℕ) : Bh (swapA P σ2 s2 dr up hm) ℓ ω u = Bh P ℓ ω u := by
  induction u with
  | zero => rfl
  | succ u ih => simp only [Bh, ih, bAct_swap]; rfl

theorem rhD_swap : rhD (swapA P σ2 s2 dr up hm) ℓ ω = rhD P ℓ ω := by
  funext u x h; simp only [rhD, Bh_swap]; rfl

theorem pool_swap (u : ℕ) : pool (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u = pool P ℓ ω ωs φ u := by
  unfold pool; rw [rhD_swap]; rfl

/-- The pool, hence the active set, does not depend on the ALG. -/
theorem active_swap (u : ℕ) : active (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u = active P ℓ ω ωs φ u := by
  unfold active sp; rw [pool_swap]; rfl

theorem armOf_swap (u : ℕ) (c : Option ι) : armOf (swapA P σ2 s2 dr up hm) ℓ ω u c = armOf P ℓ ω u c := by
  cases c with
  | none => exact bAct_swap P ℓ ω u
  | some x => rfl

theorem occAtS_swap (u : ℕ) (s : Σ j : Fin P.D, Fin (P.sl j)) :
    occAtS (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u s = occAtS P ℓ ω ωs φ u s := by
  unfold occAtS; rw [pool_swap]; unfold sp; rw [pool_swap]; rfl

variable {P} (R : P.σA → σ2 → Prop) (Good : P.σA → Finset ι → Prop)

/-- **Simulation.** -/
theorem sA_sim (h0 : R P.sA0 s2) (hd : ∀ σ τ V d, R σ τ → Good σ V → P.draw σ V d = dr τ V d)
    (hu : ∀ σ τ V d ch bit, R σ τ → Good σ V → R (P.updA σ V d ch bit) (up τ V d ch bit)) (T : ℕ)
    (hG : ∀ u < T, Good (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u)) :
    ∀ u ≤ T, R (sA P ℓ ω ωs φ u) (sA (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u) := by
  intro u hu'
  induction u with
  | zero => exact h0
  | succ u ih =>
    have hR := ih (by omega)
    have hg := hG u (by omega)
    have hE2 : isE (swapA P σ2 s2 dr up hm) (ω u).1 = isE P (ω u).1 := rfl
    simp only [sA, hE2]
    split_ifs with hE
    · have hdr := hd _ _ _ (ω u).2.1 hR hg
      have hdr' : (swapA P σ2 s2 dr up hm).draw (sA (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u)
          (active P ℓ ω ωs φ u) (ω u).2.1 = P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) (ω u).2.1 := hdr.symm
      show R (P.updA _ _ _ _ _) (up _ (active (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u) _ _ _)
      rw [active_swap, hdr', armOf_swap]
      exact hu _ _ _ _ _ _ hR hg
    · exact hR

/-- The ALG choices agree before `T`. -/
theorem algCh_sim (h0 : R P.sA0 s2) (hd : ∀ σ τ V d, R σ τ → Good σ V → P.draw σ V d = dr τ V d)
    (hu : ∀ σ τ V d ch bit, R σ τ → Good σ V → R (P.updA σ V d ch bit) (up τ V d ch bit)) (T : ℕ)
    (hG : ∀ u < T, Good (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u)) {u : ℕ} (hu' : u < T) :
    algCh (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u = algCh P ℓ ω ωs φ u := by
  show dr (sA (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u) (active (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u) (ω u).2.1 = _
  rw [active_swap]
  exact (hd _ _ _ _ (sA_sim (hm := hm) ℓ ω ωs φ R Good h0 hd hu T hG u hu'.le) (hG u hu')).symm

/-- The plays agree before `T`. -/
theorem play_sim (h0 : R P.sA0 s2) (hd : ∀ σ τ V d, R σ τ → Good σ V → P.draw σ V d = dr τ V d)
    (hu : ∀ σ τ V d ch bit, R σ τ → Good σ V → R (P.updA σ V d ch bit) (up τ V d ch bit)) (T : ℕ)
    (hG : ∀ u < T, Good (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u)) {u : ℕ} (hu' : u < T) :
    play (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u = play P ℓ ω ωs φ u := by
  have h := algCh_sim (hm := hm) ℓ ω ωs φ R Good h0 hd hu T hG hu'
  unfold play
  rcases (ω u).1 with _ | _ | s
  · exact bAct_swap P ℓ ω u
  · rw [h, armOf_swap]
  · show armOf (swapA P σ2 s2 dr up hm) ℓ ω u (occAtS (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u s) =
      armOf P ℓ ω u (occAtS P ℓ ω ωs φ u s)
    rw [occAtS_swap, armOf_swap]

/-- The ALG's policy losses agree before `T`. -/
theorem aPol_sim (h0 : R P.sA0 s2) (hd : ∀ σ τ V d, R σ τ → Good σ V → P.draw σ V d = dr τ V d)
    (hu : ∀ σ τ V d ch bit, R σ τ → Good σ V → R (P.updA σ V d ch bit) (up τ V d ch bit)) (T : ℕ)
    (hG : ∀ u < T, Good (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u)) {u : ℕ} (hu' : u < T) :
    aPol (swapA P σ2 s2 dr up hm) ℓ ωs φ ω u = aPol P ℓ ωs φ ω u := by
  have hR := sA_sim (hm := hm) ℓ ω ωs φ R Good h0 hd hu T hG u hu'.le
  unfold aPol
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [show (swapA P σ2 s2 dr up hm).draw (sA (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u)
      (active (swapA P σ2 s2 dr up hm) ℓ ω ωs φ u) d = P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) d from by
    rw [active_swap]; exact (hd _ _ _ d hR (hG u hu')).symm, sB_swap]
  rfl

end Pool.P0236
