import Pool.P0052.PoolProcess

/-!
# Cover locality: merges read the cover data only between breakpoints (P0045 C7, part a)

P0030's chain cover `Covered E C t θ F j len` evaluates `Lint C f e₁ e₂ = C f e₂ − C f e₁` only for
members `f` of `F` or `f = j`, with `E f ≤ e₁`, and with `e₁, e₂` among the entry epochs of `F ∪ {j}` and `t`.
So P0052's process is determined by the interval losses `[e₁, e₂]` (`E c ≤ e₁ ≤ e₂`) of each merge input's
copies between that input's breakpoints (`pools_congr_bp`). Turning this into a finite-state machine with
`O(|pool|²)` stored numbers (maintaining the data as epochs pass and copies enter and leave) is NOT done here.

* `AgreeOn E C C' Q S`: `C` and `C'` give each copy of `Q` the same interval losses between points of `S`,
  from its entry on. `bp E t Q`: the breakpoints of `Q` (entry epochs of its copies, and `t`).
* `pieceSum_congr`, `covered_congr`: chain sums and covers agree.
* `filterRound_congr`, `mstep_congr`, `iter_congr`: one Filter round, one merge iteration (P0042 `mstep`) and
  `K` iterations from a pool `Q` agree whenever `C, C'` agree on `Q`'s breakpoints.
* `mergeUpTo_congr_bp`, `pools_congr_bp`: process-level breakpoint locality: agreement on the breakpoints of
  every merge input of the run gives the same sub-pools at every epoch.
* `pools_congr` (corollary: agreement on all intervals `E c ≤ e₁ ≤ e₂`) and `pools_sinceEntry` (the truncated
  "losses since entry" representation gives the same sub-pools).
-/

open Finset

namespace Pool.P0068

open Pool.P0030 Pool.P0034 Pool.P0042

variable {ι : Type*} [LinearOrder ι] (E : ι → ℕ) (t : ℕ) (θ : ℝ)

/-- `C` and `C'` give the same interval losses to every copy of `Q` between points of `S` that are
not before the copy's entry. -/
def AgreeOn (C C' : ι → ℕ → ℝ) (Q : Finset ι) (S : Set ℕ) : Prop :=
  ∀ f ∈ Q, ∀ e₁ ∈ S, ∀ e₂ ∈ S, E f ≤ e₁ → e₁ ≤ e₂ → Lint C f e₁ e₂ = Lint C' f e₁ e₂

/-- The breakpoints of a pool: entry epochs of its copies, and the current epoch `t`. -/
def bp (Q : Finset ι) : Set ℕ := {e | e = t ∨ ∃ g ∈ Q, E g = e}

variable {E t}

theorem AgreeOn.mono {C C' : ι → ℕ → ℝ} {Q Q' : Finset ι} {S : Set ℕ} (h : AgreeOn E C C' Q S)
    (hQ : Q' ⊆ Q) : AgreeOn E C C' Q' S := fun f hf => h f (hQ hf)

theorem AgreeOn.mono_set {C C' : ι → ℕ → ℝ} {Q : Finset ι} {S S' : Set ℕ} (h : AgreeOn E C C' Q S)
    (hS : S' ⊆ S) : AgreeOn E C C' Q S' :=
  fun f hf e₁ he₁ e₂ he₂ hle hle' => h f hf e₁ (hS he₁) e₂ (hS he₂) hle hle'

theorem bp_mono {Q Q' : Finset ι} (hQ : Q' ⊆ Q) : bp E t Q' ⊆ bp E t Q := by
  rintro e (h | ⟨g, hg, rfl⟩)
  · exact Or.inl h
  · exact Or.inr ⟨g, hQ hg, rfl⟩

theorem pieceSum_congr {C C' : ι → ℕ → ℝ} {F : Finset ι} {S : Set ℕ}
    (hS : ∀ g ∈ F, E g ∈ S) (htS : t ∈ S) (h : AgreeOn E C C' F S) :
    ∀ (ch : List ι) (a : ℕ), ChainOK E t ch a → a ∈ S → (∀ f ∈ ch, f ∈ F) →
      pieceSum E C t ch a = pieceSum E C' t ch a
  | [], _, hok, _, _ => by simp [pieceSum]
  | [f], a, hok, ha, hF => by
    simp only [pieceSum]
    exact h f (hF f (by simp)) a ha t htS hok.1 hok.2
  | f :: g :: rest, a, hok, ha, hF => by
    simp only [pieceSum]
    have hg : g ∈ F := hF g (by simp)
    rw [h f (hF f (by simp)) a ha (E g) (hS g hg) hok.1 hok.2.1,
      pieceSum_congr hS htS h (g :: rest) (E g) hok.2.2 (hS g hg) (fun x hx => hF x (by simp [hx]))]

/-- A valid chain starts no later than `t`. -/
theorem chainOK_le : ∀ (ch : List ι) (a : ℕ), ChainOK E t ch a → a ≤ t
  | [], _, hok => hok.elim
  | [_], _, hok => hok.2
  | _ :: g :: rest, _, hok => hok.2.1.trans (chainOK_le (g :: rest) (E g) hok.2.2)

/-- Covers read the cover data only between breakpoints. -/
theorem covered_congr {C C' : ι → ℕ → ℝ} {F : Finset ι} {j : ι} {len : ℕ} {S : Set ℕ}
    (hS : ∀ g ∈ F, E g ∈ S) (hjS : E j ∈ S) (htS : t ∈ S) (h : AgreeOn E C C' F S)
    (hj : E j ≤ t → Lint C j (E j) t = Lint C' j (E j) t) :
    Covered E C t θ F j len ↔ Covered E C' t θ F j len := by
  unfold Covered
  constructor
  · rintro ⟨ch, hlen, hF, hok, hle⟩
    refine ⟨ch, hlen, hF, hok, ?_⟩
    rw [← pieceSum_congr hS htS h ch (E j) hok hjS hF, ← hj (chainOK_le ch (E j) hok)]
    exact hle
  · rintro ⟨ch, hlen, hF, hok, hle⟩
    refine ⟨ch, hlen, hF, hok, ?_⟩
    rw [pieceSum_congr hS htS h ch (E j) hok hjS hF, hj (chainOK_le ch (E j) hok)]
    exact hle

/-- One Filter round reads the cover data only between the pool's breakpoints. -/
theorem filterRound_congr {C C' : ι → ℕ → ℝ} {Q F : Finset ι} {len : ℕ}
    (hF : F ⊆ Q) (h : AgreeOn E C C' Q (bp E t Q)) :
    filterRound E C t θ Q F len = filterRound E C' t θ Q F len := by
  classical
  unfold filterRound
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  rw [covered_congr θ (S := bp E t Q) (fun g hg => Or.inr ⟨g, hF hg, rfl⟩) (Or.inr ⟨j, hj, rfl⟩)
    (Or.inl rfl) (h.mono hF) (h j hj (E j) (Or.inr ⟨j, hj, rfl⟩) t (Or.inl rfl) le_rfl)]

variable [Fintype ι]

theorem mstep_congr {C C' : ι → ℕ → ℝ} (L : ℕ) {Q : Finset ι} (y : ι → Bool)
    (h : AgreeOn E C C' Q (bp E t Q)) : mstep E C t θ L Q y = mstep E C' t θ L Q y := by
  unfold mstep
  exact filterRound_congr θ (Finset.filter_subset _ _) h

/-- `K` merge iterations from the pool `Q` read the cover data only between `Q`'s breakpoints. -/
theorem iter_congr {C C' : ι → ℕ → ℝ} (L : ℕ) (Q : Finset ι) (h : AgreeOn E C C' Q (bp E t Q)) :
    ∀ (K : ℕ) (φ : Fin K → ι → Bool),
      iter (mstep E C t θ L) Q K φ = iter (mstep E C' t θ L) Q K φ
  | 0, _ => rfl
  | K + 1, φ => by
    simp only [iter]
    rw [iter_congr L Q h K (Fin.init φ)]
    have hsub : iter (mstep E C' t θ L) Q K (Fin.init φ) ⊆ Q :=
      iter_sub (mstep E C' t θ L) Q (fun Q' y => mstep_sub E C' t θ L Q' y) K _
    exact mstep_congr θ L _ ((h.mono hsub).mono_set (bp_mono hsub))

/-- One sweep of merges at the end of epoch `a` reads the cover data only through the breakpoints of each
merge's actual input (computed with `C`). -/
theorem mergeUpTo_congr_bp {C C' : ι → ℕ → ℝ} (R K : ℕ) (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ)
    (P : ℕ → Finset ι) : ∀ m : ℕ,
    (∀ m' ≤ m, AgreeOn E C C'
      (Pool.P0052.stage E C θ R K φ a P m' (m' + 1) ∪ Pool.P0052.stage E C θ R K φ a P m' m')
      (bp E (a + 1)
        (Pool.P0052.stage E C θ R K φ a P m' (m' + 1) ∪ Pool.P0052.stage E C θ R K φ a P m' m'))) →
    Pool.P0052.mergeUpTo E C θ R K φ a m P = Pool.P0052.mergeUpTo E C' θ R K φ a m P := by
  intro m
  induction m with
  | zero =>
    intro hm
    have h0 := hm 0 le_rfl
    simp only [Pool.P0052.stage] at h0
    simp only [Pool.P0052.mergeUpTo, Pool.P0052.mergeOne]
    rw [iter_congr θ R _ h0]
  | succ m ih =>
    intro hm
    simp only [Pool.P0052.mergeUpTo]
    have h1 := hm (m + 1) le_rfl
    simp only [Pool.P0052.stage] at h1
    have e1 : Pool.P0052.mergeOne E C θ R K φ a (m + 1) (Pool.P0052.mergeUpTo E C θ R K φ a m P)
        = Pool.P0052.mergeOne E C' θ R K φ a (m + 1) (Pool.P0052.mergeUpTo E C θ R K φ a m P) := by
      simp only [Pool.P0052.mergeOne]
      rw [iter_congr θ R _ h1]
    rw [e1, ih (fun m' hm' => hm m' (by omega))]

/-- **Process-level breakpoint locality.** If, at every merge that happens in P0052's run with cover data `C`
(level `ℓ ≤ lev a` at the end of epoch `a`), `C` and `C'` agree on the breakpoints of that merge's input pool
(entry epochs of its copies and the merge time `a + 1`), then P0052's sub-pools are the same for `C` and `C'`
at every epoch. -/
theorem pools_congr_bp {C C' : ι → ℕ → ℝ} (R K : ℕ) (lev : ℕ → ℕ) (ωs : ι → Bool)
    (φ : ℕ → ℕ → Fin K → ι → Bool)
    (h : ∀ a ℓ, ℓ ≤ lev a → AgreeOn E C C'
      (Pool.P0052.beforeMerge E C θ R K lev ωs φ a ℓ (ℓ + 1) ∪
        Pool.P0052.beforeMerge E C θ R K lev ωs φ a ℓ ℓ)
      (bp E (a + 1) (Pool.P0052.beforeMerge E C θ R K lev ωs φ a ℓ (ℓ + 1) ∪
        Pool.P0052.beforeMerge E C θ R K lev ωs φ a ℓ ℓ))) :
    ∀ a, Pool.P0052.pools E C θ R K lev ωs φ a = Pool.P0052.pools E C' θ R K lev ωs φ a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    simp only [Pool.P0052.pools]
    rw [mergeUpTo_congr_bp θ R K φ a _ (lev a) (fun m' hm' => by
      have := h a m' hm'
      rwa [Pool.P0052.beforeMerge_eq_stage] at this), ih]

/-- Shift form: if `C` and `C'` give every copy the same interval losses `[e₁, e₂]` with `E c ≤ e₁ ≤ e₂`, then
P0052's sub-pool process is the same for both. (A corollary of `pools_congr_bp`.) -/
theorem pools_congr {C C' : ι → ℕ → ℝ}
    (h : ∀ c e₁ e₂, E c ≤ e₁ → e₁ ≤ e₂ → Lint C c e₁ e₂ = Lint C' c e₁ e₂)
    (R K : ℕ) (lev : ℕ → ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) :
    ∀ a, Pool.P0052.pools E C θ R K lev ωs φ a = Pool.P0052.pools E C' θ R K lev ωs φ a :=
  pools_congr_bp θ R K lev ωs φ fun _ _ _ f _ e₁ _ e₂ _ hle hle' => h f e₁ e₂ hle hle'

/-- Losses since entry: `0` up to the entry epoch, then the cumulative loss minus its value at entry. -/
def sinceEntry (C : ι → ℕ → ℝ) (c : ι) (e : ℕ) : ℝ := if E c ≤ e then C c e - C c (E c) else 0

/-- The truncated "losses since entry" representation gives the same sub-pools as the true cumulative losses. -/
theorem pools_sinceEntry (C : ι → ℕ → ℝ) (R K : ℕ) (lev : ℕ → ℕ) (ωs : ι → Bool)
    (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) :
    Pool.P0052.pools E C θ R K lev ωs φ a = Pool.P0052.pools E (sinceEntry (E := E) C) θ R K lev ωs φ a := by
  refine pools_congr θ (fun c e₁ e₂ h1 h2 => ?_) R K lev ωs φ a
  simp only [Lint, sinceEntry, if_pos h1, if_pos (h1.trans h2)]
  ring

end Pool.P0068
