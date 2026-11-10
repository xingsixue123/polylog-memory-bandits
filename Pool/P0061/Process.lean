import Pool.P0052.PoolProcess
import Pool.P0061.Chain

/-!
# Good-interval certificates for the P0052 sub-pool process

* `inP_interval`: a copy in the start pool of epoch `a` was in the start pool of every epoch from its entry
  epoch to `a` (merges only remove copies; sampling only adds copies entering now).
* `cover_of_drop`: a passive copy (P0052 `PassiveRun`) dropped by the merges of epoch `a` is P0030-`Covered` at
  merge time `a + 1` by a filter set of start-pool copies not containing it.
* `startPool_erase`: P0052's non-interference, for start pools.
* `cert_transfer` (main): the cost of the good interval `[E c, a + 1)` in the copy-free run: any learner within
  `Rh` of every start-pool copy on every epoch loses at most `θ + (a + 1 - E c) Rh` more than `c`.
-/

open Finset Pool.P0030 Pool.P0034 Pool.P0042 Pool.P0052

namespace Pool.P0061

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ) (R K : ℕ)
  (lev : ℕ → ℕ)

/-- Membership in some level. -/
def InP (P : ℕ → Finset ι) (f : ι) : Prop := ∃ ℓ, f ∈ P ℓ

/-- Sub-pools at the start of epoch `a`, after the copies entering at `a` joined level `0`. -/
noncomputable abbrev startPool (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) : ℕ → Finset ι :=
  beforeMerge E C θ R K lev ωs φ a 0

theorem inP_mergeOne {φ : ℕ → ℕ → Fin K → ι → Bool} {a ℓ : ℕ} {P : ℕ → Finset ι} {f : ι}
    (h : InP (mergeOne E C θ R K φ a ℓ P) f) : InP P f := by
  obtain ⟨j, hj⟩ := h
  unfold mergeOne at hj
  by_cases h1 : j = ℓ
  · subst h1; simp at hj
  rw [Function.update_of_ne h1] at hj
  by_cases h2 : j = ℓ + 1
  · subst h2
    rw [Function.update_self] at hj
    have := iter_sub (mstep E C (a + 1) θ R) _ (mstep_sub E C (a + 1) θ R) K (φ a ℓ) hj
    rcases mem_union.1 this with h3 | h3
    · exact ⟨ℓ + 1, h3⟩
    · exact ⟨ℓ, h3⟩
  · rw [Function.update_of_ne h2] at hj; exact ⟨j, hj⟩

theorem inP_mergeUpTo {φ : ℕ → ℕ → Fin K → ι → Bool} {a : ℕ} :
    ∀ (m : ℕ) {P : ℕ → Finset ι} {f : ι}, InP (mergeUpTo E C θ R K φ a m P) f → InP P f := by
  intro m
  induction m with
  | zero => intro P f h; exact inP_mergeOne E C θ R K h
  | succ m ih => intro P f h; exact ih (inP_mergeOne E C θ R K h)

theorem inP_beforeMerge {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {a : ℕ} :
    ∀ (m : ℕ) {f : ι}, InP (beforeMerge E C θ R K lev ωs φ a m) f →
      InP (startPool E C θ R K lev ωs φ a) f := by
  intro m f h
  cases m with
  | zero => exact h
  | succ m => exact inP_mergeUpTo E C θ R K m h

/-- The sub-pools after epoch `a` are a sub-collection of the start pool of epoch `a`. -/
theorem inP_pools_succ {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {a : ℕ} {f : ι}
    (h : InP (pools E C θ R K lev ωs φ (a + 1)) f) : InP (startPool E C θ R K lev ωs φ a) f :=
  inP_mergeUpTo E C θ R K (lev a) h

/-- A copy in the start pool of epoch `a` that did not enter at `a` was in the pools after epoch `a - 1`. -/
theorem inP_startPool {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {a : ℕ} {f : ι}
    (h : InP (startPool E C θ R K lev ωs φ a) f) (hf : E f ≠ a) :
    InP (pools E C θ R K lev ωs φ a) f := by
  obtain ⟨j, hj⟩ := h
  simp only [startPool, beforeMerge] at hj
  by_cases h0 : j = 0
  · subst h0
    rw [Function.update_self] at hj
    rcases mem_union.1 hj with h1 | h1
    · exact ⟨0, h1⟩
    · simp [newAt] at h1; exact absurd h1.1 hf
  · rw [Function.update_of_ne h0] at hj; exact ⟨j, hj⟩

theorem pools_zero_empty {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {f : ι} :
    ¬ InP (pools E C θ R K lev ωs φ 0) f := by
  rintro ⟨j, hj⟩; simp [pools] at hj

/-- **Membership interval.** A copy in the start pool of epoch `a` was in the start pool of every epoch from its
entry epoch up to `a`. -/
theorem inP_interval {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {f : ι} :
    ∀ (d a : ℕ), a - E f = d → InP (startPool E C θ R K lev ωs φ a) f →
      ∀ u, E f ≤ u → u ≤ a → InP (startPool E C θ R K lev ωs φ u) f := by
  intro d
  induction d with
  | zero =>
    intro a hd h u hu hua
    have : u = a := by omega
    subst this; exact h
  | succ d ih =>
    intro a hd h u hu hua
    rcases eq_or_lt_of_le hua with hua | hua
    · subst hua; exact h
    · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      have h1 := inP_startPool E C θ R K lev h (by omega)
      have h2 := inP_pools_succ E C θ R K lev h1
      exact ih a' (by omega) h2 u hu (by omega)


/-- A passive copy evicted by a run of `K` merge iterations was covered, at some iteration, by a filter set
contained in the merge input and not containing it. -/
theorem cover_of_evicted (t : ℕ) (c : ι) :
    ∀ (m : ℕ) (φ : Fin m → ι → Bool) (Q : Finset ι), PassiveIter E C t θ R c Q m φ → c ∈ Q →
      c ∉ iter (mstep E C t θ R) Q m φ →
      ∃ F : Finset ι, F ⊆ Q ∧ c ∉ F ∧ Covered E C t θ F c R := by
  classical
  intro m
  induction m with
  | zero => intro φ Q _ hc hn; exact absurd hc hn
  | succ m ih =>
    intro φ Q hp hc hn
    obtain ⟨hp1, hp2⟩ := hp
    by_cases hin : c ∈ iter (mstep E C t θ R) Q m (Fin.init φ)
    · have hbit := hp2 hin
      simp only [iter] at hn
      have hiff := mem_mstep_of_false E C t θ R c _ _ hbit (fun _ _ => rfl)
        (iter (mstep E C t θ R) Q m (Fin.init φ))
      have hcov : Covered E C t θ (Fof ((iter (mstep E C t θ R) Q m (Fin.init φ)).erase c)
          (φ (Fin.last m))) c R := by
        by_contra hnc; exact hn (hiff.2 ⟨hin, hnc⟩)
      refine ⟨_, ?_, ?_, hcov⟩
      · intro x hx
        have h1 : x ∈ (iter (mstep E C t θ R) Q m (Fin.init φ)).erase c := (Finset.mem_filter.1 hx).1
        exact iter_sub (mstep E C t θ R) Q (mstep_sub E C t θ R) m _ (Finset.mem_of_mem_erase h1)
      · intro hx
        have h1 := (Finset.mem_filter.1 hx).1
        simp at h1
    · exact ih (Fin.init φ) Q hp1 hc hin

theorem beforeMerge_succ {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} (a ℓ : ℕ) :
    beforeMerge E C θ R K lev ωs φ a (ℓ + 1) =
      mergeOne E C θ R K φ a ℓ (beforeMerge E C θ R K lev ωs φ a ℓ) := by
  cases ℓ with
  | zero => rfl
  | succ ℓ => rfl

theorem exists_drop (P : ℕ → Prop) (h0 : P 0) : ∀ N, ¬ P N → ∃ ℓ < N, P ℓ ∧ ¬ P (ℓ + 1) := by
  intro N
  induction N with
  | zero => intro h; exact absurd h0 h
  | succ N ih =>
    intro hN
    by_cases hP : P N
    · exact ⟨N, by omega, hP, hN⟩
    · obtain ⟨ℓ, hℓ, h1, h2⟩ := ih hP; exact ⟨ℓ, by omega, h1, h2⟩

/-- **Eviction certificate.** If a passive copy `c` is in the start pool of epoch `a` but in no sub-pool after
the merges of epoch `a`, then it is covered at merge time `a + 1` by a filter set of copies of the start pool of
epoch `a`, not containing `c`. -/
theorem cover_of_drop {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {a : ℕ} {c : ι}
    (hp : PassiveRun E C θ R K lev c ωs φ)
    (hin : InP (startPool E C θ R K lev ωs φ a) c) (hout : ¬ InP (pools E C θ R K lev ωs φ (a + 1)) c) :
    ∃ F : Finset ι, (∀ f ∈ F, InP (startPool E C θ R K lev ωs φ a) f) ∧ c ∉ F ∧
      Covered E C (a + 1) θ F c R := by
  classical
  obtain ⟨ℓ, hℓ, h1, h2⟩ := exists_drop (fun m => InP (beforeMerge E C θ R K lev ωs φ a m) c) hin
    (lev a + 1) hout
  rw [beforeMerge_succ] at h2
  set P := beforeMerge E C θ R K lev ωs φ a ℓ with hP
  have hQ : c ∈ P (ℓ + 1) ∪ P ℓ := by
    obtain ⟨j, hj⟩ := h1
    by_cases hj1 : j = ℓ
    · subst hj1; exact mem_union_right _ hj
    by_cases hj2 : j = ℓ + 1
    · subst hj2; exact mem_union_left _ hj
    exfalso; apply h2; refine ⟨j, ?_⟩
    unfold mergeOne
    rw [Function.update_of_ne hj1, Function.update_of_ne hj2]; exact hj
  have hev : c ∉ iter (mstep E C (a + 1) θ R) (P (ℓ + 1) ∪ P ℓ) K (φ a ℓ) := by
    intro hc; apply h2; refine ⟨ℓ + 1, ?_⟩
    unfold mergeOne
    rw [Function.update_of_ne (by omega), Function.update_self]; exact hc
  obtain ⟨F, hFQ, hcF, hcov⟩ := cover_of_evicted E C θ R (a + 1) c K (φ a ℓ) _
    (hp a ℓ (by omega)) hQ hev
  refine ⟨F, fun f hf => ?_, hcF, hcov⟩
  have := hFQ hf
  rcases mem_union.1 this with h3 | h3
  · exact inP_beforeMerge E C θ R K lev ℓ ⟨ℓ + 1, h3⟩
  · exact inP_beforeMerge E C θ R K lev ℓ ⟨ℓ, h3⟩


theorem startPool_erase (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false)
    (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (hp : PassiveRun E C θ R K lev c ωs φ)
    (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) (a j : ℕ) :
    (startPool E C θ R K lev ωs φ a j).erase c = startPool E C θ R K lev ωs' φ' a j := by
  classical
  simp only [startPool, beforeMerge]
  rw [erase_update]
  have hfun : (fun i => (pools E C θ R K lev ωs φ a i).erase c) = pools E C θ R K lev ωs' φ' a := by
    funext i; exact pools_erase_of_passive E C θ R K lev c ωs ωs' hs hs' φ φ' hp hφ' a i
  rw [hfun, Finset.erase_union_distrib, pools_erase_of_passive E C θ R K lev c ωs ωs' hs hs' φ φ' hp hφ' a 0,
    newAt_erase E c ωs ωs' hs hs']

/-- **Good-interval certificate, transferred to the copy-free run.** Let `c` be passive in the run `(ωs, φ)`, in
the start pool of epoch `a` and dropped by the merges of epoch `a`. Let `(ωs', φ')` be the same coins with `c`
not sampled. If, in the copy-free run, a learner's epoch loss `A u` is within `Rh` of the epoch loss `ep u f` of
every copy `f` of the start pool of epoch `u`, and the cover data are the cumulative epoch losses, then on
`[E c, a + 1)` the learner loses at most `θ + (a + 1 - E c) Rh` more than `c`. -/
theorem cert_transfer (ep : ℕ → ι → ℝ) (A : ℕ → ℝ) (Rh : ℝ) (c : ι) (ωs ωs' : ι → Bool)
    (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false) (φ φ' : ℕ → ℕ → Fin K → ι → Bool)
    (hp : PassiveRun E (cumL ep) θ R K lev c ωs φ)
    (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) {a : ℕ}
    (hin : InP (startPool E (cumL ep) θ R K lev ωs φ a) c)
    (hout : ¬ InP (pools E (cumL ep) θ R K lev ωs φ (a + 1)) c)
    (hA : ∀ u f, InP (startPool E (cumL ep) θ R K lev ωs' φ' u) f → A u ≤ ep u f + Rh) :
    E c ≤ a + 1 ∧ ∑ u ∈ Ico (E c) (a + 1), A u ≤
      ∑ u ∈ Ico (E c) (a + 1), ep u c + θ + ((a + 1 - E c : ℕ) : ℝ) * Rh := by
  classical
  obtain ⟨F, hF, hcF, ch, -, hchF, hok, hcov⟩ := cover_of_drop E (cumL ep) θ R K lev hp hin hout
  have hEc : E c ≤ a + 1 := Pool.P0041.chain_le_t E (a + 1) ch (E c) hok
  refine ⟨hEc, ?_⟩
  have hpres : ∀ f ∈ ch, ∀ u, E f ≤ u → u < a + 1 → A u ≤ ep u f + Rh := by
    intro f hf u hfu hua
    have hfF := hchF f hf
    have hfc : f ≠ c := fun h => hcF (h ▸ hfF)
    obtain ⟨j, hj⟩ := inP_interval E (cumL ep) θ R K lev (a - E f) a rfl (hF f hfF) u hfu
      (by omega)
    apply hA u f
    refine ⟨j, ?_⟩
    rw [← startPool_erase E (cumL ep) θ R K lev c ωs ωs' hs hs' φ φ' hp hφ' u j]
    exact Finset.mem_erase.2 ⟨hfc, hj⟩
  have h1 := sum_le_pieceSum E ep A Rh (a + 1) ch (E c) hok hpres
  rw [Lint_cumL ep c hEc] at hcov
  linarith

end Pool.P0061
