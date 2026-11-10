import Pool.P0042.MergeLemma

/-!
# Peng–Rubinstein's sub-pool process over explicit coins: passive copies do not interfere, and good runs keep
# every sub-pool small

Components C4 and (the deterministic half of) C3 of the coordination note P0045.

* **Coins.** Copies (experts) form a finite, linearly ordered type `ι` (entry order, ties broken), with entry epoch
  `E c`. Sampling bits `ωs : ι → Bool` (copy `c` is sampled iff `ωs c`), and filter bits
  `φ a ℓ : Fin K → ι → Bool` for the merge into level `ℓ + 1` at the end of epoch `a` (K fresh-coin iterations).
* **Process** (`pools`): after epoch `a`, the sub-pools `pools … a : ℕ → Finset ι`. In epoch `a`, the sampled copies
  entering at `a` (`newAt`) are added to level `0`. Then levels `0, 1, …, lev a` are merged in turn (`mergeUpTo`):
  level `ℓ` and level `ℓ+1` are combined by `K` iterations of P0042's `mstep` at merge time `a + 1`, the result goes to
  level `ℓ+1`, and level `ℓ` is emptied (`mergeOne`). There is no size estimation and no early stop (P0045 §2).
* **Non-interference** (`pools_erase`, all-slots version; `pools_erase_of_passive`, slot-restricted version): if
  copy `c`'s filter bits are `false` at every iteration of every merge whose input (in the run with `c`) contains
  `c` (`PassiveRun`), then the run with `c` and the run where `c` is not sampled (all other coins equal) have the
  same sub-pools up to `c` itself: `(pools ωs φ a ℓ).erase c = pools ωs' φ' a ℓ` for all `a, ℓ`.
  **Scope:** the cover data `C` (cumulative losses used by the cover test) is one fixed function shared by both
  runs, i.e. losses that do not depend on the pool (true losses, as in the K-query setting of P0045 §2). For
  estimated covers whose observation schedule depends on the pool, this theorem does not apply as is.
  Per merge step, `mem_mstep_of_false` shows that a passive copy survives the step iff it was in the input and is
  not covered by the filter set of the copy-free input. A whole-run characterization of `c`'s survival is not
  stated here. The key steps: `Fof_erase` (the filter set does not
  see `c`), `mstep_erase`, `iter_erase`, `mergeOne_erase`, `mergeUpTo_erase`.
* **Pool-size bound on good runs** (`pools_card_le`): `GoodRun` asks that every sample have at most `s0` copies and
  that every merge reach `max M0 (ρ · |input|)` (the conclusion of P0042's `merge_lemma` with
  `ρ = (1 − 1/(4L))^K`). Then, if `M0 ≤ S`, `s0 ≤ S` and `ρ · 2S ≤ S`, every sub-pool has at most `S` copies at every
  epoch. Only each single sub-pool is bounded; the whole pool (sum over levels, which depends on the schedule
  `lev`) is not bounded here. The probability that a run is good is a union bound over samples (Chernoff, P0034) and merges (P0042) once
  each merge's coins are fresh given the past (P0045's C2, the fresh-slot lemma). That last step is not done here.
-/

open Finset Pool.P0030 Pool.P0034 Pool.P0042

namespace Pool.P0052

variable {ι : Type*} [LinearOrder ι] (E : ι → ℕ) (C : ι → ℕ → ℝ) (t : ℕ) (θ : ℝ) (R : ℕ)

/-- Coin vectors that agree except at `c`, where `y c = false`. -/
def AgreeOff (c : ι) (y y' : ι → Bool) : Prop := ∀ x, x ≠ c → y x = y' x

omit [LinearOrder ι] in
theorem Fof_erase [DecidableEq ι] (c : ι) (y y' : ι → Bool) (hc : y c = false) (h : AgreeOff c y y')
    (Q : Finset ι) : Fof Q y = Fof (Q.erase c) y' := by
  ext x
  simp only [Fof, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hxQ, hx⟩
    have hxc : x ≠ c := by rintro rfl; rw [hc] at hx; exact Bool.false_ne_true hx
    exact ⟨⟨hxc, hxQ⟩, (h x hxc) ▸ hx⟩
  · rintro ⟨⟨hxc, hxQ⟩, hx⟩
    exact ⟨hxQ, (h x hxc).symm ▸ hx⟩

/-- **One Merge iteration commutes with erasing a copy outside the filter.** -/
theorem mstep_erase (c : ι) (y y' : ι → Bool) (hc : y c = false) (h : AgreeOff c y y')
    (Q : Finset ι) :
    (mstep E C t θ R Q y).erase c = mstep E C t θ R (Q.erase c) y' := by
  classical
  unfold mstep filterRound
  rw [← Fof_erase c y y' hc h Q]
  have hcF : c ∉ Fof Q y := by
    simp [Fof, hc]
  ext x
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ⟨hxc, (⟨hxQ, hnc⟩ | hxF)⟩
    · exact Or.inl ⟨⟨hxc, hxQ⟩, hnc⟩
    · exact Or.inr hxF
  · rintro (⟨⟨hxc, hxQ⟩, hnc⟩ | hxF)
    · exact ⟨hxc, Or.inl ⟨hxQ, hnc⟩⟩
    · exact ⟨fun h' => hcF (h' ▸ hxF), Or.inr hxF⟩

/-- Iterated Merge commutes with erasing a copy whose filter bits are all `false`. -/
theorem iter_erase (c : ι) : ∀ (K : ℕ) (φ φ' : Fin K → ι → Bool), (∀ k, φ k c = false) →
    (∀ k, AgreeOff c (φ k) (φ' k)) → ∀ Q : Finset ι,
    (iter (mstep E C t θ R) Q K φ).erase c = iter (mstep E C t θ R) (Q.erase c) K φ' := by
  intro K
  induction K with
  | zero => intro φ φ' _ _ Q; rfl
  | succ K ih =>
    intro φ φ' hc h Q
    simp only [iter]
    rw [mstep_erase E C t θ R c _ _ (hc _) (h _)]
    rw [ih (Fin.init φ) (Fin.init φ') (fun k => hc _) (fun k => h _) Q]

variable [Fintype ι] (K : ℕ) (lev : ℕ → ℕ)

/-- Copies entering at epoch `a` whose sampling bit is `true`. -/
noncomputable def newAt (ωs : ι → Bool) (a : ℕ) : Finset ι := Finset.univ.filter fun c => E c = a ∧ ωs c = true

/-- Merge level `ℓ` into level `ℓ + 1` at the end of epoch `a` (merge time `a + 1`), with filter coins `φ a ℓ`. -/
noncomputable def mergeOne (φ : ℕ → ℕ → Fin K → ι → Bool) (a ℓ : ℕ) (P : ℕ → Finset ι) : ℕ → Finset ι :=
  Function.update (Function.update P (ℓ + 1)
    (iter (mstep E C (a + 1) θ R) (P (ℓ + 1) ∪ P ℓ) K (φ a ℓ))) ℓ ∅

/-- Merge levels `0, 1, …, m` in turn at the end of epoch `a`. -/
noncomputable def mergeUpTo (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) : ℕ → (ℕ → Finset ι) → ℕ → Finset ι
  | 0, P => mergeOne E C θ R K φ a 0 P
  | m + 1, P => mergeOne E C θ R K φ a (m + 1) (mergeUpTo φ a m P)

/-- The sub-pools after `a` epochs: sample into level `0`, then merge levels `0..lev a`. -/
noncomputable def pools (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) : ℕ → ℕ → Finset ι
  | 0 => fun _ => ∅
  | a + 1 => mergeUpTo E C θ R K φ a (lev a)
      (Function.update (pools ωs φ a) 0 (pools ωs φ a 0 ∪ newAt E ωs a))

omit [LinearOrder ι] [Fintype ι] in
theorem erase_update [DecidableEq ι] (c : ι) (P : ℕ → Finset ι) (j : ℕ) (X : Finset ι) (j' : ℕ) :
    (Function.update P j X j').erase c = Function.update (fun i => (P i).erase c) j (X.erase c) j' := by
  by_cases h : j' = j
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem newAt_erase (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false) (a : ℕ) :
    (newAt E ωs a).erase c = newAt E ωs' a := by
  classical
  ext x
  simp only [newAt, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hxc, hE, hx⟩; exact ⟨hE, (hs x hxc) ▸ hx⟩
  · rintro ⟨hE, hx⟩
    have hxc : x ≠ c := by rintro rfl; rw [hs'] at hx; exact Bool.false_ne_true hx
    exact ⟨hxc, hE, (hs x hxc).symm ▸ hx⟩

theorem mergeOne_erase (c : ι) (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (hφ : ∀ a ℓ k, φ a ℓ k c = false)
    (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) (a ℓ : ℕ) (P : ℕ → Finset ι) (j : ℕ) :
    (mergeOne E C θ R K φ a ℓ P j).erase c = mergeOne E C θ R K φ' a ℓ (fun i => (P i).erase c) j := by
  classical
  unfold mergeOne
  rw [erase_update]
  congr 1
  · funext i
    rw [erase_update, iter_erase E C (a + 1) θ R c K (φ a ℓ) (φ' a ℓ) (hφ a ℓ) (hφ' a ℓ),
      Finset.erase_union_distrib]

theorem mergeUpTo_erase (c : ι) (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (hφ : ∀ a ℓ k, φ a ℓ k c = false)
    (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) (a : ℕ) :
    ∀ (m : ℕ) (P : ℕ → Finset ι) (j : ℕ),
      (mergeUpTo E C θ R K φ a m P j).erase c = mergeUpTo E C θ R K φ' a m (fun i => (P i).erase c) j := by
  intro m
  induction m with
  | zero => intro P j; exact mergeOne_erase E C θ R K c φ φ' hφ hφ' a 0 P j
  | succ m ih =>
    intro P j
    simp only [mergeUpTo]
    rw [mergeOne_erase E C θ R K c φ φ' hφ hφ' a (m + 1)]
    congr 1
    funext i
    exact ih P i

/-- **Non-interference of a passive copy.** If copy `c` has all its filter bits `false`, then removing it
from the run (making its sampling bit `false`, all other coins unchanged) changes every sub-pool at every epoch
only by removing `c`. So the rest of the process does not depend on `c`. -/
theorem pools_erase (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false)
    (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (hφ : ∀ a ℓ k, φ a ℓ k c = false)
    (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) :
    ∀ a ℓ, (pools E C θ R K lev ωs φ a ℓ).erase c = pools E C θ R K lev ωs' φ' a ℓ := by
  classical
  intro a
  induction a with
  | zero => intro ℓ; simp [pools]
  | succ a ih =>
    intro ℓ
    simp only [pools]
    rw [mergeUpTo_erase E C θ R K c φ φ' hφ hφ' a]
    congr 1
    funext i
    rw [erase_update]
    have hfun : (fun i => (pools E C θ R K lev ωs φ a i).erase c) = pools E C θ R K lev ωs' φ' a := by
      funext j; exact ih j
    rw [hfun, Finset.erase_union_distrib, ih 0, newAt_erase E c ωs ωs' hs hs']

/-- The pools just before the merge of level `ℓ` at the end of epoch `a` (after sampling and after merging
levels `0..ℓ-1`). -/
noncomputable def beforeMerge (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) : ℕ → ℕ → Finset ι
  | 0 => Function.update (pools E C θ R K lev ωs φ a) 0 (pools E C θ R K lev ωs φ a 0 ∪ newAt E ωs a)
  | m + 1 => mergeUpTo E C θ R K φ a m
      (Function.update (pools E C θ R K lev ωs φ a) 0 (pools E C θ R K lev ωs φ a 0 ∪ newAt E ωs a))

/-- Good events of a run: every sample has at most `s0` copies, and every merge (at levels `≤ lev a`) brings
its input down to `max M0 (ρ · |input|)`. -/
def GoodRun (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) (NE : ℕ) (s0 : ℕ) (M0 ρ : ℝ) : Prop :=
  (∀ a < NE, (newAt E ωs a).card ≤ s0) ∧
  ∀ a < NE, ∀ ℓ ≤ lev a,
    ((iter (mstep E C (a + 1) θ R)
        (beforeMerge E C θ R K lev ωs φ a ℓ (ℓ + 1) ∪ beforeMerge E C θ R K lev ωs φ a ℓ ℓ) K (φ a ℓ)).card : ℝ)
      ≤ max M0 (ρ * (beforeMerge E C θ R K lev ωs φ a ℓ (ℓ + 1) ∪ beforeMerge E C θ R K lev ωs φ a ℓ ℓ).card)

theorem mergeUpTo_succ_eq (φ : ℕ → ℕ → Fin K → ι → Bool) (a m : ℕ) (P : ℕ → Finset ι) :
    mergeUpTo E C θ R K φ a (m + 1) P = mergeOne E C θ R K φ a (m + 1) (mergeUpTo E C θ R K φ a m P) := rfl

omit [LinearOrder ι] [Fintype ι] in
theorem update_card_le (P : ℕ → Finset ι) (j : ℕ) (X : Finset ι) (S : ℝ) (hP : ∀ i, ((P i).card : ℝ) ≤ S)
    (hX : (X.card : ℝ) ≤ S) : ∀ i, ((Function.update P j X i).card : ℝ) ≤ S := by
  intro i
  by_cases h : i = j
  · subst h; simpa using hX
  · rw [Function.update_of_ne h]; exact hP i

theorem mergeUpTo_zero_level (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) :
    ∀ (m : ℕ) (P : ℕ → Finset ι), mergeUpTo E C θ R K φ a m P 0 = ∅ := by
  intro m
  induction m with
  | zero => intro P; simp [mergeUpTo, mergeOne]
  | succ m ih =>
    intro P
    simp only [mergeUpTo, mergeOne]
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), ih]

theorem pools_zero_level (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) :
    pools E C θ R K lev ωs φ a 0 = ∅ := by
  cases a with
  | zero => rfl
  | succ a => simp only [pools]; exact mergeUpTo_zero_level E C θ R K φ a _ _

/-- **Deterministic pool-size bound (PR23 Lemma 4.5 form).** On a good run, with `M0 ≤ S`, `s0 ≤ S` and
`ρ · 2S ≤ S`, every sub-pool has at most `S` copies at every epoch `≤ NE`. -/
theorem pools_card_le (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) (NE s0 : ℕ) (M0 ρ S : ℝ)
    (hρ : 0 ≤ ρ) (hgood : GoodRun E C θ R K lev ωs φ NE s0 M0 ρ) (hM0 : M0 ≤ S) (hs0 : (s0 : ℝ) ≤ S)
    (hρS : ρ * (2 * S) ≤ S) :
    ∀ a ≤ NE, ∀ ℓ, ((pools E C θ R K lev ωs φ a ℓ).card : ℝ) ≤ S := by
  classical
  have hS0 : 0 ≤ S := le_trans (Nat.cast_nonneg _) hs0
  intro a
  induction a with
  | zero => intro _ ℓ; simp [pools, hS0]
  | succ a ih =>
    intro ha
    have ihS := ih (by omega)
    set start := Function.update (pools E C θ R K lev ωs φ a) 0
      (pools E C θ R K lev ωs φ a 0 ∪ newAt E ωs a) with hstart_def
    have hstart : ∀ j, ((start j).card : ℝ) ≤ S := by
      apply update_card_le _ _ _ S ihS
      rw [pools_zero_level, Finset.empty_union]
      exact le_trans (by exact_mod_cast hgood.1 a (by omega)) hs0
    -- one merge keeps all levels ≤ S
    have hone : ∀ ℓ ≤ lev a, ∀ P : ℕ → Finset ι, beforeMerge E C θ R K lev ωs φ a ℓ = P →
        (∀ j, ((P j).card : ℝ) ≤ S) → ∀ j, ((mergeOne E C θ R K φ a ℓ P j).card : ℝ) ≤ S := by
      intro ℓ hℓ P hP hPS j
      have hm := hgood.2 a (by omega) ℓ hℓ
      rw [hP] at hm
      unfold mergeOne
      apply update_card_le _ _ _ S _ (by simpa using hS0)
      apply update_card_le _ _ _ S hPS
      have hU : (((P (ℓ + 1) ∪ P ℓ).card : ℕ) : ℝ) ≤ 2 * S := by
        have := Finset.card_union_le (P (ℓ + 1)) (P ℓ)
        have h1 := hPS (ℓ + 1)
        have h2 := hPS ℓ
        have : (((P (ℓ + 1) ∪ P ℓ).card : ℕ) : ℝ) ≤ (P (ℓ + 1)).card + (P ℓ).card := by exact_mod_cast this
        linarith
      refine hm.trans (max_le hM0 ?_)
      calc ρ * ((P (ℓ + 1) ∪ P ℓ).card : ℝ) ≤ ρ * (2 * S) := mul_le_mul_of_nonneg_left hU hρ
        _ ≤ S := hρS
    -- all merges of epoch `a`
    have hall : ∀ m ≤ lev a, ∀ j, ((mergeUpTo E C θ R K φ a m start j).card : ℝ) ≤ S := by
      intro m
      induction m with
      | zero => intro hm; exact hone 0 hm start rfl hstart
      | succ m ihm =>
        intro hm
        exact hone (m + 1) hm _ rfl (ihm (by omega))
    intro ℓ
    exact hall (lev a) le_rfl ℓ

/-! ### Slot-restricted passivity: only the bits of `c` at iterations where `c` is in the input matter -/

/-- A merge iteration whose input does not contain `c` does not read `c`'s bit, and erasing `c` changes nothing.
Together with `mstep_erase` this gives the slot-restricted step `mstep_erase_of_mem`. -/
theorem mstep_erase_of_mem (c : ι) (y y' : ι → Bool) (Q : Finset ι) (hc : c ∈ Q → y c = false)
    (h : AgreeOff c y y') :
    (mstep E C t θ R Q y).erase c = mstep E C t θ R (Q.erase c) y' := by
  classical
  by_cases hcQ : c ∈ Q
  · exact mstep_erase E C t θ R c y y' (hc hcQ) h Q
  · have hQ : Q.erase c = Q := Finset.erase_eq_of_notMem hcQ
    have hF : Fof Q y = Fof Q y' := by
      ext x
      simp only [Fof, Finset.mem_filter]
      constructor
      · rintro ⟨hxQ, hx⟩
        have hxc : x ≠ c := by rintro rfl; exact hcQ hxQ
        exact ⟨hxQ, (h x hxc) ▸ hx⟩
      · rintro ⟨hxQ, hx⟩
        have hxc : x ≠ c := by rintro rfl; exact hcQ hxQ
        exact ⟨hxQ, (h x hxc).symm ▸ hx⟩
    have hsub : c ∉ mstep E C t θ R Q y := fun hm => hcQ (mstep_sub E C t θ R Q y hm)
    rw [Finset.erase_eq_of_notMem hsub, hQ]
    unfold mstep
    rw [hF]

/-- `c`'s bit is `false` at every iteration of a merge whose current input contains `c`
(the input of iteration `j` is the result of the first `j` iterations, in the run with `c`). -/
def PassiveIter (c : ι) (Q : Finset ι) : (m : ℕ) → (Fin m → ι → Bool) → Prop
  | 0, _ => True
  | m + 1, φ => PassiveIter c Q m (Fin.init φ) ∧
      (c ∈ iter (mstep E C t θ R) Q m (Fin.init φ) → φ (Fin.last m) c = false)

/-- Slot-restricted version of `iter_erase`. -/
theorem iter_erase_of_passive (c : ι) : ∀ (m : ℕ) (φ φ' : Fin m → ι → Bool) (Q : Finset ι),
    PassiveIter E C t θ R c Q m φ → (∀ k, AgreeOff c (φ k) (φ' k)) →
    (iter (mstep E C t θ R) Q m φ).erase c = iter (mstep E C t θ R) (Q.erase c) m φ' := by
  intro m
  induction m with
  | zero => intro φ φ' Q _ _; rfl
  | succ m ih =>
    intro φ φ' Q hp h
    simp only [iter]
    rw [mstep_erase_of_mem E C t θ R c _ _ _ hp.2 (h _)]
    rw [ih (Fin.init φ) (Fin.init φ') Q hp.1 (fun k => h _)]

/-- The pools just before the merge of level `m` within one epoch, as a function of the start-of-epoch pools. -/
noncomputable def stage (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) (P : ℕ → Finset ι) : ℕ → ℕ → Finset ι
  | 0 => P
  | m + 1 => mergeUpTo E C θ R K φ a m P

theorem mergeOne_erase_of_passive (c : ι) (φ φ' : ℕ → ℕ → Fin K → ι → Bool)
    (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) (a ℓ : ℕ) (P : ℕ → Finset ι)
    (hp : PassiveIter E C (a + 1) θ R c (P (ℓ + 1) ∪ P ℓ) K (φ a ℓ)) (j : ℕ) :
    (mergeOne E C θ R K φ a ℓ P j).erase c = mergeOne E C θ R K φ' a ℓ (fun i => (P i).erase c) j := by
  classical
  unfold mergeOne
  rw [erase_update]
  congr 1
  · funext i
    rw [erase_update, iter_erase_of_passive E C (a + 1) θ R c K (φ a ℓ) (φ' a ℓ) _ hp (hφ' a ℓ),
      Finset.erase_union_distrib]

theorem mergeUpTo_erase_of_passive (c : ι) (φ φ' : ℕ → ℕ → Fin K → ι → Bool)
    (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) (a : ℕ) (P : ℕ → Finset ι) :
    ∀ (m : ℕ), (∀ m' ≤ m, PassiveIter E C (a + 1) θ R c
        (stage E C θ R K φ a P m' (m' + 1) ∪ stage E C θ R K φ a P m' m') K (φ a m')) →
      ∀ j, (mergeUpTo E C θ R K φ a m P j).erase c =
        mergeUpTo E C θ R K φ' a m (fun i => (P i).erase c) j := by
  intro m
  induction m with
  | zero =>
    intro hp j
    exact mergeOne_erase_of_passive E C θ R K c φ φ' hφ' a 0 P (hp 0 le_rfl) j
  | succ m ih =>
    intro hp j
    simp only [mergeUpTo]
    rw [mergeOne_erase_of_passive E C θ R K c φ φ' hφ' a (m + 1) (mergeUpTo E C θ R K φ a m P)
      (hp (m + 1) le_rfl)]
    congr 1
    funext i
    exact ih (fun m' hm' => hp m' (by omega)) i

theorem beforeMerge_eq_stage (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) (a ℓ : ℕ) :
    beforeMerge E C θ R K lev ωs φ a ℓ = stage E C θ R K φ a
      (Function.update (pools E C θ R K lev ωs φ a) 0 (pools E C θ R K lev ωs φ a 0 ∪ newAt E ωs a)) ℓ := by
  cases ℓ <;> rfl

/-- **Slot-restricted passivity** of copy `c` in the run `(ωs, φ)`: at every merge that actually happens
(`ℓ ≤ lev a`), `c`'s filter bit is `false` at every iteration whose input (in this run) contains `c`. Bits of `c`
at other slots are unconstrained. -/
def PassiveRun (c : ι) (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) : Prop :=
  ∀ a ℓ, ℓ ≤ lev a → PassiveIter E C (a + 1) θ R c
    (beforeMerge E C θ R K lev ωs φ a ℓ (ℓ + 1) ∪ beforeMerge E C θ R K lev ωs φ a ℓ ℓ) K (φ a ℓ)

/-- **Non-interference of a passive copy, slot-restricted version.** Only `c`'s bits at iterations of
merges whose input contains `c` need to be `false`. Then removing `c` from the run (its sampling bit
`false`, all other coins unchanged, `c`'s other bits arbitrary in either run) changes every sub-pool at every
epoch only by removing `c`. -/
theorem pools_erase_of_passive (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false)
    (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (hp : PassiveRun E C θ R K lev c ωs φ)
    (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) :
    ∀ a ℓ, (pools E C θ R K lev ωs φ a ℓ).erase c = pools E C θ R K lev ωs' φ' a ℓ := by
  classical
  intro a
  induction a with
  | zero => intro ℓ; simp [pools]
  | succ a ih =>
    intro ℓ
    simp only [pools]
    rw [mergeUpTo_erase_of_passive E C θ R K c φ φ' hφ' a _ (lev a) (fun m' hm' => by
      have := hp a m' hm'
      rwa [beforeMerge_eq_stage] at this)]
    congr 1
    funext i
    rw [erase_update]
    have hfun : (fun i => (pools E C θ R K lev ωs φ a i).erase c) = pools E C θ R K lev ωs' φ' a := by
      funext j; exact ih j
    rw [hfun, Finset.erase_union_distrib, ih 0, newAt_erase E c ωs ωs' hs hs']

theorem passiveIter_of_false (c : ι) (Q : Finset ι) :
    ∀ (m : ℕ) (φ : Fin m → ι → Bool), (∀ k, φ k c = false) → PassiveIter E C t θ R c Q m φ := by
  intro m
  induction m with
  | zero => intro _ _; trivial
  | succ m ih => intro φ h; exact ⟨ih _ (fun k => h _), fun _ => h _⟩

/-- The all-slots hypothesis of `pools_erase` implies `PassiveRun`, so `pools_erase_of_passive` generalizes
`pools_erase`. -/
theorem passiveRun_of_false (c : ι) (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool)
    (hφ : ∀ a ℓ k, φ a ℓ k c = false) : PassiveRun E C θ R K lev c ωs φ :=
  fun a ℓ _ => passiveIter_of_false E C (a + 1) θ R c _ K (φ a ℓ) (hφ a ℓ)

/-- One Merge iteration, for a copy `c` whose bit is `false`: `c` survives exactly when it was in the input and
is not covered by the filter set of the **copy-free** input (`Fof (Q.erase c) y'`). So survival of a passive
copy at a step is decided by the copy-free run's filter set. -/
theorem mem_mstep_of_false (c : ι) (y y' : ι → Bool) (hc : y c = false) (h : AgreeOff c y y')
    (Q : Finset ι) :
    c ∈ mstep E C t θ R Q y ↔ c ∈ Q ∧ ¬ Covered E C t θ (Fof (Q.erase c) y') c R := by
  classical
  rw [← Fof_erase c y y' hc h Q]
  have hcF : c ∉ Fof Q y := by simp [Fof, hc]
  unfold mstep filterRound
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (h1 | h1)
    · exact h1
    · exact absurd h1 hcF
  · intro h1; exact Or.inl h1

end Pool.P0052
