import Pool.P0065.Threads
import Pool.P0081.Threads

/-!
# Pool processes with cover data that agree off a copy, up to the current time

P0052's sub-pool process and P0065's threaded process take the cover data (cumulative losses
`C : ι → ℕ → ℝ`) as one fixed function. Their non-interference theorems (`Pool.P0052.pools_erase`,
`Pool.P0065.tpools_erase`, `Pool.P0065.forced_erase`) compare a run with a copy `c` and the copy-free
run *with the same* `C`. With estimated covers (a learner that observes one pool slot per round), the
two runs have different data: their estimates agree for every copy other than `c`, but only for the
rounds that have already happened. This file supplies the two facts needed to transfer those
theorems:

* **Congruence / causality.** The process at the boundary `a` reads the data of its sampled copies
  only at times `≤ a`: `Pool.P0083.tpools_congr` (threaded) and `Pool.P0083.pools_congr`
  (sub-pools). The step lemmas are `covered_congr`, `filterRound_congr`, `mstep_congr`,
  `iter_congr`, `mergeOne_congr`, `mergeUpTo_congr`.
* **Erase with agreeing data.** If the data agree off `c` at all times `≤ a`, the run with `c` and
  the copy-free run (each with its own data) agree off `c` at the boundary `a`:
  `Pool.P0083.tpools_erase_congr`, `Pool.P0083.forced_erase_congr`,
  `Pool.P0083.forced_erase_start_congr` (threaded) and `Pool.P0083.pools_erase_congr` (sub-pools),
  and the slot-restricted versions `Pool.P0083.tpools_erase_of_slots_congr`,
  `Pool.P0083.tpools_erase_of_slots_lt_congr` (P0081's clock slots) and
  `Pool.P0083.pools_erase_of_passive_congr` (P0052's `PassiveRun`).
  The proofs are `tpools_erase` (same data) followed by `tpools_congr` on the copy-free run, whose
  copies are all different from `c` (`Pool.P0083.mem_tpools_sampled`).

Nothing here is probabilistic, and no estimator is fixed: `C` and `C'` are arbitrary.

**What is assumed, not shown.** Every `*_erase_congr` theorem has the hypothesis `hC`: the two runs'
data agree pathwise for every copy `x ≠ c` at all times `≤ a`. For estimated covers this must be
established by a coupling. For instance, with one free observation per round, the forced copy `c`
occupies a slot and can change which other copy is observed. So one needs something like a copy-last
slot order with a fixed slot count and pool-size-independent importance weights. No such coupling,
and no estimator satisfying `hC`, is proved here (planned as FO2/FO3, not formalized here). The
unbounded slot version `tpools_erase_of_slots_congr` has a hypothesis of probability `0` for a
surviving copy (see its docstring). Use `tpools_erase_of_slots_lt_congr`.
-/

open Finset Pool.P0030 Pool.P0034 Pool.P0042 Pool.P0052 Pool.P0065

namespace Pool.P0083

section Cover

variable {ι : Type*} (E : ι → ℕ) (t : ℕ) (θ : ℝ)

/-- A valid chain started at `a` starts no later than `t`. -/
theorem chainOK_le : ∀ (ch : List ι) (a : ℕ), ChainOK E t ch a → a ≤ t
  | [], _, h => h.elim
  | [_], _, h => h.2
  | _ :: g :: rest, _, h => h.2.1.trans (chainOK_le (g :: rest) (E g) h.2.2)

/-- The loss of a valid chain reads the data of its members only at times `≤ t`. -/
theorem pieceSum_congr (C C' : ι → ℕ → ℝ) : ∀ (ch : List ι) (a : ℕ), ChainOK E t ch a →
    (∀ f ∈ ch, ∀ u ≤ t, C f u = C' f u) → pieceSum E C t ch a = pieceSum E C' t ch a
  | [], _, _, _ => rfl
  | [f], a, h, hC => by
    simp only [pieceSum, Lint]
    rw [hC f (by simp) t le_rfl, hC f (by simp) a h.2]
  | f :: g :: rest, a, h, hC => by
    have hg := chainOK_le E t (g :: rest) (E g) h.2.2
    simp only [pieceSum, Lint]
    rw [hC f (by simp) _ hg, hC f (by simp) a (h.2.1.trans hg),
      pieceSum_congr C C' (g :: rest) (E g) h.2.2 (fun f' hf' => hC f' (List.mem_cons_of_mem _ hf'))]

theorem covered_of_congr (C C' : ι → ℕ → ℝ) (F : Finset ι) (j : ι) (len : ℕ)
    (hF : ∀ f ∈ F, ∀ u ≤ t, C f u = C' f u) (hj : ∀ u ≤ t, C j u = C' j u)
    (h : Covered E C t θ F j len) : Covered E C' t θ F j len := by
  obtain ⟨ch, hlen, hmem, hok, hcost⟩ := h
  refine ⟨ch, hlen, hmem, hok, ?_⟩
  have hjt : E j ≤ t := chainOK_le E t ch (E j) hok
  rw [← pieceSum_congr E t C C' ch (E j) hok (fun f hf => hF f (hmem f hf))]
  simp only [Lint] at hcost ⊢
  rw [← hj t le_rfl, ← hj (E j) hjt]
  exact hcost

/-- **The cover test reads only the data of the tested copy and of the filters, at times `≤ t`.** -/
theorem covered_congr (C C' : ι → ℕ → ℝ) (F : Finset ι) (j : ι) (len : ℕ)
    (hF : ∀ f ∈ F, ∀ u ≤ t, C f u = C' f u) (hj : ∀ u ≤ t, C j u = C' j u) :
    Covered E C t θ F j len ↔ Covered E C' t θ F j len :=
  ⟨covered_of_congr E t θ C C' F j len hF hj,
    covered_of_congr E t θ C' C F j len (fun f hf u hu => (hF f hf u hu).symm)
      (fun u hu => (hj u hu).symm)⟩

theorem filterRound_congr [LinearOrder ι] (C C' : ι → ℕ → ℝ) (Q F : Finset ι) (len : ℕ)
    (hQ : ∀ x ∈ Q, ∀ u ≤ t, C x u = C' x u) (hF : ∀ f ∈ F, ∀ u ≤ t, C f u = C' f u) :
    filterRound E C t θ Q F len = filterRound E C' t θ Q F len := by
  classical
  unfold filterRound
  congr 1
  exact Finset.filter_congr fun x hx =>
    not_congr (covered_congr E t θ C C' F x len hF (hQ x hx))

end Cover

section Merge

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (t : ℕ) (θ : ℝ) (R : ℕ)

omit [Fintype ι] in
theorem mstep_congr (C C' : ι → ℕ → ℝ) (Q : Finset ι) (y : ι → Bool)
    (hQ : ∀ x ∈ Q, ∀ u ≤ t, C x u = C' x u) :
    mstep E C t θ R Q y = mstep E C' t θ R Q y := by
  unfold mstep
  exact filterRound_congr E t θ C C' Q (Fof Q y) R hQ
    (fun f hf => hQ f (Finset.mem_filter.1 hf).1)

theorem iter_congr (C C' : ι → ℕ → ℝ) (Q : Finset ι) (hQ : ∀ x ∈ Q, ∀ u ≤ t, C x u = C' x u) :
    ∀ (K : ℕ) (φ : Fin K → ι → Bool),
      iter (mstep E C t θ R) Q K φ = iter (mstep E C' t θ R) Q K φ := by
  intro K
  induction K with
  | zero => intro φ; rfl
  | succ K ih =>
    intro φ
    simp only [iter]
    rw [ih (Fin.init φ)]
    exact mstep_congr E t θ R C C' _ _ fun x hx =>
      hQ x (iter_sub (mstep E C' t θ R) Q (fun Q' y => mstep_sub E C' t θ R Q' y) K _ hx)

variable (K : ℕ)

theorem mergeOne_congr (C C' : ι → ℕ → ℝ) (φ : ℕ → ℕ → Fin K → ι → Bool) (a ℓ : ℕ)
    (P : ℕ → Finset ι) (hP : ∀ j, ∀ x ∈ P j, ∀ u ≤ a + 1, C x u = C' x u) :
    mergeOne E C θ R K φ a ℓ P = mergeOne E C' θ R K φ a ℓ P := by
  unfold mergeOne
  rw [iter_congr E (a + 1) θ R C C' _ (fun x hx => by
    rcases Finset.mem_union.1 hx with h | h
    · exact hP _ x h
    · exact hP _ x h)]

theorem mergeUpTo_congr (C C' : ι → ℕ → ℝ) (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ)
    (P : ℕ → Finset ι) (hP : ∀ j, ∀ x ∈ P j, ∀ u ≤ a + 1, C x u = C' x u) :
    ∀ m, mergeUpTo E C θ R K φ a m P = mergeUpTo E C' θ R K φ a m P := by
  intro m
  induction m with
  | zero => exact mergeOne_congr E θ R K C C' φ a 0 P hP
  | succ m ih =>
    simp only [mergeUpTo]
    rw [ih]
    apply mergeOne_congr
    intro j x hx u hu
    obtain ⟨⟨j', hj'⟩, -⟩ := mem_mergeUpTo m P j x hx
    exact hP j' x hj' u hu

variable (lev : ℕ → ℕ)

/-- Every copy in a sub-pool was sampled. -/
theorem mem_pools_sampled (C : ι → ℕ → ℝ) (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) :
    ∀ a ℓ x, x ∈ pools E C θ R K lev ωs φ a ℓ → ωs x = true := by
  intro a
  induction a with
  | zero => intro ℓ x hx; simp [pools] at hx
  | succ a ih =>
    intro ℓ x hx
    simp only [pools] at hx
    obtain ⟨⟨j', hj'⟩, -⟩ := mem_mergeUpTo _ _ ℓ x hx
    by_cases hj : j' = 0
    · subst hj
      rw [Function.update_self] at hj'
      rcases Finset.mem_union.1 hj' with h | h
      · exact ih 0 x h
      · simp only [newAt, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact h.2
    · rw [Function.update_of_ne hj] at hj'
      exact ih j' x hj'

/-- **Causality of the sub-pool process:** the pools after epoch `a` read the data of the sampled
copies only at times `≤ a`. -/
theorem pools_congr (C C' : ι → ℕ → ℝ) (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) :
    ∀ a, (∀ x, ωs x = true → ∀ u ≤ a, C x u = C' x u) →
      pools E C θ R K lev ωs φ a = pools E C' θ R K lev ωs φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    simp only [pools]
    rw [ih (fun x hx u hu => h x hx u (by omega))]
    refine mergeUpTo_congr E θ R K C C' φ a _ ?_ (lev a)
    intro j x hx u hu
    apply h x _ u hu
    by_cases hj : j = 0
    · subst hj
      rw [Function.update_self] at hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact mem_pools_sampled E θ R K lev C' ωs φ a 0 x hx
      · simp only [newAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact hx.2
    · rw [Function.update_of_ne hj] at hx
      exact mem_pools_sampled E θ R K lev C' ωs φ a j x hx

/-- **Non-interference with data agreeing off the copy** (sub-pool process, all-slots version). -/
theorem pools_erase_congr (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false)
    (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (hφ : ∀ a ℓ k, φ a ℓ k c = false)
    (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) (C C' : ι → ℕ → ℝ) (a : ℕ)
    (hC : ∀ x, x ≠ c → ∀ u ≤ a, C x u = C' x u) (ℓ : ℕ) :
    (pools E C θ R K lev ωs φ a ℓ).erase c = pools E C' θ R K lev ωs' φ' a ℓ := by
  rw [pools_erase E C θ R K lev c ωs ωs' hs hs' φ φ' hφ hφ' a ℓ,
    pools_congr E θ R K lev C C' ωs' φ' a (fun x hx u hu => hC x (by
      rintro rfl; rw [hs'] at hx; exact Bool.false_ne_true hx) u hu)]

/-- **Slot-restricted version** (`Pool.P0052.pools_erase_of_passive`) with each run's own data. -/
theorem pools_erase_of_passive_congr (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs')
    (hs' : ωs' c = false) (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (C C' : ι → ℕ → ℝ)
    (hp : PassiveRun E C θ R K lev c ωs φ) (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) (a : ℕ)
    (hC : ∀ x, x ≠ c → ∀ u ≤ a, C x u = C' x u) (ℓ : ℕ) :
    (pools E C θ R K lev ωs φ a ℓ).erase c = pools E C' θ R K lev ωs' φ' a ℓ := by
  rw [pools_erase_of_passive E C θ R K lev c ωs ωs' hs hs' φ φ' hp hφ' a ℓ,
    pools_congr E θ R K lev C C' ωs' φ' a (fun x hx u hu => hC x (by
      rintro rfl; rw [hs'] at hx; exact Bool.false_ne_true hx) u hu)]

end Merge

section Threads

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ)

/-- Every copy at the start of a unit (after inheritance and sampling) is sampled, if every copy of
the boundary pools is. -/
theorem mem_startPools_sampled (ωs : ι → Bool) (a : ℕ) (P : ℕ → ℕ → Finset ι)
    (hP : ∀ r ℓ x, x ∈ P r ℓ → ωs x = true) :
    ∀ r ℓ x, x ∈ startPools E thr0 D Lv Bt ωs a P r ℓ → ωs x = true := by
  intro r ℓ x hx
  unfold startPools sample at hx
  have hinh : ∀ r ℓ, x ∈ inherit D Lv Bt a P r ℓ → ωs x = true := by
    intro r ℓ h
    unfold inherit at h
    split_ifs at h with h1 h2 h3
    · exact hP r ℓ x h
    · rcases Finset.mem_union.1 h with h | h
      · exact hP r 0 x h
      · simp only [Finset.mem_biUnion, Finset.mem_Ioo, Finset.mem_range] at h
        obtain ⟨r', -, ℓ', -, h⟩ := h
        exact hP r' ℓ' x h
    · exact hP r ℓ x h
    · simp at h
  split_ifs at hx with hs
  · rcases Finset.mem_union.1 hx with h | h
    · exact hinh r 0 h
    · simp only [newAtT, Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h.2.2
  · exact hinh r ℓ hx

/-- Every copy of the threaded process was sampled. -/
theorem mem_tpools_sampled (C : ι → ℕ → ℝ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) :
    ∀ a r ℓ x, x ∈ tpools E thr0 C θ R K D Lv Bt lev ωs φ a r ℓ → ωs x = true := by
  intro a
  induction a with
  | zero => intro r ℓ x hx; simp [tpools] at hx
  | succ a ih =>
    intro r ℓ x hx
    simp only [tpools] at hx
    have hS := mem_startPools_sampled E thr0 D Lv Bt ωs a _ ih r
    split_ifs at hx with hB
    · obtain ⟨⟨j', hj'⟩, -⟩ := mem_mergeUpTo _ _ ℓ x hx
      exact hS j' x hj'
    · exact hS ℓ x hx

/-- **Causality of the threaded process:** the pools at the boundary `a` read the data of the
sampled copies only at times `≤ a`. -/
theorem tpools_congr (C C' : ι → ℕ → ℝ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) :
    ∀ a, (∀ x, ωs x = true → ∀ u ≤ a, C x u = C' x u) →
      tpools E thr0 C θ R K D Lv Bt lev ωs φ a = tpools E thr0 C' θ R K D Lv Bt lev ωs φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have hprev := ih (fun x hx u hu => h x hx u (by omega))
    funext r
    simp only [tpools]
    rw [hprev]
    split_ifs with hB
    · refine mergeUpTo_congr E θ R K C C' (φ r) a _ ?_ (lev r a)
      intro j x hx u hu
      exact h x (mem_startPools_sampled E thr0 D Lv Bt ωs a _
        (mem_tpools_sampled E thr0 θ R K D Lv Bt lev C' ωs φ a) r j x hx) u hu
    · rfl

/-- **Non-interference of a never-filter copy, with data agreeing off the copy up to the current
time** (all-slots version of `Pool.P0065.tpools_erase`, each run with its own data). -/
theorem tpools_erase_congr (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false)
    (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool) (hφ : ∀ r a ℓ k, φ r a ℓ k c = false)
    (hφ' : ∀ r a ℓ k, AgreeOff c (φ r a ℓ k) (φ' r a ℓ k)) (C C' : ι → ℕ → ℝ) (a : ℕ)
    (hC : ∀ x, x ≠ c → ∀ u ≤ a, C x u = C' x u) (r ℓ : ℕ) :
    (tpools E thr0 C θ R K D Lv Bt lev ωs φ a r ℓ).erase c =
      tpools E thr0 C' θ R K D Lv Bt lev ωs' φ' a r ℓ := by
  rw [tpools_erase c ωs ωs' hs hs' φ φ' hφ hφ' a r ℓ,
    tpools_congr E thr0 θ R K D Lv Bt lev C C' ωs' φ' a (fun x hx u hu => hC x (by
      rintro rfl; rw [hs'] at hx; exact Bool.false_ne_true hx) u hu)]

/-- `Pool.P0065.forced_erase` with each run's own data: the forced run (data `C`) is the copy-free
run (data `C'`) plus the copy, as long as the data agree off the copy up to the boundary. -/
theorem forced_erase_congr {c : ι} {ωs : ι → Bool} (hc : ωs c = false)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (C C' : ι → ℕ → ℝ) (a : ℕ)
    (hC : ∀ x, x ≠ c → ∀ u ≤ a, C x u = C' x u) (r ℓ : ℕ) :
    (tpools E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) a r ℓ).erase c =
      tpools E thr0 C' θ R K D Lv Bt lev ωs φ a r ℓ := by
  rw [forced_erase hc φ a r ℓ,
    tpools_congr E thr0 θ R K D Lv Bt lev C C' ωs φ a (fun x hx u hu => hC x (by
      rintro rfl; rw [hc] at hx; exact Bool.false_ne_true hx) u hu)]

/-- The start-of-unit pools of the forced run are those of the copy-free run plus the copy, each run
with its own data agreeing off the copy up to the boundary. -/
theorem forced_erase_start_congr {c : ι} {ωs : ι → Bool} (hc : ωs c = false)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (C C' : ι → ℕ → ℝ) (a : ℕ)
    (hC : ∀ x, x ≠ c → ∀ u ≤ a, C x u = C' x u) (r ℓ : ℕ) :
    (startPools E thr0 D Lv Bt (forceS ωs c) a
        (tpools E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) a) r ℓ).erase c =
      startPools E thr0 D Lv Bt ωs a (tpools E thr0 C' θ R K D Lv Bt lev ωs φ a) r ℓ := by
  rw [forced_erase_start hc φ a r ℓ,
    tpools_congr E thr0 θ R K D Lv Bt lev C C' ωs φ a (fun x hx u hu => hC x (by
      rintro rfl; rw [hc] at hx; exact Bool.false_ne_true hx) u hu)]

/-- **Slot-restricted version** (`Pool.P0081.tpools_erase_of_slots`) with each run's own data:
`c`'s filter bits need only be `false` at its thread-merge slots.

Caution: `hφ` quantifies over **every** unit `x`. For a copy that survives forever its slot set is
infinite, so under independent Bernoulli(`q > 0`) filter bits this hypothesis has probability `0`.
The version to use as a probabilistic opportunity is the horizon version
`Pool.P0083.tpools_erase_of_slots_lt_congr`. -/
theorem tpools_erase_of_slots_congr (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs')
    (hs' : ωs' c = false) (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool) (C C' : ι → ℕ → ℝ)
    (hφ : ∀ x ℓ k, Pool.P0081.InSlotsT E thr0 D Bt lev c x ℓ →
      φ (curT E thr0 D Bt c x) x ℓ k c = false)
    (hφ' : ∀ r a ℓ k, AgreeOff c (φ r a ℓ k) (φ' r a ℓ k)) (a : ℕ)
    (hC : ∀ x, x ≠ c → ∀ u ≤ a, C x u = C' x u) (r ℓ : ℕ) :
    (tpools E thr0 C θ R K D Lv Bt lev ωs φ a r ℓ).erase c =
      tpools E thr0 C' θ R K D Lv Bt lev ωs' φ' a r ℓ := by
  rw [Pool.P0081.tpools_erase_of_slots c ωs ωs' hs hs' φ φ' hφ hφ' a r ℓ,
    tpools_congr E thr0 θ R K D Lv Bt lev C C' ωs' φ' a (fun x hx u hu => hC x (by
      rintro rfl; rw [hs'] at hx; exact Bool.false_ne_true hx) u hu)]

/-- Horizon version (`Pool.P0081.tpools_erase_of_slots_lt`): `c`'s bits are `false` at its slots
before unit `N`, and the conclusion holds at every boundary `a ≤ N`. -/
theorem tpools_erase_of_slots_lt_congr (N : ℕ) (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs')
    (hs' : ωs' c = false) (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool) (C C' : ι → ℕ → ℝ)
    (hφ : ∀ x ℓ k, x < N → Pool.P0081.InSlotsT E thr0 D Bt lev c x ℓ →
      φ (curT E thr0 D Bt c x) x ℓ k c = false)
    (hφ' : ∀ r a ℓ k, AgreeOff c (φ r a ℓ k) (φ' r a ℓ k)) (a : ℕ) (haN : a ≤ N)
    (hC : ∀ x, x ≠ c → ∀ u ≤ a, C x u = C' x u) (r ℓ : ℕ) :
    (tpools E thr0 C θ R K D Lv Bt lev ωs φ a r ℓ).erase c =
      tpools E thr0 C' θ R K D Lv Bt lev ωs' φ' a r ℓ := by
  rw [Pool.P0081.tpools_erase_of_slots_lt N c ωs ωs' hs hs' φ φ' hφ hφ' a haN r ℓ,
    tpools_congr E thr0 θ R K D Lv Bt lev C C' ωs' φ' a (fun x hx u hu => hC x (by
      rintro rfl; rw [hs'] at hx; exact Bool.false_ne_true hx) u hu)]

/-- Sanity check: the data of the two runs may differ arbitrarily at the copy itself and after the
boundary; here the copy-free run uses data that are `0` for the copy and shifted by `1` after `a`. -/
example {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (C : ι → ℕ → ℝ) (a r ℓ : ℕ) :
    (tpools E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) a r ℓ).erase c =
      tpools E thr0 (fun x u => if x = c then 0 else if u ≤ a then C x u else C x u + 1)
        θ R K D Lv Bt lev ωs φ a r ℓ :=
  forced_erase_congr E thr0 θ R K D Lv Bt lev hc φ C _ a
    (fun x hx u hu => by simp [hx, hu]) r ℓ

end Threads

end Pool.P0083
