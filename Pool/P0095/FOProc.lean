import Pool.P0083.Congr

/-!
# The one-free-observation threaded pool process, and the pathwise copy-last coupling

The K-query threaded process `Pool.P0065.tpools` reads exact cover data `C : ι → ℕ → ℝ`. A learner with **one free
observation per unit** (the two-query model, P0022 §2, `Pool.P0027.PlayBlindLearners`) instead observes the copy in
one slot `y ∈ Fin s` of its start pools and keeps importance-weighted estimates: the observed copy's estimate grows by
`s · (its loss)`. This file defines that process for an arbitrary **occupancy rule**
`occ : Finset ι → Fin s → Option ι` (which member sits in which slot), and proves two things:

* **Identification** (`Pool.P0095.foRun_pools_eq`): its pools are exactly P0065's `tpools` run on the realized
  estimates `Pool.P0095.Chat` (the estimate history). So every pathwise statement about `tpools` with arbitrary data
  applies to it. The proof uses causality (`Pool.P0083.mergeUpTo_congr`) and the fact that past estimates are never
  changed (`Pool.P0095.est_frozen`).
* **Pathwise copy-last coupling** (`Pool.P0095.fo_forced_erase`): with the copy-last rule `Pool.P0095.occLast c`, the
  run with a never-filter copy `c` forced in (P0065's `forceS`/`forceF`) and the copy-free run, both driven by the same
  slot coins `y`, have the same pools up to `c`, and the same estimates for every copy other than `c`, at every
  boundary. This is the hypothesis `hC` that P0083's `*_erase_congr` theorems take as an assumption, now proved for
  this estimator (`Pool.P0095.fo_hC`).
* In the copy-free run the copy-last rule is the entry-order rule `Pool.P0095.occSort` (`Pool.P0095.occLast_of_not_mem`,
  `Pool.P0095.foRun_free_eq`): the copy-free run of the coupling is the actual algorithm's run.

The actual algorithm with the copy present uses `occSort`, not `occLast c`. Relating the two forced runs in law would
use P0070's slot coupling (`Pool.P0070.sum_run_slots`), which needs `Pool.P0070.Compat` (both rules show the same set of
occupants). That holds only when the start-pool members fit in the `s` slots (no overflow); with more members than
slots the two rules observe different copies (e.g. `s = 1`, members `{0,1}`, `c = 0`). So that law transfer needs a cap
`|members| ≤ s` (or a no-overflow event) and is not done here. "No cap needed" refers only to the pathwise coupling.
Nothing here is probabilistic, and nothing here bounds an estimation error.

**Scope of the estimator.** The increment `s · L a x` is an importance-weighted (unbiased) estimate of a copy's loss
only for copies that hold one of the `s` slots. On overflow, members of entry rank `≥ s` (and `c` under `occLast c`
once the other members fill the slots) are never observed, so their estimates are frozen and biased. Likewise only
copies at threads `< D` and levels `< Lv` are members; since merges write level `lev r a + 1`, downstream uses need
`lev r a + 1 < Lv` (and `|members| ≤ s`) for every pool copy to be observable. The theorems below are pathwise and
need neither condition.

The per-unit loss `L u x` of copy `x` is an arbitrary real (e.g. its arm's loss bit, or a block average).
-/

open Finset Pool.P0030 Pool.P0034 Pool.P0042 Pool.P0052 Pool.P0065

namespace Pool.P0095

section Occ

variable {ι : Type*} [LinearOrder ι] (s : ℕ)

/-- Entry-order occupancy: slot `y` holds the `y`-th smallest member, if any. -/
def occSort (V : Finset ι) (y : Fin s) : Option ι :=
  if h : y.1 < (V.sort (· ≤ ·)).length then some ((V.sort (· ≤ ·))[y.1]) else none

/-- Copy-last occupancy: the members other than `c` in entry order, then `c` (if it is a member). -/
def occLast (c : ι) (V : Finset ι) (y : Fin s) : Option ι :=
  if h : y.1 < ((V.erase c).sort (· ≤ ·)).length then some (((V.erase c).sort (· ≤ ·))[y.1])
  else if y.1 = ((V.erase c).sort (· ≤ ·)).length ∧ c ∈ V then some c else none

/-- Without the copy, the copy-last rule is the entry-order rule. -/
theorem occLast_of_not_mem {c : ι} {V : Finset ι} (hc : c ∉ V) : occLast s c V = occSort s V := by
  funext y
  unfold occLast occSort
  rw [Finset.erase_eq_of_notMem hc]
  split_ifs with h1 h2
  · rfl
  · exact absurd h2.2 hc
  · rfl

/-- **Key property of the copy-last rule.** A copy other than `c` sits in the same slot whether or not `c` is a
member. -/
theorem occLast_erase (c : ι) (V : Finset ι) (y : Fin s) {x : ι} (hx : x ≠ c) :
    occLast s c V y = some x ↔ occLast s c (V.erase c) y = some x := by
  unfold occLast
  rw [Finset.erase_idem]
  by_cases h1 : y.1 < ((V.erase c).sort (· ≤ ·)).length
  · simp only [dif_pos h1]
  · simp only [dif_neg h1]
    have hR : ¬ (y.1 = ((V.erase c).sort (· ≤ ·)).length ∧ c ∈ V.erase c) :=
      fun h => Finset.notMem_erase c V h.2
    simp only [hR, ite_false, reduceCtorEq, iff_false]
    by_cases h2 : y.1 = ((V.erase c).sort (· ≤ ·)).length ∧ c ∈ V
    · simp only [h2, and_self, ite_true, Option.some.injEq]
      exact fun h => hx h.symm
    · rw [if_neg h2]; simp

end Occ

section Proc

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ)

/-- The copies in the start pools (threads `< D`, levels `< Lv`). Copies at levels `≥ Lv` (possible when
`lev r a + 1 ≥ Lv`) are not members and are never observed. -/
def members (P : ℕ → ℕ → Finset ι) : Finset ι :=
  (Finset.range D).biUnion fun r => (Finset.range Lv).biUnion (P r)

theorem members_erase (c : ι) (P : ℕ → ℕ → Finset ι) :
    (members D Lv P).erase c = members D Lv (fun r ℓ => (P r ℓ).erase c) := by
  ext x
  simp only [members, Finset.mem_erase, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨hx, r, hr, ℓ, hℓ, h⟩; exact ⟨r, hr, ℓ, hℓ, hx, h⟩
  · rintro ⟨r, hr, ℓ, hℓ, hx, h⟩; exact ⟨hx, r, hr, ℓ, hℓ, h⟩

/-- State of the process at a boundary: the pools and the estimate history (`est x t` = estimated loss of `x`
before unit `t`; only `t ≤` the current boundary is meaningful). -/
structure FOSt (ι : Type*) where
  pools : ℕ → ℕ → Finset ι
  est : ι → ℕ → ℝ

/-- Estimate update after unit `a`, in which slot `o` was observed: the history up to `a` is kept, and the observed
copy's estimate grows by `s · L a x` at time `a + 1`. -/
def estStep (a : ℕ) (o : Option ι) (est : ι → ℕ → ℝ) : ι → ℕ → ℝ :=
  fun x t => if t ≤ a then est x t else est x a + (if o = some x then (s : ℝ) * L a x else 0)

/-- **The one-free-observation threaded process.** In unit `a`: inheritance and sampling (`startPools`), then the
occupant of slot `y a` of the start pools is observed and the estimates are updated, then every thread whose epoch
ends at `a + 1` merges (P0052's `mergeUpTo`) with the updated estimates as cover data. -/
noncomputable def foRun (occ : Finset ι → Fin s → Option ι) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s) : ℕ → FOSt ι
  | 0 => ⟨fun _ _ => ∅, fun _ _ => 0⟩
  | a + 1 =>
    ⟨fun r => if Bt r ∣ a + 1 then
        mergeUpTo E (estStep s L a (occ (members D Lv (startPools E thr0 D Lv Bt ωs a
          (foRun occ ωs φ y a).pools)) (y a)) (foRun occ ωs φ y a).est) θ R K (φ r) a (lev r a)
          (startPools E thr0 D Lv Bt ωs a (foRun occ ωs φ y a).pools r)
      else startPools E thr0 D Lv Bt ωs a (foRun occ ωs φ y a).pools r,
     estStep s L a (occ (members D Lv (startPools E thr0 D Lv Bt ωs a (foRun occ ωs φ y a).pools)) (y a))
       (foRun occ ωs φ y a).est⟩

/-- The slot observed in unit `a`. -/
noncomputable def obsAt (occ : Finset ι → Fin s → Option ι) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s) (a : ℕ) : Option ι :=
  occ (members D Lv (startPools E thr0 D Lv Bt ωs a
    (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).pools)) (y a)

/-- The realized estimate history: the estimate of `x` before unit `t`, as computed at boundary `t`. -/
noncomputable def Chat (occ : Finset ι → Fin s → Option ι) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s) (x : ι) (t : ℕ) : ℝ :=
  (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y t).est x t

variable (occ : Finset ι → Fin s → Option ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
  (y : ℕ → Fin s)

theorem foRun_succ_est (a : ℕ) :
    (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y (a + 1)).est =
      estStep s L a (obsAt E thr0 θ R K D Lv Bt lev s L occ ωs φ y a)
        (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).est := rfl

theorem foRun_succ_pools (a r : ℕ) :
    (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y (a + 1)).pools r =
      if Bt r ∣ a + 1 then
        mergeUpTo E (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y (a + 1)).est θ R K (φ r) a (lev r a)
          (startPools E thr0 D Lv Bt ωs a (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).pools r)
      else startPools E thr0 D Lv Bt ωs a (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).pools r := rfl

/-- **Past estimates are never changed.** -/
theorem est_frozen (x : ι) {t : ℕ} : ∀ a, t ≤ a →
    (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).est x t = Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y x t := by
  intro a
  induction a with
  | zero => intro h; rw [Nat.le_zero.mp h]; rfl
  | succ a ih =>
    intro h
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [foRun_succ_est]
      simp only [estStep, show t ≤ a by omega, if_true]
      exact ih (by omega)
    · subst h; rfl

/-- The estimate increment of unit `a`. -/
theorem Chat_succ (x : ι) (a : ℕ) :
    Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y x (a + 1) =
      Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y x a +
        (if obsAt E thr0 θ R K D Lv Bt lev s L occ ωs φ y a = some x then (s : ℝ) * L a x else 0) := by
  show (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y (a + 1)).est x (a + 1) = _
  rw [foRun_succ_est]
  simp only [estStep, show ¬ (a + 1 ≤ a) by omega, if_false]
  rw [est_frozen E thr0 θ R K D Lv Bt lev s L occ ωs φ y x a le_rfl]

/-- **Identification.** The pools of the one-free-observation process are P0065's threaded pools on the realized
estimates. -/
theorem foRun_pools_eq : ∀ a,
    (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).pools =
      tpools E thr0 (Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y) θ R K D Lv Bt lev ωs φ a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    funext r
    show (if Bt r ∣ a + 1 then _ else _) = _
    simp only [tpools]
    rw [← ih]
    split_ifs with hB
    · refine Pool.P0083.mergeUpTo_congr E θ R K _ _ (φ r) a _ (fun j x _ u hu => ?_) (lev r a)
      exact est_frozen E thr0 θ R K D Lv Bt lev s L occ ωs φ y x (a + 1) hu
    · rfl

/-- The estimate history agrees with `Chat` at every time up to the boundary. -/
theorem est_eq_Chat (a : ℕ) (x : ι) (t : ℕ) (ht : t ≤ a) :
    (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).est x t = Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y x t :=
  est_frozen E thr0 θ R K D Lv Bt lev s L occ ωs φ y x a ht

end Proc

section Coupling

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ)

/-- **Pathwise copy-last coupling.** With the copy-last rule, the run with a never-filter copy `c` forced in and the
copy-free run (same sampling bits off `c`, same filter bits off `c`, same slot coins) have, at every boundary, the same
pools up to `c` and the same estimate history for every copy other than `c`. -/
theorem fo_forced_erase {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (y : ℕ → Fin s) : ∀ a,
      (∀ r ℓ, ((foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y a).pools r ℓ).erase c =
        (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a).pools r ℓ) ∧
      (∀ x, x ≠ c → ∀ t,
        (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y a).est x t =
          (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a).est x t) := by
  classical
  have hs : AgreeOff c (forceS ωs c) ωs := fun x hx => by simp [forceS, Function.update_of_ne hx]
  intro a
  induction a with
  | zero => exact ⟨fun r ℓ => by simp [foRun], fun x _ t => rfl⟩
  | succ a ih =>
    obtain ⟨hP, hE⟩ := ih
    have hPfun : (fun r ℓ => ((foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y
        a).pools r ℓ).erase c) = (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a).pools := by
      funext r ℓ; exact hP r ℓ
    -- start pools
    have hS : ∀ r ℓ, (startPools E thr0 D Lv Bt (forceS ωs c) a
        (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y a).pools r ℓ).erase c =
        startPools E thr0 D Lv Bt ωs a (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a).pools r ℓ := by
      intro r ℓ
      rw [startPools_erase c (forceS ωs c) ωs hs hc, hPfun]
    -- observation
    have hobs : ∀ x, x ≠ c →
        (obsAt E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y a = some x ↔
          obsAt E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a = some x) := by
      intro x hx
      unfold obsAt
      rw [occLast_erase s c _ (y a) hx, members_erase]
      have : (fun r ℓ => (startPools E thr0 D Lv Bt (forceS ωs c) a
          (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y a).pools r ℓ).erase c) =
          startPools E thr0 D Lv Bt ωs a (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a).pools := by
        funext r ℓ; exact hS r ℓ
      rw [this]
    -- estimates
    have hE' : ∀ x, x ≠ c → ∀ t,
        (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y (a + 1)).est x t =
          (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y (a + 1)).est x t := by
      intro x hx t
      rw [foRun_succ_est, foRun_succ_est]
      simp only [estStep]
      by_cases h1 : t ≤ a
      · simp only [h1, ite_true]; exact hE x hx t
      · simp only [h1, ite_false]
        rw [hE x hx a]
        by_cases h2 : obsAt E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a = some x
        · rw [if_pos ((hobs x hx).mpr h2), if_pos h2]
        · rw [if_neg (fun h => h2 ((hobs x hx).mp h)), if_neg h2]
    refine ⟨fun r ℓ => ?_, fun x hx t => hE' x hx t⟩
    rw [foRun_succ_pools, foRun_succ_pools]
    split_ifs with hB
    · rw [mergeUpTo_erase E _ θ R K c (forceF K φ c r) (φ r)
        (fun a ℓ k => by simp [forceF]) (fun a ℓ k x hx => by simp [forceF, hx]) a,
        show (fun i => (startPools E thr0 D Lv Bt (forceS ωs c) a
          (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y a).pools r i).erase c) =
          startPools E thr0 D Lv Bt ωs a (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a).pools r
          from funext fun i => hS r i]
      refine congrFun (Pool.P0083.mergeUpTo_congr E θ R K _ _ (φ r) a _ (fun j x hx u _ => ?_) (lev r a)) ℓ
      have hxc : x ≠ c := by
        intro hxc'
        rw [hxc', ← hS r j] at hx
        exact Finset.notMem_erase c _ hx
      exact hE' x hxc u
    · exact hS r ℓ

/-- The hypothesis `hC` of P0083's `*_erase_congr` theorems, for this estimator: the realized estimate histories of
the forced run and of the copy-free run agree off `c` at every time. -/
theorem fo_hC {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (y : ℕ → Fin s) (x : ι) (hx : x ≠ c) (t : ℕ) :
    Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y x t =
      Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y x t :=
  (fo_forced_erase E thr0 θ R K D Lv Bt lev s L hc φ y t).2 x hx t

/-- The copy-free run never contains the copy, so its start pools' members never contain it. -/
theorem not_mem_members_free {c : ι} {ωs : ι → Bool} (hc : ωs c = false)
    (occ : Finset ι → Fin s → Option ι) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s) (a : ℕ) :
    c ∉ members D Lv (startPools E thr0 D Lv Bt ωs a (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a).pools) := by
  intro h
  simp only [members, Finset.mem_biUnion, Finset.mem_range] at h
  obtain ⟨r, -, ℓ, -, h⟩ := h
  have := Pool.P0083.mem_startPools_sampled E thr0 D Lv Bt ωs a _ (by
    rw [foRun_pools_eq]
    exact Pool.P0083.mem_tpools_sampled E thr0 θ R K D Lv Bt lev _ ωs φ a) r ℓ c h
  rw [hc] at this; exact Bool.false_ne_true this

/-- **The copy-free run of the coupling is the actual algorithm's run:** without the copy, the copy-last rule and the
entry-order rule give the same run. -/
theorem foRun_free_eq {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (y : ℕ → Fin s) : ∀ a,
    foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a =
      foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    have hocc : occLast s c (members D Lv (startPools E thr0 D Lv Bt ωs a
        (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a).pools)) =
        occSort s (members D Lv (startPools E thr0 D Lv Bt ωs a
          (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y a).pools)) :=
      occLast_of_not_mem s (not_mem_members_free E thr0 θ R K D Lv Bt lev s L hc _ φ y a)
    show FOSt.mk _ _ = FOSt.mk _ _
    rw [hocc, ih]

end Coupling

end Pool.P0095
