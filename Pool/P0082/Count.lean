import Pool.P0081.Threads
import Pool.P0048.Forced

/-!
# Bad-epoch counting for the threaded process (P0048's forced insertion + P0081's clock slots)

* `iter_congr_on`, `tpools_congr_slots`: changing copy `c`'s filter bits outside its clock slots
  (P0081's `InSlotsT`, thread `curT c x`) does not change the run, even with `c` present (P0081's
  `tpools_erase_of_slots` compares with the run WITHOUT `c`).

* Coins indexed by (slot, copy): `SlotC` (same shape as P0073's `SlotT`), readings `ωsC`, `φC`
  (`coinFintype`: the coin space is finite; a local instance).
* `oppSet c`, `oppVal`: copy `c`'s opportunity, its sampling bit set to `true` and its filter bits on
  its clock slots set to `false` (a fixed-coordinate event, as P0048 needs).
* `tpools_force_eq`: the run of P0048's `force` on the opportunity equals P0065's forced run
  (`forceS`/`forceF`, filter bits false everywhere), by `tpools_congr_slots`.
* `card_alive_le`, `bad_imp_surv`, and **`count_bad`**: `E[#bad] ≤ D·Lv·S/π + D·NE·P(not good)`, where
  opportunity `(j, a)` is bad when `cstar j a` is not actually sampled and P0065's `evict … j a = none`.
-/

namespace Pool.P0082

open Pool.P0065 Pool.P0081 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0048

/-- Slots of the coin array (same shape as P0073's `SlotT`). -/
abbrev SlotC (NE D Lt K : ℕ) := Fin NE ⊕ (Fin NE × Fin D × Fin (Lt + 1) × Fin K)

/-- The coin space is finite (the nesting is too deep for default instance search). -/
noncomputable def coinFintype (NE D Lt K : ℕ) (ι : Type) [DecidableEq ι] [Fintype ι] :
    Fintype (SlotC NE D Lt K × ι → Bool) :=
  @Pi.instFintype _ _ instDecidableEqProd inferInstance (fun _ => inferInstance)

attribute [local instance] coinFintype

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {C : ι → ℕ → ℝ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ} {NE Lt : ℕ}

/-- Merge iterations read the filter bits only on their input. -/
theorem iter_congr_on {t : ℕ} : ∀ (m : ℕ) (Q : Finset ι) (φ φ' : Fin m → ι → Bool),
    (∀ k, ∀ d ∈ Q, φ k d = φ' k d) → iter (mstep E C t θ R) Q m φ = iter (mstep E C t θ R) Q m φ'
  | 0, _, _, _, _ => rfl
  | m + 1, Q, φ, φ', h => by
    simp only [iter]
    rw [iter_congr_on m Q (Fin.init φ) (Fin.init φ') (fun k d hd => h _ d hd)]
    unfold mstep
    congr 1
    ext d
    simp only [Fof, Finset.mem_filter]
    constructor
    · rintro ⟨hd, h1⟩
      refine ⟨hd, ?_⟩
      have hdQ := iter_sub (mstep E C t θ R) Q (mstep_sub E C t θ R) m _ hd
      rw [← h _ d hdQ]; exact h1
    · rintro ⟨hd, h1⟩
      refine ⟨hd, ?_⟩
      have hdQ := iter_sub (mstep E C t θ R) Q (mstep_sub E C t θ R) m _ hd
      rw [h _ d hdQ]; exact h1

/-- **Non-interference outside the clock slots** (both runs contain `c`): if two filter-bit arrays
differ only at copy `c`'s bits on merges `(x, r, ℓ)` that are not its clock slots (P0081's
`InSlotsT`, with `r = curT c x`), the two runs coincide. -/
theorem tpools_congr_slots (ωs : ι → Bool) (c : ι) (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (h : ∀ r x ℓ k d, φ r x ℓ k d ≠ φ' r x ℓ k d →
      d = c ∧ ¬ (r = curT E thr0 D Bt c x ∧ InSlotsT E thr0 D Bt lev c x ℓ)) :
    ∀ a, tpools E thr0 C θ R K D Lv Bt lev ωs φ a = tpools E thr0 C θ R K D Lv Bt lev ωs φ' a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    funext r
    simp only [tpools]
    rw [← ih]
    split_ifs with hB
    · set S := startPools E thr0 D Lv Bt ωs a (tpools E thr0 C θ R K D Lv Bt lev ωs φ a) r
      have hm : ∀ m, m ≤ lev r a → mergeUpTo E C θ R K (φ r) a m S = mergeUpTo E C θ R K (φ' r) a m S := by
        intro m
        induction m with
        | zero =>
          intro hm0
          simp only [mergeUpTo, mergeOne]
          rw [iter_congr_on K _ (φ r a 0) (φ' r a 0) (fun k d hd => ?_)]
          by_contra hne
          obtain ⟨rfl, hns⟩ := h r a 0 k d hne
          exact hns (inSlotsT_of_mem_input (E := E) (thr0 := thr0) (C := C) (θ := θ) (R := R) (K := K) (D := D) (Lv := Lv) (Bt := Bt) (lev := lev) hB hm0 (by simpa [stage] using hd))
        | succ m ihm =>
          intro hm1
          simp only [mergeUpTo]
          rw [← ihm (by omega)]
          simp only [mergeOne]
          rw [iter_congr_on K _ (φ r a (m + 1)) (φ' r a (m + 1)) (fun k d hd => ?_)]
          by_contra hne
          obtain ⟨rfl, hns⟩ := h r a (m + 1) k d hne
          exact hns (inSlotsT_of_mem_input (E := E) (thr0 := thr0) (C := C) (θ := θ) (R := R) (K := K) (D := D) (Lv := Lv) (Bt := Bt) (lev := lev) hB hm1 (by simpa [stage] using hd))
      exact hm (lev r a) le_rfl
    · rfl

/-- Sampling coins read off a coin vector indexed by (slot, copy). -/
def ωsC (E : ι → ℕ) (NE D Lt K : ℕ) (ω : SlotC NE D Lt K × ι → Bool) (c : ι) : Bool :=
  if h : E c < NE then ω (Sum.inl ⟨E c, h⟩, c) else false

/-- Filter coins read off a coin vector indexed by (slot, copy). -/
def φC (NE D Lt K : ℕ) (ω : SlotC NE D Lt K × ι → Bool) (r x ℓ : ℕ) (k : Fin K) (c : ι) : Bool :=
  if h : x < NE ∧ r < D ∧ ℓ < Lt + 1 then ω (Sum.inr (⟨x, h.1⟩, ⟨r, h.2.1⟩, ⟨ℓ, h.2.2⟩, k), c) else false

open Classical in
/-- The coordinates of copy `c`'s opportunity: its sampling bit and its filter bits on its clock slots. -/
noncomputable def oppSet (E thr0 : ι → ℕ) (D : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (NE Lt K : ℕ)
    (c : ι) (hc : E c < NE) : Finset (SlotC NE D Lt K × ι) :=
  insert (Sum.inl ⟨E c, hc⟩, c)
    ((Finset.univ.filter fun s : Fin NE × Fin D × Fin (Lt + 1) × Fin K =>
        (s.2.1 : ℕ) = curT E thr0 D Bt c s.1 ∧ InSlotsT E thr0 D Bt lev c s.1 s.2.2.1).image
      fun s => (Sum.inr s, c))

/-- Values on the opportunity: sampling bit `true`, filter bits `false`. -/
def oppVal : SlotC NE D Lt K × ι → Bool
  | (Sum.inl _, _) => true
  | (Sum.inr _, _) => false


open Classical in
lemma mem_oppSet_inr {c : ι} {hc : E c < NE} {s : Fin NE × Fin D × Fin (Lt + 1) × Fin K} {d : ι} :
    (Sum.inr s, d) ∈ oppSet E thr0 D Bt lev NE Lt K c hc ↔
      d = c ∧ ((s.2.1 : ℕ) = curT E thr0 D Bt c s.1 ∧ InSlotsT E thr0 D Bt lev c s.1 s.2.2.1) := by
  unfold oppSet
  simp only [Finset.mem_insert, Prod.mk.injEq, reduceCtorEq, false_and, false_or, Finset.mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s', hs', h1, h2⟩
    cases h1; exact ⟨h2.symm, hs'⟩
  · rintro ⟨rfl, hs⟩; exact ⟨s, hs, rfl, rfl⟩

open Classical in
lemma mem_oppSet_inl {c : ι} {hc : E c < NE} {a : Fin NE} {d : ι} :
    (Sum.inl a, d) ∈ oppSet E thr0 D Bt lev NE Lt K c hc ↔ d = c ∧ a = ⟨E c, hc⟩ := by
  unfold oppSet
  simp only [Finset.mem_insert, Prod.mk.injEq, Sum.inl.injEq, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and, reduceCtorEq, false_and, exists_false, or_false]
  tauto

open Classical in
/-- **The P0048-forced run is P0065's forced run.** Forcing the opportunity coordinates of `c`
(sampling bit true, filter bits false on its clock slots) gives the same pools as P0065's
`forceS`/`forceF` (filter bits false everywhere). -/
theorem tpools_force_eq (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (c : ι) (hc : E c < NE) (ω : SlotC NE D Lt K × ι → Bool) :
    tpools E thr0 C θ R K D Lv Bt lev (ωsC E NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω))
        (φC NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω)) =
      tpools E thr0 C θ R K D Lv Bt lev (forceS (ωsC E NE D Lt K ω) c)
        (forceF K (φC NE D Lt K ω) c) := by
  set S := oppSet E thr0 D Bt lev NE Lt K c hc
  have hs : ωsC E NE D Lt K (force S oppVal ω) = forceS (ωsC E NE D Lt K ω) c := by
    funext d
    unfold ωsC forceS force
    by_cases hdc : d = c
    · subst hdc
      simp only [Function.update_self, dif_pos hc]
      rw [if_pos (mem_oppSet_inl.2 ⟨rfl, rfl⟩)]; rfl
    · rw [Function.update_of_ne hdc]
      split_ifs with h1 h2
      · exact absurd (mem_oppSet_inl.1 h2).1 hdc
      · rfl
      · rfl
  rw [hs]
  funext a
  refine tpools_congr_slots _ c _ _ (fun r x ℓ k d hne => ?_) a
  by_cases hdc : d = c
  · refine ⟨hdc, fun hin => hne ?_⟩
    subst hdc
    unfold φC forceF force
    simp only [if_true]
    split_ifs with h1 h2
    · rfl
    · exact absurd (mem_oppSet_inr.2 ⟨rfl, hin⟩) h2
    · rfl
  · exfalso
    apply hne
    simp only [φC, forceF, force, hdc, if_false]
    split_ifs with h1 h2
    · exact absurd (mem_oppSet_inr.1 h2).1 hdc
    · rfl
    · rfl



end Pool.P0082

namespace Pool.P0082

open Pool.P0065 Pool.P0081 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0048

attribute [local instance] coinFintype

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {C : ι → ℕ → ℝ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ} {NE Lt : ℕ}

/-- Copies alive at the boundary `x` lie in the sub-pools of threads `< D` and levels `< Lv`; with every
such sub-pool of size `≤ S`, at most `D·Lv·S` copies are alive. -/
lemma card_alive_le (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (x S : ℕ)
    (hsz : ∀ r < D, ∀ ℓ < Lv, (tpools E thr0 C θ R K D Lv Bt lev ωs φ x r ℓ).card ≤ S)
    (A : Finset ι) (hA : ∀ c ∈ A, ∃ r ℓ, c ∈ tpools E thr0 C θ R K D Lv Bt lev ωs φ x r ℓ) :
    A.card ≤ D * Lv * S := by
  classical
  set U := (Finset.range D).biUnion fun r => (Finset.range Lv).biUnion fun ℓ =>
    tpools E thr0 C θ R K D Lv Bt lev ωs φ x r ℓ
  have hsub : A ⊆ U := by
    intro c hc
    obtain ⟨r, ℓ, hm⟩ := hA c hc
    have hloc := tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (C := C) (θ := θ) (R := R)
      (lev := lev) hD hLv hlev ωs φ x c r ℓ hm
    simp only [U, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨r, hloc.2.2.2, ℓ, hloc.2.2.1, hm⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc ∑ r ∈ Finset.range D, ((Finset.range Lv).biUnion fun ℓ =>
        tpools E thr0 C θ R K D Lv Bt lev ωs φ x r ℓ).card
      ≤ ∑ _r ∈ Finset.range D, Lv * S := by
        refine Finset.sum_le_sum fun r hr => (Finset.card_biUnion_le).trans ?_
        calc ∑ ℓ ∈ Finset.range Lv, (tpools E thr0 C θ R K D Lv Bt lev ωs φ x r ℓ).card
            ≤ ∑ _ℓ ∈ Finset.range Lv, S :=
              Finset.sum_le_sum fun ℓ hℓ => hsz r (Finset.mem_range.1 hr) ℓ (Finset.mem_range.1 hℓ)
          _ = Lv * S := by simp
    _ = D * Lv * S := by simp; ring


open Classical in
/-- A bad opportunity in a good run gives a surviving forced copy in the P0048-forced run, whose
pools are at most one larger than the actual ones. -/
lemma bad_imp_surv (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (cstar : ℕ → ℕ → ι) {j a : ℕ} (hEc : E (cstar j a) < NE) (ha : a < NE)
    (ω : SlotC NE D Lt K × ι → Bool) (hc : ωsC E NE D Lt K ω (cstar j a) = false)
    (hev : evict E thr0 C θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) j a = none)
    (S : ℕ) (hgood : ∀ r < D, ∀ ℓ < Lv, (tpools E thr0 C θ R K D Lv Bt lev (ωsC E NE D Lt K ω)
      (φC NE D Lt K ω) NE r ℓ).card + 1 ≤ S) :
    (∃ r ℓ, cstar j a ∈ tpools E thr0 C θ R K D Lv Bt lev
      (ωsC E NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K (cstar j a) hEc) oppVal ω))
      (φC NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K (cstar j a) hEc) oppVal ω)) NE r ℓ) ∧
    ∀ r < D, ∀ ℓ < Lv, (tpools E thr0 C θ R K D Lv Bt lev
      (ωsC E NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K (cstar j a) hEc) oppVal ω))
      (φC NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K (cstar j a) hEc) oppVal ω)) NE r ℓ).card ≤ S := by
  rw [tpools_force_eq hD hLv hlev (cstar j a) hEc ω]
  refine ⟨?_, fun r hr ℓ hℓ => ?_⟩
  · unfold evict at hev
    split_ifs at hev with h
    push Not at h
    exact h NE ha le_rfl
  · have he := forced_erase (E := E) (thr0 := thr0) (C := C) (θ := θ) (R := R) (D := D) (Lv := Lv)
      (Bt := Bt) (lev := lev) hc (φC NE D Lt K ω) NE r ℓ
    have h1 := hgood r hr ℓ hℓ
    rw [← he] at h1
    set X := tpools E thr0 C θ R K D Lv Bt lev
      (forceS (ωsC E NE D Lt K ω) (cstar j a)) (forceF K (φC NE D Lt K ω) (cstar j a)) NE r ℓ
    by_cases hm : cstar j a ∈ X
    · have := Finset.card_erase_add_one hm; omega
    · rw [Finset.erase_eq_of_notMem hm] at h1; omega


set_option maxHeartbeats 2000000 in
open Classical Finset in
/-- **Bad-epoch counting for the threaded process** (in the style of P0071). Opportunity `(j, a)`
(thread `j`, unit `a < NE` on its grid) is bad when the comparator's copy `cstar j a` is not
actually sampled and, forced in as a never-filter copy, is never evicted before `NE`. If every
opportunity has probability at least `π`, then `E[#bad] ≤ D·Lv·S/π + D·NE·P(not good)`, where a run
is good when all its sub-pools at `NE` have at most `S - 1` copies. -/
theorem count_bad (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (p : SlotC NE D Lt K × ι → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (π : ℝ) (hπ : 0 < π)
    (hπ1 : π ≤ 1)
    (hpi : ∀ (j : Fin D) (a : Fin NE) (h : Bt j ∣ a),
      π ≤ piS p (oppSet E thr0 D Bt lev NE Lt K (cstar j a)
        (by rw [hE j a (by omega) h a.2]; exact a.2)) oppVal)
    (S : ℕ) :
    ∑ ω, wtv p ω * (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧
        ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 C θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ)
      ≤ (D * Lv * S : ℝ) / π + D * NE * ∑ ω, wtv p ω *
        (if ∀ r < D, ∀ ℓ < Lv, (tpools E thr0 C θ R K D Lv Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
            NE r ℓ).card + 1 ≤ S then 0 else 1) := by
  have hD := hB.hD
  have hEc : ∀ (ja : Fin D × Fin NE), Bt ja.1 ∣ ja.2 → E (cstar ja.1 ja.2) < NE := fun ja h => by
    rw [hE ja.1 ja.2 (by omega) h ja.2.2]; exact ja.2.2
  let run := fun ω : SlotC NE D Lt K × ι → Bool =>
    tpools E thr0 C θ R K D Lv Bt lev (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
  let Sop : Fin D × Fin NE → Finset (SlotC NE D Lt K × ι) := fun ja =>
    if h : Bt ja.1 ∣ ja.2 then oppSet E thr0 D Bt lev NE Lt K (cstar ja.1 ja.2) (hEc ja h) else ∅
  let Surv : Fin D × Fin NE → (SlotC NE D Lt K × ι → Bool) → Prop := fun ja ω =>
    Bt ja.1 ∣ ja.2 ∧ (∃ r ℓ, cstar ja.1 ja.2 ∈ run ω NE r ℓ) ∧
      ∀ r < D, ∀ ℓ < Lv, (run ω NE r ℓ).card ≤ S
  have hw : ∀ ω, 0 ≤ wtv p ω := wtv_nonneg hp0 hp1
  -- the cap
  have hcap : ∀ ω, (#{ja | EvS (Sop ja) oppVal ω ∧ Surv ja ω} : ℝ) ≤ D * Lv * S := by
    intro ω
    by_cases hne : ∃ ja, EvS (Sop ja) oppVal ω ∧ Surv ja ω
    · obtain ⟨ja0, -, -, -, hsz⟩ := hne
      have hinj : Set.InjOn (fun ja : Fin D × Fin NE => cstar ja.1 ja.2)
          ((Finset.univ.filter fun ja => EvS (Sop ja) oppVal ω ∧ Surv ja ω) : Set (Fin D × Fin NE)) := by
        rintro ⟨j, a⟩ hj1 ⟨j', a'⟩ hj2 heq
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj1 hj2
        simp only at heq
        have h1 := hE j a (by omega) hj1.2.1 a.2
        have h2 := hE j' a' (by omega) hj2.2.1 a'.2
        have h3 := hthr j a (by omega) hj1.2.1 a.2
        have h4 := hthr j' a' (by omega) hj2.2.1 a'.2
        rw [heq] at h1 h3
        ext <;> simp only <;> omega
      have himg := Finset.card_image_of_injOn hinj
      have hA := card_alive_le hD hLv hlev _ _ NE S hsz
        ((Finset.univ.filter fun ja => EvS (Sop ja) oppVal ω ∧ Surv ja ω).image
          fun ja : Fin D × Fin NE => cstar ja.1 ja.2)
        (fun c hc => by
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          obtain ⟨ja, ⟨-, -, hal, -⟩, rfl⟩ := hc
          exact hal)
      rw [himg] at hA
      exact_mod_cast hA
    · push Not at hne
      have : ({ja | EvS (Sop ja) oppVal ω ∧ Surv ja ω} : Finset (Fin D × Fin NE)) = ∅ := by
        ext ja; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_and]
        exact hne ja
      rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hcount := forced_count_card p hp0 hp1 Sop (fun _ => oppVal) Surv (D * Lv * S) π hπ
    (fun ja => by
      by_cases h : Bt ja.1 ∣ ja.2
      · simp only [Sop, dif_pos h]; exact hpi ja.1 ja.2 h
      · simp only [Sop, dif_neg h, piS, Finset.prod_empty]; exact hπ1)
    (fun ω => by convert hcap ω)
  -- pointwise comparison
  have hpt : ∀ ω, (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧
        ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 C θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ)
      ≤ (#{ja | Surv ja (force (Sop ja) oppVal ω)} : ℝ) + D * NE *
        (if ∀ r < D, ∀ ℓ < Lv, (run ω NE r ℓ).card + 1 ≤ S then 0 else 1) := by
    intro ω
    by_cases hg : ∀ r < D, ∀ ℓ < Lv, (run ω NE r ℓ).card + 1 ≤ S
    · rw [if_pos hg, mul_zero, add_zero]
      refine Nat.cast_le.2 (Finset.card_le_card fun ja hja => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hja ⊢
      obtain ⟨hgrid, hc, hev⟩ := hja
      have hS : Sop ja = oppSet E thr0 D Bt lev NE Lt K (cstar ja.1 ja.2) (hEc ja hgrid) := by
        simp only [Sop, dif_pos hgrid]
      rw [hS]
      obtain ⟨h1, h2⟩ := bad_imp_surv hD hLv hlev cstar (hEc ja hgrid) ja.2.2 ω hc hev S hg
      exact ⟨hgrid, h1, h2⟩
    · rw [if_neg hg, mul_one]
      have : (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
          evict E thr0 C θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ)
          ≤ D * NE := by
        have := Finset.card_filter_le (Finset.univ : Finset (Fin D × Fin NE))
          (fun ja => Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
            evict E thr0 C θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none)
        rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
        exact_mod_cast this
      have : (0 : ℝ) ≤ #{ja | Surv ja (force (Sop ja) oppVal ω)} := Nat.cast_nonneg _
      linarith
  calc _ ≤ ∑ ω, wtv p ω * ((#{ja | Surv ja (force (Sop ja) oppVal ω)} : ℝ) + D * NE *
          (if ∀ r < D, ∀ ℓ < Lv, (run ω NE r ℓ).card + 1 ≤ S then 0 else 1)) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hw ω)
    _ = ∑ ω, wtv p ω * (#{ja | Surv ja (force (Sop ja) oppVal ω)} : ℝ) + D * NE * ∑ ω, wtv p ω *
          (if ∀ r < D, ∀ ℓ < Lv, (run ω NE r ℓ).card + 1 ≤ S then 0 else 1) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ _ := by
        refine add_le_add ?_ le_rfl
        convert hcount using 3

end Pool.P0082
