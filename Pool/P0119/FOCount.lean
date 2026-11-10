import Pool.P0111.FOLaw
import Pool.P0082.Count
import Pool.P0115.FOFreed
import Pool.P0097.AdaptedTail

/-!
# Counting the bad walk points of the one-free-observation threaded process (FO analogue of P0082)

An opportunity `(j, a)` is bad when the comparator's copy `cstar j a` is not sampled and, forced into its OWN
forced copy-last run (P0095), is never evicted before `NE` (P0065's `evict … = none` with that run's estimates;
these are the bad points of P0112's walk data `evFO`).

* `foRun_congr_slots`: the FO process ignores a copy's filter bits outside its clock slots (P0082's
  `tpools_congr_slots` with the realized estimates as cover data).
* `ωsC_force`, `foRun_force_eq`: the FO run on P0048's forced opportunity coins is the forced FO run.
* `forced_count_real`: P0048's forced-insertion count with real weights.
* `SurvT`, `fSurv`, **`forced_law`**: the slot probability that a forced copy-last run does not overflow and keeps
  its copy equals the same probability for the ENTRY-ORDER run on the forced coins (P0111's law step).
* `GoodA`, `bad_le`: a bad opportunity survives in its forced run, or the actual run uses `≥ s` slots or has a
  sub-pool of size `≥ S` (P0115's `Vat_forced_card_le` and P0095's coupling).
* `card_surv_le`, `fSurv_grid`, `cap_fSurv`, `card_bad_le`, `SopG`, `fG`, `cap_fG`, `hper_fG`: the cap and the
  pointwise bound.
* **`count_bad_FO`**: `E[#bad] ≤ D·Lv·S/π + D·NE·P(actual run not GoodA)`.
-/

namespace Pool.P0119

open Finset Pool.P0095 Pool.P0065 Pool.P0081 Pool.P0082 Pool.P0052 Pool.P0048 Pool.P0105

section Slots

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s)

/-- **The FO process ignores a copy's filter bits outside its clock slots** (P0082's `tpools_congr_slots`, with the
realized estimates as cover data). -/
theorem foRun_congr_slots (ωs : ι → Bool) (c : ι) (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (h : ∀ r x ℓ k d, φ r x ℓ k d ≠ φ' r x ℓ k d →
      d = c ∧ ¬ (r = curT E thr0 D Bt c x ∧ InSlotsT E thr0 D Bt lev c x ℓ)) :
    ∀ a, foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a = foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ' y a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    have hC : ∀ x u, u ≤ a + 1 → Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y x u =
        Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ' y x u := by
      intro x u hu
      rcases Nat.lt_or_eq_of_le hu with hu | hu
      · rw [← est_eq_Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y a x u (by omega),
          ← est_eq_Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ' y a x u (by omega), ih]
      · subst hu
        rw [Chat_succ, Chat_succ]
        have h1 : Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y x a = Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ' y x a := by
          rw [← est_eq_Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y a x a le_rfl,
            ← est_eq_Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ' y a x a le_rfl, ih]
        unfold obsAt; rw [ih, h1]
    have hP : (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y (a + 1)).pools =
        (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ' y (a + 1)).pools := by
      rw [foRun_pools_eq, foRun_pools_eq]
      rw [tpools_congr_slots ωs c φ φ' h (a + 1)]
      exact Pool.P0083.tpools_congr E thr0 θ R K D Lv Bt lev _ _ ωs φ' (a + 1) (fun x _ u hu => hC x u hu)
    have hE : (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y (a + 1)).est =
        (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ' y (a + 1)).est := by
      rw [foRun_succ_est, foRun_succ_est]
      unfold obsAt
      rw [ih]
    cases h1 : foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y (a + 1)
    cases h2 : foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ' y (a + 1)
    rw [h1, h2] at hP hE
    simp only at hP hE
    rw [hP, hE]

end Slots

section Force

attribute [local instance] coinFintype

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) {NE Lt : ℕ}

theorem ωsC_force (c : ι) (hc : E c < NE) (ω : SlotC NE D Lt K × ι → Bool) :
    ωsC E NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω) = forceS (ωsC E NE D Lt K ω) c := by
  classical
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

/-- **The FO run on a forced opportunity is the forced FO run** (P0082's `tpools_force_eq` for the FO process):
setting copy `c`'s sampling bit to `true` and its filter bits on its clock slots to `false` gives P0065's forced
coins (`forceS`, `forceF`: filter bits false everywhere). -/
theorem foRun_force_eq (c : ι) (hc : E c < NE) (ω : SlotC NE D Lt K × ι → Bool) (a : ℕ) :
    foRun E thr0 θ R K D Lv Bt lev s L occ (ωsC E NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω))
        (φC NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω)) y a =
      foRun E thr0 θ R K D Lv Bt lev s L occ (forceS (ωsC E NE D Lt K ω) c) (forceF K (φC NE D Lt K ω) c) y a := by
  classical
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
  refine foRun_congr_slots E thr0 θ R K D Lv Bt lev s L occ y _ c _ _ (fun r x ℓ k d hne => ?_) a
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

end Force

section ForcedReal

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Forced-insertion counting with real weights** (P0048's `forced_count_card` with the indicator of a survival
event replaced by any nonnegative weight `f a ω`): if in every run the realized opportunities carry total weight at
most `P`, and every opportunity has probability at least `π > 0`, then `E[Σ_a f a (force_a ω)] ≤ P / π`. -/
theorem forced_count_real {α : Type*} [Fintype α] (p : κ → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (S : α → Finset κ) (v : α → κ → Bool) (f : α → (κ → Bool) → ℝ) (hf0 : ∀ a ω, 0 ≤ f a ω)
    (P π : ℝ) (hπ : 0 < π) (hpi : ∀ a, π ≤ piS p (S a) (v a))
    (hcap : ∀ ω, ∑ a, (if EvS (S a) (v a) ω then f a ω else 0) ≤ P) :
    ∑ ω, wtv p ω * ∑ a, f a (force (S a) (v a) ω) ≤ P / π := by
  classical
  rw [le_div_iff₀ hπ]
  have hw := wtv_nonneg hp0 hp1
  calc (∑ ω, wtv p ω * ∑ a, f a (force (S a) (v a) ω)) * π
      = ∑ a, π * ∑ ω, wtv p ω * f a (force (S a) (v a) ω) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ ∑ a, piS p (S a) (v a) * ∑ ω, wtv p ω * f a (force (S a) (v a) ω) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hpi a)
          (Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (hf0 a _))
    _ = ∑ a, ∑ ω, wtv p ω * ((if EvS (S a) (v a) ω then (1 : ℝ) else 0) * f a (force (S a) (v a) ω)) :=
        Finset.sum_congr rfl fun a _ => (sum_event_force p (S a) (v a) (f a)).symm
    _ = ∑ a, ∑ ω, wtv p ω * (if EvS (S a) (v a) ω then f a ω else 0) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ω _ => ?_
        by_cases h : EvS (S a) (v a) ω
        · rw [force_eq_self h, if_pos h, if_pos h, one_mul]
        · rw [if_neg h, if_neg h, zero_mul]
    _ = ∑ ω, wtv p ω * ∑ a, (if EvS (S a) (v a) ω then f a ω else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ ω, wtv p ω * P := Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hcap ω) (hw ω)
    _ = P := by rw [← Finset.sum_mul, sum_wtv, one_mul]

end ForcedReal

section Count

attribute [local instance] coinFintype

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) {NE Lt : ℕ}

/-- The survival event of opportunity `c` on a trajectory: `c` is in some pool at `NE` and every sub-pool at
`NE` has at most `S` copies. -/
def SurvT (NE S : ℕ) (c : ι) (tr : ℕ → FOSt ι) : Prop :=
  (∃ r ℓ, c ∈ (tr NE).pools r ℓ) ∧ ∀ r < D, ∀ ℓ < Lv, ((tr NE).pools r ℓ).card ≤ S

open Classical in
/-- The slot probability that, in the entry-order run on coins `ω`, nothing overflows before `NE` and the
copy `c` survives (with small pools). -/
noncomputable def fSurv [NeZero s] (S : ℕ) (c : ι) (ω : SlotC NE D Lt K × ι → Bool) : ℝ :=
  ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
    (if NoOverflow E thr0 D Lv Bt s (ωsC E NE D Lt K ω) NE
          (traj E thr0 θ R K D Lv Bt lev s L (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy)) ∧
        SurvT D Lv NE S c
          (traj E thr0 θ R K D Lv Bt lev s L (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy))
      then 1 else 0)

theorem wR_nonneg_s {T : ℕ} (yy : Fin T → Fin s) : 0 ≤ Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy :=
  Finset.prod_nonneg fun _ _ => by positivity

theorem fSurv_nonneg [NeZero s] (S : ℕ) (c : ι) (ω : SlotC NE D Lt K × ι → Bool) :
    0 ≤ fSurv E thr0 θ R K D Lv Bt lev s L S c ω :=
  Finset.sum_nonneg fun yy _ => mul_nonneg (wR_nonneg_s s yy) (by split_ifs <;> norm_num)

open Classical in
/-- **Per-opportunity law step.** The slot probability that the FORCED copy-last run of `c` (on coins `ω`)
does not overflow and has `c` surviving equals `fSurv` at the forced coins: the forced run is the run on the
P0048-forced coins (`foRun_force_eq`), and P0111 moves copy-last to entry order. -/
theorem forced_law [NeZero s] (S : ℕ) (c : ι) (hc : E c < NE) (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      (if NoOverflow E thr0 D Lv Bt s (forceS (ωsC E NE D Lt K ω) c) NE
            (traj E thr0 θ R K D Lv Bt lev s L (forceS (ωsC E NE D Lt K ω) c) (forceF K (φC NE D Lt K ω) c)
              (occLast s c) NE (extY s yy)) ∧
          SurvT D Lv NE S c (traj E thr0 θ R K D Lv Bt lev s L (forceS (ωsC E NE D Lt K ω) c)
            (forceF K (φC NE D Lt K ω) c) (occLast s c) NE (extY s yy))
        then 1 else 0) =
      fSurv E thr0 θ R K D Lv Bt lev s L S c (force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω) := by
  set ω' := force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω
  have htr : ∀ yy : Fin NE → Fin s,
      traj E thr0 θ R K D Lv Bt lev s L (forceS (ωsC E NE D Lt K ω) c) (forceF K (φC NE D Lt K ω) c)
        (occLast s c) NE (extY s yy) =
      traj E thr0 θ R K D Lv Bt lev s L (ωsC E NE D Lt K ω') (φC NE D Lt K ω') (occLast s c) NE (extY s yy) := by
    intro yy; funext a
    simp only [traj]
    rw [foRun_force_eq E thr0 θ R K D Lv Bt lev s L (occLast s c) (extY s yy) c hc ω]
  have hs := ωsC_force E thr0 K D Bt lev c hc ω
  simp only [htr]
  rw [← hs]
  unfold fSurv
  exact (law_occSort_occLast E thr0 θ R K D Lv Bt lev s L (ωsC E NE D Lt K ω') (φC NE D Lt K ω') c NE
    (SurvT D Lv NE S c)).symm

end Count

section Bad

attribute [local instance] coinFintype

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ)

/-- The good event of the actual (entry-order) run: at most `s − 1` start-pool members before `T` and sub-pools of
size at most `S − 1` at `T`. -/
def GoodA (T S : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s) : Prop :=
  (∀ u < T, (Vst E thr0 D Lv Bt ωs u (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u)).card + 1 ≤ s) ∧
    ∀ r < D, ∀ ℓ < Lv, ((foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y T).pools r ℓ).card + 1 ≤ S

open Classical in
/-- **A bad opportunity survives in its forced run, or the actual run is not good.** If `c` is not sampled and,
forced in, is never evicted before `T` (P0065's `evict … = none`, with the forced run's own estimates), then either
its forced copy-last run does not overflow and `c` survives at `T` with small pools, or the actual run fails
`GoodA`. -/
theorem bad_le (T S : ℕ) (cstar : ℕ → ℕ → ι) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} (y : ℕ → Fin s)
    {j a : ℕ} (ha : a < T) (hc : ωs (cstar j a) = false)
    (hev : evict E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar j a)) (forceS ωs (cstar j a))
      (forceF K φ (cstar j a)) y) θ R K D Lv Bt lev T cstar ωs φ j a = none) :
    (1 : ℝ) ≤ (if NoOverflow E thr0 D Lv Bt s (forceS ωs (cstar j a)) T
            (traj E thr0 θ R K D Lv Bt lev s L (forceS ωs (cstar j a)) (forceF K φ (cstar j a))
              (occLast s (cstar j a)) T y) ∧
          SurvT D Lv T S (cstar j a) (traj E thr0 θ R K D Lv Bt lev s L (forceS ωs (cstar j a))
            (forceF K φ (cstar j a)) (occLast s (cstar j a)) T y) then 1 else 0) +
      (if GoodA E thr0 θ R K D Lv Bt lev s L T S ωs φ y then 0 else 1) := by
  set c := cstar j a with hcdef
  by_cases hg : GoodA E thr0 θ R K D Lv Bt lev s L T S ωs φ y
  · rw [if_pos hg, add_zero, if_pos]
    have hmin : ∀ u, u ≤ T → min u T = u := fun u hu => Nat.min_eq_left hu
    refine ⟨fun u hu => ?_, ⟨?_, fun r hr ℓ hℓ => ?_⟩⟩
    · simp only [traj, hmin u hu.le]
      have h1 := Pool.P0115.Vat_forced_card_le E thr0 θ R K D Lv Bt lev s L hc φ y u
      have h2 := hg.1 u hu
      exact h1.trans (by unfold Vat; unfold Vst at h2; omega)
    · simp only [traj, Nat.min_self]
      unfold evict at hev
      split_ifs at hev with h
      have hal : Alive E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y)
          θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) T c := by
        by_contra hna
        exact h ⟨T, ha, le_rfl, hna⟩
      obtain ⟨r, ℓ, hm⟩ := hal
      refine ⟨r, ℓ, ?_⟩
      rwa [← foRun_pools_eq] at hm
    · simp only [traj, Nat.min_self]
      have he := (fo_forced_erase E thr0 θ R K D Lv Bt lev s L hc φ y T).1 r ℓ
      rw [foRun_free_eq E thr0 θ R K D Lv Bt lev s L hc φ y T] at he
      have h1 := Finset.pred_card_le_card_erase (s := (foRun E thr0 θ R K D Lv Bt lev s L (occLast s c)
        (forceS ωs c) (forceF K φ c) y T).pools r ℓ) (a := c)
      rw [he] at h1
      have h2 := hg.2 r hr ℓ hℓ
      omega
  · rw [if_neg hg]
    have : (0 : ℝ) ≤ (if NoOverflow E thr0 D Lv Bt s (forceS ωs c) T
            (traj E thr0 θ R K D Lv Bt lev s L (forceS ωs c) (forceF K φ c) (occLast s c) T y) ∧
          SurvT D Lv T S c (traj E thr0 θ R K D Lv Bt lev s L (forceS ωs c) (forceF K φ c) (occLast s c) T y)
        then 1 else 0) := by split_ifs <;> norm_num
    linarith

end Bad

section Main

attribute [local instance] coinFintype

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) {NE Lt : ℕ}

open Classical in
/-- At most `D·Lv·S` grid opportunities survive with small pools in one run. -/
theorem card_surv_le (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s) (S : ℕ) :
    (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ SurvT D Lv NE S (cstar ja.1 ja.2)
      (traj E thr0 θ R K D Lv Bt lev s L ωs φ (occSort s) NE y)} : ℝ) ≤ D * Lv * S := by
  set F := (Finset.univ.filter fun ja : Fin D × Fin NE => Bt ja.1 ∣ ja.2 ∧ SurvT D Lv NE S (cstar ja.1 ja.2)
      (traj E thr0 θ R K D Lv Bt lev s L ωs φ (occSort s) NE y)) with hF
  by_cases hne : F.Nonempty
  · obtain ⟨ja0, hja0⟩ := hne
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hja0
    have hsz := hja0.2.2
    simp only [traj, Nat.min_self] at hsz
    rw [foRun_pools_eq] at hsz
    have hinj : Set.InjOn (fun ja : Fin D × Fin NE => cstar ja.1 ja.2) (F : Set (Fin D × Fin NE)) := by
      rintro ⟨j, a⟩ hj1 ⟨j', a'⟩ hj2 heq
      simp only [hF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj1 hj2
      simp only at heq
      have h1 := hE j a (by omega) hj1.1 a.2
      have h2 := hE j' a' (by omega) hj2.1 a'.2
      have h3 := hthr j a (by omega) hj1.1 a.2
      have h4 := hthr j' a' (by omega) hj2.1 a'.2
      rw [heq] at h1 h3
      ext <;> simp only <;> omega
    have himg := Finset.card_image_of_injOn hinj
    have hA := card_alive_le hD hLv hlev _ _ NE S hsz (F.image fun ja : Fin D × Fin NE => cstar ja.1 ja.2)
      (fun c hc => by
        simp only [Finset.mem_image, hF, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        obtain ⟨ja, ⟨-, hal, -⟩, rfl⟩ := hc
        obtain ⟨r, ℓ, hm⟩ := hal
        simp only [traj, Nat.min_self] at hm
        rw [foRun_pools_eq] at hm
        exact ⟨r, ℓ, hm⟩)
    rw [himg] at hA
    exact_mod_cast hA
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

open Classical in
theorem fSurv_grid [NeZero s] (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) :
    (if Bt ja.1 ∣ ja.2 then fSurv E thr0 θ R K D Lv Bt lev s L S (cstar ja.1 ja.2) ω else 0) =
      ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        (if Bt ja.1 ∣ ja.2 ∧ NoOverflow E thr0 D Lv Bt s (ωsC E NE D Lt K ω) NE
            (traj E thr0 θ R K D Lv Bt lev s L (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy)) ∧
          SurvT D Lv NE S (cstar ja.1 ja.2)
            (traj E thr0 θ R K D Lv Bt lev s L (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy))
        then 1 else 0) := by
  by_cases h : Bt ja.1 ∣ ja.2
  · rw [if_pos h]
    unfold fSurv
    refine Finset.sum_congr rfl fun yy _ => ?_
    congr 1
    exact if_congr (by simp [h]) rfl rfl
  · rw [if_neg h]
    symm
    exact Finset.sum_eq_zero fun yy _ => by simp [h]

open Classical in
/-- The cap: in every coin vector, the grid opportunities carry total survival weight at most `D·Lv·S`. -/
theorem cap_fSurv [NeZero s] (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j) (S : ℕ)
    (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 then fSurv E thr0 θ R K D Lv Bt lev s L S (cstar ja.1 ja.2) ω else 0)
      ≤ D * Lv * S := by
  simp only [fSurv_grid E thr0 θ R K D Lv Bt lev s L cstar S _ ω]
  rw [Finset.sum_comm]
  calc ∑ yy : Fin NE → Fin s, ∑ ja : Fin D × Fin NE, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        (if Bt ja.1 ∣ ja.2 ∧ NoOverflow E thr0 D Lv Bt s (ωsC E NE D Lt K ω) NE
            (traj E thr0 θ R K D Lv Bt lev s L (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy)) ∧
          SurvT D Lv NE S (cstar ja.1 ja.2)
            (traj E thr0 θ R K D Lv Bt lev s L (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy))
        then 1 else 0)
      ≤ ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * (D * Lv * S) := by
        refine Finset.sum_le_sum fun yy _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (wR_nonneg_s s yy)
        refine le_trans ?_ (card_surv_le E thr0 θ R K D Lv Bt lev s L hD hLv hlev cstar hE hthr
          (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) S)
        rw [Finset.card_filter]
        push_cast
        exact Finset.sum_le_sum fun ja _ => by
          by_cases h1 : Bt ja.1 ∣ ja.2 ∧ NoOverflow E thr0 D Lv Bt s (ωsC E NE D Lt K ω) NE
              (traj E thr0 θ R K D Lv Bt lev s L (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy)) ∧
            SurvT D Lv NE S (cstar ja.1 ja.2)
              (traj E thr0 θ R K D Lv Bt lev s L (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy))
          · rw [if_pos h1, if_pos ⟨h1.1, h1.2.2⟩]
          · rw [if_neg h1]; split_ifs <;> norm_num
    _ = D * Lv * S := by
        rw [← Finset.sum_mul, Pool.P0097.sum_wR _ (by simp [Finset.sum_const, Finset.card_univ]) NE, one_mul]

open Classical in
/-- Pointwise: the bad opportunities are the surviving forced ones, plus all of them on runs that are not good. -/
theorem card_bad_le (cstar : ℕ → ℕ → ι) (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hD : 0 < D) (S : ℕ) (ω : SlotC NE D Lt K × ι → Bool) (yy : ℕ → Fin s) :
    (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar ja.1 ja.2))
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) yy)
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ) ≤
      ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 ∧
          NoOverflow E thr0 D Lv Bt s (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
            (traj E thr0 θ R K D Lv Bt lev s L (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
              (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (occLast s (cstar ja.1 ja.2)) NE yy) ∧
          SurvT D Lv NE S (cstar ja.1 ja.2) (traj E thr0 θ R K D Lv Bt lev s L
            (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
            (occLast s (cstar ja.1 ja.2)) NE yy) then 1 else 0) +
        D * NE * (if GoodA E thr0 θ R K D Lv Bt lev s L NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) yy then 0 else 1) := by
  rw [Finset.card_filter]
  push_cast
  have hcard : (D * NE : ℝ) = ∑ _ja : Fin D × Fin NE, (1 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
  rw [hcard, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ja _ => ?_
  split_ifs with h1 h2 h3 h4 <;> try norm_num
  all_goals first
    | (have := bad_le E thr0 θ R K D Lv Bt lev s L NE S cstar yy (j := ja.1) (a := ja.2) ja.2.2 h1.2.1 h1.2.2
       rw [if_neg (fun h => by tauto), if_pos (by assumption)] at this; linarith)
    | (have := bad_le E thr0 θ R K D Lv Bt lev s L NE S cstar yy (j := ja.1) (a := ja.2) ja.2.2 h1.2.1 h1.2.2
       simp_all)

open Classical in
/-- The opportunity coordinates of grid point `ja` (empty off the grid). -/
noncomputable def SopG (cstar : ℕ → ℕ → ι) (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hD : 0 < D) (ja : Fin D × Fin NE) : Finset (SlotC NE D Lt K × ι) :=
  if h : Bt ja.1 ∣ ja.2 then oppSet E thr0 D Bt lev NE Lt K (cstar ja.1 ja.2)
    (by rw [hE ja.1 ja.2 (by omega) h ja.2.2]; exact ja.2.2) else ∅

open Classical in
/-- The survival weight of grid point `ja` (zero off the grid). -/
noncomputable def fG [NeZero s] (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) : ℝ :=
  if Bt ja.1 ∣ ja.2 then fSurv E thr0 θ R K D Lv Bt lev s L S (cstar ja.1 ja.2) ω else 0

theorem fG_nonneg [NeZero s] (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) :
    0 ≤ fG E thr0 θ R K D Lv Bt lev s L cstar S ja ω := by
  unfold fG; split_ifs
  · exact fSurv_nonneg E thr0 θ R K D Lv Bt lev s L S _ ω
  · exact le_rfl

open Classical in
theorem cap_fG [NeZero s] (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j) (S : ℕ)
    (Sop : Fin D × Fin NE → Finset (SlotC NE D Lt K × ι)) (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ ja : Fin D × Fin NE, (if EvS (Sop ja) oppVal ω then fG E thr0 θ R K D Lv Bt lev s L cstar S ja ω else 0)
      ≤ D * Lv * S := by
  refine le_trans (Finset.sum_le_sum fun ja _ => ?_)
    (cap_fSurv E thr0 θ R K D Lv Bt lev s L hD hLv hlev cstar hE hthr S ω)
  by_cases h : EvS (Sop ja) oppVal ω
  · rw [if_pos h]; rfl
  · rw [if_neg h]; exact fG_nonneg E thr0 θ R K D Lv Bt lev s L cstar S ja ω

open Classical in
theorem hper_fG [NeZero s] (cstar : ℕ → ℕ → ι) (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hD : 0 < D) (S : ℕ) (ω : SlotC NE D Lt K × ι → Bool) (ja : Fin D × Fin NE) :
    ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      (if Bt ja.1 ∣ ja.2 ∧
        NoOverflow E thr0 D Lv Bt s (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
          (traj E thr0 θ R K D Lv Bt lev s L (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
            (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (occLast s (cstar ja.1 ja.2)) NE (extY s yy)) ∧
        SurvT D Lv NE S (cstar ja.1 ja.2) (traj E thr0 θ R K D Lv Bt lev s L
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
          (occLast s (cstar ja.1 ja.2)) NE (extY s yy)) then 1 else 0) =
      fG E thr0 θ R K D Lv Bt lev s L cstar S ja (force (SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω) := by
  by_cases h : Bt ja.1 ∣ ja.2
  · unfold fG SopG
    rw [if_pos h, dif_pos h]
    rw [← forced_law E thr0 θ R K D Lv Bt lev s L S (cstar ja.1 ja.2) _ ω]
    refine Finset.sum_congr rfl fun yy _ => ?_
    congr 1
    exact if_congr (by simp [h]) rfl rfl
  · unfold fG
    rw [if_neg h]
    exact Finset.sum_eq_zero fun yy _ => by simp [h]

open Classical in
/-- **Expected number of bad opportunities of the FO walk** (the FO analogue of P0082's `count_bad`). Over the
sampling/filter coins (P0082's array, weights `wtv p`) and i.i.d. uniform slots, the expected number of grid
opportunities `(j, a)` whose comparator copy is not sampled and, forced into its own forced copy-last run, is never
evicted before `NE` is at most `D·Lv·S/π + D·NE·P(the actual run is not GoodA)`. -/
theorem count_bad_FO [NeZero s] (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (p : SlotC NE D Lt K × ι → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (π : ℝ) (hπ : 0 < π)
    (hπ1 : π ≤ 1)
    (hpi : ∀ (j : Fin D) (a : Fin NE) (h : Bt j ∣ a),
      π ≤ piS p (oppSet E thr0 D Bt lev NE Lt K (cstar j a)
        (by rw [hE j a (by omega) h a.2]; exact a.2)) oppVal)
    (S : ℕ) :
    ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s (cstar ja.1 ja.2))
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (extY s yy))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ)
      ≤ (D * Lv * S : ℝ) / π + D * NE * ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s,
        Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        (if GoodA E thr0 θ R K D Lv Bt lev s L NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) then 0 else 1) := by
  have hD := hB.hD
  have hw : ∀ ω, 0 ≤ wtv p ω := wtv_nonneg hp0 hp1
  have hwR : ∀ yy : Fin NE → Fin s, 0 ≤ Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy := wR_nonneg_s s
  have hpiG : ∀ ja : Fin D × Fin NE, π ≤ piS p (SopG E thr0 K D Bt lev cstar hE hD ja) oppVal := by
    intro ja
    by_cases h : Bt ja.1 ∣ ja.2
    · unfold SopG; rw [dif_pos h]; exact hpi ja.1 ja.2 h
    · unfold SopG; rw [dif_neg h]; simp only [piS, Finset.prod_empty]; exact hπ1
  have hcap : ∀ ω : SlotC NE D Lt K × ι → Bool, ∑ ja : Fin D × Fin NE,
      (if EvS (SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω then fG E thr0 θ R K D Lv Bt lev s L cstar S ja ω
        else 0) ≤ (D * Lv * S : ℝ) :=
    cap_fG E thr0 θ R K D Lv Bt lev s L hD hLv hlev cstar hE hthr S (SopG E thr0 K D Bt lev cstar hE hD)
  have hcount := forced_count_real p hp0 hp1 (SopG E thr0 K D Bt lev cstar hE hD) (fun _ => oppVal)
    (fG E thr0 θ R K D Lv Bt lev s L cstar S) (fG_nonneg E thr0 θ R K D Lv Bt lev s L cstar S)
    (D * Lv * S : ℝ) π hπ hpiG (fun ω => by convert hcap ω)
  refine le_trans (Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun yy _ =>
    mul_le_mul_of_nonneg_left (card_bad_le E thr0 θ R K D Lv Bt lev s L cstar hE hD S ω (extY s yy))
      (hwR yy)) (hw ω)) ?_
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : ∀ ω, ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 ∧
        NoOverflow E thr0 D Lv Bt s (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
          (traj E thr0 θ R K D Lv Bt lev s L (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
            (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (occLast s (cstar ja.1 ja.2)) NE (extY s yy)) ∧
        SurvT D Lv NE S (cstar ja.1 ja.2) (traj E thr0 θ R K D Lv Bt lev s L
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
          (occLast s (cstar ja.1 ja.2)) NE (extY s yy)) then 1 else 0) =
      ∑ ja, fG E thr0 θ R K D Lv Bt lev s L cstar S ja (force (SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω) := by
    intro ω
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ja _ => ?_
    rw [← hper_fG E thr0 θ R K D Lv Bt lev s L cstar hE hD S ω ja]
  simp only [h1]
  have h2 : ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      ((D : ℝ) * NE * (if GoodA E thr0 θ R K D Lv Bt lev s L NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
        (extY s yy) then 0 else 1)) =
      D * NE * ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        (if GoodA E thr0 θ R K D Lv Bt lev s L NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) then 0 else 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun yy _ => by ring
  rw [h2]
  refine le_trans (le_of_eq ?_) (add_le_add_left hcount _)
  congr 1

end Main

end Pool.P0119
