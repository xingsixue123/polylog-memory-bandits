import Pool.P0065.Threads
import Pool.P0062.Slots

/-!
# Clock slots and slot-restricted non-interference for P0065's threaded process (thread analogue of P0062)

P0065 (and P0074) prove non-interference only for a copy that is **never** a filter (`forceF` zeroes all of its
filter bits). That event has negligible probability, so it cannot be P0048's opportunity. This file shows that, as in
P0062 for one level, the merges a copy takes part in are fixed by the clock, so passivity is a fixed-coordinate event:

* `tl c x` / `tpost c x`: the level of a surviving copy at the start of unit `x` / after the merges ending unit `x`
  (a function of `E c`, `thr0 c` and the schedules only: reset to 0 when its thread restarts and it is inherited,
  cascaded to `max ℓ (lev r x + 1)` when its thread `r = curT c x` merges).
* `mem_tlevel`: in every run, a copy in sub-pool `(r, ℓ)` at the start of unit `x` has `r = curT c x` and
  `ℓ = tl c x` (and similarly at boundaries, with `tpost`). `mem_mergeUpTo_level`: levels during a cascade.
* `InSlotsT c x ℓ`: `E c ≤ x`, its current thread merges at `x + 1`, `ℓ ≤ lev (curT c x) x`, `tl c x ≤ ℓ + 1`.
  `inSlotsT_of_mem_input`: a copy in the input of the merge `(r, x, ℓ)` has `r = curT c x` and is in that slot.
* **`tpools_erase_of_slots`**: if `c`'s filter bits are `false` at its slots `(curT c x, x, ℓ, k)`, the run with `c`
  and the run without it have the same pools up to `c` (P0052's `mergeUpTo_erase_of_passive` per merge, P0062's
  `passiveIter_of_not_mem` for merges `c` is not in).
-/

open Finset Pool.P0030 Pool.P0034 Pool.P0042 Pool.P0052 Pool.P0065

namespace Pool.P0081

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ)

/-- Level of a surviving copy `c` at the start of unit `x` (for `E c ≤ x`): `0` at entry; after unit `x`, its
thread `r = curT c x` cascades it to `max ℓ (lev r x + 1)` if `r` merges at `x + 1`; at a restart of its thread it
moves to level `0` of the coarser thread. -/
noncomputable def tl (c : ι) : ℕ → ℕ
  | 0 => 0
  | x + 1 =>
    if x + 1 ≤ E c then 0
    else if curT E thr0 D Bt c (x + 1) < curT E thr0 D Bt c x then 0
    else if Bt (curT E thr0 D Bt c x) ∣ x + 1 then max (tl c x) (lev (curT E thr0 D Bt c x) x + 1)
    else tl c x

variable {E thr0 C θ R K D Lv Bt lev}

/-- Levels during a cascade: if `c` is at a unique level `ℓ0` of `P`, then after `mergeUpTo m` it is at level
`max ℓ0 (m + 1)` (if present). -/
theorem mem_mergeUpTo_level {φ : ℕ → ℕ → Fin K → ι → Bool} {a : ℕ} {c : ι} {ℓ0 : ℕ} :
    ∀ (m : ℕ) (P : ℕ → Finset ι), (∀ j, c ∈ P j → j = ℓ0) →
      ∀ j, c ∈ mergeUpTo E C θ R K φ a m P j → j = max ℓ0 (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro P hP j hj
    rcases mem_mergeOne hj with ⟨h1 | h1, rfl⟩ | ⟨h1, h2, h3⟩
    · have := hP _ h1; omega
    · have := hP _ h1; omega
    · have := hP _ h3; omega
  | succ m ih =>
    intro P hP j hj
    simp only [mergeUpTo] at hj
    rcases mem_mergeOne hj with ⟨h1 | h1, rfl⟩ | ⟨h1, h2, h3⟩
    · have := ih P hP _ h1; omega
    · have := ih P hP _ h1; omega
    · have := ih P hP _ h3; omega


/-- Level after the merges ending unit `x`. -/
noncomputable def tpost (c : ι) (x : ℕ) : ℕ :=
  if Bt (curT E thr0 D Bt c x) ∣ x + 1 then max (tl E thr0 D Bt lev c x) (lev (curT E thr0 D Bt c x) x + 1)
  else tl E thr0 D Bt lev c x

theorem tl_succ_of_lt {c : ι} {x : ℕ} (hE : E c < x + 1) :
    tl E thr0 D Bt lev c (x + 1) =
      if curT E thr0 D Bt c (x + 1) < curT E thr0 D Bt c x then 0 else tpost (E := E) (thr0 := thr0) (D := D)
        (Bt := Bt) (lev := lev) c x := by
  simp only [tl, tpost, show ¬ x + 1 ≤ E c by omega, if_false]

/-- The boundary statement from the start statement of the same unit. -/
theorem bd_of_start {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} {x : ℕ}
    (hS : ∀ r ℓ, c ∈ startPools E thr0 D Lv Bt ωs x (tpools E thr0 C θ R K D Lv Bt lev ωs φ x) r ℓ →
        E c ≤ x ∧ r = curT E thr0 D Bt c x ∧ ℓ = tl E thr0 D Bt lev c x) :
    ∀ r ℓ, c ∈ tpools E thr0 C θ R K D Lv Bt lev ωs φ (x + 1) r ℓ →
      E c ≤ x ∧ r = curT E thr0 D Bt c x ∧ ℓ = tpost (E := E) (thr0 := thr0) (D := D) (Bt := Bt) (lev := lev) c x := by
  intro r ℓ hc
  simp only [tpools] at hc
  split_ifs at hc with hBt
  · obtain ⟨⟨j', hj'⟩, -⟩ := mem_mergeUpTo _ _ ℓ c hc
    obtain ⟨hE, hr, -⟩ := hS r j' hj'
    have hlv := mem_mergeUpTo_level (ℓ0 := tl E thr0 D Bt lev c x) (lev r x) _
      (fun j hj => (hS r j hj).2.2) ℓ hc
    refine ⟨hE, hr, ?_⟩
    unfold tpost; rw [← hr, if_pos hBt]; exact hlv
  · obtain ⟨hE, hr, hl⟩ := hS r ℓ hc
    refine ⟨hE, hr, ?_⟩
    unfold tpost; rw [← hr, if_neg hBt]; exact hl

/-- **Locations are fixed by the clock (threads).** In every run, a copy in sub-pool `(r, ℓ)` at the start of unit
`x` has `E c ≤ x`, `r = curT c x` and `ℓ = tl c x`; a copy in sub-pool `(r, ℓ)` at the boundary `x + 1` has
`r = curT c x` and `ℓ = tpost c x`. -/
theorem mem_tlevel {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} :
    ∀ x, (∀ r ℓ, c ∈ startPools E thr0 D Lv Bt ωs x (tpools E thr0 C θ R K D Lv Bt lev ωs φ x) r ℓ →
        E c ≤ x ∧ r = curT E thr0 D Bt c x ∧ ℓ = tl E thr0 D Bt lev c x) ∧
      (∀ r ℓ, c ∈ tpools E thr0 C θ R K D Lv Bt lev ωs φ (x + 1) r ℓ →
        E c ≤ x ∧ r = curT E thr0 D Bt c x ∧ ℓ = tpost (E := E) (thr0 := thr0) (D := D) (Bt := Bt) (lev := lev) c x) := by
  intro x
  induction x with
  | zero =>
    have hS0 : ∀ r ℓ, c ∈ startPools E thr0 D Lv Bt ωs 0 (tpools E thr0 C θ R K D Lv Bt lev ωs φ 0) r ℓ →
        E c ≤ 0 ∧ r = curT E thr0 D Bt c 0 ∧ ℓ = tl E thr0 D Bt lev c 0 := by
      intro r ℓ hc
      unfold startPools sample at hc
      have hinh : ∀ r ℓ, c ∉ inherit D Lv Bt 0 (tpools E thr0 C θ R K D Lv Bt lev ωs φ 0) r ℓ := by
        intro r ℓ h
        unfold inherit at h
        split_ifs at h <;> simp [tpools] at h
      split_ifs at hc with hs
      · rcases mem_union.1 hc with h | h
        · exact absurd h (hinh r 0)
        · simp only [newAtT, mem_filter, mem_univ, true_and] at h
          obtain ⟨hE, hthr, -⟩ := h
          exact ⟨hE.le, by simp [curT, hthr], by simp [tl, hs.1]⟩
      · exact absurd hc (hinh r ℓ)
    exact ⟨hS0, bd_of_start hS0⟩
  | succ x ih =>
    obtain ⟨-, hBx⟩ := ih
    have hS : ∀ r ℓ, c ∈ startPools E thr0 D Lv Bt ωs (x + 1) (tpools E thr0 C θ R K D Lv Bt lev ωs φ (x + 1)) r ℓ →
        E c ≤ x + 1 ∧ r = curT E thr0 D Bt c (x + 1) ∧ ℓ = tl E thr0 D Bt lev c (x + 1) := by
      intro r ℓ hc
      have hinh : ∀ r ℓ, c ∈ inherit D Lv Bt (x + 1) (tpools E thr0 C θ R K D Lv Bt lev ωs φ (x + 1)) r ℓ →
          E c ≤ x + 1 ∧ r = curT E thr0 D Bt c (x + 1) ∧ ℓ = tl E thr0 D Bt lev c (x + 1) := by
        intro r ℓ h
        unfold inherit at h
        by_cases h1 : r < canonT D Bt (x + 1)
        · rw [if_pos h1] at h
          obtain ⟨hE, hr, hl⟩ := hBx r ℓ h
          have hcur : curT E thr0 D Bt c (x + 1) = r := by
            rw [curT_succ hE, ← hr, min_eq_left h1.le]
          refine ⟨by omega, hcur.symm, ?_⟩
          rw [tl_succ_of_lt (by omega), hcur, ← hr, if_neg (lt_irrefl _), hl]
        rw [if_neg h1] at h
        by_cases h2 : r = canonT D Bt (x + 1)
        · rw [if_pos h2] at h
          by_cases h3 : ℓ = 0
          · rw [if_pos h3] at h
            rcases mem_union.1 h with h | h
            · obtain ⟨hE, hr, hl⟩ := hBx r 0 h
              have hcur : curT E thr0 D Bt c (x + 1) = r := by
                rw [curT_succ hE, ← hr, ← h2, min_self]
              refine ⟨by omega, hcur.symm, ?_⟩
              rw [tl_succ_of_lt (by omega), hcur, ← hr, if_neg (lt_irrefl _), h3, hl]
            · simp only [mem_biUnion, mem_Ioo, mem_range] at h
              obtain ⟨r', ⟨hr'1, -⟩, ℓ', -, h⟩ := h
              obtain ⟨hE, hr', -⟩ := hBx r' ℓ' h
              have hcur : curT E thr0 D Bt c (x + 1) = r := by
                rw [curT_succ hE, ← hr', min_eq_right (by omega), h2]
              refine ⟨by omega, hcur.symm, ?_⟩
              rw [tl_succ_of_lt (by omega), hcur, ← hr', if_pos hr'1, h3]
          · rw [if_neg h3] at h
            obtain ⟨hE, hr, hl⟩ := hBx r ℓ h
            have hcur : curT E thr0 D Bt c (x + 1) = r := by
              rw [curT_succ hE, ← hr, ← h2, min_self]
            refine ⟨by omega, hcur.symm, ?_⟩
            rw [tl_succ_of_lt (by omega), hcur, ← hr, if_neg (lt_irrefl _), hl]
        · rw [if_neg h2] at h; simp at h
      unfold startPools sample at hc
      split_ifs at hc with hs
      · rcases mem_union.1 hc with h | h
        · exact hs.1 ▸ hinh r 0 h
        · simp only [newAtT, mem_filter, mem_univ, true_and] at h
          obtain ⟨hE, hthr, -⟩ := h
          refine ⟨hE.le, ?_, ?_⟩
          · rw [curT_of_le hE.ge, hthr]
          · rw [hs.1]; simp [tl, hE]
      · exact hinh r ℓ hc
    exact ⟨hS, bd_of_start hS⟩


variable (E thr0 D Bt lev) in
/-- The thread-merge slots of copy `c`: unit `x`, level `ℓ` of its current thread, which merges at `x + 1`. -/
def InSlotsT (c : ι) (x ℓ : ℕ) : Prop :=
  E c ≤ x ∧ Bt (curT E thr0 D Bt c x) ∣ x + 1 ∧ ℓ ≤ lev (curT E thr0 D Bt c x) x ∧
    tl E thr0 D Bt lev c x ≤ ℓ + 1

/-- A copy in the input of the merge of level `ℓ` of thread `r` at the end of unit `x` (when `r` merges) is in
`r = curT c x` and in one of its slots. -/
theorem inSlotsT_of_mem_input {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} {x r ℓ : ℕ}
    (hBt : Bt r ∣ x + 1) (hℓ : ℓ ≤ lev r x)
    (h : c ∈ stage E C θ R K (φ r) x (startPools E thr0 D Lv Bt ωs x (tpools E thr0 C θ R K D Lv Bt lev ωs φ x) r)
        ℓ (ℓ + 1) ∪
      stage E C θ R K (φ r) x (startPools E thr0 D Lv Bt ωs x (tpools E thr0 C θ R K D Lv Bt lev ωs φ x) r) ℓ ℓ) :
    r = curT E thr0 D Bt c x ∧ InSlotsT E thr0 D Bt lev c x ℓ := by
  have hS := (mem_tlevel (E := E) (thr0 := thr0) (D := D) (Bt := Bt) (lev := lev) (C := C) (θ := θ) (R := R) (K := K) (Lv := Lv) (ωs := ωs) (φ := φ) (c := c) x).1
  set P := startPools E thr0 D Lv Bt ωs x (tpools E thr0 C θ R K D Lv Bt lev ωs φ x) r with hP
  -- membership in the start pool and the stage level
  have hstage : ∀ j, c ∈ stage E C θ R K (φ r) x P ℓ j →
      (∃ j', c ∈ P j') ∧ j = max (tl E thr0 D Bt lev c x) ℓ := by
    intro j hj
    cases ℓ with
    | zero =>
      simp only [stage] at hj
      exact ⟨⟨j, hj⟩, by have := (hS r j hj).2.2; omega⟩
    | succ m =>
      simp only [stage] at hj
      obtain ⟨⟨j', hj'⟩, -⟩ := mem_mergeUpTo _ _ j c hj
      have hl := mem_mergeUpTo_level (ℓ0 := tl E thr0 D Bt lev c x) m P (fun j hj => (hS r j hj).2.2) j hj
      exact ⟨⟨j', hj'⟩, hl⟩
  rcases mem_union.1 h with h1 | h1
  · obtain ⟨⟨j', hj'⟩, hl⟩ := hstage _ h1
    obtain ⟨hE, hr, -⟩ := hS r j' hj'
    exact ⟨hr, hE, hr ▸ hBt, hr ▸ hℓ, by omega⟩
  · obtain ⟨⟨j', hj'⟩, hl⟩ := hstage _ h1
    obtain ⟨hE, hr, -⟩ := hS r j' hj'
    exact ⟨hr, hE, hr ▸ hBt, hr ▸ hℓ, by omega⟩


/-- **Slot-restricted non-interference (threads).** If copy `c`'s filter bits are `false` at its thread-merge slots
(in the run with `c`), then the run with `c` and the run where `c` is not sampled (all other coins equal; `c`'s other
bits arbitrary) have the same pools up to `c` itself. -/
theorem tpools_erase_of_slots (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false)
    (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (hφ : ∀ x ℓ k, InSlotsT E thr0 D Bt lev c x ℓ → φ (curT E thr0 D Bt c x) x ℓ k c = false)
    (hφ' : ∀ r a ℓ k, AgreeOff c (φ r a ℓ k) (φ' r a ℓ k)) :
    ∀ a r ℓ, (tpools E thr0 C θ R K D Lv Bt lev ωs φ a r ℓ).erase c =
      tpools E thr0 C θ R K D Lv Bt lev ωs' φ' a r ℓ := by
  classical
  intro a
  induction a with
  | zero => intro r ℓ; simp [tpools]
  | succ a ih =>
    intro r ℓ
    have hfun : (fun r ℓ => (tpools E thr0 C θ R K D Lv Bt lev ωs φ a r ℓ).erase c) =
        tpools E thr0 C θ R K D Lv Bt lev ωs' φ' a := by
      funext r ℓ; exact ih r ℓ
    simp only [tpools]
    split_ifs with hB
    · rw [mergeUpTo_erase_of_passive E C θ R K c (φ r) (φ' r) (hφ' r) a _ (lev r a) (fun m' hm' => by
        by_cases hin : c ∈ stage E C θ R K (φ r) a
            (startPools E thr0 D Lv Bt ωs a (tpools E thr0 C θ R K D Lv Bt lev ωs φ a) r) m' (m' + 1) ∪
          stage E C θ R K (φ r) a
            (startPools E thr0 D Lv Bt ωs a (tpools E thr0 C θ R K D Lv Bt lev ωs φ a) r) m' m'
        · obtain ⟨hr, hsl⟩ := inSlotsT_of_mem_input hB hm' hin
          exact passiveIter_of_false E C (a + 1) θ R c _ K (φ r a m') (fun k => hr ▸ hφ a m' k hsl)
        · exact Pool.P0062.passiveIter_of_not_mem E C θ R (a + 1) c _ hin K (φ r a m'))]
      congr 1
      funext j
      rw [startPools_erase c ωs ωs' hs hs', hfun]
    · rw [startPools_erase c ωs ωs' hs hs', hfun]

/-- No slot before entry. -/
theorem not_inSlotsT_of_lt (c : ι) {x ℓ : ℕ} (hx : x < E c) : ¬ InSlotsT E thr0 D Bt lev c x ℓ :=
  fun h => absurd h.1 (by omega)

/-- **Horizon version of `tpools_erase_of_slots`.** It suffices that `c`'s filter bits are `false` at its slots at
the units `x < N` (a finite, clock-determined set of coordinates once the levels are bounded); the conclusion holds at
every boundary `a ≤ N`. -/
theorem tpools_erase_of_slots_lt (N : ℕ) (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs')
    (hs' : ωs' c = false)
    (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (hφ : ∀ x ℓ k, x < N → InSlotsT E thr0 D Bt lev c x ℓ → φ (curT E thr0 D Bt c x) x ℓ k c = false)
    (hφ' : ∀ r a ℓ k, AgreeOff c (φ r a ℓ k) (φ' r a ℓ k)) :
    ∀ a, a ≤ N → ∀ r ℓ, (tpools E thr0 C θ R K D Lv Bt lev ωs φ a r ℓ).erase c =
      tpools E thr0 C θ R K D Lv Bt lev ωs' φ' a r ℓ := by
  classical
  intro a
  induction a with
  | zero => intro _ r ℓ; simp [tpools]
  | succ a ih =>
    intro haN r ℓ
    have hfun : (fun r ℓ => (tpools E thr0 C θ R K D Lv Bt lev ωs φ a r ℓ).erase c) =
        tpools E thr0 C θ R K D Lv Bt lev ωs' φ' a := by
      funext r ℓ; exact ih (by omega) r ℓ
    simp only [tpools]
    split_ifs with hB
    · rw [mergeUpTo_erase_of_passive E C θ R K c (φ r) (φ' r) (hφ' r) a _ (lev r a) (fun m' hm' => by
        by_cases hin : c ∈ stage E C θ R K (φ r) a
            (startPools E thr0 D Lv Bt ωs a (tpools E thr0 C θ R K D Lv Bt lev ωs φ a) r) m' (m' + 1) ∪
          stage E C θ R K (φ r) a
            (startPools E thr0 D Lv Bt ωs a (tpools E thr0 C θ R K D Lv Bt lev ωs φ a) r) m' m'
        · obtain ⟨hr, hsl⟩ := inSlotsT_of_mem_input hB hm' hin
          exact passiveIter_of_false E C (a + 1) θ R c _ K (φ r a m')
            (fun k => hr ▸ hφ a m' k (by omega) hsl)
        · exact Pool.P0062.passiveIter_of_not_mem E C θ R (a + 1) c _ hin K (φ r a m'))]
      congr 1
      funext j
      rw [startPools_erase c ωs ωs' hs hs', hfun]
    · rw [startPools_erase c ωs ωs' hs hs', hfun]

end Pool.P0081
