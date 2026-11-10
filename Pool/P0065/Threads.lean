import Pool.P0052.PoolProcess
import Pool.P0056.WalkI

/-!
# Peng–Rubinstein's threaded pool process WITH inheritance (exact covers, explicit coins), and its
# eviction times satisfy the walk hypotheses of P0056

Threads `r < D`, thread `r` has epochs of `Bt r` units (`Bt (r+1) ∣ Bt r`, `Bt (D-1) = 1`, `BtHyp`).
Time is counted in units (the finest epochs). Each thread's sub-pools are P0052's levels; merges
are P0052's `mergeUpTo` (P0042's `mstep` with fresh filter bits, fixed length `K`).

* `tpools ωs φ a r ℓ`: the pools at the boundary `a`. At the start of unit `a`
  (`startPools`): the coarsest thread with a new epoch is `canonT a`; every finer thread restarts and
  its pools are moved into level 0 of thread `canonT a` (`inherit`, PR23 Algorithm 8); then every
  thread with a new epoch samples its new copies into its level 0 (`sample`, copies `c` with
  `E c = a`, `thr0 c = r` and sampling bit `ωs c`). At the end of unit `a` every thread whose epoch
  ends merges its levels `0..lev r a`.
* `curT c x`: the thread of copy `c` at unit `x` (its entry thread, lowered to `canonT m` at every
  restart `m`). `tpools_ok`/`start_ok`: a copy is only ever in thread `curT c x`, at a level `< Lv`.
* `removal_dvd`: a copy is removed only at a boundary where its current thread merges.
* `removal_hyp`: hence its removal time `e` satisfies `Bt (thr0 c) ∣ e`, `E c + Bt (thr0 c) ≤ e`, and
  `Bt j ∣ e` whenever a multiple of `Bt j` (`j < thr0 c`) lies strictly inside `(E c, e)`.
* `evict`, `hypI_evict`: the eviction time of the comparator's copy forced into thread `j` at unit
  `a` (as a never-filter copy, `forceS`/`forceF`) satisfies P0056's `HypI` (the inheritance walk).
* `tpools_erase`, `forced_erase`, `forced_erase_start`: a never-filter copy does not interfere: the
  forced run is the actual run plus the copy.
* `covered_of_removed_mergeUpTo` (and the `mstep`, `iter`, `mergeOne` versions): a copy removed by a
  merge was covered (P0030 `Covered`, at the merge time) by a filter set drawn from that merge's
  input.
-/

namespace Pool.P0065

open Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ)

/-- Coarsest thread with an epoch boundary at `a` (or `D - 1`). -/
noncomputable def canonT (a : ℕ) : ℕ :=
  Nat.find (⟨D - 1, Or.inr le_rfl⟩ : ∃ r, Bt r ∣ a ∨ D - 1 ≤ r)

/-- Copies sampled into thread `r` at unit `a`. -/
noncomputable def newAtT (ωs : ι → Bool) (a r : ℕ) : Finset ι :=
  Finset.univ.filter fun c => E c = a ∧ thr0 c = r ∧ ωs c = true

/-- Inheritance at the start of unit `a`: threads finer than `canonT a` are emptied into level 0 of
thread `canonT a`. -/
noncomputable def inherit (a : ℕ) (P : ℕ → ℕ → Finset ι) : ℕ → ℕ → Finset ι := fun r ℓ =>
  if r < canonT D Bt a then P r ℓ
  else if r = canonT D Bt a then
    (if ℓ = 0 then P r 0 ∪ (Finset.Ioo r D).biUnion (fun r' => (Finset.range Lv).biUnion (P r'))
     else P r ℓ)
  else ∅

/-- Sampling at the start of unit `a`. -/
noncomputable def sample (ωs : ι → Bool) (a : ℕ) (P : ℕ → ℕ → Finset ι) : ℕ → ℕ → Finset ι :=
  fun r ℓ => if ℓ = 0 ∧ Bt r ∣ a ∧ r < D then P r 0 ∪ newAtT E thr0 ωs a r else P r ℓ

/-- The pools at the start of unit `a`, after inheritance and sampling. -/
noncomputable def startPools (ωs : ι → Bool) (a : ℕ) (P : ℕ → ℕ → Finset ι) : ℕ → ℕ → Finset ι :=
  sample E thr0 D Bt ωs a (inherit D Lv Bt a P)

/-- The threaded process: pools at the boundary `a` (before the start operations of unit `a`). -/
noncomputable def tpools (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) : ℕ → ℕ → ℕ → Finset ι
  | 0 => fun _ _ => ∅
  | a + 1 => fun r =>
      if Bt r ∣ a + 1 then
        mergeUpTo E C θ R K (φ r) a (lev r a) (startPools E thr0 D Lv Bt ωs a (tpools ωs φ a) r)
      else startPools E thr0 D Lv Bt ωs a (tpools ωs φ a) r


/-- Current thread of copy `c` at unit `x` (if alive): its entry thread, lowered at every restart. -/
noncomputable def curT (c : ι) : ℕ → ℕ
  | 0 => thr0 c
  | x + 1 => if x + 1 ≤ E c then thr0 c else min (curT c x) (canonT D Bt (x + 1))

variable {E thr0 C θ R K D Lv Bt lev}

section Basic

lemma canonT_le_of_dvd {a j : ℕ} (h : Bt j ∣ a) : canonT D Bt a ≤ j :=
  Nat.find_min' _ (Or.inl h)

lemma canonT_le (a : ℕ) : canonT D Bt a ≤ D - 1 := Nat.find_min' _ (Or.inr le_rfl)

lemma curT_of_le {c : ι} {x : ℕ} (hx : x ≤ E c) : curT E thr0 D Bt c x = thr0 c := by
  cases x with
  | zero => rfl
  | succ x => simp [curT, hx]

lemma curT_succ {c : ι} {x : ℕ} (hx : E c ≤ x) :
    curT E thr0 D Bt c (x + 1) = min (curT E thr0 D Bt c x) (canonT D Bt (x + 1)) := by
  simp [curT, show ¬ x + 1 ≤ E c by omega]

lemma curT_le_thr0 (c : ι) : ∀ x, curT E thr0 D Bt c x ≤ thr0 c
  | 0 => le_rfl
  | x + 1 => by
    by_cases hx : x + 1 ≤ E c
    · simp [curT, hx]
    · simp only [curT, hx, if_false]
      exact (min_le_left _ _).trans (curT_le_thr0 c x)

lemma curT_mono (c : ι) {x y : ℕ} (hxy : x ≤ y) (hx : E c ≤ x) :
    curT E thr0 D Bt c y ≤ curT E thr0 D Bt c x := by
  induction y, hxy using Nat.le_induction with
  | base => exact le_rfl
  | succ y hxy ih => rw [curT_succ (by omega)]; exact (min_le_left _ _).trans ih

lemma curT_le_canonT (c : ι) {m y : ℕ} (hm : E c < m) (hmy : m ≤ y) :
    curT E thr0 D Bt c y ≤ canonT D Bt m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine (curT_mono c hmy (by omega)).trans ?_
  rw [curT_succ (by omega)]; exact min_le_right _ _

end Basic


section Merge

lemma mem_iter_sub {c : ι} {t : ℕ} {Q : Finset ι} {m : ℕ} {ω : Fin m → ι → Bool}
    (h : c ∈ iter (mstep E C t θ R) Q m ω) : c ∈ Q :=
  iter_sub (mstep E C t θ R) Q (fun Q' y => mstep_sub E C t θ R Q' y) m ω h

lemma mem_mergeOne {φ : ℕ → ℕ → Fin K → ι → Bool} {a ℓ : ℕ} {P : ℕ → Finset ι} {j : ℕ} {c : ι}
    (h : c ∈ mergeOne E C θ R K φ a ℓ P j) :
    (c ∈ P (ℓ + 1) ∨ c ∈ P ℓ) ∧ j = ℓ + 1 ∨ (j ≠ ℓ ∧ j ≠ ℓ + 1 ∧ c ∈ P j) := by
  unfold mergeOne at h
  by_cases hj : j = ℓ
  · subst hj; simp at h
  rw [Function.update_of_ne hj] at h
  by_cases hj1 : j = ℓ + 1
  · subst hj1
    rw [Function.update_self] at h
    exact Or.inl ⟨Finset.mem_union.1 (mem_iter_sub h), rfl⟩
  · rw [Function.update_of_ne hj1] at h
    exact Or.inr ⟨hj, hj1, h⟩

/-- Membership after `mergeUpTo m`: the copy was in some input level, and it now sits at a level
`≤ m + 1` or at its old level. -/
lemma mem_mergeUpTo {φ : ℕ → ℕ → Fin K → ι → Bool} {a : ℕ} :
    ∀ (m : ℕ) (P : ℕ → Finset ι) (j : ℕ) (c : ι), c ∈ mergeUpTo E C θ R K φ a m P j →
      (∃ j', c ∈ P j') ∧ (j ≤ m + 1 ∨ c ∈ P j)
  | 0, P, j, c, h => by
    rcases mem_mergeOne h with ⟨h1 | h1, rfl⟩ | ⟨-, -, h1⟩
    · exact ⟨⟨_, h1⟩, Or.inl le_rfl⟩
    · exact ⟨⟨_, h1⟩, Or.inl le_rfl⟩
    · exact ⟨⟨_, h1⟩, Or.inr h1⟩
  | m + 1, P, j, c, h => by
    simp only [mergeUpTo] at h
    rcases mem_mergeOne h with ⟨h1 | h1, rfl⟩ | ⟨-, -, h1⟩
    · obtain ⟨⟨j', hj'⟩, -⟩ := mem_mergeUpTo m P _ c h1
      exact ⟨⟨j', hj'⟩, Or.inl le_rfl⟩
    · obtain ⟨⟨j', hj'⟩, -⟩ := mem_mergeUpTo m P _ c h1
      exact ⟨⟨j', hj'⟩, Or.inl (by omega)⟩
    · obtain ⟨⟨j', hj'⟩, h2⟩ := mem_mergeUpTo m P j c h1
      exact ⟨⟨j', hj'⟩, h2.imp (fun h => by omega) id⟩

end Merge


section Loc

variable (E thr0 D Lv Bt)

/-- Location invariant of the pools at the start of unit `x` (after inheritance and sampling). -/
def StartOK (x : ℕ) (S : ℕ → ℕ → Finset ι) : Prop :=
  ∀ c r ℓ, c ∈ S r ℓ → E c ≤ x ∧ r = curT E thr0 D Bt c x ∧ ℓ < Lv ∧ r < D

/-- Location invariant of the pools at the boundary `x` (after the merges ending unit `x - 1`). -/
def BdOK (x : ℕ) (P : ℕ → ℕ → Finset ι) : Prop :=
  ∀ c r ℓ, c ∈ P r ℓ → E c < x ∧ r = curT E thr0 D Bt c (x - 1) ∧ ℓ < Lv ∧ r < D

variable {E thr0 D Lv Bt}

lemma curT_step {c : ι} {x : ℕ} (hx : E c < x) :
    curT E thr0 D Bt c x = min (curT E thr0 D Bt c (x - 1)) (canonT D Bt x) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [curT_succ (by omega)]; rfl

lemma start_ok (hD : 0 < D) (hLv : 0 < Lv) {x : ℕ} {P : ℕ → ℕ → Finset ι} (hP : BdOK E thr0 D Lv Bt x P)
    (ωs : ι → Bool) : StartOK E thr0 D Lv Bt x (startPools E thr0 D Lv Bt ωs x P) := by
  have hcan : canonT D Bt x < D := lt_of_le_of_lt (canonT_le x) (by omega)
  -- inheritance
  have hinh : ∀ c r ℓ, c ∈ inherit D Lv Bt x P r ℓ →
      E c ≤ x ∧ r = curT E thr0 D Bt c x ∧ ℓ < Lv ∧ r < D := by
    intro c r ℓ hc
    unfold inherit at hc
    by_cases h1 : r < canonT D Bt x
    · rw [if_pos h1] at hc
      obtain ⟨hE, hr, hl, hrD⟩ := hP c r ℓ hc
      refine ⟨hE.le, ?_, hl, hrD⟩
      rw [curT_step hE, ← hr, min_eq_left h1.le]
    rw [if_neg h1] at hc
    by_cases h2 : r = canonT D Bt x
    · rw [if_pos h2] at hc
      by_cases h3 : ℓ = 0
      · rw [if_pos h3] at hc
        rcases Finset.mem_union.1 hc with hc | hc
        · obtain ⟨hE, hr, -, -⟩ := hP c r 0 hc
          exact ⟨hE.le, by rw [curT_step hE, ← hr, ← h2, min_self], by omega, h2 ▸ hcan⟩
        · simp only [Finset.mem_biUnion, Finset.mem_Ioo, Finset.mem_range] at hc
          obtain ⟨r', ⟨hr'1, -⟩, ℓ', -, hc⟩ := hc
          obtain ⟨hE, hr', -, -⟩ := hP c r' ℓ' hc
          refine ⟨hE.le, ?_, by omega, h2 ▸ hcan⟩
          rw [curT_step hE, ← hr', min_eq_right (by omega), h2]
      · rw [if_neg h3] at hc
        obtain ⟨hE, hr, hl, hrD⟩ := hP c r ℓ hc
        exact ⟨hE.le, by rw [curT_step hE, ← hr, ← h2, min_self], hl, hrD⟩
    · rw [if_neg h2] at hc; simp at hc
  intro c r ℓ hc
  unfold startPools sample at hc
  by_cases hs : ℓ = 0 ∧ Bt r ∣ x ∧ r < D
  · rw [if_pos hs] at hc
    rcases Finset.mem_union.1 hc with hc | hc
    · exact hs.1 ▸ hinh c r 0 hc
    · simp only [newAtT, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      obtain ⟨hE, hthr, -⟩ := hc
      exact ⟨hE.le, by rw [curT_of_le hE.ge, hthr], by omega, hs.2.2⟩
  · rw [if_neg hs] at hc
    exact hinh c r ℓ hc

lemma tpools_ok (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) :
    ∀ x, BdOK E thr0 D Lv Bt x (tpools E thr0 C θ R K D Lv Bt lev ωs φ x)
  | 0 => by intro c r ℓ hc; simp [tpools] at hc
  | x + 1 => by
    have hS := start_ok hD hLv (tpools_ok hD hLv hlev ωs φ x) ωs (x := x)
    intro c r ℓ hc
    simp only [tpools] at hc
    split_ifs at hc with hB
    · obtain ⟨⟨j', hj'⟩, hlv⟩ := mem_mergeUpTo _ _ ℓ c hc
      obtain ⟨hE, hr, hl, hrD⟩ := hS c r j' hj'
      refine ⟨by omega, by simpa using hr, ?_, hrD⟩
      rcases hlv with hlv | hlv
      · have := hlev r x; omega
      · exact (hS c r ℓ hlv).2.2.1
    · obtain ⟨hE, hr, hl, hrD⟩ := hS c r ℓ hc
      exact ⟨by omega, by simpa using hr, hl, hrD⟩

end Loc


section Removal

variable (E thr0 C θ R K D Lv Bt lev) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

/-- `c` is in some pool at the boundary `x`. -/
def Alive (x : ℕ) (c : ι) : Prop :=
  ∃ r ℓ, c ∈ tpools E thr0 C θ R K D Lv Bt lev ωs φ x r ℓ

/-- `c` is in some pool at the start of unit `x`. -/
def SAlive (x : ℕ) (c : ι) : Prop :=
  ∃ r ℓ, c ∈ startPools E thr0 D Lv Bt ωs x (tpools E thr0 C θ R K D Lv Bt lev ωs φ x) r ℓ

variable {E thr0 C θ R K D Lv Bt lev ωs φ}

lemma salive_of_alive (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {x : ℕ} {c : ι}
    (h : Alive E thr0 C θ R K D Lv Bt lev ωs φ x c) : SAlive E thr0 C θ R K D Lv Bt lev ωs φ x c := by
  obtain ⟨r, ℓ, hc⟩ := h
  have hok := tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (C := C) (θ := θ) (R := R) (lev := lev)
    hD hLv hlev ωs φ x c r ℓ hc
  have hcan : canonT D Bt x < D := lt_of_le_of_lt (canonT_le x) (by omega)
  -- the inherited pools keep `c`
  have hinh : ∃ r' ℓ', c ∈ inherit D Lv Bt x (tpools E thr0 C θ R K D Lv Bt lev ωs φ x) r' ℓ' := by
    by_cases h1 : r < canonT D Bt x
    · exact ⟨r, ℓ, by unfold inherit; rw [if_pos h1]; exact hc⟩
    by_cases h2 : r = canonT D Bt x
    · refine ⟨r, ℓ, ?_⟩
      unfold inherit; rw [if_neg h1, if_pos h2]
      split_ifs with h3
      · subst h3; exact Finset.mem_union_left _ hc
      · exact hc
    · refine ⟨canonT D Bt x, 0, ?_⟩
      unfold inherit
      rw [if_neg (lt_irrefl _), if_pos rfl, if_pos rfl]
      refine Finset.mem_union_right _ ?_
      simp only [Finset.mem_biUnion, Finset.mem_Ioo, Finset.mem_range]
      exact ⟨r, ⟨by omega, hok.2.2.2⟩, ℓ, hok.2.2.1, hc⟩
  obtain ⟨r', ℓ', hc'⟩ := hinh
  refine ⟨r', ℓ', ?_⟩
  unfold startPools sample
  split_ifs with hs
  · rw [hs.1] at hc'; exact Finset.mem_union_left _ hc'
  · exact hc'

lemma alive_succ_of_not_dvd (hD : 0 < D) (hLv : 0 < Lv) {x : ℕ} {c : ι}
    (h : SAlive E thr0 C θ R K D Lv Bt lev ωs φ x c)
    (hlev : ∀ r a, lev r a + 1 < Lv)
    (hnd : ¬ Bt (curT E thr0 D Bt c x) ∣ x + 1) :
    Alive E thr0 C θ R K D Lv Bt lev ωs φ (x + 1) c := by
  obtain ⟨r, ℓ, hc⟩ := h
  have hS := start_ok (E := E) (thr0 := thr0) (Bt := Bt) hD hLv
    (tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (C := C) (θ := θ) (R := R) (lev := lev)
      hD hLv hlev ωs φ x) ωs (x := x)
  obtain ⟨-, hr, -, -⟩ := hS c r ℓ hc
  refine ⟨r, ℓ, ?_⟩
  simp only [tpools]
  rw [if_neg (hr ▸ hnd)]
  exact hc

/-- **Removal schedule.** If `c` is in the start pools of unit `x0` and is not alive at the boundary
`y > x0`, then it was removed at some boundary `x + 1 ∈ (x0, y]` where its current thread merges. -/
lemma removal_dvd (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {c : ι} {x0 : ℕ}
    (h0 : SAlive E thr0 C θ R K D Lv Bt lev ωs φ x0 c) :
    ∀ y, x0 < y → ¬ Alive E thr0 C θ R K D Lv Bt lev ωs φ y c →
      ∃ x, x0 ≤ x ∧ x < y ∧ SAlive E thr0 C θ R K D Lv Bt lev ωs φ x c ∧
        ¬ Alive E thr0 C θ R K D Lv Bt lev ωs φ (x + 1) c ∧ Bt (curT E thr0 D Bt c x) ∣ x + 1 := by
  intro y hy hna
  induction y, hy using Nat.le_induction with
  | base =>
    refine ⟨x0, le_rfl, by omega, h0, hna, ?_⟩
    by_contra hnd
    exact hna (alive_succ_of_not_dvd hD hLv h0 hlev hnd)
  | succ y hy ih =>
    by_cases hal : Alive E thr0 C θ R K D Lv Bt lev ωs φ y c
    · have hs := salive_of_alive hD hLv hlev hal
      refine ⟨y, by omega, by omega, hs, hna, ?_⟩
      by_contra hnd
      exact hna (alive_succ_of_not_dvd hD hLv hs hlev hnd)
    · obtain ⟨x, h1, h2, h3, h4, h5⟩ := ih hal
      exact ⟨x, h1, by omega, h3, h4, h5⟩

end Removal


section Schedule

/-- Hypotheses on the thread epoch lengths: positive, nested, finest equal to one unit. -/
structure BtHyp (D : ℕ) (Bt : ℕ → ℕ) : Prop where
  hD : 0 < D
  pos : ∀ r, 0 < Bt r
  dvd : ∀ r, r + 1 < D → Bt (r + 1) ∣ Bt r
  last : Bt (D - 1) = 1

lemma BtHyp.dvd_of_le (hB : BtHyp D Bt) {i j : ℕ} (hij : i ≤ j) (hj : j < D) : Bt j ∣ Bt i := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_rfl
  | succ k hik ih => exact (hB.dvd k hj).trans (ih (by omega))

lemma BtHyp.canonT_dvd (hB : BtHyp D Bt) (m : ℕ) : Bt (canonT D Bt m) ∣ m := by
  have hs := Nat.find_spec (⟨D - 1, Or.inr le_rfl⟩ : ∃ r, Bt r ∣ m ∨ D - 1 ≤ r)
  rcases hs with hs | hs
  · exact hs
  · have : canonT D Bt m = D - 1 := le_antisymm (canonT_le m) hs
    rw [this, hB.last]; exact one_dvd m

lemma curT_cases (c : ι) : ∀ x, curT E thr0 D Bt c x = thr0 c ∨
    ∃ m, E c < m ∧ m ≤ x ∧ canonT D Bt m = curT E thr0 D Bt c x
  | 0 => Or.inl rfl
  | x + 1 => by
    by_cases hx : x + 1 ≤ E c
    · exact Or.inl (curT_of_le hx)
    · rw [curT_succ (by omega)]
      rcases le_total (curT E thr0 D Bt c x) (canonT D Bt (x + 1)) with h | h
      · rw [min_eq_left h]
        rcases curT_cases c x with h' | ⟨m, h1, h2, h3⟩
        · exact Or.inl h'
        · exact Or.inr ⟨m, h1, by omega, h3⟩
      · rw [min_eq_right h]
        exact Or.inr ⟨x + 1, by omega, le_rfl, rfl⟩

/-- **The removal time of a copy satisfies the walk hypotheses** (P0057's `lb`, `edvd`, `align`):
if `c` entered thread `thr0 c` at `E c` (a multiple of `Bt (thr0 c)`) and is removed at the boundary
`e = x + 1` by a merge of its current thread, then `Bt (thr0 c) ∣ e`, `E c + Bt (thr0 c) ≤ e`, and
every coarser boundary strictly inside `(E c, e)` forces the corresponding divisibility of `e`. -/
theorem removal_hyp (hB : BtHyp D Bt) {c : ι} (hthr : thr0 c < D) (hent : Bt (thr0 c) ∣ E c) {x : ℕ}
    (hx : E c ≤ x) (hrem : Bt (curT E thr0 D Bt c x) ∣ x + 1) :
    Bt (thr0 c) ∣ x + 1 ∧ E c + Bt (thr0 c) ≤ x + 1 ∧
      ∀ j m, j < thr0 c → Bt j ∣ m → E c < m → m < x + 1 → Bt j ∣ x + 1 := by
  have hcur := curT_le_thr0 (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c x
  have hd1 : Bt (thr0 c) ∣ x + 1 := (hB.dvd_of_le hcur hthr).trans hrem
  refine ⟨hd1, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have hpos := hB.pos (thr0 c)
    obtain ⟨k, hk⟩ := hent
    -- no multiple of `Bt (thr0 c)` lies in `(E c, x + 1]`
    have hnomult : ∀ m, E c < m → m ≤ x + 1 → ¬ Bt (thr0 c) ∣ m := by
      intro m h1 h2 ⟨q, hq⟩
      have : k < q := by
        by_contra hc; push Not at hc
        have : Bt (thr0 c) * q ≤ Bt (thr0 c) * k := Nat.mul_le_mul_left _ hc
        omega
      have : Bt (thr0 c) * (k + 1) ≤ Bt (thr0 c) * q := Nat.mul_le_mul_left _ this
      nlinarith
    exact hnomult (x + 1) (by omega) le_rfl hd1
  · intro j m hj hm h1 h2
    have := curT_le_canonT (E := E) (thr0 := thr0) (D := D) (Bt := Bt) c h1 (show m ≤ x by omega)
    have hcj : curT E thr0 D Bt c x ≤ j := this.trans (canonT_le_of_dvd hm)
    exact (hB.dvd_of_le hcj (by omega)).trans hrem

end Schedule


section Erase

lemma inherit_erase [DecidableEq ι] (c : ι) (a : ℕ) (P : ℕ → ℕ → Finset ι) (r ℓ : ℕ) :
    (inherit D Lv Bt a P r ℓ).erase c = inherit D Lv Bt a (fun r ℓ => (P r ℓ).erase c) r ℓ := by
  unfold inherit
  split_ifs
  · rfl
  · ext x
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_biUnion, Finset.mem_Ioo,
      Finset.mem_range]
    constructor
    · rintro ⟨hx, h | ⟨r', hr', ℓ', hℓ', h⟩⟩
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨r', hr', ℓ', hℓ', hx, h⟩
    · rintro (⟨hx, h⟩ | ⟨r', hr', ℓ', hℓ', hx, h⟩)
      · exact ⟨hx, Or.inl h⟩
      · exact ⟨hx, Or.inr ⟨r', hr', ℓ', hℓ', h⟩⟩
  · rfl
  · simp

lemma newAtT_erase (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false)
    (a r : ℕ) : (newAtT E thr0 ωs a r).erase c = newAtT E thr0 ωs' a r := by
  classical
  ext x
  simp only [newAtT, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hxc, hE, ht, hx⟩; exact ⟨hE, ht, (hs x hxc) ▸ hx⟩
  · rintro ⟨hE, ht, hx⟩
    have hxc : x ≠ c := by rintro rfl; rw [hs'] at hx; exact Bool.false_ne_true hx
    exact ⟨hxc, hE, ht, (hs x hxc).symm ▸ hx⟩

lemma startPools_erase (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false)
    (a : ℕ) (P : ℕ → ℕ → Finset ι) (r ℓ : ℕ) :
    (startPools E thr0 D Lv Bt ωs a P r ℓ).erase c =
      startPools E thr0 D Lv Bt ωs' a (fun r ℓ => (P r ℓ).erase c) r ℓ := by
  classical
  unfold startPools sample
  split_ifs with h
  · rw [Finset.erase_union_distrib, inherit_erase, newAtT_erase c ωs ωs' hs hs']
  · rw [inherit_erase]

/-- **Non-interference of a copy that is never a filter** (all-slots version): removing it from the
run changes every pool only by removing it. -/
theorem tpools_erase (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs') (hs' : ωs' c = false)
    (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool) (hφ : ∀ r a ℓ k, φ r a ℓ k c = false)
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
    · rw [mergeUpTo_erase E C θ R K c (φ r) (φ' r) (hφ r) (hφ' r) a]
      congr 1
      funext j
      rw [startPools_erase c ωs ωs' hs hs', hfun]
    · rw [startPools_erase c ωs ωs' hs hs', hfun]

end Erase


section Certificate

/-- One merge iteration removes `c` only if `c` is not a filter and is covered by the filters. -/
lemma covered_of_removed_mstep {t : ℕ} {Q : Finset ι} {y : ι → Bool} {c : ι} (hc : c ∈ Q)
    (hr : c ∉ mstep E C t θ R Q y) : c ∉ Fof Q y ∧ Covered E C t θ (Fof Q y) c R := by
  classical
  unfold mstep filterRound at hr
  simp only [Finset.mem_union, Finset.mem_filter, not_or, not_and, not_not] at hr
  exact ⟨hr.2, hr.1 hc⟩

/-- Iterated merge: a removed copy was covered at some iteration by the filters drawn from a
sub-pool of the input. -/
lemma covered_of_removed_iter {t : ℕ} {c : ι} : ∀ (m : ℕ) (ω : Fin m → ι → Bool) (Q : Finset ι),
    c ∈ Q → c ∉ iter (mstep E C t θ R) Q m ω →
      ∃ Q' ⊆ Q, ∃ y : ι → Bool, c ∈ Q' ∧ c ∉ Fof Q' y ∧ Covered E C t θ (Fof Q' y) c R
  | 0, ω, Q, hc, hr => absurd hc hr
  | m + 1, ω, Q, hc, hr => by
    simp only [iter] at hr
    by_cases hin : c ∈ iter (mstep E C t θ R) Q m (Fin.init ω)
    · obtain ⟨h1, h2⟩ := covered_of_removed_mstep hin hr
      exact ⟨_, iter_sub (mstep E C t θ R) Q (fun Q' y => mstep_sub E C t θ R Q' y) m _,
        _, hin, h1, h2⟩
    · exact covered_of_removed_iter m (Fin.init ω) Q hc hin

lemma covered_of_removed_mergeOne {φ : ℕ → ℕ → Fin K → ι → Bool} {a ℓ : ℕ} {P : ℕ → Finset ι}
    {c : ι} (hc : c ∈ P ℓ ∨ c ∈ P (ℓ + 1)) (hr : ∀ j, c ∉ mergeOne E C θ R K φ a ℓ P j) :
    ∃ Q' ⊆ P (ℓ + 1) ∪ P ℓ, ∃ y : ι → Bool, c ∈ Q' ∧ c ∉ Fof Q' y ∧
      Covered E C (a + 1) θ (Fof Q' y) c R := by
  have h := hr (ℓ + 1)
  unfold mergeOne at h
  rw [Function.update_of_ne (by omega), Function.update_self] at h
  exact covered_of_removed_iter K (φ a ℓ) _ (by rcases hc with hc | hc <;> simp [hc]) h

/-- `mergeUpTo`: a copy present in some input level `≤ m + 1`... and absent from every output
level was covered at some merge iteration (merge time `a + 1`) by filters drawn from a set of
copies of the input. -/
lemma covered_of_removed_mergeUpTo {φ : ℕ → ℕ → Fin K → ι → Bool} {a : ℕ} {c : ι} :
    ∀ (m : ℕ) (P : ℕ → Finset ι), (∃ j, c ∈ P j) → (∀ j, c ∉ mergeUpTo E C θ R K φ a m P j) →
      ∃ Q' : Finset ι, (∀ x ∈ Q', ∃ j, x ∈ P j) ∧ ∃ y : ι → Bool, c ∈ Q' ∧ c ∉ Fof Q' y ∧
        Covered E C (a + 1) θ (Fof Q' y) c R := by
  intro m
  induction m with
  | zero =>
    intro P ⟨j, hj⟩ hr
    by_cases hj01 : j = 0 ∨ j = 1
    · obtain ⟨Q', hQ', y, h1, h2, h3⟩ := covered_of_removed_mergeOne (ℓ := 0) (P := P)
        (by rcases hj01 with rfl | rfl <;> simp [hj]) (fun j => hr j)
      refine ⟨Q', fun x hx => ?_, y, h1, h2, h3⟩
      rcases Finset.mem_union.1 (hQ' hx) with h | h
      · exact ⟨1, h⟩
      · exact ⟨0, h⟩
    · exfalso
      apply hr j
      unfold mergeUpTo mergeOne
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hj
  | succ m ih =>
    intro P hex hr
    simp only [mergeUpTo] at hr
    -- either `c` survives `mergeUpTo m` (then it is removed at the last merge) or not
    by_cases hmid : ∃ j, c ∈ mergeUpTo E C θ R K φ a m P j
    · obtain ⟨j, hj⟩ := hmid
      by_cases hjl : j = m + 1 ∨ j = m + 2
      · obtain ⟨Q', hQ', y, h1, h2, h3⟩ := covered_of_removed_mergeOne (ℓ := m + 1)
          (P := mergeUpTo E C θ R K φ a m P)
          (by rcases hjl with rfl | rfl <;> simp [hj]) (fun j => hr j)
        refine ⟨Q', fun x hx => ?_, y, h1, h2, h3⟩
        have hx' : ∃ j, x ∈ mergeUpTo E C θ R K φ a m P j := by
          rcases Finset.mem_union.1 (hQ' hx) with h | h
          · exact ⟨_, h⟩
          · exact ⟨_, h⟩
        obtain ⟨j', hj'⟩ := hx'
        exact (mem_mergeUpTo m P j' x hj').1
      · exfalso
        apply hr j
        unfold mergeOne
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hj
    · push Not at hmid
      exact ih P hex hmid

end Certificate

section Monotone

lemma not_mem_startPools_of_not_alive (hD : 0 < D) {x : ℕ} {c : ι} {ωs : ι → Bool}
    {P : ℕ → ℕ → Finset ι} (hP : ∀ r ℓ, c ∉ P r ℓ) (hx : E c ≠ x) :
    ∀ r ℓ, c ∉ startPools E thr0 D Lv Bt ωs x P r ℓ := by
  intro r ℓ hc
  unfold startPools sample at hc
  have hinh : ∀ r ℓ, c ∉ inherit D Lv Bt x P r ℓ := by
    intro r ℓ hc'
    unfold inherit at hc'
    split_ifs at hc' with h1 h2 h3
    · exact hP r ℓ hc'
    · rcases Finset.mem_union.1 hc' with h | h
      · exact hP r 0 h
      · simp only [Finset.mem_biUnion] at h
        obtain ⟨r', -, ℓ', -, h⟩ := h
        exact hP r' ℓ' h
    · exact hP r ℓ hc'
    · simp at hc'
  split_ifs at hc with hs
  · rcases Finset.mem_union.1 hc with h | h
    · exact hinh r 0 h
    · simp [newAtT] at h; exact hx h.1
  · exact hinh r ℓ hc

end Monotone


section Bridge

variable (E thr0 C θ R K D Lv Bt lev)

/-- Sampling bits with the copy `c` forced in. -/
def forceS (ωs : ι → Bool) (c : ι) : ι → Bool := Function.update ωs c true

/-- Filter bits with the copy `c` never a filter. -/
def forceF (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) : ℕ → ℕ → ℕ → Fin K → ι → Bool :=
  fun r a ℓ k x => if x = c then false else φ r a ℓ k x

/-- Eviction time of the comparator's copy `cstar j a` (thread `j`, entry `a`) in the run where it
is forced in as a never-filter copy: the first boundary `y ∈ (a, T]` at which it is not in any pool,
or `none`. -/
noncomputable def evict (T : ℕ) (cstar : ℕ → ℕ → ι) (ωs : ι → Bool)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (j a : ℕ) : Option ℕ :=
  open Classical in
  if h : ∃ y, a < y ∧ y ≤ T ∧ ¬ Alive E thr0 C θ R K D Lv Bt lev (forceS ωs (cstar j a))
      (forceF K φ (cstar j a)) y (cstar j a) then some (Nat.find h) else none

variable {E thr0 C θ R K D Lv Bt lev}

lemma salive_entry (hD : 0 < D) (hLv : 0 < Lv) {c : ι} {ωs : ι → Bool}
    {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} (hs : ωs c = true) (hthr : thr0 c < D)
    (hent : Bt (thr0 c) ∣ E c) : SAlive E thr0 C θ R K D Lv Bt lev ωs φ (E c) c := by
  refine ⟨thr0 c, 0, ?_⟩
  unfold startPools sample
  rw [if_pos ⟨rfl, hent, hthr⟩]
  refine Finset.mem_union_right _ ?_
  simp [newAtT, hs]

/-- **The eviction times of the threaded process satisfy P0056's walk hypothesis `HypI`**
(thread indices `0..D-1` here are P0056's `0..D-1`, i.e. its `D` is `D - 1`). -/
theorem hypI_evict (hB : BtHyp D Bt) (hchain : ∀ k, Bt (k + 1) ∣ Bt k) (hLv : 0 < Lv)
    (hlev : ∀ r a, lev r a + 1 < Lv) {T : ℕ} (hT : Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < T → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) :
    Pool.P0056.HypI (D - 1) Bt T (fun j a => evict E thr0 C θ R K D Lv Bt lev T cstar ωs φ j a) where
  pos := hB.pos
  chain := hchain
  T_dvd := hT
  ev_ge j a e hj hd haT he := (key j a e hj hd haT he).2.1
  ev_dvd j a e hj hd haT he := (key j a e hj hd haT he).1
  ev_leT j a e hj hd haT he := (key j a e hj hd haT he).2.2.1
  ev_cross j a e i hj hd haT he hi hnx := by
    obtain ⟨-, -, -, hal⟩ := key j a e hj hd haT he
    refine hal i (Pool.P0049.nxt (B := Bt) i a) hi ?_ ?_ hnx
    · exact Dvd.intro_left _ rfl
    · unfold Pool.P0049.nxt
      have := Nat.lt_div_mul_add (a := a) (hB.pos i)
      nlinarith
where
  key (j a e : ℕ) (hj : j ≤ D - 1) (hd : Bt j ∣ a) (haT : a < T)
      (he : evict E thr0 C θ R K D Lv Bt lev T cstar ωs φ j a = some e) :
      Bt j ∣ e ∧ a + Bt j ≤ e ∧ e ≤ T ∧
        ∀ i m, i < j → Bt i ∣ m → a < m → m < e → Bt i ∣ e := by
    classical
    have hD := hB.hD
    have hE' := hE j a hj hd haT
    have hthr' := hthr j a hj hd haT
    set c := cstar j a with hc
    unfold evict at he
    split_ifs at he with h
    simp only [Option.some.injEq] at he
    obtain ⟨hae, heT, hna⟩ := he ▸ Nat.find_spec h
    have hmin : ∀ y, a < y → y < e → Alive E thr0 C θ R K D Lv Bt lev (forceS ωs c)
        (forceF K φ c) y c := by
      intro y h1 h2
      by_contra hc'
      exact Nat.find_min h (he ▸ h2) ⟨h1, by omega, hc'⟩
    have hs0 : SAlive E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) a c := by
      have := salive_entry (E := E) (thr0 := thr0) (D := D) (Lv := Lv) (Bt := Bt) (K := K)
        (C := C) (θ := θ) (R := R) (lev := lev) (φ := forceF K φ c) hD hLv
        (c := c) (ωs := forceS ωs c) (by simp [forceS])
        (by rw [hthr']; omega) (by rw [hthr', hE']; exact hd)
      rwa [hE'] at this
    obtain ⟨x, hx1, hx2, -, hx4, hx5⟩ := removal_dvd hD hLv hlev hs0 e hae hna
    have hxe : x + 1 = e := by
      by_contra hne
      exact hx4 (hmin (x + 1) (by omega) (by omega))
    have := removal_hyp (E := E) (thr0 := thr0) (D := D) (Bt := Bt) hB (c := c)
      (by rw [hthr']; omega) (by rw [hthr', hE']; exact hd) (x := x)
      (by rw [hE']; exact hx1) hx5
    rw [hthr', hE'] at this
    rw [← hxe]
    exact ⟨this.1, this.2.1, by omega, fun i m hi hm h1 h2 => this.2.2 i m hi hm h1 h2⟩

end Bridge


section Forced

/-- **The forced run is the actual run plus the copy**: if `c` is not actually sampled, forcing it in
as a never-filter copy changes no pool except by adding `c`. -/
theorem forced_erase {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (a r ℓ : ℕ) :
    (tpools E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) a r ℓ).erase c =
      tpools E thr0 C θ R K D Lv Bt lev ωs φ a r ℓ := by
  apply tpools_erase
  · intro x hx; simp [forceS, Function.update_of_ne hx]
  · exact hc
  · intro r a ℓ k; simp [forceF]
  · intro r a ℓ k x hx; simp [forceF, hx]

/-- The start pools of the forced run are those of the actual run plus the copy. -/
theorem forced_erase_start {c : ι} {ωs : ι → Bool} (hc : ωs c = false)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (a r ℓ : ℕ) :
    (startPools E thr0 D Lv Bt (forceS ωs c) a
        (tpools E thr0 C θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) a) r ℓ).erase c =
      startPools E thr0 D Lv Bt ωs a (tpools E thr0 C θ R K D Lv Bt lev ωs φ a) r ℓ := by
  rw [startPools_erase c (forceS ωs c) ωs (fun x hx => by simp [forceS, Function.update_of_ne hx]) hc]
  congr 1
  funext r ℓ
  exact forced_erase hc φ a r ℓ

end Forced

end Pool.P0065
