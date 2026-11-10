import Pool.Prelude

/-!
# The multi-thread walk of Peng–Rubinstein's boosting, WITH inheritance (abstract, combinatorial)

Levels (threads) `r < R` with epoch lengths `B r`: `B 0` is the coarsest, `B (r+1) ∣ B r`; the horizon
`T` satisfies `B 0 ∣ T`. An eviction function `t τ r : Option ℕ` gives, for a copy of the comparator
entering level `r` at the epoch start `τ` (`B r ∣ τ`), the time `e` at which it is covered (`some e`),
or `none` (a bad epoch of level `r`).

Hypotheses (`Hyp`) on covered copies `t τ r = some e`:
* `lb`, `ub`, `edvd`: `τ + B r ≤ e ≤ T` and `B r ∣ e` (covers happen at merges, i.e. at epoch ends of
  the copy's level or of a coarser one);
* `align`: if `[τ, e)` contains a boundary `m` of a coarser level `j < r` strictly inside, then
  `B j ∣ e`. In Peng–Rubinstein's Algorithm 8 a copy that survives the restart of its thread at `m`
  is inherited by the lowest thread with a new epoch at `m` (a level `≤ j`), whose later merges are
  at multiples of `B j`. Intervals may therefore cross restarts; this is the case P0049 excludes.

The walk (`walk`, `theWalk`) starts at `(0, 0)`. At a point `(τ, r)`:
* covered at `e`: record the interval `[τ, e)`, continue at `(e, canon e)` (`canon e` = coarsest level
  whose grid contains `e`);
* bad and `r + 1 < R`: descend to `(τ, r + 1)` (no interval);
* bad at the finest level: record `[τ, τ + B r)` and continue at its end.

Main results:
* `theWalk_spec`: the records are consecutive from `0` to `T` (`Chain`), each satisfies `RecOK`
  (a covered record carries its certificate `t start lvl = some stop`, a finest bad record has
  `t start lvl = none`), their lengths sum to `T`, and for every level `j`, the records shorter than
  `B j` have total length at most `B j · nBad T B t j` (PR23 Lemma 4.18): a short record lies inside
  a bad level-`j` epoch (`RecOK.short`).
* `sum_sqrt_le`: `Σ √|I| ≤ T/√(B 0) + Σ_{1 ≤ j < R} B (j-1)·nBad(j-1)/√(B j)`, the assembly used with
  Cauchy–Schwarz-type interval costs.
-/

namespace Pool.P0057

structure Rec where
  start : ℕ
  stop : ℕ
  lvl : ℕ
  cov : Bool

variable (R T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Option ℕ)

/-- Coarsest level whose grid contains `x` (or `R - 1`). -/
noncomputable def canon (x : ℕ) : ℕ :=
  Nat.find (⟨R - 1, Or.inr le_rfl⟩ : ∃ r, B r ∣ x ∨ R - 1 ≤ r)

/-- Start of the level-`j` epoch containing `x`. -/
def est (j x : ℕ) : ℕ := x / B j * B j

/-- The walk with fuel `f` from the point `(τ, r)`. -/
noncomputable def walk : ℕ → ℕ → ℕ → List Rec
  | 0, _, _ => []
  | f + 1, τ, r =>
    if T ≤ τ then [] else
    match t τ r with
    | some e => ⟨τ, e, r, true⟩ :: walk f e (canon R B e)
    | none =>
      if r + 1 < R then walk f τ (r + 1)
      else ⟨τ, τ + B r, r, false⟩ :: walk f (τ + B r) (canon R B (τ + B r))

/-- Records are consecutive from `τ` to `T`. -/
def Chain : ℕ → List Rec → Prop
  | τ, [] => τ = T
  | τ, x :: l => x.start = τ ∧ τ < x.stop ∧ Chain x.stop l

/-- Hypotheses on the eviction function. -/
structure Hyp : Prop where
  pos : ∀ r, 0 < B r
  dvd : ∀ r, r + 1 < R → B (r + 1) ∣ B r
  hR : 0 < R
  hT : B 0 ∣ T
  lb : ∀ τ r e, B r ∣ τ → τ < T → r < R → t τ r = some e → τ + B r ≤ e
  ub : ∀ τ r e, B r ∣ τ → τ < T → r < R → t τ r = some e → e ≤ T
  edvd : ∀ τ r e, B r ∣ τ → τ < T → r < R → t τ r = some e → B r ∣ e
  align : ∀ τ r e, B r ∣ τ → τ < T → r < R → t τ r = some e →
    ∀ j m, j < r → B j ∣ m → τ < m → m < e → B j ∣ e

variable {R T B t}

section
variable (h : Hyp R T B t)
include h

lemma dvd_of_le {i j : ℕ} (hij : i ≤ j) (hj : j < R) : B j ∣ B i := by
  induction j, hij using Nat.le_induction with
  | base => exact dvd_rfl
  | succ k hik ih => exact (h.dvd k hj).trans (ih (by omega))

lemma B_le_of_le {i j : ℕ} (hij : i ≤ j) (hj : j < R) : B j ≤ B i :=
  Nat.le_of_dvd (h.pos i) (dvd_of_le h hij hj)

lemma last_dvd_T : B (R - 1) ∣ T := (dvd_of_le h (Nat.zero_le _) (by have := h.hR; omega)).trans h.hT

lemma canon_spec {x : ℕ} (hx : B (R - 1) ∣ x) : canon R B x < R ∧ B (canon R B x) ∣ x := by
  have hR := h.hR
  have hs := Nat.find_spec (⟨R - 1, Or.inr le_rfl⟩ : ∃ r, B r ∣ x ∨ R - 1 ≤ r)
  have hm := Nat.find_min' (⟨R - 1, Or.inr le_rfl⟩ : ∃ r, B r ∣ x ∨ R - 1 ≤ r) (Or.inl hx)
  refine ⟨by unfold canon; omega, ?_⟩
  rcases hs with hs | hs
  · exact hs
  · have : canon R B x = R - 1 := by unfold canon; omega
    rw [this]; exact hx

lemma canon_min {x j : ℕ} (hj : j < canon R B x) : ¬ B j ∣ x := by
  intro hd
  have := Nat.find_min (⟨R - 1, Or.inr le_rfl⟩ : ∃ r, B r ∣ x ∨ R - 1 ≤ r) hj
  exact this (Or.inl hd)

end

/-- Invariant of walk points: on the grid of their level, and every coarser epoch containing the
point has a bad start. -/
structure Inv (R T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Option ℕ) (τ r : ℕ) : Prop where
  lt : r < R
  dvd : B r ∣ τ
  le : τ ≤ T
  bad : ∀ j < r, t (est B j τ) j = none

lemma est_le (j x : ℕ) : est B j x ≤ x := Nat.div_mul_le_self x (B j)

lemma lt_est_add {j : ℕ} (hB : 0 < B j) (x : ℕ) : x < est B j x + B j := by
  unfold est
  have := Nat.lt_div_mul_add (a := x) hB
  linarith

lemma est_dvd (j x : ℕ) : B j ∣ est B j x := Dvd.intro_left _ rfl

lemma est_eq_self {j x : ℕ} (hx : B j ∣ x) : est B j x = x := Nat.div_mul_cancel hx

/-- If `s ≤ x < s + B j` and `B j ∣ s` then `s` is the epoch start of `x`. -/
lemma est_eq_of {j s x : ℕ} (hB : 0 < B j) (hs : B j ∣ s) (h1 : s ≤ x) (h2 : x < s + B j) :
    est B j x = s := by
  obtain ⟨k, rfl⟩ := hs
  unfold est
  have : x / B j = k := Nat.div_eq_of_lt_le (by nlinarith) (by nlinarith)
  rw [this]; ring

end Pool.P0057

namespace Pool.P0057

variable {R T : ℕ} {B : ℕ → ℕ} {t : ℕ → ℕ → Option ℕ}

/-- Potential that bounds the number of walk steps. -/
def pot (R T τ r : ℕ) : ℕ := (T - τ) * (R + 1) + (R - r)

section
variable (h : Hyp R T B t)
include h

lemma inv_descend {τ r : ℕ} (hI : Inv R T B t τ r) (hn : t τ r = none) (hr : r + 1 < R) :
    Inv R T B t τ (r + 1) where
  lt := hr
  dvd := (h.dvd r hr).trans hI.dvd
  le := hI.le
  bad := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact hI.bad j hj
    · rw [est_eq_self hI.dvd]; exact hn

lemma inv_cover {τ r e : ℕ} (hI : Inv R T B t τ r) (hτ : τ < T) (he : t τ r = some e) :
    Inv R T B t e (canon R B e) := by
  have hBe : B r ∣ e := h.edvd τ r e hI.dvd hτ hI.lt he
  have hlast : B (R - 1) ∣ e := (dvd_of_le h (by have := hI.lt; omega) (by have := h.hR; omega)).trans hBe
  obtain ⟨hcl, hcd⟩ := canon_spec h hlast
  refine ⟨hcl, hcd, h.ub τ r e hI.dvd hτ hI.lt he, ?_⟩
  intro j hj
  have hnd := canon_min h hj
  have hjr : j < r := by
    by_contra hc
    exact hnd ((dvd_of_le h (by omega) (by omega)).trans hBe)
  have hpos := h.pos j
  set s := est B j τ with hs
  have h1 : s ≤ τ := est_le j τ
  have h2 : τ < s + B j := lt_est_add hpos τ
  have hlt : e < s + B j := by
    by_contra hc
    push_neg at hc
    rcases hc.lt_or_eq with hc | hc
    · exact hnd (h.align τ r e hI.dvd hτ hI.lt he j (s + B j) hjr
        (dvd_add (est_dvd j τ) dvd_rfl) h2 hc)
    · exact hnd (hc ▸ dvd_add (est_dvd j τ) dvd_rfl)
  have hτe : τ < e := lt_of_lt_of_le (Nat.lt_add_of_pos_right (h.pos r))
    (h.lb τ r e hI.dvd hτ hI.lt he)
  rw [est_eq_of hpos (est_dvd j τ) (by omega) hlt]
  exact hI.bad j hjr

lemma inv_finest {τ r : ℕ} (hI : Inv R T B t τ r) (hτ : τ < T) (hr : ¬ r + 1 < R) :
    Inv R T B t (τ + B r) (canon R B (τ + B r)) := by
  have hrR : r = R - 1 := by have := hI.lt; omega
  have hBe : B r ∣ τ + B r := dvd_add hI.dvd dvd_rfl
  have hBe' : B (R - 1) ∣ τ + B r := by rw [← hrR]; exact hBe
  obtain ⟨hcl, hcd⟩ := canon_spec h hBe'
  have hle : τ + B r ≤ T := by
    obtain ⟨k, hk⟩ := hI.dvd
    obtain ⟨m, hm⟩ := (hrR ▸ last_dvd_T h : B r ∣ T)
    have hp := h.pos r
    have : k < m := by
      by_contra hc; push_neg at hc
      have : B r * m ≤ B r * k := Nat.mul_le_mul_left _ hc
      omega
    calc τ + B r = B r * (k + 1) := by rw [hk]; ring
      _ ≤ B r * m := Nat.mul_le_mul_left _ this
      _ = T := hm.symm
  refine ⟨hcl, hcd, hle, ?_⟩
  intro j hj
  have hnd := canon_min h hj
  have hjr : j < r := by
    by_contra hc
    exact hnd ((dvd_of_le h (by omega) (by omega)).trans hBe)
  have hpos := h.pos j
  set s := est B j τ with hs
  have h1 : s ≤ τ := est_le j τ
  have h2 : τ < s + B j := lt_est_add hpos τ
  have hlt : τ + B r < s + B j := by
    by_contra hc
    push_neg at hc
    -- s + B j is a multiple of B r in (τ, τ + B r]
    have hm : B r ∣ s + B j :=
      (dvd_of_le h hjr.le hI.lt).trans (dvd_add (est_dvd j τ) dvd_rfl)
    obtain ⟨k, hk⟩ := hI.dvd
    obtain ⟨m, hm'⟩ := hm
    have hp := h.pos r
    have hkm : k < m := by
      by_contra hc'; push_neg at hc'
      have : B r * m ≤ B r * k := Nat.mul_le_mul_left _ hc'
      omega
    have hmk : m ≤ k + 1 := by
      by_contra hc'; push_neg at hc'
      have : B r * (k + 2) ≤ B r * m := Nat.mul_le_mul_left _ hc'
      nlinarith
    have : m = k + 1 := by omega
    subst this
    exact hnd (by rw [hk, show B r * k + B r = B r * (k + 1) by ring, ← hm']; exact dvd_add (est_dvd j τ) dvd_rfl)
  rw [est_eq_of hpos (est_dvd j τ) (by omega) hlt]
  exact hI.bad j hjr

end


/-- Properties of an emitted record. -/
structure RecOK (R T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Option ℕ) (x : Rec) : Prop where
  inv : Inv R T B t x.start x.lvl
  lt : x.start < x.stop
  le : x.stop ≤ T
  cov : x.cov = true → t x.start x.lvl = some x.stop
  fin : x.cov = false → x.lvl + 1 = R ∧ t x.start x.lvl = none ∧ x.stop = x.start + B x.lvl
  short : ∀ j < R, x.stop - x.start < B j →
    t (est B j x.start) j = none ∧ x.stop ≤ est B j x.start + B j

section
variable (h : Hyp R T B t)
include h

lemma short_cover {τ r e j : ℕ} (hI : Inv R T B t τ r) (hτ : τ < T) (he : t τ r = some e)
    (hj : j < R) (hs : e - τ < B j) :
    t (est B j τ) j = none ∧ e ≤ est B j τ + B j := by
  have hlb := h.lb τ r e hI.dvd hτ hI.lt he
  have hjr : j < r := by
    by_contra hc; push_neg at hc
    have := B_le_of_le h hc hj
    omega
  refine ⟨hI.bad j hjr, ?_⟩
  have hpos := h.pos j
  have h1 : est B j τ ≤ τ := est_le j τ
  have h2 : τ < est B j τ + B j := lt_est_add hpos τ
  by_contra hc; push_neg at hc
  have hd := h.align τ r e hI.dvd hτ hI.lt he j (est B j τ + B j) hjr
    (dvd_add (est_dvd j τ) dvd_rfl) h2 hc
  obtain ⟨k, hk⟩ := est_dvd (B := B) j τ
  obtain ⟨m, hm⟩ := hd
  have : k + 1 < m := by
    by_contra hc'; push_neg at hc'
    have : B j * m ≤ B j * (k + 1) := Nat.mul_le_mul_left _ hc'
    have : est B j τ + B j = B j * (k + 1) := by rw [hk]; ring
    omega
  have h3 : B j * (k + 2) ≤ B j * m := Nat.mul_le_mul_left _ this
  have h4 : B j * (k + 2) = est B j τ + 2 * B j := by rw [hk]; ring
  omega

lemma short_finest {τ r j : ℕ} (hI : Inv R T B t τ r) (hr : ¬ r + 1 < R)
    (hj : j < R) (hs : B r < B j) :
    t (est B j τ) j = none ∧ τ + B r ≤ est B j τ + B j := by
  have hjr : j < r := by
    by_contra hc; push_neg at hc
    have := B_le_of_le h hc hj
    omega
  refine ⟨hI.bad j hjr, ?_⟩
  have hpos := h.pos j
  have h2 : τ < est B j τ + B j := lt_est_add hpos τ
  have hm : B r ∣ est B j τ + B j :=
    (dvd_of_le h hjr.le hI.lt).trans (dvd_add (est_dvd j τ) dvd_rfl)
  obtain ⟨k, hk⟩ := hI.dvd
  obtain ⟨m, hm'⟩ := hm
  have hp := h.pos r
  have hkm : k < m := by
    by_contra hc'; push_neg at hc'
    have : B r * m ≤ B r * k := Nat.mul_le_mul_left _ hc'
    omega
  have : B r * (k + 1) ≤ B r * m := Nat.mul_le_mul_left _ hkm
  nlinarith

theorem walk_spec : ∀ (f τ r : ℕ), Inv R T B t τ r → pot R T τ r < f →
    Chain T τ (walk R T B t f τ r) ∧ ∀ x ∈ walk R T B t f τ r, RecOK R T B t x
  | 0, τ, r, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, τ, r, hI, hf => by
    unfold walk
    by_cases hT : T ≤ τ
    · rw [if_pos hT]
      exact ⟨le_antisymm hI.le hT, by simp⟩
    rw [if_neg hT]
    push_neg at hT
    cases he : t τ r with
    | some e =>
      have hlb := h.lb τ r e hI.dvd hT hI.lt he
      have hub := h.ub τ r e hI.dvd hT hI.lt he
      have hpos := h.pos r
      have hI' := inv_cover h hI hT he
      have hpot : pot R T e (canon R B e) < f := by
        unfold pot at hf ⊢
        have : (T - e) * (R + 1) + (R + 1) ≤ (T - τ) * (R + 1) := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
        have := hI.lt
        omega
      obtain ⟨hc, hr⟩ := walk_spec f e (canon R B e) hI' hpot
      refine ⟨⟨rfl, show τ < e by omega, hc⟩, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hI, show τ < e by omega, hub, fun _ => he, fun h' => by simp at h',
          fun j hj hs => short_cover h hI hT he hj hs⟩
      · exact hr x hx
    | none =>
      by_cases hr : r + 1 < R
      · rw [if_pos hr]
        have hI' := inv_descend h hI he hr
        have hpot : pot R T τ (r + 1) < f := by unfold pot at hf ⊢; omega
        exact walk_spec f τ (r + 1) hI' hpot
      · rw [if_neg hr]
        have hpos := h.pos r
        have hI' := inv_finest h hI hT hr
        have hpot : pot R T (τ + B r) (canon R B (τ + B r)) < f := by
          unfold pot at hf ⊢
          have : (T - (τ + B r)) * (R + 1) + (R + 1) ≤ (T - τ) * (R + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by have := hI'.le; omega)
          have := hI.lt
          omega
        obtain ⟨hc, hrs⟩ := walk_spec f (τ + B r) (canon R B (τ + B r)) hI' hpot
        refine ⟨⟨rfl, show τ < τ + B r by omega, hc⟩, ?_⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · refine ⟨hI, show τ < τ + B r by omega, hI'.le, fun h' => by simp at h',
            fun _ => ⟨show r + 1 = R by have := hI.lt; omega, he, rfl⟩, ?_⟩
          intro j hj hs
          simp only [Nat.add_sub_cancel_left] at hs
          exact short_finest h hI hr hj hs
        · exact hrs x hx

end


/-- Length of a record. -/
def len (x : Rec) : ℕ := x.stop - x.start

lemma chain_sum_le : ∀ (L : List Rec) (τ : ℕ), Chain T τ L → ∀ a b : ℕ,
    ((L.filter fun x => decide (a ≤ x.start ∧ x.stop ≤ b)).map len).sum ≤ b - max a τ
  | [], _, _, a, b => by simp
  | x :: L, τ, ⟨hs, hlt, hc⟩, a, b => by
    have ih := chain_sum_le L x.stop hc a b
    by_cases hp : a ≤ x.start ∧ x.stop ≤ b
    · rw [List.filter_cons_of_pos (by simpa using hp), List.map_cons, List.sum_cons]
      have hl : len x = x.stop - x.start := rfl
      have : max a x.stop = x.stop := max_eq_right (by omega)
      rw [this] at ih
      have : max a τ = τ := max_eq_right (by omega)
      rw [this]
      omega
    · rw [List.filter_cons_of_neg (by simpa using hp)]
      refine ih.trans ?_
      have : max a τ ≤ max a x.stop := max_le_max le_rfl (by omega)
      omega

lemma sum_filter_mono {α : Type} (L : List α) (g : α → ℕ) (p q : α → Bool)
    (h : ∀ x ∈ L, p x = true → q x = true) :
    ((L.filter p).map g).sum ≤ ((L.filter q).map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have ih := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hp : p x = true
    · have hq := h x List.mem_cons_self hp
      simp [List.filter_cons, hp, hq, ih]
    · by_cases hq : q x = true
      · simp only [List.filter_cons, hp, hq]; simp; omega
      · simp only [List.filter_cons, hp, hq]; simpa using ih

lemma sum_fiber {α : Type} (L : List α) (g : α → ℕ) (p : α → Bool) (key : α → ℕ) (S : Finset ℕ)
    (hS : ∀ x ∈ L, p x = true → key x ∈ S) :
    ((L.filter p).map g).sum = ∑ s ∈ S, ((L.filter fun x => p x && decide (key x = s)).map g).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have ih := ih (fun y hy => hS y (List.mem_cons_of_mem _ hy))
    by_cases hp : p x = true
    · have hk := hS x (List.mem_cons_self) hp
      simp only [List.filter_cons, hp, if_true, List.map_cons, List.sum_cons, Bool.true_and]
      rw [ih]
      have : ∀ s ∈ S, ((if decide (key x = s) = true then x :: L.filter (fun x => p x && decide (key x = s))
          else L.filter (fun x => p x && decide (key x = s))).map g).sum =
          (if key x = s then g x else 0) + ((L.filter fun x => p x && decide (key x = s)).map g).sum := by
        intro s _
        by_cases h : key x = s <;> simp [h]
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq S (key x) (fun _ => g x)]
      simp [hk]
    · simp only [List.filter_cons, hp, if_false, Bool.false_and]
      simpa using ih

section
variable (h : Hyp R T B t)
include h

/-- Intervals shorter than a level-`j` epoch lie in bad level-`j` epochs: their total length is at
most `B j` times the number of bad level-`j` epochs. -/
theorem sum_short_le {L : List Rec} {τ0 : ℕ} (hc : Chain T τ0 L) (hok : ∀ x ∈ L, RecOK R T B t x)
    {j : ℕ} (hj : j < R) :
    ((L.filter fun x => decide (len x < B j)).map len).sum ≤
      B j * ((Finset.range T).filter fun s => B j ∣ s ∧ t s j = none).card := by
  set S := (Finset.range T).filter fun s => B j ∣ s ∧ t s j = none
  have hS : ∀ x ∈ L, decide (len x < B j) = true → est B j x.start ∈ S := by
    intro x hx hp
    simp only [decide_eq_true_eq] at hp
    obtain ⟨hbad, -⟩ := (hok x hx).short j hj hp
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨lt_of_le_of_lt (est_le j x.start) (lt_of_lt_of_le (hok x hx).lt (hok x hx).le),
      est_dvd j x.start, hbad⟩
  rw [sum_fiber L len _ (fun x => est B j x.start) S hS, mul_comm, ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_le_sum fun s _ => ?_
  calc ((L.filter fun x => decide (len x < B j) && decide (est B j x.start = s)).map len).sum
      ≤ ((L.filter fun x => decide (s ≤ x.start ∧ x.stop ≤ s + B j)).map len).sum := by
        apply sum_filter_mono
        intro x hx hp
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
        obtain ⟨hl, he⟩ := hp
        obtain ⟨-, hst⟩ := (hok x hx).short j hj hl
        rw [he] at hst
        exact ⟨he ▸ est_le j x.start, hst⟩
    _ ≤ s + B j - max s τ0 := chain_sum_le L τ0 hc s (s + B j)
    _ ≤ B j := by omega

end


lemma chain_sum_len : ∀ (L : List Rec) (τ : ℕ), Chain T τ L → (L.map len).sum = T - τ
  | [], τ, hc => by simp [Chain] at hc; simp [hc]
  | x :: L, τ, ⟨hs, hlt, hc⟩ => by
    have ih := chain_sum_len L x.stop hc
    have hle : x.stop ≤ T := by
      clear ih hs hlt
      induction L generalizing x with
      | nil => exact le_of_eq hc
      | cons y L' ihL => exact (le_of_lt hc.2.1).trans (ihL y hc.2.2)
    simp only [List.map_cons, List.sum_cons, ih, len]
    omega

/-- The walk from the origin with enough fuel. -/
noncomputable def theWalk (R T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Option ℕ) : List Rec :=
  walk R T B t (pot R T 0 0 + 1) 0 0

/-- Number of bad level-`j` epochs. -/
noncomputable def nBad (T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Option ℕ) (j : ℕ) : ℕ :=
  ((Finset.range T).filter fun s => B j ∣ s ∧ t s j = none).card

section
variable (h : Hyp R T B t)
include h

theorem theWalk_spec :
    Chain T 0 (theWalk R T B t) ∧ (∀ x ∈ theWalk R T B t, RecOK R T B t x) ∧
      ((theWalk R T B t).map len).sum = T ∧
      ∀ j < R, (((theWalk R T B t).filter fun x => decide (len x < B j)).map len).sum ≤
        B j * nBad T B t j := by
  have hI : Inv R T B t 0 0 := ⟨h.hR, dvd_zero _, Nat.zero_le _, fun j hj => absurd hj (by omega)⟩
  obtain ⟨hc, hok⟩ := walk_spec h _ 0 0 hI (Nat.lt_succ_self _)
  refine ⟨hc, hok, by rw [theWalk, chain_sum_len _ 0 hc]; simp, fun j hj => ?_⟩
  exact sum_short_le h hc hok hj

/-- Cost assembly: `Σ √|I| ≤ T/√(B 0) + Σ_{1 ≤ j < R} B (j-1) · H_{j-1} / √(B j)`. -/
theorem sum_sqrt_le :
    ((theWalk R T B t).map fun x => Real.sqrt (len x)).sum ≤
      T / Real.sqrt (B 0) +
        ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * nBad T B t (j - 1) / Real.sqrt (B j) := by
  obtain ⟨-, hok, hsum, hshort⟩ := theWalk_spec h
  set L := theWalk R T B t
  have hR := h.hR
  have hpt : ∀ x ∈ L, Real.sqrt (len x) ≤ (len x : ℝ) / Real.sqrt (B 0) +
      ∑ j ∈ Finset.Ico 1 R, (if len x < B (j - 1) then (len x : ℝ) else 0) / Real.sqrt (B j) := by
    intro x hx
    have hge : B (R - 1) ≤ len x := by
      have hok := hok x hx
      cases hcv : x.cov
      · obtain ⟨h1, -, h3⟩ := hok.fin hcv
        unfold len; rw [h3]; have : x.lvl = R - 1 := by omega
        rw [this]; omega
      · have := h.lb x.start x.lvl x.stop hok.inv.dvd (lt_of_lt_of_le hok.lt hok.le) hok.inv.lt
          (hok.cov hcv)
        have := B_le_of_le h (show x.lvl ≤ R - 1 by have := hok.inv.lt; omega) (by omega)
        unfold len; omega
    have hnn : ∀ j ∈ Finset.Ico 1 R,
        0 ≤ (if len x < B (j - 1) then (len x : ℝ) else 0) / Real.sqrt (B j) := by
      intro j _; positivity
    have key : ∀ j, (0 : ℝ) < B j → B j ≤ len x →
        Real.sqrt (len x) ≤ (len x : ℝ) / Real.sqrt (B j) := by
      intro j hb hj
      rw [le_div_iff₀ (Real.sqrt_pos.2 hb)]
      calc Real.sqrt (len x) * Real.sqrt (B j) ≤ Real.sqrt (len x) * Real.sqrt (len x) := by
            gcongr
        _ = len x := Real.mul_self_sqrt (by positivity)
    by_cases h0 : B 0 ≤ len x
    · have := key 0 (by exact_mod_cast h.pos 0) h0
      linarith [Finset.sum_nonneg hnn]
    · have hex : ∃ j, B j ≤ len x := ⟨R - 1, hge⟩
      set j0 := Nat.find hex with hj0
      have hj0s : B j0 ≤ len x := Nat.find_spec hex
      have hj0R : j0 ≤ R - 1 := Nat.find_min' hex hge
      have hj01 : 1 ≤ j0 := by
        by_contra hc
        have : j0 = 0 := by omega
        rw [this] at hj0s; exact h0 hj0s
      have hmin : len x < B (j0 - 1) := by
        have := Nat.find_min hex (show j0 - 1 < j0 by omega)
        push_neg at this; exact this
      have hmem : j0 ∈ Finset.Ico 1 R := Finset.mem_Ico.2 ⟨hj01, by omega⟩
      have hterm := Finset.single_le_sum hnn hmem
      rw [if_pos hmin] at hterm
      have := key j0 (by exact_mod_cast h.pos j0) hj0s
      have h0' : (0 : ℝ) ≤ (len x : ℝ) / Real.sqrt (B 0) := by positivity
      linarith
  refine (List.sum_le_sum hpt).trans ?_
  -- split the sum
  have hsplit : ∀ (M : List Rec), (M.map fun x => (len x : ℝ) / Real.sqrt (B 0) +
      ∑ j ∈ Finset.Ico 1 R, (if len x < B (j - 1) then (len x : ℝ) else 0) / Real.sqrt (B j)).sum =
      ((M.map len).sum : ℝ) / Real.sqrt (B 0) + ∑ j ∈ Finset.Ico 1 R,
        ((((M.filter fun x => decide (len x < B (j - 1))).map len).sum : ℕ) : ℝ) / Real.sqrt (B j) := by
    intro M
    induction M with
    | nil => simp
    | cons y M ih =>
      rw [List.map_cons, List.sum_cons, ih]
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_div]
      have : ∀ j ∈ Finset.Ico 1 R, (((((y :: M).filter fun x => decide (len x < B (j - 1))).map len).sum
          : ℕ) : ℝ) / Real.sqrt (B j) = (if len y < B (j - 1) then (len y : ℝ) else 0) / Real.sqrt (B j)
          + ((((M.filter fun x => decide (len x < B (j - 1))).map len).sum : ℕ) : ℝ) / Real.sqrt (B j) := by
        intro j _
        by_cases hy : len y < B (j - 1)
        · simp [List.filter_cons, hy, add_div]
        · simp [List.filter_cons, hy]
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
      ring
  rw [hsplit, hsum]
  gcongr with j hj
  rw [← Nat.cast_mul]
  exact_mod_cast hshort (j - 1) (by have := Finset.mem_Ico.1 hj; omega)

end

end Pool.P0057
