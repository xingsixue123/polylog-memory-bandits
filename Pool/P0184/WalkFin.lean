import Pool.P0153.CountB

/-!
# Self-financing (b″)-records: the whole-walk sum of P0135's walk

P0153 bounds the costs of the *counted* records (covered and finest-bad) of `Pool.P0135.theWalkB` by
`T·a 0 + Σ_{1≤j<R} B(j-1)·K_{j-1}·a j + K_{R-1}·c` with `K_j = nBadB j + #((b″)-records of thread ≤ j)`.
If every (b″)-record of thread `i` has cost `≤ -w i` with `w i` at least the weight that the count gives it,
the (b″)-records pay for themselves and the whole walk costs
`≤ T·a 0 + Σ_{1≤j<R} B(j-1)·nBadB(j-1)·a j + nBadB(R-1)·c` (+ the free bad records).
-/

namespace Pool.P0184

open Pool.P0135 Pool.P0137 Pool.P0153

variable {R T : ℕ} {B : ℕ → ℕ} {t : ℕ → ℕ → Out} {g : ℕ → Out}

/-- The thread weight of a record: `w i` for a (b″)-record of thread `i`, else `0`. -/
def bw (w : ℕ → ℝ) (x : RecB) : ℝ :=
  match x.out with
  | .bev _ i => w i
  | _ => 0

/-- Free bad records. -/
def freeBad (x : RecB) : Bool :=
  match x.out with
  | .bad => x.free
  | _ => false

/-- The weight that P0153's count gives a record. -/
noncomputable def cw (R : ℕ) (B : ℕ → ℕ) (a : ℕ → ℝ) (c : ℝ) (x : RecB) : ℝ :=
  ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * (if bevLe (j - 1) x then 1 else 0) * a j +
    (if bevLe (R - 1) x then 1 else 0) * c

lemma sum_map_add (L : List RecB) (f1 f2 : RecB → ℝ) :
    (L.map fun x => f1 x + f2 x).sum = (L.map f1).sum + (L.map f2).sum := by
  induction L with
  | nil => simp
  | cons y L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma sum_map_le (L : List RecB) (f1 f2 : RecB → ℝ) (h : ∀ x ∈ L, f1 x ≤ f2 x) :
    (L.map f1).sum ≤ (L.map f2).sum := by
  induction L with
  | nil => simp
  | cons y L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h y (by simp)) (ih fun x hx => h x (by simp [hx]))

lemma sum_map_filter (L : List RecB) (p : RecB → Bool) (f : RecB → ℝ) :
    ((L.filter p).map f).sum = (L.map fun x => if p x then f x else 0).sum := by
  induction L with
  | nil => simp
  | cons y L ih => by_cases hy : p y <;> simp [List.filter_cons, hy, ih]

lemma countP_eq_sum (L : List RecB) (p : RecB → Bool) :
    (L.countP p : ℝ) = (L.map fun x => if p x then (1 : ℝ) else 0).sum := by
  induction L with
  | nil => simp
  | cons y L ih => by_cases hy : p y <;> simp [List.countP_cons, hy, ih] <;> ring

lemma sum_map_finset (L : List RecB) (s : Finset ℕ) (F : ℕ → RecB → ℝ) :
    (L.map fun x => ∑ j ∈ s, F j x).sum = ∑ j ∈ s, (L.map (F j)).sum := by
  induction L with
  | nil => simp
  | cons y L ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

lemma sum_map_mul (L : List RecB) (f : RecB → ℝ) (k : ℝ) :
    (L.map fun x => k * f x).sum = k * (L.map f).sum := by
  induction L with
  | nil => simp
  | cons y L ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- The count terms of P0153 coming from (b″)-records are `Σ_x cw x`. -/
lemma bev_terms_eq (L : List RecB) (a : ℕ → ℝ) (c : ℝ) :
    ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * (L.countP (bevLe (j - 1)) : ℝ) * a j +
      (L.countP (bevLe (R - 1)) : ℝ) * c = (L.map (cw R B a c)).sum := by
  unfold cw
  rw [sum_map_add, sum_map_finset]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [countP_eq_sum]
    have : (L.map fun x => (B (j - 1) : ℝ) * (if bevLe (j - 1) x then 1 else 0) * a j) =
        L.map fun x => ((B (j - 1) : ℝ) * a j) * (if bevLe (j - 1) x then 1 else 0) := by
      congr 1; funext x; ring
    rw [this, sum_map_mul]; ring
  · rw [countP_eq_sum]
    have : (L.map fun x => (if bevLe (R - 1) x then (1 : ℝ) else 0) * c) =
        L.map fun x => c * (if bevLe (R - 1) x then 1 else 0) := by
      congr 1; funext x; ring
    rw [this, sum_map_mul]; ring

lemma chainB_le : ∀ (L : List RecB) (τ : ℕ), ChainB T τ L → τ ≤ T
  | [], τ, hc => le_of_eq hc
  | x :: L, τ, hc => hc.2.1.le.trans (chainB_le L x.stop hc.2.2)

/-- Sum over a chain of records = sum over `[τ, T)`. -/
lemma chainB_sum (hfun : ℕ → ℝ) : ∀ (L : List RecB) (τ : ℕ), ChainB T τ L →
    ∑ u ∈ Finset.Ico τ T, hfun u = (L.map fun x => ∑ u ∈ Finset.Ico x.start x.stop, hfun u).sum
  | [], τ, hc => by
    simp only [ChainB] at hc
    subst hc; simp
  | x :: L, τ, hc => by
    obtain ⟨h1, h2, h3⟩ := hc
    have ih := chainB_sum hfun L x.stop h3
    have hle : x.stop ≤ T := chainB_le L x.stop h3
    simp only [List.map_cons, List.sum_cons, ← ih, h1]
    rw [Finset.sum_Ico_consecutive _ h2.le hle]

section
variable (h : HypB R T B t g)
include h

/-- A (b″)-record of a walk satisfying `RecOKB` has its thread `< R` (`HypB.blt`, `HypB.fblt`). -/
lemma bev_thread_lt {W : ℕ → ℕ → Prop} {x : RecB} (hx : RecOKB R T B t g W x) {e i : ℕ}
    (hout : x.out = .bev e i) : i < R := by
  have hsT : x.start < T := lt_of_lt_of_le hx.lt hx.le
  cases hfr : x.free
  · obtain ⟨hl, hd, ht⟩ := hx.grid hfr
    rw [hout] at ht
    have := (h.blt x.start x.lvl e i hd hsT hl ht).2.2
    omega
  · have hg := hx.free hfr
    rw [hout] at hg
    exact (h.fblt x.start e i hsT hg).2.2

/-- **The whole walk with self-financing (b″)-records.** Per-round costs `hc u`; counted records (covered, finest
bad) cost `≤ f(len)` (P0153's shape), a (b″)-record of thread `i` costs `≤ -w i`, a free bad record `≤ cf`. If `w`
dominates the count weight `cw` (a (b″)-record of thread `i` is charged `B(j-1)·a j` at every `j - 1 ≥ i` and `c` if
`i ≤ R - 1`), then `Σ_{u<T} hc u ≤ T·a 0 + Σ_{1≤j<R} B(j-1)·nBadB(j-1)·a j + nBadB(R-1)·c + cf·#(free bad)`. -/
theorem walk_sum_fin (hc : ℕ → ℝ) (f : ℕ → ℝ) (a : ℕ → ℝ) (c cf : ℝ) (w : ℕ → ℝ)
    (ha : ∀ j < R, 0 ≤ a j) (hc0 : 0 ≤ c)
    (hbig : ∀ j < R, ∀ ℓ : ℕ, B j ≤ ℓ → f ℓ ≤ ℓ * a j)
    (hsmall : ∀ ℓ : ℕ, ℓ < B (R - 1) → f ℓ ≤ c)
    (hcnt : ∀ x ∈ theWalkB R T B t g, counted x = true →
      ∑ u ∈ Finset.Ico x.start x.stop, hc u ≤ f (len x))
    (hbev : ∀ x ∈ theWalkB R T B t g, ∀ e i, x.out = .bev e i →
      ∑ u ∈ Finset.Ico x.start x.stop, hc u ≤ -w i)
    (hfree : ∀ x ∈ theWalkB R T B t g, freeBad x = true →
      ∑ u ∈ Finset.Ico x.start x.stop, hc u ≤ cf)
    (hw : ∀ i < R, ∑ j ∈ Finset.Ico 1 R, (if i ≤ j - 1 then (B (j - 1) : ℝ) * a j else 0) +
      (if i ≤ R - 1 then c else 0) ≤ w i) :
    ∑ u ∈ Finset.range T, hc u ≤
      T * a 0 + ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * (nBadB T B t (j - 1) : ℝ) * a j +
        (nBadB T B t (R - 1) : ℝ) * c +
        cf * ((theWalkB R T B t g).countP freeBad : ℝ) := by
  obtain ⟨hch, hok, -, -⟩ := theWalkB_spec h
  set L := theWalkB R T B t g with hL
  rw [Finset.range_eq_Ico, chainB_sum hc L 0 hch]
  -- pointwise split
  have hpt : ∀ x ∈ L, ∑ u ∈ Finset.Ico x.start x.stop, hc u ≤
      (if counted x then f (len x) else 0) - bw w x + (if freeBad x then cf else 0) := by
    intro x hx
    rcases hout : x.out with e | ⟨e, i⟩ | _
    · have hct : counted x = true := by simp [counted, hout]
      have := hcnt x hx hct
      simp [hct, bw, hout, freeBad, this]
    · have hct : counted x = false := by simp [counted, hout]
      have := hbev x hx e i hout
      simp [hct, bw, hout, freeBad]; linarith
    · cases hfr : x.free
      · have hct : counted x = true := by simp [counted, hout, hfr]
        have := hcnt x hx hct
        simp [hct, bw, hout, freeBad, hfr, this]
      · have hct : counted x = false := by simp [counted, hout, hfr]
        have hfb : freeBad x = true := by simp [freeBad, hout, hfr]
        have := hfree x hx hfb
        simp [hct, bw, hout, hfb, this]
  have hsum := sum_map_le L _ _ hpt
  rw [show (L.map fun x => (if counted x then f (len x) else 0) - bw w x + (if freeBad x then cf else 0)) =
      L.map (fun x => (if counted x then f (len x) else 0) + ((fun x => -bw w x) x + (if freeBad x then cf else 0)))
      by congr 1; funext x; ring] at hsum
  rw [sum_map_add, sum_map_add, ← sum_map_filter] at hsum
  -- P0153 on the counted records
  have hP := sum_costB_le h f a c ha hc0 hbig hsmall
  unfold KB at hP
  push_cast at hP
  simp only [mul_add, add_mul, Finset.sum_add_distrib] at hP
  have hBev := bev_terms_eq (R := R) (B := B) L a c
  -- the (b″) weights dominate
  have hdom : (L.map (cw R B a c)).sum ≤ (L.map (bw w)).sum := by
    refine sum_map_le L _ _ fun x hx => ?_
    unfold cw bw
    rcases hout : x.out with e | ⟨e, i⟩ | _
    · simp [bevLe, hout]
    · have hiR : i < R := bev_thread_lt h (hok x hx) hout
      have := hw i hiR
      simp only [bevLe, hout, decide_eq_true_eq]
      convert this using 2
      · refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs <;> ring
      · split_ifs <;> ring
    · simp [bevLe, hout]
  have hneg : (L.map fun x => -bw w x).sum = -(L.map (bw w)).sum := by
    have := sum_map_mul L (bw w) (-1)
    simp only [neg_one_mul] at this
    rw [this]
  have hfb : (L.map fun x => if freeBad x then cf else 0).sum = cf * (L.countP freeBad : ℝ) := by
    rw [countP_eq_sum, ← sum_map_mul]
    congr 1; refine List.map_congr_left fun x _ => ?_; split_ifs <;> ring
  rw [hneg, hfb] at hsum
  linarith

end

end Pool.P0184
