import Pool.P0135.WalkB

/-!
# Part 2 of P0135's walk with (b′)-ends: the finest short count and the √-cost assembly

* `Pool.P0137.chainB_stop_gt`, `Pool.P0137.chainB_stop_unique`: in a chain, stops strictly increase, so at most one record
  ends at any given round.
* **`Pool.P0137.card_shortB_finest`**: counted records shorter than the finest epoch `B (R-1)` number at most
  `K_{R-1} = nBadB (R-1) + #(b′)-records` (each ends at the end of its own finest epoch, which starts bad or contains a
  (b′)-end).
* **`Pool.P0137.sum_sqrtB_le`**: over the counted records of `theWalkB`,
  `Σ √|I| ≤ T/√(B 0) + Σ_{1 ≤ j < R} B (j-1)·K_{j-1}/√(B j) + K_{R-1}·√(B (R-1))`, with
  `K_j = Pool.P0137.KB … j = nBadB j + #(b′)-records of thread ≤ j` (P0057's `sum_sqrt_le` with the (b′)-ends added).

Not counted here (paid separately, as in P0131): free bad rounds (one round each) and the (b′)-records themselves.
-/

namespace Pool.P0137

open Pool.P0135
open Pool.P0057 (est est_le est_dvd lt_est_add est_eq_of B_le_of_le dvd_of_le sum_fiber sum_filter_mono)

variable {R T : ℕ} {B : ℕ → ℕ} {t : ℕ → ℕ → Out} {g : ℕ → Out}

lemma chainB_stop_gt : ∀ (L : List RecB) (τ : ℕ), ChainB T τ L → ∀ y ∈ L, τ < y.stop
  | [], _, _, y, hy => by simp at hy
  | x :: L, τ, ⟨hs, hlt, hc⟩, y, hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hlt
    · exact lt_trans hlt (chainB_stop_gt L x.stop hc y hy)

lemma chainB_stop_unique : ∀ (L : List RecB) (τ : ℕ), ChainB T τ L → ∀ c : ℕ,
    (L.filter fun x => decide (x.stop = c)).length ≤ 1
  | [], _, _, _ => by simp
  | x :: L, τ, ⟨hs, hlt, hc⟩, c => by
    by_cases hx : x.stop = c
    · rw [List.filter_cons_of_pos (by simpa using hx), List.length_cons]
      have : (L.filter fun y => decide (y.stop = c)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy
        have := chainB_stop_gt L x.stop hc y hy
        simp; omega
      rw [this]; simp
    · rw [List.filter_cons_of_neg (by simpa using hx)]
      exact chainB_stop_unique L x.stop hc c

section
variable (h : HypB R T B t g)
include h

/-- Counted records shorter than the finest epoch are at most `K_{R-1}` in number. -/
theorem card_shortB_finest {L : List RecB} {τ0 : ℕ} (hc : ChainB T τ0 L)
    (hok : ∀ x ∈ L, RecOKB R T B t g (fun p j => IsBevEnd L p j) x) :
    (L.filter fun x => counted x && decide (len x < B (R - 1))).length ≤
      nBadB T B t (R - 1) + L.countP (bevLe (R - 1)) := by
  have hR := h.hR
  set j := R - 1 with hjdef
  have hj : j < R := by omega
  have hpos := h.pos j
  set S1 := (Finset.range T).filter fun s => B j ∣ s ∧ t s j = Out.bad
  set S2 := ((L.filter (bevLe j)).map fun x => est B j x.stop).toFinset
  -- a short counted record ends at the end of its finest epoch
  have hend : ∀ x ∈ L, (counted x && decide (len x < B j)) = true →
      x.stop = est B j x.start + B j ∧ est B j x.start ∈ S1 ∪ S2 := by
    intro x hx hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hw, hst⟩ := (hok x hx).short hp.1 j hj hp.2
    refine ⟨?_, ?_⟩
    · -- the record is free and covered (grid counted records have length ≥ B j)
      have hok' := hok x hx
      cases hfr : x.free
      · obtain ⟨hl, -, hsrc⟩ := hok'.grid hfr
        exfalso
        cases hout : x.out with
        | cov e =>
          rw [hout] at hsrc
          have he := hok'.cov e hout
          have := h.lb x.start x.lvl e (hok'.grid hfr).2.1
            (lt_of_lt_of_le hok'.lt hok'.le) hl hsrc
          have := B_le_of_le h.base (show x.lvl ≤ j by omega) hj
          have := hp.2; unfold len at this; omega
        | bev e j' => simp [counted, hout] at hp
        | bad =>
          obtain ⟨h1, h2⟩ := hok'.bad hout
          rw [hfr] at h1; simp only [Bool.false_eq_true, if_false] at h1
          have hl' := h2 hfr
          have hxl : x.lvl = j := by omega
          have hl := hp.2; unfold len at hl; rw [h1, hxl] at hl; omega
      · cases hout : x.out with
        | cov e =>
          have hsrc := hok'.free hfr
          rw [hout] at hsrc
          have he := hok'.cov e hout
          obtain ⟨-, -, hd⟩ := h.flt x.start e (lt_of_lt_of_le hok'.lt hok'.le) hsrc
          rw [he] at hd
          have hd' : B j ∣ x.stop := hd
          have h1 := est_le (B := B) j x.start
          obtain ⟨k, hk⟩ := est_dvd (B := B) j x.start
          obtain ⟨m, hm⟩ := hd'
          have hlt := hok'.lt
          have : k < m := by
            by_contra hc'; push_neg at hc'
            have : B j * m ≤ B j * k := Nat.mul_le_mul_left _ hc'
            omega
          have : B j * (k + 1) ≤ B j * m := Nat.mul_le_mul_left _ this
          have : est B j x.start + B j = B j * (k + 1) := by rw [hk]; ring
          omega
        | bev e j' => simp [counted, hout] at hp
        | bad => simp [counted, hout, hfr] at hp
    · rcases hw with hb | ⟨p, j', ⟨y, hy, hy'⟩, hj', h1, h2⟩
      · refine Finset.mem_union_left _ ?_
        simp only [S1, Finset.mem_filter, Finset.mem_range]
        exact ⟨lt_of_le_of_lt (est_le j x.start) (lt_of_lt_of_le (hok x hx).lt (hok x hx).le),
          est_dvd j x.start, hb⟩
      · refine Finset.mem_union_right _ ?_
        have hyp : y.stop = p := ((hok y hy).bev p j' hy').symm
        have hest : est B j p = est B j x.start :=
          est_eq_of hpos (est_dvd j x.start) h1.le (lt_of_le_of_lt h2 (lt_est_add hpos _))
        simp only [S2, List.mem_toFinset, List.mem_map, List.mem_filter]
        refine ⟨y, ⟨hy, ?_⟩, by rw [hyp, hest]⟩
        simp [bevLe, hy', hj']
  -- count by fibers: each fiber has at most one record (they share their stop)
  have hfib := Pool.P0057.sum_fiber L (fun _ => 1) (fun x => counted x && decide (len x < B j))
    (fun x => est B j x.start) (S1 ∪ S2) (fun x hx hp => (hend x hx hp).2)
  have hlen : ∀ (M : List RecB), (M.map fun _ => (1 : ℕ)).sum = M.length := by
    intro M; induction M with
    | nil => simp
    | cons y M ih => simp [ih]; omega
  rw [hlen] at hfib
  rw [hfib]
  have hcard : (S1 ∪ S2).card ≤ nBadB T B t j + L.countP (bevLe j) := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add (le_of_eq rfl) ?_)
    refine (List.toFinset_card_le _).trans ?_
    rw [List.length_map, List.countP_eq_length_filter]
  refine le_trans ?_ hcard
  calc ∑ s ∈ S1 ∪ S2, ((L.filter fun x => (counted x && decide (len x < B j)) &&
        decide (est B j x.start = s)).map fun _ => (1 : ℕ)).sum
      ≤ ∑ s ∈ S1 ∪ S2, 1 := by
        refine Finset.sum_le_sum fun s _ => ?_
        refine le_trans (Pool.P0057.sum_filter_mono L (fun _ => 1) _
          (fun x => decide (x.stop = s + B j)) fun x hx hp => ?_) ?_
        · simp only [Bool.and_eq_true, decide_eq_true_eq] at hp ⊢
          obtain ⟨hp1, hp2⟩ := hp
          have := (hend x hx (by simpa using hp1)).1
          rw [this, hp2]
        · rw [hlen]; exact chainB_stop_unique L τ0 hc (s + B j)
    _ = (S1 ∪ S2).card := by simp

end


/-- Number of bad-or-(b′) level-`j` epochs that the count charges. -/
noncomputable def KB (T : ℕ) (B : ℕ → ℕ) (t : ℕ → ℕ → Out) (L : List RecB) (j : ℕ) : ℕ :=
  nBadB T B t j + L.countP (bevLe j)

section
variable (h : HypB R T B t g)
include h

/-- **Cost assembly.** Over the counted records (covered and finest-bad):
`Σ √|I| ≤ T/√(B 0) + Σ_{1 ≤ j < R} B (j-1)·K_{j-1}/√(B j) + K_{R-1}·√(B (R-1))`, with
`K_j = #bad level-j epochs + #(b′)-records of thread ≤ j`. -/
theorem sum_sqrtB_le :
    (((theWalkB R T B t g).filter counted).map fun x => Real.sqrt (len x)).sum ≤
      T / Real.sqrt (B 0) +
        ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * KB T B t (theWalkB R T B t g) (j - 1) / Real.sqrt (B j) +
        KB T B t (theWalkB R T B t g) (R - 1) * Real.sqrt (B (R - 1)) := by
  obtain ⟨hc, hok, hsum, hshort⟩ := theWalkB_spec h
  set L := theWalkB R T B t g
  have hR := h.hR
  set F := L.filter counted
  have hpt : ∀ x ∈ F, Real.sqrt (len x) ≤ (len x : ℝ) / Real.sqrt (B 0) +
      ∑ j ∈ Finset.Ico 1 R, (if len x < B (j - 1) then (len x : ℝ) else 0) / Real.sqrt (B j) +
      (if len x < B (R - 1) then Real.sqrt (B (R - 1)) else 0) := by
    intro x _
    have hnn : ∀ j ∈ Finset.Ico 1 R,
        0 ≤ (if len x < B (j - 1) then (len x : ℝ) else 0) / Real.sqrt (B j) := by
      intro j _; positivity
    have h0' : (0 : ℝ) ≤ (len x : ℝ) / Real.sqrt (B 0) := by positivity
    have hS := Finset.sum_nonneg hnn
    by_cases hsm : len x < B (R - 1)
    · rw [if_pos hsm]
      have : Real.sqrt (len x) ≤ Real.sqrt (B (R - 1)) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hsm.le)
      linarith
    rw [if_neg hsm]
    push_neg at hsm
    have key : ∀ j, (0 : ℝ) < B j → B j ≤ len x →
        Real.sqrt (len x) ≤ (len x : ℝ) / Real.sqrt (B j) := by
      intro j hb hj
      rw [le_div_iff₀ (Real.sqrt_pos.2 hb)]
      calc Real.sqrt (len x) * Real.sqrt (B j) ≤ Real.sqrt (len x) * Real.sqrt (len x) := by
            gcongr
        _ = len x := Real.mul_self_sqrt (by positivity)
    by_cases h0 : B 0 ≤ len x
    · have := key 0 (by exact_mod_cast h.pos 0) h0
      linarith
    · have hex : ∃ j, B j ≤ len x := ⟨R - 1, hsm⟩
      set j0 := Nat.find hex with hj0
      have hj0s : B j0 ≤ len x := Nat.find_spec hex
      have hj0R : j0 ≤ R - 1 := Nat.find_min' hex hsm
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
      linarith
  refine (List.sum_le_sum hpt).trans ?_
  have hsplit : ∀ (M : List RecB), (M.map fun x => (len x : ℝ) / Real.sqrt (B 0) +
      ∑ j ∈ Finset.Ico 1 R, (if len x < B (j - 1) then (len x : ℝ) else 0) / Real.sqrt (B j) +
      (if len x < B (R - 1) then Real.sqrt (B (R - 1)) else 0)).sum =
      ((M.map len).sum : ℝ) / Real.sqrt (B 0) + ∑ j ∈ Finset.Ico 1 R,
        ((((M.filter fun x => decide (len x < B (j - 1))).map len).sum : ℕ) : ℝ) / Real.sqrt (B j) +
        ((M.filter fun x => decide (len x < B (R - 1))).length : ℝ) * Real.sqrt (B (R - 1)) := by
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
      by_cases hy : len y < B (R - 1)
      · simp [List.filter_cons, hy]; ring
      · simp [List.filter_cons, hy]; ring
  rw [hsplit]
  -- three comparisons
  have hF : (F.map len).sum ≤ T := by
    rw [← hsum]
    exact List.Sublist.sum_le_sum ((List.filter_sublist (p := counted) (l := L)).map len) (fun _ _ => Nat.zero_le _)
  have hfilt : ∀ q : RecB → Bool, F.filter q = L.filter fun x => counted x && q x := by
    intro q; simp only [F, List.filter_filter]
    congr 1; funext x; exact Bool.and_comm _ _
  have hT : ((F.map len).sum : ℝ) / Real.sqrt (B 0) ≤ T / Real.sqrt (B 0) := by
    gcongr
  have hmid : ∑ j ∈ Finset.Ico 1 R,
      ((((F.filter fun x => decide (len x < B (j - 1))).map len).sum : ℕ) : ℝ) / Real.sqrt (B j) ≤
      ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * KB T B t L (j - 1) / Real.sqrt (B j) := by
    gcongr with j hj
    rw [hfilt, ← Nat.cast_mul]
    exact_mod_cast hshort (j - 1) (by have := Finset.mem_Ico.1 hj; omega)
  have hlast : ((F.filter fun x => decide (len x < B (R - 1))).length : ℝ) * Real.sqrt (B (R - 1)) ≤
      KB T B t L (R - 1) * Real.sqrt (B (R - 1)) := by
    gcongr
    rw [hfilt]
    exact_mod_cast card_shortB_finest h hc hok
  linarith

end

end Pool.P0137
