import Pool.P0057.Walk

/-!
# Counting the records of P0057's inheritance walk

* `card_long_le`: records of length `≥ L` number at most `T / L`.
* `card_scale_le`: records of length in `[B (j+1), B j)` number at most `B j · nBad j / B (j+1)`
  (from P0057's short-record bound).
* `len_ge_finest`: every record has length at least `B (R-1)`.
* **`card_walk_le`**: the walk has at most `T / B 0 + Σ_{j < R-1} B j · nBad j / B (j+1)` records.
* `chain_start_ge`, `chain_starts_nodup`, **`sum_bad_len_le`**: the finest bad records have total length
  at most `B (R-1) · nBad (R-1)`.
-/

namespace Pool.P0086

open Pool.P0057

variable {R T : ℕ} {B : ℕ → ℕ} {t : ℕ → ℕ → Option ℕ}

/-- Records of length at least `L > 0` number at most `T / L` (their lengths sum to at most `T`). -/
lemma card_long_le (h : Hyp R T B t) {L : ℕ} (hL : 0 < L) :
    ((theWalk R T B t).filter fun x => decide (L ≤ len x)).length * L ≤ T := by
  obtain ⟨-, -, hsum, -⟩ := theWalk_spec h
  have : ∀ (M : List Rec), ((M.filter fun x => decide (L ≤ len x)).length * L) ≤ (M.map len).sum := by
    intro M
    induction M with
    | nil => simp
    | cons y M ih =>
      by_cases hy : L ≤ len y
      · simp [List.filter_cons, hy, List.length_cons, Nat.succ_mul]; omega
      · simp [List.filter_cons, hy]; omega
  exact (this _).trans hsum.le

/-- Records of length in `[B (j+1), B j)` number at most `B j · nBad j / B (j+1)`. -/
lemma card_scale_le (h : Hyp R T B t) {j : ℕ} (hj : j < R) :
    ((theWalk R T B t).filter fun x => decide (B (j + 1) ≤ len x ∧ len x < B j)).length * B (j + 1) ≤
      B j * nBad T B t j := by
  obtain ⟨-, -, -, hshort⟩ := theWalk_spec h
  have hs := hshort j hj
  have : ∀ (M : List Rec), (M.filter fun x => decide (B (j + 1) ≤ len x ∧ len x < B j)).length * B (j + 1) ≤
      ((M.filter fun x => decide (len x < B j)).map len).sum := by
    intro M
    induction M with
    | nil => simp
    | cons y M ih =>
      by_cases hy1 : len y < B j
      · rw [List.filter_cons_of_pos (p := fun x => decide (len x < B j)) (by simpa using hy1),
          List.map_cons, List.sum_cons]
        by_cases hy2 : B (j + 1) ≤ len y
        · rw [List.filter_cons_of_pos (by simp [hy1, hy2]), List.length_cons, Nat.succ_mul]; omega
        · rw [List.filter_cons_of_neg (by simp [hy2])]; omega
      · rw [List.filter_cons_of_neg (p := fun x => decide (len x < B j)) (by simpa using hy1),
          List.filter_cons_of_neg (by simp [hy1])]
        exact ih
  exact (this _).trans hs


lemma length_le_sum_filters {α κ : Type} (L : List α) (P : κ → α → Bool) (s : Finset κ)
    (h : ∀ x ∈ L, ∃ c ∈ s, P c x = true) : L.length ≤ ∑ c ∈ s, (L.filter (P c)).length := by
  induction L with
  | nil => simp
  | cons y L ih =>
    have ih := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨c0, hc0, hy⟩ := h y List.mem_cons_self
    have : ∀ c ∈ s, ((y :: L).filter (P c)).length = (if P c y then 1 else 0) + (L.filter (P c)).length := by
      intro c _
      by_cases hc : P c y = true
      · simp [List.filter_cons, hc]; omega
      · simp [List.filter_cons, hc]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, List.length_cons]
    have h1 : 1 ≤ ∑ c ∈ s, (if P c y then 1 else 0) := by
      calc 1 = (if P c0 y then 1 else 0) := by simp [hy]
        _ ≤ ∑ c ∈ s, (if P c y then 1 else 0) :=
          Finset.single_le_sum (f := fun c => if P c y then 1 else 0) (fun _ _ => Nat.zero_le _) hc0
    omega

/-- Every walk record has length at least the finest epoch `B (R - 1)`. -/
lemma len_ge_finest (h : Hyp R T B t) {x : Rec} (hx : x ∈ theWalk R T B t) : B (R - 1) ≤ len x := by
  obtain ⟨-, hok, -, -⟩ := theWalk_spec h
  have hR := h.hR
  have hok := hok x hx
  cases hcv : x.cov
  · obtain ⟨h1, -, h3⟩ := hok.fin hcv
    unfold len; rw [h3]; have : x.lvl = R - 1 := by omega
    rw [this]; omega
  · have := h.lb x.start x.lvl x.stop hok.inv.dvd (lt_of_lt_of_le hok.lt hok.le) hok.inv.lt (hok.cov hcv)
    have := B_le_of_le h (show x.lvl ≤ R - 1 by have := hok.inv.lt; omega) (by omega)
    unfold len; omega

/-- **Number of walk records**: at most `T / B 0 + Σ_{j < R - 1} B j · nBad j / B (j+1)`. -/
theorem card_walk_le (h : Hyp R T B t) :
    ((theWalk R T B t).length : ℝ) ≤ T / B 0 +
      ∑ j ∈ Finset.range (R - 1), (B j : ℝ) * nBad T B t j / B (j + 1) := by
  classical
  set L := theWalk R T B t
  -- classes: `none` = long (len ≥ B 0), `some j` = scale j
  let P : Option ℕ → Rec → Bool := fun c x => match c with
    | none => decide (B 0 ≤ len x)
    | some j => decide (B (j + 1) ≤ len x ∧ len x < B j)
  let s : Finset (Option ℕ) := insert none ((Finset.range (R - 1)).image some)
  have hcover : ∀ x ∈ L, ∃ c ∈ s, P c x = true := by
    intro x hx
    have hfin := len_ge_finest h hx
    by_cases h0 : B 0 ≤ len x
    · exact ⟨none, by simp [s], by simp [P, h0]⟩
    · push Not at h0
      have hex : ∃ j, B j ≤ len x := ⟨R - 1, hfin⟩
      set j0 := Nat.find hex
      have hj0s : B j0 ≤ len x := Nat.find_spec hex
      have hj0R : j0 ≤ R - 1 := Nat.find_min' hex hfin
      have hj01 : 1 ≤ j0 := by
        by_contra hc
        have : j0 = 0 := by omega
        rw [this] at hj0s; omega
      have hmin : len x < B (j0 - 1) := by
        have := Nat.find_min hex (show j0 - 1 < j0 by omega)
        push Not at this; exact this
      refine ⟨some (j0 - 1), by simp [s]; omega, ?_⟩
      simp only [P, decide_eq_true_eq]
      exact ⟨by rw [show j0 - 1 + 1 = j0 by omega]; exact hj0s, hmin⟩
  have hlen := length_le_sum_filters L P s hcover
  have hnone : s = insert none ((Finset.range (R - 1)).image some) := rfl
  rw [hnone, Finset.sum_insert (by simp), Finset.sum_image (by simp)] at hlen
  have hR := h.hR
  have hB0 : (0 : ℝ) < B 0 := by exact_mod_cast h.pos 0
  have h1 : ((L.filter (P none)).length : ℝ) ≤ T / B 0 := by
    rw [le_div_iff₀ hB0]
    exact_mod_cast card_long_le h (h.pos 0)
  have h2 : ∀ j ∈ Finset.range (R - 1), ((L.filter (P (some j))).length : ℝ) ≤ (B j : ℝ) * nBad T B t j / B (j + 1) := by
    intro j hj
    have hBj : (0 : ℝ) < B (j + 1) := by exact_mod_cast h.pos (j + 1)
    rw [le_div_iff₀ hBj]
    exact_mod_cast card_scale_le h (j := j) (by have := Finset.mem_range.1 hj; omega)
  calc (L.length : ℝ) ≤ ((L.filter (P none)).length : ℝ) +
        ∑ j ∈ Finset.range (R - 1), ((L.filter (P (some j))).length : ℝ) := by exact_mod_cast hlen
    _ ≤ _ := add_le_add h1 (Finset.sum_le_sum h2)


lemma chain_start_ge {T : ℕ} : ∀ (L : List Rec) (τ : ℕ), Chain T τ L → ∀ x ∈ L, τ ≤ x.start
  | [], _, _, x, hx => absurd hx (by simp)
  | y :: L, τ, ⟨hs, hlt, hc⟩, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · omega
    · have := chain_start_ge L y.stop hc x hx; omega

lemma chain_starts_nodup {T : ℕ} : ∀ (L : List Rec) (τ : ℕ), Chain T τ L → (L.map Rec.start).Nodup
  | [], _, _ => by simp
  | y :: L, τ, ⟨hs, hlt, hc⟩ => by
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, chain_starts_nodup L y.stop hc⟩
    obtain ⟨x, hx, hxs⟩ := List.mem_map.1 hmem
    have := chain_start_ge L y.stop hc x hx
    omega

/-- **Total length of the finest bad records** is at most `B (R-1) · nBad (R-1)`. -/
theorem sum_bad_len_le (h : Hyp R T B t) :
    (((theWalk R T B t).filter fun x => !x.cov).map len).sum ≤ B (R - 1) * nBad T B t (R - 1) := by
  classical
  obtain ⟨hc, hok, -, -⟩ := theWalk_spec h
  set L := theWalk R T B t
  set M := L.filter fun x => !x.cov
  have hR := h.hR
  -- each bad record has length `B (R-1)` and a bad start
  have hlenM : ∀ x ∈ M, len x = B (R - 1) := by
    intro x hx
    obtain ⟨hxL, hxc⟩ := List.mem_filter.1 hx
    have hcv : x.cov = false := by simpa using hxc
    obtain ⟨h1, -, h3⟩ := (hok x hxL).fin hcv
    unfold len; rw [h3]; have : x.lvl = R - 1 := by omega
    rw [this]; omega
  have hsum : (M.map len).sum = M.length * B (R - 1) := by
    have : M.map len = M.map (fun _ => B (R - 1)) := List.map_congr_left hlenM
    rw [this, List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hsum, mul_comm]
  apply Nat.mul_le_mul_left
  -- the starts of bad records are distinct bad level-`(R-1)` epoch starts
  have hnd : (M.map Rec.start).Nodup := (chain_starts_nodup L 0 hc).sublist (List.Sublist.map _ List.filter_sublist)
  have hsub : ∀ s ∈ M.map Rec.start, s ∈ (Finset.range T).filter fun s => B (R - 1) ∣ s ∧ t s (R - 1) = none := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hxL, hxc⟩ := List.mem_filter.1 hx
    have hcv : x.cov = false := by simpa using hxc
    obtain ⟨h1, h2, -⟩ := (hok x hxL).fin hcv
    have hxl : x.lvl = R - 1 := by omega
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨lt_of_lt_of_le (hok x hxL).lt (hok x hxL).le, ?_, ?_⟩
    · rw [← hxl]; exact (hok x hxL).inv.dvd
    · rw [← hxl]; exact h2
  calc M.length = (M.map Rec.start).length := (List.length_map _).symm
    _ = (M.map Rec.start).toFinset.card := (List.toFinset_card_of_nodup hnd).symm
    _ ≤ nBad T B t (R - 1) := Finset.card_le_card (fun s hs => hsub s (List.mem_toFinset.1 hs))

end Pool.P0086
