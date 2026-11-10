import Pool.P0049.Walk
/-!
# The Peng–Rubinstein walk WITH inheritance (deterministic part)

P0049 formalized the multi-thread bad-epoch walk under `Pool.P0049.Hyp`. There, a good interval of
thread `j+1` must end inside its parent thread-`j` epoch (restart without inheritance). It was pointed out that in Peng–Rubinstein (arXiv:2303.01673, §4.2, Baseline₊) a comparator copy that
survives a restart is inherited by a coarser thread, so its eviction time can lie beyond the parent
epoch. Their bad-epoch count (Lemma 4.19, "a passive copy in a bad epoch survives to the end") is
about that scheme.

This file proves the same walk bounds under the weaker `HypI`. It uses the same walk
(`Pool.P0049.walk`) and the same events. `HypI` drops `ev_le` (stay inside the parent) and keeps:
- `ev_leT`: `e ≤ T`;
- `ev_cross`: if the interval `[a, e)` of a thread-`j` copy crosses the end of its thread-`i`
  ancestor epoch (`i < j`, `nxt i a < e`), then `B i ∣ e`. After crossing, the copy lives in thread
  `≤ i`, whose covers happen at multiples of `B i`. This is our reading (not proved here) of PR23's `K(a)`: the timesteps reachable by
  `⊕`, which rise to coarser threads at parent ends (Definition 4.17).
`HypI.of_hyp`: P0049's `Hyp` implies `HypI`.

**Counting by length class instead of by thread** (PR23 Lemma 4.18(ii): `L_r` = intervals shorter
than `B_{r-1}`):
- `slen_le`: good intervals shorter than `B i`, together with the bad deepest epochs, have total
  length `≤ B i · H_i`. Here `H_i` is the number of bad thread-`i` epochs visited by the walk.
- `sum_le_walkI`: the same bound as `Pool.P0049.sum_le_walk`,
  `wt 0 · T + Σ_{i<D} wt (i+1) · B i · H_i + c · H_D`, now under `HypI`. Each good interval is charged
  to its length class.
- `sum_le_walkI_dyadic`: the dyadic corollary (halving for `i < D`, `H_i ≤ h`).
- `sum_Ico_eq_walk` (partition), `valid_of_mem`, `badStart_sorted`, `nb_le_card` (`H_i ≤` all bad
  thread-`i` epochs) are re-proved under `HypI`.

Here a bad epoch (`ev k a = none`) means that the copy is never covered before `T`. This is PR23's
"survives to the end", as we read it, the event whose count their Lemma 4.19 bounds. That a concrete
algorithm's eviction data satisfies `HypI` must be proved for that algorithm.
-/

namespace Pool.P0056

open Pool.P0049 (Ev walk rise cov nb badStart sum_nb_eq walk_good walk_desc walk_leaf walk_stop
  rise_le_D not_dvd_of_lt_rise rise_le_of_dvd nxt Valid wt sqrt_add_le wt_nonneg)

/-- Hypotheses for the walk WITH inheritance. -/
structure HypI (D : ℕ) (B : ℕ → ℕ) (T : ℕ) (ev : ℕ → ℕ → Option ℕ) : Prop where
  pos : ∀ j, 0 < B j
  chain : ∀ k, B (k+1) ∣ B k
  T_dvd : B 0 ∣ T
  ev_ge : ∀ j a e, j ≤ D → B j ∣ a → a < T → ev j a = some e → a + B j ≤ e
  ev_dvd : ∀ j a e, j ≤ D → B j ∣ a → a < T → ev j a = some e → B j ∣ e
  ev_leT : ∀ j a e, j ≤ D → B j ∣ a → a < T → ev j a = some e → e ≤ T
  ev_cross : ∀ j a e i, j ≤ D → B j ∣ a → a < T → ev j a = some e → i < j →
    nxt (B := B) i a < e → B i ∣ e

variable {D : ℕ} {B : ℕ → ℕ} {T : ℕ} {ev : ℕ → ℕ → Option ℕ}

lemma dvd_of_le (h : HypI D B T ev) {i k : ℕ} (hik : i ≤ k) : B k ∣ B i := by
  induction k, hik using Nat.le_induction with
  | base => exact dvd_rfl
  | succ k _ ih => exact (h.chain k).trans ih

lemma dvd_rise (h : HypI D B T ev) {u j : ℕ} (hj : j ≤ D) (hd : B j ∣ u) : B (rise D B u) ∣ u := by
  rcases Nat.find_spec (⟨D, Or.inl le_rfl⟩ : ∃ j, D ≤ j ∨ B j ∣ u) with h1 | h1
  · have : rise D B u = D := le_antisymm (rise_le_D u) h1
    rw [this]; exact (dvd_of_le h hj).trans hd
  · exact h1

lemma dvd_of_rise_le (h : HypI D B T ev) {u i j : ℕ} (hj : j ≤ D) (hd : B j ∣ u)
    (hi : rise D B u ≤ i) : B i ∣ u :=
  (dvd_of_le h hi).trans (dvd_rise h hj hd)

lemma lt_nxt (h : HypI D B T ev) (i s : ℕ) : s < nxt (B := B) i s := by
  unfold nxt
  have := h.pos i
  have := Nat.lt_div_mul_add (a := s) this
  nlinarith [Nat.div_add_mod s (B i), Nat.mod_lt s (h.pos i)]

lemma nxt_le_of_dvd (h : HypI D B T ev) {i s m : ℕ} (hd : B i ∣ m) (hs : s < m) :
    nxt (B := B) i s ≤ m := by
  unfold nxt
  obtain ⟨c, rfl⟩ := hd
  have hp := h.pos i
  have : s / B i < c := by
    rw [Nat.div_lt_iff_lt_mul hp]; linarith [mul_comm (B i) c]
  nlinarith

lemma nxt_mono (h : HypI D B T ev) {i k : ℕ} (hik : i ≤ k) (s : ℕ) :
    nxt (B := B) k s ≤ nxt (B := B) i s := by
  apply nxt_le_of_dvd h
  · exact Dvd.dvd.mul_left (dvd_of_le h hik) _
  · exact lt_nxt h i s

lemma nxt_le_T (h : HypI D B T ev) {i s : ℕ} (hs : s < T) : nxt (B := B) i s ≤ T :=
  nxt_le_of_dvd h ((dvd_of_le h (Nat.zero_le i)).trans h.T_dvd) hs

lemma nxt_of_dvd (h : HypI D B T ev) {i s : ℕ} (hd : B i ∣ s) : nxt (B := B) i s = s + B i := by
  unfold nxt; obtain ⟨c, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left _ (h.pos i)]; ring

theorem sum_Ico_eq_walk (h : HypI D B T ev) (f : ℕ → ℝ) :
    ∀ s j, j ≤ D → B j ∣ s →
      ∑ u ∈ Finset.Ico s T, f u = ((walk D B T ev s j).map (cov D B f)).sum := by
  intro s j
  induction s, j using walk.induct D B T ev with
  | case1 s j hs e he hse ih =>
    intro hj hd
    rw [walk_good hs he hse]
    have heT := h.ev_leT j s e hj hd hs he
    have hde := h.ev_dvd j s e hj hd hs he
    rw [List.map_cons, List.sum_cons, ← ih (rise_le_D e) (dvd_rise h hj hde)]
    simp only [cov]
    exact (Finset.sum_Ico_consecutive f hse.le heT).symm
  | case2 s j hs e he hse =>
    intro hj hd
    have := h.ev_ge j s e hj hd hs he
    have := h.pos j
    omega
  | case3 s j hs he hjD ih =>
    intro hj hd
    rw [walk_desc hs he hjD, List.map_cons, List.sum_cons, ← ih hjD ((h.chain j).trans hd)]
    simp [cov, show j ≠ D by omega]
  | case4 s j hs he hjD hb ih =>
    intro hj hd
    have hjD' : j = D := by omega
    subst hjD'
    rw [walk_leaf hs he hjD hb]
    have hle : s + B j ≤ T := by rw [← nxt_of_dvd h hd]; exact nxt_le_T h hs
    rw [List.map_cons, List.sum_cons,
      ← ih (rise_le_D _) (dvd_rise h le_rfl (dvd_add hd dvd_rfl))]
    simp only [cov, ite_true]
    exact (Finset.sum_Ico_consecutive f (by omega) hle).symm
  | case5 s j hs he hjD hb =>
    intro _ _; exact absurd (h.pos D) hb
  | case6 s j hs =>
    intro _ _
    rw [walk_stop hs, Finset.Ico_eq_empty (by omega)]; simp

lemma div_eq_of_lt_nxt (h : HypI D B T ev) {i s e : ℕ} (hse : s ≤ e) (he : e < nxt (B := B) i s) :
    e / B i = s / B i := by
  unfold nxt at he
  apply le_antisymm
  · have : e / B i < s / B i + 1 := (Nat.div_lt_iff_lt_mul (h.pos i)).2 he
    omega
  · exact Nat.div_le_div_right hse

theorem valid_of_mem (h : HypI D B T ev) :
    ∀ s j, j ≤ D → B j ∣ s → ∀ x ∈ walk D B T ev s j, Valid D B T ev x := by
  intro s j
  induction s, j using walk.induct D B T ev with
  | case1 s j hs e he hse ih =>
    intro hj hd x hx
    rw [walk_good hs he hse] at hx
    have hde := h.ev_dvd j s e hj hd hs he
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hj, hd, hs, he, hse⟩
    · exact ih (rise_le_D e) (dvd_rise h hj hde) x hx
  | case2 s j hs e he hse =>
    intro hj hd
    have := h.ev_ge j s e hj hd hs he
    have := h.pos j
    omega
  | case3 s j hs he hjD ih =>
    intro hj hd x hx
    rw [walk_desc hs he hjD] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hj, hd, hs, he⟩
    · exact ih hjD ((h.chain j).trans hd) x hx
  | case4 s j hs he hjD hb ih =>
    intro hj hd x hx
    have hjD' : j = D := by omega
    rw [walk_leaf hs he hjD hb] at hx
    rw [hjD'] at hd he
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨le_rfl, hd, hs, he⟩
    · exact ih (rise_le_D _) (dvd_rise h le_rfl (dvd_add hd dvd_rfl)) x hx
  | case5 s j hs he hjD hb =>
    intro _ _; exact absurd (h.pos D) hb
  | case6 s j hs =>
    intro _ _ x hx
    rw [walk_stop hs] at hx; simp at hx

theorem badStart_sorted (h : HypI D B T ev) (i : ℕ) :
    ∀ s j, j ≤ D → B j ∣ s →
      ((walk D B T ev s j).filterMap (badStart i)).Pairwise (· < ·) ∧
      ∀ a ∈ (walk D B T ev s j).filterMap (badStart i), s < a ∨ (s = a ∧ j ≤ i) := by
  intro s j
  induction s, j using walk.induct D B T ev with
  | case1 s j hs e he hse ih =>
    intro hj hd
    rw [walk_good hs he hse]
    have hde := h.ev_dvd j s e hj hd hs he
    obtain ⟨h1, h2⟩ := ih (rise_le_D e) (dvd_rise h hj hde)
    simp only [List.filterMap_cons, badStart]
    refine ⟨h1, fun a ha => ?_⟩
    rcases h2 a ha with h3 | h3 <;> left <;> omega
  | case2 s j hs e he hse =>
    intro hj hd
    have := h.ev_ge j s e hj hd hs he
    have := h.pos j
    omega
  | case3 s j hs he hjD ih =>
    intro hj hd
    rw [walk_desc hs he hjD]
    obtain ⟨h1, h2⟩ := ih hjD ((h.chain j).trans hd)
    simp only [List.filterMap_cons, badStart]
    by_cases hji : j = i
    · subst hji
      simp only [ite_true]
      refine ⟨List.Pairwise.cons (fun a ha => ?_) h1, fun a ha => ?_⟩
      · rcases h2 a ha with h3 | h3
        · exact h3
        · omega
      · rcases List.mem_cons.1 ha with rfl | ha
        · right; exact ⟨rfl, le_rfl⟩
        · rcases h2 a ha with h3 | h3
          · left; exact h3
          · omega
    · simp only [ite_eq_right hji]
      refine ⟨h1, fun a ha => ?_⟩
      rcases h2 a ha with h3 | h3
      · left; exact h3
      · right; omega
  | case4 s j hs he hjD hb ih =>
    intro hj hd
    have hjD' : j = D := by omega
    rw [walk_leaf hs he hjD hb]
    rw [hjD'] at hd
    obtain ⟨h1, h2⟩ := ih (rise_le_D _) (dvd_rise h le_rfl (dvd_add hd dvd_rfl))
    simp only [List.filterMap_cons, badStart]
    have hb' := h.pos D
    by_cases hDi : D = i
    · simp only [ite_eq_left hDi]
      refine ⟨List.Pairwise.cons (fun a ha => ?_) h1, fun a ha => ?_⟩
      · rcases h2 a ha with h3 | h3 <;> omega
      · rcases List.mem_cons.1 ha with rfl | ha
        · right; exact ⟨rfl, by omega⟩
        · rcases h2 a ha with h3 | h3 <;> left <;> omega
    · simp only [ite_eq_right hDi]
      refine ⟨h1, fun a ha => ?_⟩
      rcases h2 a ha with h3 | h3 <;> left <;> omega
  | case5 s j hs he hjD hb =>
    intro _ _; exact absurd (h.pos D) hb
  | case6 s j hs =>
    intro _ _
    rw [walk_stop hs]; simp

theorem nb_le_card (h : HypI D B T ev) (i : ℕ) :
    ((walk D B T ev 0 0).map (nb i)).sum ≤
      ((Finset.range T).filter (fun a => B i ∣ a ∧ ev i a = none)).card := by
  rw [sum_nb_eq]
  set L := (walk D B T ev 0 0).filterMap (badStart i)
  have hnd : L.Nodup := (badStart_sorted h i 0 0 (Nat.zero_le _) (dvd_zero _)).1.imp
    (fun hab => ne_of_lt hab)
  rw [← List.toFinset_card_of_nodup hnd]
  apply Finset.card_le_card
  intro a ha
  rw [List.mem_toFinset, List.mem_filterMap] at ha
  obtain ⟨x, hx, hxa⟩ := ha
  have hv := valid_of_mem h 0 0 (Nat.zero_le _) (dvd_zero _) x hx
  cases x with
  | good _ _ _ => simp [badStart] at hxa
  | bad a' k =>
    simp only [badStart] at hxa
    split_ifs at hxa with hk
    · cases hxa; subst hk
      obtain ⟨-, hd, ha', he⟩ := hv
      simp [Finset.mem_filter, ha', hd, he]


lemma B_le_of_le (h : HypI D B T ev) {i k : ℕ} (hik : i ≤ k) : B k ≤ B i :=
  Nat.le_of_dvd (h.pos i) (dvd_of_le h hik)

/-- length of the *short* events for class `i`: good intervals shorter than `B i`, and the bad
deepest epochs (when `i < D`). -/
def slen (D : ℕ) (B : ℕ → ℕ) (i : ℕ) : Ev → ℕ
  | Ev.good a e _ => if e - a < B i then e - a else 0
  | Ev.bad _ k => if k = D ∧ i < D then B D else 0

/-- Counting invariant with inheritance: short events (length `< B i`) in the walk from `(s, j)`
have total length at most `B i` times the visited bad thread-`i` epochs, plus the rest of the
current thread-`i` ancestor epoch when `i < j`. -/
theorem slen_le (h : HypI D B T ev) (i : ℕ) (hi : i < D) :
    ∀ s j, j ≤ D → B j ∣ s →
      ((walk D B T ev s j).map (slen D B i)).sum + (if i < j then s else 0) ≤
        B i * ((walk D B T ev s j).map (nb i)).sum + (if i < j then nxt (B := B) i s else 0) := by
  intro s j
  induction s, j using walk.induct D B T ev with
  | case1 s j hs e he hse ih =>
    intro hj hd
    rw [walk_good hs he hse]
    have hde := h.ev_dvd j s e hj hd hs he
    have hr := rise_le_of_dvd (D := D) hde
    have IH := ih (rise_le_D e) (dvd_rise h hj hde)
    simp only [List.map_cons, List.sum_cons, slen, nb, zero_add]
    have hnx_le : nxt (B := B) i s ≤ s + B i := by
      unfold nxt; have := Nat.div_mul_le_self s (B i); nlinarith
    have hlt := lt_nxt h i s
    by_cases hY : i < rise D B e
    · have hij : i < j := lt_of_lt_of_le hY hr
      have hnd := not_dvd_of_lt_rise hY
      have hle : e ≤ nxt (B := B) i s := by
        by_contra hc
        exact hnd (h.ev_cross j s e i hj hd hs he hij (by omega))
      have hne : e ≠ nxt (B := B) i s := by
        intro heq; apply hnd; rw [heq]; exact Dvd.intro_left _ rfl
      have hnx : nxt (B := B) i e = nxt (B := B) i s := by
        unfold nxt; rw [div_eq_of_lt_nxt h hse.le (lt_of_le_of_ne hle hne)]
      rw [ite_eq_left hY, ite_eq_left hY, hnx] at IH
      rw [ite_eq_left hij, ite_eq_left hij, ite_eq_left (by omega : e - s < B i)]
      omega
    · rw [ite_eq_right hY, ite_eq_right hY] at IH
      by_cases hsh : e - s < B i
      · have hij : i < j := by
          by_contra hc
          have := B_le_of_le h (show j ≤ i by omega)
          have := h.ev_ge j s e hj hd hs he
          omega
        have hle : e ≤ nxt (B := B) i s := by
          by_contra hc
          have hdi := h.ev_cross j s e i hj hd hs he hij (by omega)
          have h1 := nxt_le_of_dvd h hdi (show nxt (B := B) i s < e by omega)
          rw [nxt_of_dvd h (Dvd.intro_left _ rfl : B i ∣ nxt (B := B) i s)] at h1
          omega
        rw [ite_eq_left hsh, ite_eq_left hij, ite_eq_left hij]
        omega
      · rw [ite_eq_right hsh, zero_add]
        split_ifs <;> omega
  | case2 s j hs e he hse =>
    intro hj hd
    have := h.ev_ge j s e hj hd hs he
    have := h.pos j
    omega
  | case3 s j hs he hjD ih =>
    intro hj hd
    rw [walk_desc hs he hjD]
    have IH := ih hjD ((h.chain j).trans hd)
    simp only [List.map_cons, List.sum_cons, slen, nb]
    have hlen0 : (if j = D ∧ i < D then B D else 0) = 0 := by
      rw [ite_eq_right]; omega
    rw [hlen0, zero_add]
    have hnx := nxt_of_dvd h hd
    by_cases hji : j = i
    · subst hji
      rw [ite_eq_left (by omega : j < j + 1), ite_eq_left (by omega : j < j + 1), hnx] at IH
      rw [ite_eq_left rfl, ite_eq_right (lt_irrefl j), ite_eq_right (lt_irrefl j)]
      nlinarith
    · rw [ite_eq_right hji, zero_add]
      by_cases hij : i < j
      · rw [ite_eq_left (by omega : i < j + 1), ite_eq_left (by omega : i < j + 1)] at IH
        rw [ite_eq_left hij, ite_eq_left hij]
        exact IH
      · rw [ite_eq_right (by omega : ¬ i < j + 1), ite_eq_right (by omega : ¬ i < j + 1)] at IH
        rw [ite_eq_right hij, ite_eq_right hij]
        exact IH
  | case4 s j hs he hjD hb ih =>
    intro hj hd
    have hjD' : j = D := by omega
    rw [walk_leaf hs he hjD hb]
    rw [hjD'] at hd
    have hde : B D ∣ s + B D := dvd_add hd dvd_rfl
    have IH := ih (rise_le_D _) (dvd_rise h le_rfl hde)
    simp only [List.map_cons, List.sum_cons, slen, nb]
    rw [ite_eq_right (by omega : D ≠ i), zero_add, ite_eq_left (⟨trivial, hi⟩ : True ∧ i < D)]
    have hij : i < j := by omega
    have hle : s + B D ≤ nxt (B := B) i s := by
      rw [← nxt_of_dvd h hd]; exact nxt_mono h hi.le s
    have hse : s < s + B D := by have := h.pos D; omega
    rw [ite_eq_left hij, ite_eq_left hij]
    by_cases hY : i < rise D B (s + B D)
    · have hne : s + B D ≠ nxt (B := B) i s := by
        intro heq; apply not_dvd_of_lt_rise hY; rw [heq]; exact Dvd.intro_left _ rfl
      have hnx : nxt (B := B) i (s + B D) = nxt (B := B) i s := by
        unfold nxt; rw [div_eq_of_lt_nxt h hse.le (lt_of_le_of_ne hle hne)]
      rw [ite_eq_left hY, ite_eq_left hY, hnx] at IH
      omega
    · rw [ite_eq_right hY, ite_eq_right hY] at IH
      have hdi : B i ∣ s + B D := dvd_of_rise_le h le_rfl hde (by omega)
      have hge := nxt_le_of_dvd h hdi hse
      omega
  | case5 s j hs he hjD hb =>
    intro _ _; exact absurd (h.pos D) hb
  | case6 s j hs =>
    intro _ _
    rw [walk_stop hs]
    simp only [List.map_nil, List.sum_nil, mul_zero, zero_add]
    split_ifs
    · exact (lt_nxt h i s).le
    · exact le_rfl

/-- length of a good interval if it belongs to length class `k`: class `0` is `[B 0, ∞)`, class
`k+1` is `[B (k+1), B k)`. Bad events belong to no class. -/
def ccl (B : ℕ → ℕ) (k : ℕ) : Ev → ℕ
  | Ev.good a e _ =>
    if k = 0 then (if B 0 ≤ e - a then e - a else 0)
    else (if B k ≤ e - a ∧ e - a < B (k - 1) then e - a else 0)
  | Ev.bad _ _ => 0

lemma ccl_le_slen (k : ℕ) (x : Ev) : ccl B (k+1) x ≤ slen D B k x := by
  cases x with
  | good a e j =>
    simp only [ccl, slen, Nat.add_sub_cancel, Nat.add_one_ne_zero, ite_false]
    split_ifs <;> omega
  | bad a j => simp [ccl]

/-- **Walk cost bound with inheritance.** Same conclusion as `Pool.P0049.sum_le_walk`, under
the weaker `HypI` (good intervals may cross ancestor epochs, provided that after crossing the end of
the thread-`i` ancestor they end at a multiple of `B i`). -/
theorem sum_le_walkI (h : HypI D B T ev) (r : ℕ → ℝ) {α β c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hgood : ∀ a e k, k ≤ D → B k ∣ a → a < T → ev k a = some e →
      ∑ u ∈ Finset.Ico a e, r u ≤ α * Real.sqrt ((e - a : ℕ) : ℝ) + β)
    (hleaf : ∀ a, B D ∣ a → a < T → ev D a = none →
      ∑ u ∈ Finset.Ico a (a + B D), r u ≤ c) :
    ∑ u ∈ Finset.range T, r u ≤
      wt B α β 0 * T +
      ∑ i ∈ Finset.range D,
        wt B α β (i+1) * (B i * (((walk D B T ev 0 0).map (nb i)).sum : ℝ)) +
      c * (((walk D B T ev 0 0).map (nb D)).sum : ℝ) := by
  have hw := wt_nonneg B hα hβ
  have hpt : ∀ x, Valid D B T ev x →
      cov D B r x ≤ ∑ k ∈ Finset.range (D+1), wt B α β k * (ccl B k x : ℝ) +
        c * (nb D x : ℝ) := by
    intro x hx
    cases x with
    | good a e j =>
      obtain ⟨hj, hd, ha, he, hae⟩ := hx
      have hge := h.ev_ge j a e hj hd ha he
      have hex : ∃ k, B k ≤ e - a := ⟨j, by omega⟩
      set k0 := Nat.find hex with hk0
      have hk0spec : B k0 ≤ e - a := Nat.find_spec hex
      have hk0j : k0 ≤ j := Nat.find_min' hex (by omega)
      have hccl : ccl B k0 (Ev.good a e j) = e - a := by
        simp only [ccl]
        by_cases hz : k0 = 0
        · rw [ite_eq_left hz, ite_eq_left (hz ▸ hk0spec)]
        · rw [ite_eq_right hz]
          have hlt : e - a < B (k0 - 1) := by
            have := Nat.find_min hex (show k0 - 1 < k0 by omega)
            omega
          rw [ite_eq_left ⟨hk0spec, hlt⟩]
      have hsingle : wt B α β k0 * ((e - a : ℕ) : ℝ) ≤
          ∑ k ∈ Finset.range (D+1), wt B α β k * (ccl B k (Ev.good a e j) : ℝ) := by
        have := Finset.single_le_sum (f := fun k => wt B α β k * (ccl B k (Ev.good a e j) : ℝ))
          (fun k _ => mul_nonneg (hw k) (Nat.cast_nonneg _))
          (Finset.mem_range.2 (show k0 < D + 1 by omega))
        simpa [hccl] using this
      simp only [cov, nb, Nat.cast_zero, mul_zero, add_zero]
      refine (hgood a e j hj hd ha he).trans ((sqrt_add_le α β _ _ hα hβ
        (by exact_mod_cast h.pos k0) (by exact_mod_cast hk0spec)).trans hsingle)
    | bad a k =>
      obtain ⟨hk, hd, ha, he⟩ := hx
      have hs0 : 0 ≤ ∑ k' ∈ Finset.range (D+1), wt B α β k' * (ccl B k' (Ev.bad a k) : ℝ) :=
        Finset.sum_nonneg (fun k' _ => mul_nonneg (hw k') (Nat.cast_nonneg _))
      simp only [cov, nb]
      split_ifs with hkD
      · subst hkD; simp only [Nat.cast_one, mul_one]
        have := hleaf a hd ha he; linarith
      · simp only [Nat.cast_zero, mul_zero, add_zero]; exact hs0
  have hlist : ∀ L : List Ev, (∀ x ∈ L, Valid D B T ev x) →
      (L.map (cov D B r)).sum ≤ ∑ k ∈ Finset.range (D+1),
        wt B α β k * (((L.map (ccl B k)).sum : ℕ) : ℝ) + c * (((L.map (nb D)).sum : ℕ) : ℝ) := by
    intro L hL
    induction L with
    | nil => simp
    | cons x L ih =>
      have h1 := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
      have h2 := hpt x (hL x List.mem_cons_self)
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, mul_add, Finset.sum_add_distrib]
      linarith
  have hval := valid_of_mem h 0 0 (Nat.zero_le _) (dvd_zero _)
  have hpart := sum_Ico_eq_walk h r 0 0 (Nat.zero_le _) (dvd_zero _)
  -- class 0 has total length ≤ T
  have hT0 : (((walk D B T ev 0 0).map (ccl B 0)).sum : ℝ) ≤ T := by
    have hpart1 := sum_Ico_eq_walk h (fun _ => (1 : ℝ)) 0 0 (Nat.zero_le _) (dvd_zero _)
    have key : ∀ L : List Ev, (∀ x ∈ L, Valid D B T ev x) →
        (((L.map (ccl B 0)).sum : ℕ) : ℝ) ≤ (L.map (cov D B (fun _ => (1:ℝ)))).sum := by
      intro L hL
      induction L with
      | nil => simp
      | cons x L ih =>
        simp only [List.map_cons, List.sum_cons, Nat.cast_add]
        have h1 := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
        have h2 : ((ccl B 0 x : ℕ) : ℝ) ≤ cov D B (fun _ => (1:ℝ)) x := by
          have hx := hL x (List.mem_cons_self)
          cases x with
          | good a e k =>
            obtain ⟨-, -, -, -, hae⟩ := hx
            simp only [ccl, cov, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
            split_ifs <;> simp [Nat.cast_sub hae.le, hae.le]
          | bad a k =>
            simp only [ccl, cov, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
            split_ifs <;> simp
        linarith
    have := key _ hval
    rw [← hpart1] at this
    simpa using this
  -- class i+1 has total length ≤ B i · H_i
  have hTi : ∀ i ∈ Finset.range D,
      wt B α β (i+1) * (((walk D B T ev 0 0).map (ccl B (i+1))).sum : ℝ) ≤
      wt B α β (i+1) * (B i * (((walk D B T ev 0 0).map (nb i)).sum : ℝ)) := by
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hw _)
    have h1 : ((walk D B T ev 0 0).map (ccl B (i+1))).sum ≤
        ((walk D B T ev 0 0).map (slen D B i)).sum :=
      List.sum_le_sum (fun x _ => ccl_le_slen (D := D) i x)
    have h2 := slen_le h i (Finset.mem_range.1 hi) 0 0 (Nat.zero_le _) (dvd_zero _)
    simp only [Nat.not_lt_zero, ite_false, add_zero] at h2
    exact_mod_cast h1.trans h2
  rw [Finset.range_eq_Ico, hpart]
  refine (hlist _ hval).trans ?_
  rw [Finset.sum_range_succ']
  have h0 := mul_le_mul_of_nonneg_left hT0 (hw 0)
  have := Finset.sum_le_sum hTi
  linarith

/-- `HypI` is weaker than P0049's `Hyp`: every restart-without-inheritance instance is an
instance with inheritance (in which no interval crosses its parent epoch). -/
theorem HypI.of_hyp (h : Pool.P0049.Hyp D B T ev) : HypI D B T ev where
  pos := h.pos
  chain := h.chain
  T_dvd := h.T_dvd
  ev_ge := h.ev_ge
  ev_dvd := h.ev_dvd
  ev_leT := fun j a e hj hd ha he => Pool.P0049.e_le_T h hj ha hd he
  ev_cross := by
    intro j a e i hj hd ha he hij hlt
    exfalso
    have := Pool.P0049.e_le_nxt h hj ha hd he hij
    omega

/-- **Dyadic corollary.** With halving epoch lengths `B i = 2 B (i+1)` and at most `h` visited
bad epochs per thread, the total cost is at most
`α T/√(B 0) + β T/B 0 + 2 D h (α √(B 0) + β) + c h`. With `B 0 = T/n` and `h = Õ(n)` this is
`Õ(α √(nT) + β n)` (PR23, Lemmas 4.18 and 4.21). -/
theorem sum_le_walkI_dyadic (h : HypI D B T ev) (hdy : ∀ i < D, B i = 2 * B (i+1)) (r : ℕ → ℝ)
    {α β c hb : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hgood : ∀ a e k, k ≤ D → B k ∣ a → a < T → ev k a = some e →
      ∑ u ∈ Finset.Ico a e, r u ≤ α * Real.sqrt ((e - a : ℕ) : ℝ) + β)
    (hleaf : ∀ a, B D ∣ a → a < T → ev D a = none →
      ∑ u ∈ Finset.Ico a (a + B D), r u ≤ c)
    (hH : ∀ i ≤ D, (((walk D B T ev 0 0).map (nb i)).sum : ℝ) ≤ hb) :
    ∑ u ∈ Finset.range T, r u ≤
      α * T / Real.sqrt (B 0) + β * T / B 0 + 2 * D * hb * (α * Real.sqrt (B 0) + β) + c * hb := by
  have main := sum_le_walkI h r hα hβ hgood hleaf
  have hmono : ∀ i ≤ D, B i ≤ B 0 := by
    intro i; induction i with
    | zero => intro _; exact le_rfl
    | succ i ih => intro hi; have := hdy i (by omega); have := ih (by omega); omega
  have hterm : ∀ i ∈ Finset.range D,
      wt B α β (i+1) * (B i * (((walk D B T ev 0 0).map (nb i)).sum : ℝ)) ≤
        2 * hb * (α * Real.sqrt (B 0) + β) := by
    intro i hi
    have hpos : (0 : ℝ) < B (i+1) := by exact_mod_cast h.pos (i+1)
    have hiD : i < D := Finset.mem_range.1 hi
    have hBi : (B i : ℝ) = 2 * B (i+1) := by exact_mod_cast hdy i hiD
    have hsq : Real.sqrt (B (i+1)) * Real.sqrt (B (i+1)) = B (i+1) :=
      Real.mul_self_sqrt hpos.le
    have hspos : 0 < Real.sqrt (B (i+1)) := Real.sqrt_pos.2 hpos
    have hw : wt B α β (i+1) * B i = 2 * (α * Real.sqrt (B (i+1)) + β) := by
      unfold wt; rw [hBi]; field_simp; nlinarith [hsq]
    have hs0 : Real.sqrt (B (i+1)) ≤ Real.sqrt (B 0) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hmono (i+1) (by omega))
    have hnb := hH i (by have := Finset.mem_range.1 hi; omega)
    have hnb0 : (0:ℝ) ≤ (((walk D B T ev 0 0).map (nb i)).sum : ℝ) := Nat.cast_nonneg _
    calc wt B α β (i+1) * (B i * (((walk D B T ev 0 0).map (nb i)).sum : ℝ))
        = 2 * (α * Real.sqrt (B (i+1)) + β) * (((walk D B T ev 0 0).map (nb i)).sum : ℝ) := by
          rw [← mul_assoc, hw]
      _ ≤ 2 * (α * Real.sqrt (B 0) + β) * hb := by
          apply mul_le_mul _ hnb hnb0 (by positivity)
          nlinarith
      _ = 2 * hb * (α * Real.sqrt (B 0) + β) := by ring
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hD := hH D le_rfl
  have hcD : c * (((walk D B T ev 0 0).map (nb D)).sum : ℝ) ≤ c * hb :=
    mul_le_mul_of_nonneg_left hD hc
  have h0 : wt B α β 0 * T = α * T / Real.sqrt (B 0) + β * T / B 0 := by
    unfold wt; ring
  rw [h0] at main
  nlinarith

end Pool.P0056
