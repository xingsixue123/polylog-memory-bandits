import Pool.Prelude
/-!
# The Peng–Rubinstein bad-epoch walk (deterministic part)

Abstract, deterministic version of the walk of Peng–Rubinstein (arXiv:2303.01673, §4.2.2,
Algorithm 12, Lemma 4.18, and the assembly in the proof of Lemma 4.21), for any number of nested
threads. Nothing here is probabilistic, and nothing refers to a particular algorithm.

**Setting.**
- Threads `0, …, D` (thread `0` is the coarsest), with epoch lengths `B 0, …, B D`, all positive and
  nested: `B (k+1) ∣ B k`; the horizon `T` is a multiple of `B 0`. An epoch of thread `k` is
  `[a, a + B k)` with `B k ∣ a`.
- Eviction data `ev k a : Option ℕ` for every thread `k` and epoch start `a`:
  - `ev k a = some e`: the (analysis) copy of the comparator that enters thread `k` at epoch `a` is
    covered at the end of round `e - 1`. We then call `[a, e)` a *good interval*. It is required
    (`Hyp`) that `e ≥ a + B k`, that `B k ∣ e` (covers happen at epoch ends of the thread), and that
    `e` does not exceed the end of the enclosing thread-`(k-1)` epoch (threads restart every
    `B (k-1)` rounds), resp. `e ≤ T` for thread `0`.
    This is a **restart-without-inheritance** model: a good interval never crosses the end of its
    parent epoch. It is not Peng–Rubinstein's inheritance walk, where a copy surviving a restart moves
    to a coarser thread and can be covered later; such data must be encoded as `none` here.
  - `ev k a = none`: the copy is never covered (a *bad epoch* of thread `k`).

**The walk** (`walk`) starts at round `0` at thread `0`. At an epoch start `s` of thread `j`:
- if `ev j s = some e`, it emits the good interval `[s, e)` and continues at round `e`;
- if `ev j s = none` and `j < D`, it records the bad epoch and descends to thread `j + 1`, same round;
- if `ev j s = none` and `j = D`, it emits the bad deepest epoch `[s, s + B D)` and continues at
  `s + B D`.
It continues at the coarsest thread at which the new round is an epoch start (`rise`).

**Main results.**
- `sum_Ico_eq_walk`: the good intervals and the bad deepest epochs partition `[s, T)`.
- `len_succ_le`: the good thread-`(i+1)` intervals (and, for `i + 1 = D`, the bad deepest epochs) have
  total length at most `B i · H_i`, where `H_i` is the number of bad thread-`i` epochs visited by
  the walk (PR23 Lemma 4.18(ii)). `len0_le`: thread `0` has total length at most `T`.
- `nb_le_card`: `H_i` is at most the number of all bad thread-`i` epochs in `[0, T)`.
- `sum_le_walk`: if every good interval `[a, e)` costs at most `α √(e - a) + β` and every bad deepest
  epoch at most `c`, the total cost over `[0, T)` is at most
  `wt 0 · T + Σ_{i<D} wt (i+1) · B i · H_i + c · H_D`, with `wt k = α/√(B k) + β/(B k)`.
- `sum_le_walk_dyadic`: with `B i = 2 B (i+1)` for `i < D` and `H_i ≤ h`, the total is at most
  `α T/√(B 0) + β T/(B 0) + 2 D h (α √(B 0) + β) + c h`.
- The case `D = 0` is the one-level walk: total ≤ `(α/√B + β/B) T + c · H_0`.
-/

namespace Pool.P0049

/-- Output events of the walk: a good interval `[a, e)` of thread `j`, or a bad epoch `(a, j)`
(a descent if `j < D`, a bad deepest epoch `[a, a + B D)` if `j = D`). -/
inductive Ev where
  | good (a e j : ℕ)
  | bad (a j : ℕ)
  deriving DecidableEq

variable (D : ℕ) (B : ℕ → ℕ) (T : ℕ) (ev : ℕ → ℕ → Option ℕ)

/-- coarsest thread (index ≤ D) at which `u` is an epoch start; `D` by default. -/
noncomputable def rise (u : ℕ) : ℕ :=
  Nat.find (⟨D, Or.inl le_rfl⟩ : ∃ j, D ≤ j ∨ B j ∣ u)

/-- The walk from round `s` at thread `j` (see the module docstring). The guards `s < e` and
`0 < B D` only ensure termination; under `Hyp` they always hold. -/
noncomputable def walk (s j : ℕ) : List Ev :=
  if _hs : s < T then
    match _h : ev j s with
    | some e => if _hse : s < e then Ev.good s e j :: walk e (rise D B e) else []
    | none =>
      if hj : j < D then Ev.bad s j :: walk s (j+1)
      else if _hb : 0 < B D then Ev.bad s D :: walk (s + B D) (rise D B (s + B D)) else []
  else []
termination_by (T - s, D - j)
decreasing_by
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-- Hypotheses on the epoch lengths and the eviction data. -/
structure Hyp : Prop where
  pos : ∀ j, 0 < B j
  chain : ∀ k, B (k+1) ∣ B k
  T_dvd : B 0 ∣ T
  ev_ge : ∀ j a e, j ≤ D → B j ∣ a → a < T → ev j a = some e → a + B j ≤ e
  ev_dvd : ∀ j a e, j ≤ D → B j ∣ a → a < T → ev j a = some e → B j ∣ e
  ev_le0 : ∀ a e, B 0 ∣ a → a < T → ev 0 a = some e → e ≤ T
  ev_le : ∀ j a e, j + 1 ≤ D → B (j+1) ∣ a → a < T → ev (j+1) a = some e →
    e ≤ (a / B j + 1) * B j

variable {D B T ev}

lemma dvd_of_le (h : Hyp D B T ev) {i k : ℕ} (hik : i ≤ k) : B k ∣ B i := by
  induction k, hik using Nat.le_induction with
  | base => exact dvd_rfl
  | succ k _ ih => exact (h.chain k).trans ih

lemma rise_le_D (u : ℕ) : rise D B u ≤ D := Nat.find_min' _ (Or.inl le_rfl)

lemma not_dvd_of_lt_rise {u i : ℕ} (hi : i < rise D B u) : ¬ B i ∣ u :=
  fun hd => Nat.find_min _ hi (Or.inr hd)

lemma rise_le_of_dvd {u j : ℕ} (hd : B j ∣ u) : rise D B u ≤ j := Nat.find_min' _ (Or.inr hd)

lemma dvd_rise (h : Hyp D B T ev) {u j : ℕ} (hj : j ≤ D) (hd : B j ∣ u) : B (rise D B u) ∣ u := by
  rcases Nat.find_spec (⟨D, Or.inl le_rfl⟩ : ∃ j, D ≤ j ∨ B j ∣ u) with h1 | h1
  · have : rise D B u = D := le_antisymm (rise_le_D u) h1
    rw [this]; exact (dvd_of_le h hj).trans hd
  · exact h1

lemma dvd_of_rise_le (h : Hyp D B T ev) {u i j : ℕ} (hj : j ≤ D) (hd : B j ∣ u)
    (hi : rise D B u ≤ i) : B i ∣ u :=
  (dvd_of_le h hi).trans (dvd_rise h hj hd)

/-- the end of the thread-`i` epoch containing `s`. -/
def nxt (i s : ℕ) : ℕ := (s / B i + 1) * B i

lemma lt_nxt (h : Hyp D B T ev) (i s : ℕ) : s < nxt (B := B) i s := by
  unfold nxt
  have := h.pos i
  have := Nat.lt_div_mul_add (a := s) this
  nlinarith [Nat.div_add_mod s (B i), Nat.mod_lt s (h.pos i)]

lemma nxt_le_of_dvd (h : Hyp D B T ev) {i s m : ℕ} (hd : B i ∣ m) (hs : s < m) :
    nxt (B := B) i s ≤ m := by
  unfold nxt
  obtain ⟨c, rfl⟩ := hd
  have hp := h.pos i
  have : s / B i < c := by
    rw [Nat.div_lt_iff_lt_mul hp]; linarith [mul_comm (B i) c]
  nlinarith

lemma nxt_mono (h : Hyp D B T ev) {i k : ℕ} (hik : i ≤ k) (s : ℕ) :
    nxt (B := B) k s ≤ nxt (B := B) i s := by
  apply nxt_le_of_dvd h
  · exact Dvd.dvd.mul_left (dvd_of_le h hik) _
  · exact lt_nxt h i s

lemma nxt_le_T (h : Hyp D B T ev) {i s : ℕ} (hs : s < T) : nxt (B := B) i s ≤ T :=
  nxt_le_of_dvd h ((dvd_of_le h (Nat.zero_le i)).trans h.T_dvd) hs

section eqns
variable {s j e : ℕ}

lemma walk_good (hs : s < T) (he : ev j s = some e) (hse : s < e) :
    walk D B T ev s j = Ev.good s e j :: walk D B T ev e (rise D B e) := by
  rw [walk.eq_1, dite_eq_left hs]; split <;> simp_all

lemma walk_desc (hs : s < T) (he : ev j s = none) (hj : j < D) :
    walk D B T ev s j = Ev.bad s j :: walk D B T ev s (j+1) := by
  rw [walk.eq_1, dite_eq_left hs]; split <;> simp_all

lemma walk_leaf (hs : s < T) (he : ev j s = none) (hj : ¬ j < D) (hb : 0 < B D) :
    walk D B T ev s j = Ev.bad s D :: walk D B T ev (s + B D) (rise D B (s + B D)) := by
  rw [walk.eq_1, dite_eq_left hs]; split <;> simp_all

lemma walk_stop (hs : ¬ s < T) : walk D B T ev s j = [] := by
  rw [walk.eq_1, dite_eq_right hs]
end eqns

/-- the rounds covered by an event, weighted by `f` (descents cover nothing). -/
def cov (D : ℕ) (B : ℕ → ℕ) (f : ℕ → ℝ) : Ev → ℝ
  | Ev.good a e _ => ∑ u ∈ Finset.Ico a e, f u
  | Ev.bad a k => if k = D then ∑ u ∈ Finset.Ico a (a + B D), f u else 0

lemma nxt_of_dvd (h : Hyp D B T ev) {i s : ℕ} (hd : B i ∣ s) : nxt (B := B) i s = s + B i := by
  unfold nxt; obtain ⟨c, rfl⟩ := hd
  rw [Nat.mul_div_cancel_left _ (h.pos i)]; ring

lemma e_le_T (h : Hyp D B T ev) {s j e : ℕ} (hj : j ≤ D) (hs : s < T) (hd : B j ∣ s)
    (he : ev j s = some e) : e ≤ T := by
  rcases j with _ | j
  · exact h.ev_le0 s e hd hs he
  · exact (h.ev_le j s e hj hd hs he).trans (nxt_le_T h hs)

theorem sum_Ico_eq_walk (h : Hyp D B T ev) (f : ℕ → ℝ) :
    ∀ s j, j ≤ D → B j ∣ s →
      ∑ u ∈ Finset.Ico s T, f u = ((walk D B T ev s j).map (cov D B f)).sum := by
  intro s j
  induction s, j using walk.induct D B T ev with
  | case1 s j hs e he hse ih =>
    intro hj hd
    rw [walk_good hs he hse]
    have heT := e_le_T h hj hs hd he
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

/-- length contributed to thread `i`: good intervals of thread `i`, and the leaves if `i = D`. -/
def len (D : ℕ) (B : ℕ → ℕ) (i : ℕ) : Ev → ℕ
  | Ev.good a e j => if j = i then e - a else 0
  | Ev.bad _ k => if k = D ∧ i = D then B D else 0

/-- bad epochs of thread `i` visited by the walk. -/
def nb (i : ℕ) : Ev → ℕ
  | Ev.good _ _ _ => 0
  | Ev.bad _ k => if k = i then 1 else 0

lemma div_eq_of_lt_nxt (h : Hyp D B T ev) {i s e : ℕ} (hse : s ≤ e) (he : e < nxt (B := B) i s) :
    e / B i = s / B i := by
  unfold nxt at he
  apply le_antisymm
  · have : e / B i < s / B i + 1 := (Nat.div_lt_iff_lt_mul (h.pos i)).2 he
    omega
  · exact Nat.div_le_div_right hse

lemma e_le_nxt (h : Hyp D B T ev) {s j e i : ℕ} (hj : j ≤ D) (hs : s < T) (hd : B j ∣ s)
    (he : ev j s = some e) (hij : i < j) : e ≤ nxt (B := B) i s := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact (h.ev_le j s e hj hd hs he).trans (nxt_mono h (by omega) s)

/-- Main counting invariant: the length of thread `i+1` intervals in the walk from `(s, j)`
is at most `B i` times the number of visited bad thread-`i` epochs, plus the rest of the
current thread-`i` ancestor epoch when `i < j`. -/
theorem len_le (h : Hyp D B T ev) (i : ℕ) (hi : i < D) :
    ∀ s j, j ≤ D → B j ∣ s →
      ((walk D B T ev s j).map (len D B (i+1))).sum + (if i < j then s else 0) ≤
        B i * ((walk D B T ev s j).map (nb i)).sum + (if i < j then nxt (B := B) i s else 0) := by
  intro s j
  induction s, j using walk.induct D B T ev with
  | case1 s j hs e he hse ih =>
    intro hj hd
    rw [walk_good hs he hse]
    have hde := h.ev_dvd j s e hj hd hs he
    have hr := rise_le_of_dvd (D := D) hde
    have IH := ih (rise_le_D e) (dvd_rise h hj hde)
    simp only [List.map_cons, List.sum_cons, len, nb, zero_add]
    set L := ((walk D B T ev e (rise D B e)).map (len D B (i+1))).sum
    set N := ((walk D B T ev e (rise D B e)).map (nb i)).sum
    by_cases hY : i < rise D B e
    · have hij : i < j := lt_of_lt_of_le hY hr
      have hle := e_le_nxt h hj hs hd he hij
      have hne : e ≠ nxt (B := B) i s := by
        intro heq; apply not_dvd_of_lt_rise hY; rw [heq]; exact Dvd.intro_left _ rfl
      have hnx : nxt (B := B) i e = nxt (B := B) i s := by
        unfold nxt; rw [div_eq_of_lt_nxt h hse.le (lt_of_le_of_ne hle hne)]
      rw [ite_eq_left hY, ite_eq_left hY, hnx] at IH
      rw [ite_eq_left hij, ite_eq_left hij]
      split_ifs <;> omega
    · rw [ite_eq_right hY, ite_eq_right hY] at IH
      by_cases hji : j = i + 1
      · have hij : i < j := by omega
        have hle := e_le_nxt h hj hs hd he hij
        have hdi : B i ∣ e := dvd_of_rise_le h hj hde (by omega)
        have hge := nxt_le_of_dvd h hdi hse
        rw [ite_eq_left hji, ite_eq_left hij, ite_eq_left hij]
        omega
      · rw [ite_eq_right hji]
        split_ifs with hij
        · have := lt_nxt h i s; omega
        · omega
  | case2 s j hs e he hse =>
    intro hj hd
    have := h.ev_ge j s e hj hd hs he
    have := h.pos j
    omega
  | case3 s j hs he hjD ih =>
    intro hj hd
    rw [walk_desc hs he hjD]
    have IH := ih hjD ((h.chain j).trans hd)
    simp only [List.map_cons, List.sum_cons, len, nb]
    have hlen0 : (if j = D ∧ i + 1 = D then B D else 0) = 0 := by
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
    simp only [List.map_cons, List.sum_cons, len, nb]
    rw [ite_eq_right (by omega : D ≠ i), zero_add]
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
      split_ifs <;> omega
    · rw [ite_eq_right hY, ite_eq_right hY] at IH
      split_ifs with hc
      · have hdi : B i ∣ s + B D := dvd_of_rise_le h le_rfl hde (by omega)
        have hge := nxt_le_of_dvd h hdi hse
        omega
      · omega
  | case5 s j hs he hjD hb =>
    intro _ _; exact absurd (h.pos D) hb
  | case6 s j hs =>
    intro _ _
    rw [walk_stop hs]
    simp only [List.map_nil, List.sum_nil, mul_zero, zero_add]
    split_ifs
    · exact (lt_nxt h i s).le
    · exact le_rfl

/-- The events the walk can emit: good intervals `[a, e)` with `ev k a = some e`, bad epochs
`(a, k)` with `ev k a = none`, all at epoch starts `a < T` of threads `k ≤ D`. -/
def Valid (D : ℕ) (B : ℕ → ℕ) (T : ℕ) (ev : ℕ → ℕ → Option ℕ) : Ev → Prop
  | Ev.good a e k => k ≤ D ∧ B k ∣ a ∧ a < T ∧ ev k a = some e ∧ a < e
  | Ev.bad a k => k ≤ D ∧ B k ∣ a ∧ a < T ∧ ev k a = none

theorem valid_of_mem (h : Hyp D B T ev) :
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

/-- Per thread: the total length of thread-`0` intervals is at most `T`. -/
theorem len0_le (h : Hyp D B T ev) :
    ((walk D B T ev 0 0).map (len D B 0)).sum ≤ T := by
  have hpart := sum_Ico_eq_walk h (fun _ => (1 : ℝ)) 0 0 (Nat.zero_le _) (dvd_zero _)
  have hval := valid_of_mem h 0 0 (Nat.zero_le _) (dvd_zero _)
  have key : ∀ L : List Ev, (∀ x ∈ L, Valid D B T ev x) →
      (((L.map (len D B 0)).sum : ℕ) : ℝ) ≤ (L.map (cov D B (fun _ => (1:ℝ)))).sum := by
    intro L hL
    induction L with
    | nil => simp
    | cons x L ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      have h1 := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
      have h2 : ((len D B 0 x : ℕ) : ℝ) ≤ cov D B (fun _ => (1:ℝ)) x := by
        have hx := hL x (List.mem_cons_self)
        cases x with
        | good a e k =>
          obtain ⟨-, -, -, -, hae⟩ := hx
          simp only [len, cov, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
          split_ifs <;> simp [Nat.cast_sub hae.le, hae.le]
        | bad a k =>
          simp only [len, cov, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
          split_ifs <;> simp_all
      linarith
  have := key _ hval
  rw [← hpart] at this
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one, Nat.sub_zero] at this
  exact_mod_cast this

/-- Per thread: thread-`(i+1)` intervals have total length at most `B i` times the number of
visited bad thread-`i` epochs. -/
theorem len_succ_le (h : Hyp D B T ev) {i : ℕ} (hi : i < D) :
    ((walk D B T ev 0 0).map (len D B (i+1))).sum ≤ B i * ((walk D B T ev 0 0).map (nb i)).sum := by
  have := len_le h i hi 0 0 (Nat.zero_le _) (dvd_zero _)
  simpa using this

lemma sqrt_add_le (α β b x : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hb : 0 < b) (hx : b ≤ x) :
    α * Real.sqrt x + β ≤ (α / Real.sqrt b + β / b) * x := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsx : Real.sqrt b ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have h1 : α * Real.sqrt x ≤ α / Real.sqrt b * x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hsb]
    have : Real.sqrt x * Real.sqrt b ≤ x := by nlinarith [Real.sqrt_nonneg x]
    nlinarith
  have h2 : β ≤ β / b * x := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]; nlinarith
  rw [add_mul]; linarith

/-- weight of thread `k` in the final bound. -/
noncomputable def wt (B : ℕ → ℕ) (α β : ℝ) (k : ℕ) : ℝ :=
  α / Real.sqrt (B k) + β / (B k)

lemma wt_nonneg (B : ℕ → ℕ) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (k : ℕ) : 0 ≤ wt B α β k := by
  unfold wt; positivity

/-- **Walk cost bound.** If the cost of every good interval `[a, e)` (with `ev k a = some e`)
is at most `α √(e - a) + β`, and the cost of every bad deepest-thread epoch is at most `c`,
then the total cost over `[0, T)` is at most
`wt 0 · T + Σ_{i < D} wt (i+1) · B i · H_i + c · H_D`,
where `H_i` is the number of bad thread-`i` epochs visited by the walk. -/
theorem sum_le_walk (h : Hyp D B T ev) (r : ℕ → ℝ) {α β c : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
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
  -- pointwise bound
  have hpt : ∀ x, Valid D B T ev x →
      cov D B r x ≤ ∑ k ∈ Finset.range (D+1), wt B α β k * (len D B k x : ℝ) +
        c * (nb D x : ℝ) := by
    intro x hx
    cases x with
    | good a e k =>
      obtain ⟨hk, hd, ha, he, hae⟩ := hx
      have hsum : ∑ k' ∈ Finset.range (D+1), wt B α β k' * (len D B k' (Ev.good a e k) : ℝ) =
          wt B α β k * ((e - a : ℕ) : ℝ) := by
        simp only [len]
        rw [Finset.sum_eq_single k]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · intro hk'; exact absurd (Finset.mem_range.2 (by omega)) hk'
      rw [hsum]; simp only [cov, nb, Nat.cast_zero, mul_zero, add_zero]
      refine (hgood a e k hk hd ha he).trans ?_
      apply sqrt_add_le α β _ _ hα hβ (by exact_mod_cast h.pos k)
      have := h.ev_ge k a e hk hd ha he
      exact_mod_cast (by omega : B k ≤ e - a)
    | bad a k =>
      obtain ⟨hk, hd, ha, he⟩ := hx
      have hs0 : 0 ≤ ∑ k' ∈ Finset.range (D+1), wt B α β k' * (len D B k' (Ev.bad a k) : ℝ) :=
        Finset.sum_nonneg (fun k' _ => mul_nonneg (hw k') (Nat.cast_nonneg _))
      simp only [cov, nb]
      split_ifs with hkD
      · subst hkD; simp only [Nat.cast_one, mul_one]
        have := hleaf a hd ha he; linarith
      · simp only [Nat.cast_zero, mul_zero, add_zero]; exact hs0
  -- sum over the list
  have hlist : ∀ L : List Ev, (∀ x ∈ L, Valid D B T ev x) →
      (L.map (cov D B r)).sum ≤ ∑ k ∈ Finset.range (D+1),
        wt B α β k * (((L.map (len D B k)).sum : ℕ) : ℝ) + c * (((L.map (nb D)).sum : ℕ) : ℝ) := by
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
  rw [Finset.range_eq_Ico, hpart]
  refine (hlist _ hval).trans ?_
  rw [Finset.sum_range_succ']
  have h0 : wt B α β 0 * (((walk D B T ev 0 0).map (len D B 0)).sum : ℝ) ≤ wt B α β 0 * T :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast len0_le h) (hw 0)
  have hi : ∀ i ∈ Finset.range D,
      wt B α β (i+1) * (((walk D B T ev 0 0).map (len D B (i+1))).sum : ℝ) ≤
      wt B α β (i+1) * (B i * (((walk D B T ev 0 0).map (nb i)).sum : ℝ)) := by
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hw _)
    exact_mod_cast len_succ_le h (Finset.mem_range.1 hi)
  have := Finset.sum_le_sum hi
  linarith

/-- the start of a bad thread-`i` event. -/
def badStart (i : ℕ) : Ev → Option ℕ
  | Ev.good _ _ _ => none
  | Ev.bad a k => if k = i then some a else none

lemma sum_nb_eq (i : ℕ) (L : List Ev) : (L.map (nb i)).sum = (L.filterMap (badStart i)).length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    cases x with
    | good a e k => simp [nb, badStart, ih, List.filterMap_cons]
    | bad a k =>
      by_cases hk : k = i
      · simp [nb, badStart, hk, ih, add_comm]
      · simp [nb, badStart, hk, ih]

lemma start_ge_good (h : Hyp D B T ev) :
    ∀ s j, j ≤ D → B j ∣ s → ∀ x ∈ walk D B T ev s j, ∀ a e k, x = Ev.good a e k → s ≤ a := by
  intro s j
  induction s, j using walk.induct D B T ev with
  | case1 s j hs e he hse ih =>
    intro hj hd x hx a e' k hxe
    rw [walk_good hs he hse] at hx
    have hde := h.ev_dvd j s e hj hd hs he
    rcases List.mem_cons.1 hx with rfl | hx
    · cases hxe; exact le_rfl
    · have := ih (rise_le_D e) (dvd_rise h hj hde) x hx a e' k hxe; omega
  | case2 s j hs e he hse =>
    intro hj hd
    have := h.ev_ge j s e hj hd hs he
    have := h.pos j
    omega
  | case3 s j hs he hjD ih =>
    intro hj hd x hx a e' k hxe
    rw [walk_desc hs he hjD] at hx
    rcases List.mem_cons.1 hx with rfl | hx
    · cases hxe
    · exact ih hjD ((h.chain j).trans hd) x hx a e' k hxe
  | case4 s j hs he hjD hb ih =>
    intro hj hd x hx a e' k hxe
    have hjD' : j = D := by omega
    rw [walk_leaf hs he hjD hb] at hx
    rw [hjD'] at hd
    rcases List.mem_cons.1 hx with rfl | hx
    · cases hxe
    · have := ih (rise_le_D _) (dvd_rise h le_rfl (dvd_add hd dvd_rfl)) x hx a e' k hxe; omega
  | case5 s j hs he hjD hb =>
    intro _ _; exact absurd (h.pos D) hb
  | case6 s j hs =>
    intro _ _ x hx
    rw [walk_stop hs] at hx; simp at hx

/-- Bad starts of a fixed thread are strictly increasing along the walk; every bad start is
`> s`, or `= s` at a thread `≥ j`. -/
theorem badStart_sorted (h : Hyp D B T ev) (i : ℕ) :
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

/-- The number of visited bad thread-`i` epochs is at most the number of all bad
thread-`i` epochs in `[0, T)`. -/
theorem nb_le_card (h : Hyp D B T ev) (i : ℕ) :
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

/-- **Dyadic corollary.** With halving epoch lengths `B i = 2 B (i+1)` and at most `h` visited
bad epochs per thread, the total cost is at most
`α T/√(B 0) + β T/B 0 + 2 D h (α √(B 0) + β) + c h`. With `B 0 = T/n` and `h = Õ(n)` this is
`Õ(α √(nT) + β n)` (PR23, Lemmas 4.18 and 4.21). -/
theorem sum_le_walk_dyadic (h : Hyp D B T ev) (hdy : ∀ i < D, B i = 2 * B (i+1)) (r : ℕ → ℝ)
    {α β c hb : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hc : 0 ≤ c)
    (hgood : ∀ a e k, k ≤ D → B k ∣ a → a < T → ev k a = some e →
      ∑ u ∈ Finset.Ico a e, r u ≤ α * Real.sqrt ((e - a : ℕ) : ℝ) + β)
    (hleaf : ∀ a, B D ∣ a → a < T → ev D a = none →
      ∑ u ∈ Finset.Ico a (a + B D), r u ≤ c)
    (hH : ∀ i ≤ D, (((walk D B T ev 0 0).map (nb i)).sum : ℝ) ≤ hb) :
    ∑ u ∈ Finset.range T, r u ≤
      α * T / Real.sqrt (B 0) + β * T / B 0 + 2 * D * hb * (α * Real.sqrt (B 0) + β) + c * hb := by
  have main := sum_le_walk h r hα hβ hgood hleaf
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

end Pool.P0049
