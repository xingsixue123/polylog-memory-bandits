import Pool.P0019.SleepingHedge
/-!
# Dyadic decompositions and the regret of sleeping-experts Hedge against a piecewise comparator

Deterministic (no probability, no model).

**Dyadic decomposition.** A *piece* `(a, l)` is the interval `[a, a + 2^l)`; it is *dyadic* (`Dy`)
if `2^l ∣ a`. `dec L u v` decomposes `[u, v)` (for `u ≤ v ≤ 2^L`) into dyadic pieces:
- `dec_sum`: `Σ_{t ∈ [u,v)} f t = Σ_{pieces} Σ_{t ∈ piece} f t` for every `f`, so the pieces partition `[u, v)`;
- `dec_dy`: every piece is dyadic and lies inside `[u, v)`;
- `dec_len`: there are at most `2L + 1` pieces.

**Regret through dyadic specialists.** Take P0019's specialists Hedge (`Pool.P0019.sprob`, priors `q`,
rate `η`, awake pattern `aw`, losses `c ≥ 0`), with expected loss `algLoss` and second moment `algVar`.
- `regret_interval_le`: for each piece `p` of `dec L u v`, suppose some specialist `spec p` is awake
  (among rounds `< T`) exactly on `p` and has the comparator's loss `g` there. Then
  `Σ_{[u,v)} (algLoss − g) ≤ (2L+1) Λ/η + (η/2) Σ_{[u,v)} algVar`, where `Λ ≥ log(Q/q(spec p))`.
- `regret_chain_le`: the same for consecutive pieces `[b k, b (k+1))`, `k < m` (for example the pieces of
  a covering chain, with `g` the loss of the current chain member). The bound is
  `m (2L+1) Λ/η + (η/2) Σ algVar`.

This is the per-interval regret input that P0022 §1 proposes in place of PR23's MonocarpicExpert.
(Informal remark about the intended application, not proved here: a learner using one specialist per
(arm, lifespan, dyadic interval) would have few specialists per lifespan awake at any time. No learner
is defined in this file.)

Note: `dec` is not the canonical (minimal) dyadic decomposition. For example `dec 4 0 16` has 8 pieces
although `[0,16)` is a single dyadic interval, and `dec 3 0 7` has 5 pieces instead of 3, because
`suf l 0` splits `[0, 2^l)` into pieces of sizes `1, 1, 2, …, 2^{l-1}`. Only `dec_sum`, `dec_dy` and
`dec_len` (at most `2L + 1` pieces) are claimed; nothing assumes minimality or one piece per level.
-/

namespace Pool.P0054

open Finset

/-- shift a dyadic piece `(a, l)` (the interval `[a, a + 2^l)`) by `m`. -/
def sh (m : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (p.1 + m, p.2)

/-- decomposition of `[0, v)` (for `v ≤ 2^l`) into dyadic pieces. -/
def pre : ℕ → ℕ → List (ℕ × ℕ)
  | 0, v => if v = 0 then [] else [(0, 0)]
  | l+1, v => if v < 2^l then pre l v else (0, l) :: (pre l (v - 2^l)).map (sh (2^l))

/-- decomposition of `[u, 2^l)` (for `u ≤ 2^l`) into dyadic pieces. -/
def suf : ℕ → ℕ → List (ℕ × ℕ)
  | 0, u => if u = 0 then [(0, 0)] else []
  | l+1, u => if 2^l ≤ u then (suf l (u - 2^l)).map (sh (2^l)) else suf l u ++ [(2^l, l)]

/-- decomposition of `[u, v)` (for `u ≤ v ≤ 2^L`) into dyadic pieces. -/
def dec : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, u, v => if u < v then [(0, 0)] else []
  | L+1, u, v =>
    if v ≤ 2^L then dec L u v
    else if 2^L ≤ u then (dec L (u - 2^L) (v - 2^L)).map (sh (2^L))
    else suf L u ++ (pre L (v - 2^L)).map (sh (2^L))

/-- the sum of `f` over the rounds of a piece. -/
def ps (f : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := ∑ t ∈ Ico p.1 (p.1 + 2^p.2), f t

lemma ps_sh (f : ℕ → ℝ) (m : ℕ) (p : ℕ × ℕ) : ps f (sh m p) = ps (fun t => f (t + m)) p := by
  unfold ps sh
  rw [show p.1 + m + 2^p.2 = (p.1 + 2^p.2) + m by ring, ← Finset.sum_Ico_add']

lemma sum_map_sh (f : ℕ → ℝ) (m : ℕ) (L : List (ℕ × ℕ)) :
    ((L.map (sh m)).map (ps f)).sum = (L.map (ps (fun t => f (t + m)))).sum := by
  induction L with
  | nil => simp
  | cons p L ih => simp only [List.map_cons, List.sum_cons, ps_sh, ih]

lemma sum_Ico_shift (f : ℕ → ℝ) (a b m : ℕ) :
    ∑ t ∈ Ico (a + m) (b + m), f t = ∑ t ∈ Ico a b, f (t + m) :=
  (Finset.sum_Ico_add' f a b m).symm

theorem pre_sum : ∀ l v, v ≤ 2^l → ∀ f : ℕ → ℝ,
    ∑ t ∈ Ico 0 v, f t = ((pre l v).map (ps f)).sum := by
  intro l
  induction l with
  | zero =>
    intro v hv f
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hv) with rfl | rfl
    · simp [pre]
    · simp [pre, ps]
  | succ l ih =>
    intro v hv f
    simp only [pre]
    split_ifs with h
    · exact ih v h.le f
    · rw [List.map_cons, List.sum_cons, sum_map_sh, ← ih (v - 2^l) (by rw [pow_succ] at hv; omega)]
      rw [← Finset.sum_Ico_consecutive f (Nat.zero_le (2^l)) (by omega : 2^l ≤ v)]
      simp only [ps, zero_add]
      congr 1
      rw [← sum_Ico_shift f 0 (v - 2^l) (2^l)]
      congr 1; ext; simp; omega

theorem suf_sum : ∀ l u, u ≤ 2^l → ∀ f : ℕ → ℝ,
    ∑ t ∈ Ico u (2^l), f t = ((suf l u).map (ps f)).sum := by
  intro l
  induction l with
  | zero =>
    intro u hu f
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (by simpa using hu) with rfl | rfl
    · simp [suf, ps]
    · simp [suf]
  | succ l ih =>
    intro u hu f
    simp only [suf]
    split_ifs with h
    · rw [sum_map_sh, ← ih (u - 2^l) (by rw [pow_succ] at hu; omega)]
      rw [← sum_Ico_shift f (u - 2^l) (2^l) (2^l)]
      congr 1; ext; simp [pow_succ]; omega
    · rw [List.map_append, List.sum_append, ← ih u (by omega)]
      rw [← Finset.sum_Ico_consecutive f (by omega : u ≤ 2^l) (by rw [pow_succ]; omega :
        2^l ≤ 2^(l+1))]
      simp [ps, pow_succ, mul_two]

theorem dec_sum : ∀ L u v, u ≤ v → v ≤ 2^L → ∀ f : ℕ → ℝ,
    ∑ t ∈ Ico u v, f t = ((dec L u v).map (ps f)).sum := by
  intro L
  induction L with
  | zero =>
    intro u v huv hv f
    simp only [dec]
    split_ifs with h
    · have : u = 0 := by simp at hv; omega
      have : v = 1 := by simp at hv; omega
      subst_vars; simp [ps]
    · rw [Finset.Ico_eq_empty (by omega)]; simp
  | succ L ih =>
    intro u v huv hv f
    simp only [dec]
    split_ifs with h1 h2
    · exact ih u v huv h1 f
    · rw [sum_map_sh, ← ih (u - 2^L) (v - 2^L) (by omega) (by rw [pow_succ] at hv; omega)]
      rw [← sum_Ico_shift f (u - 2^L) (v - 2^L) (2^L)]
      congr 1; ext; simp; omega
    · rw [List.map_append, List.sum_append, ← suf_sum L u (by omega), sum_map_sh,
        ← pre_sum L (v - 2^L) (by rw [pow_succ] at hv; omega)]
      rw [← Finset.sum_Ico_consecutive f (by omega : u ≤ 2^L) (by omega : 2^L ≤ v)]
      congr 1
      rw [← sum_Ico_shift f 0 (v - 2^L) (2^L)]
      congr 1; ext; simp; omega

theorem pre_len : ∀ l v, (pre l v).length ≤ l + 1 := by
  intro l; induction l with
  | zero => intro v; simp only [pre]; split_ifs <;> simp
  | succ l ih => intro v; simp only [pre]; split_ifs
                 · exact (ih v).trans (by omega)
                 · simp only [List.length_cons, List.length_map]; have := ih (v - 2^l); omega

theorem suf_len : ∀ l u, (suf l u).length ≤ l + 1 := by
  intro l; induction l with
  | zero => intro u; simp only [suf]; split_ifs <;> simp
  | succ l ih => intro u; simp only [suf]; split_ifs
                 · simp only [List.length_map]; exact (ih _).trans (by omega)
                 · simp only [List.length_append, List.length_singleton]; have := ih u; omega

theorem dec_len : ∀ L u v, (dec L u v).length ≤ 2 * L + 1 := by
  intro L; induction L with
  | zero => intro u v; simp only [dec]; split_ifs <;> simp
  | succ L ih => intro u v; simp only [dec]; split_ifs
                 · exact (ih u v).trans (by omega)
                 · simp only [List.length_map]; exact (ih _ _).trans (by omega)
                 · simp only [List.length_append, List.length_map]
                   have := suf_len L u; have := pre_len L (v - 2^L); omega

/-- A piece `(a, l)` is dyadic: `2^l ∣ a`. -/
def Dy (p : ℕ × ℕ) : Prop := 2 ^ p.2 ∣ p.1

lemma dy_sh {m : ℕ} {p : ℕ × ℕ} (hp : Dy p) (hm : 2 ^ p.2 ∣ m) : Dy (sh m p) :=
  dvd_add hp hm

theorem pre_dy : ∀ l v, ∀ p ∈ pre l v, Dy p ∧ p.2 ≤ l ∧ p.1 + 2^p.2 ≤ v := by
  intro l; induction l with
  | zero =>
    intro v p hp; simp only [pre] at hp
    split_ifs at hp with h
    · simp at hp
    · simp at hp; subst hp; simp [Dy]; omega
  | succ l ih =>
    intro v p hp; simp only [pre] at hp
    split_ifs at hp with h
    · obtain ⟨h1, h2, h3⟩ := ih v p hp; exact ⟨h1, by omega, h3⟩
    · rcases List.mem_cons.1 hp with rfl | hp
      · refine ⟨by simp [Dy], by simp, by simp; omega⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨h1, h2, h3⟩ := ih _ q hq
        refine ⟨dy_sh h1 (pow_dvd_pow 2 h2), h2.trans (by omega), ?_⟩
        simp only [sh]; omega

theorem suf_dy : ∀ l u, ∀ p ∈ suf l u, Dy p ∧ p.2 ≤ l ∧ u ≤ p.1 ∧ p.1 + 2^p.2 ≤ 2^l := by
  intro l; induction l with
  | zero =>
    intro u p hp; simp only [suf] at hp
    split_ifs at hp with h
    · simp at hp; subst hp; subst h; simp [Dy]
    · simp at hp
  | succ l ih =>
    intro u p hp; simp only [suf] at hp
    split_ifs at hp with h
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      obtain ⟨h1, h2, h3, h4⟩ := ih _ q hq
      refine ⟨dy_sh h1 (pow_dvd_pow 2 h2), h2.trans (by omega), ?_, ?_⟩
      · simp only [sh]; omega
      · simp only [sh, pow_succ]; omega
    · rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨h1, h2, h3, h4⟩ := ih u p hp
        exact ⟨h1, by omega, h3, h4.trans (by rw [pow_succ]; omega)⟩
      · simp at hp; subst hp
        refine ⟨by simp [Dy], by simp, by simp; omega, by simp [pow_succ]; omega⟩

/-- The pieces of `dec L u v` are dyadic intervals inside `[u, v)`. -/
theorem dec_dy : ∀ L u v, v ≤ 2^L → ∀ p ∈ dec L u v, Dy p ∧ u ≤ p.1 ∧ p.1 + 2^p.2 ≤ v := by
  intro L; induction L with
  | zero =>
    intro u v hv p hp; simp only [dec] at hp
    split_ifs at hp with h
    · simp at hp; subst hp; simp [Dy]; simp at hv; omega
    · simp at hp
  | succ L ih =>
    intro u v hv p hp; simp only [dec] at hp
    split_ifs at hp with h1 h2
    · exact ih u v h1 p hp
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      obtain ⟨d1, d2, d3⟩ := ih _ _ (by rw [pow_succ] at hv; omega) q hq
      have hl : q.2 ≤ L := by
        by_contra hc
        have : 2^(L+1) ≤ 2^q.2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at hv this; omega
      refine ⟨dy_sh d1 (pow_dvd_pow 2 hl), ?_, ?_⟩ <;> simp only [sh] <;> omega
    · rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨d1, d2, d3, d4⟩ := suf_dy L u p hp
        exact ⟨d1, d3, by omega⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨d1, d2, d3⟩ := pre_dy L _ q hq
        refine ⟨dy_sh d1 (pow_dvd_pow 2 d2), ?_, ?_⟩ <;> simp only [sh] <;> omega

section regret
open Pool.P0019 Real
variable {ι : Type*} [Fintype ι] {q : ι → ℝ} {η : ℝ} {aw : ℕ → ι → Bool} {c : ℕ → ι → ℝ}

/-- the expected loss of the specialists Hedge at round `t`. -/
noncomputable def algLoss (q : ι → ℝ) (η : ℝ) (aw : ℕ → ι → Bool) (c : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  ∑ j, sprob q η aw c t j * c t j

/-- its second moment at round `t`. -/
noncomputable def algVar (q : ι → ℝ) (η : ℝ) (aw : ℕ → ι → Bool) (c : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  ∑ j, sprob q η aw c t j * c t j ^ 2

lemma sum_range_ite_eq (T a b : ℕ) (hb : b ≤ T) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ t < T, P t ↔ a ≤ t ∧ t < b) (F : ℕ → ℝ) :
    ∑ t ∈ range T, (if P t then F t else 0) = ∑ t ∈ Ico a b, F t := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext t; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩; exact (hP t h1).1 h2
  · rintro ⟨h1, h2⟩; exact ⟨by omega, (hP t (by omega)).2 ⟨h1, h2⟩⟩

/-- **Regret against a comparator on an interval, through dyadic specialists.**
Suppose that for each dyadic piece `p` of `dec L u v` there is a specialist `spec p`, awake (among
rounds `< T`) exactly on the piece, whose loss equals the comparator's loss `g` there. Then on
`[u, v)` the specialists Hedge loses at most `(2L+1) Λ / η + (η/2) Σ_{[u,v)} algVar` more than the
comparator, where `Λ` bounds `log (Q / q (spec p))`. -/
theorem regret_interval_le (hq : ∀ i, 0 < q i) (hη : 0 < η) (hc : ∀ t i, 0 ≤ c t i)
    (T L u v : ℕ) (huv : u ≤ v) (hv : v ≤ 2^L) (hvT : v ≤ T)
    (spec : ℕ × ℕ → ι) (g : ℕ → ℝ)
    (haw : ∀ p ∈ dec L u v, ∀ t < T, aw t (spec p) = true ↔ p.1 ≤ t ∧ t < p.1 + 2^p.2)
    (hg : ∀ p ∈ dec L u v, ∀ t, p.1 ≤ t → t < p.1 + 2^p.2 → c t (spec p) = g t)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ p ∈ dec L u v, log ((∑ j, q j) / q (spec p)) ≤ Λ) :
    ∑ t ∈ Ico u v, (algLoss q η aw c t - g t) ≤
      (2 * L + 1) * Λ / η + η / 2 * ∑ t ∈ Ico u v, algVar q η aw c t := by
  rw [dec_sum L u v huv hv, dec_sum L u v huv hv]
  have hpiece : ∀ p ∈ dec L u v,
      ps (fun t => algLoss q η aw c t - g t) p ≤ Λ / η + η / 2 * ps (algVar q η aw c) p := by
    intro p hp
    obtain ⟨-, -, hpv⟩ := dec_dy L u v hv p hp
    have hreg := sleeping_hedge_regret (aw := aw) hq hη hc T (spec p)
    rw [sum_range_ite_eq T p.1 (p.1 + 2^p.2) (by omega) (fun t => aw t (spec p) = true)
        (haw p hp)] at hreg
    rw [sum_range_ite_eq T p.1 (p.1 + 2^p.2) (by omega) (fun t => aw t (spec p) = true)
        (haw p hp)] at hreg
    have hsame : ps (fun t => algLoss q η aw c t - g t) p =
        ∑ t ∈ Ico p.1 (p.1 + 2^p.2), (∑ j, sprob q η aw c t j * c t j - c t (spec p)) := by
      unfold ps algLoss
      apply Finset.sum_congr rfl
      intro t ht; rw [Finset.mem_Ico] at ht; rw [hg p hp t ht.1 ht.2]
    rw [hsame]
    have : log ((∑ j, q j) / q (spec p)) / η ≤ Λ / η :=
      div_le_div_of_nonneg_right (hΛ p hp) hη.le
    unfold ps algVar
    linarith
  have hsum : ∀ P : List (ℕ × ℕ), (∀ p ∈ P, p ∈ dec L u v) →
      (P.map (ps (fun t => algLoss q η aw c t - g t))).sum ≤
        P.length * (Λ / η) + η / 2 * (P.map (ps (algVar q η aw c))).sum := by
    intro P hP
    induction P with
    | nil => simp
    | cons p P ih =>
      have h1 := hpiece p (hP p List.mem_cons_self)
      have h2 := ih (fun x hx => hP x (List.mem_cons_of_mem _ hx))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      nlinarith
  refine (hsum _ (fun p hp => hp)).trans ?_
  have hlen : ((dec L u v).length : ℝ) ≤ 2 * L + 1 := by exact_mod_cast dec_len L u v
  have : ((dec L u v).length : ℝ) * (Λ / η) ≤ (2 * L + 1) * (Λ / η) :=
    mul_le_mul_of_nonneg_right hlen (div_nonneg hΛ0 hη.le)
  rw [mul_div_assoc]
  linarith

/-- **Chain version.** For consecutive pieces `[b k, b (k+1))`, `k < m`, each with its own
dyadic specialists `spec k` matching the comparator loss `g` (e.g. the loss of the `k`-th member
of a covering chain), the regret on `[b 0, b m)` is at most
`m (2L+1) Λ / η + (η/2) Σ_{[b 0, b m)} algVar`. -/
theorem regret_chain_le (hq : ∀ i, 0 < q i) (hη : 0 < η) (hc : ∀ t i, 0 ≤ c t i)
    (T L m : ℕ) (b : ℕ → ℕ) (hb : ∀ k < m, b k ≤ b (k+1)) (hbm : b m ≤ 2^L) (hbT : b m ≤ T)
    (spec : ℕ → ℕ × ℕ → ι) (g : ℕ → ℝ)
    (haw : ∀ k < m, ∀ p ∈ dec L (b k) (b (k+1)), ∀ t < T,
      aw t (spec k p) = true ↔ p.1 ≤ t ∧ t < p.1 + 2^p.2)
    (hg : ∀ k < m, ∀ p ∈ dec L (b k) (b (k+1)), ∀ t, p.1 ≤ t → t < p.1 + 2^p.2 →
      c t (spec k p) = g t)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ k < m, ∀ p ∈ dec L (b k) (b (k+1)), log ((∑ j, q j) / q (spec k p)) ≤ Λ) :
    ∑ t ∈ Ico (b 0) (b m), (algLoss q η aw c t - g t) ≤
      m * ((2 * L + 1) * Λ / η) + η / 2 * ∑ t ∈ Ico (b 0) (b m), algVar q η aw c t := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmono : ∀ j ≤ m, b 0 ≤ b j := by
      intro j hj
      induction j with
      | zero => exact le_rfl
      | succ j ihj => exact (ihj (by omega)).trans (hb j (by omega))
    have hbm' : b m ≤ b (m+1) := hb m (by omega)
    have h1 := ih (fun k hk => hb k (by omega)) (hbm'.trans hbm) (hbm'.trans hbT)
      (fun k hk => haw k (by omega)) (fun k hk => hg k (by omega)) (fun k hk => hΛ k (by omega))
    have h2 := regret_interval_le hq hη hc T L (b m) (b (m+1)) hbm' hbm hbT (spec m) g
      (haw m (by omega)) (hg m (by omega)) hΛ0 (hΛ m (by omega))
    have h0 : b 0 ≤ b m := hmono m le_rfl
    rw [← Finset.sum_Ico_consecutive _ h0 hbm', ← Finset.sum_Ico_consecutive _ h0 hbm']
    push_cast
    nlinarith

end regret

end Pool.P0054
