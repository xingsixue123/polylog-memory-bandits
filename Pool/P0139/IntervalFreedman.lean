import Pool.P0115.FOFreed
import Pool.P0129.ProbeCost

/-!
# Interval-uniform Freedman bounds in P0092's coin model, and P0129's probing cost with its good event discharged

Coins `ω : Fin t → Z` are i.i.d. with law `ν` (P0092). An **error process** `D` (round `s` reads the coins of rounds
`0..s`) satisfies `Incr ν D c` if it is bounded above by `c`, conditionally centred, and has conditional second moment
`≤ c`. Typical instances (`incr_of_unbiased`): the error `Y − μ` of an unbiased estimate `Y ∈ [0, c]` of a predictable
mean `μ ∈ [0, 1]`, e.g. a constant-rate slot estimate `ℓ·1[slot]/x` (`c = 1/x`) or the estimate of a policy loss from
its own rounds of probability `q_B` (`c = 1/q_B`); and differences of two such errors (`incr_sub`).

* `gD D gate a b`: the increments on the rounds `s ∈ [a, b)` where a predictable `gate` is on.
* `wid c L len = 2√(c·len·L) + 2cL`: the tuned Freedman width (P0115's `tune_le`).
* **`interval_tail`** / **`interval_tail_neg`**: for `b ≤ T`, the gated sum over `[a, b)` is `≥ wid(b − a)` (resp.
  `≤ −wid(b − a)`, given `D ≥ −c`) with probability `≤ e^{−L}` (P0100's `freedman_coins`).
* **`Good D gate c L t ω`**: on every interval `[a, b)` with `b ≤ t`, `|gated sum| < wid(b − a)`. It is prefix-closed
  (**`good_prefix`**) and **`prob_not_good`**: it fails at the horizon with probability `≤ 2(T+1)²e^{−L}`
  (union bound over all intervals, both tails).
* `stt`, `span`: the first and last gated round, and the length of that span; **`abs_runSum_gS_lt`**: on the good
  event, the gated sum over all rounds `< t` is within `wid(span)` (the width of the item's own alive span, not of
  the horizon, and it stops growing after the gate turns off for good).
* **`probe_cost_freedman`**: for a P0129 probe at constant rate `x` that is evicted (rule (b′)/(b″), any reference)
  once its estimated alive gap reaches `Λf(span)`, with estimated gap = true alive gap + alive-gated error process,
  `E[probing cost] ≤ x·E[Λf(span_T) + wid(span_T) + 1] + x·T·2(T+1)²e^{−L}`. This discharges the good event that
  P0129's `probe_cost_le` takes as a hypothesis.

Not included: any concrete design, the identification of a design's estimates with the forms above, and certificates.
-/

open Finset Real

namespace Pool.P0139

open Pool.P0092

variable {Z : Type} [Fintype Z] (ν : PMF Z)

/-- The increments `D` restricted to the rounds `s ∈ [a, b)` on which the predictable gate is on. -/
noncomputable def gD (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool)
    (a b : ℕ) : (s : ℕ) → (Fin (s + 1) → Z) → ℝ :=
  fun s ω => if a ≤ s ∧ s < b ∧ gate s (Fin.init ω) = true then D s ω else 0

/-- The tuned Freedman width for range/variance proxy `c`, confidence `L` and length `len`. -/
noncomputable def wid (c L len : ℝ) : ℝ := 2 * Real.sqrt (c * len * L) + 2 * c * L

theorem wid_pos {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (len : ℝ) : 0 < wid c L len := by
  unfold wid; positivity

theorem wid_mono {c L : ℝ} (hc : 0 < c) (hL : 0 < L) {l₁ l₂ : ℝ} (h : l₁ ≤ l₂) :
    wid c L l₁ ≤ wid c L l₂ := by
  unfold wid
  have : Real.sqrt (c * l₁ * L) ≤ Real.sqrt (c * l₂ * L) :=
    Real.sqrt_le_sqrt (by have := mul_le_mul_of_nonneg_left h hc.le; nlinarith)
  linarith

/-- Hypotheses on the increments: bounded above by `c`, conditionally centred, conditional second moment `≤ c`. -/
structure Incr (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (c : ℝ) : Prop where
  up : ∀ s (ω : Fin s → Z) z, D s (Fin.snoc ω z) ≤ c
  mean : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * D s (Fin.snoc ω z) = 0
  var : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * D s (Fin.snoc ω z) ^ 2 ≤ c

omit [Fintype Z] in
theorem gD_snoc (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) (a b s : ℕ)
    (ω : Fin s → Z) (z : Z) :
    gD D gate a b s (Fin.snoc ω z) = if a ≤ s ∧ s < b ∧ gate s ω = true then D s (Fin.snoc ω z) else 0 := by
  simp only [gD, Fin.init_snoc]

/-- **Freedman on one interval.** For `b ≤ T`, `L > 0`, `c > 0`: the gated sum over `[a, b)` exceeds
`wid c L (b − a)` with probability `≤ e^{−L}`. -/
theorem interval_tail (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool)
    {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (hD : Incr ν D c) {a b T : ℕ} (hbT : b ≤ T) :
    probGe ν T (runSum (gD D gate a b) T) (wid c L ((b - a : ℕ) : ℝ)) ≤ Real.exp (-L) := by
  rcases Nat.eq_zero_or_pos (b - a) with h0 | hpos
  · -- empty interval: the sum is zero and the width positive
    have hz : ∀ ω : Fin T → Z, runSum (gD D gate a b) T ω = 0 := by
      have hz' : ∀ t (ω : Fin t → Z), runSum (gD D gate a b) t ω = 0 := by
        intro t
        induction t with
        | zero => intro ω; rfl
        | succ t ih =>
          intro ω
          simp only [runSum, ih, gD]
          rw [if_neg (by omega)]; ring
      exact fun ω => hz' T ω
    have : probGe ν T (runSum (gD D gate a b) T) (wid c L ((b - a : ℕ) : ℝ)) = 0 := by
      unfold probGe
      refine Finset.sum_eq_zero fun ω _ => ?_
      rw [hz ω, if_neg (not_le.mpr (wid_pos hc hL _))]; ring
    rw [this]; exact (Real.exp_pos _).le
  · have hlen : (0 : ℝ) < ((b - a : ℕ) : ℝ) := by exact_mod_cast hpos
    obtain ⟨hκ0, hκc, hκw⟩ := Pool.P0115.tune_le hc hlen hL
    set κ := min (1 / c) (Real.sqrt (L / (c * ((b - a : ℕ) : ℝ)))) with hκ
    have vD_def : (fun (s : ℕ) (_ : Fin s → Z) => (if a ≤ s ∧ s < b then c else 0)) =
        fun s _ => c * (if a ≤ s ∧ s < b then (1 : ℝ) else 0) := by
      funext s _; split_ifs <;> ring
    have hF := Pool.P0100.freedman_coins ν (gD D gate a b)
      (fun s _ => if a ≤ s ∧ s < b then c else 0) hκ0 (T := T)
      (fun s _ ω z _ _ => by
        rw [gD_snoc]
        split_ifs
        · calc κ * D s (Fin.snoc ω z) ≤ κ * c := mul_le_mul_of_nonneg_left (hD.up s ω z) hκ0.le
            _ ≤ 1 := by linarith [hκc]
        · simp)
      (fun s _ ω _ => by
        simp only [gD_snoc]
        split_ifs
        · rw [hD.mean s ω]
        · simp)
      (fun s _ ω _ => by
        simp only [gD_snoc]
        split_ifs with h1 h2
        · exact hD.var s ω
        · exact absurd ⟨h1.1, h1.2.1⟩ h2
        · simp; exact hc.le
        · simp) L
    have hV : ∀ ω : Fin T → Z, Pool.P0100.runV (fun s _ => if a ≤ s ∧ s < b then c else 0) T ω =
        c * ((b - a : ℕ) : ℝ) := by
      intro ω
      rw [Pool.P0115.runV_det (fun s => if a ≤ s ∧ s < b then c else 0) T ω,
        ← Pool.P0115.sum_range_ind (a := a) hbT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
    refine le_trans (probGe_mono ν (fun ω h => ?_)) hF
    rw [hV ω]
    have hw : κ * (c * ((b - a : ℕ) : ℝ)) + L / κ ≤ wid c L ((b - a : ℕ) : ℝ) := by
      unfold wid; linarith [hκw]
    linarith



omit [Fintype Z] in
theorem gD_neg (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) (a b : ℕ) :
    gD (fun s ω => -D s ω) gate a b = fun s ω => -gD D gate a b s ω := by
  funext s ω; unfold gD; split_ifs <;> simp

/-- The lower tail: if also `−c ≤ D`, the gated sum is `≤ −wid` with probability `≤ e^{−L}`. -/
theorem interval_tail_neg (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool)
    {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (hD : Incr ν D c)
    (hlow : ∀ s (ω : Fin s → Z) z, -c ≤ D s (Fin.snoc ω z)) {a b T : ℕ} (hbT : b ≤ T) :
    probGe ν T (fun ω => -runSum (gD D gate a b) T ω) (wid c L ((b - a : ℕ) : ℝ)) ≤ Real.exp (-L) := by
  have hD' : Incr ν (fun s ω => -D s ω) c :=
    { up := fun s ω z => by have := hlow s ω z; linarith
      mean := fun s ω => by
        simp only [mul_neg, Finset.sum_neg_distrib, hD.mean s ω, neg_zero]
      var := fun s ω => by simpa only [neg_sq] using hD.var s ω }
  have h := interval_tail ν (fun s ω => -D s ω) gate hc hL hD' (a := a) hbT
  rw [gD_neg] at h
  refine le_trans (le_of_eq ?_) h
  unfold probGe
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Pool.P0115.runSum_neg]

/-- **The good event at time `t`**: on every interval `[a, b)` with `b ≤ t`, the gated sum is within the width. -/
def Good (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) (c L : ℝ)
    (t : ℕ) (ω : Fin t → Z) : Prop :=
  ∀ a b, a ≤ b → b ≤ t → |runSum (gD D gate a b) t ω| < wid c L ((b - a : ℕ) : ℝ)

omit [Fintype Z] in
theorem runSum_gD_stable (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool)
    {a b t : ℕ} (hb : b ≤ t) (ω : Fin t → Z) (z : Z) :
    runSum (gD D gate a b) (t + 1) (Fin.snoc ω z) = runSum (gD D gate a b) t ω := by
  simp only [runSum, Fin.init_snoc, gD_snoc]
  rw [if_neg (by omega)]; ring

omit [Fintype Z] in
/-- The good events are prefix-closed. -/
theorem good_prefix (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) (c L : ℝ)
    (t : ℕ) (ω : Fin t → Z) (z : Z) (h : Good D gate c L (t + 1) (Fin.snoc ω z)) : Good D gate c L t ω := by
  intro a b hab hb
  have := h a b hab (by omega)
  rwa [runSum_gD_stable D gate hb] at this

open Classical in
/-- **Union bound**: the good event at the horizon fails with probability `≤ 2 (T+1)² e^{−L}`. -/
theorem prob_not_good (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool)
    {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (hD : Incr ν D c)
    (hlow : ∀ s (ω : Fin s → Z) z, -c ≤ D s (Fin.snoc ω z)) (T : ℕ) :
    (∑ ω : Fin T → Z, wgt ν ω * if Good D gate c L T ω then (0 : ℝ) else 1) ≤
      2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
  set I : Finset ((ℕ × ℕ) × Bool) :=
    (((Finset.range (T + 1)) ×ˢ (Finset.range (T + 1))).filter (fun p => p.1 ≤ p.2)) ×ˢ Finset.univ with hI
  let f : (ℕ × ℕ) × Bool → (Fin T → Z) → ℝ := fun i ω =>
    (if i.2 then runSum (gD D gate i.1.1 i.1.2) T ω else -runSum (gD D gate i.1.1 i.1.2) T ω) -
      wid c L ((i.1.2 - i.1.1 : ℕ) : ℝ)
  have hstep : (∑ ω : Fin T → Z, wgt ν ω * if Good D gate c L T ω then (0 : ℝ) else 1) ≤
      ∑ ω : Fin T → Z, wgt ν ω * if ∃ i ∈ I, (0 : ℝ) ≤ f i ω then 1 else 0 := by
    refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (wgt_nonneg ν ω)
    by_cases hg : Good D gate c L T ω
    · rw [if_pos hg]; split_ifs <;> norm_num
    by_cases hex : ∃ i ∈ I, (0 : ℝ) ≤ f i ω
    · rw [if_neg hg, if_pos hex]
    · exfalso
      apply hex
      simp only [Good, not_forall, not_lt] at hg
      obtain ⟨a, b, hab, hbT, hw⟩ := hg
      rcases le_abs'.mp hw with h1 | h1
      · refine ⟨((a, b), false), ?_, ?_⟩
        · simp only [hI, Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, and_true]
          omega
        · simp only [f, Bool.false_eq_true, ↓reduceIte]; linarith
      · refine ⟨((a, b), true), ?_, ?_⟩
        · simp only [hI, Finset.mem_product, Finset.mem_filter, Finset.mem_range, Finset.mem_univ, and_true]
          omega
        · simp only [f, ↓reduceIte]; linarith
  refine le_trans hstep (le_trans (probGe_exists_le ν I f 0) ?_)
  have hone : ∀ i ∈ I, probGe ν T (f i) 0 ≤ Real.exp (-L) := by
    intro i hi
    simp only [hI, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hi
    rcases i with ⟨⟨a, b⟩, sgn⟩
    have hbT : b ≤ T := by simp only at hi; omega
    cases sgn
    · refine le_trans (probGe_mono ν (fun ω h => ?_)) (interval_tail_neg ν D gate hc hL hD hlow (a := a) hbT)
      simp only [f, Bool.false_eq_true, ↓reduceIte] at h; linarith
    · refine le_trans (probGe_mono ν (fun ω h => ?_)) (interval_tail ν D gate hc hL hD (a := a) hbT)
      simp only [f, ↓reduceIte] at h; linarith
  calc ∑ i ∈ I, probGe ν T (f i) 0 ≤ ∑ _i ∈ I, Real.exp (-L) := Finset.sum_le_sum hone
    _ = (I.card : ℝ) * Real.exp (-L) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        have h1 : I.card ≤ (T + 1) * (T + 1) * 2 := by
          rw [hI, Finset.card_product]
          refine Nat.mul_le_mul ?_ (by simp)
          refine le_trans (Finset.card_filter_le _ _) ?_
          rw [Finset.card_product, Finset.card_range]
        have h2 : (I.card : ℝ) ≤ ((T + 1) * (T + 1) * 2 : ℕ) := by exact_mod_cast h1
        push_cast at h2; nlinarith

/-! ## The alive span: first and last gated round -/

/-- `(first gated round, last gated round + 1)` among the rounds `< t`, or `(0, 0)` if there is none. -/
def stt (gate : (s : ℕ) → (Fin s → Z) → Bool) : (t : ℕ) → (Fin t → Z) → ℕ × ℕ
  | 0, _ => (0, 0)
  | t + 1, ω =>
    if gate t (Fin.init ω) then
      (if (stt gate t (Fin.init ω)).2 = 0 then (t, t + 1) else ((stt gate t (Fin.init ω)).1, t + 1))
    else stt gate t (Fin.init ω)

/-- The same pair after round `t`, read on the coins of the rounds `< t` (the gate is predictable). -/
def sttN (gate : (s : ℕ) → (Fin s → Z) → Bool) (t : ℕ) (ω : Fin t → Z) : ℕ × ℕ :=
  if gate t ω then (if (stt gate t ω).2 = 0 then (t, t + 1) else ((stt gate t ω).1, t + 1)) else stt gate t ω

omit [Fintype Z] in
theorem stt_snoc (gate : (s : ℕ) → (Fin s → Z) → Bool) (t : ℕ) (ω : Fin t → Z) (z : Z) :
    stt gate (t + 1) (Fin.snoc ω z) = sttN gate t ω := by
  simp only [stt, sttN, Fin.init_snoc]

/-- Length of the span of the gated rounds `< t`. -/
def span (gate : (s : ℕ) → (Fin s → Z) → Bool) (t : ℕ) (ω : Fin t → Z) : ℕ :=
  (stt gate t ω).2 - (stt gate t ω).1

/-- The same after round `t` (predictable). -/
def spanN (gate : (s : ℕ) → (Fin s → Z) → Bool) (t : ℕ) (ω : Fin t → Z) : ℕ :=
  (sttN gate t ω).2 - (sttN gate t ω).1

omit [Fintype Z] in
theorem span_snoc (gate : (s : ℕ) → (Fin s → Z) → Bool) (t : ℕ) (ω : Fin t → Z) (z : Z) :
    span gate (t + 1) (Fin.snoc ω z) = spanN gate t ω := by
  simp only [span, spanN, stt_snoc]

omit [Fintype Z] in
theorem stt_inv (gate : (s : ℕ) → (Fin s → Z) → Bool) :
    ∀ t (ω : Fin t → Z), ((stt gate t ω).1 = 0 ∧ (stt gate t ω).2 = 0) ∨
      ((stt gate t ω).1 < (stt gate t ω).2 ∧ (stt gate t ω).2 ≤ t) := by
  intro t
  induction t with
  | zero => intro ω; left; simp [stt]
  | succ t ih =>
    intro ω
    have h := ih (Fin.init ω)
    simp only [stt]
    split_ifs with hg h0
    · right; simp
    · right; simp only; omega
    · rcases h with h | h
      · left; exact h
      · right; omega

omit [Fintype Z] in
theorem span_le_succ (gate : (s : ℕ) → (Fin s → Z) → Bool) (t : ℕ) (ω : Fin t → Z) (z : Z) :
    span gate t ω ≤ span gate (t + 1) (Fin.snoc ω z) := by
  have h := stt_inv gate t ω
  simp only [span, stt, Fin.init_snoc]
  by_cases hg : gate t ω = true
  · by_cases h0 : (stt gate t ω).2 = 0
    · simp only [hg, h0, ↓reduceIte]; omega
    · simp only [hg, h0, ↓reduceIte]; omega
  · simp only [hg, Bool.false_eq_true, ↓reduceIte]; omega

/-- The increments `D` on the gated rounds (no interval restriction). -/
noncomputable def gS (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) :
    (s : ℕ) → (Fin (s + 1) → Z) → ℝ :=
  fun s ω => if gate s (Fin.init ω) = true then D s ω else 0

omit [Fintype Z] in
/-- The gated sum equals the interval sum over any interval containing the gated span. -/
theorem runSum_gS_eq (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool) :
    ∀ t (ω : Fin t → Z) a b, ((stt gate t ω).2 = 0 ∨ (a ≤ (stt gate t ω).1 ∧ (stt gate t ω).2 ≤ b)) →
      runSum (gS D gate) t ω = runSum (gD D gate a b) t ω := by
  intro t
  induction t with
  | zero => intro ω a b _; rfl
  | succ t ih =>
    intro ω a b hab
    have hinv := stt_inv gate t (Fin.init ω)
    simp only [runSum]
    by_cases hg : gate t (Fin.init ω) = true
    · by_cases h0 : (stt gate t (Fin.init ω)).2 = 0
      · have hst : stt gate (t + 1) ω = (t, t + 1) := by simp only [stt, hg, h0, ↓reduceIte]
        rw [hst] at hab
        simp only at hab
        have hab' : a ≤ t ∧ t + 1 ≤ b := by omega
        rw [ih (Fin.init ω) a b (Or.inl h0)]
        congr 1
        simp only [gS, gD, hg, and_true, ↓reduceIte]
        rw [if_pos ⟨hab'.1, by omega⟩]
      · have hst : stt gate (t + 1) ω = ((stt gate t (Fin.init ω)).1, t + 1) := by
          simp only [stt, hg, h0, ↓reduceIte]
        rw [hst] at hab
        simp only at hab
        have hab' : a ≤ (stt gate t (Fin.init ω)).1 ∧ t + 1 ≤ b := by omega
        have hlt : (stt gate t (Fin.init ω)).1 < (stt gate t (Fin.init ω)).2 ∧
            (stt gate t (Fin.init ω)).2 ≤ t := by
          rcases hinv with h | h
          · exact absurd h.2 h0
          · exact h
        rw [ih (Fin.init ω) a b (Or.inr ⟨hab'.1, by omega⟩)]
        congr 1
        simp only [gS, gD, hg, and_true, ↓reduceIte]
        rw [if_pos ⟨by omega, by omega⟩]
    · have hst : stt gate (t + 1) ω = stt gate t (Fin.init ω) := by
        simp only [stt, hg, Bool.false_eq_true, ↓reduceIte]
      rw [hst] at hab
      rw [ih (Fin.init ω) a b hab]
      congr 1
      simp only [gS, gD, hg, Bool.false_eq_true, and_false, ↓reduceIte]

omit [Fintype Z] in
/-- On the good event, the gated sum is within the width of its own span. -/
theorem abs_runSum_gS_lt (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (gate : (s : ℕ) → (Fin s → Z) → Bool)
    {c L : ℝ} (t : ℕ) (ω : Fin t → Z) (hG : Good D gate c L t ω) :
    |runSum (gS D gate) t ω| < wid c L (span gate t ω : ℝ) := by
  have hinv := stt_inv gate t ω
  rw [runSum_gS_eq D gate t ω (stt gate t ω).1 (stt gate t ω).2 (by
    rcases hinv with h | h
    · left; exact h.2
    · right; exact ⟨le_rfl, le_rfl⟩)]
  exact hG _ _ (by rcases hinv with h | h <;> omega) (by rcases hinv with h | h <;> omega)

/-! ## Instances: unbiased estimators and differences -/

/-- An unbiased nonnegative estimate `Y ∈ [0, c]` of a predictable mean `μ ∈ [0, 1]` (with `c ≥ 1`): its error
`Y − μ` satisfies `Incr` with constant `c`, and `−c ≤ Y − μ`. -/
theorem incr_of_unbiased (Y : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) (μ : (s : ℕ) → (Fin s → Z) → ℝ) {c : ℝ}
    (hc : 1 ≤ c) (hY0 : ∀ s (ω : Fin s → Z) z, 0 ≤ Y s (Fin.snoc ω z))
    (hYc : ∀ s (ω : Fin s → Z) z, Y s (Fin.snoc ω z) ≤ c)
    (hmean : ∀ s (ω : Fin s → Z), ∑ z, (ν z).toReal * Y s (Fin.snoc ω z) = μ s ω)
    (hμ0 : ∀ s (ω : Fin s → Z), 0 ≤ μ s ω) (hμ1 : ∀ s (ω : Fin s → Z), μ s ω ≤ 1) :
    Incr ν (fun s ω => Y s ω - μ s (Fin.init ω)) c ∧
      ∀ s (ω : Fin s → Z) z, -c ≤ Y s (Fin.snoc ω z) - μ s ω := by
  have h1 := sum_toReal_one ν
  refine ⟨{ up := fun s ω z => ?_, mean := fun s ω => ?_, var := fun s ω => ?_ }, fun s ω z => ?_⟩
  · simp only [Fin.init_snoc]; linarith [hYc s ω z, hμ0 s ω]
  · simp only [Fin.init_snoc, mul_sub, Finset.sum_sub_distrib, hmean s ω, ← Finset.sum_mul, h1, one_mul,
      sub_self]
  · simp only [Fin.init_snoc]
    have hsq : ∀ z, (Y s (Fin.snoc ω z) - μ s ω) ^ 2 ≤ c * Y s (Fin.snoc ω z) - 2 * μ s ω * Y s (Fin.snoc ω z) +
        μ s ω ^ 2 := by
      intro z
      have := hY0 s ω z; have := hYc s ω z
      nlinarith
    calc ∑ z, (ν z).toReal * (Y s (Fin.snoc ω z) - μ s ω) ^ 2
        ≤ ∑ z, (ν z).toReal * (c * Y s (Fin.snoc ω z) - 2 * μ s ω * Y s (Fin.snoc ω z) + μ s ω ^ 2) :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hsq z) ENNReal.toReal_nonneg
      _ = c * μ s ω - 2 * μ s ω * μ s ω + μ s ω ^ 2 := by
          simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [← Finset.sum_mul, h1]
          have e1 : ∑ z, (ν z).toReal * (c * Y s (Fin.snoc ω z)) = c * μ s ω := by
            rw [show ∑ z, (ν z).toReal * (c * Y s (Fin.snoc ω z)) = c * ∑ z, (ν z).toReal * Y s (Fin.snoc ω z) by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring, hmean s ω]
          have e2 : ∑ z, (ν z).toReal * (2 * μ s ω * Y s (Fin.snoc ω z)) = 2 * μ s ω * μ s ω := by
            rw [show ∑ z, (ν z).toReal * (2 * μ s ω * Y s (Fin.snoc ω z)) =
                2 * μ s ω * ∑ z, (ν z).toReal * Y s (Fin.snoc ω z) by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun z _ => by ring, hmean s ω]
          rw [e1, e2]; ring
      _ ≤ c := by have := hμ0 s ω; have := hμ1 s ω; nlinarith
  · linarith [hY0 s ω z, hμ1 s ω, hc]

/-- The difference of two error processes (e.g. a probe's estimate error minus ALG's estimate error) satisfies
`Incr` with constant `2(c₁ + c₂)`, with the matching lower bound. -/
theorem incr_sub (D₁ D₂ : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) {c₁ c₂ : ℝ} (h₁ : Incr ν D₁ c₁) (h₂ : Incr ν D₂ c₂)
    (l₁ : ∀ s (ω : Fin s → Z) z, -c₁ ≤ D₁ s (Fin.snoc ω z)) (l₂ : ∀ s (ω : Fin s → Z) z, -c₂ ≤ D₂ s (Fin.snoc ω z))
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    Incr ν (fun s ω => D₁ s ω - D₂ s ω) (2 * (c₁ + c₂)) ∧
      ∀ s (ω : Fin s → Z) z, -(2 * (c₁ + c₂)) ≤ D₁ s (Fin.snoc ω z) - D₂ s (Fin.snoc ω z) := by
  refine ⟨{ up := fun s ω z => ?_, mean := fun s ω => ?_, var := fun s ω => ?_ }, fun s ω z => ?_⟩
  · linarith [h₁.up s ω z, l₂ s ω z]
  · simp only [mul_sub, Finset.sum_sub_distrib, h₁.mean s ω, h₂.mean s ω, sub_self]
  · calc ∑ z, (ν z).toReal * (D₁ s (Fin.snoc ω z) - D₂ s (Fin.snoc ω z)) ^ 2
        ≤ ∑ z, (ν z).toReal * (2 * D₁ s (Fin.snoc ω z) ^ 2 + 2 * D₂ s (Fin.snoc ω z) ^ 2) :=
          Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left
            (by nlinarith [sq_nonneg (D₁ s (Fin.snoc ω z) + D₂ s (Fin.snoc ω z))]) ENNReal.toReal_nonneg
      _ = 2 * ∑ z, (ν z).toReal * D₁ s (Fin.snoc ω z) ^ 2 + 2 * ∑ z, (ν z).toReal * D₂ s (Fin.snoc ω z) ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ ≤ 2 * (c₁ + c₂) := by linarith [h₁.var s ω, h₂.var s ω]
  · linarith [l₁ s ω z, h₂.up s ω z]

/-! ## The probing-cost bound of P0129 with its good event discharged -/

open Classical in
/-- **Probing cost with concentration.** A P0129 probe at constant rate `x`, evicted by rule (b′) with a threshold
`Λf(span)` that depends only on its alive span, whose estimated alive gap `est` is the true alive gap plus the alive-gated
sum of an error process `D` (`Incr` with constant `c`, `D ≥ −c`, e.g. `incr_sub` of a probe and an ALG estimate),
pays in expectation at most `x·E[Λf(span) + wid(span) + 1] + x·T·2(T+1)²e^{−L}`, where `span` is the probe's alive
span at the horizon and `wid(len) = 2√(c·len·L) + 2cL`. -/
theorem probe_cost_freedman (P : Pool.P0129.Probe Z) {x : ℝ} (hx : Pool.P0129.HasRate ν P x) (T : ℕ)
    (D : (s : ℕ) → (Fin (s + 1) → Z) → ℝ) {c L : ℝ} (hc : 0 < c) (hL : 0 < L) (hD : Incr ν D c)
    (hlow : ∀ s (ω : Fin s → Z) z, -c ≤ D s (Fin.snoc ω z))
    (Λf : ℕ → ℝ) (hΛm : Monotone Λf) (hΛ0 : ∀ k, 0 ≤ Λf k)
    (est : (t : ℕ) → (Fin (t + 1) → Z) → ℝ)
    (hest : ∀ t (ω : Fin (t + 1) → Z),
      est t ω = runSum (Pool.P0129.ag P) (t + 1) ω + runSum (gS D P.alive) (t + 1) ω)
    (hrule : ∀ t (ω : Fin t → Z) z, P.alive (t + 1) (Fin.snoc ω z) → P.alive t ω →
      est t (Fin.snoc ω z) < Λf (spanN P.alive t ω))
    (hfresh : ∀ t (ω : Fin t → Z) z, P.alive (t + 1) (Fin.snoc ω z) → ¬ P.alive t ω →
      runSum (Pool.P0129.ag P) t ω = 0)
    (hg : ∀ t (ω : Fin t → Z), |P.g t ω| ≤ 1) :
    Pool.P0129.expect ν T (runSum (Pool.P0129.pc P) T) ≤
      x * Pool.P0129.expect ν T (fun ω => Λf (span P.alive T ω) + wid c L (span P.alive T ω) + 1) +
        x * T * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) := by
  set G := Good D P.alive c L with hGdef
  set Ψ : (t : ℕ) → (Fin t → Z) → ℝ := fun t ω => Λf (span P.alive t ω) + wid c L (span P.alive t ω) with hΨdef
  have hΨnn : ∀ t (ω : Fin t → Z), 0 ≤ Ψ t ω := fun t ω => add_nonneg (hΛ0 _) (wid_pos hc hL _).le
  have halive := Pool.P0129.halive_of_rule P G Ψ est (fun t ω => Λf (spanN P.alive t ω))
    (fun t ω => wid c L (spanN P.alive t ω)) hrule hfresh
    (fun t ω z hG => by
      rw [hest]
      have h := abs_runSum_gS_lt D P.alive (t + 1) (Fin.snoc ω z) hG
      rw [span_snoc] at h
      linarith [(abs_lt.mp h).1])
    (fun t ω z => by simp only [hΨdef, span_snoc, le_refl]) hΨnn
  have hmain := Pool.P0129.probe_cost_le ν P hx T G Ψ (good_prefix D P.alive c L)
    (fun t ω z => by
      have hs := span_le_succ P.alive t ω z
      exact add_le_add (hΛm hs) (wid_mono hc hL (by exact_mod_cast hs)))
    (fun ω => by linarith [hΨnn 0 ω]) halive hg
  refine le_trans hmain ?_
  have hx0 := Pool.P0129.HasRate.nonneg ν P hx
  have hbad := prob_not_good ν D P.alive hc hL hD hlow T
  have hsplit : Pool.P0129.expect ν T (fun ω => if G T ω then Ψ T ω + 1 else (T : ℝ)) ≤
      Pool.P0129.expect ν T (fun ω => Λf (span P.alive T ω) + wid c L (span P.alive T ω) + 1) +
        T * ∑ ω : Fin T → Z, wgt ν ω * if G T ω then (0 : ℝ) else 1 := by
    unfold Pool.P0129.expect
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    have hw := wgt_nonneg ν ω
    have hp := hΨnn T ω
    by_cases h : G T ω
    · simp only [h, ↓reduceIte, mul_zero, add_zero, hΨdef, le_refl]
    · simp only [h, ↓reduceIte, mul_one]
      have : 0 ≤ wgt ν ω * (Λf (span P.alive T ω) + wid c L (span P.alive T ω) + 1) :=
        mul_nonneg hw (by simp only [hΨdef] at hp; linarith)
      nlinarith
  calc x * Pool.P0129.expect ν T (fun ω => if G T ω then Ψ T ω + 1 else (T : ℝ))
      ≤ x * (Pool.P0129.expect ν T (fun ω => Λf (span P.alive T ω) + wid c L (span P.alive T ω) + 1) +
          T * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L))) := by
        refine mul_le_mul_of_nonneg_left (le_trans hsplit ?_) hx0
        have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
        nlinarith
    _ = _ := by ring

end Pool.P0139
