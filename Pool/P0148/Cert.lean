import Pool.P0138.VarHyp
import Pool.P0075.ChainHedge

/-!
# Record certificates for P0136's Design Z (its §3), deterministic given the concentration events

Three data streams on the copies: true losses `ℓ`, the exploitation learner's estimates `c` (IX, from its
own plays) and the slot estimates `d` (covers and rule (b″) read only `d`). `A` is the learner's
estimated (in-`c`) loss, `Atrue` its true policy loss.

* `cover_cert`: the comparator copy `j` is `Covered` at `t` (P0030, margin `θ`, chain length `≤ m`) by a
  chain of members on the slot data `cumL d`. Hypotheses (each one a concentration event or the learner's
  guarantee):
  for every member `f ∈ F` and every interval `[s, s')` with `E j ≤ s`, `E f ≤ s`, `s' ≤ t` (i.e. inside
  the comparator's record `[E j, t)`; the chain pieces are such intervals):
  - the learner is within `α + Σ V` (in `c`) of `f` (P0138's variance form);
  - IX one-sidedness `Σ c ≤ Σ ℓ + Γ`;
  - slot lower tail `Σ ℓ ≤ Σ d + W` (one constant `W`, at the scale of the record's length);
  - slot upper tail `Σ d j ≤ Σ ℓ j + W` for the comparator;
  - `Σ Atrue ≤ Σ A + Ψ`.
  Conclusion: `Σ_{[E j, t)} (Atrue − ℓ j) ≤ θ + m(α + Γ + W) + W + Ψ + Σ_{[E j,t)} V`.
* `bend_cert`: the comparator is evicted by (b″) against the base learner's estimated policy loss `B̂`.
  The learner contains the base meta-arm. Conclusion: `Σ (Atrue − ℓ j) ≤ Ψ + α + Σ V + Γ + W_D + W_B + W − Λ`.
* `cover_cert_hedge`: `cover_cert` for P0089's dyadic-specialist learner, with P0138's
  `hedge_interval_hyp_var` discharging the learner hypothesis.
-/

open Finset Real

namespace Pool.P0148

open Pool.P0030 Pool.P0061 Pool.P0075

variable {κ : Type*} [LinearOrder κ]

/-- Piecewise chain bound with three data streams. -/
theorem chain_est_le (E : κ → ℕ) (t a₀ : ℕ) (ℓ c d : ℕ → κ → ℝ) (A V : ℕ → ℝ) (α Γ W : ℝ)
    (Pres : κ → Prop)
    (hL : ∀ f, Pres f → ∀ s s', a₀ ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', c u f + α + ∑ u ∈ Ico s s', V u)
    (hIX : ∀ f, Pres f → ∀ s s', a₀ ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', c u f ≤ ∑ u ∈ Ico s s', ℓ u f + Γ)
    (hlo : ∀ f, Pres f → ∀ s s', a₀ ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', ℓ u f ≤ ∑ u ∈ Ico s s', d u f + W) :
    ∀ (ch : List κ) (a : ℕ), a₀ ≤ a → ChainOK E t ch a → (∀ f ∈ ch, Pres f) →
      ∑ u ∈ Ico a t, A u ≤ pieceSum E (cumL d) t ch a + ch.length * (α + Γ + W) +
        ∑ u ∈ Ico a t, V u := by
  have piece : ∀ (f : κ) (lo hi : ℕ), Pres f → a₀ ≤ lo → E f ≤ lo → lo ≤ hi → hi ≤ t →
      ∑ u ∈ Ico lo hi, A u ≤ ∑ u ∈ Ico lo hi, d u f + (α + Γ + W) + ∑ u ∈ Ico lo hi, V u := by
    intro f lo hi hP ha hf hlo' hhi
    have h1 := hL f hP lo hi ha hf hlo' hhi
    have h2 := hIX f hP lo hi ha hf hlo' hhi
    have h3 := hlo f hP lo hi ha hf hlo' hhi
    linarith
  intro ch
  induction ch with
  | nil => intro a _ h; exact h.elim
  | cons f rest ih =>
    intro a ha hok hpres
    cases rest with
    | nil =>
      obtain ⟨hfa, hat⟩ := hok
      simp only [pieceSum, List.length_singleton, Nat.cast_one, one_mul]
      rw [Lint_cumL d f hat]
      exact piece f a t (hpres f List.mem_cons_self) ha hfa hat le_rfl
    | cons g rest' =>
      obtain ⟨hfa, hag, hrest⟩ := hok
      have hgt := chainOK_le E t _ _ hrest
      have h1 := piece f a (E g) (hpres f List.mem_cons_self) ha hfa hag hgt
      have h2 := ih (E g) (ha.trans hag) hrest (fun x hx => hpres x (List.mem_cons_of_mem _ hx))
      simp only [pieceSum, List.length_cons, Nat.cast_add, Nat.cast_one] at h2 ⊢
      rw [Lint_cumL d f hag]
      rw [← Finset.sum_Ico_consecutive _ hag hgt, ← Finset.sum_Ico_consecutive _ hag hgt]
      nlinarith

/-- **Covered-record certificate (Design Z, §3).** -/
theorem cover_cert (E : κ → ℕ) (t : ℕ) (ℓ c d : ℕ → κ → ℝ) (A Atrue V : ℕ → ℝ)
    {F : Finset κ} {j : κ} {m : ℕ} {α Γ W Ψ θ : ℝ} (hα : 0 ≤ α) (hΓ : 0 ≤ Γ) (hW : 0 ≤ W) (Pres : κ → Prop)
    (hL : ∀ f, Pres f → ∀ s s', E j ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', c u f + α + ∑ u ∈ Ico s s', V u)
    (hIX : ∀ f, Pres f → ∀ s s', E j ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', c u f ≤ ∑ u ∈ Ico s s', ℓ u f + Γ)
    (hlo : ∀ f, Pres f → ∀ s s', E j ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', ℓ u f ≤ ∑ u ∈ Ico s s', d u f + W)
    (hFP : ∀ f ∈ F, Pres f)
    (hcov : Covered E (cumL d) t θ F j m)
    (hup : ∑ u ∈ Ico (E j) t, d u j ≤ ∑ u ∈ Ico (E j) t, ℓ u j + W)
    (htrue : ∑ u ∈ Ico (E j) t, Atrue u ≤ ∑ u ∈ Ico (E j) t, A u + Ψ) :
    ∑ u ∈ Ico (E j) t, (Atrue u - ℓ u j) ≤
      θ + m * (α + Γ + W) + W + Ψ + ∑ u ∈ Ico (E j) t, V u := by
  obtain ⟨ch, hlen, hmem, hok, hcv⟩ := hcov
  have hjt := chainOK_le E t ch (E j) hok
  have h := chain_est_le E t (E j) ℓ c d A V α Γ W Pres hL hIX hlo ch (E j) le_rfl hok
    (fun f hf => hFP f (hmem f hf))
  rw [Lint_cumL d j hjt] at hcv
  have hX : 0 ≤ α + Γ + W := by linarith
  have hl : (ch.length : ℝ) * (α + Γ + W) ≤ m * (α + Γ + W) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hX
  rw [Finset.sum_sub_distrib]
  linarith

/-- **(b″)-record certificate (Design Z, §3).** `fB` is the base meta-arm of the learner, present on
`[a, e)`; `cB` its IX data, `drawn` the realized losses of the arms drawn from the base policy when the
meta-arm is played, `bpol` the base policy loss `⟨b_u, ℓ_u⟩`, `Bhat` its estimate from base rounds, `Lhat`
the comparator's slot estimate. Rule (b″) fired at `e`: `Σ Lhat − Σ Bhat ≥ Λ`. -/
theorem bend_cert (a e : ℕ) (A Atrue V cB drawn bpol Bhat Lhat ℓj : ℕ → ℝ)
    {α Γ WD WB W Ψ Λ : ℝ}
    (hL : ∑ u ∈ Ico a e, A u ≤ ∑ u ∈ Ico a e, cB u + α + ∑ u ∈ Ico a e, V u)
    (hIX : ∑ u ∈ Ico a e, cB u ≤ ∑ u ∈ Ico a e, drawn u + Γ)
    (hD : ∑ u ∈ Ico a e, drawn u ≤ ∑ u ∈ Ico a e, bpol u + WD)
    (hB : ∑ u ∈ Ico a e, bpol u ≤ ∑ u ∈ Ico a e, Bhat u + WB)
    (hrule : Λ ≤ ∑ u ∈ Ico a e, Lhat u - ∑ u ∈ Ico a e, Bhat u)
    (hup : ∑ u ∈ Ico a e, Lhat u ≤ ∑ u ∈ Ico a e, ℓj u + W)
    (htrue : ∑ u ∈ Ico a e, Atrue u ≤ ∑ u ∈ Ico a e, A u + Ψ) :
    ∑ u ∈ Ico a e, (Atrue u - ℓj u) ≤ Ψ + α + ∑ u ∈ Ico a e, V u + Γ + WD + WB + W - Λ := by
  rw [Finset.sum_sub_distrib]
  linarith


section Hedge

open Pool.P0089 Pool.P0138

variable [Fintype κ] {L : ℕ}

/-- **Covered-record certificate for P0089's dyadic-specialist learner** on nonnegative (IX) data `c`:
P0138's `hedge_interval_hyp_var` discharges the learner hypothesis of `cover_cert`, with
`α = (2L+1)(log|Spec| + 2δT)/η` and the variance budget `(η/2)·palgVar`. -/
theorem cover_cert_hedge [Nonempty (Spec κ L)] (present : ℕ → κ → Prop) (E : κ → ℕ) (t T : ℕ)
    (hTL : T ≤ 2 ^ L) (ℓ c d : ℕ → κ → ℝ) (hc0 : ∀ u f, 0 ≤ c u f)
    {η : ℝ} (hη : 0 < η) {δ : ℝ} (hδ : 0 ≤ δ) (ρ : ℕ → ℝ) (hρ : ∀ u, |ρ u| ≤ δ)
    (Atrue : ℕ → ℝ) {Γ W Ψ θ : ℝ} (hΓ : 0 ≤ Γ) (hW : 0 ≤ W)
    {F : Finset κ} {j : κ} {m : ℕ}
    (hpres : ∀ f ∈ F, ∀ u, E j ≤ u → E f ≤ u → u < t → present u f)
    (hIX : ∀ f ∈ F, ∀ s s', E j ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', c u f ≤ ∑ u ∈ Ico s s', ℓ u f + Γ)
    (hlo : ∀ f ∈ F, ∀ s s', E j ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', ℓ u f ≤ ∑ u ∈ Ico s s', d u f + W)
    (hcov : Covered E (cumL d) t θ F j m)
    (hup : ∑ u ∈ Ico (E j) t, d u j ≤ ∑ u ∈ Ico (E j) t, ℓ u j + W) :
    let A : ℕ → ℝ := fun u => if u < T then
      palgLoss (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) c) ρ u else 0
    let Vr : ℕ → ℝ := fun u => if u < T then
      palgVar (fun _ => (1 : ℝ)) η (specAw (L := L) present) (specLoss (L := L) c) ρ u else 0
    let α : ℝ := (2 * L + 1) * (Real.log (Fintype.card (Spec κ L)) + 2 * δ * T) / η
    (∑ u ∈ Ico (E j) t, Atrue u ≤ ∑ u ∈ Ico (E j) t, A u + Ψ) →
    ∑ u ∈ Ico (E j) t, (Atrue u - ℓ u j) ≤
      θ + m * (α + Γ + W) + W + Ψ + η / 2 * ∑ u ∈ Ico (E j) t, Vr u := by
  intro A Vr α htrue
  have hα : 0 ≤ α := by
    have : (0 : ℝ) ≤ Real.log (Fintype.card (Spec κ L)) :=
      Real.log_nonneg (show (1 : ℝ) ≤ Fintype.card (Spec κ L) by exact_mod_cast Fintype.card_pos)
    positivity
  have h := cover_cert (Pres := fun f => f ∈ F) E t ℓ c d A Atrue (fun u => η / 2 * Vr u) hα hΓ hW
    (fun f hf s s' hjs hs hss hst => by
      have := hedge_interval_hyp_var (L := L) present c hc0 hη hδ ρ hρ T hTL f s s' hss
        (fun u h1 h2 => hpres f hf u (hjs.trans h1) (hs.trans h1) (lt_of_lt_of_le h2 hst))
      rw [← Finset.mul_sum]; exact this)
    hIX hlo (fun f hf => hf) hcov hup htrue
  rw [← Finset.mul_sum] at h
  exact h

end Hedge

end Pool.P0148
