import Pool.P0148.Cert

/-!
# Covered-record certificate when chain members may RETIRE during the record

P0156 (merged) turns Design Z's (b″)-eviction into **retirement**: the member leaves ALG, but stays in
its pools with fake slot data `d = 1` per round until a merge removes it. A cover chain may then use a member on a
segment where it is retired, and there P0148's learner hypothesis (ALG competes with the member) no longer holds.

On a retired segment, ALG still competes with the **base meta-arm**, which is always present. Its IX data are at most
the drawn arms' losses plus `Γ`, and those are `≤ 1` per round, i.e. `≤` the fake data. So every chain piece keeps a
bound of the same form: `Σ A ≤ Σ d_f + (2α + 2Γ + W) + Σ V` (only `α` and `Γ` double; the retired part
needs no slot width).

* `chain_piece_le`: the chain bound from a single per-piece hypothesis (via P0148's `chain_est_le`).
* `piece_of_retire`: the per-piece hypothesis for a member with retirement time `r` (possibly never retired), from
  P0148's three active-part hypotheses on `[E f, r)` and the meta-arm's hypotheses on `[r, ·)`.
* `cover_cert_ret`: P0148's `cover_cert` with retiring members; with `piece_of_retire` the per-member constant is
  `2α + 2Γ + W` instead of P0148's `α + Γ + W`.
-/

open Finset Real

namespace Pool.P0160

open Pool.P0030 Pool.P0061 Pool.P0075 Pool.P0148

variable {κ : Type*} [LinearOrder κ]

/-- **Chain bound from a per-piece hypothesis.** -/
theorem chain_piece_le (E : κ → ℕ) (t a₀ : ℕ) (d : ℕ → κ → ℝ) (A V : ℕ → ℝ) (β : ℝ) (Pres : κ → Prop)
    (hpiece : ∀ f, Pres f → ∀ s s', a₀ ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', d u f + β + ∑ u ∈ Ico s s', V u) :
    ∀ (ch : List κ) (a : ℕ), a₀ ≤ a → ChainOK E t ch a → (∀ f ∈ ch, Pres f) →
      ∑ u ∈ Ico a t, A u ≤ pieceSum E (cumL d) t ch a + ch.length * β + ∑ u ∈ Ico a t, V u := by
  intro ch a ha hok hP
  have h := chain_est_le E t a₀ d d d A V β 0 0 Pres hpiece
    (fun f _ s s' _ _ _ _ => by linarith) (fun f _ s s' _ _ _ _ => by linarith) ch a ha hok hP
  simpa using h

/-- **Per-piece bound for a member that retires at `r`.** Active part `[s, min(s', r))`: P0148's three hypotheses
(learner vs the member, IX one-sidedness, slot lower tail). Retired part `[max(s, r), s')`: the learner vs the base
meta-arm, the meta-arm's IX one-sidedness against the drawn losses, drawn losses `≤ 1`, and fake data `d = 1` on
the retired part `[r, s')` only. The constant is `2α + 2Γ + W`. -/
theorem piece_of_retire {f : κ} (r s s' : ℕ) (hss : s ≤ s') (ℓ c d : ℕ → κ → ℝ) (A V cB drawn : ℕ → ℝ)
    {α Γ W : ℝ} (hα : 0 ≤ α) (hΓ : 0 ≤ Γ) (hW : 0 ≤ W)
    (hL : ∑ u ∈ Ico s (min s' (max s r)), A u ≤ ∑ u ∈ Ico s (min s' (max s r)), c u f + α +
      ∑ u ∈ Ico s (min s' (max s r)), V u)
    (hIX : ∑ u ∈ Ico s (min s' (max s r)), c u f ≤ ∑ u ∈ Ico s (min s' (max s r)), ℓ u f + Γ)
    (hlo : ∑ u ∈ Ico s (min s' (max s r)), ℓ u f ≤ ∑ u ∈ Ico s (min s' (max s r)), d u f + W)
    (hLB : ∑ u ∈ Ico (min s' (max s r)) s', A u ≤ ∑ u ∈ Ico (min s' (max s r)) s', cB u + α +
      ∑ u ∈ Ico (min s' (max s r)) s', V u)
    (hIXB : ∑ u ∈ Ico (min s' (max s r)) s', cB u ≤ ∑ u ∈ Ico (min s' (max s r)) s', drawn u + Γ)
    (hdrawn : ∀ u, drawn u ≤ 1) (hfake : ∀ u, r ≤ u → u < s' → d u f = 1) :
    ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', d u f + (2 * α + 2 * Γ + W) + ∑ u ∈ Ico s s', V u := by
  have hm1 : s ≤ min s' (max s r) := le_min hss (le_max_left _ _)
  have hm2 : min s' (max s r) ≤ s' := min_le_left _ _
  have hdr : ∑ u ∈ Ico (min s' (max s r)) s', drawn u ≤ ∑ u ∈ Ico (min s' (max s r)) s', d u f := by
    refine Finset.sum_le_sum fun u hu => ?_
    have hu' := (Finset.mem_Ico.1 hu).1
    have hru : r ≤ u := le_trans (le_trans (le_max_right s r) ?_) hu'
    · rw [hfake u hru (Finset.mem_Ico.1 hu).2]; exact hdrawn u
    · -- if min = s' the interval is empty; otherwise min = max s r
      rcases le_total s' (max s r) with h | h
      · rw [min_eq_left h] at hu'
        exact absurd (Finset.mem_Ico.1 hu).2 (by omega)
      · rw [min_eq_right h]
  rw [← Finset.sum_Ico_consecutive _ hm1 hm2, ← Finset.sum_Ico_consecutive _ hm1 hm2,
    ← Finset.sum_Ico_consecutive _ hm1 hm2]
  linarith

/-- **Covered-record certificate with retiring members** (P0148's `cover_cert`; with `piece_of_retire` the per-member
constant is `β = 2α + 2Γ + W`).
For every cover member `f`, every interval `[s, s')` inside the comparator's record satisfies the per-piece bound
(e.g. by `piece_of_retire`). -/
theorem cover_cert_ret (E : κ → ℕ) (t : ℕ) (ℓ d : ℕ → κ → ℝ) (A Atrue V : ℕ → ℝ)
    {F : Finset κ} {j : κ} {m : ℕ} {β W Ψ θ : ℝ} (hβ : 0 ≤ β) (Pres : κ → Prop)
    (hpiece : ∀ f, Pres f → ∀ s s', E j ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', d u f + β + ∑ u ∈ Ico s s', V u)
    (hFP : ∀ f ∈ F, Pres f)
    (hcov : Covered E (cumL d) t θ F j m)
    (hup : ∑ u ∈ Ico (E j) t, d u j ≤ ∑ u ∈ Ico (E j) t, ℓ u j + W)
    (htrue : ∑ u ∈ Ico (E j) t, Atrue u ≤ ∑ u ∈ Ico (E j) t, A u + Ψ) :
    ∑ u ∈ Ico (E j) t, (Atrue u - ℓ u j) ≤ θ + m * β + W + Ψ + ∑ u ∈ Ico (E j) t, V u := by
  obtain ⟨ch, hlen, hmem, hok, hcv⟩ := hcov
  have hjt := chainOK_le E t ch (E j) hok
  have h := chain_piece_le E t (E j) d A V β Pres hpiece ch (E j) le_rfl hok (fun f hf => hFP f (hmem f hf))
  rw [Lint_cumL d j hjt] at hcv
  have hl : (ch.length : ℝ) * β ≤ m * β := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hβ
  rw [Finset.sum_sub_distrib]
  linarith

end Pool.P0160
