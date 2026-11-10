import Pool.P0054.Dyadic
import Pool.P0061.Chain
/-!
# Covering chains against a sleeping-experts Hedge with dyadic specialists

Deterministic glue between the cover certificates of the Peng–Rubinstein pool (P0030 chains, as
produced by P0061's `cert_transfer`) and the regret of P0019's specialists Hedge through dyadic
specialists (P0054).

**Setting.** Copies `κ` (linearly ordered, entry times `E`, per-round losses `ℓ u f`). A specialists
Hedge over `σ` (priors `q`, rate `η`, awake pattern `aw`, losses `c ≥ 0`). `Pres f` says that the
learner keeps copy `f` on `[E f, t)`. For such `f` and every dyadic piece `p ⊆ [E f, t)` (`Dy p`),
the specialist `spec f p` is awake (among rounds `< T`) exactly on `p` and has loss `ℓ u f` there.
That is the design "one specialist per (copy, dyadic interval of its lifespan)" (P0022 §1).

* `chain_hedge_le`: for every chain `ch` valid from `a` (P0030 `ChainOK E t ch a`) whose members
  satisfy `Pres`,
  `Σ_{u∈[a,t)} algLoss u ≤ pieceSum(ch) + |ch|·(2L+1)Λ/η + (η/2) Σ_{u∈[a,t)} algVar u`.
* `covered_hedge_le`: if the comparator `j` is `Covered` (P0030, margin `θ`, chain length `≤ m`) by
  members of `F ⊆ Pres`, then
  `Σ_{u∈[E j,t)} (algLoss u − ℓ u j) ≤ θ + m (2L+1) Λ/η + (η/2) Σ algVar`.
  With `r u = algLoss u − ℓ u j − (η/2) algVar u`, this is the per-good-interval cost `β` (with
  `α = 0`) of the walks P0049/P0056/P0057.
-/

namespace Pool.P0075
open Finset Real Pool.P0054

variable {κ : Type*} [LinearOrder κ]

lemma chainOK_le (E : κ → ℕ) (t : ℕ) : ∀ (l : List κ) (x : ℕ), Pool.P0030.ChainOK E t l x → x ≤ t
  | [], _, h => h.elim
  | [_], _, h => h.2
  | _ :: g :: rest, _, h => h.2.1.trans (chainOK_le E t (g :: rest) (E g) h.2.2)

variable {σ : Type*} [Fintype σ] {q : σ → ℝ} {η : ℝ} {aw : ℕ → σ → Bool} {c : ℕ → σ → ℝ}

theorem chain_hedge_le (hq : ∀ i, 0 < q i) (hη : 0 < η) (hc : ∀ u i, 0 ≤ c u i)
    (T L t : ℕ) (htL : t ≤ 2^L) (htT : t ≤ T)
    (E : κ → ℕ) (ℓ : ℕ → κ → ℝ) (spec : κ → ℕ × ℕ → σ) (Pres : κ → Prop)
    (haw : ∀ f, Pres f → ∀ p, Dy p → E f ≤ p.1 → p.1 + 2^p.2 ≤ t → ∀ u < T,
      aw u (spec f p) = true ↔ p.1 ≤ u ∧ u < p.1 + 2^p.2)
    (hg : ∀ f, Pres f → ∀ p, Dy p → E f ≤ p.1 → p.1 + 2^p.2 ≤ t → ∀ u, p.1 ≤ u → u < p.1 + 2^p.2 →
      c u (spec f p) = ℓ u f)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ f, Pres f → ∀ p, log ((∑ j, q j) / q (spec f p)) ≤ Λ) :
    ∀ (ch : List κ) (a : ℕ), Pool.P0030.ChainOK E t ch a → (∀ f ∈ ch, Pres f) →
      ∑ u ∈ Ico a t, algLoss q η aw c u ≤
        Pool.P0030.pieceSum E (Pool.P0061.cumL ℓ) t ch a + ch.length * ((2 * L + 1) * Λ / η) +
          η / 2 * ∑ u ∈ Ico a t, algVar q η aw c u := by
  -- one piece [lo, hi) played by member f
  have piece : ∀ (f : κ) (lo hi : ℕ), Pres f → E f ≤ lo → lo ≤ hi → hi ≤ t →
      ∑ u ∈ Ico lo hi, algLoss q η aw c u ≤ ∑ u ∈ Ico lo hi, ℓ u f + (2 * L + 1) * Λ / η +
        η / 2 * ∑ u ∈ Ico lo hi, algVar q η aw c u := by
    intro f lo hi hP hf hlo hhi
    have h := regret_interval_le hq hη hc T L lo hi hlo (hhi.trans htL) (hhi.trans htT) (spec f)
      (fun u => ℓ u f)
      (fun p hp => by
        obtain ⟨hdy, h1, h2⟩ := dec_dy L lo hi (hhi.trans htL) p hp
        exact haw f hP p hdy (hf.trans h1) (h2.trans hhi))
      (fun p hp => by
        obtain ⟨hdy, h1, h2⟩ := dec_dy L lo hi (hhi.trans htL) p hp
        exact hg f hP p hdy (hf.trans h1) (h2.trans hhi))
      hΛ0 (fun p _ => hΛ f hP p)
    rw [Finset.sum_sub_distrib] at h
    linarith
  intro ch
  induction ch with
  | nil => intro a h; exact h.elim
  | cons f rest ih =>
    intro a hok hpres
    cases rest with
    | nil =>
      obtain ⟨hfa, hat⟩ := hok
      simp only [Pool.P0030.pieceSum, List.length_singleton, Nat.cast_one, one_mul]
      rw [Pool.P0061.Lint_cumL ℓ f hat]
      exact piece f a t (hpres f List.mem_cons_self) hfa hat le_rfl
    | cons g rest' =>
      obtain ⟨hfa, hag, hrest⟩ := hok
      have hgt := chainOK_le E t _ _ hrest
      have h1 := piece f a (E g) (hpres f List.mem_cons_self) hfa hag hgt
      have h2 := ih (E g) hrest (fun x hx => hpres x (List.mem_cons_of_mem _ hx))
      simp only [Pool.P0030.pieceSum, List.length_cons, Nat.cast_add, Nat.cast_one] at h2 ⊢
      rw [Pool.P0061.Lint_cumL ℓ f hag]
      rw [← Finset.sum_Ico_consecutive _ hag hgt, ← Finset.sum_Ico_consecutive _ hag hgt]
      nlinarith

/-- **Good-interval cost from a cover.** If the comparator copy `j` (loss `ℓ u j`, entry `E j`) is
covered on `[E j, t)` (P0030 `Covered`, margin `θ`) by a chain of at most `m` members, all of which
satisfy `Pres`, then the specialists Hedge loses at most
`θ + m (2L+1) Λ / η + (η/2) Σ algVar` more than `j` on `[E j, t)`. -/
theorem covered_hedge_le (hq : ∀ i, 0 < q i) (hη : 0 < η) (hc : ∀ u i, 0 ≤ c u i)
    (T L t : ℕ) (htL : t ≤ 2^L) (htT : t ≤ T)
    (E : κ → ℕ) (ℓ : ℕ → κ → ℝ) (spec : κ → ℕ × ℕ → σ) (Pres : κ → Prop)
    (haw : ∀ f, Pres f → ∀ p, Dy p → E f ≤ p.1 → p.1 + 2^p.2 ≤ t → ∀ u < T,
      aw u (spec f p) = true ↔ p.1 ≤ u ∧ u < p.1 + 2^p.2)
    (hg : ∀ f, Pres f → ∀ p, Dy p → E f ≤ p.1 → p.1 + 2^p.2 ≤ t → ∀ u, p.1 ≤ u → u < p.1 + 2^p.2 →
      c u (spec f p) = ℓ u f)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ f, Pres f → ∀ p, log ((∑ j, q j) / q (spec f p)) ≤ Λ)
    {θ : ℝ} {F : Finset κ} {j : κ} {m : ℕ} (hFP : ∀ f ∈ F, Pres f)
    (hcov : Pool.P0030.Covered E (Pool.P0061.cumL ℓ) t θ F j m) :
    ∑ u ∈ Ico (E j) t, (algLoss q η aw c u - ℓ u j) ≤
      θ + m * ((2 * L + 1) * Λ / η) + η / 2 * ∑ u ∈ Ico (E j) t, algVar q η aw c u := by
  obtain ⟨ch, hlen, hmem, hok, hcv⟩ := hcov
  have hjt := chainOK_le E t ch (E j) hok
  have h := chain_hedge_le hq hη hc T L t htL htT E ℓ spec Pres haw hg hΛ0 hΛ ch (E j) hok
    (fun f hf => hFP f (hmem f hf))
  rw [Pool.P0061.Lint_cumL ℓ j hjt] at hcv
  have hX : 0 ≤ (2 * L + 1) * Λ / η := by positivity
  have hl : (ch.length : ℝ) * ((2 * L + 1) * Λ / η) ≤ m * ((2 * L + 1) * Λ / η) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hX
  rw [Finset.sum_sub_distrib]
  linarith

end Pool.P0075
