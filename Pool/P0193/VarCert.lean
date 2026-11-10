import Pool.P0160.RetCert
import Pool.P0158.FreedV

/-!
# Record certificates with piece-dependent widths

P0148's `cover_cert` and P0160's `cover_cert_ret` charge every chain piece the same constant (`α + Γ + W`, resp.
`β`). With thread-dependent probe rates (P0150 §1.1) a member's slot width on a piece `[s, s')` depends on the member
and on the piece (`widV (Σ_{[s,s')} v) ρ L` of P0158, with the variance proxy bounded by P0171 / P0159's occupancy
bounds `Σ_{[s,s')} v ≤ (s' − s)·M + c₀`). Here:

* `pieceW`: the sum of a per-member, per-piece width `β f lo hi` over the pieces of a chain (same recursion as
  P0030's `pieceSum`).
* `chain_piece_le_var`: the chain bound with a per-piece hypothesis whose constant is `β f s s'`.
* `cover_cert_var`: P0160's covered-record certificate with piece-dependent widths, for any uniform bound `Wc` on
  `pieceW` over admissible chains.
* `sqrt_add_sqrt_le`: `√a + √(k·b) ≤ √((k+1)(a+b))` (Cauchy–Schwarz for two terms).
* `pieceW_le_sqrt`: if every piece's width is `≤ β₀ + 2√(L·((hi − lo)·M + c₀))`, a chain of length `m` from `a` has
  `pieceW ≤ m·β₀ + 2√(L·m·((t − a)·M + m·c₀))`.
* `cover_cert_sqrt`: the certificate in that shape: `Σ (Atrue − ℓ j) ≤ θ + m·β₀ + 2√(L·m·(|rec|·M + m·c₀)) + W_j +
  Ψ + Σ V`.
-/

open Finset Real

namespace Pool.P0193

open Pool.P0030 Pool.P0061 Pool.P0075 Pool.P0148 Pool.P0160

variable {κ : Type*} [LinearOrder κ]

/-- Sum of a per-member, per-piece quantity over the pieces of a chain started at `a` (pieces as in P0030's
`pieceSum`: `[a, E g)` for the head `f` followed by `g`, and `[E f_m, t)` for the last member). -/
def pieceW (E : κ → ℕ) (t : ℕ) (β : κ → ℕ → ℕ → ℝ) : List κ → ℕ → ℝ
  | [], _ => 0
  | [f], a => β f a t
  | f :: g :: rest, a => β f a (E g) + pieceW E t β (g :: rest) (E g)

/-- **Chain bound with piece-dependent constants.** -/
theorem chain_piece_le_var (E : κ → ℕ) (t a₀ : ℕ) (d : ℕ → κ → ℝ) (A V : ℕ → ℝ) (β : κ → ℕ → ℕ → ℝ)
    (Pres : κ → Prop)
    (hpiece : ∀ f, Pres f → ∀ s s', a₀ ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', d u f + β f s s' + ∑ u ∈ Ico s s', V u) :
    ∀ (ch : List κ) (a : ℕ), a₀ ≤ a → ChainOK E t ch a → (∀ f ∈ ch, Pres f) →
      ∑ u ∈ Ico a t, A u ≤ pieceSum E (cumL d) t ch a + pieceW E t β ch a + ∑ u ∈ Ico a t, V u := by
  intro ch
  induction ch with
  | nil => intro a _ h; exact h.elim
  | cons f rest ih =>
    intro a ha hok hpres
    cases rest with
    | nil =>
      obtain ⟨hfa, hat⟩ := hok
      simp only [pieceSum, pieceW]
      rw [Lint_cumL d f hat]
      exact hpiece f (hpres f List.mem_cons_self) a t ha hfa hat le_rfl
    | cons g rest' =>
      obtain ⟨hfa, hag, hrest⟩ := hok
      have hgt := chainOK_le E t _ _ hrest
      have h1 := hpiece f (hpres f List.mem_cons_self) a (E g) ha hfa hag hgt
      have h2 := ih (E g) (ha.trans hag) hrest (fun x hx => hpres x (List.mem_cons_of_mem _ hx))
      simp only [pieceSum, pieceW] at h2 ⊢
      rw [Lint_cumL d f hag]
      rw [← Finset.sum_Ico_consecutive _ hag hgt, ← Finset.sum_Ico_consecutive _ hag hgt]
      linarith

/-- **Covered-record certificate with piece-dependent widths** (P0160's `cover_cert_ret` with `β f s s'` in place of
the constant `β`). `Wc` bounds `pieceW` on every admissible chain (length `≤ m`, members in `F`, valid from `E j`). -/
theorem cover_cert_var (E : κ → ℕ) (t : ℕ) (ℓ d : ℕ → κ → ℝ) (A Atrue V : ℕ → ℝ)
    {F : Finset κ} {j : κ} {m : ℕ} {W Ψ θ Wc : ℝ} (β : κ → ℕ → ℕ → ℝ) (Pres : κ → Prop)
    (hpiece : ∀ f, Pres f → ∀ s s', E j ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', d u f + β f s s' + ∑ u ∈ Ico s s', V u)
    (hFP : ∀ f ∈ F, Pres f)
    (hWc : ∀ ch : List κ, ch.length ≤ m → (∀ f ∈ ch, f ∈ F) → ChainOK E t ch (E j) →
      pieceW E t β ch (E j) ≤ Wc)
    (hcov : Covered E (cumL d) t θ F j m)
    (hup : ∑ u ∈ Ico (E j) t, d u j ≤ ∑ u ∈ Ico (E j) t, ℓ u j + W)
    (htrue : ∑ u ∈ Ico (E j) t, Atrue u ≤ ∑ u ∈ Ico (E j) t, A u + Ψ) :
    ∑ u ∈ Ico (E j) t, (Atrue u - ℓ u j) ≤ θ + Wc + W + Ψ + ∑ u ∈ Ico (E j) t, V u := by
  obtain ⟨ch, hlen, hmem, hok, hcv⟩ := hcov
  have hjt := chainOK_le E t ch (E j) hok
  have h := chain_piece_le_var E t (E j) d A V β Pres hpiece ch (E j) le_rfl hok
    (fun f hf => hFP f (hmem f hf))
  have hw := hWc ch hlen hmem hok
  rw [Lint_cumL d j hjt] at hcv
  rw [Finset.sum_sub_distrib]
  linarith

/-- Cauchy–Schwarz for two terms: `√a + √(k·b) ≤ √((k + 1)(a + b))`. -/
theorem sqrt_add_sqrt_le {a b k : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : 0 ≤ k) :
    √a + √(k * b) ≤ √((k + 1) * (a + b)) := by
  have hkb : 0 ≤ k * b := mul_nonneg hk hb
  have hR : 0 ≤ (k + 1) * (a + b) := by positivity
  rw [Real.le_sqrt (by positivity) hR]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hkb
  -- 2√a√(kb) ≤ ka + b  ⟸  (√(ka) − √b)² ≥ 0 with √(ka)·√b = √a·√(kb)
  have hprod : √a * √(k * b) = √(k * a) * √b := by
    rw [← Real.sqrt_mul ha, ← Real.sqrt_mul (mul_nonneg hk ha)]; ring_nf
  have h3 := Real.sq_sqrt (mul_nonneg hk ha)
  have h4 := Real.sq_sqrt hb
  have hsq : 0 ≤ (√(k * a) - √b) ^ 2 := sq_nonneg _
  nlinarith [hprod, h1, h2, h3, h4, hsq]

/-- **Chain widths with √-shaped pieces.** If every piece `[lo, hi)` of a member costs at most
`β₀ + 2√(L·((hi − lo)·M + c₀))`, a valid chain of length `m` started at `a ≤ t` costs at most
`m·β₀ + 2√(L·m·((t − a)·M + m·c₀))`. The constants `β₀`, `M`, `c₀` are the same for all members: with
member-dependent constants (e.g. P0171's `thr0·ρ·T/n`, which depends on the member's entry thread) take their maximum
over the members that can occur in the chain. -/
theorem pieceW_le_sqrt (E : κ → ℕ) (t : ℕ) (β : κ → ℕ → ℕ → ℝ) {β₀ L M c₀ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hc₀ : 0 ≤ c₀) (Pres : κ → Prop)
    (hβ : ∀ f, Pres f → ∀ lo hi, lo ≤ hi → hi ≤ t →
      β f lo hi ≤ β₀ + 2 * √(L * (((hi - lo : ℕ) : ℝ) * M + c₀))) :
    ∀ (ch : List κ) (a : ℕ), ChainOK E t ch a → (∀ f ∈ ch, Pres f) →
      pieceW E t β ch a ≤ ch.length * β₀ +
        2 * √(L * (ch.length * (((t - a : ℕ) : ℝ) * M + ch.length * c₀))) := by
  intro ch
  induction ch with
  | nil => intro a h; exact h.elim
  | cons f rest ih =>
    intro a hok hpres
    cases rest with
    | nil =>
      obtain ⟨_, hat⟩ := hok
      simp only [pieceW, List.length_singleton, Nat.cast_one, one_mul]
      exact hβ f (hpres f List.mem_cons_self) a t hat le_rfl
    | cons g rest' =>
      obtain ⟨_, hag, hrest⟩ := hok
      have hgt := chainOK_le E t _ _ hrest
      have h1 := hβ f (hpres f List.mem_cons_self) a (E g) hag hgt
      have h2 := ih (E g) hrest (fun x hx => hpres x (List.mem_cons_of_mem _ hx))
      simp only [pieceW, List.length_cons] at h2 ⊢
      set k : ℝ := ((rest'.length + 1 : ℕ) : ℝ) with hk
      have hk0 : 0 ≤ k := by positivity
      -- lengths: (t - a) = (E g - a) + (t - E g)
      have hlen : ((t - a : ℕ) : ℝ) = ((E g - a : ℕ) : ℝ) + ((t - E g : ℕ) : ℝ) := by
        rw [← Nat.cast_add]; congr 1; omega
      set x₁ : ℝ := ((E g - a : ℕ) : ℝ) * M + c₀ with hx₁
      set x₂ : ℝ := ((t - E g : ℕ) : ℝ) * M + k * c₀ with hx₂
      have hx₁0 : 0 ≤ x₁ := by positivity
      have hx₂0 : 0 ≤ x₂ := by positivity
      have hcs := sqrt_add_sqrt_le (mul_nonneg hL hx₁0) (mul_nonneg hL hx₂0) hk0
      have e1 : L * (k * (((t - E g : ℕ) : ℝ) * M + k * c₀)) = k * (L * x₂) := by rw [hx₂]; ring
      have e2 : L * ((k + 1) * (((t - a : ℕ) : ℝ) * M + (k + 1) * c₀)) =
          (k + 1) * (L * x₁ + L * x₂) := by
        rw [hlen, hx₁, hx₂]; ring
      have hmono : √((k + 1) * (L * x₁ + L * x₂)) ≤
          √(L * ((k + 1) * (((t - a : ℕ) : ℝ) * M + (k + 1) * c₀))) := by
        apply Real.sqrt_le_sqrt
        rw [e2]
      have hcast : ((rest'.length + 1 + 1 : ℕ) : ℝ) = k + 1 := by rw [hk]; push_cast; ring
      rw [hcast]
      rw [e1] at h2
      have : β f a (E g) + pieceW E t β (g :: rest') (E g) ≤
          (k + 1) * β₀ + 2 * (√(L * x₁) + √(k * (L * x₂))) := by
        have h2' : pieceW E t β (g :: rest') (E g) ≤ k * β₀ + 2 * √(k * (L * x₂)) := by
          simpa [hk] using h2
        have h1' : β f a (E g) ≤ β₀ + 2 * √(L * x₁) := h1
        linarith
      linarith

/-- **Covered-record certificate with √-shaped piece widths.** Every cover member `f` satisfies, on every piece
`[s, s')` of the comparator's record, `Σ A ≤ Σ d_f + β₀ + 2√(L·((s' − s)·M + c₀)) + Σ V` (e.g. P0160's
`piece_of_retire` with the slot width `widV (Σ v) ρ L` of P0158 and P0171's occupancy bound `Σ v ≤ (s'−s)M + c₀`,
the range term `2ρL` put into `β₀`). Then the record costs at most
`θ + m·β₀ + 2√(L·m·((t − E j)·M + m·c₀)) + W + Ψ + Σ V`. One `β₀`, `M` and `c₀` serve all cover members: P0171's
additive constant `thr0·ρ·T/n` depends on the member's entry thread, so `c₀` must be its maximum over `F` (the
hypothesis only needs an upper bound; a crude maximum enters as `m·c₀` inside the root). -/
theorem cover_cert_sqrt (E : κ → ℕ) (t : ℕ) (ℓ d : ℕ → κ → ℝ) (A Atrue V : ℕ → ℝ)
    {F : Finset κ} {j : κ} {m : ℕ} {W Ψ θ β₀ L M c₀ : ℝ} (hβ₀ : 0 ≤ β₀) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hc₀ : 0 ≤ c₀) (Pres : κ → Prop)
    (hpiece : ∀ f, Pres f → ∀ s s', E j ≤ s → E f ≤ s → s ≤ s' → s' ≤ t →
      ∑ u ∈ Ico s s', A u ≤ ∑ u ∈ Ico s s', d u f + (β₀ + 2 * √(L * (((s' - s : ℕ) : ℝ) * M + c₀))) +
        ∑ u ∈ Ico s s', V u)
    (hFP : ∀ f ∈ F, Pres f)
    (hcov : Covered E (cumL d) t θ F j m)
    (hup : ∑ u ∈ Ico (E j) t, d u j ≤ ∑ u ∈ Ico (E j) t, ℓ u j + W)
    (htrue : ∑ u ∈ Ico (E j) t, Atrue u ≤ ∑ u ∈ Ico (E j) t, A u + Ψ) :
    ∑ u ∈ Ico (E j) t, (Atrue u - ℓ u j) ≤
      θ + (m * β₀ + 2 * √(L * (m * (((t - E j : ℕ) : ℝ) * M + m * c₀)))) + W + Ψ +
        ∑ u ∈ Ico (E j) t, V u := by
  classical
  -- the per-piece width, restricted to the comparator's record so that `hpiece` applies
  let β : κ → ℕ → ℕ → ℝ := fun _ lo hi => β₀ + 2 * √(L * (((hi - lo : ℕ) : ℝ) * M + c₀))
  refine cover_cert_var E t ℓ d A Atrue V β Pres hpiece hFP ?_ hcov hup htrue
  intro ch hlen hmem hok
  have h := pieceW_le_sqrt E t β hL hM hc₀ (fun _ => True) (fun f _ lo hi _ _ => le_rfl) ch (E j) hok
    (fun _ _ => trivial)
  refine h.trans ?_
  have hl : (ch.length : ℝ) ≤ m := by exact_mod_cast hlen
  have hl0 : (0 : ℝ) ≤ ch.length := by positivity
  have hT : (0 : ℝ) ≤ ((t - E j : ℕ) : ℝ) * M := by positivity
  have h1 : (ch.length : ℝ) * β₀ ≤ m * β₀ := mul_le_mul_of_nonneg_right hl hβ₀
  have h2 : √(L * (ch.length * (((t - E j : ℕ) : ℝ) * M + ch.length * c₀))) ≤
      √(L * (m * (((t - E j : ℕ) : ℝ) * M + m * c₀))) := by
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ hL
    have hc1 : (ch.length : ℝ) * c₀ ≤ m * c₀ := mul_le_mul_of_nonneg_right hl hc₀
    have hin : ((t - E j : ℕ) : ℝ) * M + ch.length * c₀ ≤ ((t - E j : ℕ) : ℝ) * M + m * c₀ := by linarith
    calc (ch.length : ℝ) * (((t - E j : ℕ) : ℝ) * M + ch.length * c₀)
        ≤ m * (((t - E j : ℕ) : ℝ) * M + ch.length * c₀) :=
          mul_le_mul_of_nonneg_right hl (by positivity)
      _ ≤ m * (((t - E j : ℕ) : ℝ) * M + m * c₀) :=
          mul_le_mul_of_nonneg_left hin (by linarith)
  linarith

/-- **P0158's width in the √-shape.** If the variance proxy of a piece is at most `(s' − s)·M + c₀` (P0171's
occupancy bound) and the range parameter is at most `ρ₀`, then `widV (Σ v) ρ L ≤ 2ρ₀L + 2√(L·((s' − s)·M + c₀))`,
i.e. the piece width has the shape of `pieceW_le_sqrt` with `β₀ = 2ρ₀L` (plus the learner's constants). -/
theorem widV_le_sqrt {V ρ ρ₀ L len M c₀ : ℝ} (hL : 0 ≤ L) (hV : V ≤ len * M + c₀) (hρ : ρ ≤ ρ₀) :
    Pool.P0158.widV V ρ L ≤ 2 * ρ₀ * L + 2 * √(L * (len * M + c₀)) := by
  unfold Pool.P0158.widV
  have h1 : √(V * L) ≤ √(L * (len * M + c₀)) := by
    apply Real.sqrt_le_sqrt; rw [mul_comm]; exact mul_le_mul_of_nonneg_left hV hL
  have h2 : ρ * L ≤ ρ₀ * L := mul_le_mul_of_nonneg_right hρ hL
  linarith

end Pool.P0193
