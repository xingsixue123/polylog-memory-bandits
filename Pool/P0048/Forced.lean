import Pool.P0034.Coins

/-!
# Forced-insertion counting of bad epochs

Independent coins `ω : ι → Bool`, coin `x` being `true` with probability `p x`
(`wtv p ω = ∏ x, (p x if ω x else 1 − p x)`). An *opportunity* `a` (for example: "the best arm
enters at epoch `a` and is passive") is the event that the coins of a finite set `S a` take
prescribed values `v a`. Forcing the opportunity sets these coins to their values and leaves all
other coins unchanged (`force`).

* `sum_ind_mul`: if `g` does not depend on coin `x`, then `E[1{ω x = c} · g] = P(ω x = c) · E[g]`.
* `sum_event_force`: for a finite set of coins `S`, `E[1{ω|S = v} · g(force S v ω)] =
  P(ω|S = v) · E[g(force S v ω)]`.
* `forced_count` (main): let `Surv a ω` say that the copy inserted at opportunity `a` survives in
  the run determined by `ω`. If in every run at most `P` realized opportunities have surviving
  copies, then `Σ_a P(opportunity a) · P(Surv a (force ω)) ≤ P`. With `P(opportunity a) ≥ π`
  for all `a`, the expected number of *bad* opportunities (those whose forced copy would survive)
  is at most `P / π` (`forced_count_card`).

No independence between copies and no non-interference ("passivity") of a copy with the rest of
the system is assumed: `Surv` is an arbitrary predicate of the whole coin vector.
`forced_count_uniform` restates the bound for P0034's uniform coins `Pool.P0034.wt`.
-/

open Finset

namespace Pool.P0048

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weight of a coin value: `p` for `true`, `1 − p` for `false`. -/
noncomputable def cw (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Product weight of a coin vector with per-coin probabilities `p x`. -/
noncomputable def wtv (p : ι → ℝ) (ω : ι → Bool) : ℝ := ∏ x, cw (p x) (ω x)

/-- Probability that the coins of `S` take the values `v`. -/
noncomputable def piS (p : ι → ℝ) (S : Finset ι) (v : ι → Bool) : ℝ := ∏ x ∈ S, cw (p x) (v x)

/-- Set the coins of `S` to the values `v`, keep the others. -/
def force (S : Finset ι) (v : ι → Bool) (ω : ι → Bool) : ι → Bool :=
  fun x => if x ∈ S then v x else ω x

/-- The event that the coins of `S` have the values `v`. -/
abbrev EvS (S : Finset ι) (v : ι → Bool) (ω : ι → Bool) : Prop := ∀ x ∈ S, ω x = v x

theorem cw_add (q : ℝ) (b : Bool) : cw q b + cw q (!b) = 1 := by
  cases b <;> simp [cw]

theorem cw_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (b : Bool) : 0 ≤ cw q b := by
  cases b <;> simp [cw] <;> linarith

theorem wtv_nonneg {p : ι → ℝ} (h0 : ∀ x, 0 ≤ p x) (h1 : ∀ x, p x ≤ 1) (ω : ι → Bool) :
    0 ≤ wtv p ω :=
  Finset.prod_nonneg fun x _ => cw_nonneg (h0 x) (h1 x) _

theorem sum_wtv (p : ι → ℝ) : ∑ ω : ι → Bool, wtv p ω = 1 := by
  unfold wtv
  rw [← Fintype.prod_sum]
  refine Finset.prod_eq_one fun x _ => ?_
  simp [cw]

/-- Weight of the coins other than `x`. -/
noncomputable def rest (p : ι → ℝ) (x : ι) (ω : ι → Bool) : ℝ :=
  ∏ y ∈ univ.erase x, cw (p y) (ω y)

theorem wtv_eq (p : ι → ℝ) (x : ι) (ω : ι → Bool) : wtv p ω = cw (p x) (ω x) * rest p x ω := by
  unfold wtv rest
  exact (Finset.mul_prod_erase univ (fun y => cw (p y) (ω y)) (mem_univ x)).symm

theorem rest_update (p : ι → ℝ) (x : ι) (ω : ι → Bool) (b : Bool) :
    rest p x (Function.update ω x b) = rest p x ω := by
  unfold rest
  refine Finset.prod_congr rfl fun y hy => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hy)]

/-- Flip coin `x`. -/
def flip (x : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun ω := Function.update ω x (!ω x)
  invFun ω := Function.update ω x (!ω x)
  left_inv ω := by
    funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [Function.update_of_ne hy]
  right_inv ω := by
    funext y
    by_cases hy : y = x
    · subst hy; simp
    · simp [Function.update_of_ne hy]

/-- **One coin.** If `g` does not depend on coin `x`, then
`E[1{ω x = c} · g] = P(ω x = c) · E[g]`. -/
theorem sum_ind_mul (p : ι → ℝ) (x : ι) (c : Bool) (g : (ι → Bool) → ℝ)
    (hg : ∀ ω b, g (Function.update ω x b) = g ω) :
    ∑ ω, wtv p ω * ((if ω x = c then (1 : ℝ) else 0) * g ω) =
      cw (p x) c * ∑ ω, wtv p ω * g ω := by
  -- split any sum by whether coin `x` equals `c`, pairing `ω` with its flip
  have hsplit : ∀ F : (ι → Bool) → ℝ,
      ∑ ω, F ω = ∑ ω, (if ω x = c then F ω + F (flip x ω) else 0) := by
    intro F
    have h1 : ∑ ω, F ω = ∑ ω, (if ω x = c then F ω else 0) + ∑ ω, (if ω x = c then 0 else F ω) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ω _ => ?_
      split_ifs <;> simp
    have h2 : ∑ ω, (if ω x = c then (0 : ℝ) else F ω) =
        ∑ ω, (if ω x = c then F (flip x ω) else 0) := by
      rw [← (flip x).sum_comp]
      refine Finset.sum_congr rfl fun ω _ => ?_
      have hf : (flip x ω) x = !ω x := by simp [flip]
      rw [hf]
      cases hω : ω x <;> cases c <;> simp
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs <;> simp
  rw [hsplit (fun ω => wtv p ω * g ω), Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases hω : ω x = c
  · simp only [hω, ite_true, one_mul]
    have hgf : g (flip x ω) = g ω := hg ω _
    have hwf : wtv p (flip x ω) = cw (p x) (!c) * rest p x ω := by
      rw [wtv_eq p x]
      simp only [flip, Equiv.coe_fn_mk, Function.update_self]
      rw [rest_update, hω]
    rw [hgf, hwf, wtv_eq p x ω, hω]
    have := cw_add (p x) c
    linear_combination (-(rest p x ω * g ω * cw (p x) c)) * this
  · simp [hω]

theorem force_insert {x : ι} {S : Finset ι} (hx : x ∉ S) (v ω : ι → Bool) :
    force (insert x S) v ω = Function.update (force S v ω) x (v x) := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [force]
  · simp [force, Function.update_of_ne hy, Finset.mem_insert, hy]

theorem force_update_of_mem {x : ι} {S : Finset ι} (hx : x ∈ S) (v ω : ι → Bool) (b : Bool) :
    force S v (Function.update ω x b) = force S v ω := by
  funext y
  by_cases hy : y = x
  · subst hy; simp [force, hx]
  · simp [force, Function.update_of_ne hy]

theorem evS_update_of_not_mem {x : ι} {S : Finset ι} (hx : x ∉ S) (v ω : ι → Bool) (b : Bool) :
    EvS S v (Function.update ω x b) ↔ EvS S v ω := by
  unfold EvS
  refine forall₂_congr fun y hy => ?_
  have hyx : y ≠ x := by rintro rfl; exact hx hy
  rw [Function.update_of_ne hyx]

theorem force_eq_self {S : Finset ι} {v ω : ι → Bool} (h : EvS S v ω) : force S v ω = ω := by
  funext y
  unfold force
  split_ifs with hy
  · exact (h y hy).symm
  · rfl

/-- **Finitely many coins.** `E[1{ω|S = v} · g(force S v ω)] = P(ω|S = v) · E[g(force S v ω)]`. -/
theorem sum_event_force (p : ι → ℝ) (S : Finset ι) (v : ι → Bool) (g : (ι → Bool) → ℝ) :
    ∑ ω, wtv p ω * ((if EvS S v ω then (1 : ℝ) else 0) * g (force S v ω)) =
      piS p S v * ∑ ω, wtv p ω * g (force S v ω) := by
  induction S using Finset.induction_on generalizing g with
  | empty =>
    simp [piS, EvS, force]
  | @insert x S hx ih =>
    -- step 1: peel off coin `x`
    have hstep : ∀ ω, (if EvS (insert x S) v ω then (1 : ℝ) else 0) * g (force (insert x S) v ω) =
        (if ω x = v x then (1 : ℝ) else 0) *
          ((if EvS S v ω then (1 : ℝ) else 0) * g (force (insert x S) v ω)) := by
      intro ω
      have : EvS (insert x S) v ω ↔ ω x = v x ∧ EvS S v ω := by
        unfold EvS; simp [Finset.mem_insert]
      by_cases h1 : ω x = v x <;> by_cases h2 : EvS S v ω <;> simp [this, h1, h2]
    simp_rw [hstep]
    rw [sum_ind_mul p x (v x)]
    swap
    · intro ω b
      rw [force_update_of_mem (Finset.mem_insert_self x S)]
      simp only [evS_update_of_not_mem hx]
    -- step 2: apply the induction hypothesis with `g ∘ update · x (v x)`
    have hcomp : ∀ ω, g (force (insert x S) v ω) =
        (fun ω' => g (Function.update ω' x (v x))) (force S v ω) := by
      intro ω; rw [force_insert hx]
    simp_rw [hcomp]
    rw [ih (fun ω' => g (Function.update ω' x (v x)))]
    simp only [piS, Finset.prod_insert hx]
    ring

/-- **Forced-insertion counting.** `Surv a ω`: the copy of opportunity `a` survives in the run of
coin vector `ω` (meaningful when the opportunity is realized, `EvS (S a) (v a) ω`). If in every run
at most `P` realized opportunities have surviving copies, then the opportunity-weighted
probabilities that a forced copy survives sum to at most `P`. -/
theorem forced_count {α : Type*} [Fintype α] (p : ι → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∀ x, p x ≤ 1) (S : α → Finset ι) (v : α → ι → Bool)
    (Surv : α → (ι → Bool) → Prop) [∀ a ω, Decidable (Surv a ω)] (P : ℝ)
    (hcap : ∀ ω, (#{a | EvS (S a) (v a) ω ∧ Surv a ω} : ℝ) ≤ P) :
    ∑ a, piS p (S a) (v a) *
      ∑ ω, wtv p ω * (if Surv a (force (S a) (v a) ω) then (1 : ℝ) else 0) ≤ P := by
  have hc : ∀ (Q : α → Prop) [DecidablePred Q],
      (#{a | Q a} : ℝ) = ∑ a, (if Q a then (1 : ℝ) else 0) := by
    intro Q _
    rw [Finset.card_filter]; push_cast; rfl
  calc ∑ a, piS p (S a) (v a) *
        ∑ ω, wtv p ω * (if Surv a (force (S a) (v a) ω) then (1 : ℝ) else 0)
      = ∑ a, ∑ ω, wtv p ω * ((if EvS (S a) (v a) ω then (1 : ℝ) else 0) *
          (if Surv a (force (S a) (v a) ω) then (1 : ℝ) else 0)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sum_event_force p (S a) (v a) (fun ω => if Surv a ω then (1 : ℝ) else 0)]
    _ = ∑ a, ∑ ω, wtv p ω * (if EvS (S a) (v a) ω ∧ Surv a ω then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ω _ => ?_
        by_cases h : EvS (S a) (v a) ω
        · rw [force_eq_self h, if_pos h, one_mul]
          by_cases hs : Surv a ω
          · rw [if_pos hs, if_pos ⟨h, hs⟩]
          · rw [if_neg hs, if_neg (fun hh => hs hh.2)]
        · rw [if_neg h, if_neg (show ¬(EvS (S a) (v a) ω ∧ Surv a ω) from fun hh => h hh.1),
            zero_mul]
    _ = ∑ ω, wtv p ω * (#{a | EvS (S a) (v a) ω ∧ Surv a ω} : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [hc, Finset.mul_sum]
    _ ≤ ∑ ω, wtv p ω * P :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hcap ω) (wtv_nonneg hp0 hp1 ω)
    _ = P := by rw [← Finset.sum_mul, sum_wtv, one_mul]

/-- **Expected number of bad opportunities.** If every opportunity has probability at least
`π > 0`, the expected number of opportunities whose forced copy would survive is at most `P / π`. -/
theorem forced_count_card {α : Type*} [Fintype α] (p : ι → ℝ) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∀ x, p x ≤ 1) (S : α → Finset ι) (v : α → ι → Bool)
    (Surv : α → (ι → Bool) → Prop) [∀ a ω, Decidable (Surv a ω)] (P π : ℝ) (hπ : 0 < π)
    (hpi : ∀ a, π ≤ piS p (S a) (v a))
    (hcap : ∀ ω, (#{a | EvS (S a) (v a) ω ∧ Surv a ω} : ℝ) ≤ P) :
    ∑ ω, wtv p ω * (#{a | Surv a (force (S a) (v a) ω)} : ℝ) ≤ P / π := by
  rw [le_div_iff₀ hπ]
  have hc : ∀ ω, (#{a | Surv a (force (S a) (v a) ω)} : ℝ) =
      ∑ a, (if Surv a (force (S a) (v a) ω) then (1 : ℝ) else 0) := by
    intro ω
    rw [Finset.card_filter]; push_cast; rfl
  have hmain := forced_count p hp0 hp1 S v Surv P hcap
  calc (∑ ω, wtv p ω * (#{a | Surv a (force (S a) (v a) ω)} : ℝ)) * π
      = ∑ a, π * ∑ ω, wtv p ω * (if Surv a (force (S a) (v a) ω) then (1 : ℝ) else 0) := by
        simp_rw [hc, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ ∑ a, piS p (S a) (v a) *
          ∑ ω, wtv p ω * (if Surv a (force (S a) (v a) ω) then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hpi a) ?_
        exact Finset.sum_nonneg fun ω _ =>
          mul_nonneg (wtv_nonneg hp0 hp1 ω) (by split_ifs <;> norm_num)
    _ ≤ P := hmain

/-- P0034's uniform coins are the special case `p x = q`. -/
theorem wt_eq_wtv (q : ℝ) (ω : ι → Bool) : Pool.P0034.wt q ω = wtv (fun _ => q) ω := by
  unfold Pool.P0034.wt wtv cw; rfl

/-- **Single-coin form with P0034's uniform coins.** Opportunity `a` is the coin `a` itself
(`ι = α`): "the best arm is inserted at `a`" with probability `q`. Forcing sets coin `a` to
`true`. Then `q · E[#{a : the copy forced at a survives}] ≤ P`. -/
theorem forced_count_uniform (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (Surv : ι → (ι → Bool) → Prop) [∀ a ω, Decidable (Surv a ω)] (P : ℝ)
    (hcap : ∀ ω, (#{a | ω a = true ∧ Surv a ω} : ℝ) ≤ P) :
    q * ∑ ω, Pool.P0034.wt q ω * (#{a | Surv a (Function.update ω a true)} : ℝ) ≤ P := by
  have hforce : ∀ (a : ι) (ω : ι → Bool),
      force {a} (fun _ => true) ω = Function.update ω a true := by
    intro a ω; funext y
    by_cases hy : y = a
    · subst hy; simp [force]
    · simp [force, hy, Function.update_of_ne hy]
  have hev : ∀ (a : ι) (ω : ι → Bool), EvS {a} (fun _ => true) ω ↔ ω a = true := by
    intro a ω; simp [EvS]
  have hcap' : ∀ ω, (#{a | EvS {a} (fun _ => true) ω ∧ Surv a ω} : ℝ) ≤ P := by
    intro ω
    simp only [hev]
    exact hcap ω
  have hmain := forced_count (fun _ => q) (fun _ => hq0) (fun _ => hq1) (fun a => {a})
    (fun _ _ => true) Surv P hcap'
  have hpi : ∀ a : ι, piS (fun _ => q) {a} (fun _ => true) = q := by
    intro a; simp [piS, cw]
  simp only [hpi, hforce] at hmain
  have hc : ∀ ω, (#{a | Surv a (Function.update ω a true)} : ℝ) =
      ∑ a, (if Surv a (Function.update ω a true) then (1 : ℝ) else 0) := by
    intro ω
    rw [Finset.card_filter]; push_cast; rfl
  simp_rw [wt_eq_wtv, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  simpa [Finset.mul_sum] using hmain

/-- **Non-vacuity check.** On `Fin m`, let a copy survive iff no later coin is true
(`Surv a ω :⇔ ∀ b > a, ω b = false`), so among the inserted copies (`ω a = true`) only the latest
survives. The capacity hypothesis of `forced_count_uniform` holds with `P = 1`, so
`q · E[#{a : no coin after a is true}] ≤ 1`. -/
theorem lastSurvivor_cap (m : ℕ) (ω : Fin m → Bool) :
    (#{a | ω a = true ∧ ∀ b, a < b → ω b = false} : ℝ) ≤ 1 := by
  have : #{a | ω a = true ∧ ∀ b, a < b → ω b = false} ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rcases lt_trichotomy a b with h | h | h
    · have := ha.2 b h; rw [hb.1] at this; exact absurd this (by decide)
    · exact h
    · have := hb.2 a h; rw [ha.1] at this; exact absurd this (by decide)
  exact_mod_cast this

theorem lastSurvivor_count (m : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    q * ∑ ω : Fin m → Bool, Pool.P0034.wt q ω *
      (#{a | ∀ b, a < b → Function.update ω a true b = false} : ℝ) ≤ 1 :=
  forced_count_uniform q hq0 hq1 (fun a ω => ∀ b, a < b → ω b = false) 1
    (lastSurvivor_cap m)

end Pool.P0048
