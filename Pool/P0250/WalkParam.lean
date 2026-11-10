import Pool.P0242.ActOcc
import Pool.P0250.AlgExp

/-!
# A concrete walk-shape parameter family for P0186's walk (widths `A + B·√m`), and ALG's term in expectation

Part 1 (deterministic): the family `f(m) = A + B√m`, `a j = A/Bt j + B/√(Bt j)`, `c = A + B√(Bt(D−1))`, `w = wP` (thread-dependent)
satisfies P0186's walk-shape conditions (`hbig_P`, `hsmall_P`, `hw_P`, `hfB_P`), and the walk's right-hand side is
`≤ T·(A/Bt 0 + B/√(Bt 0)) + walkW` with the per-thread weight `walkW = Σ_{1≤j<D} ρ(A + B√(Bt j))·nBad_{j−1} +
(A + B√(Bt(D−1)))·nBad_{D−1}` (`rhs_le_thread`). With P0222's `Wocc ≤ W0 + W1√m` (`Wocc_le`),
P0242's per-run bound holds with every shape hypothesis discharged (`run_bound_param`).

Part 2 (expectation, fixed sampling/filter bits): P0234's `algTerm` for P0225's `withAlgG` is bounded by `wE` times the
expected walk bound plus `wE·T·P(¬GoodAll)` (`alg_expect_param`), with `P(¬GoodAll)` bounded by a union bound
(`prob_not_goodAll`; the two no-overflow events stay explicit), combined in `alg_expect_final`.
-/

namespace Pool.P0250

open Finset Real Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0231 Pool.P0242
open Pool.P0226 (sum_trunc αT αT_nonneg widV_mono2 widV_nonneg gT)

/-- The record cost `A + B·√m`. -/
noncomputable def ffP (A B : ℝ) (m : ℕ) : ℝ := A + B * √(m : ℝ)

/-- The per-round rate of thread `j`: `A/Bt j + B/√(Bt j)`. -/
noncomputable def aaP (A B : ℝ) (Bt : ℕ → ℕ) (j : ℕ) : ℝ := A / (Bt j : ℝ) + B / √(Bt j : ℝ)

/-- The finest-record cost: `A + B·√(Bt (D−1))`. -/
noncomputable def ccP (A B : ℝ) (Bt : ℕ → ℕ) (D : ℕ) : ℝ := A + B * √(Bt (D - 1) : ℝ)

/-- The THREAD-DEPENDENT rule-margin budget `w i`: exactly P0186's `hw` left side for thread `i` (the weights of the
threads finer than `i` and the finest-record cost). For a fine thread it only contains fine-scale terms. -/
noncomputable def wP (A B : ℝ) (Bt : ℕ → ℕ) (D : ℕ) (i : ℕ) : ℝ :=
  ∑ j ∈ Ico 1 D, (if i ≤ j - 1 then (Bt (j - 1) : ℝ) * aaP A B Bt j else 0) +
    (if i ≤ D - 1 then ccP A B Bt D else 0)

variable {A B : ℝ} {Bt : ℕ → ℕ} {D : ℕ}

theorem aaP_nonneg (hA : 0 ≤ A) (hB : 0 ≤ B) (j : ℕ) : 0 ≤ aaP A B Bt j := by
  unfold aaP; positivity

theorem ccP_nonneg (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ ccP A B Bt D := by
  unfold ccP; positivity

/-- P0186's `hbig` for this family: for `m ≥ Bt j > 0`, `A + B√m ≤ m·(A/Bt j + B/√(Bt j))`. -/
theorem hbig_P (hA : 0 ≤ A) (hB : 0 ≤ B) (hpos : ∀ j, 0 < Bt j) (j m : ℕ) (hm : Bt j ≤ m) :
    ffP A B m ≤ m * aaP A B Bt j := by
  unfold ffP aaP
  have hb : (0 : ℝ) < Bt j := by exact_mod_cast hpos j
  have hbm : (Bt j : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hb hbm
  have hsb : 0 < √(Bt j : ℝ) := Real.sqrt_pos.2 hb
  have hsm : √(Bt j : ℝ) ≤ √(m : ℝ) := Real.sqrt_le_sqrt hbm
  have h1 : A ≤ m * (A / Bt j) := by
    rw [mul_div_assoc', le_div_iff₀ hb]; nlinarith
  have hmm : √(m : ℝ) * √(m : ℝ) = (m : ℝ) := Real.mul_self_sqrt hm0.le
  have h2 : B * √(m : ℝ) ≤ m * (B / √(Bt j : ℝ)) := by
    rw [mul_div_assoc', le_div_iff₀ hsb]
    have h0 : 0 ≤ √(m : ℝ) := Real.sqrt_nonneg _
    have h3 := mul_le_mul_of_nonneg_left hsm (mul_nonneg hB h0)
    calc B * √(m : ℝ) * √(Bt j : ℝ) ≤ B * √(m : ℝ) * √(m : ℝ) := h3
      _ = (√(m : ℝ) * √(m : ℝ)) * B := by ring
      _ = m * B := by rw [hmm]
  rw [mul_add]; linarith

/-- P0186's `hsmall` for this family. -/
theorem hsmall_P (hB : 0 ≤ B) (m : ℕ) (hm : m < Bt (D - 1)) : ffP A B m ≤ ccP A B Bt D := by
  unfold ffP ccP
  have : √(m : ℝ) ≤ √(Bt (D - 1) : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hm.le)
  nlinarith

/-- P0186's `hw` for this family (with equality: `w i` is thread `i`'s left side). -/
theorem hw_P (i : ℕ) :
    ∑ j ∈ Ico 1 D, (if i ≤ j - 1 then (Bt (j - 1) : ℝ) * aaP A B Bt j else 0) +
      (if i ≤ D - 1 then ccP A B Bt D else 0) ≤ wP A B Bt D i := le_rfl

/-- Per-thread walk weight: `Bt(j−1)·a_j ≤ ρ·(A + B·√(Bt j))` when `Bt(j−1) ≤ ρ·Bt j`. -/
theorem weight_le (hA : 0 ≤ A) (hB : 0 ≤ B) (hpos : ∀ j, 0 < Bt j) {ρ : ℝ} {j : ℕ}
    (hr : (Bt (j - 1) : ℝ) ≤ ρ * Bt j) :
    (Bt (j - 1) : ℝ) * aaP A B Bt j ≤ ρ * (A + B * √(Bt j : ℝ)) := by
  have hb : (0 : ℝ) < Bt j := by exact_mod_cast hpos j
  have hsb : 0 < √(Bt j : ℝ) := Real.sqrt_pos.2 hb
  unfold aaP
  rw [mul_add]
  have e1 : (Bt (j - 1) : ℝ) * (A / Bt j) ≤ ρ * A := by
    rw [mul_div_assoc', div_le_iff₀ hb]; nlinarith
  have hss : (Bt j : ℝ) = √(Bt j : ℝ) * √(Bt j : ℝ) := (Real.mul_self_sqrt hb.le).symm
  have e2 : (Bt (j - 1) : ℝ) * (B / √(Bt j : ℝ)) ≤ ρ * (B * √(Bt j : ℝ)) := by
    rw [mul_div_assoc', div_le_iff₀ hsb]
    have : (Bt (j - 1) : ℝ) * B ≤ ρ * (√(Bt j : ℝ) * √(Bt j : ℝ)) * B := by
      rw [← hss]; exact mul_le_mul_of_nonneg_right hr hB
    nlinarith
  nlinarith

/-- The per-thread bad-epoch weight of the walk: `Σ_{1≤j<D} ρ(A + B√(Bt j))·nb(j−1) + (A + B√(Bt(D−1)))·nb(D−1)`. -/
noncomputable def walkW (A B : ℝ) (Bt : ℕ → ℕ) (D : ℕ) (ρ : ℝ) (nb : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Ico 1 D, ρ * (A + B * √(Bt j : ℝ)) * nb (j - 1) + ccP A B Bt D * nb (D - 1)

theorem walkW_nonneg (hA : 0 ≤ A) (hB : 0 ≤ B) {ρ : ℝ} (hρ : 0 ≤ ρ) (nb : ℕ → ℝ) (hnb : ∀ j, 0 ≤ nb j) :
    0 ≤ walkW A B Bt D ρ nb := by
  unfold walkW
  have := ccP_nonneg (Bt := Bt) (D := D) hA hB
  have := hnb (D - 1)
  refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) (by positivity)
  have := hnb (j - 1); positivity

/-- **The walk right-hand side for this family, per thread.** With `Bt (j−1) ≤ ρ·Bt j` and any counts `nb ≥ 0`:
`T·aa 0 + Σ_{1≤j<D} Bt(j−1)·nb(j−1)·aa j + nb(D−1)·cc ≤ T·(A/Bt 0 + B/√(Bt 0)) + walkW` (each bad epoch start of
thread `j−1` is charged at thread `j`'s scale `ρ(A + B√(Bt j))`, not at the coarsest scale). -/
theorem rhs_le_thread (hA : 0 ≤ A) (hB : 0 ≤ B) (hpos : ∀ j, 0 < Bt j) {ρ : ℝ}
    (hρ : ∀ j, 1 ≤ j → (Bt (j - 1) : ℝ) ≤ ρ * Bt j) (T : ℝ) (nb : ℕ → ℝ) (hnb : ∀ j, 0 ≤ nb j) :
    T * aaP A B Bt 0 + ∑ j ∈ Ico 1 D, (Bt (j - 1) : ℝ) * nb (j - 1) * aaP A B Bt j + nb (D - 1) * ccP A B Bt D ≤
      T * (A / Bt 0 + B / √(Bt 0 : ℝ)) + walkW A B Bt D ρ nb := by
  unfold walkW
  have hsum : ∑ j ∈ Ico 1 D, (Bt (j - 1) : ℝ) * nb (j - 1) * aaP A B Bt j ≤
      ∑ j ∈ Ico 1 D, ρ * (A + B * √(Bt j : ℝ)) * nb (j - 1) :=
    Finset.sum_le_sum fun j hj => by
      simp only [Finset.mem_Ico] at hj
      have h := weight_le hA hB hpos (hρ j hj.1)
      have := hnb (j - 1)
      nlinarith
  have h0 : T * aaP A B Bt 0 = T * (A / Bt 0 + B / √(Bt 0 : ℝ)) := rfl
  have hl : nb (D - 1) * ccP A B Bt D = ccP A B Bt D * nb (D - 1) := mul_comm _ _
  linarith

/-- P0186's `hfB` for this family under `Bt (D − 1) = 1` (P0065's `BtHyp`) and `1 ≤ A + B`. -/
theorem hfB_P (hlast : Bt (D - 1) = 1) (h1 : 1 ≤ A + B) :
    (1 : ℝ) * Bt (D - 1) ≤ ffP A B (Bt (D - 1)) := by
  unfold ffP; rw [hlast]; simp; linarith

/-- `√(a + b) ≤ √a + √b` for `a, b ≥ 0`. -/
theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt ha; have := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- P0222's `Wocc` is at most `W0 + W1·√m` with `W0 = 2L/xmin + 2√(L·Θ·(ρT/n))`, `W1 = 2√(L·M)`. -/
theorem Wocc_le {Ls xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ Ls) (hM : 0 ≤ M) (hΘ : 0 ≤ Θ * (ρ * TT / nn)) (m : ℕ) :
    Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m ≤
      (2 * Ls / xmin + 2 * √(Ls * (Θ * (ρ * TT / nn)))) + 2 * √(Ls * M) * √(m : ℝ) := by
  unfold Pool.P0222.Wocc
  have e : Ls * ((m : ℝ) * M + Θ * (ρ * TT / nn)) = Ls * M * m + Ls * (Θ * (ρ * TT / nn)) := by ring
  rw [e]
  have h := sqrt_add_le' (mul_nonneg (mul_nonneg hL hM) (Nat.cast_nonneg m)) (mul_nonneg hL hΘ)
  rw [Real.sqrt_mul (mul_nonneg hL hM)] at h
  linarith

/-- Averaging a good-event bound `C + K·nb + V` (with `C, K, nb ≥ 0`). -/
theorem split_good {α : Type} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (nb : α → ℝ) (hnb : ∀ a, 0 ≤ nb a) (V : α → ℝ) (Gd : α → Prop) [DecidablePred Gd] :
    ∑ a, w a * (if Gd a then C + K * nb a + V a else 0) ≤
      C + K * ∑ a, w a * nb a + ∑ a, w a * (if Gd a then V a else 0) := by
  have hpt : ∀ a, w a * (if Gd a then C + K * nb a + V a else 0) ≤
      w a * C + K * (w a * nb a) + w a * (if Gd a then V a else 0) := by
    intro a
    split_ifs
    · ring_nf; exact le_rfl
    · have := mul_nonneg (hw a) hC
      have := mul_nonneg hK (mul_nonneg (hw a) (hnb a))
      simp only [mul_zero, add_zero]; linarith
  calc _ ≤ ∑ a, (w a * C + K * (w a * nb a) + w a * (if Gd a then V a else 0)) := Finset.sum_le_sum fun a _ => hpt a
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul, ← Finset.mul_sum]

section Param

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (Pool.P0225.withAlgG P η L N G γ wE ρG).K → ι → Bool) (T : ℕ)
  (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

local notation "QQ" => Pool.P0225.withAlgG P η L N G γ wE ρG

/-- The constant part `A` of the record cost: `θ + R·(2α + 2Γ) + (R+1)·W0 + Lt/κ` with `Γ = Lc/(2wEγ)` (P0186's IX
constant) and `W0 = 2Ls/xmin + 2√(Ls·Θ·(ρT/n))` (the length-free part of P0222's `Wocc`). -/
noncomputable def AP (T : ℕ) (δ Ls Lc Lt κ xmin M ρ nn TT Θ : ℝ) : ℝ :=
  (QQ).θ + (QQ).R * (2 * αT (ι := ι) η L T δ + 2 * (Lc / (2 * (wE * γ)))) +
    ((QQ).R + 1) * (2 * Ls / xmin + 2 * √(Ls * (Θ * (ρ * TT / nn)))) + Lt / κ

/-- The `√`-part `B` of the record cost: `(R+1)·2√(Ls·M)`. -/
noncomputable def BP (Ls M : ℝ) : ℝ := ((QQ).R + 1) * (2 * √(Ls * M))

/-- The rule margins `Λ'` that this family needs (P0186's `hΛ` with equality; `w = wP`, thread-dependent). -/
noncomputable def ΛP (T : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ) (j m : ℕ) : ℝ :=
  Lt / κ + αT (ι := ι) η L T δ + Lc / (2 * (wE * γ)) + 0 +
    Pool.P0158.widV (m * (QQ).cB) (max 1 (QQ).cB) Lb + Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m +
    wP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D j

/-- The number of bad epoch starts of thread `j` (P0135's `nBadB` for P0242's run, as in `run_bound_occ`). -/
noncomputable def nbad (cstar : ℕ → ℕ → ι) (j : ℕ) : ℝ :=
  (Pool.P0135.nBadB T (QQ).Bt (fun τ r => Pool.P0186.outMix (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
    (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (QQ) ℓ) (rhD (QQ) ℓ ω) (QQ).lay (zc (QQ) ω)) ∅
    (fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (QQ) ℓ) (rhD (QQ) ℓ ω) (Pool.P0176.lastLay (QQ).sl c')
      (zc (QQ) ω))
    (fun _ => ∅) ((QQ).D - 1) T ωs φ (cstar r τ)) j : ℝ)

/-- **P0242's per-run bound with every walk-shape hypothesis discharged** by the family `f(m) = A + B√m`,
`a j = A/Bt j + B/√(Bt j)`, `c = A + B√(Bt(D−1))`, `w i = wP i` (thread-dependent), `Λ' = ΛP` (the rule margins must
dominate `ΛP` at the copy's thread, `hΛ'`):
on the good events,
`Σ_{u<T} (aPt − ℓ_u(i) − ((η/2)·VR + slT)) ≤ T·(A/Bt 0 + B/√(Bt 0)) + walkW(nBad)` (per-thread weights). -/
theorem run_bound_param (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    (hL : (Pool.P0225.withAlgG P η L N G γ wE ρG).IsLaw) (hN : 0 < (Pool.P0225.withAlgG P η L N G γ wE ρG).N) (hη : 0 < η) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρG : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)
    {Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).xr j)
    (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hBt0 : ∀ i, 0 < (QQ).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((QQ).Bt (i - 1) : ℝ) ≤ ρ * (QQ).Bt i) (hx0 : 1 / Pool.P0191.xrN (QQ).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QQ).xr i ≤ max M (TT / (nn * (QQ).Bt i)))
    (hΘ : ∀ f, ((QQ).thr0 f : ℝ) ≤ Θ)
    (hlay : (Pool.P0225.withAlgG P η L N G γ wE ρG).lay = Pool.P0176.sortLay (Pool.P0225.withAlgG P η L N G γ wE ρG).sl)
    (hS : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ rc0 f)
      (Pool.P0203.gateS (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ rc0 f) (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) f)
      (Pool.P0158.rmax1 (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl
      (sp (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u))
    (hB : Pool.P0158.GoodV (Pool.P0216.DB (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ rc0) (fun _ _ => true)
      (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) (Pool.P0158.rmax1 (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)) Lb T
      (Pool.P0203.pre _ ω T))
    (hX : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN) (lossX P η L N G γ wE ρG ℓ x)
      (obsX P η L N G γ wE ρG ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρG ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (hXm : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN)
      (YB P η L N G γ wE ρG ℓ rc0) (bPolX P η L N G γ wE ρG ℓ rc0) (obsX P η L N G γ wE ρG ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (hA : Pool.P0149.StepGood (Pool.P0240.DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lt / κ) T
      (Pool.P0203.pre _ ω T))
    (hθ : 0 ≤ (QQ).θ) (hR1 : 1 ≤ (QQ).R) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hT : (QQ).Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    (i : Fin n) (harm : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).arm (cstar j a) = i)
    (hgF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false →
      Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.gateS (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a))
        (Pool.P0158.rmax1 (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a))) Ls T
        (Pool.P0203.pre (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ω T))
    (hfF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false → ∀ u, u < T →
      Pool.P0176.Fits (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl
        (sp (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ ω (Pool.P0065.forceS ωs (cstar j a))
          (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) u))
    (hΛ' : ∀ c u, ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ
        (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤ (QQ).Λ c u)
    (hTΘ : 0 ≤ Θ * (ρ * TT / nn))
    (h1 : 1 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ + BP P η L N G γ wE ρG Ls M) :
    ∑ u ∈ Finset.range T, (aPt P η L N G γ wE ρG ℓ ω ωs φ T u - gT ℓ T i u -
        (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ ω ωs φ T u + slT P η L N G γ wE ρG ℓ ω ωs φ T rc0 κ u)) ≤
      T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 +
          BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) +
        walkW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ρ
            (fun j => nbad P η L N G γ wE ρG ℓ ω ωs φ T cstar j) := by
  have hR0 : (0 : ℝ) ≤ (QQ).R := by have : (1 : ℝ) ≤ (QQ).R := by exact_mod_cast hR1
                                    linarith
  have hα := αT_nonneg (ι := ι) η L T hη hδ
  have hΓ : 0 ≤ Lc / (2 * (wE * γ)) := div_nonneg hLc (by positivity)
  have hA0 : 0 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ := by
    unfold AP; have : 0 ≤ Lt / κ := div_nonneg hLt hκ.le
    have : 0 ≤ 2 * Ls / xmin := div_nonneg (by linarith) hxm.le
    positivity
  have hB0 : 0 ≤ BP P η L N G γ wE ρG Ls M := by unfold BP; positivity
  have hf : ∀ m : ℕ, (QQ).θ + (QQ).R * (2 * αT (ι := ι) η L T δ + 2 * (Lc / (2 * (wE * γ))) +
      Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m) + Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m + Lt / κ ≤
      ffP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) m := by
    intro m
    have hW := Wocc_le (xmin := xmin) (ρ := ρ) (nn := nn) (TT := TT) hLs hM hTΘ m
    unfold ffP AP BP
    nlinarith
  have H := run_bound_occ P η L N G γ wE ρG ℓ ω ωs φ T rc0 hD hLv hlev hL hN hη hδ hρG hγ hwE0 hwE hTL hcB0 hLs hLb
    hLc hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hlay hS hfit hB hX hXm hA hθ hR1 hBt hT cstar hE hthr i
    harm hgF hfF (ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ) hΛ'
    (ffP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M))
    (aaP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt)
    (ccP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D)
    (fun j => wP (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D j)
    (fun j _ => aaP_nonneg hA0 hB0 j) (ccP_nonneg hA0 hB0)
    (fun j _ m hm => hbig_P hA0 hB0 hBt.pos j m hm) (fun m hm => hsmall_P hB0 m hm) hf
    (hfB_P hBt.last (by exact h1)) (fun j m => le_rfl) (fun i' _ => hw_P i')
  refine H.trans ?_
  exact rhs_le_thread hA0 hB0 hBt.pos hρ (T : ℝ) _ (fun j => Nat.cast_nonneg _)

/-- **All good events of `run_bound_param`** on a full coin sequence `ω` (horizon `T`): P0203's slot event and
no overflow, P0216's B̂ event, P0231's IX events (copies and meta-arm), P0240's `DT` event, and P0218's slot event and
no overflow for the forced runs of unsampled comparator copies `cstar j a`. -/
def GoodAll (hL : (QQ).IsLaw) (hN : 0 < (QQ).N) (Ls Lb Lc Lt κ : ℝ) (cstar : ℕ → ℕ → ι)
    (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) : Prop :=
    (∀ f, Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ rc0 f)
      (Pool.P0203.gateS (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ωs φ rc0 f) (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) f)
      (Pool.P0158.rmax1 (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) f)) Ls T (Pool.P0203.pre _ ω T)) ∧
    (∀ u, u < T → Pool.P0176.Fits (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl
      (sp (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ ω ωs φ u)) ∧
    (Pool.P0158.GoodV (Pool.P0216.DB (Pool.P0225.withAlgG P η L N G γ wE ρG) ℓ rc0) (fun _ _ => true)
      (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB) (Pool.P0158.rmax1 (fun _ => (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)) Lb T
      (Pool.P0203.pre _ ω T)) ∧
    (∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN) (lossX P η L N G γ wE ρG ℓ x)
      (obsX P η L N G γ wE ρG ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρG ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T)) ∧
    (Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (Pool.P0225.withAlgG P η L N G γ wE ρG) hL hN)
      (YB P η L N G γ wE ρG ℓ rc0) (bPolX P η L N G γ wE ρG ℓ rc0) (obsX P η L N G γ wE ρG ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T)) ∧
    (Pool.P0149.StepGood (Pool.P0240.DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lt / κ) T
      (Pool.P0203.pre _ ω T)) ∧
    (∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false →
      Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.gateS (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a))
        (Pool.P0158.rmax1 (Pool.P0203.rS (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a))) Ls T
        (Pool.P0203.pre (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ω T)) ∧
    (∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false → ∀ u, u < T →
      Pool.P0176.Fits (Pool.P0225.withAlgG P η L N G γ wE ρG).Lv (Pool.P0225.withAlgG P η L N G γ wE ρG).sl
        (sp (Pool.P0218.PL (Pool.P0225.withAlgG P η L N G γ wE ρG) (cstar j a)) ℓ ω (Pool.P0065.forceS ωs (cstar j a))
          (Pool.P0065.forceF (Pool.P0225.withAlgG P η L N G γ wE ρG).K φ (cstar j a)) u))

open Classical in
/-- **ALG's term in expectation** (fixed sampling/filter bits; P0234's `algTerm`, i.e. P0217's `algT` integrand form):
with the parameter family of `run_bound_param`,
`algTerm ≤ wE·E[[G]·(T·(A/Bt 0 + B/√(Bt 0)) + walkW(nBad) + Σ_{u<T} V_u)] + wE·T·P(¬G)`,
`V = (η/2)·VR + slT`, `G = GoodAll`. -/
theorem alg_expect_param (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    (hL : (Pool.P0225.withAlgG P η L N G γ wE ρG).IsLaw) (hN : 0 < (Pool.P0225.withAlgG P η L N G γ wE ρG).N) (hη : 0 < η) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρG : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)
    {Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).xr j)
    (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hBt0 : ∀ i, 0 < (QQ).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((QQ).Bt (i - 1) : ℝ) ≤ ρ * (QQ).Bt i) (hx0 : 1 / Pool.P0191.xrN (QQ).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QQ).xr i ≤ max M (TT / (nn * (QQ).Bt i)))
    (hΘ : ∀ f, ((QQ).thr0 f : ℝ) ≤ Θ)
    (hlay : (Pool.P0225.withAlgG P η L N G γ wE ρG).lay = Pool.P0176.sortLay (Pool.P0225.withAlgG P η L N G γ wE ρG).sl)
    (hθ : 0 ≤ (QQ).θ) (hR1 : 1 ≤ (QQ).R) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hT : (QQ).Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    (i : Fin n) (harm : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).arm (cstar j a) = i)
    (hΛ' : ∀ c u, ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ
        (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤ (QQ).Λ c u)
    (hTΘ : 0 ≤ Θ * (ρ * TT / nn))
    (h1 : 1 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ + BP P η L N G γ wE ρG Ls M) :
    Pool.P0234.algTerm (QQ) ℓ ωs φ rc0 T i ≤
      wE * ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
        (if GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω) then
          T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 +
              BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) +
            walkW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ρ
            (fun j => nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T cstar j) +
            ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
              slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u) else 0) +
      wE * T * ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
        (if GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) := by
  have hwQ : (QQ).wE = wE := hwE
  have h := alg_expect_of (QQ) ℓ ωs φ rc0 hL hN (by rw [hwQ]; exact hwE0.le) T i
    (fun ω => GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω))
    (fun ω => T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 +
                  BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) +
                walkW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ρ
            (fun j => nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T cstar j) +
                ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
                  slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u)) ?_
  · rw [hwQ] at h; exact h
  intro ω hg
  obtain ⟨hS, hfit, hB, hX, hXm, hA, hgF, hfF⟩ := hg
  have H := run_bound_param P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 hD hLv hlev hL hN hη hδ hρG hγ
    hwE0 hwE hTL hcB0 hLs hLb hLc hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hlay hS hfit hB hX hXm hA hθ hR1
    hBt hT cstar hE hthr i harm hgF hfF hΛ' hTΘ h1
  have e : ∑ u ∈ Finset.range T, (aPt P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u - gT ℓ T i u -
        (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
          slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u)) =
      ∑ u ∈ Finset.range T, (aPol (QQ) ℓ ωs φ (Pool.P0210.extR (QQ) rc0 ω) u - ((ℓ u i).toNat : ℝ)) -
        ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
          slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' : u < T := Finset.mem_range.1 hu
    unfold aPt gT; rw [if_pos hu', if_pos hu']
  rw [e] at H
  linarith

/-- No overflow of the actual run before `T` (kept as an explicit event). -/
def FitA (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) : Prop :=
  ∀ u, u < T → Pool.P0176.Fits (QQ).Lv (QQ).sl (sp (QQ) ℓ ω ωs φ u)

/-- No overflow of the forced runs of the unsampled comparator copies before `T` (kept as an explicit event). -/
def FitF (cstar : ℕ → ℕ → ι) (ω : ℕ → RC (Pool.P0225.withAlgG P η L N G γ wE ρG)) : Prop :=
  ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false → ∀ u, u < T →
    Pool.P0176.Fits (QQ).Lv (QQ).sl
      (sp (Pool.P0218.PL (QQ) (cstar j a)) ℓ ω (Pool.P0065.forceS ωs (cstar j a))
        (Pool.P0065.forceF (QQ).K φ (cstar j a)) u)

open Classical in
/-- **The failure probability of `GoodAll`** (union bound over P0218's slot + forced-run events, P0216's B̂ event,
P0231's IX events, P0240's `DT` event; the two no-overflow events stay explicit): over P0194's round coins,
`P(¬GoodAll) ≤ P(¬FitA) + P(¬FitF) + 4|ι|(T+1)²e^{−Ls} + 2(T+1)²e^{−Lb} + (|ι|+1)(T+1)²e^{−Lc} + (T+1)²e^{−Lt}`. -/
theorem prob_not_goodAll (hL : (QQ).IsLaw) (hN : 0 < (QQ).N) (hD : 0 < P.D) (hLv : 0 < P.Lv)
    (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (hlayOK : Pool.P0191.LayOK (QQ).sl (QQ).lay) (hxr0 : ∀ j, 0 < (QQ).xr j)
    (hxr1 : ∀ j, (QQ).xr j ≤ 1) (hcw : (QQ).cB * (QQ).wB = 1) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE)
    {Ls Lb Lc Lt κ : ℝ} (hLs : 0 < Ls) (hLb : 0 < Lb) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (cstar : ℕ → ℕ → ι) :
    ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
        (if GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) ≤
      ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
          (if FitA P η L N G γ wE ρG ℓ ωs φ T (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) +
        ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
          (if FitF P η L N G γ wE ρG ℓ ωs φ T cstar (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) +
        2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls))) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lb) +
        Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) +
        ((T : ℝ) + 1) ^ 2 * Real.exp (-Lt) := by
  have hp : ∀ ω : Fin T → RC (QQ), 0 ≤ Pool.P0202.pw (wR (QQ)) ω := fun ω => Pool.P0228.pw_nonneg (QQ) hL ω
  have hw := fun {t : ℕ} (ω : Fin t → RC (QQ)) => Pool.P0228.wgt_eq_pw (QQ) hL hN ω
  -- the seven events, on `T`-prefixes
  set E1 : (Fin T → RC (QQ)) → Prop := fun ω =>
    (∀ c, Pool.P0158.GoodV (Pool.P0203.DS (QQ) ℓ ωs φ rc0 c) (Pool.P0203.gateS (QQ) ℓ ωs φ rc0 c)
      (Pool.P0203.rS (QQ) c) (Pool.P0158.rmax1 (Pool.P0203.rS (QQ) c)) Ls T ω) ∧
    (∀ c, Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0218.PL (QQ) c) ℓ (Pool.P0065.forceS ωs c)
        (Pool.P0065.forceF (QQ).K φ c) rc0 c)
      (Pool.P0203.gateS (Pool.P0218.PL (QQ) c) ℓ (Pool.P0065.forceS ωs c) (Pool.P0065.forceF (QQ).K φ c) rc0 c)
      (Pool.P0203.rS (QQ) c) (Pool.P0158.rmax1 (Pool.P0203.rS (QQ) c)) Ls T ω) with hE1
  set E2 : (Fin T → RC (QQ)) → Prop := fun ω =>
    Pool.P0158.GoodV (Pool.P0216.DB (QQ) ℓ rc0) (fun _ _ => true) (fun _ => (QQ).cB)
      (Pool.P0158.rmax1 (fun _ => (QQ).cB)) Lb T ω with hE2
  set E3 : (Fin T → RC (QQ)) → Prop := fun ω =>
    ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (QQ) hL hN) (lossX P η L N G γ wE ρG ℓ x)
      (obsX P η L N G γ wE ρG ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρG ℓ ωs φ rc0 x) Lc T ω with hE3
  set E4 : (Fin T → RC (QQ)) → Prop := fun ω =>
    Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (QQ) hL hN)
      (YB P η L N G γ wE ρG ℓ rc0) (bPolX P η L N G γ wE ρG ℓ rc0) (obsX P η L N G γ wE ρG ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T ω with hE4
  set E5 : (Fin T → RC (QQ)) → Prop := fun ω =>
    Pool.P0149.StepGood (Pool.P0240.DT P η L N G γ wE ρG ℓ ωs φ rc0 κ) (fun _ _ => true) (Lt / κ) T ω with hE5
  set FA : (Fin T → RC (QQ)) → Prop := fun ω => FitA P η L N G γ wE ρG ℓ ωs φ T (Pool.P0210.extR (QQ) rc0 ω)
  set FF : (Fin T → RC (QQ)) → Prop := fun ω => FitF P η L N G γ wE ρG ℓ ωs φ T cstar (Pool.P0210.extR (QQ) rc0 ω)
  -- pointwise: the bad indicator is at most the sum of the seven bad indicators
  have hpt : ∀ ω : Fin T → RC (QQ),
      (if GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω) then (0 : ℝ) else 1) ≤
      (if FA ω then 0 else 1) + (if FF ω then 0 else 1) + (if E1 ω then 0 else 1) + (if E2 ω then 0 else 1) +
        (if E3 ω then 0 else 1) + (if E4 ω then 0 else 1) + (if E5 ω then 0 else 1) := by
    intro ω
    have hpre : Pool.P0203.pre (QQ) (Pool.P0210.extR (QQ) rc0 ω) T = ω := Pool.P0228.pre_extR (QQ) rc0 ω
    by_cases hg : GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω)
    · rw [if_pos hg]; positivity
    · rw [if_neg hg]
      by_contra hcon
      push_neg at hcon
      have h0 : ∀ (p : Prop) [Decidable p], (0 : ℝ) ≤ if p then 0 else 1 := fun p _ => by split_ifs <;> norm_num
      have k1 : FA ω := by by_contra h; rw [if_neg h] at hcon; linarith [h0 (FF ω), h0 (E1 ω), h0 (E2 ω), h0 (E3 ω), h0 (E4 ω), h0 (E5 ω)]
      have k2 : FF ω := by by_contra h; rw [if_neg h] at hcon; linarith [h0 (FA ω), h0 (E1 ω), h0 (E2 ω), h0 (E3 ω), h0 (E4 ω), h0 (E5 ω)]
      have k3 : E1 ω := by by_contra h; rw [if_neg h] at hcon; linarith [h0 (FA ω), h0 (FF ω), h0 (E2 ω), h0 (E3 ω), h0 (E4 ω), h0 (E5 ω)]
      have k4 : E2 ω := by by_contra h; rw [if_neg h] at hcon; linarith [h0 (FA ω), h0 (FF ω), h0 (E1 ω), h0 (E3 ω), h0 (E4 ω), h0 (E5 ω)]
      have k5 : E3 ω := by by_contra h; rw [if_neg h] at hcon; linarith [h0 (FA ω), h0 (FF ω), h0 (E1 ω), h0 (E2 ω), h0 (E4 ω), h0 (E5 ω)]
      have k6 : E4 ω := by by_contra h; rw [if_neg h] at hcon; linarith [h0 (FA ω), h0 (FF ω), h0 (E1 ω), h0 (E2 ω), h0 (E3 ω), h0 (E5 ω)]
      have k7 : E5 ω := by by_contra h; rw [if_neg h] at hcon; linarith [h0 (FA ω), h0 (FF ω), h0 (E1 ω), h0 (E2 ω), h0 (E3 ω), h0 (E4 ω)]
      apply hg
      refine ⟨?_, k1, ?_, ?_, ?_, ?_, ?_, k2⟩
      · rw [hpre]; exact k3.1
      · rw [hpre]; exact k4
      · rw [hpre]; exact k5
      · rw [hpre]; exact k6
      · rw [hpre]; exact k7
      · intro j a _ _ _ _
        have hpre' : Pool.P0203.pre (Pool.P0218.PL (QQ) (cstar j a)) (Pool.P0210.extR (QQ) rc0 ω) T = ω := hpre
        rw [hpre']; exact k3.2 (cstar j a)
  -- the five probability bounds, with `pw` for `wgt`
  have b1 := Pool.P0218.prob_not_goodRec (QQ) ℓ ωs φ hL hN hD hLv hlev hlayOK hxr0 hxr1 rc0 hLs T
  have b2 := Pool.P0216.prob_not_goodB (QQ) ℓ rc0 hL hN hcw hLb T
  have b3 := Pool.P0231.prob_not_ixGood_all P η L N G γ wE ρG ℓ ωs φ rc0 hL hN hγ hwE0 Lc T
  have b4 := Pool.P0231.prob_not_ixGood_meta P η L N G γ wE ρG ℓ ωs φ rc0 hL hN hγ hwE0 Lc T
  have b5 := Pool.P0240.prob_not_goodHT (ℓ := ℓ) (ωs := ωs) (φ := φ) (rc0 := rc0) hL hN hwE hwE0 hγ hκ0 hκ1 Lt T
  simp only [hw] at b1 b2 b3 b4 b5
  set X : (Fin T → RC (QQ)) → ℝ := fun ω => Pool.P0202.pw (wR (QQ)) ω with hX
  have hsplit : ∑ ω : Fin T → RC (QQ), X ω *
        ((if FA ω then 0 else 1) + (if FF ω then 0 else 1) + (if E1 ω then 0 else 1) + (if E2 ω then 0 else 1) +
          (if E3 ω then 0 else 1) + (if E4 ω then 0 else 1) + (if E5 ω then 0 else 1)) =
      ∑ ω, X ω * (if FA ω then 0 else 1) + ∑ ω, X ω * (if FF ω then 0 else 1) + ∑ ω, X ω * (if E1 ω then 0 else 1) +
        ∑ ω, X ω * (if E2 ω then 0 else 1) + ∑ ω, X ω * (if E3 ω then 0 else 1) +
        ∑ ω, X ω * (if E4 ω then 0 else 1) + ∑ ω, X ω * (if E5 ω then 0 else 1) := by
    simp only [mul_add, Finset.sum_add_distrib]
  have hmain : ∑ ω : Fin T → RC (QQ), X ω *
        (if GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) ≤
      ∑ ω : Fin T → RC (QQ), X ω *
        ((if FA ω then 0 else 1) + (if FF ω then 0 else 1) + (if E1 ω then 0 else 1) + (if E2 ω then 0 else 1) +
          (if E3 ω then 0 else 1) + (if E4 ω then 0 else 1) + (if E5 ω then 0 else 1)) :=
    Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hp ω)
  rw [hsplit] at hmain
  have c1 : ∑ ω, X ω * (if E1 ω then 0 else 1) ≤ 2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls))) := by
    refine le_trans (le_of_eq ?_) b1; exact Finset.sum_congr rfl fun ω _ => by congr 1
  have c2 : ∑ ω, X ω * (if E2 ω then 0 else 1) ≤ 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lb) := by
    refine le_trans (le_of_eq ?_) b2; exact Finset.sum_congr rfl fun ω _ => by congr 1
  have c3 : ∑ ω, X ω * (if E3 ω then 0 else 1) ≤ Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) := by
    refine le_trans (le_of_eq ?_) b3; exact Finset.sum_congr rfl fun ω _ => by congr 1
  have c4 : ∑ ω, X ω * (if E4 ω then 0 else 1) ≤ ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) := by
    refine le_trans (le_of_eq ?_) b4; exact Finset.sum_congr rfl fun ω _ => by congr 1
  have c5 : ∑ ω, X ω * (if E5 ω then 0 else 1) ≤ ((T : ℝ) + 1) ^ 2 * Real.exp (-Lt) := by
    refine le_trans (le_of_eq ?_) b5; exact Finset.sum_congr rfl fun ω _ => by congr 1
  linarith

open Classical in
/-- **ALG's term in expectation, final form** (fixed sampling/filter bits): with the family of `run_bound_param`,
`algTerm ≤ wE·(T·(A/Bt 0 + B/√(Bt 0)) + E[walkW(nBad)] + E[[G]·Σ_{u<T} V_u]) + wE·T·(P(¬FitA) + P(¬FitF)
+ 4|ι|(T+1)²e^{−Ls} + 2(T+1)²e^{−Lb} + (|ι|+1)(T+1)²e^{−Lc} + (T+1)²e^{−Lt})`. -/
theorem alg_expect_final (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    (hL : (Pool.P0225.withAlgG P η L N G γ wE ρG).IsLaw) (hN : 0 < (Pool.P0225.withAlgG P η L N G γ wE ρG).N) (hη : 0 < η) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρG : ∀ σ V ch bit, |ρG σ V ch bit| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)
    {Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).xr j)
    (hn : 0 < nn) (hTT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hBt0 : ∀ i, 0 < (QQ).Bt i)
    (hρ : ∀ i, 1 ≤ i → ((QQ).Bt (i - 1) : ℝ) ≤ ρ * (QQ).Bt i) (hx0 : 1 / Pool.P0191.xrN (QQ).xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN (QQ).xr i ≤ max M (TT / (nn * (QQ).Bt i)))
    (hΘ : ∀ f, ((QQ).thr0 f : ℝ) ≤ Θ)
    (hlay : (Pool.P0225.withAlgG P η L N G γ wE ρG).lay = Pool.P0176.sortLay (Pool.P0225.withAlgG P η L N G γ wE ρG).sl)
    (hθ : 0 ≤ (QQ).θ) (hR1 : 1 ≤ (QQ).R) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hT : (QQ).Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    (i : Fin n) (harm : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).arm (cstar j a) = i)
    (hΛ' : ∀ c u, ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ
        (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤ (QQ).Λ c u)
    (hTΘ : 0 ≤ Θ * (ρ * TT / nn))
    (h1 : 1 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ + BP P η L N G γ wE ρG Ls M)
    (hlayOK : Pool.P0191.LayOK (QQ).sl (QQ).lay) (hxr0 : ∀ j, 0 < (QQ).xr j) (hxr1 : ∀ j, (QQ).xr j ≤ 1)
    (hcw : (QQ).cB * (QQ).wB = 1) (hLs0 : 0 < Ls) (hLb0 : 0 < Lb) (hκ1 : κ ≤ 1) :
    Pool.P0234.algTerm (QQ) ℓ ωs φ rc0 T i ≤
      wE * (T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 +
          BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) +
        ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
            walkW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ) (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ρ (fun j => nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T cstar j) +
        ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
          (if GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω) then
            ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
              slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u) else 0)) +
      wE * T * (∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
            (if FitA P η L N G γ wE ρG ℓ ωs φ T (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) +
          ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω *
            (if FitF P η L N G γ wE ρG ℓ ωs φ T cstar (Pool.P0210.extR (QQ) rc0 ω) then 0 else 1) +
          2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Ls))) + 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-Lb) +
          Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) + ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) +
          ((T : ℝ) + 1) ^ 2 * Real.exp (-Lt)) := by
  classical
  have hAP := alg_expect_param P η L N G γ wE ρG ℓ ωs φ T rc0 hD hLv hlev hL hN hη hδ hρG hγ hwE0 hwE hTL hcB0 hLs hLb hLc hLt hκ hxm hxm1 hxr hn hTT hM hρ0 hBt0 hρ hx0 hx hΘ hlay hθ hR1 hBt hT cstar hE hthr i harm hΛ' hTΘ h1
  have hPG := prob_not_goodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN hD hLv hlev hlayOK hxr0 hxr1 hcw hγ hwE0 hwE
    (Ls := Ls) (Lb := Lb) (Lc := Lc) (Lt := Lt) (κ := κ) hLs0 hLb0 hκ hκ1 cstar
  have hp : ∀ ω : Fin T → RC (QQ), 0 ≤ Pool.P0202.pw (wR (QQ)) ω := fun ω => Pool.P0228.pw_nonneg (QQ) hL ω
  have hs1 : ∑ ω : Fin T → RC (QQ), Pool.P0202.pw (wR (QQ)) ω = 1 := Pool.P0228.sum_pw (QQ) hL hN T
  have hR0 : (0 : ℝ) ≤ (QQ).R := by have : (1 : ℝ) ≤ (QQ).R := by exact_mod_cast hR1
                                    linarith
  have hα := αT_nonneg (ι := ι) η L T hη hδ
  have hA0 : 0 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ := by
    unfold AP
    have : 0 ≤ Lt / κ := div_nonneg hLt hκ.le
    have : 0 ≤ 2 * Ls / xmin := div_nonneg (by linarith) hxm.le
    have : 0 ≤ Lc / (2 * (wE * γ)) := div_nonneg hLc (by positivity)
    positivity
  have hB0 : 0 ≤ BP P η L N G γ wE ρG Ls M := by unfold BP; positivity
  have hC0 : 0 ≤ T * (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ / (QQ).Bt 0 +
          BP P η L N G γ wE ρG Ls M / √((QQ).Bt 0 : ℝ)) := by
    have : 0 ≤ ((QQ).Bt 0 : ℝ) := Nat.cast_nonneg _
    positivity
  have hK0 : (0 : ℝ) ≤ 1 := zero_le_one
  have hnb : ∀ ω : Fin T → RC (QQ), 0 ≤ walkW (AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ)
      (BP P η L N G γ wE ρG Ls M) (QQ).Bt (QQ).D ρ
      (fun j => nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T cstar j) := fun ω =>
    walkW_nonneg hA0 hB0 hρ0 _ (fun j => by unfold nbad; exact Nat.cast_nonneg _)
  have hfirst := split_good (fun ω : Fin T → RC (QQ) => Pool.P0202.pw (wR (QQ)) ω) hp hs1 hC0 hK0 _ hnb
    (fun ω => ∑ u ∈ Finset.range T, (η / 2 * Pool.P0225.VR P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T u +
      slT P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 ω) ωs φ T rc0 κ u))
    (fun ω => GoodAll P η L N G γ wE ρG ℓ ωs φ T rc0 hL hN Ls Lb Lc Lt κ cstar (Pool.P0210.extR (QQ) rc0 ω))
  beta_reduce at hfirst
  simp only [one_mul] at hfirst
  have hw0 : 0 ≤ wE := hwE0.le
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left hfirst hw0
  have := mul_le_mul_of_nonneg_left hPG (mul_nonneg hw0 hT0)
  linarith

end Param

end Pool.P0250
