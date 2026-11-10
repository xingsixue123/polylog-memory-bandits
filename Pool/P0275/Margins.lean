import Pool.P0268.AlgAge

/-!
# Clock-determined rule margins: the walk's link and the probing remainder's per-thread clock bound at once

Given any record margins `Λr j m` (thread `j`, age `m`) with a per-thread bound `Λr j m ≤ B j`, the rule margins
`margOf x u := Λr (min (curT x (u+1)) (D−1)) (u+1−E x)` satisfy P0235/P0242/P0250/P0268's margin link `hΛ'` with
equality, and P0255's next-round clock bound `hΛn` with the running maximum `Λbar j := max_{min j (D−1) ≤ j' ≤ D−1} B j'`
(antitone, nonnegative when `B` is). `withΛ` installs them in a `ParD`; nothing else of the process changes.
-/

namespace Pool.P0275

open Finset Pool.P0194

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- The rule margins: the record margin of the NEXT round's thread (clipped to `D − 1`) at the next round's age. -/
noncomputable def margOf (E : ι → ℕ) (thr0 : ι → ℕ) (D : ℕ) (Bt : ℕ → ℕ) (Λr : ℕ → ℕ → ℝ) (x : ι) (u : ℕ) : ℝ :=
  Λr (min (Pool.P0065.curT E thr0 D Bt x (u + 1)) (D - 1)) (u + 1 - E x)

/-- The per-thread clock bound: the largest per-thread bound over threads `≥ min j (D − 1)`. -/
noncomputable def Λbar (D : ℕ) (B : ℕ → ℝ) (j : ℕ) : ℝ :=
  (Icc (min j (D - 1)) (D - 1)).sup' ⟨D - 1, by simp⟩ B

/-- The link holds with equality. -/
theorem margOf_link (E : ι → ℕ) (thr0 : ι → ℕ) (D : ℕ) (Bt : ℕ → ℕ) (Λr : ℕ → ℕ → ℝ) (x : ι) (u : ℕ) :
    Λr (min (Pool.P0065.curT E thr0 D Bt x (u + 1)) (D - 1)) (u + 1 - E x) ≤ margOf E thr0 D Bt Λr x u :=
  le_rfl

theorem Λbar_anti (D : ℕ) (B : ℕ → ℝ) {i i' : ℕ} (h : i ≤ i') : Λbar D B i' ≤ Λbar D B i :=
  sup'_mono _ (Icc_subset_Icc (min_le_min_right _ h) le_rfl) _

theorem le_Λbar (D : ℕ) (B : ℕ → ℝ) (j : ℕ) : B (min j (D - 1)) ≤ Λbar D B j :=
  le_sup' B (by simp)

theorem Λbar_nonneg (D : ℕ) {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (j : ℕ) : 0 ≤ Λbar D B j :=
  (hB _).trans (le_Λbar D B j)

/-- `Λbar` is attained: it is `B j'` for some thread `min j (D−1) ≤ j' ≤ D − 1`. -/
theorem Λbar_eq (D : ℕ) (B : ℕ → ℝ) (j : ℕ) : ∃ j', min j (D - 1) ≤ j' ∧ j' ≤ D - 1 ∧ Λbar D B j = B j' := by
  obtain ⟨j', hj', h⟩ := exists_mem_eq_sup' (s := Icc (min j (D - 1)) (D - 1)) ⟨D - 1, by simp⟩ B
  exact ⟨j', (mem_Icc.1 hj').1, (mem_Icc.1 hj').2, h⟩

/-- **The clock bound** (P0255's `hΛn`, for every round and copy): when `Λr j m ≤ B j` for all `j, m`. -/
theorem margOf_le_Λbar (E : ι → ℕ) (thr0 : ι → ℕ) (D : ℕ) (Bt : ℕ → ℕ) {Λr : ℕ → ℕ → ℝ} {B : ℕ → ℝ}
    (hΛB : ∀ j m, Λr j m ≤ B j) (x : ι) (c : ℕ) :
    margOf E thr0 D Bt Λr x c ≤ Λbar D B (Pool.P0065.curT E thr0 D Bt x (c + 1)) :=
  (hΛB _ _).trans (le_Λbar D B _)

theorem margOf_nonneg (E : ι → ℕ) (thr0 : ι → ℕ) (D : ℕ) (Bt : ℕ → ℕ) {Λr : ℕ → ℕ → ℝ}
    (h0 : ∀ j m, 0 ≤ Λr j m) (x : ι) (u : ℕ) : 0 ≤ margOf E thr0 D Bt Λr x u := h0 _ _

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]

/-- Install rule margins in a `ParD` (no other field changes). -/
def withΛ (P : ParD n ι) (Λ : ι → ℕ → ℝ) : ParD n ι := { P with Λ := Λ }

/-- `P` with the clock-determined margins of the record margins `Λr`. -/
noncomputable def withMarg (P : ParD n ι) (Λr : ℕ → ℕ → ℝ) : ParD n ι :=
  withΛ P (margOf P.E P.thr0 P.D P.Bt Λr)

theorem withMarg_Λ (P : ParD n ι) (Λr : ℕ → ℕ → ℝ) :
    (withMarg P Λr).Λ = margOf P.E P.thr0 P.D P.Bt Λr := rfl

/-- **Both requirements on `withMarg P Λr`**: the link (P0268's `hΛ'` form, with equality) and the clock bound
(P0255's `hΛn`, antitone nonnegative `Λbar`). -/
theorem withMarg_hyps (P : ParD n ι) (Λr : ℕ → ℕ → ℝ) (B : ℕ → ℝ) (hΛB : ∀ j m, Λr j m ≤ B j) :
    (∀ c u, Λr (min (Pool.P0065.curT (withMarg P Λr).E (withMarg P Λr).thr0 (withMarg P Λr).D (withMarg P Λr).Bt c
        (u + 1)) ((withMarg P Λr).D - 1)) (u + 1 - (withMarg P Λr).E c) ≤ (withMarg P Λr).Λ c u) ∧
    (∀ x c, (withMarg P Λr).E x ≤ c → (withMarg P Λr).Λ x c ≤
        Λbar P.D B (Pool.P0065.curT (withMarg P Λr).E (withMarg P Λr).thr0 (withMarg P Λr).D (withMarg P Λr).Bt x
          (c + 1))) ∧
    (∀ i i', i ≤ i' → Λbar P.D B i' ≤ Λbar P.D B i) :=
  ⟨fun c u => le_rfl, fun x c _ => margOf_le_Λbar P.E P.thr0 P.D P.Bt hΛB x c,
    fun _ _ h => Λbar_anti P.D B h⟩

section AgeCapped

open Pool.P0250 Pool.P0268

variable (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ)
  (ρG : Pool.P0212.AState ι → Finset ι → Option ι → Bool → ℝ)

/-- **P0268's age-capped record margins as rule margins.** `P` with the clock-determined margins of
`ΛPc` (computed on `P` itself; `ΛPc` does not read `P.Λ`). -/
noncomputable def margP (T : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ) (Θn : ℕ) : ParD n ι :=
  withMarg P (ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn)

/-- `ΛPc` on `margP` is `ΛPc` on `P` (it reads no margin). -/
theorem ΛPc_margP (T : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ) (Θn : ℕ) :
    ΛPc (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn
      TT Θ Θn = ΛPc P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn := rfl

/-- The per-thread clock bound of `margP`: the running maximum of P0250's `ΛP j (lenOf j)`. -/
noncomputable def ΛbarP (T : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ) (Θn : ℕ) : ℕ → ℝ :=
  Λbar P.D (fun j => ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ j
    (Pool.P0238.lenOf Θn T P.Bt j))


/-- **P0268's margin link `hΛ'` holds for `margP`** (with equality), in the exact form of
`run_bound_param_age` / `alg_expect_final_age`. -/
theorem margP_hΛ' (T : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ) (Θn : ℕ) :
    ∀ c u, ΛPc (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG T δ Ls Lb Lc Lt κ
      xmin M ρ nn TT Θ Θn
        (min (Pool.P0065.curT (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).E (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).thr0 (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).D (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).Bt c (u + 1)) ((Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).D - 1)) (u + 1 - (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).E c) ≤
      (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).Λ c u :=
  fun _ _ => le_rfl

/-- **P0255's next-round clock bound `hΛn` holds for `margP`** (on the process with ALG installed, the `P` of
`restD2_le`), with `ΛbarP`. -/
theorem margP_hΛn (T : ℕ) {δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (Θn : ℕ) (hcB : 0 ≤ P.cB) (hLb : 0 ≤ Lb)
    (hLs : 0 ≤ Ls) (hM : 0 ≤ M) :
    ∀ x c, (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).E x ≤ c → (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).Λ x c ≤
      ΛbarP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn
        (Pool.P0065.curT (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).E (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).thr0 (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).D (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).Bt x (c + 1)) :=
  fun x c _ => margOf_le_Λbar P.E P.thr0 P.D P.Bt
    (fun j m => ΛPc_le P η L N G γ wE ρG T Θn j m hcB hLb hLs hM) x c

theorem ΛbarP_anti (T : ℕ) (δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ) (Θn : ℕ) :
    ∀ i i', i ≤ i' → ΛbarP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn i' ≤
      ΛbarP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn i :=
  fun _ _ h => Λbar_anti _ _ h

/-- P0250's rule-margin budget `wP` is nonnegative. -/
theorem wP_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (Bt : ℕ → ℕ) (D i : ℕ) : 0 ≤ wP A B Bt D i := by
  unfold wP
  refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) ?_
  · split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (aaP_nonneg hA hB j)
    · exact le_rfl
  · split_ifs
    · exact ccP_nonneg hA hB
    · exact le_rfl

/-- P0250's record margins are nonnegative (so `ΛbarP` is, as P0255's `restD2_le` asks: `hΛ0`). -/
theorem ΛP_nonneg (T : ℕ) {δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (hη : 0 < η) (hδ : 0 ≤ δ) (hγ : 0 < γ)
    (hwE : 0 < wE) (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ) (hxm : 0 < xmin)
    (hM : 0 ≤ M) (hθ : 0 ≤ P.θ) (j m : ℕ) :
    0 ≤ ΛP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ j m := by
  have hα := Pool.P0226.αT_nonneg (ι := ι) (η := η) (L := L) (T := T) hη hδ
  have h1 : 0 ≤ Lt / κ := div_nonneg hLt hκ.le
  have h2 : 0 ≤ Lc / (2 * (wE * γ)) := div_nonneg hLc (by positivity)
  have h3 : 0 ≤ 2 * Ls / xmin := div_nonneg (by linarith) hxm.le
  have hAP : 0 ≤ AP P η L N G γ wE ρG T δ Ls Lc Lt κ xmin M ρ nn TT Θ := by
    unfold AP
    have : 0 ≤ (Pool.P0225.withAlgG P η L N G γ wE ρG).θ := hθ
    have := Real.sqrt_nonneg (Ls * (Θ * (ρ * TT / nn)))
    positivity
  have hBP : 0 ≤ BP P η L N G γ wE ρG Ls M := by
    unfold BP; positivity
  unfold ΛP
  have := Pool.P0226.widV_nonneg (V := (m : ℝ) * (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)
    (le_trans zero_le_one (le_max_left 1 (Pool.P0225.withAlgG P η L N G γ wE ρG).cB)) hLb
  have := wP_nonneg hAP hBP (Pool.P0225.withAlgG P η L N G γ wE ρG).Bt (Pool.P0225.withAlgG P η L N G γ wE ρG).D j
  have : 0 ≤ Pool.P0222.Wocc Ls xmin M ρ nn TT Θ m := by
    unfold Pool.P0222.Wocc; have := Real.sqrt_nonneg (Ls * ((m : ℝ) * M + Θ * (ρ * TT / nn))); linarith
  linarith

theorem ΛbarP_nonneg (T : ℕ) {δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (Θn : ℕ) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hγ : 0 < γ) (hwE : 0 < wE) (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hM : 0 ≤ M) (hθ : 0 ≤ P.θ) (i : ℕ) :
    0 ≤ ΛbarP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn i :=
  Λbar_nonneg _ (fun j => ΛP_nonneg P η L N G γ wE ρG T hη hδ hγ hwE hLs hLb hLc hLt hκ hxm hM hθ j _) i

/-- **The process margins of `margP` are nonnegative** (P0255's margin-level `hΛ0 : ∀ x c, 0 ≤ P.Λ x c`, on the process
with ALG installed): `margOf` reads `ΛPc j m = ΛP j (min m (lenOf j))`, which is `≥ 0` by `ΛP_nonneg`. -/
theorem margP_Λ_nonneg (T : ℕ) {δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ : ℝ} (Θn : ℕ) (hη : 0 < η) (hδ : 0 ≤ δ)
    (hγ : 0 < γ) (hwE : 0 < wE) (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hLt : 0 ≤ Lt) (hκ : 0 < κ)
    (hxm : 0 < xmin) (hM : 0 ≤ M) (hθ : 0 ≤ P.θ) :
    ∀ x c, 0 ≤ (Pool.P0225.withAlgG (margP P η L N G γ wE ρG T δ Ls Lb Lc Lt κ xmin M ρ nn TT Θ Θn) η L N G γ wE ρG).Λ x c :=
  fun x c => margOf_nonneg P.E P.thr0 P.D P.Bt
    (fun j m => ΛP_nonneg P η L N G γ wE ρG T hη hδ hγ hwE hLs hLb hLc hLt hκ hxm hM hθ j _) x c

end AgeCapped

end Pool.P0275
