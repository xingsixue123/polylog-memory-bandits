import Pool.P0137.CostB

/-!
# Record counts and general per-record costs for P0135's walk with (b′)-ends

P0137 bounds `Σ √|I|` over the counted records of `Pool.P0135.theWalkB`. Additive per-record costs (the learner's
`k·R(η)` per record, P0131 §3(c)) need a record count, which P0137 leaves open. Here:

* **`Pool.P0153.sum_costB_le`**: for any record cost `f` with `f ℓ ≤ ℓ·a j` once `ℓ ≥ B j` (`j < R`, `a j ≥ 0`) and
  `f ℓ ≤ c` below the finest epoch (`c ≥ 0`): `Σ_counted f(|I|) ≤ T·a 0 + Σ_{1≤j<R} B(j-1)·K_{j-1}·a j + K_{R-1}·c`,
  `K_j = Pool.P0137.KB … j` (P0137's √-bound is the case `f = √`, `a j = 1/√(B j)`, `c = √(B (R-1))`).
* **`Pool.P0153.card_countedB_le`**: #counted records `≤ T/B 0 + Σ_{1≤j<R} B(j-1)·K_{j-1}/B j + K_{R-1}`.
* **`Pool.P0153.card_countedB_le_ratio`**: with `B (j-1) ≤ r·B j`, `≤ T/B 0 + r·Σ_{j<R-1} K_j + K_{R-1}`.
* **`Pool.P0153.sum_affineB_le`**: `Σ (α√|I| + β) ≤ α·(P0137's bound) + β·(the count)`.

Abstract and combinatorial: no process, certificate or probability. Free bad records and (b′)-records are not counted
(as in P0137).
-/

namespace Pool.P0153

open Pool.P0135 Pool.P0137

variable {R T : ℕ} {B : ℕ → ℕ} {t : ℕ → ℕ → Out} {g : ℕ → Out}

section
variable (h : HypB R T B t g)
include h

/-- **General per-record cost assembly.** If a record cost `f` satisfies `f ℓ ≤ ℓ · a j` once `ℓ ≥ B j`
(`j < R`) and `f ℓ ≤ c` below the finest epoch, then over the counted records of `theWalkB`
`Σ f(|I|) ≤ T·a 0 + Σ_{1 ≤ j < R} B (j-1)·K_{j-1}·a j + K_{R-1}·c`. -/
theorem sum_costB_le (f : ℕ → ℝ) (a : ℕ → ℝ) (c : ℝ) (ha : ∀ j < R, 0 ≤ a j) (hc0 : 0 ≤ c)
    (hbig : ∀ j < R, ∀ ℓ : ℕ, B j ≤ ℓ → f ℓ ≤ ℓ * a j)
    (hsmall : ∀ ℓ : ℕ, ℓ < B (R - 1) → f ℓ ≤ c) :
    (((theWalkB R T B t g).filter counted).map fun x => f (len x)).sum ≤
      T * a 0 +
        ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * KB T B t (theWalkB R T B t g) (j - 1) * a j +
        KB T B t (theWalkB R T B t g) (R - 1) * c := by
  obtain ⟨hc, hok, hsum, hshort⟩ := theWalkB_spec h
  set L := theWalkB R T B t g
  have hR := h.hR
  set F := L.filter counted
  have hpt : ∀ x ∈ F, f (len x) ≤ (len x : ℝ) * a 0 +
      ∑ j ∈ Finset.Ico 1 R, (if len x < B (j - 1) then (len x : ℝ) else 0) * a j +
      (if len x < B (R - 1) then c else 0) := by
    intro x _
    have hnn : ∀ j ∈ Finset.Ico 1 R,
        0 ≤ (if len x < B (j - 1) then (len x : ℝ) else 0) * a j := by
      intro j hj
      refine mul_nonneg ?_ (ha j (Finset.mem_Ico.1 hj).2)
      split_ifs <;> positivity
    have h0' : (0 : ℝ) ≤ (len x : ℝ) * a 0 := mul_nonneg (by positivity) (ha 0 hR)
    have hS := Finset.sum_nonneg hnn
    by_cases hsm : len x < B (R - 1)
    · rw [if_pos hsm]
      have := hsmall _ hsm
      linarith
    rw [if_neg hsm]
    push_neg at hsm
    by_cases h0 : B 0 ≤ len x
    · have := hbig 0 hR _ h0
      linarith
    · have hex : ∃ j, B j ≤ len x := ⟨R - 1, hsm⟩
      set j0 := Nat.find hex with hj0
      have hj0s : B j0 ≤ len x := Nat.find_spec hex
      have hj0R : j0 ≤ R - 1 := Nat.find_min' hex hsm
      have hj01 : 1 ≤ j0 := by
        by_contra hc'
        have : j0 = 0 := by omega
        rw [this] at hj0s; exact h0 hj0s
      have hmin : len x < B (j0 - 1) := by
        have := Nat.find_min hex (show j0 - 1 < j0 by omega)
        push_neg at this; exact this
      have hmem : j0 ∈ Finset.Ico 1 R := Finset.mem_Ico.2 ⟨hj01, by omega⟩
      have hterm := Finset.single_le_sum hnn hmem
      rw [if_pos hmin] at hterm
      have := hbig j0 (by omega) _ hj0s
      linarith
  refine (List.sum_le_sum hpt).trans ?_
  have hsplit : ∀ (M : List RecB), (M.map fun x => (len x : ℝ) * a 0 +
      ∑ j ∈ Finset.Ico 1 R, (if len x < B (j - 1) then (len x : ℝ) else 0) * a j +
      (if len x < B (R - 1) then c else 0)).sum =
      ((M.map len).sum : ℝ) * a 0 + ∑ j ∈ Finset.Ico 1 R,
        ((((M.filter fun x => decide (len x < B (j - 1))).map len).sum : ℕ) : ℝ) * a j +
        ((M.filter fun x => decide (len x < B (R - 1))).length : ℝ) * c := by
    intro M
    induction M with
    | nil => simp
    | cons y M ih =>
      rw [List.map_cons, List.sum_cons, ih]
      simp only [List.map_cons, List.sum_cons, Nat.cast_add, add_mul]
      have : ∀ j ∈ Finset.Ico 1 R, (((((y :: M).filter fun x => decide (len x < B (j - 1))).map len).sum
          : ℕ) : ℝ) * a j = (if len y < B (j - 1) then (len y : ℝ) else 0) * a j
          + ((((M.filter fun x => decide (len x < B (j - 1))).map len).sum : ℕ) : ℝ) * a j := by
        intro j _
        by_cases hy : len y < B (j - 1)
        · simp [List.filter_cons, hy, add_mul]
        · simp [List.filter_cons, hy]
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
      by_cases hy : len y < B (R - 1)
      · simp [List.filter_cons, hy]; ring
      · simp [List.filter_cons, hy]; ring
  rw [hsplit]
  have hF : (F.map len).sum ≤ T := by
    rw [← hsum]
    exact List.Sublist.sum_le_sum ((List.filter_sublist (p := counted) (l := L)).map len)
      (fun _ _ => Nat.zero_le _)
  have hfilt : ∀ q : RecB → Bool, F.filter q = L.filter fun x => counted x && q x := by
    intro q; simp only [F, List.filter_filter]
    congr 1; funext x; exact Bool.and_comm _ _
  have hT : ((F.map len).sum : ℝ) * a 0 ≤ T * a 0 :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hF) (ha 0 hR)
  have hmid : ∑ j ∈ Finset.Ico 1 R,
      ((((F.filter fun x => decide (len x < B (j - 1))).map len).sum : ℕ) : ℝ) * a j ≤
      ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * KB T B t L (j - 1) * a j := by
    refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (ha j (Finset.mem_Ico.1 hj).2)
    rw [hfilt, ← Nat.cast_mul]
    exact_mod_cast hshort (j - 1) (by have := Finset.mem_Ico.1 hj; omega)
  have hlast : ((F.filter fun x => decide (len x < B (R - 1))).length : ℝ) * c ≤
      KB T B t L (R - 1) * c := by
    refine mul_le_mul_of_nonneg_right ?_ hc0
    rw [hfilt]
    exact_mod_cast card_shortB_finest h hc hok
  linarith

/-- **P0137's √-bound as the case `f = √`** of `sum_costB_le` (`a j = 1/√(B j)`, `c = √(B (R-1))`). -/
theorem sum_sqrtB_le' :
    (((theWalkB R T B t g).filter counted).map fun x => Real.sqrt (len x)).sum ≤
      T * (1 / Real.sqrt (B 0)) +
        ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * KB T B t (theWalkB R T B t g) (j - 1) * (1 / Real.sqrt (B j)) +
        KB T B t (theWalkB R T B t g) (R - 1) * Real.sqrt (B (R - 1)) :=
  sum_costB_le h (fun ℓ => Real.sqrt ℓ) (fun j => 1 / Real.sqrt (B j)) (Real.sqrt (B (R - 1)))
    (fun j _ => by positivity) (Real.sqrt_nonneg _)
    (fun j _ ℓ hℓ => by
      have hb : (0 : ℝ) < Real.sqrt (B j) := Real.sqrt_pos.2 (by exact_mod_cast h.pos j)
      rw [← div_eq_mul_one_div, le_div_iff₀ hb]
      calc Real.sqrt ℓ * Real.sqrt (B j) ≤ Real.sqrt ℓ * Real.sqrt ℓ := by gcongr
        _ = ℓ := Real.mul_self_sqrt (by positivity))
    (fun ℓ hℓ => Real.sqrt_le_sqrt (by exact_mod_cast hℓ.le))

/-- **Record count.** The counted records of `theWalkB` number at most
`T/B 0 + Σ_{1 ≤ j < R} B (j-1)·K_{j-1}/B j + K_{R-1}`. -/
theorem card_countedB_le :
    (((theWalkB R T B t g).filter counted).length : ℝ) ≤
      T / (B 0 : ℝ) +
        ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * KB T B t (theWalkB R T B t g) (j - 1) / (B j : ℝ) +
        KB T B t (theWalkB R T B t g) (R - 1) := by
  have key := sum_costB_le h (fun _ => (1 : ℝ)) (fun j => 1 / (B j : ℝ)) 1
    (fun j _ => by have := h.pos j; positivity) zero_le_one
    (fun j _ ℓ hℓ => by
      have hb : (0 : ℝ) < B j := by exact_mod_cast h.pos j
      rw [← div_eq_mul_one_div, le_div_iff₀ hb, one_mul]; exact_mod_cast hℓ)
    (fun _ _ => le_rfl)
  have hlen : ∀ (M : List RecB), (M.map fun _ => (1 : ℝ)).sum = M.length := by
    intro M; induction M with
    | nil => simp
    | cons y M ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring
  rw [hlen] at key
  refine key.trans (le_of_eq ?_)
  simp only [mul_one, ← div_eq_mul_one_div]

/-- **Affine record costs** `α·√|I| + β` (cover margin plus an additive per-record learner cost):
`Σ (α√|I| + β) ≤ α·(P0137's √-bound) + β·(the record count)`, for `α, β ≥ 0`. -/
theorem sum_affineB_le {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (((theWalkB R T B t g).filter counted).map fun x => α * Real.sqrt (len x) + β).sum ≤
      α * (T / Real.sqrt (B 0) +
        ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * KB T B t (theWalkB R T B t g) (j - 1) / Real.sqrt (B j) +
        KB T B t (theWalkB R T B t g) (R - 1) * Real.sqrt (B (R - 1))) +
      β * (T / (B 0 : ℝ) +
        ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * KB T B t (theWalkB R T B t g) (j - 1) / (B j : ℝ) +
        KB T B t (theWalkB R T B t g) (R - 1)) := by
  have hs := sum_sqrtB_le h
  have hcard := card_countedB_le h
  set F := (theWalkB R T B t g).filter counted
  have hsplit : ∀ (M : List RecB), (M.map fun x => α * Real.sqrt (len x) + β).sum =
      α * (M.map fun x => Real.sqrt (len x)).sum + β * M.length := by
    intro M; induction M with
    | nil => simp
    | cons y M ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring
  rw [hsplit]
  have := mul_le_mul_of_nonneg_left hs hα
  have := mul_le_mul_of_nonneg_left hcard hβ
  linarith

/-- **Record count with ratio `r`** (`B (j-1) ≤ r·B j`): counted records ≤ `T/B 0 + r·Σ_{j<R-1} K_j + K_{R-1}`. -/
theorem card_countedB_le_ratio {r : ℝ} (hr : ∀ j, 1 ≤ j → j < R → (B (j - 1) : ℝ) ≤ r * B j) :
    (((theWalkB R T B t g).filter counted).length : ℝ) ≤
      T / (B 0 : ℝ) + r * ∑ j ∈ Finset.Ico 1 R, (KB T B t (theWalkB R T B t g) (j - 1) : ℝ) +
        KB T B t (theWalkB R T B t g) (R - 1) := by
  refine (card_countedB_le h).trans ?_
  rw [Finset.mul_sum]
  have : ∑ j ∈ Finset.Ico 1 R, (B (j - 1) : ℝ) * KB T B t (theWalkB R T B t g) (j - 1) / (B j : ℝ) ≤
      ∑ j ∈ Finset.Ico 1 R, r * (KB T B t (theWalkB R T B t g) (j - 1) : ℝ) := by
    refine Finset.sum_le_sum fun j hj => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hj
    have hb : (0 : ℝ) < B j := by exact_mod_cast h.pos j
    have hK : (0 : ℝ) ≤ KB T B t (theWalkB R T B t g) (j - 1) := by positivity
    rw [div_le_iff₀ hb]
    calc (B (j - 1) : ℝ) * KB T B t (theWalkB R T B t g) (j - 1)
        ≤ r * B j * KB T B t (theWalkB R T B t g) (j - 1) := mul_le_mul_of_nonneg_right (hr j h1 h2) hK
      _ = r * KB T B t (theWalkB R T B t g) (j - 1) * B j := by ring
  linarith

end

end Pool.P0153
