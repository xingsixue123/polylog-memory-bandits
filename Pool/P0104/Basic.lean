import Pool.P0104.Machine

/-!
# Basic lemmas for the threaded machine

* `InRange`, `pl_eq_of`, `mem_U_mkP`: the flattened sub-pools.
* `mergeUpTo_congr_time`: merges at the end of unit `a` read the filter coins of time `a` only.
* `Cm_bp`, **`agreeOn_Cm`**: if the table holds the true losses since each pool copy's entry, the rebuilt cover
  data agree with the true cumulative losses on every interval a merge of the pool reads (P0068's `AgreeOn`
  on the breakpoints), so P0078's `mergeUpTo_congrC` gives the true merges.
* `lst_length_le`, `mem_lst`, **`bitOf_eq`**: on valid data the queried bit of a pool copy is its arm's bit.
* `P1of`, `unitEnd_fst`, `unitEnd_table`, `unitEnd_hedge`: the components of `unitEnd`; `decH_unitEnd` (the
  decoded Hedge reset rule), `unitEnd_table_new` (zero table entries for new copies), `kM_nonneg` (the `toNat`
  truncation is inactive for `η ≥ 0`, `δ > 0`); the last three make the decoding explicit.
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0030 Pool.P0042 Pool.P0052 Pool.P0065

namespace Pool.P0104

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (p : Prm n ι)

/-- A family vanishing outside the stored range. -/
def InRange (P : ℕ → ℕ → Finset ι) : Prop := ∀ r ℓ, (p.D ≤ r ∨ p.Lv ≤ ℓ) → P r ℓ = ∅

theorem Lt_succ (hD : 0 < p.D) (hLv : 0 < p.Lv) : p.Lt + 1 = p.D * p.Lv := by
  unfold Prm.Lt; have := Nat.mul_pos hD hLv; omega

theorem pl_eq_of (hD : 0 < p.D) (hLv : 0 < p.Lv) {P : ℕ → ℕ → Finset ι} (hP : InRange p P) (x : Raw p)
    (hx : x.1 = mkP p P) (r ℓ : ℕ) : pl p x r ℓ = P r ℓ := by
  by_cases h : r < p.D ∧ ℓ < p.Lv
  · refine pl_mkP p x hx h.2 ?_
    rw [Lt_succ p hD hLv]
    calc r * p.Lv + ℓ < r * p.Lv + p.Lv := by omega
      _ = (r + 1) * p.Lv := by ring
      _ ≤ p.D * p.Lv := Nat.mul_le_mul_right _ h.1
  · rw [hP r ℓ (by omega)]
    unfold pl
    rw [dif_neg]
    rintro ⟨h1, h2⟩
    rw [Lt_succ p hD hLv] at h2
    apply h
    refine ⟨?_, h1⟩
    by_contra hr
    have : p.D * p.Lv ≤ r * p.Lv := Nat.mul_le_mul_right _ (by omega)
    omega

theorem mem_U_mkP (hD : 0 < p.D) (hLv : 0 < p.Lv) {P : ℕ → ℕ → Finset ι} (hP : InRange p P) {c : ι} :
    c ∈ Finset.univ.biUnion (mkP p P) ↔ ∃ r ℓ, c ∈ P r ℓ := by
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mkP]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨_, _, hk⟩
  · rintro ⟨r, ℓ, hc⟩
    have h : r < p.D ∧ ℓ < p.Lv := by
      by_contra h
      rw [hP r ℓ (by omega)] at hc
      simp at hc
    have hk : r * p.Lv + ℓ < p.Lt + 1 := by
      rw [Lt_succ p hD hLv]
      calc r * p.Lv + ℓ < r * p.Lv + p.Lv := by omega
        _ = (r + 1) * p.Lv := by ring
        _ ≤ p.D * p.Lv := Nat.mul_le_mul_right _ h.1
    refine ⟨⟨r * p.Lv + ℓ, hk⟩, ?_⟩
    simp only
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hLv, Nat.div_eq_of_lt h.2, zero_add,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h.2]
    exact hc

/-- Merges at the end of unit `a` read the filter coins of time `a` only. -/
theorem mergeUpTo_congr_time {C : ι → ℕ → ℝ} {φ φ' : ℕ → ℕ → Fin p.K → ι → Bool} (a : ℕ)
    (h : φ a = φ' a) : ∀ m (P : ℕ → Finset ι),
    mergeUpTo p.E C p.θ p.R p.K φ a m P = mergeUpTo p.E C p.θ p.R p.K φ' a m P := by
  intro m
  induction m with
  | zero => intro P; simp only [mergeUpTo, mergeOne, h]
  | succ m ih => intro P; simp only [mergeUpTo]; rw [ih P]; simp only [mergeOne, h]

section Table

variable {p}

open Classical in
/-- The rebuilt cover data at a breakpoint is minus the loss since that breakpoint. -/
theorem Cm_bp {U : Finset ι} {Dt : ι → ι → ℕ} {cu : ℕ → ι → ℝ} {a : ℕ}
    (hU : ∀ d ∈ U, p.E d ≤ a)
    (hDt : ∀ c ∈ U, ∀ d ∈ U, p.E c ≤ p.E d → (Dt c d : ℝ) = ∑ w ∈ Ico (p.E d) (a + 1), cu w c)
    {f : ι} (hf : f ∈ U) {u : ℕ} (hu : u ∈ Pool.P0068.bp p.E (a + 1) U) (hfu : p.E f ≤ u) :
    Cm p U Dt a f u = -∑ w ∈ Ico u (a + 1), cu w f := by
  unfold Cm
  rcases hu with hu | ⟨g, hg, rfl⟩
  · subst hu; simp
  · have hne : p.E g ≠ a + 1 := by have := hU g hg; omega
    rw [if_neg hne, dif_pos ⟨g, hg, rfl⟩]
    have hspec := (⟨g, hg, rfl⟩ : ∃ d ∈ U, p.E d = p.E g).choose_spec
    rw [hDt f hf _ hspec.1 (by rw [hspec.2]; exact hfu), hspec.2]

/-- **The rebuilt cover data agree with the true cumulative losses** on every interval read by a merge of
the pool `U` at time `a + 1`. -/
theorem agreeOn_Cm {U : Finset ι} {Dt : ι → ι → ℕ} {cu : ℕ → ι → ℝ} {a : ℕ}
    (hU : ∀ d ∈ U, p.E d ≤ a)
    (hDt : ∀ c ∈ U, ∀ d ∈ U, p.E c ≤ p.E d → (Dt c d : ℝ) = ∑ w ∈ Ico (p.E d) (a + 1), cu w c) :
    Pool.P0068.AgreeOn p.E (Cm p U Dt a) (Pool.P0061.cumL cu) U (Pool.P0068.bp p.E (a + 1) U) := by
  intro f hf e₁ he₁ e₂ he₂ h1 h2
  have hle : ∀ u ∈ Pool.P0068.bp p.E (a + 1) U, u ≤ a + 1 := by
    rintro u (rfl | ⟨g, hg, rfl⟩)
    · exact le_rfl
    · have := hU g hg; omega
  rw [Pool.P0061.Lint_cumL cu f h2]
  unfold Pool.P0030.Lint
  rw [Cm_bp hU hDt hf he₂ (h1.trans h2), Cm_bp hU hDt hf he₁ h1,
    ← Finset.sum_Ico_consecutive _ h2 (hle e₂ he₂)]
  ring

end Table

section Queries

variable {p}

theorem lst_length_le {x : Raw p} (hx : Pool.P0078.Valid p.Ns x) : (lst p x).length ≤ p.Ns := by
  unfold lst; rw [Finset.length_sort]; exact hx.1

theorem mem_lst {x : Raw p} {c : ι} : c ∈ lst p x ↔ c ∈ Pool.P0078.U x := by
  unfold lst; exact Finset.mem_sort _

/-- The queried bit of a pool copy is the loss bit of its arm. -/
theorem bitOf_eq [NeZero n] {x : Raw p} (hx : Pool.P0078.Valid p.Ns x) (v : Fin n → Bool) {c : ι}
    (hc : c ∈ Pool.P0078.U x) : bitOf p x (fun k => v (qry p x k)) c = (v (p.arm c)).toNat := by
  have hmem : c ∈ lst p x := mem_lst.mpr hc
  have hlt : (lst p x).idxOf c < (lst p x).length := List.idxOf_lt_length_iff.mpr hmem
  have hNs : (lst p x).idxOf c < p.Ns := lt_of_lt_of_le hlt (lst_length_le hx)
  unfold bitOf qry
  rw [dif_pos hNs]
  simp only [dif_pos hlt, List.getElem_idxOf hlt]
  cases v (p.arm c) <;> rfl

end Queries

section Unfold

/-- The pre-merge pools of `unitEnd`. -/
noncomputable def P1of (x : Raw p) (a : ℕ) (β : ι → ℕ) (z : Jd p → Bool) : ℕ → ℕ → Finset ι := fun r =>
  if p.Bt r ∣ a + 1 then
    mergeUpTo p.E (Cm p (Pool.P0078.U x) (fun c d => (x.2.1 c d : ℕ) + β c) a) p.θ p.R p.K
      (φz p z r) a (p.lev r a) (pl p x r)
  else pl p x r

theorem unitEnd_fst (x : Raw p) (a : ℕ) (β : ι → ℕ) (z : Jd p → Bool) :
    (unitEnd p x a β z).1 = mkP p (startPools p.E p.thr0 p.D p.Lv p.Bt (ωz p z) (a + 1) (P1of p x a β z)) :=
  rfl

open Classical in
theorem unitEnd_table (x : Raw p) (a : ℕ) (β : ι → ℕ) (z : Jd p → Bool) (c d : ι) :
    (unitEnd p x a β z).2.1 c d =
      if c ∈ Finset.univ.biUnion (unitEnd p x a β z).1 ∧ d ∈ Finset.univ.biUnion (unitEnd p x a β z).1 ∧
        c ∈ Pool.P0078.U x ∧ d ∈ Pool.P0078.U x then capF p.TT ((x.2.1 c d : ℕ) + β c) else 0 := by
  simp only [unitEnd]

open Classical in
theorem unitEnd_hedge (x : Raw p) (a : ℕ) (β : ι → ℕ) (z : Jd p → Bool) (c : ι) :
    (unitEnd p x a β z).2.2 c =
      if c ∈ Finset.univ.biUnion (unitEnd p x a β z).1 then
        encH p (fun l => if c ∈ Pool.P0078.U x ∧ ¬ 2 ^ (l : ℕ) ∣ a + 1 then
          (capF p.NN (hN p x c l + β c), capF p.MM ((hM p x c l + kM p x β).toNat)) else (0, 0))
      else 0 := by
  simp only [unitEnd]

open Classical in
/-- The Hedge reset rule, decoded: on a present copy each level continues iff
the copy was present before and the level's dyadic block does not end at `a + 1`; otherwise it restarts at
`(0, 0)`. -/
theorem decH_unitEnd (x : Raw p) (a : ℕ) (β : ι → ℕ) (z : Jd p → Bool) (c : ι)
    (hc : c ∈ Pool.P0078.U (unitEnd p x a β z)) (l : Fin (p.L + 1)) :
    decH p ((unitEnd p x a β z).2.2 c) l =
      if c ∈ Pool.P0078.U x ∧ ¬ 2 ^ (l : ℕ) ∣ a + 1 then
        (capF p.NN (hN p x c l + β c), capF p.MM ((hM p x c l + kM p x β).toNat)) else (0, 0) := by
  have hc' : c ∈ Finset.univ.biUnion (unitEnd p x a β z).1 := hc
  rw [unitEnd_hedge]
  simp only [hc', if_true, decH_encH]

open Classical in
/-- A copy that was not in the pool before the update has zero table entries after it. -/
theorem unitEnd_table_new (x : Raw p) (a : ℕ) (β : ι → ℕ) (z : Jd p → Bool) {c : ι}
    (hc : c ∉ Pool.P0078.U x) (d : ι) : (unitEnd p x a β z).2.1 c d = 0 := by
  rw [unitEnd_table]
  rw [if_neg (fun h => hc h.2.2.1)]

/-- `kM ≥ 0` when `η ≥ 0` and `δ > 0`: the `toNat` truncation in `unitEnd`
never fires in that regime. -/
theorem kM_nonneg (hη : 0 ≤ p.η) (hδ : 0 < p.δ) (x : Raw p) (β : ι → ℕ) : 0 ≤ kM p x β := by
  unfold kM
  have hden_le : ∑ c ∈ Pool.P0078.U x, ∑ l, wM p x c l * Real.exp (-p.η * β c) ≤ totW p x := by
    unfold totW
    refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun l _ => ?_
    have h1 : Real.exp (-p.η * β c) ≤ 1 := by
      rw [Real.exp_le_one_iff]; have : (0:ℝ) ≤ β c := Nat.cast_nonneg _; nlinarith
    have h0 : 0 ≤ wM p x c l := (Real.exp_pos _).le
    nlinarith
  have hden_nn : 0 ≤ ∑ c ∈ Pool.P0078.U x, ∑ l, wM p x c l * Real.exp (-p.η * β c) :=
    Finset.sum_nonneg fun c _ => Finset.sum_nonneg fun l _ =>
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hlog : 0 ≤ Real.log (totW p x / ∑ c ∈ Pool.P0078.U x, ∑ l, wM p x c l * Real.exp (-p.η * β c)) := by
    rcases hden_nn.eq_or_lt with h | h
    · rw [← h, div_zero, Real.log_zero]
    · exact Real.log_nonneg ((one_le_div h).2 hden_le)
  have : (0:ℝ) ≤ Real.log (totW p x / ∑ c ∈ Pool.P0078.U x, ∑ l, wM p x c l * Real.exp (-p.η * β c)) / p.δ :=
    div_nonneg hlog hδ.le
  rw [round_eq]
  exact Int.floor_nonneg.mpr (by linarith)

end Unfold

end Pool.P0104
