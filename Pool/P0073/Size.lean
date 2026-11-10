import Pool.P0065.Threads

/-!
# Pool sizes of the threaded process on good runs (deterministic; the thread analogue of P0052's
# `pools_card_le`)
-/

namespace Pool.P0073

open Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {C : ι → ℕ → ℝ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}

variable (E thr0 C θ R K D Lv Bt lev) in
/-- Good run of the threaded process: every sample has at most `s0` copies, and every merge
iteration sequence of a merge that happens brings its input to `max M0 (ρ · |input|)`. -/
def GoodRunT (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (NE s0 : ℕ) (M0 ρ : ℝ) : Prop :=
  (∀ a < NE, ∀ r < D, Bt r ∣ a → (newAtT E thr0 ωs a r).card ≤ s0) ∧
  ∀ a < NE, ∀ r < D, Bt r ∣ a + 1 → ∀ ℓ ≤ lev r a,
    ((iter (mstep E C (a + 1) θ R)
        (stage E C θ R K (φ r) a (startPools E thr0 D Lv Bt ωs a
          (tpools E thr0 C θ R K D Lv Bt lev ωs φ a) r) ℓ (ℓ + 1) ∪
         stage E C θ R K (φ r) a (startPools E thr0 D Lv Bt ωs a
          (tpools E thr0 C θ R K D Lv Bt lev ωs φ a) r) ℓ ℓ) K (φ r a ℓ)).card : ℝ) ≤
      max M0 (ρ * (stage E C θ R K (φ r) a (startPools E thr0 D Lv Bt ωs a
          (tpools E thr0 C θ R K D Lv Bt lev ωs φ a) r) ℓ (ℓ + 1) ∪
         stage E C θ R K (φ r) a (startPools E thr0 D Lv Bt ωs a
          (tpools E thr0 C θ R K D Lv Bt lev ωs φ a) r) ℓ ℓ).card)

/-- One merge (`mergeOne`) keeps every level `≤ S` except possibly level 0 (`≤ S'`), and empties
level `ℓ`; generic in the merge outcome bound. -/
lemma mergeOne_card {φ : ℕ → ℕ → Fin K → ι → Bool} {a ℓ : ℕ} {P : ℕ → Finset ι} {S S' M0 ρ : ℝ}
    (hρ : 0 ≤ ρ) (hM0 : M0 ≤ S) (hρS : ρ * (S + S') ≤ S) (hSS : S ≤ S')
    (hP0 : ((P 0).card : ℝ) ≤ S') (hP : ∀ j, j ≠ 0 → ((P j).card : ℝ) ≤ S)
    (hm : ((iter (mstep E C (a + 1) θ R) (P (ℓ + 1) ∪ P ℓ) K (φ a ℓ)).card : ℝ) ≤
      max M0 (ρ * (P (ℓ + 1) ∪ P ℓ).card)) :
    (((mergeOne E C θ R K φ a ℓ P 0).card : ℝ) ≤ S') ∧
      ∀ j, j ≠ 0 → ((mergeOne E C θ R K φ a ℓ P j).card : ℝ) ≤ S := by
  have hS0 : 0 ≤ S := by
    have := hP 1 one_ne_zero; exact le_trans (Nat.cast_nonneg _) this
  have hU : (((P (ℓ + 1) ∪ P ℓ).card : ℕ) : ℝ) ≤ S + S' := by
    have h := Finset.card_union_le (P (ℓ + 1)) (P ℓ)
    have h1 := hP (ℓ + 1) (by omega)
    have h2 : ((P ℓ).card : ℝ) ≤ S' := by
      by_cases hl : ℓ = 0
      · subst hl; exact hP0
      · exact (hP ℓ hl).trans hSS
    have : (((P (ℓ + 1) ∪ P ℓ).card : ℕ) : ℝ) ≤ (P (ℓ + 1)).card + (P ℓ).card := by exact_mod_cast h
    linarith
  have hnew : ((iter (mstep E C (a + 1) θ R) (P (ℓ + 1) ∪ P ℓ) K (φ a ℓ)).card : ℝ) ≤ S :=
    hm.trans (max_le hM0 ((mul_le_mul_of_nonneg_left hU hρ).trans hρS))
  have hval : ∀ j, mergeOne E C θ R K φ a ℓ P j =
      if j = ℓ then ∅ else if j = ℓ + 1 then iter (mstep E C (a + 1) θ R) (P (ℓ + 1) ∪ P ℓ) K (φ a ℓ)
      else P j := by
    intro j
    unfold mergeOne
    by_cases h1 : j = ℓ
    · subst h1; simp
    · rw [Function.update_of_ne h1]
      by_cases h2 : j = ℓ + 1
      · subst h2; simp
      · rw [Function.update_of_ne h2]; simp [h1, h2]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hval 0]
    split_ifs with h1 h2
    · simp; linarith
    · exact hnew.trans hSS
    · exact hP0
  · rw [hval j]
    split_ifs with h1 h2
    · simp [hS0]
    · exact hnew
    · exact hP j hj


lemma mergeUpTo_card {φ : ℕ → ℕ → Fin K → ι → Bool} {a : ℕ} {P : ℕ → Finset ι} {S S' M0 ρ : ℝ}
    (hρ : 0 ≤ ρ) (hM0 : M0 ≤ S) (hρS : ρ * (S + S') ≤ S) (hSS : S ≤ S')
    (hP0 : ((P 0).card : ℝ) ≤ S') (hP : ∀ j, j ≠ 0 → ((P j).card : ℝ) ≤ S) :
    ∀ m, (∀ ℓ ≤ m, ((iter (mstep E C (a + 1) θ R)
        (stage E C θ R K φ a P ℓ (ℓ + 1) ∪ stage E C θ R K φ a P ℓ ℓ) K (φ a ℓ)).card : ℝ) ≤
        max M0 (ρ * (stage E C θ R K φ a P ℓ (ℓ + 1) ∪ stage E C θ R K φ a P ℓ ℓ).card)) →
      (((mergeUpTo E C θ R K φ a m P 0).card : ℝ) ≤ S') ∧
        ∀ j, j ≠ 0 → ((mergeUpTo E C θ R K φ a m P j).card : ℝ) ≤ S := by
  intro m
  induction m with
  | zero =>
    intro hg
    exact mergeOne_card hρ hM0 hρS hSS hP0 hP (hg 0 le_rfl)
  | succ m ih =>
    intro hg
    obtain ⟨h0, h1⟩ := ih (fun ℓ hℓ => hg ℓ (by omega))
    exact mergeOne_card hρ hM0 hρS hSS h0 h1 (hg (m + 1) le_rfl)

/-- **Pool sizes of the threaded process on a good run.** With `S' = s0 + D·Lv·S`, `M0 ≤ S`,
`ρ (S + S') ≤ S`: at every boundary `a ≤ NE`, every level `≥ 1` has at most `S` copies, level 0 at
most `S'`, and level 0 is empty when the thread's epoch has just ended. -/
theorem tpools_card_le (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (NE s0 : ℕ) (M0 ρ S : ℝ)
    (hρ : 0 ≤ ρ) (hgood : GoodRunT E thr0 C θ R K D Lv Bt lev ωs φ NE s0 M0 ρ) (hM0 : M0 ≤ S)
    (hS0 : 0 ≤ S) (hρS : ρ * (S + (s0 + D * Lv * S)) ≤ S) :
    ∀ a ≤ NE, (∀ r ℓ, ℓ ≠ 0 → ((tpools E thr0 C θ R K D Lv Bt lev ωs φ a r ℓ).card : ℝ) ≤ S) ∧
      (∀ r, ((tpools E thr0 C θ R K D Lv Bt lev ωs φ a r 0).card : ℝ) ≤ s0 + D * Lv * S) ∧
      (∀ r, r < D → Bt r ∣ a → tpools E thr0 C θ R K D Lv Bt lev ωs φ a r 0 = ∅) := by
  classical
  have hD := hB.hD
  set S' : ℝ := s0 + D * Lv * S with hS'
  have hSS : S ≤ S' := by
    have : (1 : ℝ) ≤ D * Lv := by
      have : (1 : ℕ) ≤ D * Lv := Nat.one_le_iff_ne_zero.2 (by positivity)
      exact_mod_cast this
    nlinarith [Nat.cast_nonneg (α := ℝ) s0]
  intro a
  induction a with
  | zero => intro _; simp [tpools, hS0]; positivity
  | succ a ih =>
    intro ha
    obtain ⟨ihS, ih0, ihE⟩ := ih (by omega)
    set P := tpools E thr0 C θ R K D Lv Bt lev ωs φ a
    have hcan : canonT D Bt a < D := lt_of_le_of_lt (canonT_le a) (by omega)
    have hcdvd : Bt (canonT D Bt a) ∣ a := hB.canonT_dvd a
    -- the start pools
    have hst : ∀ r, (∀ ℓ, ℓ ≠ 0 → ((startPools E thr0 D Lv Bt ωs a P r ℓ).card : ℝ) ≤ S) ∧
        ((startPools E thr0 D Lv Bt ωs a P r 0).card : ℝ) ≤ S' := by
      intro r
      constructor
      · intro ℓ hℓ
        unfold startPools sample inherit
        simp only [hℓ, false_and, if_false]
        split_ifs
        · exact ihS r ℓ hℓ
        · exact ihS r ℓ hℓ
        · simp [hS0]
      · unfold startPools sample inherit
        simp only [true_and]
        by_cases hr1 : r < canonT D Bt a
        · have hnd : ¬ Bt r ∣ a := fun h => absurd (canonT_le_of_dvd (D := D) h) (by omega)
          simp only [hr1, if_true, hnd, false_and, if_false]
          exact ih0 r
        by_cases hr2 : r = canonT D Bt a
        · subst hr2
          simp only [lt_irrefl, if_false, if_true, hcdvd, hcan, and_self]
          have hz : P (canonT D Bt a) 0 = ∅ := ihE _ hcan hcdvd
          rw [hz, Finset.empty_union]
          -- inherited copies
          have hinh : (((Finset.Ioo (canonT D Bt a) D).biUnion
              (fun r' => (Finset.range Lv).biUnion (P r'))).card : ℝ) ≤ D * Lv * S := by
            have h1 := Finset.card_biUnion_le (s := Finset.Ioo (canonT D Bt a) D)
              (t := fun r' => (Finset.range Lv).biUnion (P r'))
            have h2 : ∀ r' ∈ Finset.Ioo (canonT D Bt a) D,
                (((Finset.range Lv).biUnion (P r')).card : ℝ) ≤ Lv * S := by
              intro r' hr'
              rw [Finset.mem_Ioo] at hr'
              have h3 := Finset.card_biUnion_le (s := Finset.range Lv) (t := P r')
              have h4 : ∀ ℓ' ∈ Finset.range Lv, ((P r' ℓ').card : ℝ) ≤ S := by
                intro ℓ' _
                by_cases h0 : ℓ' = 0
                · subst h0
                  rw [ihE r' hr'.2 ((hB.dvd_of_le hr'.1.le hr'.2).trans hcdvd)]; simp [hS0]
                · exact ihS r' ℓ' h0
              calc (((Finset.range Lv).biUnion (P r')).card : ℝ)
                  ≤ ∑ ℓ' ∈ Finset.range Lv, ((P r' ℓ').card : ℝ) := by exact_mod_cast h3
                _ ≤ ∑ _ℓ' ∈ Finset.range Lv, S := Finset.sum_le_sum h4
                _ = Lv * S := by simp
            calc (((Finset.Ioo (canonT D Bt a) D).biUnion
                  (fun r' => (Finset.range Lv).biUnion (P r'))).card : ℝ)
                ≤ ∑ r' ∈ Finset.Ioo (canonT D Bt a) D,
                    (((Finset.range Lv).biUnion (P r')).card : ℝ) := by exact_mod_cast h1
              _ ≤ ∑ _r' ∈ Finset.Ioo (canonT D Bt a) D, (Lv * S : ℝ) := Finset.sum_le_sum h2
              _ ≤ D * (Lv * S) := by
                rw [Finset.sum_const, nsmul_eq_mul]
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                have : (Finset.Ioo (canonT D Bt a) D).card ≤ D := by simp; omega
                exact_mod_cast this
              _ = D * Lv * S := by ring
          have hnew : ((newAtT E thr0 ωs a (canonT D Bt a)).card : ℝ) ≤ s0 := by
            exact_mod_cast hgood.1 a (by omega) _ hcan hcdvd
          calc (((Finset.Ioo (canonT D Bt a) D).biUnion
                (fun r' => (Finset.range Lv).biUnion (P r')) ∪
                newAtT E thr0 ωs a (canonT D Bt a)).card : ℝ)
              ≤ (((Finset.Ioo (canonT D Bt a) D).biUnion
                  (fun r' => (Finset.range Lv).biUnion (P r'))).card : ℝ) +
                (newAtT E thr0 ωs a (canonT D Bt a)).card := by exact_mod_cast Finset.card_union_le _ _
            _ ≤ S' := by rw [hS']; linarith
        · have hr3 : canonT D Bt a < r := by omega
          simp only [hr1, hr2, if_false]
          split_ifs with hs
          · rw [Finset.empty_union]
            have := hgood.1 a (by omega) r hs.2 hs.1
            have : ((newAtT E thr0 ωs a r).card : ℝ) ≤ s0 := by exact_mod_cast this
            have : (0 : ℝ) ≤ D * Lv * S := by positivity
            rw [hS']; linarith
          · simp; positivity
    refine ⟨?_, ?_, ?_⟩
    · intro r ℓ hℓ
      simp only [tpools]
      split_ifs with hB'
      · by_cases hrD : r < D
        · exact (mergeUpTo_card hρ hM0 hρS hSS (hst r).2 (hst r).1 (lev r a)
            (fun ℓ' hℓ' => hgood.2 a (by omega) r hrD hB' ℓ' hℓ')).2 ℓ hℓ
        · -- threads `≥ D` are empty
          have : ∀ j, startPools E thr0 D Lv Bt ωs a P r j = ∅ := by
            intro j; ext c; simp only [Finset.notMem_empty, iff_false]; intro hc
            have := (start_ok (E := E) (thr0 := thr0) (Bt := Bt) hD hLv
              (tpools_ok (E := E) (thr0 := thr0) (Bt := Bt) (C := C) (θ := θ) (R := R) (lev := lev)
                hD hLv hlev ωs φ a) ωs (x := a) c r j hc).2.2.2
            omega
          have hsub : ∀ c, c ∉ mergeUpTo E C θ R K (φ r) a (lev r a)
              (startPools E thr0 D Lv Bt ωs a P r) ℓ := by
            intro c hc
            obtain ⟨⟨j, hj⟩, -⟩ := mem_mergeUpTo _ _ ℓ c hc
            rw [this j] at hj; simp at hj
          rw [Finset.eq_empty_of_forall_notMem hsub]; simp [hS0]
      · exact (hst r).1 ℓ hℓ
    · intro r
      simp only [tpools]
      split_ifs with hB'
      · rw [mergeUpTo_zero_level]; simp; positivity
      · exact (hst r).2
    · intro r hrD hdvd
      simp only [tpools]
      rw [if_pos hdvd, mergeUpTo_zero_level]

end Pool.P0073
