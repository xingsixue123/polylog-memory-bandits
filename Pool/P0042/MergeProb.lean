import Pool.P0030.MergeCore
import Pool.P0034.Coins

/-!
# Goodness of a random (Bernoulli) filter set
-/

open Finset Real Pool.P0030 Pool.P0034

namespace Pool.P0042

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (C : ι → ℕ → ℝ) (t : ℕ) (θ : ℝ)
  (Q : Finset ι) (k : ℕ)

open Classical in
/-- Comparability set as a function of the breakpoint `τ` and the stage `r`. -/
noncomputable def D' (τ r : ℕ) (i : ι) : Finset ι :=
  Q.filter fun j => j < i ∧ Lint C j (E i) τ - 2 ^ r * θ ≤ Lint C i (E i) τ

theorem D_eq (ps : List ι) (i : ι) : D E C t θ Q ps i = D' E C θ Q (tau E t ps) ps.length i := by
  unfold D D'; rfl

theorem tau_mem (ps : List ι) (hps : ∀ p ∈ ps, p ∈ Q) : tau E t ps ∈ insert t (Q.image E) := by
  cases ps with
  | nil => simp [tau]
  | cons g rest => exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem E (hps g (by simp)))

variable {p : ℝ}

/-- **G1 fails with small probability.** -/
theorem prob_not_G1 (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rstar : ℕ) :
    prob p (fun ω => ¬ G1 E C t θ Q k (Fof Q ω) rstar) ≤
      ((insert t (Q.image E)).card * rstar * Q.card : ℕ) * (1 - p) ^ k := by
  classical
  set fam := (insert t (Q.image E)) ×ˢ (Finset.range rstar ×ˢ Q)
  let A : ℕ × ℕ × ι → (ι → Bool) → Prop := fun x ω =>
    k ≤ (D' E C θ Q x.1 x.2.1 x.2.2).card ∧ ∀ y ∈ D' E C θ Q x.1 x.2.1 x.2.2, ω y = false
  have hsub : ∀ ω, ¬ G1 E C t θ Q k (Fof Q ω) rstar → ∃ x ∈ fam, A x ω := by
    intro ω hω
    simp only [G1, not_forall, not_exists, not_and] at hω
    obtain ⟨ps, hlen, hpsQ, i, hiQ, hk, hno⟩ := hω
    refine ⟨(tau E t ps, ps.length, i), ?_, ?_, ?_⟩
    · simp only [fam, Finset.mem_product, Finset.mem_range]
      exact ⟨tau_mem E t Q ps hpsQ, hlen, hiQ⟩
    · rw [← D_eq]; exact hk
    · intro y hy
      rw [← D_eq] at hy
      by_contra hyt
      have hyt' : ω y = true := by simpa using hyt
      exact hno y (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, hyt'⟩) hy
  calc prob p (fun ω => ¬ G1 E C t θ Q k (Fof Q ω) rstar)
      ≤ prob p (fun ω => ∃ x ∈ fam, A x ω) := prob_mono hp0 hp1 hsub
    _ ≤ ∑ x ∈ fam, prob p (A x) := prob_exists_le hp0 hp1 fam A
    _ ≤ ∑ _x ∈ fam, (1 - p) ^ k := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hk : k ≤ (D' E C θ Q x.1 x.2.1 x.2.2).card
        · calc prob p (A x) ≤ prob p (fun ω => ∀ y ∈ D' E C θ Q x.1 x.2.1 x.2.2, ω y = false) :=
                prob_mono hp0 hp1 (fun ω h => h.2)
            _ = (1 - p) ^ (D' E C θ Q x.1 x.2.1 x.2.2).card := prob_all_false _
            _ ≤ (1 - p) ^ k := pow_le_pow_of_le_one (by linarith) (by linarith) hk
        · calc prob p (A x) ≤ prob p (fun _ => False) := prob_mono hp0 hp1 (fun ω h => hk h.1)
            _ = 0 := by
                unfold prob
                exact Finset.sum_eq_zero fun ω _ => by rw [ind_neg (A := fun _ => False) id]; ring
            _ ≤ (1 - p) ^ k := pow_nonneg (by linarith) k
    _ = (fam.card : ℝ) * (1 - p) ^ k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
        congr 1
        simp only [fam, Finset.card_product, Finset.card_range]
        push_cast; ring

/-- The `k` latest elements of `U` (those with fewer than `k` elements of `U` above them). -/
noncomputable def topK (U : Finset ι) (k : ℕ) : Finset ι := U.filter fun f => (U.filter (f < ·)).card < k

omit [Fintype ι] in
theorem le_card_topK (U : Finset ι) (k : ℕ) (hk : k ≤ U.card) : k ≤ (topK U k).card := by
  classical
  set rank : ι → ℕ := fun f => (U.filter (f < ·)).card with hrank
  have hlt : ∀ f g, f ∈ U → g ∈ U → f < g → rank g < rank f := by
    intro f g hf hg hfg
    apply Finset.card_lt_card
    refine ⟨fun z hz => ?_, ?_⟩
    · simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hfg.trans hz.2⟩
    · intro hsub
      have := hsub (Finset.mem_filter.mpr ⟨hg, hfg⟩)
      simp at this
  have hinj : Set.InjOn rank U := by
    intro f hf g hg hfg
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd hfg (hlt f g hf hg h).ne'
    · exact absurd hfg (hlt g f hg hf h).ne
  have hrange : U.image rank ⊆ Finset.range U.card := by
    intro m hm
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hm
    simp only [Finset.mem_range]
    apply Finset.card_lt_card
    refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
    have := hsub hf
    simp at this
  have himg : U.image rank = Finset.range U.card :=
    Finset.eq_of_subset_of_card_le hrange (by rw [Finset.card_range, Finset.card_image_of_injOn hinj])
  have htop : (topK U k).image rank = (Finset.range U.card).filter (fun m : ℕ => m < k) := by
    rw [← himg]
    ext m
    simp only [topK, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨f, ⟨hf, hfk⟩, rfl⟩; exact ⟨⟨f, hf, rfl⟩, hfk⟩
    · rintro ⟨⟨f, hf, rfl⟩, hfk⟩; exact ⟨f, ⟨hf, hfk⟩, rfl⟩
  have hfilt : (Finset.range U.card).filter (fun m : ℕ => m < k) = Finset.range k := by
    ext m; simp only [Finset.mem_filter, Finset.mem_range]; omega
  have hsub : (topK U k : Set ι) ⊆ (U : Set ι) := fun x hx => (Finset.mem_filter.mp hx).1
  have := Finset.card_image_of_injOn (s := topK U k) (hinj.mono hsub)
  rw [htop, hfilt, Finset.card_range] at this
  rw [← this]

/-- **G2 fails with small probability.** -/
theorem prob_not_G2 (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rstar : ℕ) :
    prob p (fun ω => ¬ G2 E C t θ Q k (Fof Q ω) rstar) ≤
      (∑ m ∈ Finset.range rstar, (Fintype.card ι : ℝ) ^ m) * (1 - p) ^ k := by
  classical
  set fam := (Finset.range rstar).sigma fun m => (Finset.univ : Finset (Fin m → ι))
  let A : (Σ m, Fin m → ι) → (ι → Bool) → Prop := fun x ω =>
    k ≤ (Uof E C t θ Q k (List.ofFn x.2)).card ∧
      ∀ f ∈ topK (Uof E C t θ Q k (List.ofFn x.2)) k, ω f = false
  have hsub : ∀ ω, ¬ G2 E C t θ Q k (Fof Q ω) rstar → ∃ x ∈ fam, A x ω := by
    intro ω hω
    simp only [G2, not_forall, not_exists, not_and] at hω
    obtain ⟨ps, hlen, _, hk, hno⟩ := hω
    refine ⟨⟨ps.length, ps.get⟩, ?_, ?_, ?_⟩
    · simp [fam, hlen]
    · simpa [List.ofFn_get] using hk
    · intro f hf
      simp only [List.ofFn_get] at hf
      obtain ⟨hfU, hfk⟩ := Finset.mem_filter.mp hf
      by_contra hft
      have hft' : ω f = true := by simpa using hft
      have hfQ : f ∈ Q := Wof_sub E C t θ Q k ps (Finset.mem_sdiff.mp hfU).1
      exact hno f (Finset.mem_filter.mpr ⟨hfQ, hft'⟩) hfU hfk
  calc prob p (fun ω => ¬ G2 E C t θ Q k (Fof Q ω) rstar)
      ≤ prob p (fun ω => ∃ x ∈ fam, A x ω) := prob_mono hp0 hp1 hsub
    _ ≤ ∑ x ∈ fam, prob p (A x) := prob_exists_le hp0 hp1 fam A
    _ ≤ ∑ _x ∈ fam, (1 - p) ^ k := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases hk : k ≤ (Uof E C t θ Q k (List.ofFn x.2)).card
        · calc prob p (A x) ≤ prob p (fun ω => ∀ f ∈ topK (Uof E C t θ Q k (List.ofFn x.2)) k,
                  ω f = false) := prob_mono hp0 hp1 (fun ω h => h.2)
            _ = (1 - p) ^ (topK (Uof E C t θ Q k (List.ofFn x.2)) k).card := prob_all_false _
            _ ≤ (1 - p) ^ k :=
                pow_le_pow_of_le_one (by linarith) (by linarith) (le_card_topK _ k hk)
        · calc prob p (A x) ≤ prob p (fun _ => False) := prob_mono hp0 hp1 (fun ω h => hk h.1)
            _ = 0 := by
                unfold prob
                exact Finset.sum_eq_zero fun ω _ => by rw [ind_neg (A := fun _ => False) id]; ring
            _ ≤ (1 - p) ^ k := pow_nonneg (by linarith) k
    _ = (fam.card : ℝ) * (1 - p) ^ k := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
        congr 1
        simp only [fam, Finset.card_sigma, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
        push_cast; rfl

/-- **One Filter round with a Bernoulli filter set** (probabilistic version of PR23 Lemma 4.4's step):
the filter round fails to shrink the pool to `|Q| + 2c − a` with probability at most the sum of the three
failure probabilities (G1, G2, and `|F| > c`). -/
theorem prob_filterRound_bad (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE : Monotone E) (hQt : ∀ i ∈ Q, E i ≤ t)
    (Tmax : ℝ) (hL : ∀ i ∈ Q, ∀ a b, a ≤ b → b ≤ t → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (rstar a : ℕ) (hr : 1 ≤ rstar) (hT : Tmax ≤ 2 ^ (rstar - 1) * θ)
    (hsize : a + k + (rstar - 1) * (a + 2 * k) ≤ Q.card) (c : ℕ) {κ : ℝ} (hκ : 0 ≤ κ) :
    prob p (fun ω => Q.card + 2 * c < (filterRound E C t θ Q (Fof Q ω) rstar).card + a) ≤
      ((insert t (Q.image E)).card * rstar * Q.card : ℕ) * (1 - p) ^ k +
      (∑ m ∈ Finset.range rstar, (Fintype.card ι : ℝ) ^ m) * (1 - p) ^ k +
      exp (p * Q.card * (exp κ - 1) - κ * (c + 1)) := by
  classical
  have himp : ∀ ω, Q.card + 2 * c < (filterRound E C t θ Q (Fof Q ω) rstar).card + a →
      (¬ G1 E C t θ Q k (Fof Q ω) rstar ∨ ¬ G2 E C t θ Q k (Fof Q ω) rstar) ∨
        ((c : ℝ) + 1 ≤ (Fof Q ω).card) := by
    intro ω hω
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    have hF : (Fof Q ω).card ≤ c := by
      have : ((Fof Q ω).card : ℝ) < c + 1 := h3
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
    have := card_filterRound_le E C t θ Q k hE hQt Tmax hL (Fof Q ω) rstar a hr hT hsize h1 h2
    omega
  calc prob p (fun ω => Q.card + 2 * c < (filterRound E C t θ Q (Fof Q ω) rstar).card + a)
      ≤ prob p (fun ω => (¬ G1 E C t θ Q k (Fof Q ω) rstar ∨ ¬ G2 E C t θ Q k (Fof Q ω) rstar) ∨
        ((c : ℝ) + 1 ≤ (Fof Q ω).card)) := prob_mono hp0 hp1 himp
    _ ≤ prob p (fun ω => ¬ G1 E C t θ Q k (Fof Q ω) rstar ∨ ¬ G2 E C t θ Q k (Fof Q ω) rstar) +
        prob p (fun ω => (c : ℝ) + 1 ≤ (Fof Q ω).card) := prob_or_le hp0 hp1 _ _
    _ ≤ (prob p (fun ω => ¬ G1 E C t θ Q k (Fof Q ω) rstar) +
          prob p (fun ω => ¬ G2 E C t θ Q k (Fof Q ω) rstar)) +
        prob p (fun ω => (c : ℝ) + 1 ≤ (Fof Q ω).card) := by
        gcongr; exact prob_or_le hp0 hp1 _ _
    _ ≤ _ := by
        have h1 := prob_not_G1 E C t θ Q k hp0 hp1 rstar
        have h2 := prob_not_G2 E C t θ Q k hp0 hp1 rstar
        have h3 := prob_card_ge hp0 hp1 Q hκ ((c : ℝ) + 1)
        linarith

end Pool.P0042
