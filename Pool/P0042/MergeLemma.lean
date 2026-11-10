import Pool.P0042.MergeProb
import Pool.P0042.MultiRound

/-!
# A variant of PR23's Merge lemma (Lemma 4.4) for the chain-cover rule: iterated Bernoulli filtering shrinks the pool
-/

open Finset Real Pool.P0030 Pool.P0034

namespace Pool.P0042

variable {ι : Type*} [LinearOrder ι] [Fintype ι]

/-- Deterministic consequence of "no bad round": geometric shrinking down to `M0`. -/
theorem card_iter_le (step : Finset ι → (ι → Bool) → Finset ι)
    (hstep : ∀ Q' y, step Q' y ⊆ Q') (Q : Finset ι) (M0 ε : ℝ) (hM0 : 0 ≤ M0) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ K (ω : Fin K → ι → Bool),
      ¬ anyBad step Q (fun Q' y => M0 ≤ Q'.card ∧ (1 - ε) * Q'.card < (step Q' y).card) K ω →
      ((iter step Q K ω).card : ℝ) ≤ max M0 ((1 - ε) ^ K * Q.card) := by
  intro K
  induction K with
  | zero => intro ω _; simp [iter]
  | succ K ih =>
    intro ω hω
    simp only [anyBad, not_or, not_and, not_lt] at hω
    obtain ⟨hprev, hnow⟩ := hω
    have hK := ih (Fin.init ω) hprev
    simp only [iter]
    set Q' := iter step Q K (Fin.init ω)
    have hsub : ((step Q' (ω (Fin.last K))).card : ℝ) ≤ Q'.card := by
      exact_mod_cast Finset.card_le_card (hstep _ _)
    by_cases hM : M0 ≤ (Q'.card : ℝ)
    · have h1 := hnow hM
      have hpow : (1 - ε) ^ (K + 1) * Q.card = (1 - ε) * ((1 - ε) ^ K * Q.card) := by ring
      rcases le_total M0 ((1 - ε) ^ K * Q.card) with h | h
      · rw [max_eq_right h] at hK
        calc ((step Q' (ω (Fin.last K))).card : ℝ) ≤ (1 - ε) * Q'.card := h1
          _ ≤ (1 - ε) * ((1 - ε) ^ K * Q.card) := mul_le_mul_of_nonneg_left hK (by linarith)
          _ ≤ max M0 ((1 - ε) ^ (K + 1) * Q.card) := by rw [hpow]; exact le_max_right _ _
      · rw [max_eq_left h] at hK
        calc ((step Q' (ω (Fin.last K))).card : ℝ) ≤ (1 - ε) * Q'.card := h1
          _ ≤ (1 - ε) * M0 := mul_le_mul_of_nonneg_left hK (by linarith)
          _ ≤ M0 := by nlinarith
          _ ≤ _ := le_max_left _ _
    · push Not at hM
      calc ((step Q' (ω (Fin.last K))).card : ℝ) ≤ Q'.card := hsub
        _ ≤ M0 := hM.le
        _ ≤ _ := le_max_left _ _

variable (E : ι → ℕ) (C : ι → ℕ → ℝ) (t : ℕ) (θ : ℝ)

/-- One Merge iteration: filter with a fresh Bernoulli filter set. -/
noncomputable def mstep (L : ℕ) (Q' : Finset ι) (y : ι → Bool) : Finset ι :=
  filterRound E C t θ Q' (Fof Q' y) L

omit [Fintype ι] in
theorem mstep_sub (L : ℕ) (Q' : Finset ι) (y : ι → Bool) : mstep E C t θ L Q' y ⊆ Q' := by
  classical
  intro x hx
  unfold mstep filterRound at hx
  rcases Finset.mem_union.mp hx with h | h
  · exact (Finset.mem_filter.mp h).1
  · exact (Finset.mem_filter.mp h).1

/-- The uniform per-iteration failure bound. -/
noncomputable def delta (N : ℕ) (p : ℝ) (L k : ℕ) (M0 : ℝ) : ℝ :=
  (((N + 1) * L * N : ℕ) : ℝ) * (1 - p) ^ k +
    (∑ m ∈ Finset.range L, (N : ℝ) ^ m) * (1 - p) ^ k + exp (-(M0 / (32 * L)))

theorem delta_nonneg {N : ℕ} {p : ℝ} (hp1 : p ≤ 1) {L k : ℕ} {M0 : ℝ} : 0 ≤ delta N p L k M0 := by
  unfold delta
  have : 0 ≤ (1 - p) ^ k := pow_nonneg (by linarith) k
  positivity

/-- **One Merge iteration fails with probability at most `delta`**, uniformly over pools of size `≥ M0`. -/
theorem prob_bad_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE : Monotone E) (Q' : Finset ι)
    (hQt : ∀ i ∈ Q', E i ≤ t)
    (Tmax : ℝ) (hL : ∀ i ∈ Q', ∀ a b, a ≤ b → b ≤ t → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (L k : ℕ) (hL1 : 1 ≤ L) (hT : Tmax ≤ 2 ^ (L - 1) * θ) (M0 : ℝ) (hM0 : 16 * L ≤ M0)
    (hk : 4 * L * k ≤ M0) (hp : p * (exp 1 - 1) ≤ 1 / (32 * L)) :
    prob p (fun y => M0 ≤ Q'.card ∧ (1 - 1 / (4 * L : ℝ)) * Q'.card < (mstep E C t θ L Q' y).card)
      ≤ delta (Fintype.card ι) p L k M0 := by
  classical
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hδnn : 0 ≤ delta (Fintype.card ι) p L k M0 := delta_nonneg hp1
  by_cases hM : M0 ≤ (Q'.card : ℝ)
  swap
  · calc prob p _ ≤ prob p (fun _ => False) := prob_mono hp0 hp1 (fun y h => hM h.1)
      _ = 0 := by
          unfold prob
          exact Finset.sum_eq_zero fun ω _ => by rw [ind_neg (A := fun _ => False) id]; ring
      _ ≤ _ := hδnn
  set M := Q'.card with hMdef
  set a := M / (2 * L) with ha
  set c := M / (16 * L) with hc
  have hMreal : (16 * L : ℝ) ≤ M := hM0.trans hM
  have hMk : 4 * L * k ≤ M := by exact_mod_cast (show ((4 * L * k : ℕ) : ℝ) ≤ M by push_cast; linarith)
  -- size condition
  have h2a : 2 * L * a ≤ M := by rw [ha]; exact Nat.mul_div_le M (2 * L)
  have hsize : a + k + (L - 1) * (a + 2 * k) ≤ Q'.card := by
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [← hMdef]
    nlinarith [h2a, hMk]
  -- event inclusion
  have hincl : ∀ y, (M0 ≤ (Q'.card : ℝ) ∧ (1 - 1 / (4 * L : ℝ)) * Q'.card < (mstep E C t θ L Q' y).card) →
      Q'.card + 2 * c < (filterRound E C t θ Q' (Fof Q' y) L).card + a := by
    intro y ⟨_, hy⟩
    have ha' : (M : ℝ) / (2 * L) - 1 ≤ a := by
      have h0 := Nat.lt_div_mul_add (show 0 < 2 * L by omega) (a := M)
      have h : ((M : ℕ) : ℝ) < ((M / (2 * L) * (2 * L) + 2 * L : ℕ) : ℝ) := by exact_mod_cast h0
      push_cast at h
      rw [div_sub_one (by positivity), div_le_iff₀ (by positivity)]
      rw [ha]; linarith
    have hc' : (c : ℝ) ≤ M / (16 * L) := by
      rw [hc, le_div_iff₀ (by positivity)]
      have h0 := Nat.div_mul_le_self M (16 * L)
      have h : ((M / (16 * L) * (16 * L) : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast h0
      push_cast at h
      linarith
    have key : (M : ℝ) - a + 2 * c ≤ (1 - 1 / (4 * L : ℝ)) * M := by
      have e1 : (M : ℝ) / (2 * L) = 4 * (M / (8 * L)) := by field_simp; ring
      have e2 : (M : ℝ) / (16 * L) = (M / (8 * L)) / 2 := by field_simp; ring
      have e3 : (1 - 1 / (4 * L : ℝ)) * M = M - 2 * (M / (8 * L)) := by field_simp; ring
      have h8 : (1 : ℝ) ≤ M / (8 * L) := by rw [le_div_iff₀ (by positivity)]; linarith
      rw [e3]; rw [e1] at ha'; rw [e2] at hc'; linarith
    have : (Q'.card : ℝ) + 2 * c < (filterRound E C t θ Q' (Fof Q' y) L).card + a := by
      have hy' : (1 - 1 / (4 * L : ℝ)) * M < (filterRound E C t θ Q' (Fof Q' y) L).card := hy
      linarith
    exact_mod_cast this
  have hmain := prob_filterRound_bad E C t θ Q' k hp0 hp1 hE hQt Tmax
    hL L a hL1 hT hsize c (κ := 1) zero_le_one
  calc prob p _ ≤ prob p (fun y => Q'.card + 2 * c < (filterRound E C t θ Q' (Fof Q' y) L).card + a) :=
        prob_mono hp0 hp1 hincl
    _ ≤ _ := hmain
    _ ≤ delta (Fintype.card ι) p L k M0 := by
        unfold delta
        have hq : 0 ≤ (1 - p) ^ k := pow_nonneg (by linarith) k
        have hI : ((insert t (Q'.image E)).card : ℝ) ≤ Fintype.card ι + 1 := by
          have := Finset.card_insert_le t (Q'.image E)
          have h2 := (Finset.card_image_le (s := Q') (f := E)).trans (Finset.card_le_univ Q')
          exact_mod_cast (by omega : (insert t (Q'.image E)).card ≤ Fintype.card ι + 1)
        have hQ : (Q'.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ Q'
        have h1 : ((((insert t (Q'.image E)).card * L * Q'.card : ℕ) : ℝ)) * (1 - p) ^ k ≤
            (((Fintype.card ι + 1) * L * Fintype.card ι : ℕ) : ℝ) * (1 - p) ^ k := by
          apply mul_le_mul_of_nonneg_right _ hq
          push_cast
          apply mul_le_mul (mul_le_mul_of_nonneg_right hI (by positivity)) hQ (by positivity)
            (by positivity)
        have h3 : exp (p * Q'.card * (exp 1 - 1) - 1 * (c + 1)) ≤ exp (-(M0 / (32 * L))) := by
          apply exp_le_exp.mpr
          have hc1 : (M : ℝ) / (16 * L) ≤ c + 1 := by
            rw [hc, div_le_iff₀ (by positivity)]
            have h0 := Nat.lt_div_mul_add (show 0 < 16 * L by omega) (a := M)
            have h : ((M : ℕ) : ℝ) < ((M / (16 * L) * (16 * L) + 16 * L : ℕ) : ℝ) := by
              exact_mod_cast h0
            push_cast at h
            linarith
          have hpm : p * M * (exp 1 - 1) ≤ M / (32 * L) := by
            calc p * M * (exp 1 - 1) = (p * (exp 1 - 1)) * M := by ring
              _ ≤ 1 / (32 * L) * M := mul_le_mul_of_nonneg_right hp (by positivity)
              _ = M / (32 * L) := by ring
          have e : (M : ℝ) / (16 * L) = 2 * (M / (32 * L)) := by field_simp; ring
          have hMM : M0 / (32 * L) ≤ (M : ℝ) / (32 * L) := div_le_div_of_nonneg_right hM (by positivity)
          rw [← hMdef]; linarith
        linarith

/-- **Merge lemma for the chain-cover filter rule** (a variant of PR23's Lemma 4.4: P0030's chain cover,
`K` forced iterations, no size-estimation stop). The entry and interval-loss hypotheses are needed only on
the initial pool `Q`. After `K` iterations of filtering with fresh Bernoulli(`p`) filter sets, the pool has at most `max M0 ((1 − 1/(4L))^K |Q|)` experts, except
with probability at most `K · delta`. -/
theorem merge_lemma {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE : Monotone E) (Q : Finset ι)
    (hQt : ∀ i ∈ Q, E i ≤ t)
    (Tmax : ℝ) (hL : ∀ i ∈ Q, ∀ a b, a ≤ b → b ≤ t → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (L k : ℕ) (hL1 : 1 ≤ L) (hT : Tmax ≤ 2 ^ (L - 1) * θ) (M0 : ℝ) (hM0 : 16 * L ≤ M0)
    (hk : 4 * L * k ≤ M0) (hp : p * (exp 1 - 1) ≤ 1 / (32 * L)) (K : ℕ) :
    probK p K (fun ω => max M0 ((1 - 1 / (4 * L : ℝ)) ^ K * Q.card) <
        (iter (mstep E C t θ L) Q K ω).card) ≤ K * delta (Fintype.card ι) p L k M0 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hL1' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hε1 : 1 / (4 * L : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  calc probK p K _ ≤ probK p K (anyBad (mstep E C t θ L) Q
        (fun Q' y => M0 ≤ Q'.card ∧ (1 - 1 / (4 * L : ℝ)) * Q'.card < (mstep E C t θ L Q' y).card) K) := by
        apply probK_mono hp0 hp1
        intro ω hω
        by_contra hnb
        have := card_iter_le (mstep E C t θ L) (mstep_sub E C t θ L) Q M0 (1 / (4 * L : ℝ))
          (by linarith) (by positivity) hε1 K ω hnb
        linarith
    _ ≤ probK p K (anyBad (mstep E C t θ L) Q (fun Q' y => Q' ⊆ Q ∧
          (M0 ≤ Q'.card ∧ (1 - 1 / (4 * L : ℝ)) * Q'.card < (mstep E C t θ L Q' y).card)) K) :=
        probK_mono hp0 hp1 (anyBad_sub (mstep E C t θ L) Q (mstep_sub E C t θ L) _ K)
    _ ≤ K * delta (Fintype.card ι) p L k M0 := by
        refine probK_anyBad_le (mstep E C t θ L) Q hp0 hp1 _ _ (fun Q' => ?_) K
        by_cases hsub : Q' ⊆ Q
        · calc prob p _ ≤ prob p (fun y => M0 ≤ Q'.card ∧
                (1 - 1 / (4 * L : ℝ)) * Q'.card < (mstep E C t θ L Q' y).card) :=
                prob_mono hp0 hp1 (fun y h => h.2)
            _ ≤ _ := prob_bad_le E C t θ hp0 hp1 hE Q' (fun i hi => hQt i (hsub hi)) Tmax
                (fun i hi => hL i (hsub hi)) L k hL1 hT M0 hM0 hk hp
        · calc prob p _ ≤ prob p (fun _ => False) := prob_mono hp0 hp1 (fun y h => hsub h.1)
            _ = 0 := by
                unfold prob
                exact Finset.sum_eq_zero fun ω _ => by rw [ind_neg (A := fun _ => False) id]; ring
            _ ≤ _ := delta_nonneg hp1

end Pool.P0042
