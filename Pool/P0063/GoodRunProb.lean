import Pool.P0052.PoolProcess
import Pool.P0046.Bridge

/-!
# The probability that P0052's sub-pool process has a good run (union bound over all samples and merge iterations)

All coins of a run are one array `ω : Slot NE Lt K → ι → Bool` of independent bits (P0046's `bw2`):
* the sampling slot `inl a` (`a < NE`): copy `c` with `E c = a` is sampled iff `ω (inl a) c` (probability `ps`);
* the filter slot `inr (a, ℓ, k)`: the filter bits of iteration `k` of the merge into level `ℓ + 1` at the end of epoch
  `a` (probability `p`).
`ωsOf` and `φOf` read P0052's sampling and filter coins off the array.

`prob_not_goodRun`: the run is not good (P0052's `GoodRun`) with probability at most `NE · δs + NE (Lt+1) K · δ`.
Here `δs` bounds the probability that one epoch samples more than `s0` copies, and `δ` is P0042's one-iteration bound
`delta`. Each merge iteration's filter is fresh given everything before it (P0046's `fresh_slot_le`).
-/

open Finset Pool.P0030 Pool.P0034 Pool.P0042 Pool.P0046 Pool.P0052

namespace Pool.P0063

section Congr

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ) (R K : ℕ) (lev : ℕ → ℕ)

theorem mergeUpTo_congr (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) :
    ∀ m, (∀ ℓ ≤ m, φ a ℓ = φ' a ℓ) → ∀ P, mergeUpTo E C θ R K φ a m P = mergeUpTo E C θ R K φ' a m P := by
  intro m
  induction m with
  | zero => intro h P; simp only [mergeUpTo, mergeOne, h 0 le_rfl]
  | succ m ih =>
    intro h P
    simp only [mergeUpTo, mergeOne]
    rw [ih (fun ℓ hℓ => h ℓ (by omega)) P, h (m + 1) le_rfl]

theorem pools_congr (ωs : ι → Bool) (φ φ' : ℕ → ℕ → Fin K → ι → Bool) :
    ∀ a, (∀ a' < a, φ a' = φ' a') → pools E C θ R K lev ωs φ a = pools E C θ R K lev ωs φ' a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    simp only [pools]
    rw [ih (fun a' ha' => h a' (by omega))]
    exact mergeUpTo_congr E C θ R K φ φ' a (lev a) (fun ℓ _ => by rw [h a (by omega)]) _

theorem beforeMerge_congr (ωs : ι → Bool) (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (a ℓ : ℕ)
    (h1 : ∀ a' < a, φ a' = φ' a') (h2 : ∀ ℓ' < ℓ, φ a ℓ' = φ' a ℓ') :
    beforeMerge E C θ R K lev ωs φ a ℓ = beforeMerge E C θ R K lev ωs φ' a ℓ := by
  cases ℓ with
  | zero => simp only [beforeMerge]; rw [pools_congr E C θ R K lev ωs φ φ' a h1]
  | succ m =>
    simp only [beforeMerge]
    rw [pools_congr E C θ R K lev ωs φ φ' a h1,
      mergeUpTo_congr E C θ R K φ φ' a m (fun ℓ' hℓ' => h2 ℓ' (by omega))]

/-- Members of a merge output come from its input levels. -/
theorem mem_mergeUpTo (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) :
    ∀ m (P : ℕ → Finset ι) j, ∀ c ∈ mergeUpTo E C θ R K φ a m P j, ∃ i, c ∈ P i := by
  have hone : ∀ ℓ (P : ℕ → Finset ι) j, ∀ c ∈ mergeOne E C θ R K φ a ℓ P j, ∃ i, c ∈ P i := by
    intro ℓ P j c hc
    unfold mergeOne at hc
    by_cases hj : j = ℓ
    · subst hj; simp at hc
    · rw [Function.update_of_ne hj] at hc
      by_cases hj' : j = ℓ + 1
      · subst hj'
        rw [Function.update_self] at hc
        have := iter_sub (mstep E C (a + 1) θ R) (P (ℓ + 1) ∪ P ℓ) (mstep_sub E C (a + 1) θ R) K (φ a ℓ) hc
        rcases Finset.mem_union.mp this with h | h
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      · rw [Function.update_of_ne hj'] at hc; exact ⟨j, hc⟩
  intro m
  induction m with
  | zero => exact hone 0
  | succ m ih =>
    intro P j c hc
    obtain ⟨i, hi⟩ := hone (m + 1) _ j c hc
    exact ih P i c hi

/-- Every copy in the pools after epoch `a` entered before epoch `a`. -/
theorem E_lt_of_mem_pools (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) :
    ∀ a ℓ, ∀ c ∈ pools E C θ R K lev ωs φ a ℓ, E c < a := by
  intro a
  induction a with
  | zero => intro ℓ c hc; simp [pools] at hc
  | succ a ih =>
    intro ℓ c hc
    simp only [pools] at hc
    obtain ⟨i, hi⟩ := mem_mergeUpTo E C θ R K φ a _ _ ℓ c hc
    by_cases h0 : i = 0
    · subst h0
      rw [Function.update_self] at hi
      rcases Finset.mem_union.mp hi with h | h
      · have := ih 0 c h; omega
      · simp only [newAt, Finset.mem_filter] at h; omega
    · rw [Function.update_of_ne h0] at hi
      have := ih i c hi; omega

/-- Every copy in the pools just before a merge at the end of epoch `a` entered at or before `a`. -/
theorem E_le_of_mem_beforeMerge (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) (a ℓ j : ℕ) :
    ∀ c ∈ beforeMerge E C θ R K lev ωs φ a ℓ j, E c ≤ a := by
  have hstart : ∀ i, ∀ c ∈ Function.update (pools E C θ R K lev ωs φ a) 0
      (pools E C θ R K lev ωs φ a 0 ∪ newAt E ωs a) i, E c ≤ a := by
    intro i c hc
    by_cases h0 : i = 0
    · subst h0
      rw [Function.update_self] at hc
      rcases Finset.mem_union.mp hc with h | h
      · exact (E_lt_of_mem_pools E C θ R K lev ωs φ a 0 c h).le
      · simp only [newAt, Finset.mem_filter] at h; omega
    · rw [Function.update_of_ne h0] at hc
      exact (E_lt_of_mem_pools E C θ R K lev ωs φ a i c hc).le
  intro c hc
  cases ℓ with
  | zero => exact hstart j c hc
  | succ m =>
    obtain ⟨i, hi⟩ := mem_mergeUpTo E C θ R K φ a m _ j c hc
    exact hstart i c hi

end Congr

section Iter

variable {X : Type*} [Fintype X] [DecidableEq X] (step : Finset X → (X → Bool) → Finset X) (Q : Finset X)

/-- A bad sequence has a first-order bad round: some round `k` is bad for its own input. -/
theorem exists_bad_of_anyBad (bad : Finset X → (X → Bool) → Prop) :
    ∀ (K : ℕ) (ω : Fin K → X → Bool), anyBad step Q bad K ω →
      ∃ k : Fin K, bad (iter step Q k (fun j => ω (Fin.castLE k.2.le j))) (ω k) := by
  intro K
  induction K with
  | zero => intro ω h; exact absurd h id
  | succ K ih =>
    intro ω h
    rcases h with h | h
    · obtain ⟨k, hk⟩ := ih (Fin.init ω) h
      refine ⟨k.castSucc, ?_⟩
      have e1 : (fun j : Fin k => Fin.init ω (Fin.castLE k.2.le j)) =
          (fun j : Fin k => ω (Fin.castLE (Fin.castSucc k).2.le j)) := by
        funext j; rfl
      rw [e1] at hk
      exact hk
    · exact ⟨Fin.last K, h⟩

end Iter

/-- Slots of the coin array: one sampling slot per epoch and one filter slot per merge iteration. -/
abbrev Slot (NE Lt K : ℕ) := Fin NE ⊕ (Fin NE × Fin (Lt + 1) × Fin K)

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ) (R K : ℕ) (lev : ℕ → ℕ)
variable {NE Lt : ℕ}

/-- Probabilities of the array: `ps` on sampling slots, `p` on filter slots. -/
def qOf (ps p : ℝ) : Slot NE Lt K → ι → ℝ
  | Sum.inl _, _ => ps
  | Sum.inr _, _ => p

/-- Sampling coins read off the array. -/
def ωsOf (ω : Slot NE Lt K → ι → Bool) (c : ι) : Bool :=
  if h : E c < NE then ω (Sum.inl ⟨E c, h⟩) c else false

/-- Filter coins read off the array (`false` outside the array). -/
def φOf (ω : Slot NE Lt K → ι → Bool) (a ℓ : ℕ) (k : Fin K) (c : ι) : Bool :=
  if h : a < NE ∧ ℓ < Lt + 1 then ω (Sum.inr (⟨a, h.1⟩, ⟨ℓ, h.2⟩, k)) c else false

theorem φOf_eq (ω : Slot NE Lt K → ι → Bool) (a : Fin NE) (ℓ : Fin (Lt + 1)) (k : Fin K) :
    φOf K ω a ℓ k = ω (Sum.inr (a, ℓ, k)) := by
  funext c; simp [φOf, a.2, ℓ.2]

/-- Arrays agreeing off the filter slot `(a, ℓ, k)` give the same coins except at that iteration. -/
theorem φOf_agree (ω ω' : Slot NE Lt K → ι → Bool) (s0 : Fin NE × Fin (Lt + 1) × Fin K)
    (h : ∀ s, s ≠ Sum.inr s0 → ω s = ω' s) (a ℓ : ℕ) (k : Fin K)
    (hne : ¬ (a = s0.1.val ∧ ℓ = s0.2.1.val ∧ k = s0.2.2)) :
    φOf K ω a ℓ k = φOf K ω' a ℓ k := by
  funext c
  unfold φOf
  split_ifs with hh
  · rw [h]
    intro heq
    apply hne
    have h' := Sum.inr_injective heq
    rw [Prod.ext_iff, Prod.ext_iff] at h'
    exact ⟨congrArg Fin.val h'.1, congrArg Fin.val h'.2.1, h'.2.2⟩
  · rfl

theorem ωsOf_agree (ω ω' : Slot NE Lt K → ι → Bool) (s0 : Fin NE × Fin (Lt + 1) × Fin K)
    (h : ∀ s, s ≠ Sum.inr s0 → ω s = ω' s) : ωsOf E K ω = ωsOf E K ω' := by
  funext c
  unfold ωsOf
  split_ifs with hh
  · rw [h _ (by simp)]
  · rfl

/-- The pool entering a merge (levels `ℓ+1` and `ℓ` just before it). -/
noncomputable def mergeIn (ω : Slot NE Lt K → ι → Bool) (a ℓ : ℕ) : Finset ι :=
  beforeMerge E C θ R K lev (ωsOf E K ω) (φOf K ω) a ℓ (ℓ + 1) ∪
    beforeMerge E C θ R K lev (ωsOf E K ω) (φOf K ω) a ℓ ℓ

/-- The pool entering iteration `k` of the merge `(a, ℓ)`. -/
noncomputable def iterIn (ω : Slot NE Lt K → ι → Bool) (a ℓ : ℕ) (k : Fin K) : Finset ι :=
  iter (mstep E C (a + 1) θ R) (mergeIn E C θ R K lev ω a ℓ) k (fun j => φOf K ω a ℓ (Fin.castLE k.2.le j))

/-- **Locality**: the input of iteration `(a, ℓ, k)` does not read the bits of its own slot. -/
theorem iterIn_local (s0 : Fin NE × Fin (Lt + 1) × Fin K) (ω ω' : Slot NE Lt K → ι → Bool)
    (h : ∀ s, s ≠ Sum.inr s0 → ω s = ω' s) :
    iterIn E C θ R K lev ω s0.1 s0.2.1 s0.2.2 = iterIn E C θ R K lev ω' s0.1 s0.2.1 s0.2.2 := by
  obtain ⟨a, ℓ, k⟩ := s0
  have hφ1 : ∀ a' < a.val, φOf K ω a' = φOf K ω' a' := by
    intro a' ha'; funext ℓ' k'
    exact φOf_agree K ω ω' (a, ℓ, k) h a' ℓ' k' (by rintro ⟨h1, -⟩; simp at h1; omega)
  have hφ2 : ∀ ℓ' < ℓ.val, φOf K ω a ℓ' = φOf K ω' a ℓ' := by
    intro ℓ' hℓ'; funext k'
    exact φOf_agree K ω ω' (a, ℓ, k) h a ℓ' k' (by rintro ⟨-, h2, -⟩; simp at h2; omega)
  have hs := ωsOf_agree E K ω ω' (a, ℓ, k) h
  unfold iterIn mergeIn
  simp only
  rw [hs, beforeMerge_congr E C θ R K lev _ (φOf K ω) (φOf K ω') a ℓ hφ1 hφ2]
  congr 1
  funext j
  apply φOf_agree K ω ω' (a, ℓ, k) h
  rintro ⟨-, -, h3⟩
  have := congrArg Fin.val h3
  simp at this; omega


section Prob

/-- P0034's `prob` of an event of the sampled subset `Fof Q y`, as the explicit subset sum. -/
theorem prob_eq_subsetSum (p : ℝ) {κ : Type} [Fintype κ] [DecidableEq κ] (Q : Finset κ) (A : Finset κ → Prop)
    [DecidablePred A] :
    prob p (fun y => A (Fof Q y)) =
      ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) * (if A F then 1 else 0) := by
  rw [← bE_filter p Q (fun F => if A F then 1 else 0)]
  unfold prob bE
  apply Finset.sum_congr rfl; intro y _
  rw [bw_const_eq_wt]
  by_cases h : A (Fof Q y)
  · rw [ind_pos h]; simp only [Fof] at h; simp [h]
  · rw [ind_neg h]; simp only [Fof] at h; simp [h]

variable (M0 : ℝ) (kk : ℕ)

/-- The bad event of one merge iteration at the end of epoch `a`, as a function of its input and filter. -/
def Abad (a : ℕ) (Q F : Finset ι) : Prop :=
  (∀ i ∈ Q, E i ≤ a + 1) ∧ M0 ≤ Q.card ∧
    (1 - 1 / (4 * R : ℝ)) * Q.card < (filterRound E C (a + 1) θ Q F R).card

open Classical in
/-- One merge iteration is bad with probability at most P0042's `delta`, whatever its (random) input. -/
theorem iter_slot_le {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE : Monotone E)
    (Tmax : ℝ) (hC : ∀ i a b, a ≤ b → b ≤ NE → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (hR : 1 ≤ R) (hT : Tmax ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (s0 : Fin NE × Fin (Lt + 1) × Fin K) :
    ∑ ω, bw2 (qOf K ps p) ω *
        (if Abad E C θ R M0 s0.1 (iterIn E C θ R K lev ω s0.1 s0.2.1 s0.2.2)
            ((iterIn E C θ R K lev ω s0.1 s0.2.1 s0.2.2).filter (fun c => ω (Sum.inr s0) c = true))
          then 1 else 0) ≤ delta (Fintype.card ι) p R kk M0 := by
  have hq01 : ∀ (s : Slot NE Lt K) (c : ι), 0 ≤ qOf K ps p s c ∧ qOf K ps p s c ≤ 1 := by
    intro s c; cases s <;> simp [qOf, hps, hp0, hp1]
  refine fresh_slot_le (qOf K ps p) hq01 (Sum.inr s0) p (fun c => rfl)
    (fun ω => iterIn E C θ R K lev ω s0.1 s0.2.1 s0.2.2)
    (fun ω ω' h => iterIn_local E C θ R K lev s0 ω ω' h) (Abad E C θ R M0 s0.1) _ ?_
  intro Q
  by_cases hQ : ∀ i ∈ Q, E i ≤ (s0.1 : ℕ) + 1
  · have hs0NE : (s0.1 : ℕ) + 1 ≤ NE := s0.1.2
    have hL : ∀ i ∈ Q, ∀ a b, a ≤ b → b ≤ (s0.1 : ℕ) + 1 → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax :=
      fun i _ a b hab hb => hC i a b hab (hb.trans hs0NE)
    have hb := prob_bad_le E C ((s0.1 : ℕ) + 1) θ hp0 hp1 hE Q hQ Tmax hL R kk hR hT M0 hM0 hk hp
    have heq := prob_eq_subsetSum p Q (fun F => M0 ≤ Q.card ∧
      (1 - 1 / (4 * R : ℝ)) * Q.card < (filterRound E C ((s0.1 : ℕ) + 1) θ Q F R).card)
    have h2 : ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) *
        (if Abad E C θ R M0 s0.1 Q F then 1 else 0) =
        ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) *
        (if M0 ≤ Q.card ∧ (1 - 1 / (4 * R : ℝ)) * Q.card <
            (filterRound E C ((s0.1 : ℕ) + 1) θ Q F R).card then 1 else 0) := by
      apply Finset.sum_congr rfl; intro F _
      congr 1
      by_cases hc : M0 ≤ Q.card ∧ (1 - 1 / (4 * R : ℝ)) * Q.card <
          (filterRound E C ((s0.1 : ℕ) + 1) θ Q F R).card
      · rw [if_pos (show Abad E C θ R M0 s0.1 Q F from ⟨hQ, hc⟩), if_pos hc]
      · rw [if_neg (show ¬ Abad E C θ R M0 s0.1 Q F from fun h => hc h.2), if_neg hc]
    rw [h2, ← heq]
    exact hb
  · have h0 : ∀ F, ¬ Abad E C θ R M0 s0.1 Q F := fun F h => hQ h.1
    simp only [h0, if_false, mul_zero, Finset.sum_const_zero]
    exact delta_nonneg hp1

open Classical in
/-- One epoch samples more than `s0` copies with probability at most `δs`. -/
theorem sample_slot_le {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a : ℕ, a < NE → ∑ F ∈ (Finset.univ.filter fun c => E c = a).powerset,
      ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a).card - F.card) *
        (if s0 < F.card then 1 else 0) ≤ δs) (a : Fin NE) :
    ∑ ω : Slot NE Lt K → ι → Bool, bw2 (qOf K ps p) ω *
      (if s0 < (newAt E (ωsOf E K ω) a).card then 1 else 0) ≤ δs := by
  have hq01 : ∀ (s : Slot NE Lt K) (c : ι), 0 ≤ qOf K ps p s c ∧ qOf K ps p s c ≤ 1 := by
    intro s c; cases s <;> simp [qOf, hps, hp0, hp1]
  have hnew : ∀ ω : Slot NE Lt K → ι → Bool, newAt E (ωsOf E K ω) a =
      (Finset.univ.filter fun c => E c = a).filter (fun c => ω (Sum.inl a) c = true) := by
    intro ω; ext c
    unfold newAt
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    unfold ωsOf
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have hlt : E c < NE := h1 ▸ a.2
      rw [dif_pos hlt] at h2
      have : (⟨E c, hlt⟩ : Fin NE) = a := Fin.ext h1
      rwa [this] at h2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have hlt : E c < NE := h1 ▸ a.2
      rw [dif_pos hlt]
      have : (⟨E c, hlt⟩ : Fin NE) = a := Fin.ext h1
      rwa [this]
  simp only [hnew]
  have key := fresh_slot_le (qOf K ps p) hq01 (Sum.inl a) ps (fun c => rfl)
    (fun _ => Finset.univ.filter fun c => E c = a) (fun _ _ _ => rfl)
    (fun Q F => Q = (Finset.univ.filter fun c => E c = a) ∧ s0 < F.card) δs
    (fun Q => by
      by_cases hQ : Q = Finset.univ.filter fun c => E c = a
      · subst hQ; simpa using hs a a.2
      · simp only [hQ, false_and, ite_false, mul_zero, Finset.sum_const_zero]
        refine le_trans (Finset.sum_nonneg fun F _ => ?_) (hs a a.2)
        apply mul_nonneg (mul_nonneg (pow_nonneg hps.1 _) (pow_nonneg (by linarith [hps.2]) _))
        split_ifs <;> norm_num)
  simpa using key


/-- **Deterministic step**: a run in which no sample is large and no merge iteration is bad is good. -/
theorem goodRun_of_noBad (ω : Slot NE Lt K → ι → Bool) (s0 : ℕ) (hlev : ∀ a < NE, lev a ≤ Lt)
    (hR : 1 ≤ R) (hM0 : 0 ≤ M0)
    (hs : ∀ a : Fin NE, ¬ s0 < (newAt E (ωsOf E K ω) a).card)
    (hm : ∀ s : Fin NE × Fin (Lt + 1) × Fin K,
      ¬ Abad E C θ R M0 s.1 (iterIn E C θ R K lev ω s.1 s.2.1 s.2.2)
        ((iterIn E C θ R K lev ω s.1 s.2.1 s.2.2).filter (fun c => ω (Sum.inr s) c = true))) :
    GoodRun E C θ R K lev (ωsOf E K ω) (φOf K ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K) := by
  classical
  refine ⟨fun a ha => not_lt.mp (hs ⟨a, ha⟩), ?_⟩
  intro a ha ℓ hℓ
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hε0 : 0 ≤ 1 / (4 * R : ℝ) := by positivity
  have hε1 : 1 / (4 * R : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  by_contra hbad
  have hany := mt (card_iter_le (mstep E C (a + 1) θ R) (mstep_sub E C (a + 1) θ R)
    (mergeIn E C θ R K lev ω a ℓ) M0 (1 / (4 * R : ℝ)) hM0 hε0 hε1 K (φOf K ω a ℓ)) hbad
  obtain ⟨k, hk⟩ := exists_bad_of_anyBad _ _ _ K (φOf K ω a ℓ) (not_not.mp hany)
  have hℓ' : ℓ < Lt + 1 := by have := hlev a ha; omega
  apply hm (⟨a, ha⟩, ⟨ℓ, hℓ'⟩, k)
  have hit : iterIn E C θ R K lev ω (⟨a, ha⟩ : Fin NE) (⟨ℓ, hℓ'⟩ : Fin (Lt + 1)) k =
      iter (mstep E C (a + 1) θ R) (mergeIn E C θ R K lev ω a ℓ) k
        (fun j => φOf K ω a ℓ (Fin.castLE k.2.le j)) := rfl
  rw [hit]
  refine ⟨?_, hk.1, ?_⟩
  · intro i hi
    have hsub := iter_sub (mstep E C (a + 1) θ R) (mergeIn E C θ R K lev ω a ℓ)
      (mstep_sub E C (a + 1) θ R) k _ hi
    unfold mergeIn at hsub
    rcases Finset.mem_union.mp hsub with h | h
    · have := E_le_of_mem_beforeMerge E C θ R K lev _ _ a ℓ _ i h; simp only; omega
    · have := E_le_of_mem_beforeMerge E C θ R K lev _ _ a ℓ _ i h; simp only; omega
  · have h2 := hk.2
    have hφ : φOf K ω a ℓ k = ω (Sum.inr (⟨a, ha⟩, ⟨ℓ, hℓ'⟩, k)) := φOf_eq K ω ⟨a, ha⟩ ⟨ℓ, hℓ'⟩ k
    unfold mstep at h2
    rw [hφ] at h2
    exact h2

/-- The bad event of a slot: a large sample, or a bad merge iteration. -/
def slotBad (s0 : ℕ) : Slot NE Lt K → (Slot NE Lt K → ι → Bool) → Prop
  | Sum.inl a, ω => s0 < (newAt E (ωsOf E K ω) a).card
  | Sum.inr s, ω => Abad E C θ R M0 s.1 (iterIn E C θ R K lev ω s.1 s.2.1 s.2.2)
        ((iterIn E C θ R K lev ω s.1 s.2.1 s.2.2).filter (fun c => ω (Sum.inr s) c = true))

open Classical in
/-- **Probability of a bad run.** Under P0042's parameter conditions, P0052's sub-pool process driven by the slot
array is not good (`GoodRun` with `ρ = (1 − 1/(4R))^K`) with probability at most `NE·δs + NE·(Lt+1)·K·delta`. -/
theorem prob_not_goodRun {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE : Monotone E)
    (Tmax : ℝ) (hC : ∀ i a b, a ≤ b → b ≤ NE → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (hR : 1 ≤ R) (hT : Tmax ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (hlev : ∀ a < NE, lev a ≤ Lt)
    (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a : ℕ, a < NE → ∑ F ∈ (Finset.univ.filter fun c => E c = a).powerset,
      ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a).card - F.card) *
        (if s0 < F.card then 1 else 0) ≤ δs) :
    ∑ ω : Slot NE Lt K → ι → Bool, bw2 (qOf K ps p) ω *
        (if GoodRun E C θ R K lev (ωsOf E K ω) (φOf K ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K) then 0 else 1)
      ≤ NE * δs + NE * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 := by
  have hq01 : ∀ (s : Slot NE Lt K) (c : ι), 0 ≤ qOf K ps p s c ∧ qOf K ps p s c ≤ 1 := by
    intro s c; cases s <;> simp [qOf, hps, hp0, hp1]
  have hw : ∀ ω : Slot NE Lt K → ι → Bool, 0 ≤ bw2 (qOf K ps p) ω := fun ω =>
    Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
      split_ifs
      · exact (hq01 s c).1
      · linarith [(hq01 s c).2]
  have hM0' : 0 ≤ M0 := le_trans (by positivity) hM0
  let P := slotBad E C θ R K lev (NE := NE) (Lt := Lt) M0 s0
  have hpt : ∀ ω, (if GoodRun E C θ R K lev (ωsOf E K ω) (φOf K ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
      then (0 : ℝ) else 1) ≤ if ∃ b ∈ Finset.univ, P b ω then 1 else 0 := by
    intro ω
    by_cases hg : GoodRun E C θ R K lev (ωsOf E K ω) (φOf K ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
    · rw [if_pos hg]; split_ifs <;> norm_num
    · rw [if_neg hg]
      have : ∃ b ∈ Finset.univ, P b ω := by
        by_contra hno
        push Not at hno
        exact hg (goodRun_of_noBad E C θ R K lev M0 ω s0 hlev hR hM0'
          (fun a => hno (Sum.inl a) (Finset.mem_univ _)) (fun s => hno (Sum.inr s) (Finset.mem_univ _)))
      rw [if_pos this]
  have hpt' : ∀ ω, (if GoodRun E C θ R K lev (ωsOf E K ω) (φOf K ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
      then (0 : ℝ) else 1) ≤ ∑ b, if P b ω then 1 else 0 := by
    intro ω
    refine (hpt ω).trans ?_
    split_ifs with h
    · obtain ⟨b, -, hb⟩ := h
      calc (1 : ℝ) = if P b ω then 1 else 0 := by rw [if_pos hb]
        _ ≤ ∑ b, if P b ω then 1 else 0 :=
            Finset.single_le_sum (f := fun b => if P b ω then (1:ℝ) else 0)
              (fun b _ => by split_ifs <;> norm_num) (Finset.mem_univ b)
    · exact Finset.sum_nonneg fun b _ => by split_ifs <;> norm_num
  calc _ ≤ ∑ ω : Slot NE Lt K → ι → Bool, bw2 (qOf K ps p) ω * ∑ b, (if P b ω then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hpt' ω) (hw ω)
    _ = ∑ b, ∑ ω, bw2 (qOf K ps p) ω * (if P b ω then 1 else 0) := by
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ = ∑ a : Fin NE, ∑ ω, bw2 (qOf K ps p) ω * (if P (Sum.inl a) ω then 1 else 0) +
          ∑ s : Fin NE × Fin (Lt + 1) × Fin K, ∑ ω, bw2 (qOf K ps p) ω *
            (if P (Sum.inr s) ω then 1 else 0) := Fintype.sum_sum_type _
    _ ≤ ∑ _a : Fin NE, δs + ∑ _s : Fin NE × Fin (Lt + 1) × Fin K, delta (Fintype.card ι) p R kk M0 := by
        apply add_le_add
        · refine Finset.sum_le_sum fun a _ => le_of_eq_of_le ?_ (sample_slot_le E K (Lt := Lt) hps hp0 hp1 s0 δs hs a)
          exact Finset.sum_congr rfl fun ω _ => by congr 1; exact if_congr Iff.rfl rfl rfl
        · refine Finset.sum_le_sum fun s _ => le_of_eq_of_le ?_
            (iter_slot_le E C θ R K lev M0 kk hps hp0 hp1 hE Tmax hC hR hT hM0 hk hp s)
          exact Finset.sum_congr rfl fun ω _ => by congr 1
    _ = NE * δs + NE * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, Fintype.card_prod,
          Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
        push_cast; ring


/-- **Chernoff bound for one epoch's sample**, in the subset-sum form required by `prob_not_goodRun`. -/
theorem sample_tail_le {ps : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) {κ : Type} [Fintype κ] [DecidableEq κ] (X : Finset κ)
    (s0 : ℕ) :
    ∑ F ∈ X.powerset, ps ^ F.card * (1 - ps) ^ (X.card - F.card) * (if s0 < F.card then 1 else 0) ≤
      Real.exp (ps * X.card * (Real.exp 1 - 1) - (s0 + 1)) := by
  have h1 := prob_card_ge hps.1 hps.2 X (κ := 1) zero_le_one ((s0 : ℝ) + 1)
  have h2 := prob_eq_subsetSum ps X (fun F => ((s0 : ℝ) + 1) ≤ F.card)
  rw [h2] at h1
  calc _ = ∑ F ∈ X.powerset, ps ^ F.card * (1 - ps) ^ (X.card - F.card) *
        (if ((s0 : ℝ) + 1) ≤ F.card then 1 else 0) := by
        apply Finset.sum_congr rfl; intro F _
        congr 1
        apply if_congr _ rfl rfl
        constructor
        · intro h; exact_mod_cast h
        · intro h; exact_mod_cast h
    _ ≤ _ := h1
    _ = _ := by ring_nf

open Classical in
/-- **Every sub-pool stays below `S`, except with small probability**: combining `prob_not_goodRun` with
P0052's deterministic `pools_card_le`. -/
theorem prob_pools_large_le {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hE : Monotone E)
    (Tmax : ℝ) (hC : ∀ i a b, a ≤ b → b ≤ NE → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (hR : 1 ≤ R) (hT : Tmax ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (hlev : ∀ a < NE, lev a ≤ Lt)
    (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a : ℕ, a < NE → ∑ F ∈ (Finset.univ.filter fun c => E c = a).powerset,
      ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a).card - F.card) *
        (if s0 < F.card then 1 else 0) ≤ δs)
    (S : ℝ) (hM0S : M0 ≤ S) (hs0S : (s0 : ℝ) ≤ S) (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * (2 * S) ≤ S) :
    ∑ ω : Slot NE Lt K → ι → Bool, bw2 (qOf K ps p) ω *
        (if ∀ a ≤ NE, ∀ ℓ, ((pools E C θ R K lev (ωsOf E K ω) (φOf K ω) a ℓ).card : ℝ) ≤ S then 0 else 1)
      ≤ NE * δs + NE * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 := by
  have hq01 : ∀ (s : Slot NE Lt K) (c : ι), 0 ≤ qOf K ps p s c ∧ qOf K ps p s c ≤ 1 := by
    intro s c; cases s <;> simp [qOf, hps, hp0, hp1]
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hρ0 : 0 ≤ (1 - 1 / (4 * R : ℝ)) ^ K := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  refine le_trans (Finset.sum_le_sum fun ω _ => ?_)
    (prob_not_goodRun E C θ R K lev M0 kk hps hp0 hp1 hE Tmax hC hR hT hM0 hk hp hlev s0 δs hs)
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
    split_ifs
    · exact (hq01 s c).1
    · linarith [(hq01 s c).2])
  by_cases hg : GoodRun E C θ R K lev (ωsOf E K ω) (φOf K ω) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
  · rw [if_pos (pools_card_le E C θ R K lev _ _ NE s0 M0 _ S hρ0 hg hM0S hs0S hρS)]
    split_ifs <;> norm_num
  · rw [if_neg hg]; split_ifs <;> norm_num

end Prob

end Pool.P0063
