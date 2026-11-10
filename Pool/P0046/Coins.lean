import Pool.Prelude

/-!
# Independent Bernoulli bits with per-coordinate probabilities: independence of disjoint blocks, the marginal law
of a sampled subset, and the fresh-slot lemma

* `bw q ω = ∏ᵢ (q i or 1 − q i)`, `bprob`, `bE` on `ω : I → Bool`.
* `bE_mul_of_indep`: functions of disjoint coordinate blocks are independent.
* `bE_filter`: with all probabilities `p`, `{c ∈ Q : ω c}` has the law of a random subset of `Q` with independent
  inclusions.
* `bw2`, `fresh_slot`: slot-indexed bits `ω s c`; if a set `X ω` is determined by the other slots, then the bits of a
  fixed slot `s₀` on `X ω` form a random subset of `X ω`.
-/

namespace Pool.P0046

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Weight of a bit configuration `ω` under independent bits with `P(ω i = true) = q i`. -/
noncomputable def bw (q : I → ℝ) (ω : I → Bool) : ℝ := ∏ i, if ω i then q i else 1 - q i

open Classical in
/-- Probability of an event on the bit space. -/
noncomputable def bprob (q : I → ℝ) (P : (I → Bool) → Prop) : ℝ :=
  ∑ ω : I → Bool, bw q ω * (if P ω then 1 else 0)

lemma bw_nonneg {q : I → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (ω : I → Bool) : 0 ≤ bw q ω :=
  prod_nonneg fun i _ => by
    split_ifs
    · exact (hq i).1
    · linarith [(hq i).2]

lemma sum_bw (q : I → ℝ) : ∑ ω : I → Bool, bw q ω = 1 := by
  unfold bw
  rw [← Fintype.prod_sum (fun (i : I) (b : Bool) => if b then q i else 1 - q i)]
  simp

lemma bprob_le_one {q : I → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (P : (I → Bool) → Prop) :
    bprob q P ≤ 1 := by
  classical
  calc bprob q P ≤ ∑ ω : I → Bool, bw q ω := by
        apply sum_le_sum; intro ω _
        have := bw_nonneg hq ω
        split_ifs <;> simp [this]
    _ = 1 := sum_bw q

lemma bprob_mono {q : I → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) {P P' : (I → Bool) → Prop}
    (h : ∀ ω, P ω → P' ω) : bprob q P ≤ bprob q P' := by
  classical
  apply sum_le_sum; intro ω _
  apply mul_le_mul_of_nonneg_left _ (bw_nonneg hq ω)
  have := h ω
  split_ifs <;> simp_all

lemma bprob_exists_le {q : I → ℝ} (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) {β : Type*} (S : Finset β)
    (P : β → (I → Bool) → Prop) :
    bprob q (fun ω => ∃ b ∈ S, P b ω) ≤ ∑ b ∈ S, bprob q (P b) := by
  classical
  unfold bprob
  rw [sum_comm]
  apply sum_le_sum; intro ω _
  rw [← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (bw_nonneg hq ω)
  split_ifs with h
  · obtain ⟨b, hb, hP⟩ := h
    calc (1 : ℝ) = if P b ω then 1 else 0 := by simp [hP]
      _ ≤ ∑ b ∈ S, if P b ω then 1 else 0 :=
          single_le_sum (f := fun b => if P b ω then (1:ℝ) else 0)
            (fun b _ => by split_ifs <;> norm_num) hb
  · exact sum_nonneg fun b _ => by split_ifs <;> norm_num

section Indep

/-- Expectation on the bit space. -/
noncomputable def bE (q : I → ℝ) (f : (I → Bool) → ℝ) : ℝ := ∑ ω : I → Bool, bw q ω * f ω

/-- **Independence of disjoint coordinate blocks.** If `f` reads only coordinates in `P` and `g` only
coordinates outside `P`, then `E[f g] = E[f] E[g]`. -/
lemma bE_mul_of_indep (q : I → ℝ) (P : I → Prop) [DecidablePred P] (f g : (I → Bool) → ℝ)
    (hf : ∀ ω ω', (∀ i, P i → ω i = ω' i) → f ω = f ω')
    (hg : ∀ ω ω', (∀ i, ¬ P i → ω i = ω' i) → g ω = g ω') :
    bE q (fun ω => f ω * g ω) = bE q f * bE q g := by
  let e := Equiv.piEquivPiSubtypeProd P (fun _ : I => Bool)
  let wP : ({i // P i} → Bool) → ℝ := fun y => ∏ i, if y i then q i else 1 - q i
  let wN : ({i // ¬ P i} → Bool) → ℝ := fun z => ∏ i, if z i then q i else 1 - q i
  have hw : ∀ y z, bw q (e.symm (y, z)) = wP y * wN z := by
    intro y z
    unfold bw
    rw [← Fintype.prod_subtype_mul_prod_subtype P]
    congr 1
    · apply Fintype.prod_congr; intro i
      simp [e, Equiv.piEquivPiSubtypeProd, i.2]
    · apply Fintype.prod_congr; intro i
      simp [e, Equiv.piEquivPiSubtypeProd, i.2]
  let z₀ : {i // ¬ P i} → Bool := fun _ => false
  let y₀ : {i // P i} → Bool := fun _ => false
  have hf' : ∀ y z, f (e.symm (y, z)) = f (e.symm (y, z₀)) := by
    intro y z; apply hf; intro i hi
    simp [e, Equiv.piEquivPiSubtypeProd, hi]
  have hg' : ∀ y z, g (e.symm (y, z)) = g (e.symm (y₀, z)) := by
    intro y z; apply hg; intro i hi
    simp [e, Equiv.piEquivPiSubtypeProd, hi]
  have hsN : ∑ z, wN z = 1 := by
    simp only [wN]
    rw [← Fintype.prod_sum (fun (i : {i // ¬ P i}) (b : Bool) => if b then q i else 1 - q i)]
    simp
  have hsP : ∑ y, wP y = 1 := by
    simp only [wP]
    rw [← Fintype.prod_sum (fun (i : {i // P i}) (b : Bool) => if b then q i else 1 - q i)]
    simp
  have expand : ∀ h : (I → Bool) → ℝ, bE q h = ∑ y, ∑ z, wP y * wN z * h (e.symm (y, z)) := by
    intro h
    unfold bE
    rw [← e.symm.sum_comp, Fintype.sum_prod_type]
    apply sum_congr rfl; intro y _
    apply sum_congr rfl; intro z _
    rw [hw]
  rw [expand, expand f, expand g]
  simp_rw [hf', hg']
  have h1 : ∀ y, ∑ z, wP y * wN z * f (e.symm (y, z₀)) = wP y * f (e.symm (y, z₀)) := by
    intro y
    rw [← sum_mul, ← mul_sum, hsN, mul_one]
  have h2 : ∑ y, ∑ z, wP y * wN z * g (e.symm (y₀, z)) = ∑ z, wN z * g (e.symm (y₀, z)) := by
    rw [sum_comm]
    apply sum_congr rfl; intro z _
    rw [← sum_mul, ← sum_mul, hsP, one_mul]
  rw [sum_congr rfl (fun y _ => h1 y), h2, sum_mul_sum]
  apply sum_congr rfl; intro y _
  apply sum_congr rfl; intro z _
  ring

end Indep

section Marginal

lemma bE_ind (q : I → ℝ) (a : I) : bE q (fun x => if x a then 1 else 0) = q a := by
  unfold bE bw
  have : ∀ x : I → Bool, (∏ c, if x c then q c else 1 - q c) * (if x a then (1:ℝ) else 0) =
      ∏ c, ((if x c then q c else 1 - q c) * (if c = a then (if x c then 1 else 0) else 1)) := by
    intro x
    rw [prod_mul_distrib, prod_ite_eq' univ a]
    simp
  simp_rw [this]
  rw [← Fintype.prod_sum (fun (c : I) (b : Bool) =>
    (if b then q c else 1 - q c) * (if c = a then (if b then 1 else 0) else 1))]
  rw [prod_eq_single a]
  · simp
  · intro c _ hca
    simp [hca]
  · simp

lemma bE_add (q : I → ℝ) (f g : (I → Bool) → ℝ) : bE q (fun x => f x + g x) = bE q f + bE q g := by
  unfold bE; rw [← sum_add_distrib]; apply sum_congr rfl; intro x _; ring

/-- **Marginal lemma.** With all bits `true` w.p. `p`, the set of elements of `Q` whose bit is `true`
has the law of a random subset of `Q` with independent inclusions. -/
lemma bE_filter (p : ℝ) (Q : Finset I) (h : Finset I → ℝ) :
    bE (fun _ => p) (fun x => h (Q.filter (fun c => x c = true))) =
      ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) * h F := by
  induction Q using Finset.induction_on generalizing h with
  | empty =>
    simp only [filter_empty, powerset_empty, sum_singleton, card_empty, pow_zero, Nat.sub_self, mul_one, one_mul]
    unfold bE; rw [← sum_mul, sum_bw]; ring
  | insert a Q ha ih =>
    have hsplit : ∀ x : I → Bool, h ((insert a Q).filter (fun c => x c = true)) =
        (if x a = true then 1 else 0) * h (insert a (Q.filter (fun c => x c = true))) +
        (if x a = false then 1 else 0) * h (Q.filter (fun c => x c = true)) := by
      intro x
      rw [filter_insert]
      cases x a <;> simp
    simp_rw [hsplit]
    rw [bE_add]
    have hind : ∀ (b : Bool) (g : Finset I → ℝ),
        bE (fun _ => p) (fun x => (if x a = b then 1 else 0) * g (Q.filter (fun c => x c = true))) =
          bE (fun _ => p) (fun x => if x a = b then 1 else 0) *
            bE (fun _ => p) (fun x => g (Q.filter (fun c => x c = true))) := by
      intro b g
      apply bE_mul_of_indep (fun _ => p) (fun c => c = a)
      · intro ω ω' h; rw [h a rfl]
      · intro ω ω' h'
        congr 1
        apply filter_congr
        intro c hc
        rw [h' c (fun hca => ha (hca ▸ hc))]
    have e1 := hind true (fun F => h (insert a F))
    have e2 := hind false h
    have i1 : bE (fun _ => p) (fun x => if x a = true then (1:ℝ) else 0) = p := by
      have := bE_ind (fun _ => p) a; simpa using this
    have i0 : bE (fun _ => p) (fun x => if x a = false then (1:ℝ) else 0) = 1 - p := by
      have h1 := bE_ind (fun _ => p) a
      have h2 : bE (fun _ => p) (fun x => (if x a then (1:ℝ) else 0) + (if x a = false then 1 else 0)) = 1 := by
        unfold bE
        have : ∀ x : I → Bool, (if x a then (1:ℝ) else 0) + (if x a = false then 1 else 0) = 1 := by
          intro x; cases x a <;> simp
        simp_rw [this, mul_one, sum_bw]
      rw [bE_add] at h2
      linarith
    rw [e1, e2, i1, i0, ih h, ih (fun F => h (insert a F)), sum_powerset_insert ha, card_insert_of_notMem ha, mul_sum, mul_sum, add_comm]
    congr 1
    · apply sum_congr rfl; intro F hF
      have hle := card_le_card (mem_powerset.mp hF)
      rw [show Q.card + 1 - F.card = (Q.card - F.card) + 1 by omega, pow_succ]
      ring
    · apply sum_congr rfl; intro F hF
      have haF : a ∉ F := fun h => ha (mem_powerset.mp hF h)
      have hle := card_le_card (mem_powerset.mp hF)
      rw [card_insert_of_notMem haF, show Q.card + 1 - (F.card + 1) = Q.card - F.card by omega, pow_succ]
      ring

end Marginal

section Fresh

variable {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]

/-- Weight of slot-indexed bits `ω s c` (slot `s`, copy `c`), independent with `P(true) = q s c`. -/
noncomputable def bw2 (q : σ → κ → ℝ) (ω : σ → κ → Bool) : ℝ :=
  ∏ s, ∏ c, if ω s c then q s c else 1 - q s c

lemma sum_bw2 (q : σ → κ → ℝ) : ∑ ω : σ → κ → Bool, bw2 q ω = 1 := by
  unfold bw2
  rw [← Fintype.prod_sum (fun (s : σ) (x : κ → Bool) => ∏ c, if x c then q s c else 1 - q s c)]
  apply prod_eq_one; intro s _
  have := sum_bw (q s)
  unfold bw at this
  exact this

/-- **Fresh-slot lemma.** If the set `X ω` and the integrand `G ω ·` are determined by the bits of slots other
than `s₀`, and the bits of slot `s₀` are `true` w.p. `p`, then the bits of slot `s₀` on `X ω` form a random subset of
`X ω` with independent inclusions, independent of everything else. -/
lemma fresh_slot (q : σ → κ → ℝ) (s₀ : σ) (p : ℝ) (hq : ∀ c, q s₀ c = p)
    (X : (σ → κ → Bool) → Finset κ) (hX : ∀ ω ω', (∀ s, s ≠ s₀ → ω s = ω' s) → X ω = X ω')
    (G : (σ → κ → Bool) → Finset κ → ℝ) (hG : ∀ ω ω', (∀ s, s ≠ s₀ → ω s = ω' s) → G ω = G ω') :
    ∑ ω, bw2 q ω * G ω ((X ω).filter (fun c => ω s₀ c = true)) =
      ∑ ω, bw2 q ω * ∑ F ∈ (X ω).powerset, p ^ F.card * (1 - p) ^ ((X ω).card - F.card) * G ω F := by
  let e := Equiv.piSplitAt s₀ (fun _ : σ => κ → Bool)
  let wR : ({s // s ≠ s₀} → κ → Bool) → ℝ := fun r => ∏ s, ∏ c, if r s c then q s c else 1 - q s c
  have hw : ∀ x r, bw2 q (e.symm (x, r)) = bw (fun _ => p) x * wR r := by
    intro x r
    unfold bw2 bw
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ s₀]
    congr 1
    · apply Fintype.prod_congr; intro c
      simp [e, Equiv.piSplitAt, hq]
    · apply Fintype.prod_congr; intro s
      apply Fintype.prod_congr; intro c
      simp [e, Equiv.piSplitAt, s.2]
  have hoff : ∀ x r s, s ≠ s₀ → e.symm (x, r) s = e.symm (fun _ => false, r) s := by
    intro x r s hs
    simp [e, Equiv.piSplitAt, hs]
  have hX' : ∀ x r, X (e.symm (x, r)) = X (e.symm (fun _ => false, r)) :=
    fun x r => hX _ _ (hoff x r)
  have hG' : ∀ x r, G (e.symm (x, r)) = G (e.symm (fun _ => false, r)) :=
    fun x r => hG _ _ (hoff x r)
  have hs0 : ∀ x r, e.symm (x, r) s₀ = x := by intro x r; simp [e, Equiv.piSplitAt]
  have expand : ∀ h : (σ → κ → Bool) → ℝ, ∑ ω, bw2 q ω * h ω =
      ∑ r, ∑ x, bw (fun _ => p) x * wR r * h (e.symm (x, r)) := by
    intro h
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, sum_comm]
    apply sum_congr rfl; intro r _
    apply sum_congr rfl; intro x _
    rw [hw]
  rw [expand, expand]
  apply sum_congr rfl; intro r _
  simp_rw [hX', hG', hs0]
  set Q := X (e.symm (fun _ => false, r))
  set G₀ := G (e.symm (fun _ => false, r))
  have hm := bE_filter p Q G₀
  unfold bE at hm
  have h1 : ∑ x : κ → Bool, bw (fun _ => p) x * wR r * G₀ (Q.filter (fun c => x c = true)) =
      wR r * ∑ x : κ → Bool, bw (fun _ => p) x * G₀ (Q.filter (fun c => x c = true)) := by
    rw [mul_sum]; apply sum_congr rfl; intro x _; ring
  have h2 : ∑ x : κ → Bool, bw (fun _ => p) x * wR r *
      ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) * G₀ F =
      wR r * ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) * G₀ F := by
    rw [← sum_mul, ← sum_mul, sum_bw (fun _ : κ => p), one_mul]
  rw [h1, h2, hm]

/-- The special case of `fresh_slot` where the integrand depends on the coins only through `X ω`. -/
lemma fresh_slot_set (q : σ → κ → ℝ) (s₀ : σ) (p : ℝ) (hq : ∀ c, q s₀ c = p)
    (X : (σ → κ → Bool) → Finset κ) (hX : ∀ ω ω', (∀ s, s ≠ s₀ → ω s = ω' s) → X ω = X ω')
    (G : Finset κ → Finset κ → ℝ) :
    ∑ ω, bw2 q ω * G (X ω) ((X ω).filter (fun c => ω s₀ c = true)) =
      ∑ ω, bw2 q ω * ∑ F ∈ (X ω).powerset, p ^ F.card * (1 - p) ^ ((X ω).card - F.card) * G (X ω) F :=
  fresh_slot q s₀ p hq X hX (fun ω => G (X ω)) (fun ω ω' h => by rw [hX ω ω' h])

/-- Bound form: if for every pool `Q` the event `A Q` has probability at most `δ` under independent inclusions,
then the event for the filter drawn at slot `s₀` has probability at most `δ`. -/
lemma fresh_slot_le (q : σ → κ → ℝ) (hq01 : ∀ s c, 0 ≤ q s c ∧ q s c ≤ 1) (s₀ : σ) (p : ℝ)
    (hq : ∀ c, q s₀ c = p)
    (X : (σ → κ → Bool) → Finset κ) (hX : ∀ ω ω', (∀ s, s ≠ s₀ → ω s = ω' s) → X ω = X ω')
    (A : Finset κ → Finset κ → Prop) [∀ Q F, Decidable (A Q F)] (δ : ℝ)
    (hA : ∀ Q, ∑ F ∈ Q.powerset, p ^ F.card * (1 - p) ^ (Q.card - F.card) * (if A Q F then 1 else 0) ≤ δ) :
    ∑ ω, bw2 q ω * (if A (X ω) ((X ω).filter (fun c => ω s₀ c = true)) then 1 else 0) ≤ δ := by
  rw [fresh_slot_set q s₀ p hq X hX (fun Q F => if A Q F then 1 else 0)]
  have hw : ∀ ω, 0 ≤ bw2 q ω := fun ω => prod_nonneg fun s _ => prod_nonneg fun c _ => by
    split_ifs
    · exact (hq01 s c).1
    · linarith [(hq01 s c).2]
  calc ∑ ω, bw2 q ω * ∑ F ∈ (X ω).powerset, p ^ F.card * (1 - p) ^ ((X ω).card - F.card) *
          (if A (X ω) F then 1 else 0)
      ≤ ∑ ω, bw2 q ω * δ := sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hA (X ω)) (hw ω)
    _ = δ := by rw [← sum_mul, sum_bw2, one_mul]

end Fresh

end Pool.P0046
