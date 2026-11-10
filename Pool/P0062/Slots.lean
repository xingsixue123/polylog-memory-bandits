import Pool.P0052.PoolProcess

/-!
# Clock slots of the P0052 sub-pool process: a copy's merges are fixed by the schedule

* `lvl lev e a`: the level, at the start of epoch `a`, of a surviving copy that entered at epoch `e` (a function of
  the clock only). `mem_level`: every copy in the process is at exactly this level; `mem_stage_level`: during the
  cascade of epoch `a`, after the merges of levels `0..m-1`, it is at level `max (lvl …) m`.
* `InSlots lev e a ℓ`: the merge `(a, ℓ)` is one a copy entering at `e` can take part in. `inSlots_of_mem_input`:
  a copy in the input of a merge is in one of its slots.
* `passiveRun_of_slots`: if the copy's filter bits are `false` in all its slots (every epoch), it is passive
  (P0052 `PassiveRun`), whatever the other coins: a fixed-coordinate event IMPLIES passivity (sufficient
  condition). `passiveRun_of_slots_lt` needs in addition all filter bits at epochs `≥ NE` false.
* `trunc`, `pools_trunc` (causality: the run up to `NE` ignores coins of epochs `≥ NE`) and
  `pools_erase_of_slots_lt`: up to the horizon `NE`, removing the copy changes nothing else as soon as its filter
  bits are `false` on the FINITE set `slots L (E c) NE × Fin K`, with no condition on any other coin.
* `levPR L a = min (ν₂(a+1)) L` (Peng–Rubinstein's schedule, capped) and `card_slots_le`: at most
  `2L + NE/2^L + 1` slots before epoch `NE`.
-/

open Finset Pool.P0030 Pool.P0034 Pool.P0042 Pool.P0052

namespace Pool.P0062

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (C : ι → ℕ → ℝ) (θ : ℝ) (R K : ℕ)
  (lev : ℕ → ℕ)

/-- The level, at the start of epoch `a` (after entrants joined), of a copy entering at epoch `e` that has
survived: `0` at entry; after the merges of epoch `a` it is `lev a + 1` if it was at most `lev a`. -/
def lvl (e : ℕ) : ℕ → ℕ
  | 0 => 0
  | a + 1 => if a < e then 0 else (if lvl e a ≤ lev a then lev a + 1 else lvl e a)

theorem lvl_self (e : ℕ) : lvl lev e e = 0 := by
  cases e with
  | zero => rfl
  | succ e => simp [lvl]

theorem lvl_succ (e a : ℕ) (h : e ≤ a) : lvl lev e (a + 1) = max (lvl lev e a) (lev a + 1) := by
  simp only [lvl, show ¬ a < e by omega, ite_false]
  split_ifs with h1 <;> omega

/-- Levels during the cascade of epoch `a`: after the merges of levels `0..m-1`, a surviving copy that started the
epoch at level `L` is at level `max L m`. -/
theorem mem_stage_level {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {a : ℕ} {c : ι}
    (h0 : ∀ j, c ∈ beforeMerge E C θ R K lev ωs φ a 0 j → j = lvl lev (E c) a) :
    ∀ m j, c ∈ beforeMerge E C θ R K lev ωs φ a m j → j = max (lvl lev (E c) a) m := by
  intro m
  induction m with
  | zero => intro j hj; rw [h0 j hj]; simp
  | succ m ih =>
    intro j hj
    have hstep : beforeMerge E C θ R K lev ωs φ a (m + 1) =
        mergeOne E C θ R K φ a m (beforeMerge E C θ R K lev ωs φ a m) := by
      cases m <;> rfl
    rw [hstep] at hj
    unfold mergeOne at hj
    by_cases h1 : j = m
    · subst h1; simp at hj
    rw [Function.update_of_ne h1] at hj
    by_cases h2 : j = m + 1
    · subst h2
      rw [Function.update_self] at hj
      have := iter_sub (mstep E C (a + 1) θ R) _ (mstep_sub E C (a + 1) θ R) K (φ a m) hj
      rcases mem_union.1 this with h3 | h3
      · have := ih _ h3; omega
      · have := ih _ h3; omega
    · rw [Function.update_of_ne h2] at hj
      have := ih _ hj
      omega

/-- **Levels are fixed by the clock.** A copy in sub-pool `j` after `a` epochs entered before `a`, and
`j = lvl (E c) a`; a copy in level `j` of the start pool of epoch `a` entered at or before `a` and
`j = lvl (E c) a`. -/
theorem mem_level {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {c : ι} :
    ∀ a, (∀ j, c ∈ pools E C θ R K lev ωs φ a j → E c < a ∧ j = lvl lev (E c) a) ∧
      (∀ j, c ∈ beforeMerge E C θ R K lev ωs φ a 0 j → E c ≤ a ∧ j = lvl lev (E c) a) := by
  intro a
  induction a with
  | zero =>
    refine ⟨fun j hj => by simp [pools] at hj, fun j hj => ?_⟩
    simp only [beforeMerge, pools] at hj
    by_cases h0 : j = 0
    · subst h0; simp [newAt] at hj; rw [hj.1]; simp [lvl]
    · rw [Function.update_of_ne h0] at hj; simp at hj
  | succ a ih =>
    obtain ⟨_, ih2⟩ := ih
    have hp : ∀ j, c ∈ pools E C θ R K lev ωs φ (a + 1) j → E c < a + 1 ∧ j = lvl lev (E c) (a + 1) := by
      intro j hj
      have hmem : c ∈ beforeMerge E C θ R K lev ωs φ a (lev a + 1) j := hj
      -- c was in the start pool of epoch a
      have hin : ∃ j', c ∈ beforeMerge E C θ R K lev ωs φ a 0 j' := by
        have : ∀ m j, c ∈ beforeMerge E C θ R K lev ωs φ a m j →
            ∃ j', c ∈ beforeMerge E C θ R K lev ωs φ a 0 j' := by
          intro m
          induction m with
          | zero => intro j hj; exact ⟨j, hj⟩
          | succ m ihm =>
            intro j hj
            have hstep : beforeMerge E C θ R K lev ωs φ a (m + 1) =
                mergeOne E C θ R K φ a m (beforeMerge E C θ R K lev ωs φ a m) := by
              cases m <;> rfl
            rw [hstep] at hj
            unfold mergeOne at hj
            by_cases h1 : j = m
            · subst h1; simp at hj
            rw [Function.update_of_ne h1] at hj
            by_cases h2 : j = m + 1
            · subst h2
              rw [Function.update_self] at hj
              have := iter_sub (mstep E C (a + 1) θ R) _ (mstep_sub E C (a + 1) θ R) K (φ a m) hj
              rcases mem_union.1 this with h3 | h3
              · exact ihm _ h3
              · exact ihm _ h3
            · rw [Function.update_of_ne h2] at hj; exact ihm _ hj
        exact this _ _ hmem
      obtain ⟨j', hj'⟩ := hin
      have hE : E c ≤ a := (ih2 j' hj').1
      have := mem_stage_level E C θ R K lev (fun j hj => (ih2 j hj).2) (lev a + 1) j hmem
      refine ⟨by omega, ?_⟩
      rw [this, lvl_succ lev _ _ hE]
    refine ⟨hp, fun j hj => ?_⟩
    simp only [beforeMerge] at hj
    by_cases h0 : j = 0
    · subst h0
      rw [Function.update_self] at hj
      rcases mem_union.1 hj with h1 | h1
      · exact ⟨(hp 0 h1).1.le, (hp 0 h1).2⟩
      · simp [newAt] at h1; rw [h1.1]; exact ⟨le_rfl, (lvl_self lev _).symm⟩
    · rw [Function.update_of_ne h0] at hj
      exact ⟨(hp j hj).1.le, (hp j hj).2⟩


/-- The merge slots `(a, ℓ)` a copy entering at epoch `e` can take part in (fixed by the clock). -/
def InSlots (e a ℓ : ℕ) : Prop := e ≤ a ∧ ℓ ≤ lev a ∧ lvl lev e a ≤ ℓ + 1

/-- A copy in the input of the merge `(a, ℓ)` (with `ℓ ≤ lev a`) is in one of its clock slots. -/
theorem inSlots_of_mem_input {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {a ℓ : ℕ} {c : ι}
    (hℓ : ℓ ≤ lev a)
    (h : c ∈ beforeMerge E C θ R K lev ωs φ a ℓ (ℓ + 1) ∪ beforeMerge E C θ R K lev ωs φ a ℓ ℓ) :
    InSlots lev (E c) a ℓ := by
  have h0 := (mem_level E C θ R K lev (ωs := ωs) (φ := φ) (c := c) a).2
  have hst := mem_stage_level E C θ R K lev (fun j hj => (h0 j hj).2)
  -- c was in the start pool, so E c ≤ a
  have hstart : ∀ m j, c ∈ beforeMerge E C θ R K lev ωs φ a m j →
      ∃ j', c ∈ beforeMerge E C θ R K lev ωs φ a 0 j' := by
    intro m
    induction m with
    | zero => intro j hj; exact ⟨j, hj⟩
    | succ m ihm =>
      intro j hj
      have hstep : beforeMerge E C θ R K lev ωs φ a (m + 1) =
          mergeOne E C θ R K φ a m (beforeMerge E C θ R K lev ωs φ a m) := by
        cases m <;> rfl
      rw [hstep] at hj
      unfold mergeOne at hj
      by_cases h1 : j = m
      · subst h1; simp at hj
      rw [Function.update_of_ne h1] at hj
      by_cases h2 : j = m + 1
      · subst h2
        rw [Function.update_self] at hj
        have := iter_sub (mstep E C (a + 1) θ R) _ (mstep_sub E C (a + 1) θ R) K (φ a m) hj
        rcases mem_union.1 this with h3 | h3
        · exact ihm _ h3
        · exact ihm _ h3
      · rw [Function.update_of_ne h2] at hj; exact ihm _ hj
  rcases mem_union.1 h with h1 | h1
  · obtain ⟨j', hj'⟩ := hstart _ _ h1
    have := hst ℓ (ℓ + 1) h1
    exact ⟨(h0 j' hj').1, hℓ, by omega⟩
  · obtain ⟨j', hj'⟩ := hstart _ _ h1
    have := hst ℓ ℓ h1
    exact ⟨(h0 j' hj').1, hℓ, by omega⟩

theorem passiveIter_of_not_mem (t : ℕ) (c : ι) (Q : Finset ι) (hc : c ∉ Q) :
    ∀ (m : ℕ) (φ : Fin m → ι → Bool), PassiveIter E C t θ R c Q m φ := by
  intro m
  induction m with
  | zero => intro _; trivial
  | succ m ih =>
    intro φ
    refine ⟨ih _, fun h => absurd (iter_sub (mstep E C t θ R) Q (mstep_sub E C t θ R) m _ h) hc⟩

/-- **Passivity from fixed coordinates.** If copy `c`'s filter bits are `false` at every iteration of every merge
in its clock slots, then `c` is passive in the run (P0052 `PassiveRun`), whatever the other coins. -/
theorem passiveRun_of_slots {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {c : ι}
    (h : ∀ a ℓ k, InSlots lev (E c) a ℓ → φ a ℓ k c = false) :
    PassiveRun E C θ R K lev c ωs φ := by
  intro a ℓ hℓ
  by_cases hin : c ∈ beforeMerge E C θ R K lev ωs φ a ℓ (ℓ + 1) ∪ beforeMerge E C θ R K lev ωs φ a ℓ ℓ
  · exact passiveIter_of_false E C (a + 1) θ R c _ K (φ a ℓ)
      (fun k => h a ℓ k (inSlots_of_mem_input E C θ R K lev hℓ hin))
  · exact passiveIter_of_not_mem E C θ R (a + 1) c _ hin K (φ a ℓ)



/-- The filter coins truncated at the horizon `NE`: unchanged before epoch `NE`, `false` from `NE` on. -/
def trunc (NE : ℕ) (φ : ℕ → ℕ → Fin K → ι → Bool) : ℕ → ℕ → Fin K → ι → Bool :=
  fun a ℓ k x => if a < NE then φ a ℓ k x else false

omit [LinearOrder ι] [Fintype ι] in
theorem trunc_of_lt {NE a : ℕ} (φ : ℕ → ℕ → Fin K → ι → Bool) (ha : a < NE) : trunc K NE φ a = φ a := by
  funext ℓ k x; simp [trunc, ha]

/-- The cascade of epoch `a` reads only the coins of epoch `a`. -/
theorem mergeUpTo_congr (φ φ' : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) (h : φ a = φ' a) :
    ∀ m P, mergeUpTo E C θ R K φ a m P = mergeUpTo E C θ R K φ' a m P := by
  intro m
  induction m with
  | zero => intro P; simp [mergeUpTo, mergeOne, h]
  | succ m ih => intro P; simp [mergeUpTo, mergeOne, h, ih]

/-- **Causality.** Up to the horizon `NE`, the run does not depend on the filter coins of epochs `≥ NE`. -/
theorem pools_trunc (ωs : ι → Bool) (φ : ℕ → ℕ → Fin K → ι → Bool) (NE : ℕ) :
    ∀ a, a ≤ NE → pools E C θ R K lev ωs (trunc K NE φ) a = pools E C θ R K lev ωs φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro ha
    simp only [pools]
    rw [ih (by omega)]
    exact mergeUpTo_congr E C θ R K _ _ a (trunc_of_lt K φ (by omega)) _ _

section Count

/-- Peng–Rubinstein's merge schedule, capped at `L`: at the end of epoch `a`, merge levels `0..ν₂(a+1)`. -/
def levPR (L a : ℕ) : ℕ := min (padicValNat 2 (a + 1)) L

theorem le_levPR_iff {L a j : ℕ} (hj : j ≤ L) : j ≤ levPR L a ↔ 2 ^ j ∣ a + 1 := by
  rw [levPR, le_min_iff, padicValNat_dvd_iff_le_of_ne_one (by norm_num) (by omega)]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, hj⟩

theorem levPR_le (L a : ℕ) : levPR L a ≤ L := min_le_right _ _

theorem lvl_mono (e : ℕ) : ∀ d a, e ≤ a → lvl lev e a ≤ lvl lev e (a + d) := by
  intro d
  induction d with
  | zero => intro a _; simp
  | succ d ih =>
    intro a ha
    have := ih a ha
    rw [← add_assoc, lvl_succ lev e (a + d) (by omega)]
    omega

/-- In a clock slot `(a, ℓ)`, no earlier epoch since entry merged above level `ℓ`. -/
theorem lev_le_of_inSlots {e a ℓ : ℕ} (h : InSlots lev e a ℓ) :
    ∀ a', e ≤ a' → a' < a → lev a' ≤ ℓ := by
  intro a' h1 h2
  obtain ⟨-, -, h3⟩ := h
  have hm := lvl_mono lev e (a - (a' + 1)) (a' + 1) (by omega)
  rw [show a' + 1 + (a - (a' + 1)) = a by omega, lvl_succ lev e a' h1] at hm
  omega

/-- At most two epochs `a ∈ [e, NE)` with `2^ℓ ∣ a + 1` precede the first multiple of `2^(ℓ+1)`. -/
theorem card_two (ℓ e NE : ℕ) :
    ((Ico e NE).filter (fun a => 2 ^ ℓ ∣ a + 1 ∧ ∀ a', e ≤ a' → a' < a → ¬ 2 ^ (ℓ + 1) ∣ a' + 1)).card ≤ 2 := by
  classical
  set S := (Ico e NE).filter (fun a => 2 ^ ℓ ∣ a + 1 ∧ ∀ a', e ≤ a' → a' < a → ¬ 2 ^ (ℓ + 1) ∣ a' + 1)
  have hinj : Set.InjOn (fun a => (a + 1) / 2 ^ ℓ % 2) S := by
    intro a ha b hb hab
    simp only [S, coe_filter, mem_Ico, Set.mem_ofPred_eq] at ha hb
    obtain ⟨⟨hea, -⟩, ⟨p, hp⟩, ha2⟩ := ha
    obtain ⟨⟨heb, -⟩, ⟨q, hq⟩, hb2⟩ := hb
    have h2 : 0 < 2 ^ ℓ := by positivity
    simp only at hab
    rw [hp, hq, Nat.mul_div_cancel_left _ h2, Nat.mul_div_cancel_left _ h2] at hab
    by_contra hne
    -- wlog a < b
    have key : ∀ a b p q, e ≤ a → a + 1 = 2 ^ ℓ * p → b + 1 = 2 ^ ℓ * q → p % 2 = q % 2 → a < b →
        (∀ a', e ≤ a' → a' < b → ¬ 2 ^ (ℓ + 1) ∣ a' + 1) → False := by
      intro a b p q hea hp hq hpq hab hb2
      have hpq' : p < q := by
        by_contra h; push Not at h
        have : 2 ^ ℓ * q ≤ 2 ^ ℓ * p := Nat.mul_le_mul_left _ h
        omega
      rcases Nat.even_or_odd p with ⟨r, hr⟩ | ⟨r, hr⟩
      · apply hb2 a hea hab
        exact ⟨r, by rw [hp, hr, pow_succ]; ring⟩
      · have hq2 : p + 1 < q := by omega
        have hlt : 2 ^ ℓ * (p + 1) < 2 ^ ℓ * q := Nat.mul_lt_mul_of_pos_left hq2 (by positivity)
        apply hb2 (a + 2 ^ ℓ) (by omega) (by rw [mul_add, mul_one] at hlt; omega)
        refine ⟨r + 1, ?_⟩
        rw [add_right_comm, hp, hr, pow_succ]; ring
    rcases lt_or_gt_of_ne hne with h | h
    · exact key a b p q hea hp hq hab h hb2
    · exact key b a q p heb hq hp hab.symm h ha2
  calc S.card ≤ (range 2).card := by
        apply card_le_card_of_injOn _ (fun a _ => by simpa using Nat.mod_lt _ (by norm_num : 0 < 2)) hinj
    _ = 2 := by simp

/-- Epochs `a ∈ [e, NE)` with `2^L ∣ a + 1`: at most `NE / 2^L + 1`. -/
theorem card_mult (L e NE : ℕ) :
    ((Ico e NE).filter (fun a => 2 ^ L ∣ a + 1)).card ≤ NE / 2 ^ L + 1 := by
  classical
  have hinj : Set.InjOn (fun a => (a + 1) / 2 ^ L) ((Ico e NE).filter (fun a => 2 ^ L ∣ a + 1)) := by
    intro a ha b hb hab
    simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at ha hb
    obtain ⟨-, p, hp⟩ := ha
    obtain ⟨-, q, hq⟩ := hb
    have h2 : 0 < 2 ^ L := by positivity
    simp only at hab
    rw [hp, hq, Nat.mul_div_cancel_left _ h2, Nat.mul_div_cancel_left _ h2] at hab
    subst hab; omega
  calc _ ≤ (range (NE / 2 ^ L + 1)).card := by
        apply card_le_card_of_injOn _ (fun a ha => ?_) hinj
        simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at ha
        simp only [coe_range, Set.mem_Iio]
        have : (a + 1) / 2 ^ L ≤ NE / 2 ^ L := Nat.div_le_div_right (by omega)
        omega
    _ = NE / 2 ^ L + 1 := by simp


/-- The clock slots `(a, ℓ)`, `a < NE`, of a copy entering at `e`, under the schedule `levPR L`. -/
noncomputable def slots (L e NE : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Ico e NE) ×ˢ (range (L + 1))).filter (fun x => InSlots (levPR L) e x.1 x.2)

/-- **Slot count.** Under Peng–Rubinstein's schedule capped at `L`, a copy takes part in at most
`2L + NE/2^L + 1` merges before epoch `NE`. -/
theorem card_slots_le (L e NE : ℕ) : (slots L e NE).card ≤ 2 * L + NE / 2 ^ L + 1 := by
  classical
  have hfib : (slots L e NE).card =
      ∑ ℓ ∈ range (L + 1), ((Ico e NE).filter (fun a => InSlots (levPR L) e a ℓ)).card := by
    unfold slots
    rw [card_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [card_filter]
  rw [hfib, Finset.sum_range_succ]
  have hlow : ∀ ℓ ∈ range L, ((Ico e NE).filter (fun a => InSlots (levPR L) e a ℓ)).card ≤ 2 := by
    intro ℓ hℓ
    rw [mem_range] at hℓ
    refine le_trans (card_le_card fun a ha => ?_) (card_two ℓ e NE)
    simp only [mem_filter] at ha ⊢
    obtain ⟨ha1, hs⟩ := ha
    refine ⟨ha1, (le_levPR_iff (by omega)).1 hs.2.1, fun a' h1 h2 hd => ?_⟩
    have := lev_le_of_inSlots (levPR L) hs a' h1 h2
    have := (le_levPR_iff (L := L) (a := a') (j := ℓ + 1) (by omega)).2 hd
    omega
  have htop : ((Ico e NE).filter (fun a => InSlots (levPR L) e a L)).card ≤ NE / 2 ^ L + 1 := by
    refine le_trans (card_le_card fun a ha => ?_) (card_mult L e NE)
    simp only [mem_filter] at ha ⊢
    exact ⟨ha.1, (le_levPR_iff le_rfl).1 ha.2.2.1⟩
  have := Finset.sum_le_sum hlow
  simp only [sum_const, card_range, smul_eq_mul] at this
  omega

/-- Membership in the slot set. -/
theorem mem_slots {L e NE a ℓ : ℕ} (ha : a < NE) (h : InSlots (levPR L) e a ℓ) : (a, ℓ) ∈ slots L e NE := by
  classical
  unfold slots
  simp only [mem_filter, mem_product, mem_Ico, mem_range]
  exact ⟨⟨⟨h.1, ha⟩, by have := h.2.1; have := levPR_le L a; omega⟩, h⟩


/-- Passivity from finitely many coordinates: the copy's filter bits in its slots before `NE` are `false`, and
all filter bits from epoch `NE` on are `false` (a run that stops filtering at the horizon). -/
theorem passiveRun_of_slots_lt {L NE : ℕ} {ωs : ι → Bool} {φ : ℕ → ℕ → Fin K → ι → Bool} {c : ι}
    (h : ∀ x ∈ slots L (E c) NE, ∀ k, φ x.1 x.2 k c = false) (hNE : ∀ a ℓ k, NE ≤ a → φ a ℓ k c = false) :
    PassiveRun E C θ R K (levPR L) c ωs φ := by
  refine passiveRun_of_slots E C θ R K (levPR L) (fun a ℓ k hs => ?_)
  by_cases ha : a < NE
  · exact h (a, ℓ) (mem_slots ha hs) k
  · exact hNE a ℓ k (by omega)

/-- **Non-interference up to the horizon from finitely many coordinates.** If `c`'s filter bits are `false` at
the coordinates `slots L (E c) NE × Fin K` (no condition on any other coin, in particular none at epochs `≥ NE`),
then removing `c` from the run changes every sub-pool after `a ≤ NE` epochs only by removing `c`. This is the
horizon-restricted form of P0052's `pools_erase_of_passive`, which is what a regret walk up to `NE` uses. -/
theorem pools_erase_of_slots_lt {L NE : ℕ} (c : ι) (ωs ωs' : ι → Bool) (hs : AgreeOff c ωs ωs')
    (hs' : ωs' c = false) (φ φ' : ℕ → ℕ → Fin K → ι → Bool)
    (h : ∀ x ∈ slots L (E c) NE, ∀ k, φ x.1 x.2 k c = false)
    (hφ' : ∀ a ℓ k, AgreeOff c (φ a ℓ k) (φ' a ℓ k)) :
    ∀ a, a ≤ NE → ∀ ℓ, (pools E C θ R K (levPR L) ωs φ a ℓ).erase c =
      pools E C θ R K (levPR L) ωs' φ' a ℓ := by
  intro a ha ℓ
  have hp : PassiveRun E C θ R K (levPR L) c ωs (trunc K NE φ) := by
    refine passiveRun_of_slots_lt E C θ R K (L := L) (NE := NE) (fun x hx k => ?_) (fun a ℓ k hNE => ?_)
    · have hx1 : x.1 < NE := by
        classical
        unfold slots at hx
        simp only [mem_filter, mem_product, mem_Ico] at hx
        exact hx.1.1.2
      simp [trunc, hx1, h x hx k]
    · simp [trunc, show ¬ a < NE by omega]
  have hagree : ∀ a ℓ k, AgreeOff c (trunc K NE φ a ℓ k) (trunc K NE φ' a ℓ k) := by
    intro a ℓ k x hx
    simp only [trunc]
    split_ifs
    · exact hφ' a ℓ k x hx
    · rfl
  have := pools_erase_of_passive E C θ R K (levPR L) c ωs ωs' hs hs' (trunc K NE φ) (trunc K NE φ') hp hagree a ℓ
  rwa [pools_trunc E C θ R K (levPR L) ωs φ NE a ha,
    pools_trunc E C θ R K (levPR L) ωs' φ' NE a ha] at this

end Count

end Pool.P0062
