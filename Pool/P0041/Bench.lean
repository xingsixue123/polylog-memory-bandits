import Pool.P0030.MergeCore

/-!
# PR23's benchmark, computed recursively, is at most any chain's loss
-/

open Finset Pool.P0030

namespace Pool.P0041

variable {ι : Type*} (E : ι → ℕ) (C : ι → ℕ → ℝ) (t : ℕ) (F : Finset ι)

open Classical in
/-- Entry epochs of filter members strictly between `a` and `t`. -/
noncomputable def laterEntries (a : ℕ) : Finset ℕ := (F.image E).filter fun e => a < e ∧ e < t

open Classical in
/-- Next breakpoint after epoch `a`: the first entry epoch of a member of `F` after `a`, or `t`. -/
noncomputable def nextBP (a : ℕ) : ℕ :=
  if h : (laterEntries E t F a).Nonempty then (laterEntries E t F a).min' h else t

theorem nextBP_gt (a : ℕ) (ha : a < t) : a < nextBP E t F a := by
  classical
  unfold nextBP
  split_ifs with h
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.1
  · exact ha

theorem nextBP_le (a : ℕ) : nextBP E t F a ≤ t := by
  classical
  unfold nextBP
  split_ifs with h
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2.2.le
  · exact le_rfl

/-- No member of `F` enters strictly between `a` and `nextBP a`. -/
theorem nextBP_le_entry (a : ℕ) (f : ι) (hf : f ∈ F) (h1 : a < E f) (h2 : E f ≤ t) :
    nextBP E t F a ≤ E f := by
  classical
  rcases h2.lt_or_eq with h2 | h2
  · have hmem : E f ∈ laterEntries E t F a :=
      Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem E hf, h1, h2⟩
    unfold nextBP
    rw [dif_pos ⟨_, hmem⟩]
    exact Finset.min'_le _ _ hmem
  · rw [h2]; exact nextBP_le E t F a

open Classical in
/-- Piecewise benchmark (as we read PR23) from epoch `a` to `t`: on each piece between consecutive filter entry epochs, the
best filter member that has already entered; `⊤` if some piece has no entered member. -/
noncomputable def bench (a : ℕ) : WithTop ℝ :=
  if h : a < t then
    (if hne : (F.filter fun f => E f ≤ a).Nonempty then
        (((F.filter fun f => E f ≤ a).image fun f => Lint C f a (nextBP E t F a)).min' (hne.image _) : WithTop ℝ)
      else ⊤) + bench (nextBP E t F a)
  else 0
termination_by t - a
decreasing_by
  have := nextBP_gt E t F a h
  omega

theorem bench_of_ge (a : ℕ) (ha : t ≤ a) : bench E C t F a = 0 := by
  rw [bench]; simp [not_lt.mpr ha]

theorem bench_of_lt (a : ℕ) (ha : a < t) (f : ι) (hf : f ∈ F) (hfa : E f ≤ a) :
    bench E C t F a ≤ ((Lint C f a (nextBP E t F a) : ℝ) : WithTop ℝ) + bench E C t F (nextBP E t F a) := by
  classical
  rw [bench, dif_pos ha]
  have hmem : f ∈ F.filter fun f => E f ≤ a := Finset.mem_filter.mpr ⟨hf, hfa⟩
  rw [dif_pos ⟨f, hmem⟩]
  gcongr
  exact_mod_cast Finset.min'_le _ _ (Finset.mem_image_of_mem _ hmem)

variable [LinearOrder ι]

theorem chain_le_t : ∀ (ch : List ι) (a : ℕ), ChainOK E t ch a → a ≤ t
  | [], _, h => absurd h id
  | [_], _, h => h.2
  | _ :: g :: rest, _, h => h.2.1.trans (chain_le_t (g :: rest) (E g) h.2.2)

theorem pieceSum_at_t : ∀ (ch : List ι), ChainOK E t ch t → pieceSum E C t ch t = 0
  | [], h => absurd h id
  | [f], _ => by simp [pieceSum, Lint]
  | f :: g :: rest, h => by
    obtain ⟨_, hg, hrest⟩ := h
    have hgt : E g = t := by
      have : E g ≤ t := chain_le_t E t (g :: rest) (E g) hrest
      omega
    simp only [pieceSum]
    rw [hgt] at hrest ⊢
    rw [pieceSum_at_t (g :: rest) hrest]
    simp [Lint]

/-- **A chain cover is a PR23 benchmark cover**: the benchmark from epoch `a` is at most the loss of any
valid chain of filter members started at `a`. -/
theorem bench_le_pieceSum : ∀ (d : ℕ) (a : ℕ), t - a = d → ∀ (ch : List ι), ChainOK E t ch a →
    (∀ f ∈ ch, f ∈ F) → bench E C t F a ≤ ((pieceSum E C t ch a : ℝ) : WithTop ℝ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
    intro a hd ch
    induction ch with
    | nil => intro h; exact absurd h id
    | cons f rest ihch =>
      intro hok hF
      by_cases ha : t ≤ a
      · rw [bench_of_ge E C t F a ha]
        have hat : a = t := le_antisymm (chain_le_t E t _ a hok) ha
        rw [hat] at hok
        rw [hat, pieceSum_at_t E C t (f :: rest) hok]; simp
      push Not at ha
      have hfF : f ∈ F := hF f (by simp)
      have hfa : E f ≤ a := by
        cases rest with
        | nil => exact hok.1
        | cons g r => exact hok.1
      set nb := nextBP E t F a
      have hnb : a < nb := nextBP_gt E t F a ha
      have hnbt : nb ≤ t := nextBP_le E t F a
      have hstep := bench_of_lt E C t F a ha f hfF hfa
      cases rest with
      | nil =>
        -- chain [f]
        have hrec : bench E C t F nb ≤ ((pieceSum E C t [f] nb : ℝ) : WithTop ℝ) :=
          ihd (t - nb) (by omega) nb rfl [f] ⟨hfa.trans hnb.le, hnbt⟩ (by simpa using hfF)
        refine hstep.trans ?_
        simp only [pieceSum] at hrec ⊢
        rw [← Lint_add C f a nb t]
        push_cast
        gcongr
      | cons g rest' =>
        obtain ⟨_, hag, hrest⟩ := hok
        rcases hag.lt_or_eq with hag | hag
        · -- the first filter entry after `a` is not after `E g`
          have hgF : g ∈ F := hF g (by simp)
          have hgt : E g ≤ t := chain_le_t E t _ _ hrest
          have hnbg : nb ≤ E g := nextBP_le_entry E t F a g hgF hag hgt
          have hrec : bench E C t F nb ≤ ((pieceSum E C t (f :: g :: rest') nb : ℝ) : WithTop ℝ) :=
            ihd (t - nb) (by omega) nb rfl (f :: g :: rest') ⟨hfa.trans hnb.le, hnbg, hrest⟩ hF
          refine hstep.trans ?_
          simp only [pieceSum] at hrec ⊢
          rw [← Lint_add C f a nb (E g)]
          push_cast at hrec ⊢
          rw [add_assoc]
          gcongr
        · -- `E g = a`: the first piece is empty
          have hrest' : ChainOK E t (g :: rest') a := by rw [hag]; exact hrest
          have := ihch hrest' (fun x hx => hF x (List.mem_cons_of_mem f hx))
          simp only [pieceSum]
          rw [← hag, show Lint C f a a = 0 by simp [Lint], zero_add]
          rw [hag] at this ⊢
          exact this

/-- Benchmark cover (our reading of PR23 Def. 4.2 / Alg. 5): `j` is covered (margin `θ`) when the benchmark
from its entry epoch is at most
its own loss plus `θ`. -/
def BenchCovered (θ : ℝ) (j : ι) : Prop :=
  bench E C t F (E j) ≤ ((Lint C j (E j) t + θ : ℝ) : WithTop ℝ)

/-- **A chain cover (P0030) implies PR23's benchmark cover**, so a Filter that removes
benchmark-covered experts removes every chain-covered one. -/
theorem benchCovered_of_covered (θ : ℝ) (j : ι) (len : ℕ) (h : Covered E C t θ F j len) :
    BenchCovered E C t F θ j := by
  obtain ⟨ch, -, hF, hok, hle⟩ := h
  have := bench_le_pieceSum E C t F (t - E j) (E j) rfl ch hok hF
  unfold BenchCovered
  refine this.trans ?_
  exact_mod_cast (by linarith : pieceSum E C t ch (E j) ≤ Lint C j (E j) t + θ)

/-- Edge case: the benchmark from epoch `a ≥ t` is the empty sum `0`, so `BenchCovered` holds iff
`0 ≤ Lint C j (E j) t + θ`, whatever `F` is (even `F = ∅`). -/
theorem benchCovered_iff_of_entry_ge (θ : ℝ) (j : ι) (hj : t ≤ E j) :
    BenchCovered E C t F θ j ↔ 0 ≤ Lint C j (E j) t + θ := by
  unfold BenchCovered
  rw [bench_of_ge E C t F (E j) hj]
  exact_mod_cast Iff.rfl

/-- In particular, an expert entering at the current epoch `t` is benchmark-covered for every
`θ ≥ 0`, even when `F` is empty (a chain cover would need an entered filter member). -/
theorem benchCovered_of_entry_eq (θ : ℝ) (hθ : 0 ≤ θ) (j : ι) (hj : E j = t) :
    BenchCovered E C t F θ j := by
  rw [benchCovered_iff_of_entry_ge E C t F θ j hj.ge, hj]
  simpa [Lint] using hθ

open Classical in
/-- A Filter round that evicts benchmark-covered experts: keep the filter and the experts that are not
benchmark-covered. -/
noncomputable def benchFilterRound (Q : Finset ι) (θ : ℝ) : Finset ι :=
  (Q.filter fun i => ¬ BenchCovered E C t F θ i) ∪ F

/-- The benchmark Filter round keeps no more than P0030's chain Filter round (any chain length). -/
theorem benchFilterRound_subset (Q : Finset ι) (θ : ℝ) (len : ℕ) :
    benchFilterRound E C t F Q θ ⊆ filterRound E C t θ Q F len := by
  classical
  intro i hi
  unfold benchFilterRound at hi
  unfold filterRound
  rcases Finset.mem_union.mp hi with hi | hi
  · obtain ⟨hiQ, hnb⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨hiQ, fun hc => hnb (benchCovered_of_covered E C t F θ i len hc)⟩)
  · exact Finset.mem_union_right _ hi

/-- Hence P0030's size bound `card_filterRound_le` applies to the benchmark Filter round. -/
theorem card_benchFilterRound_le (Q : Finset ι) (θ : ℝ) (k : ℕ) (hE : Monotone E)
    (hQt : ∀ i ∈ Q, E i ≤ t) (Tmax : ℝ)
    (hL : ∀ i ∈ Q, ∀ a b, a ≤ b → b ≤ t → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (rstar a : ℕ) (hr : 1 ≤ rstar) (hT : Tmax ≤ 2 ^ (rstar - 1) * θ)
    (hsize : a + k + (rstar - 1) * (a + 2 * k) ≤ Q.card)
    (hG1 : G1 E C t θ Q k F rstar) (hG2 : G2 E C t θ Q k F rstar) :
    (benchFilterRound E C t F Q θ).card + a ≤ Q.card + 2 * F.card := by
  have h1 := Finset.card_le_card (benchFilterRound_subset E C t F Q θ rstar)
  have h2 := card_filterRound_le E C t θ Q k hE hQt Tmax hL F rstar a hr hT hsize hG1 hG2
  omega

end Pool.P0041
