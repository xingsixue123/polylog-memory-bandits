import Pool.Prelude

/-!
# Deterministic core of Peng–Rubinstein's Merge lemma (one Filter round)

Peng–Rubinstein (arXiv:2303.01673, Lemma 4.4) bound the pool size of their low-memory experts algorithm by showing
that a random filter set removes a `1/O(log)` fraction of the pool in each Filter round. This file proves the
deterministic part of that argument for loss data given as arbitrary cumulative losses `C` (true or estimated; `main`
additionally assumes that every pool interval loss lies in `[0, Tmax]`), with an arbitrary cover margin `θ`, so that it
can be reused for full-information and bandit variants.

* Experts form a linearly ordered type `ι` (entry order, ties broken); `E i` is the entry epoch (monotone);
  `C i e` is the cumulative loss of `i` before epoch `e`, so `Lint C i a b = C i b - C i a`.
* `Covered E C t θ F j len`: there is a chain `f₁, …, f_m` of members of `F` (`m ≤ len`) with
  `E f₁ ≤ E j ≤ E f₂ ≤ … ≤ E f_m ≤ t` and `L_j[E j, t) ≥ L_{f₁}[E j, E f₂) + L_{f₂}[E f₂, E f₃) + … + L_{f_m}[E f_m, t) − θ`.
  This is a chain version of Peng–Rubinstein's Definition 4.2, and it is strictly stronger. Their benchmark is
  the minimum over entered members of `F` on each piece of the partition by filter entry epochs. Informally, a chain
  cover is also a cover for that benchmark, since each chain piece is a union of partition pieces on which the
  chain's expert has entered. That implication is NOT proved in this file. The converse fails: the benchmark may
  switch back to an older expert, which a chain cannot do. Results here are about `Covered` exactly as defined.
* The analysis process (`D`, `Rset`, `Oset`, `Wnext`, `Wof`, `Uof`) follows their proof: comparability sets with
  doubling slack `2^r θ`, heavy experts `R_r`, pivots `j_r` (latest filter member of `W_r \ R_r`), late experts `O_r`.
  Every set the analysis inspects is a deterministic function of the pivot list, so randomness enters only through
  two **goodness properties** of `F` over explicit families of sets:
  `G1` (every comparability set with at least `k` elements meets `F`) and `G2` (for every pivot list, the candidate
  set, if it has at least `k` elements, has a member of `F` among its `k` latest elements).
  A union bound over these families replaces the "deferred decisions" in the original proof.
* `main`: under `G1`, `G2` and a size condition, at least `a` experts of `Q` are, unless in `F`, covered by `F`-chains
  of length `≤ rstar`, where `2^{rstar-1} θ` exceeds every interval loss `Tmax`.
* `card_filterRound_le`: hence one Filter round leaves at most `|Q| − a + 2|F|` experts.
-/

open Finset

namespace Pool.P0030

variable {ι : Type*} [LinearOrder ι] (E : ι → ℕ) (C : ι → ℕ → ℝ) (t : ℕ) (θ : ℝ)

/-- Loss of expert `i` over epochs `[a, b)`, from cumulative losses. -/
def Lint (i : ι) (a b : ℕ) : ℝ := C i b - C i a

theorem Lint_add (i : ι) (a b c : ℕ) : Lint C i a b + Lint C i b c = Lint C i a c := by
  unfold Lint; ring

/-- Loss of a chain of experts started at epoch `a`: the first expert covers `[a, E f₂)`, the
`s`-th covers `[E f_s, E f_{s+1})`, the last covers `[E f_m, t)`. -/
def pieceSum : List ι → ℕ → ℝ
  | [], _ => 0
  | [f], a => Lint C f a t
  | f :: g :: rest, a => Lint C f a (E g) + pieceSum (g :: rest) (E g)

/-- Validity of a chain started at epoch `a`: each expert has entered when its piece starts and the
breakpoints are nondecreasing and at most `t`. -/
def ChainOK : List ι → ℕ → Prop
  | [], _ => False
  | [f], a => E f ≤ a ∧ a ≤ t
  | f :: g :: rest, a => E f ≤ a ∧ a ≤ E g ∧ ChainOK (g :: rest) (E g)

/-- `j` is covered (margin `θ`) by a chain of at most `len` members of `F`. -/
def Covered (F : Finset ι) (j : ι) (len : ℕ) : Prop :=
  ∃ ch : List ι, ch.length ≤ len ∧ (∀ f ∈ ch, f ∈ F) ∧ ChainOK E t ch (E j) ∧
    pieceSum E C t ch (E j) - θ ≤ Lint C j (E j) t

/-- Current breakpoint of a pivot list (head = oldest-entering pivot so far). -/
def tau : List ι → ℕ
  | [] => t
  | j :: _ => E j

variable (Q : Finset ι) (k : ℕ)

open Classical in
/-- Experts older than `i` that are comparable with `i` on `[E i, τ)`, with slack `2^{|ps|} θ`. -/
noncomputable def D (ps : List ι) (i : ι) : Finset ι :=
  Q.filter fun j => j < i ∧
    Lint C j (E i) (tau E t ps) - 2 ^ ps.length * θ ≤ Lint C i (E i) (tau E t ps)

open Classical in
/-- Experts of `W` with many comparable older experts. -/
noncomputable def Rset (W : Finset ι) (ps : List ι) : Finset ι :=
  W.filter fun i => k ≤ (D E C t θ Q ps i).card

/-- Invariant of the analysis at a pivot list. -/
def Inv (W : Finset ι) (ps : List ι) : Prop :=
  ∀ w ∈ W, (∀ p ∈ ps.head?, w < p) ∧
    pieceSum E C t ps (tau E t ps) + (2 ^ ps.length - 1) * θ ≤ Lint C w (tau E t ps) t

/-- Pivots are filter members and form a valid chain from the current breakpoint. -/
def PivOK (F : Finset ι) (ps : List ι) : Prop :=
  (∀ p ∈ ps, p ∈ F) ∧ (ps = [] ∨ ChainOK E t ps (tau E t ps))

theorem pieceSum_cons (j : ι) (ps : List ι) (a : ℕ) :
    pieceSum E C t (j :: ps) a = Lint C j a (tau E t ps) + pieceSum E C t ps (tau E t ps) := by
  cases ps with
  | nil => simp [pieceSum, tau]
  | cons g rest => simp [pieceSum, tau]

/-- **Case 1 step**: an expert of `W` with a comparable older filter member is covered. -/
theorem covered_of_D (hE : Monotone E) (hQt : ∀ i ∈ Q, E i ≤ t) (F : Finset ι) (W : Finset ι)
    (ps : List ι) (hinv : Inv E C t θ W ps) (hpiv : PivOK E t F ps) {i j : ι} (hi : i ∈ W)
    (hiQ : i ∈ Q) (hj : j ∈ D E C t θ Q ps i) (hjF : j ∈ F) :
    Covered E C t θ F i (ps.length + 1) := by
  classical
  have hj' := (Finset.mem_filter.mp hj).2
  obtain ⟨hji, hjL⟩ := hj'
  obtain ⟨hhead, hsum⟩ := hinv i hi
  refine ⟨j :: ps, by simp, ?_, ?_, ?_⟩
  · intro f hf
    rcases List.mem_cons.mp hf with h | h
    · rw [h]; exact hjF
    · exact hpiv.1 f h
  · -- chain validity
    cases ps with
    | nil =>
      exact ⟨hE hji.le, hQt i hiQ⟩
    | cons g rest =>
      have hig : i < g := hhead g (by simp)
      refine ⟨hE hji.le, hE hig.le, ?_⟩
      rcases hpiv.2 with h | h
      · exact absurd h (List.cons_ne_nil g rest)
      · simpa [tau] using h
  · rw [pieceSum_cons, ← Lint_add C i (E i) (tau E t ps) t]
    have h2 : (2 : ℝ) ^ ps.length * θ - θ = (2 ^ ps.length - 1) * θ := by ring
    linarith

open Classical in
/-- Experts of `W \ R` entering no earlier than the new pivot `j`. -/
noncomputable def Oset (W : Finset ι) (ps : List ι) (j : ι) : Finset ι :=
  (W \ Rset E C t θ Q k W ps).filter fun w => j ≤ w

/-- The surviving set after choosing pivot `j`. -/
noncomputable def Wnext (W : Finset ι) (ps : List ι) (j : ι) : Finset ι :=
  W \ (Rset E C t θ Q k W ps ∪ Oset E C t θ Q k W ps j ∪ D E C t θ Q ps j)

/-- **Case 2 step**: the invariant passes to the extended pivot list. -/
theorem inv_step (hE : Monotone E) (hQt : ∀ i ∈ Q, E i ≤ t) (F W : Finset ι) (hWQ : W ⊆ Q)
    (ps : List ι) (hinv : Inv E C t θ W ps) (hpiv : PivOK E t F ps) {j : ι}
    (hjU : j ∈ W \ Rset E C t θ Q k W ps) (hjF : j ∈ F) :
    Inv E C t θ (Wnext E C t θ Q k W ps j) (j :: ps) ∧ PivOK E t F (j :: ps) := by
  classical
  have hjW : j ∈ W := (Finset.mem_sdiff.mp hjU).1
  obtain ⟨hjhead, -⟩ := hinv j hjW
  constructor
  · intro w hw
    simp only [Wnext, Finset.mem_sdiff, Finset.mem_union, not_or] at hw
    obtain ⟨hwW, ⟨hwR, hwO⟩, hwD⟩ := hw
    have hwU : w ∈ W \ Rset E C t θ Q k W ps := Finset.mem_sdiff.mpr ⟨hwW, hwR⟩
    have hwj : w < j := by
      by_contra hc
      apply hwO
      exact Finset.mem_filter.mpr ⟨hwU, not_lt.mp hc⟩
    refine ⟨fun p hp => by simp at hp; rw [← hp]; exact hwj, ?_⟩
    obtain ⟨-, hsum⟩ := hinv w hwW
    have hnotD : ¬ (Lint C w (E j) (tau E t ps) - 2 ^ ps.length * θ ≤ Lint C j (E j) (tau E t ps)) := by
      intro h
      apply hwD
      exact Finset.mem_filter.mpr ⟨hWQ hwW, hwj, h⟩
    push Not at hnotD
    simp only [tau, List.length_cons]
    rw [pieceSum_cons, ← Lint_add C w (E j) (tau E t ps) t, pow_succ]
    have h2 : ((2 : ℝ) ^ ps.length * 2 - 1) * θ = 2 ^ ps.length * θ + (2 ^ ps.length - 1) * θ := by
      ring
    rw [h2]
    linarith
  · refine ⟨fun p hp => ?_, Or.inr ?_⟩
    · rcases List.mem_cons.mp hp with h | h
      · rw [h]; exact hjF
      · exact hpiv.1 p h
    · cases ps with
      | nil => exact ⟨le_refl _, hQt j (hWQ hjW)⟩
      | cons g rest =>
        have hjg : j < g := hjhead g (by simp)
        refine ⟨le_refl _, hE hjg.le, ?_⟩
        rcases hpiv.2 with h | h
        · exact absurd h (List.cons_ne_nil g rest)
        · simpa [tau] using h

/-- Size accounting for Case 2. -/
theorem card_Wnext (W : Finset ι) (ps : List ι) {j : ι} (hjU : j ∈ W \ Rset E C t θ Q k W ps) :
    W.card ≤ (Wnext E C t θ Q k W ps j).card + (Rset E C t θ Q k W ps).card +
      (Oset E C t θ Q k W ps j).card + (k - 1) := by
  classical
  have hjR : ¬ k ≤ (D E C t θ Q ps j).card := by
    intro h
    exact (Finset.mem_sdiff.mp hjU).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hjU).1, h⟩)
  have hD : (D E C t θ Q ps j).card ≤ k - 1 := by omega
  have h1 : W ⊆ Wnext E C t θ Q k W ps j ∪ (Rset E C t θ Q k W ps ∪ Oset E C t θ Q k W ps j ∪
      D E C t θ Q ps j) := by
    intro w hw
    by_cases h : w ∈ Rset E C t θ Q k W ps ∪ Oset E C t θ Q k W ps j ∪ D E C t θ Q ps j
    · exact Finset.mem_union_right _ h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hw, h⟩)
  calc W.card ≤ (Wnext E C t θ Q k W ps j ∪ (Rset E C t θ Q k W ps ∪ Oset E C t θ Q k W ps j ∪
        D E C t θ Q ps j)).card := Finset.card_le_card h1
    _ ≤ (Wnext E C t θ Q k W ps j).card + (Rset E C t θ Q k W ps ∪ Oset E C t θ Q k W ps j ∪
        D E C t θ Q ps j).card := Finset.card_union_le _ _
    _ ≤ (Wnext E C t θ Q k W ps j).card + ((Rset E C t θ Q k W ps).card +
        (Oset E C t θ Q k W ps j).card + (D E C t θ Q ps j).card) := by
        have := Finset.card_union_le (Rset E C t θ Q k W ps ∪ Oset E C t θ Q k W ps j)
          (D E C t θ Q ps j)
        have := Finset.card_union_le (Rset E C t θ Q k W ps) (Oset E C t θ Q k W ps j)
        omega
    _ ≤ _ := by omega

/-- At most `k` elements of a finset have fewer than `k` elements of the finset below them. -/
theorem card_few_below (S : Finset ι) (k : ℕ) :
    (S.filter fun i => (S.filter (· < i)).card < k).card ≤ k := by
  classical
  have hinj : Set.InjOn (fun i => (S.filter (· < i)).card)
      (S.filter fun i => (S.filter (· < i)).card < k) := by
    intro x hx y hy hxy
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have : (S.filter (· < x)).card < (S.filter (· < y)).card := by
        apply Finset.card_lt_card
        refine ⟨fun z hz => ?_, ?_⟩
        · simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans h⟩
        · intro hsub
          have hxS : x ∈ S := (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
          have := hsub (Finset.mem_filter.mpr ⟨hxS, h⟩)
          simp at this
      simp only at hxy; omega
    · have : (S.filter (· < y)).card < (S.filter (· < x)).card := by
        apply Finset.card_lt_card
        refine ⟨fun z hz => ?_, ?_⟩
        · simp only [Finset.mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.trans h⟩
        · intro hsub
          have hyS : y ∈ S := (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1
          have := hsub (Finset.mem_filter.mpr ⟨hyS, h⟩)
          simp at this
      simp only at hxy; omega
  have := Finset.card_le_card_of_injOn (fun i => (S.filter (· < i)).card)
    (t := Finset.range k) (fun i hi => by
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hi
      simp [hi.2]) hinj
  simpa using this

/-- **Termination**: once the slack `2^{|ps|} θ` exceeds every interval loss, all but at most `k`
experts of `W` have at least `k` comparable older experts. -/
theorem card_U_le (hE : Monotone E) (hQt : ∀ i ∈ Q, E i ≤ t) (Tmax : ℝ)
    (hL : ∀ i ∈ Q, ∀ a b, a ≤ b → b ≤ t → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (W : Finset ι) (hWQ : W ⊆ Q) (ps : List ι) (hinv : Inv E C t θ W ps)
    (hτt : tau E t ps ≤ t) (hT : Tmax ≤ 2 ^ ps.length * θ) :
    (W \ Rset E C t θ Q k W ps).card ≤ k := by
  classical
  have hsub : W \ Rset E C t θ Q k W ps ⊆ Q.filter fun i => (Q.filter (· < i)).card < k := by
    intro i hi
    obtain ⟨hiW, hiR⟩ := Finset.mem_sdiff.mp hi
    have hiQ := hWQ hiW
    refine Finset.mem_filter.mpr ⟨hiQ, ?_⟩
    by_contra hk
    push Not at hk
    apply hiR
    refine Finset.mem_filter.mpr ⟨hiW, le_trans hk (Finset.card_le_card ?_)⟩
    -- every older expert of `Q` is comparable
    have hEi : E i ≤ tau E t ps := by
      obtain ⟨hhead, -⟩ := hinv i hiW
      cases ps with
      | nil => exact hQt i hiQ
      | cons g rest => exact hE (hhead g (by simp)).le
    intro j hj
    obtain ⟨hjQ, hji⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨hjQ, hji, ?_⟩
    have h1 := (hL j hjQ (E i) (tau E t ps) hEi hτt).2
    have h2 := (hL i hiQ (E i) (tau E t ps) hEi hτt).1
    linarith
  exact (Finset.card_le_card hsub).trans (card_few_below Q k)

/-- The analysis process: surviving set after a pivot list. -/
noncomputable def Wof : List ι → Finset ι
  | [] => Q
  | j :: ps => Wnext E C t θ Q k (Wof ps) ps j

/-- Candidate set for the next pivot. -/
noncomputable def Uof (ps : List ι) : Finset ι := Wof E C t θ Q k ps \ Rset E C t θ Q k (Wof E C t θ Q k ps) ps

/-- **Goodness G1**: every large comparability set (for pivot lists shorter than `rstar`) meets `F`. -/
def G1 (F : Finset ι) (rstar : ℕ) : Prop :=
  ∀ ps : List ι, ps.length < rstar → (∀ p ∈ ps, p ∈ Q) → ∀ i ∈ Q, k ≤ (D E C t θ Q ps i).card →
    ∃ f ∈ F, f ∈ D E C t θ Q ps i

/-- **Goodness G2**: for every pivot list shorter than `rstar`, if the candidate set has at least `k`
elements then one of its `k` latest elements is in `F`. -/
def G2 (F : Finset ι) (rstar : ℕ) : Prop :=
  ∀ ps : List ι, ps.length < rstar → (∀ p ∈ ps, p ∈ Q) → k ≤ (Uof E C t θ Q k ps).card →
    ∃ f ∈ F, f ∈ Uof E C t θ Q k ps ∧ ((Uof E C t θ Q k ps).filter (f < ·)).card < k

theorem Wof_sub (ps : List ι) : Wof E C t θ Q k ps ⊆ Q := by
  induction ps with
  | nil => exact le_refl _
  | cons j ps ih => exact (Finset.sdiff_subset).trans ih

theorem tau_le (hQt : ∀ i ∈ Q, E i ≤ t) (ps : List ι) (hps : ∀ p ∈ ps, p ∈ Q) : tau E t ps ≤ t := by
  cases ps with
  | nil => exact le_refl _
  | cons g rest => exact hQt g (hps g (by simp))

/-- **Deterministic core of PR23's Merge lemma (one Filter round).** Under the goodness properties,
there is a set of at least `a` experts of `Q` every one of which, if not itself in `F`, is covered
(margin `θ`) by a chain of at most `rstar` members of `F`. -/
theorem main (hE : Monotone E) (hQt : ∀ i ∈ Q, E i ≤ t) (Tmax : ℝ)
    (hL : ∀ i ∈ Q, ∀ a b, a ≤ b → b ≤ t → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (F : Finset ι) (rstar a : ℕ) (hr : 1 ≤ rstar) (hT : Tmax ≤ 2 ^ (rstar - 1) * θ)
    (hsize : a + k + (rstar - 1) * (a + 2 * k) ≤ Q.card)
    (hG1 : G1 E C t θ Q k F rstar) (hG2 : G2 E C t θ Q k F rstar) :
    ∃ R ⊆ Q, a ≤ R.card ∧ ∀ i ∈ R, i ∉ F → Covered E C t θ F i rstar := by
  classical
  -- Case 1 at a reachable stage suffices
  have case1 : ∀ ps : List ι, ps.length < rstar → (∀ p ∈ ps, p ∈ Q) →
      Inv E C t θ (Wof E C t θ Q k ps) ps →
      PivOK E t F ps → a ≤ (Rset E C t θ Q k (Wof E C t θ Q k ps) ps).card →
      ∃ R ⊆ Q, a ≤ R.card ∧ ∀ i ∈ R, i ∉ F → Covered E C t θ F i rstar := by
    intro ps hlen hpsQ hinv hpiv hR
    refine ⟨Rset E C t θ Q k (Wof E C t θ Q k ps) ps, ?_, hR, ?_⟩
    · exact (Finset.filter_subset _ _).trans (Wof_sub E C t θ Q k ps)
    · intro i hi hiF
      obtain ⟨hiW, hk⟩ := Finset.mem_filter.mp hi
      obtain ⟨f, hfF, hfD⟩ := hG1 ps hlen hpsQ i (Wof_sub E C t θ Q k ps hiW) hk
      obtain ⟨ch, hch, rest⟩ := covered_of_D E C t θ Q hE hQt F _ ps hinv hpiv hiW
        (Wof_sub E C t θ Q k ps hiW) hfD hfF
      exact ⟨ch, hch.trans (by omega), rest⟩
  -- the stage invariant
  have stage : ∀ m, m < rstar → (∃ R ⊆ Q, a ≤ R.card ∧ ∀ i ∈ R, i ∉ F → Covered E C t θ F i rstar) ∨
      ∃ ps : List ι, ps.length = m ∧ (∀ p ∈ ps, p ∈ Q) ∧ Inv E C t θ (Wof E C t θ Q k ps) ps ∧
        PivOK E t F ps ∧ Q.card ≤ (Wof E C t θ Q k ps).card + m * (a + 2 * k) := by
    intro m
    induction m with
    | zero =>
      intro _
      right
      refine ⟨[], rfl, by simp, ?_, ⟨by simp, Or.inl rfl⟩, by simp [Wof]⟩
      intro w _
      simp [pieceSum, tau, Lint]
    | succ m ih =>
      intro hm
      rcases ih (by omega) with h | ⟨ps, hlen, hpsQ, hinv, hpiv, hcard⟩
      · exact Or.inl h
      · by_cases hR : a ≤ (Rset E C t θ Q k (Wof E C t θ Q k ps) ps).card
        · exact Or.inl (case1 ps (by omega) hpsQ hinv hpiv hR)
        · right
          push Not at hR
          set W := Wof E C t θ Q k ps
          set U := Uof E C t θ Q k ps
          have hUdef : U = W \ Rset E C t θ Q k W ps := rfl
          have hUcard : W.card ≤ U.card + (Rset E C t θ Q k W ps).card := by
            have := Finset.card_sdiff_add_card_inter W (Rset E C t θ Q k W ps)
            have h2 : (W ∩ Rset E C t θ Q k W ps).card ≤ (Rset E C t θ Q k W ps).card :=
              Finset.card_le_card Finset.inter_subset_right
            rw [hUdef]; omega
          have hmle : m * (a + 2 * k) ≤ (rstar - 1) * (a + 2 * k) :=
            Nat.mul_le_mul_right _ (by omega)
          have hUk : k ≤ U.card := by
            generalize m * (a + 2 * k) = X at *
            generalize (rstar - 1) * (a + 2 * k) = Y at *
            omega
          obtain ⟨f, hfF, hfU, hfew0⟩ := hG2 ps (by omega) hpsQ hUk
          have hfew : (U.filter (f < ·)).card < k := hfew0
          -- the new pivot: the latest filter member of `U`
          have hne : (U ∩ F).Nonempty := ⟨f, Finset.mem_inter.mpr ⟨hfU, hfF⟩⟩
          set j := (U ∩ F).max' hne
          have hjUF : j ∈ U ∩ F := Finset.max'_mem _ _
          have hjU : j ∈ U := (Finset.mem_inter.mp hjUF).1
          have hjF : j ∈ F := (Finset.mem_inter.mp hjUF).2
          have hfj : f ≤ j := Finset.le_max' _ f (Finset.mem_inter.mpr ⟨hfU, hfF⟩)
          have hO : (Oset E C t θ Q k W ps j).card ≤ k := by
            have hsub : Oset E C t θ Q k W ps j ⊆ insert f (U.filter (f < ·)) := by
              intro w hw
              obtain ⟨hwU, hjw⟩ := Finset.mem_filter.mp hw
              rcases eq_or_lt_of_le (hfj.trans hjw) with h | h
              · rw [← h]; exact Finset.mem_insert_self _ _
              · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hwU, h⟩)
            calc (Oset E C t θ Q k W ps j).card ≤ (insert f (U.filter (f < ·))).card :=
                  Finset.card_le_card hsub
              _ ≤ (U.filter (f < ·)).card + 1 := Finset.card_insert_le _ _
              _ ≤ k := by omega
          have hstep := inv_step E C t θ Q k hE hQt F W (Wof_sub E C t θ Q k ps) ps hinv hpiv hjU hjF
          have hcardW := card_Wnext E C t θ Q k W ps hjU
          refine ⟨j :: ps, by simp [hlen], ?_, hstep.1, hstep.2, ?_⟩
          · intro p hp
            rcases List.mem_cons.mp hp with h | h
            · rw [h]; exact Wof_sub E C t θ Q k ps (Finset.mem_sdiff.mp hjU).1
            · exact hpsQ p h
          · show Q.card ≤ (Wnext E C t θ Q k W ps j).card + (m + 1) * (a + 2 * k)
            have e : (m + 1) * (a + 2 * k) = m * (a + 2 * k) + a + 2 * k := by ring
            rw [e]
            generalize m * (a + 2 * k) = X at *
            omega
  -- final stage
  rcases stage (rstar - 1) (by omega) with h | ⟨ps, hlen, hpsQ, hinv, hpiv, hcard⟩
  · exact h
  · have hU := card_U_le E C t θ Q k hE hQt Tmax hL (Wof E C t θ Q k ps) (Wof_sub E C t θ Q k ps) ps
      hinv (tau_le E t Q hQt ps hpsQ) (by rw [hlen]; exact hT)
    have hRcard : a ≤ (Rset E C t θ Q k (Wof E C t θ Q k ps) ps).card := by
      have := Finset.card_sdiff_add_card_inter (Wof E C t θ Q k ps)
        (Rset E C t θ Q k (Wof E C t θ Q k ps) ps)
      have h2 : (Wof E C t θ Q k ps ∩ Rset E C t θ Q k (Wof E C t θ Q k ps) ps).card ≤
          (Rset E C t θ Q k (Wof E C t θ Q k ps) ps).card :=
        Finset.card_le_card Finset.inter_subset_right
      omega
    exact case1 ps (by omega) hpsQ hinv hpiv hRcard

open Classical in
/-- One Filter round: keep the filter members and the experts that are not covered. -/
noncomputable def filterRound (F : Finset ι) (len : ℕ) : Finset ι :=
  (Q.filter fun i => ¬ Covered E C t θ F i len) ∪ F

/-- **Size after one Filter round**, under the goodness properties: at most `|Q| - a + 2|F|`. -/
theorem card_filterRound_le (hE : Monotone E) (hQt : ∀ i ∈ Q, E i ≤ t) (Tmax : ℝ)
    (hL : ∀ i ∈ Q, ∀ a b, a ≤ b → b ≤ t → 0 ≤ Lint C i a b ∧ Lint C i a b ≤ Tmax)
    (F : Finset ι) (rstar a : ℕ) (hr : 1 ≤ rstar) (hT : Tmax ≤ 2 ^ (rstar - 1) * θ)
    (hsize : a + k + (rstar - 1) * (a + 2 * k) ≤ Q.card)
    (hG1 : G1 E C t θ Q k F rstar) (hG2 : G2 E C t θ Q k F rstar) :
    (filterRound E C t θ Q F rstar).card + a ≤ Q.card + 2 * F.card := by
  classical
  obtain ⟨R, hRQ, hRa, hRcov⟩ := main E C t θ Q k hE hQt Tmax hL F rstar a hr hT hsize hG1 hG2
  have hsub : (Q.filter fun i => ¬ Covered E C t θ F i rstar) ⊆ Q \ (R \ F) := by
    intro i hi
    obtain ⟨hiQ, hnc⟩ := Finset.mem_filter.mp hi
    refine Finset.mem_sdiff.mpr ⟨hiQ, fun h => ?_⟩
    obtain ⟨hiR, hiF⟩ := Finset.mem_sdiff.mp h
    exact hnc (hRcov i hiR hiF)
  have h1 : (Q.filter fun i => ¬ Covered E C t θ F i rstar).card ≤ Q.card - (R \ F).card := by
    calc _ ≤ (Q \ (R \ F)).card := Finset.card_le_card hsub
      _ = Q.card - (R \ F).card := Finset.card_sdiff_of_subset ((Finset.sdiff_subset).trans hRQ)
  have h2 : R.card ≤ (R \ F).card + F.card := by
    have := Finset.card_sdiff_add_card_inter R F
    have : (R ∩ F).card ≤ F.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have h3 : (R \ F).card ≤ Q.card := (Finset.card_le_card ((Finset.sdiff_subset).trans hRQ))
  have h4 := Finset.card_union_le (Q.filter fun i => ¬ Covered E C t θ F i rstar) F
  unfold filterRound
  omega

/-- Sanity check: the goodness properties are satisfiable (by `F = Q`, when `k ≥ 1`). -/
theorem G1_self (rstar : ℕ) (hk : 1 ≤ k) : G1 E C t θ Q k Q rstar := by
  intro ps _ _ i _ hcard
  obtain ⟨f, hf⟩ := Finset.card_pos.mp (show 0 < (D E C t θ Q ps i).card by omega)
  exact ⟨f, (Finset.mem_filter.mp hf).1, hf⟩

theorem G2_self (rstar : ℕ) (hk : 1 ≤ k) : G2 E C t θ Q k Q rstar := by
  intro ps _ _ hcard
  have hne : (Uof E C t θ Q k ps).Nonempty :=
    Finset.card_pos.mp (show 0 < (Uof E C t θ Q k ps).card by omega)
  refine ⟨(Uof E C t θ Q k ps).max' hne, ?_, Finset.max'_mem _ _, ?_⟩
  · exact Wof_sub E C t θ Q k ps ((Finset.mem_sdiff.mp (Finset.max'_mem _ hne)).1)
  · have : (Uof E C t θ Q k ps).filter (fun x => (Uof E C t θ Q k ps).max' hne < x) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and, not_lt]
      intro hx; exact Finset.le_max' _ x hx
    rw [this]; simp; omega

end Pool.P0030
