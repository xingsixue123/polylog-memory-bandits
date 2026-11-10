import Pool.Prelude

/-!
# A bounded state space for pool learners: sub-pools, pairwise interval losses and in-epoch losses on at most `Ns`
copies, with `log₂ |state| = O(Ns² log TT + Ns log(|ι| 2^{Lt} BB))`

`Raw` stores sub-pools `P : Fin (Lt+1) → Finset ι`, a pairwise table `D : ι → ι → Fin (TT+1)` and per-copy counters
`ep : ι → Fin (BB+1)`. `Valid` asks that the union `U` of the sub-pools has at most `Ns` copies and that `D` and `ep`
vanish off `U`. `PState` is the subtype of valid data. `card_PState_le` bounds its cardinality by injecting it into
slot arrays (`enc`: the sorted union with level masks and counters, and the matrix of `D` on it).
-/

open Finset

namespace Pool.P0078

variable {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {Lt Ns TT BB : ℕ}

/-- Raw pool data. -/
abbrev Raw (ι : Type) (Lt TT BB : ℕ) := (Fin (Lt + 1) → Finset ι) × (ι → ι → Fin (TT + 1)) × (ι → Fin (BB + 1))

/-- The copies present in some sub-pool. -/
def U (x : Raw ι Lt TT BB) : Finset ι := Finset.univ.biUnion x.1

theorem mem_U {x : Raw ι Lt TT BB} {c : ι} : c ∈ U x ↔ ∃ ℓ, c ∈ x.1 ℓ := by
  simp [U]

/-- Valid data: at most `Ns` copies, tables vanish off the pool. -/
def Valid (Ns : ℕ) (x : Raw ι Lt TT BB) : Prop :=
  (U x).card ≤ Ns ∧ (∀ c d, (c ∉ U x ∨ d ∉ U x) → x.2.1 c d = 0) ∧ ∀ c, c ∉ U x → x.2.2 c = 0

/-- The bounded state space. -/
abbrev PState (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (Lt Ns TT BB : ℕ) :=
  {x : Raw ι Lt TT BB // Valid Ns x}

/-- Slot arrays. -/
abbrev Arr (ι : Type) (Lt Ns TT BB : ℕ) :=
  (Fin Ns → Option (ι × (Fin (Lt + 1) → Bool) × Fin (BB + 1))) × (Fin Ns → Fin Ns → Fin (TT + 1))

/-- Encoding into slot arrays: the sorted pool with level masks and counters, and the table on it. -/
def enc (Ns : ℕ) (x : Raw ι Lt TT BB) : Arr ι Lt Ns TT BB :=
  (fun k => if h : k.1 < ((U x).sort (· ≤ ·)).length then
      some (((U x).sort (· ≤ ·))[k.1], fun ℓ => decide (((U x).sort (· ≤ ·))[k.1] ∈ x.1 ℓ),
        x.2.2 ((U x).sort (· ≤ ·))[k.1]) else none,
   fun k k' => if h : k.1 < ((U x).sort (· ≤ ·)).length ∧ k'.1 < ((U x).sort (· ≤ ·)).length then
      x.2.1 ((U x).sort (· ≤ ·))[k.1] ((U x).sort (· ≤ ·))[k'.1] else 0)

theorem enc_inj {x y : Raw ι Lt TT BB} (hx : Valid Ns x) (hy : Valid Ns y) (h : enc Ns x = enc Ns y) : x = y := by
  set lx := (U x).sort (· ≤ ·) with hlx
  set ly := (U y).sort (· ≤ ·) with hly
  have hlenx : lx.length ≤ Ns := by rw [hlx, Finset.length_sort]; exact hx.1
  have hleny : ly.length ≤ Ns := by rw [hly, Finset.length_sort]; exact hy.1
  have h1 : ∀ k : Fin Ns, (enc Ns x).1 k = (enc Ns y).1 k := fun k => by rw [h]
  have h2 : ∀ k k' : Fin Ns, (enc Ns x).2 k k' = (enc Ns y).2 k k' := fun k k' => by rw [h]
  -- the sorted lists agree
  have hlen : lx.length = ly.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := h1 ⟨lx.length, lt_of_lt_of_le hlt hleny⟩
      simp only [enc, ← hlx, ← hly, lt_irrefl, dite_false, hlt, dite_true] at this
      exact absurd this.symm (Option.some_ne_none _)
    · have := h1 ⟨ly.length, lt_of_lt_of_le hlt hlenx⟩
      simp only [enc, ← hlx, ← hly, lt_irrefl, dite_false, hlt, dite_true] at this
      exact absurd this (Option.some_ne_none _)
  have hget : ∀ (k : ℕ) (hk : k < lx.length), lx[k] = ly[k]'(hlen ▸ hk) ∧
      (∀ ℓ, decide (lx[k] ∈ x.1 ℓ) = decide (ly[k]'(hlen ▸ hk) ∈ y.1 ℓ)) ∧
      x.2.2 lx[k] = y.2.2 (ly[k]'(hlen ▸ hk)) := by
    intro k hk
    have := h1 ⟨k, lt_of_lt_of_le hk hlenx⟩
    simp only [enc, ← hlx, ← hly, hk, dite_true, hlen ▸ hk, Option.some.injEq, Prod.mk.injEq] at this
    exact ⟨this.1, fun ℓ => congrFun this.2.1 ℓ, this.2.2⟩
  have hl : lx = ly := List.ext_getElem hlen fun k hk _ => (hget k hk).1
  have hU : U x = U y := by
    have hx' : (lx).toFinset = U x := by rw [hlx]; exact Finset.sort_toFinset _ _
    have hy' : (ly).toFinset = U y := by rw [hly]; exact Finset.sort_toFinset _ _
    rw [← hx', ← hy', hl]
  -- every member of `U x` is some `lx[k]`
  have hidx : ∀ c ∈ U x, ∃ (k : ℕ) (hk : k < lx.length), lx[k] = c := by
    intro c hc
    have : c ∈ lx := by rw [hlx, Finset.mem_sort]; exact hc
    obtain ⟨k, hk, hkc⟩ := List.mem_iff_getElem.mp this
    exact ⟨k, hk, hkc⟩
  obtain ⟨Px, Dx, ex⟩ := x
  obtain ⟨Py, Dy, ey⟩ := y
  simp only at hget hidx hU
  have hP : Px = Py := by
    funext ℓ
    ext c
    constructor
    · intro hc
      have hcU : c ∈ U (Px, Dx, ex) := mem_U.mpr ⟨ℓ, hc⟩
      obtain ⟨k, hk, rfl⟩ := hidx c hcU
      have hiff := decide_eq_decide.mp ((hget k hk).2.1 ℓ)
      have := hiff.mp hc
      rwa [← (hget k hk).1] at this
    · intro hc
      have hcU : c ∈ U (Px, Dx, ex) := by rw [hU]; exact mem_U.mpr ⟨ℓ, hc⟩
      obtain ⟨k, hk, rfl⟩ := hidx c hcU
      have hiff := decide_eq_decide.mp ((hget k hk).2.1 ℓ)
      exact hiff.mpr (by rwa [← (hget k hk).1])
  have he : ex = ey := by
    funext c
    by_cases hc : c ∈ U (Px, Dx, ex)
    · obtain ⟨k, hk, rfl⟩ := hidx c hc
      rw [(hget k hk).2.2, (hget k hk).1]
    · exact (hx.2.2 c hc).trans (hy.2.2 c (by rw [← hU]; exact hc)).symm
  have hD : Dx = Dy := by
    funext c d
    by_cases hcd : c ∈ U (Px, Dx, ex) ∧ d ∈ U (Px, Dx, ex)
    · obtain ⟨k, hk, rfl⟩ := hidx c hcd.1
      obtain ⟨k', hk', rfl⟩ := hidx d hcd.2
      have := h2 ⟨k, lt_of_lt_of_le hk hlenx⟩ ⟨k', lt_of_lt_of_le hk' hlenx⟩
      simp only [enc, ← hlx, ← hly, hk, hk', hlen ▸ hk, hlen ▸ hk', and_self, dite_true] at this
      rw [this, (hget k hk).1, (hget k' hk').1]
    · rw [not_and_or] at hcd
      exact (hx.2.1 c d hcd).trans (hy.2.1 c d (by rw [← hU]; exact hcd)).symm
  rw [hP, hD, he]

open Classical in
theorem card_PState_le :
    Fintype.card (PState ι Lt Ns TT BB) ≤
      (Fintype.card ι * 2 ^ (Lt + 1) * (BB + 1) + 1) ^ Ns * (TT + 1) ^ (Ns * Ns) := by
  classical
  have hinj : Function.Injective (fun s : PState ι Lt Ns TT BB => enc Ns s.1) := by
    intro s t hst
    exact Subtype.ext (enc_inj s.2 t.2 hst)
  have := Fintype.card_le_of_injective _ hinj
  refine this.trans (le_of_eq ?_)
  simp only [Arr, Fintype.card_prod, Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_bool]
  ring

end Pool.P0078
