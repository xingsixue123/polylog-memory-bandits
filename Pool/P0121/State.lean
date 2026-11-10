import Pool.Prelude

/-!
# A generic bounded state space: at most `Ns` labelled copies, a pairwise table on them, and a global component

`Raw ι Lb G TT` stores a label `lab c : Option Lb` per copy (`none` = absent), a pairwise table
`tab c d : Fin (TT+1)` and a global component `g : G`. `Valid Ns` asks that at most `Ns` copies are present
(`U`) and that the table vanishes off present pairs. `GState` is the subtype of valid data, and
`card_GState_le` bounds its cardinality by `(|ι|·(|Lb|+1) + 1)^Ns · (TT+1)^(Ns·Ns) · |G|` through an
injective encoding into slot arrays (`enc`: the sorted present copies with their labels, the table on them,
and `g`).
-/

open Finset

namespace Pool.P0121.TS

variable {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {Lb G : Type} {Ns TT : ℕ}

/-- Raw data: labels (`none` = absent), pairwise table, global component. -/
abbrev Raw (ι Lb G : Type) (TT : ℕ) := (ι → Option Lb) × (ι → ι → Fin (TT + 1)) × G

/-- The present copies. -/
def U (x : Raw ι Lb G TT) : Finset ι := univ.filter fun c => (x.1 c).isSome

omit [DecidableEq ι] [LinearOrder ι] in
theorem mem_U {x : Raw ι Lb G TT} {c : ι} : c ∈ U x ↔ (x.1 c).isSome := by simp [U]

omit [DecidableEq ι] [LinearOrder ι] in
theorem not_mem_U {x : Raw ι Lb G TT} {c : ι} : c ∉ U x ↔ x.1 c = none := by
  rw [mem_U]; cases x.1 c <;> simp

/-- Valid data: at most `Ns` present copies, the table vanishes off present pairs. -/
def Valid (Ns : ℕ) (x : Raw ι Lb G TT) : Prop :=
  (U x).card ≤ Ns ∧ ∀ c d, (c ∉ U x ∨ d ∉ U x) → x.2.1 c d = 0

/-- The bounded state space. -/
abbrev GState (ι : Type) [Fintype ι] [DecidableEq ι] [LinearOrder ι] (Lb G : Type) (Ns TT : ℕ) :=
  {x : Raw ι Lb G TT // Valid Ns x}

/-- Slot arrays. -/
abbrev Arr (ι Lb G : Type) (Ns TT : ℕ) :=
  (Fin Ns → Option (ι × Option Lb)) × (Fin Ns → Fin Ns → Fin (TT + 1)) × G

/-- The sorted present copies. -/
def srt (x : Raw ι Lb G TT) : List ι := (U x).sort (· ≤ ·)

/-- Encoding into slot arrays. -/
def enc (Ns : ℕ) (x : Raw ι Lb G TT) : Arr ι Lb G Ns TT :=
  (fun k => if h : k.1 < (srt x).length then some ((srt x)[k.1], x.1 (srt x)[k.1]) else none,
   fun k k' => if h : k.1 < (srt x).length ∧ k'.1 < (srt x).length then
      x.2.1 (srt x)[k.1] (srt x)[k'.1] else 0,
   x.2.2)

theorem enc_inj {x y : Raw ι Lb G TT} (hx : Valid Ns x) (hy : Valid Ns y) (h : enc Ns x = enc Ns y) :
    x = y := by
  set lx := srt x with hlx
  set ly := srt y with hly
  have hlenx : lx.length ≤ Ns := by rw [hlx, srt, Finset.length_sort]; exact hx.1
  have hleny : ly.length ≤ Ns := by rw [hly, srt, Finset.length_sort]; exact hy.1
  have h1 : ∀ k : Fin Ns, (enc Ns x).1 k = (enc Ns y).1 k := fun k => by rw [h]
  have h2 : ∀ k k' : Fin Ns, (enc Ns x).2.1 k k' = (enc Ns y).2.1 k k' := fun k k' => by rw [h]
  have h3 : (enc Ns x).2.2 = (enc Ns y).2.2 := by rw [h]
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
      x.1 lx[k] = y.1 (ly[k]'(hlen ▸ hk)) := by
    intro k hk
    have := h1 ⟨k, lt_of_lt_of_le hk hlenx⟩
    simp only [enc, ← hlx, ← hly, hk, dite_true, hlen ▸ hk, Option.some.injEq, Prod.mk.injEq] at this
    exact this
  have hl : lx = ly := List.ext_getElem hlen fun k hk _ => (hget k hk).1
  have hU : U x = U y := by
    have hx' : lx.toFinset = U x := by rw [hlx]; exact Finset.sort_toFinset _ _
    have hy' : ly.toFinset = U y := by rw [hly]; exact Finset.sort_toFinset _ _
    rw [← hx', ← hy', hl]
  have hidx : ∀ c ∈ U x, ∃ (k : ℕ) (hk : k < lx.length), lx[k] = c := by
    intro c hc
    have : c ∈ lx := by rw [hlx, srt, Finset.mem_sort]; exact hc
    obtain ⟨k, hk, hkc⟩ := List.mem_iff_getElem.mp this
    exact ⟨k, hk, hkc⟩
  obtain ⟨labx, tx, gx⟩ := x
  obtain ⟨laby, ty, gy⟩ := y
  simp only at hget hidx hU h3
  have hlab : labx = laby := by
    funext c
    by_cases hc : c ∈ U (labx, tx, gx)
    · obtain ⟨k, hk, rfl⟩ := hidx c hc
      rw [(hget k hk).2, ← (hget k hk).1]
    · have hc' : c ∉ U (laby, ty, gy) := by rw [← hU]; exact hc
      exact (not_mem_U.1 hc).trans (not_mem_U.1 hc').symm
  have ht : tx = ty := by
    funext c d
    by_cases hcd : c ∈ U (labx, tx, gx) ∧ d ∈ U (labx, tx, gx)
    · obtain ⟨k, hk, rfl⟩ := hidx c hcd.1
      obtain ⟨k', hk', rfl⟩ := hidx d hcd.2
      have := h2 ⟨k, lt_of_lt_of_le hk hlenx⟩ ⟨k', lt_of_lt_of_le hk' hlenx⟩
      simp only [enc, ← hlx, ← hly, hk, hk', hlen ▸ hk, hlen ▸ hk', and_self, dite_true] at this
      rw [this, (hget k hk).1, (hget k' hk').1]
    · rw [not_and_or] at hcd
      exact (hx.2 c d hcd).trans (hy.2 c d (by rw [← hU]; exact hcd)).symm
  simp only [enc] at h3
  rw [hlab, ht, h3]

open Classical in
theorem card_GState_le [Fintype Lb] [Fintype G] :
    Fintype.card (GState ι Lb G Ns TT) ≤
      (Fintype.card ι * (Fintype.card Lb + 1) + 1) ^ Ns * (TT + 1) ^ (Ns * Ns) * Fintype.card G := by
  classical
  have hinj : Function.Injective (fun s : GState ι Lb G Ns TT => enc Ns s.1) := by
    intro s t hst
    exact Subtype.ext (enc_inj s.2 t.2 hst)
  refine (Fintype.card_le_of_injective _ hinj).trans (le_of_eq ?_)
  simp only [Arr, Fintype.card_prod, Fintype.card_fun, Fintype.card_option, Fintype.card_fin]
  rw [← pow_mul]; ring

end Pool.P0121.TS
