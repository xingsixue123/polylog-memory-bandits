import Pool.P0121.Machine
import Pool.P0121.Ideal

/-!
# The threaded machine follows P0065's process on good runs

Abstract objects along a coin vector `ω` on P0082's coin array (`SlotC NE D Lt K × Cp → Bool`), for the unit
losses `bt ℓ u c = ℓ (u + 1) (arm c)` of the day losses `ℓ`:
* `tp ω a`: P0065's `tpools` with exact covers `cumL cu`; `sp ω a`: its start pools of unit `a`; `pr ω a`: the copies
  present in some start pool.
* `idl ω`: the ideal learner data (`Pool.P0121.TMI.ideal`) along `pr ω`.

`Inv ω a x`: the data `x` has `sp ω a`'s masks, present set `pr ω a`, the true in-lifetime table, and the ideal
learner data.
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0030 Pool.P0042 Pool.P0052 Pool.P0065 Pool.P0121.TS Pool.P0121.TM

namespace Pool.P0121.TMRun

variable {n NE D : ℕ} [NeZero n] {Lv L M Lt K R : ℕ} (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (θ η ε : ℝ) (Ns : ℕ)

section Abstract

variable (ℓ : LossSeq n)

/-- Unit loss bit of a copy. -/
def bt (u : ℕ) (c : Cp n NE D) : ℕ := (ℓ (u + 1) (arm n NE D c)).toNat

/-- Unit loss of a copy (real). -/
def cu (u : ℕ) (c : Cp n NE D) : ℝ := (bt ℓ u c : ℝ)

variable (ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool)

/-- Sampling coins. -/
abbrev ωs : Cp n NE D → Bool := Pool.P0082.ωsC (E n NE D) NE D Lt K ω

/-- Filter coins. -/
abbrev φs : ℕ → ℕ → ℕ → Fin K → Cp n NE D → Bool := Pool.P0082.φC NE D Lt K ω

/-- P0065's pools at the unit boundaries. -/
noncomputable abbrev tp (a : ℕ) : ℕ → ℕ → Finset (Cp n NE D) :=
  tpools (E n NE D) (thr0 n NE D) (Pool.P0061.cumL (cu ℓ)) θ R K D Lv Bt lev (ωs ω) (φs ω) a

/-- P0065's start pools of unit `a`. -/
noncomputable abbrev sp (a : ℕ) : ℕ → ℕ → Finset (Cp n NE D) :=
  startPools (E n NE D) (thr0 n NE D) D Lv Bt (ωs ω) a (tp (Lv := Lv) (R := R) Bt lev θ ℓ ω a)

open Classical in
/-- The present copies of unit `a`. -/
noncomputable def pr (a : ℕ) : Finset (Cp n NE D) :=
  univ.filter fun c => ∃ (r : Fin D) (j : Fin Lv), c ∈ sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a r j

/-- The ideal learner data along `pr`. -/
noncomputable abbrev idl : ℕ → ℕ × (Cp n NE D → ℕ → ℕ × ℕ) :=
  Pool.P0121.TMI.ideal L (pr (Lv := Lv) (R := R) Bt lev θ ℓ ω) (bt ℓ) η ε

/-- Good unit: at most `Ns` present copies. -/
def Good (a : ℕ) : Prop := (pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a).card ≤ Ns

/-- The invariant at the start of unit `a`. -/
def Inv (a : ℕ) (x : RawT n NE D Lv L M) : Prop :=
  (∀ (r : Fin D) (j : Fin Lv) c, mk (x.1 c) r j = decide (c ∈ sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a r j)) ∧
  U x = pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a ∧
  (∀ c ∈ U x, ∀ d ∈ U x, E n NE D c ≤ E n NE D d →
    (x.2.1 c d : ℕ) = ∑ u ∈ Ico (E n NE D d) a, bt ℓ u c) ∧
  kLx x = (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω a).1 ∧
  ∀ c ∈ U x, ∀ j < L + 1, ld x c j = (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω a).2 c j

end Abstract

section Mem

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E' thr0' : ι → ℕ}

/-- Membership in the start pools: an old copy, or a new one. -/
theorem mem_startPools {ωs' : ι → Bool} {a : ℕ} {P : ℕ → ℕ → Finset ι} {c : ι} {r j : ℕ}
    (h : c ∈ startPools E' thr0' D Lv Bt ωs' a P r j) : (∃ r' j', c ∈ P r' j') ∨ E' c = a := by
  unfold startPools sample at h
  split_ifs at h with h1
  · rcases Finset.mem_union.1 h with h | h
    · left
      unfold inherit at h
      split_ifs at h with h2 h3 h4
      · exact ⟨_, _, h⟩
      · rcases Finset.mem_union.1 h with h | h
        · exact ⟨_, _, h⟩
        · obtain ⟨r', -, hr'⟩ := Finset.mem_biUnion.1 h
          obtain ⟨j', -, hj'⟩ := Finset.mem_biUnion.1 hr'
          exact ⟨_, _, hj'⟩
      · exact ⟨_, _, h⟩
      · simp at h
    · right
      simp only [newAtT, Finset.mem_filter] at h
      exact h.2.1
  · left
    unfold inherit at h
    split_ifs at h with h2 h3 h4
    · exact ⟨_, _, h⟩
    · rcases Finset.mem_union.1 h with h | h
      · exact ⟨_, _, h⟩
      · obtain ⟨r', -, hr'⟩ := Finset.mem_biUnion.1 h
        obtain ⟨j', -, hj'⟩ := Finset.mem_biUnion.1 hr'
        exact ⟨_, _, hj'⟩
    · exact ⟨_, _, h⟩
    · simp at h

/-- Start pools read the sampling coins only of the copies entering at `a`. -/
theorem startPools_congr {ωs₁ ωs₂ : ι → Bool} {a : ℕ} (h : ∀ c, E' c = a → ωs₁ c = ωs₂ c)
    (P : ℕ → ℕ → Finset ι) :
    startPools E' thr0' D Lv Bt ωs₁ a P = startPools E' thr0' D Lv Bt ωs₂ a P := by
  have hN : ∀ r, newAtT E' thr0' ωs₁ a r = newAtT E' thr0' ωs₂ a r := by
    intro r; ext c
    simp only [newAtT, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [← h c h1]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h c h1]; exact h3⟩
  unfold startPools sample
  funext r j
  simp only [hN]

/-- Merges of an all-empty family stay empty. -/
theorem mergeUpTo_empty (C : ι → ℕ → ℝ) (φ : ℕ → ℕ → Fin K → ι → Bool) (a m : ℕ) (P : ℕ → Finset ι)
    (hP : ∀ j, P j = ∅) (j : ℕ) : mergeUpTo E' C θ R K φ a m P j = ∅ := by
  ext c
  simp only [Finset.notMem_empty, iff_false]
  intro hc
  obtain ⟨i, hi⟩ := Pool.P0063.mem_mergeUpTo E' C θ R K φ a m P j c hc
  rw [hP i] at hi; simp at hi

end Mem


section Loc

variable (ℓ : LossSeq n) (ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool)

/-- Location of the start pools: entered, thread `< D`, level `< Lv`. -/
theorem sp_ok (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (a : ℕ) :
    StartOK (E n NE D) (thr0 n NE D) D Lv Bt a (sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a) :=
  start_ok hD hLv (tpools_ok hD hLv hlev _ _ a) _

theorem mem_pr {a : ℕ} {c : Cp n NE D} :
    c ∈ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a ↔ ∃ (r : Fin D) (j : Fin Lv), c ∈ sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a r j := by
  classical
  simp [pr]

theorem mem_pr_of (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {a r j : ℕ} {c : Cp n NE D}
    (h : c ∈ sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a r j) : c ∈ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a := by
  obtain ⟨-, -, hj, hr⟩ := sp_ok Bt lev θ ℓ ω hD hLv hlev a c r j h
  exact (mem_pr Bt lev θ ℓ ω).2 ⟨⟨r, hr⟩, ⟨j, hj⟩, h⟩

theorem E_le_of_mem_pr (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {a : ℕ} {c : Cp n NE D}
    (h : c ∈ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a) : E n NE D c ≤ a := by
  obtain ⟨r, j, h⟩ := (mem_pr Bt lev θ ℓ ω).1 h
  exact (sp_ok Bt lev θ ℓ ω hD hLv hlev a c r j h).1

/-- A copy present at `a + 1` but not at `a` entered at `a + 1`. -/
theorem E_of_new (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {a : ℕ} {c : Cp n NE D}
    (h1 : c ∈ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω (a + 1)) (h0 : c ∉ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a) :
    E n NE D c = a + 1 := by
  obtain ⟨r, j, h⟩ := (mem_pr Bt lev θ ℓ ω).1 h1
  rcases mem_startPools Bt h with ⟨r', j', h'⟩ | h'
  · exfalso; apply h0
    have h'' : c ∈ (if Bt r' ∣ a + 1 then mergeUpTo (E n NE D) (Pool.P0061.cumL (cu ℓ)) θ R K (φs ω r') a (lev r' a)
        (sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a r') else sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a r') j' := h'
    split_ifs at h''
    · obtain ⟨i, hi⟩ := Pool.P0063.mem_mergeUpTo _ _ θ R K _ a _ _ j' c h''
      exact mem_pr_of Bt lev θ ℓ ω hD hLv hlev hi
    · exact mem_pr_of Bt lev θ ℓ ω hD hLv hlev h''
  · exact h'

/-- No re-entry (P0102's `hent`). -/
theorem hent (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) :
    ∀ u, ∀ f ∈ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω (u + 1), f ∉ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω u →
      ∀ u' ≤ u, f ∉ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω u' := by
  intro u f h1 h0 u' hu' h
  have := E_of_new Bt lev θ ℓ ω hD hLv hlev h1 h0
  have := E_le_of_mem_pr Bt lev θ ℓ ω hD hLv hlev h
  omega

/-- From the masks: the machine's pools are the start pools. -/
theorem Pn_eq (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {a : ℕ} {x : RawT n NE D Lv L M}
    (hm : ∀ (r : Fin D) (j : Fin Lv) c, mk (x.1 c) r j = decide (c ∈ sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a r j)) :
    ∀ r j, Pn x r j = sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a r j := by
  intro r j
  unfold Pn
  split_ifs with h
  · ext c; simp [hm ⟨r, h.1⟩ ⟨j, h.2⟩ c]
  · ext c
    simp only [Finset.notMem_empty, false_iff]
    intro hc
    obtain ⟨-, -, hj, hr⟩ := sp_ok Bt lev θ ℓ ω hD hLv hlev a c r j hc
    exact h ⟨hr, hj⟩

end Loc

section Bits

variable (Ns : ℕ)

theorem lst_length_le {x : RawT n NE D Lv L M} (hx : Valid Ns x) : (lst x).length ≤ Ns := by
  unfold lst srt; rw [Finset.length_sort]; exact hx.1

theorem mem_lst {x : RawT n NE D Lv L M} {c : Cp n NE D} : c ∈ lst x ↔ c ∈ U x := by
  unfold lst srt; exact Finset.mem_sort _

/-- The queried bit of a present copy is the loss bit of its arm. -/
theorem bitOf_eq {x : RawT n NE D Lv L M} (hx : Valid Ns x) (v : Fin n → Bool) {c : Cp n NE D}
    (hc : c ∈ U x) : bitOf Ns x (fun k => v (qry Ns x k)) c = v (arm n NE D c) := by
  have hmem : c ∈ lst x := (mem_lst).mpr hc
  have hlt : (lst x).idxOf c < (lst x).length := List.idxOf_lt_length_iff.mpr hmem
  have hNs : (lst x).idxOf c < Ns := lt_of_lt_of_le hlt (lst_length_le Ns hx)
  unfold bitOf qry
  rw [dif_pos hNs]
  simp only [dif_pos hlt, List.getElem_idxOf hlt]

end Bits


section Inc

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- P0102's increment depends only on the present copies' data at the round. -/
theorem inc_congr {pr₁ pr₂ : ℕ → Finset ι} {b₁ b₂ : ℕ → ι → ℕ} {k₁ k₂ : ℕ → ℕ} {w₁ w₂ : ℕ → ι → ℕ → ℕ × ℕ}
    {u₁ u₂ : ℕ} (hpr : pr₁ u₁ = pr₂ u₂) (hb : ∀ f ∈ pr₁ u₁, b₁ u₁ f = b₂ u₂ f) (hk : k₁ u₁ = k₂ u₂)
    (hw : ∀ f ∈ pr₁ u₁, ∀ j < L + 1, w₁ u₁ f j = w₂ u₂ f j) :
    Pool.P0102.inc L pr₁ b₁ η ε k₁ w₁ u₁ = Pool.P0102.inc L pr₂ b₂ η ε k₂ w₂ u₂ := by
  have hmw : ∀ f ∈ pr₁ u₁, ∀ j : Fin (L + 1),
      Pool.P0102.mw η ε k₁ w₁ u₁ f j = Pool.P0102.mw η ε k₂ w₂ u₂ f j := by
    intro f hf j
    unfold Pool.P0102.mw; rw [hk, hw f hf j j.2]
  have hA : Pool.P0102.mA L pr₁ η ε k₁ w₁ u₁ = Pool.P0102.mA L pr₂ η ε k₂ w₂ u₂ := by
    unfold Pool.P0102.mA; rw [← hpr]
    exact Finset.sum_congr rfl fun f hf => Finset.sum_congr rfl fun j _ => hmw f hf j
  have hA' : Pool.P0102.mA' L pr₁ b₁ η ε k₁ w₁ u₁ = Pool.P0102.mA' L pr₂ b₂ η ε k₂ w₂ u₂ := by
    unfold Pool.P0102.mA'; rw [← hpr]
    exact Finset.sum_congr rfl fun f hf => Finset.sum_congr rfl fun j _ => by rw [hmw f hf j, hb f hf]
  unfold Pool.P0102.inc
  rw [hA, hA', hpr]

end Inc

section Step

variable (ℓ : LossSeq n) (ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool)

theorem bt_le_one (u : ℕ) (c : Cp n NE D) : bt ℓ u c ≤ 1 := by
  unfold bt; cases ℓ (u + 1) (arm n NE D c) <;> simp

theorem sum_bt_le (m k : ℕ) (c : Cp n NE D) : ∑ u ∈ Ico m k, bt ℓ u c ≤ k - m := by
  calc ∑ u ∈ Ico m k, bt ℓ u c ≤ ∑ _u ∈ Ico m k, 1 := Finset.sum_le_sum fun u _ => bt_le_one ℓ u c
    _ = k - m := by simp

theorem toNat_eq_bt {x : RawT n NE D Lv L M} (hx : Valid Ns x) {a : ℕ} {c : Cp n NE D} (hc : c ∈ U x) :
    (bitOf Ns x (fun k => ℓ (a + 1) (qry Ns x k)) c).toNat = bt ℓ a c := by
  rw [bitOf_eq Ns hx (ℓ (a + 1)) hc]; rfl

/-- The new grid index is the ideal one. -/
theorem kNew_val (hη : 0 ≤ η) (hε : 0 < ε) (hM : NE * ⌊η / ε⌋₊ ≤ M) {a : ℕ} (ha : a + 1 ≤ NE)
    {x : RawT n NE D Lv L M} (hx : Valid Ns x) (hinv : Inv (L := L) (R := R) Bt lev θ η ε ℓ ω a x) :
    ((kNew η ε Ns x (fun k => ℓ (a + 1) (qry Ns x k)) : Fin (M + 1)) : ℕ) =
      (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω (a + 1)).1 := by
  have hinc : Pool.P0102.inc L (fun _ => U x) (fun _ c => (bitOf Ns x (fun k => ℓ (a + 1) (qry Ns x k)) c).toNat)
      η ε (fun _ => kLx x) (fun _ => ld x) 0 =
      Pool.P0102.inc L (pr (Lv := Lv) (R := R) Bt lev θ ℓ ω) (bt ℓ) η ε
        (fun u => (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω u).1)
        (fun u => (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω u).2) a :=
    inc_congr η ε hinv.2.1 (fun f hf => toNat_eq_bt (ℓ := ℓ) Ns hx hf) hinv.2.2.2.1
      (fun f hf j hj => hinv.2.2.2.2 f hf j hj)
  have hval : kLx x + Pool.P0102.inc L (fun _ => U x)
      (fun _ c => (bitOf Ns x (fun k => ℓ (a + 1) (qry Ns x k)) c).toNat) η ε (fun _ => kLx x) (fun _ => ld x) 0 =
      (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω (a + 1)).1 := by
    rw [hinc, hinv.2.2.2.1]; rfl
  have hle := Pool.P0102.kL_le (Pool.P0121.TMI.ideal_rec L (pr (Lv := Lv) (R := R) Bt lev θ ℓ ω) (bt ℓ) η ε)
    (bt_le_one ℓ) hη hε (a + 1)
  have : (a + 1) * ⌊η / ε⌋₊ ≤ M := le_trans (Nat.mul_le_mul_right _ ha) hM
  unfold kNew capN
  simp only
  rw [hval]
  exact min_eq_left (hle.trans this)

/-- The new table holds the true losses since entry. -/
theorem tabN_val (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {a : ℕ} (ha : a + 1 ≤ NE)
    {x : RawT n NE D Lv L M} (hx : Valid Ns x)
    (hinv : Inv (L := L) (R := R) Bt lev θ η ε ℓ ω a x) {c d : Cp n NE D} (hc : c ∈ U x) (hd : d ∈ U x)
    (hcd : E n NE D c ≤ E n NE D d) :
    (tabN Ns x (fun k => ℓ (a + 1) (qry Ns x k)) c d : ℕ) = ∑ u ∈ Ico (E n NE D d) (a + 1), bt ℓ u c := by
  have h0 := hinv.2.2.1 c hc d hd hcd
  have hEd : E n NE D d ≤ a := E_le_of_mem_pr Bt lev θ ℓ ω hD hLv hlev (by rw [← hinv.2.1]; exact hd)
  have hb := toNat_eq_bt (ℓ := ℓ) Ns hx (a := a) hc
  have hs := sum_bt_le ℓ (E n NE D d) a c
  unfold tabN
  rw [Pool.P0078.addB_val, h0, Finset.sum_Ico_succ_top hEd, ← hb]
  · cases bitOf Ns x (fun k => ℓ (a + 1) (qry Ns x k)) c <;> rfl
  · rw [h0]
    have : bt ℓ a c ≤ 1 := bt_le_one ℓ a c
    rw [← hb] at this
    split_ifs <;> omega

/-- The table-rebuilt cover data agree with the true cumulative losses on every interval between breakpoints. -/
theorem agreeOn_Cm (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {a : ℕ} (ha : a + 1 ≤ NE)
    {x : RawT n NE D Lv L M} (hx : Valid Ns x) (hinv : Inv (L := L) (R := R) Bt lev θ η ε ℓ ω a x) :
    Pool.P0068.AgreeOn (E n NE D) (Pool.P0061.cumL (cu ℓ))
      (Cm (tabN Ns x (fun k => ℓ (a + 1) (qry Ns x k))) (U x) a) (U x)
      (Pool.P0068.bp (E n NE D) (a + 1) (U x)) := by
  classical
  have hEa : ∀ d ∈ U x, E n NE D d ≤ a := fun d hd =>
    E_le_of_mem_pr Bt lev θ ℓ ω hD hLv hlev (by rw [← hinv.2.1]; exact hd)
  have key : ∀ i ∈ U x, ∀ u ∈ Pool.P0068.bp (E n NE D) (a + 1) (U x), E n NE D i ≤ u →
      Cm (tabN Ns x (fun k => ℓ (a + 1) (qry Ns x k))) (U x) a i u =
        Pool.P0061.cumL (cu ℓ) i u - Pool.P0061.cumL (cu ℓ) i (a + 1) := by
    intro i hi u hu hiu
    unfold Cm
    by_cases hua : u = a + 1
    · rw [if_pos hua, hua, sub_self]
    · rw [if_neg hua]
      have hex : ∃ d ∈ U x, E n NE D d = u := by
        rcases hu with h | ⟨d, hd, hdu⟩
        · exact absurd h hua
        · exact ⟨d, hd, hdu⟩
      rw [dif_pos hex]
      obtain ⟨hdU, hdE⟩ := hex.choose_spec
      have hD' := tabN_val Bt lev θ η ε Ns ℓ ω hD hLv hlev ha hx hinv hi hdU (by rw [hdE]; exact hiu)
      rw [hD', hdE]
      have hle : u ≤ a + 1 := by have := hEa _ hdU; omega
      have h1 := Pool.P0061.Lint_cumL (cu ℓ) i hle
      unfold Pool.P0030.Lint at h1
      rw [← neg_sub, h1]
      push_cast
      rfl
  intro i hi u hu v hv hiu huv
  unfold Pool.P0030.Lint
  rw [key i hi u hu hiu, key i hi v hv (hiu.trans huv)]
  ring

/-- The machine's merges are P0065's: the pools at boundary `a + 1`. -/
theorem P1Of_eq (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hlevLt : ∀ r a, lev r a < Lt + 1) {a : ℕ} (ha : a + 1 < NE)
    {x : RawT n NE D Lv L M} (hx : Valid Ns x) (hinv : Inv (L := L) (R := R) Bt lev θ η ε ℓ ω a x)
    (z : Jd n NE D Lt K → Bool)
    (hz : ∀ (r : Fin D) (j : Fin (Lt + 1)) (k : Fin K) c,
      z (Sum.inl (r, j, k, c)) = ω (Sum.inr (⟨a, by omega⟩, r, j, k), c)) :
    P1Of (R := R) Bt lev θ Ns x a (fun k => ℓ (a + 1) (qry Ns x k)) z =
      tp (Lv := Lv) (R := R) Bt lev θ ℓ ω (a + 1) := by
  have hP := Pn_eq Bt lev θ ℓ ω hD hLv hlev hinv.1
  funext r
  show (if Bt r ∣ a + 1 then _ else _) = (if Bt r ∣ a + 1 then _ else _)
  by_cases hB : Bt r ∣ a + 1
  · rw [if_pos hB, if_pos hB]
    by_cases hr : r < D
    · rw [show Pn x r = sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a r from funext (hP r)]
      rw [Pool.P0078.mergeUpTo_congrC (E n NE D) (Cm (tabN Ns x (fun k => ℓ (a + 1) (qry Ns x k))) (U x) a)
        (Pool.P0061.cumL (cu ℓ)) θ R K _ a (U x)
        (fun f hf e₁ h₁ e₂ h₂ h₃ h₄ => (agreeOn_Cm Bt lev θ η ε Ns ℓ ω hD hLv hlev ha.le hx hinv f hf e₁ h₁ e₂ h₂ h₃ h₄).symm)
        (lev r a) _ ?_]
      · apply Pool.P0063.mergeUpTo_congr
        intro j hj
        funext k c
        unfold φz
        show _ = Pool.P0082.φC NE D Lt K ω r a j k c
        unfold Pool.P0082.φC
        have hjl : j < Lt + 1 := lt_of_le_of_lt hj (hlevLt r a)
        rw [dif_pos ⟨hr, hjl⟩, dif_pos ⟨by omega, hr, hjl⟩]
        exact hz ⟨r, hr⟩ ⟨j, hjl⟩ k c
      · intro j c hc
        rw [hinv.2.1]
        exact mem_pr_of Bt lev θ ℓ ω hD hLv hlev hc
    · have h1 : ∀ j, Pn x r j = ∅ := fun j => by unfold Pn; rw [dif_neg (fun h => hr h.1)]
      have h2 : ∀ j, sp (Lv := Lv) (R := R) Bt lev θ ℓ ω a r j = ∅ := fun j => by rw [← hP r j, h1 j]
      funext j
      rw [mergeUpTo_empty θ _ _ a _ _ h1, mergeUpTo_empty θ _ _ a _ _ h2]
  · rw [if_neg hB, if_neg hB]
    exact funext (hP r)

/-- The machine's start pools of unit `a + 1` are P0065's. -/
theorem P2Of_eq (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hlevLt : ∀ r a, lev r a < Lt + 1) {a : ℕ} (ha : a + 1 < NE)
    {x : RawT n NE D Lv L M} (hx : Valid Ns x) (hinv : Inv (L := L) (R := R) Bt lev θ η ε ℓ ω a x)
    (z : Jd n NE D Lt K → Bool)
    (hz : ∀ (r : Fin D) (j : Fin (Lt + 1)) (k : Fin K) c,
      z (Sum.inl (r, j, k, c)) = ω (Sum.inr (⟨a, by omega⟩, r, j, k), c))
    (hz' : ∀ c, z (Sum.inr c) = ω (Sum.inl ⟨a + 1, ha⟩, c)) :
    P2Of (R := R) Bt lev θ Ns x a (fun k => ℓ (a + 1) (qry Ns x k)) z =
      sp (Lv := Lv) (R := R) Bt lev θ ℓ ω (a + 1) := by
  unfold P2Of
  rw [P1Of_eq Bt lev θ η ε Ns ℓ ω hD hLv hlev hlevLt ha hx hinv z hz]
  apply startPools_congr
  intro c hc
  unfold ωz
  show _ = Pool.P0082.ωsC (E n NE D) NE D Lt K ω c
  unfold Pool.P0082.ωsC
  rw [dif_pos (by rw [hc]; exact ha), hz' c]
  simp only [hc]

theorem U_newLab {x : RawT n NE D Lv L M} {bt' : Cp n NE D → Bool} {a : ℕ} {k' : Fin (M + 1)}
    {P2 : ℕ → ℕ → Finset (Cp n NE D)} {c : Cp n NE D} :
    (newLab x bt' a k' P2 c).isSome ↔ ∃ (r : Fin D) (j : Fin Lv), c ∈ P2 r j := by
  classical
  unfold newLab
  split_ifs with h <;> simp [h]

theorem mk_newLab {x : RawT n NE D Lv L M} {bt' : Cp n NE D → Bool} {a : ℕ} {k' : Fin (M + 1)}
    {P2 : ℕ → ℕ → Finset (Cp n NE D)} (c : Cp n NE D) (r : Fin D) (j : Fin Lv) :
    Pool.P0121.TM.mk (newLab x bt' a k' P2 c) r j = decide (c ∈ P2 r j) := by
  classical
  unfold newLab Pool.P0121.TM.mk
  split_ifs with h
  · rfl
  · simp only [Bool.false_eq, decide_eq_false_iff_not]
    intro hc; exact h ⟨r, j, hc⟩

theorem ldo_newLab_none {x : RawT n NE D Lv L M} {bt' : Cp n NE D → Bool} {a : ℕ} {k' : Fin (M + 1)}
    {P2 : ℕ → ℕ → Finset (Cp n NE D)} {c : Cp n NE D} (hex : ∃ (r : Fin D) (j : Fin Lv), c ∈ P2 r j)
    (hxc : x.1 c = none) {j : ℕ} (hj : j < L + 1) :
    ldo (newLab x bt' a k' P2 c) j = (0, (k' : ℕ)) := by
  classical
  unfold newLab
  rw [if_pos hex]
  simp [ldo, hj, hxc]

theorem ldo_newLab_some {x : RawT n NE D Lv L M} {bt' : Cp n NE D → Bool} {a : ℕ} {k' : Fin (M + 1)}
    {P2 : ℕ → ℕ → Finset (Cp n NE D)} {c : Cp n NE D} (hex : ∃ (r : Fin D) (j : Fin Lv), c ∈ P2 r j)
    {v : Lb D Lv L M} (hxc : x.1 c = some v) {j : ℕ} (hj : j < L + 1) :
    ldo (newLab x bt' a k' P2 c) j = if ¬ 2 ^ j ∣ a + 1 then
      ((addB (v.2 ⟨j, hj⟩).1 (bt' c) : ℕ), ((v.2 ⟨j, hj⟩).2 : ℕ)) else (0, (k' : ℕ)) := by
  classical
  unfold newLab
  rw [if_pos hex]
  by_cases hd : 2 ^ j ∣ a + 1 <;> simp [ldo, hj, hxc, hd]

theorem ldo_some {v : Lb D Lv L M} {j : ℕ} (hj : j < L + 1) :
    ldo (some v) j = (((v.2 ⟨j, hj⟩).1 : ℕ), ((v.2 ⟨j, hj⟩).2 : ℕ)) := by
  simp [ldo, hj]

/-- **One day of the machine preserves the invariant** (on a good next unit). -/
theorem step_inv (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hlevLt : ∀ r a, lev r a < Lt + 1) (hη : 0 ≤ η) (hε : 0 < ε) (hM : NE * ⌊η / ε⌋₊ ≤ M)
    {a : ℕ} (ha : a + 1 < NE) {x : RawT n NE D Lv L M} (hx : Valid Ns x)
    (hinv : Inv (L := L) (R := R) Bt lev θ η ε ℓ ω a x) (z : Jd n NE D Lt K → Bool)
    (hz : ∀ (r : Fin D) (j : Fin (Lt + 1)) (k : Fin K) c,
      z (Sum.inl (r, j, k, c)) = ω (Sum.inr (⟨a, by omega⟩, r, j, k), c))
    (hz' : ∀ c, z (Sum.inr c) = ω (Sum.inl ⟨a + 1, ha⟩, c))
    (hg : Good (Lv := Lv) (R := R) Bt lev θ Ns ℓ ω (a + 1)) :
    Valid Ns (stepRaw (R := R) Bt lev θ η ε Ns x a (fun k => ℓ (a + 1) (qry Ns x k)) z) ∧
      Inv (L := L) (R := R) Bt lev θ η ε ℓ ω (a + 1)
        (stepRaw (R := R) Bt lev θ η ε Ns x a (fun k => ℓ (a + 1) (qry Ns x k)) z) := by
  classical
  set o : Fin Ns → Bool := fun k => ℓ (a + 1) (qry Ns x k) with ho
  have hP2 := P2Of_eq Bt lev θ η ε Ns ℓ ω hD hLv hlev hlevLt ha hx hinv z hz hz'
  have hk := kNew_val Bt lev θ η ε Ns ℓ ω hη hε hM ha.le hx hinv
  set y := stepRaw (R := R) Bt lev θ η ε Ns x a o z with hy
  have hlab : ∀ c, y.1 c = newLab x (bitOf Ns x o) a (kNew η ε Ns x o)
      (sp (Lv := Lv) (R := R) Bt lev θ ℓ ω (a + 1)) c := by
    intro c; show newLab _ _ _ _ (P2Of (R := R) Bt lev θ Ns x a o z) c = _; rw [hP2]
  have hUy : U y = pr (Lv := Lv) (R := R) Bt lev θ ℓ ω (a + 1) := by
    ext c
    rw [mem_U, hlab, U_newLab, mem_pr]
  have hUx := hinv.2.1
  -- learner data
  have hld : ∀ c ∈ U y, ∀ j < L + 1, ld y c j = (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω (a + 1)).2 c j := by
    intro c hc j hj
    have hcp : c ∈ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω (a + 1) := by rw [← hUy]; exact hc
    have hex : ∃ (r : Fin D) (j : Fin Lv), c ∈ sp (Lv := Lv) (R := R) Bt lev θ ℓ ω (a + 1) r j :=
      (mem_pr Bt lev θ ℓ ω).1 hcp
    have hidl : (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω (a + 1)).2 c j =
        if c ∈ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a ∧ ¬ 2 ^ j ∣ a + 1 then
          (((idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω a).2 c j).1 + bt ℓ a c,
            ((idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω a).2 c j).2)
        else (0, (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω (a + 1)).1) := rfl
    have hlt : ((idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω (a + 1)).2 c j).1 < 2 ^ j :=
      Pool.P0121.TMI.ideal_C_lt L (pr (Lv := Lv) (R := R) Bt lev θ ℓ ω) (bt ℓ) η ε (bt_le_one ℓ) (a + 1) c hcp j
    unfold ld
    rw [hlab c, hidl]
    rcases hxc : x.1 c with _ | v0
    · have hcx : c ∉ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a := by
        rw [← hUx, not_mem_U]; exact hxc
      rw [ldo_newLab_none hex hxc hj, if_neg (fun h => hcx h.1), hk]
    · have hcU : c ∈ U x := by rw [mem_U, hxc]; rfl
      have hcpa : c ∈ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a := by rw [← hUx]; exact hcU
      have hold := hinv.2.2.2.2 c hcU j hj
      unfold ld at hold
      rw [hxc, ldo_some hj] at hold
      rw [ldo_newLab_some hex hxc hj]
      by_cases hdv : 2 ^ j ∣ a + 1
      · rw [if_neg (fun h => h hdv), if_neg (fun h => h.2 hdv), hk]
      · rw [if_pos hdv, if_pos ⟨hcpa, hdv⟩, ← hold]
        have hb := toNat_eq_bt (ℓ := ℓ) Ns hx (a := a) hcU
        rw [hidl, if_pos ⟨hcpa, hdv⟩, ← hold] at hlt
        simp only at hlt
        have hpow : 2 ^ j ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [Prod.mk.injEq]
        refine ⟨?_, rfl⟩
        rw [Pool.P0078.addB_val, ← hb]
        · cases bitOf Ns x o c <;> rfl
        · rw [← hb] at hlt
          have : (if bitOf Ns x o c = true then 1 else 0) = (bitOf Ns x o c).toNat := by
            cases bitOf Ns x o c <;> rfl
          rw [this]; exact le_of_lt (lt_of_lt_of_le hlt hpow)
  refine ⟨⟨by rw [hUy]; exact hg, fun c d hcd => ?_⟩, ?_, hUy, ?_, ?_, hld⟩
  · show (if _ then _ else _ : Fin (NE + 1)) = 0
    rw [if_neg]
    rintro ⟨h1, h2, -, -⟩
    rcases hcd with h | h
    · exact h (mem_U.2 h1)
    · exact h (mem_U.2 h2)
  · intro r j c
    rw [hlab c]
    exact mk_newLab c r j
  · intro c hc d hd hcd
    show ((if _ then _ else _ : Fin (NE + 1)) : ℕ) = _
    have hcs : (y.1 c).isSome := (mem_U).1 hc
    have hds : (y.1 d).isSome := (mem_U).1 hd
    have hcp : c ∈ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω (a + 1) := by rw [← hUy]; exact hc
    have hdp : d ∈ pr (Lv := Lv) (R := R) Bt lev θ ℓ ω (a + 1) := by rw [← hUy]; exact hd
    by_cases hdx : d ∈ U x
    · have hcx : c ∈ U x := by
        by_contra hcx
        have h1 := E_of_new Bt lev θ ℓ ω hD hLv hlev hcp (by rw [← hUx]; exact hcx)
        have h2 := E_le_of_mem_pr Bt lev θ ℓ ω hD hLv hlev (by rw [← hUx]; exact hdx)
        omega
      rw [if_pos ⟨hcs, hds, hcx, hdx⟩]
      exact tabN_val Bt lev θ η ε Ns ℓ ω hD hLv hlev ha.le hx hinv hcx hdx hcd
    · rw [if_neg (fun h => hdx h.2.2.2)]
      have := E_of_new Bt lev θ ℓ ω hD hLv hlev hdp (by rw [← hUx]; exact hdx)
      rw [this]; simp
  · show (kNew η ε Ns x o : ℕ) = _
    exact hk

theorem init_inv (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (hNE : 0 < NE)
    (z : Jd n NE D Lt K → Bool) (hz' : ∀ c, z (Sum.inr c) = ω (Sum.inl ⟨0, hNE⟩, c))
    (hg : Good (Lv := Lv) (R := R) Bt lev θ Ns ℓ ω 0) :
    Valid Ns (initRaw (Lv := Lv) (L := L) (M := M) Bt z) ∧
      Inv (L := L) (R := R) Bt lev θ η ε ℓ ω 0 (initRaw (Lv := Lv) (L := L) (M := M) Bt z) := by
  classical
  have hP2 : startPools (E n NE D) (thr0 n NE D) D Lv Bt (ωz z) 0 (fun _ _ => ∅) =
      sp (Lv := Lv) (R := R) Bt lev θ ℓ ω 0 := by
    apply startPools_congr
    intro c hc
    unfold ωz
    show _ = Pool.P0082.ωsC (E n NE D) NE D Lt K ω c
    unfold Pool.P0082.ωsC
    rw [dif_pos (by rw [hc]; exact hNE), hz' c]
    simp only [hc]
  set x := initRaw (Lv := Lv) (L := L) (M := M) Bt z with hx
  have hlab : ∀ c, x.1 c = if ∃ (r : Fin D) (j : Fin Lv), c ∈ sp (Lv := Lv) (R := R) Bt lev θ ℓ ω 0 r j then
      (some (fun (r : Fin D) (j : Fin Lv) => decide (c ∈ sp (Lv := Lv) (R := R) Bt lev θ ℓ ω 0 r j),
        fun _ => ((0 : Fin (2 ^ L + 1)), (0 : Fin (M + 1)))) : Option (Lb D Lv L M)) else none := by
    intro c; rw [← hP2]; rfl
  have hU : U x = pr (Lv := Lv) (R := R) Bt lev θ ℓ ω 0 := by
    ext c; rw [mem_U, hlab, mem_pr]; split_ifs with h <;> simp [h]
  refine ⟨⟨by rw [hU]; exact hg, fun _ _ _ => rfl⟩, ?_, hU, ?_, rfl, ?_⟩
  · intro r j c
    rw [hlab c]
    unfold Pool.P0121.TM.mk
    split_ifs with h
    · rfl
    · simp only [Bool.false_eq, decide_eq_false_iff_not]
      intro hc; exact h ⟨r, j, hc⟩
  · intro c _ d _ _
    simp [x, initRaw]
  · intro c hc j hj
    have hex : ∃ (r : Fin D) (j : Fin Lv), c ∈ sp (Lv := Lv) (R := R) Bt lev θ ℓ ω 0 r j := by
      rw [← mem_pr, ← hU]; exact hc
    unfold ld
    rw [hlab c, if_pos hex, ldo_some hj]
    rfl

/-- The coin array read off the machine's day coins: sampling bits of unit `a` on day `a`, filter bits of the merges
ending unit `a` on day `a + 1`. -/
def Φ (zf : ℕ → Jd n NE D Lt K → Bool) : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool
  | (Sum.inl a, c) => zf a (Sum.inr c)
  | (Sum.inr (a, r, j, k), c) => zf (a + 1) (Sum.inl (r, j, k, c))

end Step

section Run

variable (ℓ : LossSeq n) {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)

/-- **The machine runs P0065's threaded process on good runs.** At day `a + 1` (unit `a < NE`), if every unit
`≤ a` is good for the coin array `Φ zf`, the state is the start pools of unit `a` with the true in-lifetime tables
and the ideal learner data. -/
theorem run_inv (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hlevLt : ∀ r a, lev r a < Lt + 1) (hη : 0 ≤ η) (hε : 0 < ε) (hM : NE * ⌊η / ε⌋₊ ≤ M)
    (zf : ℕ → Jd n NE D Lt K → Bool) :
    ∀ a, a < NE → (∀ a' ≤ a, Good (Lv := Lv) (R := R) Bt lev θ Ns ℓ (Φ zf) a') →
      Inv (L := L) (R := R) Bt lev θ η ε ℓ (Φ zf) a
        ((tmach (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE) (D := D) Bt lev θ η ε Ns
          hps hq).runFin ℓ (a + 1) (fun i => zf i)).1 := by
  intro a
  induction a with
  | zero =>
    intro hNE hg
    have h0 := init_inv Bt lev θ η ε Ns ℓ (Φ zf) (L := L) (M := M) hD hLv hlev hNE (zf 0) (fun c => rfl)
      (hg 0 le_rfl)
    have hr : ((tmach (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE) (D := D) Bt lev θ η ε Ns
        hps hq).runFin ℓ (0 + 1) (fun i => zf i)).1 = initRaw (Lv := Lv) (L := L) (M := M) Bt (zf 0) := by
      show (validate Ns (initRaw (Lv := Lv) (L := L) (M := M) Bt (zf 0))).1 = _
      unfold validate; rw [dif_pos h0.1]
    rw [hr]; exact h0.2
  | succ a ih =>
    intro ha hg
    set s := (tmach (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE) (D := D) Bt lev θ η ε Ns
      hps hq).runFin ℓ (a + 1) (fun i => zf i) with hs
    have hinv := ih (by omega) (fun a' h => hg a' (by omega))
    have hst := step_inv Bt lev θ η ε Ns ℓ (Φ zf) hD hLv hlev hlevLt hη hε hM ha s.2 hinv (zf (a + 1))
      (fun r j k c => rfl) (fun c => rfl) (hg (a + 1) le_rfl)
    have hr : ((tmach (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE) (D := D) Bt lev θ η ε Ns
        hps hq).runFin ℓ (a + 1 + 1) (fun i => zf i)).1 =
        stepRaw (R := R) Bt lev θ η ε Ns s.1 a (fun k => ℓ (a + 1) (qry Ns s.1 k)) (zf (a + 1)) := by
      show (if a + 1 = 0 then validate Ns (initRaw (Lv := Lv) (L := L) (M := M) Bt (zf (a + 1)))
        else validate Ns (stepRaw (R := R) Bt lev θ η ε Ns s.1 (a + 1 - 1) (fun k => ℓ (a + 1) (qry Ns s.1 k))
          (zf (a + 1)))).1 = _
      rw [if_neg (Nat.succ_ne_zero a)]
      show (validate Ns (stepRaw (R := R) Bt lev θ η ε Ns s.1 a (fun k => ℓ (a + 1) (qry Ns s.1 k))
          (zf (a + 1)))).1 = _
      unfold validate; rw [dif_pos hst.1]
    rw [hr]; exact hst.2

end Run


end Pool.P0121.TMRun
