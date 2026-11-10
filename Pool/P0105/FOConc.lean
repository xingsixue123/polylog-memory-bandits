import Pool.P0095.FOProc
import Pool.P0092.Azuma
import Pool.P0074.Cert


/-!
# Concentration of slot-IW estimates, and certificates for the one-free-observation threaded process

**Generic part.** A process observes, in unit `u`, the occupant of a uniformly drawn slot `ω u ∈ Fin s` of a slot
layout `ocf u h` of a set `Vf u h` of copies (both may depend on the earlier draws `h`); the observed copy's estimate
grows by `s · L u x`. `errIncr` is the estimation error of unit `u` for a weighting `w` of the copies (observed
increment minus the true losses of the present copies), set to `0` when `|Vf| > s` (overflow). It has conditional
mean `0` (`errIncr_mean`) and range `s + 1` (`errIncr_bd`), so P0092's Azuma bound applies (`errIncr_conc`).

**FO instance.** For P0095's threaded process `foRun`: causality in the slot draws (`foRun_congr_y`), the accumulated
error equals the realized estimate increments minus the true losses on every slot sequence without overflow
(`runSum_foErr_eq`), and the interval form for one copy (`fo_interval_conc`).

**Certificates.** `fo_cert` is P0074's `thread_cert_interval` for this process: in the all-slots forced copy-last run
(`forceS`, `forceF`, `occLast c`), the learner's loss over the forced copy's lifetime is within `θ + Rα + β·len` of the
copy's OWN realized estimate, if the learner is within `α + β·len` of every present copy's realized estimate in the
actual run (`occSort`). `fo_cert_conc` adds the concentration of that one estimate: outside a slot event of weight
`≤ 2 exp (-x²/(4(s+1)²T))`, the learner is within `x + θ + Rα + β·len` of the copy's TRUE loss, on every slot
sequence without overflow.

Not done here: the probability of overflow (pool sizes with adapted data), the in-law transfer between `occSort` and
`occLast c` (needs a cap), the clock-slot forced run used for counting, the learner, the machine.
-/

namespace Pool.P0105

open Finset

/-- Sum over the slots of a list laid out in the first slots. -/
theorem sum_slots_list {α : Type*} [DecidableEq α] (s : ℕ) (Lst : List α) (hnd : Lst.Nodup) (hlen : Lst.length ≤ s)
    (g : Option α → ℝ) (hg : g none = 0) :
    ∑ y : Fin s, g (if h : y.1 < Lst.length then some Lst[y.1] else none) = ∑ z ∈ Lst.toFinset, g (some z) := by
  rw [List.sum_toFinset _ hnd]
  have h1 : ∑ y : Fin s, g (if h : y.1 < Lst.length then some Lst[y.1] else none) =
      ∑ i ∈ range s, (if h : i < Lst.length then g (some Lst[i]) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> simp [hg]
  rw [h1]
  have h2 : ∑ i ∈ range s, (if h : i < Lst.length then g (some Lst[i]) else 0) =
      ∑ i ∈ range Lst.length, (if h : i < Lst.length then g (some Lst[i]) else 0) := by
    symm
    apply Finset.sum_subset (Finset.range_subset_range.mpr hlen)
    intro i _ hi
    simp only [Finset.mem_range] at hi
    simp [hi]
  rw [h2, ← Fin.sum_univ_eq_sum_range (fun i => if h : i < Lst.length then g (some Lst[i]) else 0)]
  simp only [Fin.is_lt, dite_true]
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem <;> simp

end Pool.P0105

namespace Pool.P0105
open Finset Pool.P0095 Pool.P0065

/-- An occupancy rule lays out every member set of size `≤ s` in distinct slots. -/
def SlotSum {ι : Type*} [DecidableEq ι] (s : ℕ) (occ : Finset ι → Fin s → Option ι) : Prop :=
  ∀ V : Finset ι, V.card ≤ s → ∀ g : Option ι → ℝ, g none = 0 →
    ∑ y : Fin s, g (occ V y) = ∑ z ∈ V, g (some z)

theorem slotSum_occSort {ι : Type*} [LinearOrder ι] (s : ℕ) : SlotSum s (occSort (ι := ι) s) := by
  intro V hV g hg
  unfold occSort
  rw [sum_slots_list s _ (Finset.sort_nodup _ _) (by rw [Finset.length_sort]; exact hV) g hg,
    Finset.sort_toFinset]

/-- The copy-last list: the members other than `c` in sorted order, then `c` if present. -/
def lastList {ι : Type*} [LinearOrder ι] (c : ι) (V : Finset ι) : List ι :=
  (V.erase c).sort (· ≤ ·) ++ (if c ∈ V then [c] else [])

theorem occLast_eq_lastList {ι : Type*} [LinearOrder ι] (s : ℕ) (c : ι) (V : Finset ι) (y : Fin s) :
    occLast s c V y = if h : y.1 < (lastList c V).length then some (lastList c V)[y.1] else none := by
  set Lst := (V.erase c).sort (· ≤ ·) with hL
  unfold occLast
  rw [← hL]
  by_cases h1 : y.1 < Lst.length
  · have h1' : y.1 < (lastList c V).length := by simp only [lastList, ← hL, List.length_append]; omega
    rw [dif_pos h1, dif_pos h1']
    simp only [lastList, ← hL, List.getElem_append_left h1]
  · rw [dif_neg h1]
    by_cases hc : c ∈ V
    · by_cases h2 : y.1 = Lst.length
      · have h1' : y.1 < (lastList c V).length := by
          simp only [lastList, ← hL, if_pos hc, List.length_append, List.length_singleton]; omega
        rw [if_pos ⟨h2, hc⟩, dif_pos h1']
        simp only [lastList, ← hL, hc, if_true, List.getElem_append_right (by omega : Lst.length ≤ y.1)]
        simp [h2]
      · have h1' : ¬ y.1 < (lastList c V).length := by
          simp only [lastList, ← hL, if_pos hc, List.length_append, List.length_singleton]; omega
        rw [if_neg (fun h => h2 h.1), dif_neg h1']
    · have h1' : ¬ y.1 < (lastList c V).length := by
        simp only [lastList, ← hL, if_neg hc, List.append_nil]; exact h1
      rw [if_neg (fun h => hc h.2), dif_neg h1']

theorem lastList_nodup {ι : Type*} [LinearOrder ι] (c : ι) (V : Finset ι) : (lastList c V).Nodup := by
  unfold lastList
  split_ifs with hc
  · rw [List.nodup_append]
    refine ⟨Finset.sort_nodup _ _, List.nodup_singleton c, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    rw [Finset.mem_sort] at ha
    exact fun h => Finset.notMem_erase a V (h ▸ ha)
  · simp

theorem lastList_length {ι : Type*} [LinearOrder ι] (c : ι) (V : Finset ι) : (lastList c V).length = V.card := by
  simp only [lastList, List.length_append, Finset.length_sort]
  split_ifs with hc
  · rw [Finset.card_erase_of_mem hc]; simp; have := Finset.card_pos.mpr ⟨c, hc⟩; omega
  · rw [Finset.erase_eq_of_notMem hc]; simp

theorem lastList_toFinset {ι : Type*} [LinearOrder ι] (c : ι) (V : Finset ι) : (lastList c V).toFinset = V := by
  ext z
  simp only [lastList, List.toFinset_append, Finset.mem_union, List.mem_toFinset, Finset.mem_sort,
    Finset.mem_erase]
  split_ifs with hc
  · simp only [List.mem_singleton]
    constructor
    · rintro (⟨-, h⟩ | rfl) <;> assumption
    · intro hz; by_cases hzc : z = c
      · exact Or.inr hzc
      · exact Or.inl ⟨hzc, hz⟩
  · simp only [List.not_mem_nil, or_false]
    constructor
    · exact fun h => h.2
    · intro hz; exact ⟨fun h => hc (h ▸ hz), hz⟩

theorem slotSum_occLast {ι : Type*} [LinearOrder ι] (s : ℕ) (c : ι) : SlotSum s (occLast (ι := ι) s c) := by
  intro V hV g hg
  simp only [occLast_eq_lastList]
  rw [sum_slots_list s _ (lastList_nodup c V) (by rw [lastList_length]; exact hV) g hg, lastList_toFinset]

end Pool.P0105

namespace Pool.P0105
open Finset

/-! ### Generic slot-IW estimation errors

A process observes, in unit `u`, the occupant of a uniformly drawn slot `ω u ∈ Fin s` of a slot layout
`ocf u h : Fin s → Option ι` of a set `Vf u h` of copies; both may depend on the earlier draws `h : Fin u → Fin s`.
The observed copy's estimate grows by `s · L u x`. -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (L : ℕ → ι → ℝ)
  (Vf : (u : ℕ) → (Fin u → Fin s) → Finset ι) (ocf : (u : ℕ) → (Fin u → Fin s) → Fin s → Option ι)

/-- The layout puts every set of size `≤ s` into distinct slots. -/
def SlotLayout : Prop :=
  ∀ u h, (Vf u h).card ≤ s → ∀ g : Option ι → ℝ, g none = 0 →
    ∑ y : Fin s, g (ocf u h y) = ∑ z ∈ Vf u h, g (some z)

omit [Fintype ι] in
/-- A duplicate-free list read with `getElem?` is a slot layout of its elements. -/
theorem sum_slots_getElem? (Lst : List ι) (hnd : Lst.Nodup) (hlen : Lst.length ≤ s)
    (g : Option ι → ℝ) (hg : g none = 0) :
    ∑ y : Fin s, g Lst[(y : ℕ)]? = ∑ z ∈ Lst.toFinset, g (some z) := by
  rw [← sum_slots_list s Lst hnd hlen g hg]
  refine Finset.sum_congr rfl fun y _ => ?_
  congr 1
  split_ifs with h
  · exact List.getElem?_eq_getElem h
  · exact List.getElem?_eq_none (by omega)

/-- **The estimation-error increment of unit `u`** for a weighting `w u x` of the copies: the observed IW
increment minus its conditional mean (the true loss of every present copy), gated by `|Vf| ≤ s`. -/
noncomputable def errIncr (w : ℕ → ι → ℝ) (u : ℕ) (ω : Fin (u + 1) → Fin s) : ℝ :=
  if (Vf u (Fin.init ω)).card ≤ s then
    ∑ x, w u x * ((if ocf u (Fin.init ω) (ω (Fin.last u)) = some x then (s : ℝ) * L u x else 0) -
      (if x ∈ Vf u (Fin.init ω) then L u x else 0))
  else 0

/-- Conditional mean `0` under uniform slots. -/
theorem errIncr_mean [NeZero s] (hocc : SlotLayout s Vf ocf) (w : ℕ → ι → ℝ) (u : ℕ) (ω : Fin u → Fin s) :
    ∑ z : Fin s, (1 / (s : ℝ)) * errIncr s L Vf ocf w u (Fin.snoc ω z) = 0 := by
  unfold errIncr
  simp only [Fin.init_snoc, Fin.snoc_last]
  by_cases hc : (Vf u ω).card ≤ s
  · simp only [if_pos hc]
    have hs : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne s)
    rw [← Finset.mul_sum, Finset.sum_comm]
    have : ∀ x, ∑ z : Fin s, w u x * ((if ocf u ω z = some x then (s : ℝ) * L u x else 0) -
        (if x ∈ Vf u ω then L u x else 0)) = 0 := by
      intro x
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      rw [hocc u ω hc (fun o => if o = some x then (s : ℝ) * L u x else 0) (by simp)]
      simp only [Option.some.injEq, Finset.sum_ite_eq', Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun x _ => this x, Finset.sum_const_zero, mul_zero]
  · simp [if_neg hc]

/-- Bounded by `s + 1` when `|L| ≤ 1` and `∑ₓ |w u x| ≤ 1`. -/
theorem errIncr_bd (hL : ∀ u x, |L u x| ≤ 1) (w : ℕ → ι → ℝ) (hw : ∀ u, ∑ x, |w u x| ≤ 1) (u : ℕ)
    (ω : Fin (u + 1) → Fin s) : |errIncr s L Vf ocf w u ω| ≤ s + 1 := by
  unfold errIncr
  split_ifs
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ x, |w u x * ((if ocf u (Fin.init ω) (ω (Fin.last u)) = some x then (s : ℝ) * L u x else 0) -
        (if x ∈ Vf u (Fin.init ω) then L u x else 0))| ≤ |w u x| * (s + 1) := by
      intro x
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) (abs_nonneg _)
      have h1 : |(if ocf u (Fin.init ω) (ω (Fin.last u)) = some x then (s : ℝ) * L u x else 0)| ≤ s := by
        split_ifs
        · rw [abs_mul, Nat.abs_cast]
          exact mul_le_of_le_one_right (Nat.cast_nonneg s) (hL u x)
        · simp
      have h2 : |(if x ∈ Vf u (Fin.init ω) then L u x else 0)| ≤ 1 := by
        split_ifs
        · exact hL u x
        · simp
      linarith
    refine (Finset.sum_le_sum fun x _ => hterm x).trans ?_
    rw [← Finset.sum_mul]
    have := hw u
    have hs : (0 : ℝ) ≤ s + 1 := by positivity
    nlinarith
  · simp; positivity

/-- **Concentration of slot-IW estimation errors.** Under i.i.d. uniform slots, for any fixed weighting `w` with
`∑ₓ |w u x| ≤ 1` and losses `|L| ≤ 1`: `P(|∑_{u<T} errIncr| ≥ x) ≤ 2 exp (-x²/(4(s+1)²T))` for
`0 ≤ x ≤ 2(s+1)T`. -/
theorem errIncr_conc [NeZero s] (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s) (hocc : SlotLayout s Vf ocf)
    (hL : ∀ u x, |L u x| ≤ 1) (w : ℕ → ι → ℝ) (hw : ∀ u, ∑ x, |w u x| ≤ 1)
    {T : ℕ} (hT : 0 < T) {x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ 2 * (s + 1) * T) :
    Pool.P0092.probAbsGe ν T (Pool.P0092.runSum (errIncr s L Vf ocf w) T) x ≤
      2 * Real.exp (-(x ^ 2) / (4 * ((s : ℝ) + 1) ^ 2 * T)) :=
  Pool.P0092.azuma_coins_abs ν (errIncr s L Vf ocf w) (by positivity) (errIncr_bd s L Vf ocf hL w hw)
    (fun u ω => by simp only [hν]; exact errIncr_mean s L Vf ocf hocc w u ω) hT hx0 hxT

end Generic

end Pool.P0105

namespace Pool.P0105
open Finset Pool.P0095 Pool.P0065

section Conc

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ)
  (occ : Finset ι → Fin s → Option ι) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

/-- **Causality in the slot coins.** The state at boundary `a` reads only the slots of units `< a`. -/
theorem foRun_congr_y {y y' : ℕ → Fin s} : ∀ a, (∀ v < a, y v = y' v) →
    foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y a = foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y' a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have ih' := ih (fun v hv => h v (by omega))
    simp only [foRun]
    rw [ih', h a (Nat.lt_succ_self a)]

/-- The members of the start pools in unit `u` (the copies that can be observed in unit `u`). -/
noncomputable def Vat (y : ℕ → Fin s) (u : ℕ) : Finset ι :=
  members D Lv (startPools E thr0 D Lv Bt ωs u (foRun E thr0 θ R K D Lv Bt lev s L occ ωs φ y u).pools)

theorem Vat_congr_y {y y' : ℕ → Fin s} (u : ℕ) (h : ∀ v < u, y v = y' v) :
    Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ y u = Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ y' u := by
  unfold Vat; rw [foRun_congr_y E thr0 θ R K D Lv Bt lev s L occ ωs φ u h]

theorem Chat_congr_y {y y' : ℕ → Fin s} (x : ι) (t : ℕ) (h : ∀ v < t, y v = y' v) :
    Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y x t = Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ y' x t := by
  unfold Chat; rw [foRun_congr_y E thr0 θ R K D Lv Bt lev s L occ ωs φ t h]

theorem obsAt_eq (y : ℕ → Fin s) (u : ℕ) :
    obsAt E thr0 θ R K D Lv Bt lev s L occ ωs φ y u = occ (Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ y u) (y u) :=
  rfl

/-- Extension of a finite slot sequence to all units (slot `0` after it). -/
def extY [NeZero s] {t : ℕ} (ω : Fin t → Fin s) : ℕ → Fin s := fun u => if h : u < t then ω ⟨u, h⟩ else 0

theorem extY_snoc [NeZero s] {u : ℕ} (ω : Fin u → Fin s) (z : Fin s) : ∀ v < u, extY s (Fin.snoc ω z) v = extY s ω v := by
  intro v hv
  simp only [extY, dif_pos hv, dif_pos (show v < u + 1 by omega)]
  exact Fin.snoc_castSucc (α := fun _ => Fin s) (p := ω) (x := z) (i := ⟨v, hv⟩)

theorem extY_init [NeZero s] {u : ℕ} (ω : Fin (u + 1) → Fin s) : ∀ v < u, extY s (Fin.init ω) v = extY s ω v := by
  intro v hv
  simp only [extY, dif_pos hv, dif_pos (show v < u + 1 by omega)]
  rfl

theorem extY_last [NeZero s] {u : ℕ} (ω : Fin (u + 1) → Fin s) : extY s ω u = ω (Fin.last u) := by
  simp [extY, Fin.last]

/-- The FO process as a generic slot process: the start-pool members of unit `u` and their layout `occ`. -/
noncomputable def foV [NeZero s] (u : ℕ) (h : Fin u → Fin s) : Finset ι :=
  Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s h) u

theorem slotLayout_fo [NeZero s] (hocc : SlotSum s occ) :
    SlotLayout s (foV E thr0 θ R K D Lv Bt lev s L occ ωs φ)
      (fun u h => occ (foV E thr0 θ R K D Lv Bt lev s L occ ωs φ u h)) :=
  fun _ _ hc g hg => hocc _ hc g hg

/-- The estimation-error increments of the FO process. -/
noncomputable abbrev foErr [NeZero s] (w : ℕ → ι → ℝ) : (u : ℕ) → (Fin (u + 1) → Fin s) → ℝ :=
  errIncr s L (foV E thr0 θ R K D Lv Bt lev s L occ ωs φ)
    (fun u h => occ (foV E thr0 θ R K D Lv Bt lev s L occ ωs φ u h)) w

/-- **Identification of the accumulated error.** On slot sequences along which every start-pool member set fits
in the `s` slots, the accumulated FO error is the weighted estimation error: realized estimate increments
`Ĉ x (u+1) - Ĉ x u` minus the true losses of the present copies. -/
theorem runSum_foErr_eq [NeZero s] (w : ℕ → ι → ℝ) : ∀ (T : ℕ) (ω : Fin T → Fin s),
    (∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) u).card ≤ s) →
    Pool.P0092.runSum (foErr E thr0 θ R K D Lv Bt lev s L occ ωs φ w) T ω =
      ∑ u ∈ range T, ∑ x, w u x *
        ((Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) x (u + 1) -
          Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) x u) -
          (if x ∈ Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) u then L u x else 0)) := by
  intro T
  induction T with
  | zero => intro _ _; rfl
  | succ T ih =>
    intro ω hcard
    have hV : ∀ u ≤ T, Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s (Fin.init ω)) u =
        Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) u := fun u hu =>
      Vat_congr_y E thr0 θ R K D Lv Bt lev s L occ ωs φ u (fun v hv => extY_init s ω v (by omega))
    have hCh : ∀ x, ∀ t ≤ T, Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s (Fin.init ω)) x t =
        Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) x t := fun x t ht =>
      Chat_congr_y E thr0 θ R K D Lv Bt lev s L occ ωs φ x t (fun v hv => extY_init s ω v (by omega))
    show Pool.P0092.runSum _ T (Fin.init ω) + foErr E thr0 θ R K D Lv Bt lev s L occ ωs φ w T ω = _
    rw [ih (Fin.init ω) (fun u hu => by rw [hV u hu.le]; exact hcard u (by omega)), Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.mem_range] at hu
      simp only [hV u hu.le, hCh _ (u + 1) (by omega), hCh _ u (by omega)]
    · have hfv : foV E thr0 θ R K D Lv Bt lev s L occ ωs φ T (Fin.init ω) =
          Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) T := hV T le_rfl
      simp only [foErr, errIncr, hfv]
      rw [if_pos (hcard T (by omega))]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Chat_succ, obsAt_eq, extY_last]
      ring
/-- The weighting that selects copy `c` on the units `[a, b)`. -/
def wIv (c : ι) (a b : ℕ) (u : ℕ) (x : ι) : ℝ := if x = c ∧ a ≤ u ∧ u < b then 1 else 0

theorem wIv_abs (c : ι) (a b u : ℕ) : ∑ x, |wIv c a b u x| ≤ 1 := by
  unfold wIv
  have : ∀ x, |(if x = c ∧ a ≤ u ∧ u < b then (1 : ℝ) else 0)| = if x = c then (if a ≤ u ∧ u < b then 1 else 0) else 0 := by
    intro x; by_cases hx : x = c <;> by_cases hu : a ≤ u ∧ u < b <;> simp [hx, hu]
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> norm_num

theorem sum_wIv (c : ι) {a b T : ℕ} (hbT : b ≤ T) (F : ℕ → ι → ℝ) :
    ∑ u ∈ range T, ∑ x, wIv c a b u x * F u x = ∑ u ∈ Ico a b, F u c := by
  have h1 : ∀ u, ∑ x, wIv c a b u x * F u x = if a ≤ u ∧ u < b then F u c else 0 := by
    intro u
    unfold wIv
    have : ∀ x, (if x = c ∧ a ≤ u ∧ u < b then (1 : ℝ) else 0) * F u x =
        if x = c then (if a ≤ u ∧ u < b then F u x else 0) else 0 := by
      intro x; by_cases hx : x = c <;> by_cases hu : a ≤ u ∧ u < b <;> simp [hx, hu]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [h1]
  rw [← Finset.sum_filter]
  congr 1
  ext u; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega

/-- **Interval concentration for one copy.** For a copy `c` and units `[a, b)` with `b ≤ T`: the weight of the slot
sequences along which every start-pool member set fits in the `s` slots and `c`'s realized estimate over `[a, b)`
deviates by `≥ x` from `c`'s true loss over the units of `[a, b)` in which it is present is
`≤ 2 exp (-x²/(4(s+1)²T))`. -/
theorem fo_interval_conc [NeZero s] (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s) (hocc : SlotSum s occ)
    (hL : ∀ u x, |L u x| ≤ 1) (c : ι) {a b T : ℕ} (hab : a ≤ b) (hbT : b ≤ T) (hT : 0 < T)
    {x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ 2 * (s + 1) * T) :
    ∑ ω : Fin T → Fin s, Pool.P0092.wgt ν ω *
      (if (∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) u).card ≤ s) ∧
          x ≤ |(Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) c b -
              Chat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) c a) -
            ∑ u ∈ Ico a b, (if c ∈ Vat E thr0 θ R K D Lv Bt lev s L occ ωs φ (extY s ω) u then L u c else 0)|
        then 1 else 0) ≤
      2 * Real.exp (-(x ^ 2) / (4 * ((s : ℝ) + 1) ^ 2 * T)) := by
  refine le_trans ?_ (errIncr_conc s L _ _ ν hν (slotLayout_fo E thr0 θ R K D Lv Bt lev s L occ ωs φ hocc) hL
    (wIv c a b) (wIv_abs c a b) hT hx0 hxT)
  unfold Pool.P0092.probAbsGe
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (Pool.P0092.wgt_nonneg ν ω)
  split_ifs with h1 h2
  · exact le_rfl
  · exfalso; apply h2
    rw [runSum_foErr_eq E thr0 θ R K D Lv Bt lev s L occ ωs φ (wIv c a b) T ω h1.1, sum_wIv c hbT,
      Finset.sum_sub_distrib, Finset.sum_Ico_sub _ hab]
    exact h1.2
  · norm_num
  · exact le_rfl

end Conc

end Pool.P0105

namespace Pool.P0105

section Cert

open Pool.P0065 Pool.P0052 Pool.P0042 Pool.P0034 Pool.P0030 Pool.P0095

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {E thr0 : ι → ℕ} {θ : ℝ}
  {R K D Lv : ℕ} {Bt : ℕ → ℕ} {lev : ℕ → ℕ → ℕ}

/-- P0074's certificate with each run's own per-unit data. -/
theorem thread_cert_interval_own (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (cuF cuA : ℕ → ι → ℝ) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} (hc : ωs c = false)
    (hag : ∀ x, x ≠ c → ∀ u, cuF u x = cuA u x)
    {x : ℕ} (hx : E c ≤ x)
    (hin : SAlive E thr0 (Pool.P0061.cumL cuF) θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) x c)
    (hout : ¬ Alive E thr0 (Pool.P0061.cumL cuF) θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c)
      (x + 1) c)
    (A : ℕ → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : ∀ f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (tpools E thr0 (Pool.P0061.cumL cuA) θ R K D Lv Bt lev ωs φ u) r ℓ) →
      ∑ u ∈ Finset.Ico s s', A u ≤ ∑ u ∈ Finset.Ico s s', cuA u f + α + β * ((s' - s : ℕ) : ℝ)) :
    ∑ u ∈ Finset.Ico (E c) (x + 1), A u ≤
      ∑ u ∈ Finset.Ico (E c) (x + 1), cuF u c + θ + R * α + β * ((x + 1 - E c : ℕ) : ℝ) := by
  have hpools : ∀ u, tpools E thr0 (Pool.P0061.cumL cuF) θ R K D Lv Bt lev ωs φ u =
      tpools E thr0 (Pool.P0061.cumL cuA) θ R K D Lv Bt lev ωs φ u := fun u =>
    Pool.P0083.tpools_congr E thr0 θ R K D Lv Bt lev _ _ ωs φ u (fun x' hx' t _ => by
      have hne : x' ≠ c := by rintro rfl; rw [hc] at hx'; exact Bool.false_ne_true hx'
      unfold Pool.P0061.cumL
      exact Finset.sum_congr rfl fun v _ => hag x' hne v)
  refine Pool.P0074.thread_cert_interval hD hLv hlev cuF hc hx hin hout A α β hα hβ ?_
  intro f s s' hss hpres
  rcases Nat.eq_or_lt_of_le hss with heq | hlt
  · subst heq; simp [hα]
  · have hpres' : ∀ u, s ≤ u → u < s' → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
        (tpools E thr0 (Pool.P0061.cumL cuA) θ R K D Lv Bt lev ωs φ u) r ℓ := by
      intro u h1 h2; rw [← hpools u]; exact hpres u h1 h2
    have hf : f ≠ c := by
      obtain ⟨r, ℓ, hmem⟩ := hpres' s le_rfl hlt
      have := Pool.P0083.mem_startPools_sampled E thr0 D Lv Bt ωs s _
        (Pool.P0083.mem_tpools_sampled E thr0 θ R K D Lv Bt lev _ ωs φ s) r ℓ f hmem
      intro hfc; rw [hfc, hc] at this; exact Bool.false_ne_true this
    have h := hA f s s' hss hpres'
    rwa [Finset.sum_congr rfl fun u _ => hag f hf u]


/-- Per-unit increments of an estimate history. -/
def incrOf (C : ι → ℕ → ℝ) (u : ℕ) (x : ι) : ℝ := C x (u + 1) - C x u

omit [LinearOrder ι] [Fintype ι] in
theorem cumL_incrOf (C : ι → ℕ → ℝ) (h0 : ∀ x, C x 0 = 0) : Pool.P0061.cumL (incrOf C) = C := by
  funext x e
  unfold Pool.P0061.cumL incrOf
  rw [Finset.sum_range_sub (fun u => C x u), h0, sub_zero]

omit [LinearOrder ι] [Fintype ι] in
theorem sum_Ico_incrOf (C : ι → ℕ → ℝ) (x : ι) {a b : ℕ} (hab : a ≤ b) :
    ∑ u ∈ Finset.Ico a b, incrOf C u x = C x b - C x a :=
  Finset.sum_Ico_sub (fun u => C x u) hab

/-- **Certificate for the one-free-observation process.** Let `c` be a never-sampled copy, forced into the run
(sampling bits `forceS ωs c`, filter bits `forceF K φ c`, copy-last slot layout), and let it leave the pools at
`x + 1`. If the learner is within `α + β·len` of the realized estimates of every copy on every interval during
which the copy is present in the actual run (`occSort`, the copy-free run), then over `c`'s lifetime the learner is
within `θ + Rα + β·len` of `c`'s realized estimate in the forced run. -/
theorem fo_cert (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (s : ℕ) (L : ℕ → ι → ℝ)
    {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} (hc : ωs c = false) (y : ℕ → Fin s)
    {x : ℕ} (hx : E c ≤ x)
    (hin : SAlive E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y)
      θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) x c)
    (hout : ¬ Alive E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y)
      θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) (x + 1) c)
    (A : ℕ → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : ∀ f a b, a ≤ b → (∀ u, a ≤ u → u < b → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
      (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y u).pools r ℓ) →
      ∑ u ∈ Finset.Ico a b, A u ≤ Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y f b -
        Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y f a + α + β * ((b - a : ℕ) : ℝ)) :
    ∑ u ∈ Finset.Ico (E c) (x + 1), A u ≤
      Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y c (x + 1) -
        Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y c (E c) +
        θ + R * α + β * ((x + 1 - E c : ℕ) : ℝ) := by
  set CF := Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) y with hCF
  set CA := Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) ωs φ y with hCA
  have hCAS : CA = Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ y := by
    funext f t; simp only [hCA, Chat]; rw [foRun_free_eq E thr0 θ R K D Lv Bt lev s L hc φ y t]
  have hF0 : ∀ x, CF x 0 = 0 := fun _ => rfl
  have hA0 : ∀ x, CA x 0 = 0 := fun _ => rfl
  have h := thread_cert_interval_own hD hLv hlev (incrOf CF) (incrOf CA) hc
    (fun f hf u => by
      unfold incrOf
      rw [hCF, hCA, fo_hC E thr0 θ R K D Lv Bt lev s L hc φ y f hf (u + 1),
        fo_hC E thr0 θ R K D Lv Bt lev s L hc φ y f hf u])
    hx (by rw [cumL_incrOf CF hF0]; exact hin) (by rw [cumL_incrOf CF hF0]; exact hout) A α β hα hβ
    (fun f a b hab hpres => by
      rw [sum_Ico_incrOf CA f hab, hCAS]
      refine hA f a b hab fun u h1 h2 => ?_
      obtain ⟨r, ℓ, hm⟩ := hpres u h1 h2
      refine ⟨r, ℓ, ?_⟩
      rw [cumL_incrOf CA hA0, hCA, ← foRun_pools_eq E thr0 θ R K D Lv Bt lev s L,
        foRun_free_eq E thr0 θ R K D Lv Bt lev s L hc φ y u] at hm
      exact hm)
  rwa [sum_Ico_incrOf CF c (by omega)] at h

open Classical in
/-- **Certificate with concentration.** Over i.i.d. uniform slot sequences of length `T`, the weight of the
sequences on which (i) every start-pool member set of the forced run fits in the `s` slots, (ii) the forced copy `c`
is present at the start of unit `e` and gone at `e + 1 ≤ T`, (iii) the learner `A ω` is within `α + β·len` of the
actual run's estimates on every presence interval (`fo_cert`'s hypothesis), and yet (iv) the learner's loss over
`[E c, e + 1)` exceeds `c`'s TRUE loss by `x + θ + Rα + β·len`, is at most `2 exp (-x²/(4(s+1)²T))`. Losses in
`[0, 1]`. -/
theorem fo_cert_conc (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (s : ℕ) [NeZero s]
    (L : ℕ → ι → ℝ) (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1)
    (ν : PMF (Fin s)) (hν : ∀ z, (ν z).toReal = 1 / s)
    {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} {c : ι} (hc : ωs c = false)
    {e T : ℕ} (hx : E c ≤ e) (heT : e + 1 ≤ T) (A : (Fin T → Fin s) → ℕ → ℝ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    {x : ℝ} (hx0 : 0 ≤ x) (hxT : x ≤ 2 * (s + 1) * T) :
    ∑ ω : Fin T → Fin s, Pool.P0092.wgt ν ω *
      (if (∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c)
              (extY s ω) u).card ≤ s) ∧
          SAlive E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) (extY s ω))
            θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) e c ∧
          ¬ Alive E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) (extY s ω))
            θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) (e + 1) c ∧
          (∀ f a b, a ≤ b → (∀ u, a ≤ u → u < b → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
            (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ (extY s ω) u).pools r ℓ) →
            ∑ u ∈ Finset.Ico a b, A ω u ≤ Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ (extY s ω) f b -
              Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ (extY s ω) f a + α + β * ((b - a : ℕ) : ℝ)) ∧
          ∑ u ∈ Finset.Ico (E c) (e + 1), L u c + x + θ + R * α + β * ((e + 1 - E c : ℕ) : ℝ) ≤
            ∑ u ∈ Finset.Ico (E c) (e + 1), A ω u
        then 1 else 0) ≤
      2 * Real.exp (-(x ^ 2) / (4 * ((s : ℝ) + 1) ^ 2 * T)) := by
  have hL : ∀ u x, |L u x| ≤ 1 := fun u x => abs_le.mpr ⟨by linarith [hL0 u x], hL1 u x⟩
  have hT : 0 < T := by omega
  refine le_trans ?_ (fo_interval_conc E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) ν hν
    (slotSum_occLast s c) hL c (a := E c) (b := e + 1) (by omega) heT hT hx0 hxT)
  refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (Pool.P0092.wgt_nonneg ν ω)
  by_cases h : (∀ u < T, (Vat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c)
              (extY s ω) u).card ≤ s) ∧
          SAlive E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) (extY s ω))
            θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) e c ∧
          ¬ Alive E thr0 (Chat E thr0 θ R K D Lv Bt lev s L (occLast s c) (forceS ωs c) (forceF K φ c) (extY s ω))
            θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) (e + 1) c ∧
          (∀ f a b, a ≤ b → (∀ u, a ≤ u → u < b → ∃ r ℓ, f ∈ startPools E thr0 D Lv Bt ωs u
            (foRun E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ (extY s ω) u).pools r ℓ) →
            ∑ u ∈ Finset.Ico a b, A ω u ≤ Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ (extY s ω) f b -
              Chat E thr0 θ R K D Lv Bt lev s L (occSort s) ωs φ (extY s ω) f a + α + β * ((b - a : ℕ) : ℝ)) ∧
          ∑ u ∈ Finset.Ico (E c) (e + 1), L u c + x + θ + R * α + β * ((e + 1 - E c : ℕ) : ℝ) ≤
            ∑ u ∈ Finset.Ico (E c) (e + 1), A ω u
  · obtain ⟨hgood, hin, hout, hA, hbig⟩ := h
    have hcert := fo_cert hD hLv hlev s L hc (extY s ω) hx hin hout (A ω) α β hα hβ hA
    have hle : ∑ u ∈ Finset.Ico (E c) (e + 1), (if c ∈ Vat E thr0 θ R K D Lv Bt lev s L (occLast s c)
        (forceS ωs c) (forceF K φ c) (extY s ω) u then L u c else 0) ≤ ∑ u ∈ Finset.Ico (E c) (e + 1), L u c :=
      Finset.sum_le_sum fun u _ => by split_ifs <;> linarith [hL0 u c]
    rw [if_pos ⟨hgood, hin, hout, hA, hbig⟩, if_pos]
    refine ⟨hgood, le_trans ?_ (le_abs_self _)⟩
    linarith
  · rw [if_neg h]
    split_ifs <;> norm_num

end Cert

end Pool.P0105

