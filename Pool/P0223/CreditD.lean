import Pool.P0223.PathD
import Pool.P0162.CreditSqrt

/-!
# The credit term of P0194's probing bound (rate jumps × lead over BASE), via P0162

`Pool.P0223.probe_pathD` leaves the credit sum `Σ_x Σ_{t ∈ (E x, b x)} (rate jump at t)·(lead of x over BASE on
[E x, t))⁺`. A jump happens only when the copy's current thread changes, so the jumps are grouped by destination
thread; each copy enters a thread at most once (`curT` is nonincreasing after entry), so the lead windows of the jumps
into one thread have multiplicity at most the number of active copies, which is ≤ `Σ_j sl j` when every thread fits.
P0162's `jump_cost_threads` then bounds the credit by `(S'·Σ_j x_j)·(BASE − ALG)[0,T)` plus per-thread slack, given
ALG's interval guarantees against BASE (`hint`) and against each copy over its active window (`hA`), both hypotheses.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065

namespace Pool.P0223

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- A copy enters a given thread at most once after its entry (`curT` is nonincreasing). -/
theorem jump_unique (x : ι) {j t1 t2 : ℕ} (h1 : P.E x < t1) (h2 : P.E x < t2)
    (hj1 : curT P.E P.thr0 P.D P.Bt x t1 = j) (hn1 : curT P.E P.thr0 P.D P.Bt x (t1 - 1) ≠ j)
    (hj2 : curT P.E P.thr0 P.D P.Bt x t2 = j) (hn2 : curT P.E P.thr0 P.D P.Bt x (t2 - 1) ≠ j) : t1 = t2 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have a := curT_mono (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) x (show t1 ≤ t2 - 1 by omega)
      (by omega)
    have b := curT_mono (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) x (show t2 - 1 ≤ t2 by omega)
      (by omega)
    omega
  · have a := curT_mono (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) x (show t2 ≤ t1 - 1 by omega)
      (by omega)
    have b := curT_mono (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) x (show t1 - 1 ≤ t1 by omega)
      (by omega)
    omega

/-- The destination thread of a pair `(copy, round)` (thread `0` if the current thread is out of range). -/
noncomputable def key (hD : 0 < P.D) (i : ι × ℕ) : Fin P.D :=
  if h : curT P.E P.thr0 P.D P.Bt i.1 i.2 < P.D then ⟨_, h⟩ else ⟨0, hD⟩

/-- Fitting threads bound the number of active copies by the total slot count. -/
theorem card_active_le {ω : ℕ → RC P} {u : ℕ} (hfit : Fits P.Lv P.sl (sp P ℓ ω ωs φ u)) :
    ((active P ℓ ω ωs φ u).card : ℝ) ≤ ∑ j : Fin P.D, (P.sl j : ℝ) := by
  have h1 : (active P ℓ ω ωs φ u).card ≤ (Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u)).card :=
    Finset.card_le_card Finset.sdiff_subset
  have h2 : (Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u)).card ≤
      ∑ r ∈ range P.D, (blockMem P.Lv (sp P ℓ ω ωs φ u) r).card :=
    Finset.card_biUnion_le
  have h3 : ∑ r ∈ range P.D, (blockMem P.Lv (sp P ℓ ω ωs φ u) r).card ≤ ∑ j : Fin P.D, P.sl j := by
    rw [← Fin.sum_univ_eq_sum_range (fun r => (blockMem P.Lv (sp P ℓ ω ωs φ u) r).card)]
    exact Finset.sum_le_sum fun j _ => hfit j
  have : (active P ℓ ω ωs φ u).card ≤ ∑ j : Fin P.D, P.sl j := h1.trans (h2.trans h3)
  exact_mod_cast this

variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)

/-- The lead of copy `x` over BASE on `[E x, t)` (P0154's `isum` of BASE minus `x`). -/
noncomputable def lead (ω : ℕ → RC P) (x : ι) (t : ℕ) : ℝ :=
  -Pool.P0154.isum (fun t => ℓr P ℓ t x - bPol P ℓ ω t) (P.E x) t

/-- The rate jump of copy `x` at round `t`. -/
noncomputable def jmp (ω : ℕ → RC P) (x : ι) (t : ℕ) : ℝ :=
  Pool.P0209.rateD P ℓ ωs φ ω t x - Pool.P0209.rateD P ℓ ωs φ ω (t - 1) x

open Classical in
/-- All `(copy, round)` pairs of the credit sum: copies entering before `T`, rounds in `(E x, b x)`. -/
noncomputable def Wall (ω : ℕ → RC P) (T : ℕ) : Finset (ι × ℕ) :=
  ((univ.filter (fun x => P.E x < T)) ×ˢ range T).filter
    (fun i => P.E i.1 + 1 ≤ i.2 ∧ i.2 < Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T i.1)

open Classical in
/-- The jumps into thread `j`: pairs of `Wall` where the current thread changes and becomes `j`. -/
noncomputable def Wj (ω : ℕ → RC P) (T : ℕ) (j : Fin P.D) : Finset (ι × ℕ) :=
  ((Wall P ℓ ωs φ hD hLv hlev ω T).filter
    (fun i => curT P.E P.thr0 P.D P.Bt i.1 i.2 ≠ curT P.E P.thr0 P.D P.Bt i.1 (i.2 - 1))).filter
    (fun i => key P hD i = j)

section Facts

variable (ω : ℕ → RC P) (T : ℕ) (hlay : Pool.P0191.LayOK P.sl P.lay)
  (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
include hlay hfit

/-- On `Wall`, the copy is active and every thread fits at `t − 1` and at `t`, so both rates are thread weights. -/
theorem rates_wall {i : ι × ℕ} (hi : i ∈ Wall P ℓ ωs φ hD hLv hlev ω T) :
    ∃ (h0 : curT P.E P.thr0 P.D P.Bt i.1 i.2 < P.D) (h1 : curT P.E P.thr0 P.D P.Bt i.1 (i.2 - 1) < P.D),
      Pool.P0209.rateD P ℓ ωs φ ω i.2 i.1 = P.xr ⟨_, h0⟩ ∧
      Pool.P0209.rateD P ℓ ωs φ ω (i.2 - 1) i.1 = P.xr ⟨_, h1⟩ := by
  unfold Wall at hi
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hi
  obtain ⟨⟨⟨-, hxT⟩, htT⟩, hE, hb⟩ := hi
  have hw := (Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T i.1 hxT).2.2
  have ha0 : i.1 ∈ active P ℓ ω ωs φ i.2 := (hw i.2 htT).2 ⟨by omega, hb⟩
  have ha1 : i.1 ∈ active P ℓ ω ωs φ (i.2 - 1) := (hw (i.2 - 1) (by omega)).2 ⟨by omega, by omega⟩
  exact ⟨Pool.P0223.curT_lt P ℓ ω ωs φ hD hLv hlev ha0, Pool.P0223.curT_lt P ℓ ω ωs φ hD hLv hlev ha1,
    Pool.P0223.rateD_active P ℓ ω ωs φ hD hLv hlev hlay (hfit _ htT) ha0,
    Pool.P0223.rateD_active P ℓ ω ωs φ hD hLv hlev hlay (hfit _ (by omega)) ha1⟩

/-- Jumps into thread `j` are in `[0, x_j]` when the rates are positive and antitone in the thread index. -/
theorem jmp_bounds (hxr : ∀ j, 0 < P.xr j) (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i)
    (j : Fin P.D) {i : ι × ℕ} (hi : i ∈ Wj P ℓ ωs φ hD hLv hlev ω T j) :
    0 ≤ jmp P ℓ ωs φ ω i.1 i.2 ∧ jmp P ℓ ωs φ ω i.1 i.2 ≤ P.xr j := by
  unfold Wj at hi
  rw [Finset.mem_filter, Finset.mem_filter] at hi
  obtain ⟨⟨hw, -⟩, hk⟩ := hi
  obtain ⟨h0, h1, e0, e1⟩ := rates_wall P ℓ ωs φ hD hLv hlev ω T hlay hfit hw
  have hkj : (⟨_, h0⟩ : Fin P.D) = j := by
    unfold key at hk; rw [dif_pos h0] at hk; exact hk
  unfold Wall at hw
  rw [Finset.mem_filter] at hw
  have hmono : curT P.E P.thr0 P.D P.Bt i.1 i.2 ≤ curT P.E P.thr0 P.D P.Bt i.1 (i.2 - 1) :=
    curT_mono (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) i.1 (by omega) (by omega)
  unfold jmp
  rw [e0, e1, hkj]
  have hle : P.xr ⟨_, h1⟩ ≤ P.xr j := by
    rw [← hkj]; exact hanti _ _ (by simpa [Fin.le_def] using hmono)
  have hpos := hxr ⟨_, h1⟩
  constructor <;> linarith

/-- The credit sum over `Wall` is the sum over the jumps grouped by destination thread (no jump, no change of rate). -/
theorem sum_wall_eq (g : ι × ℕ → ℝ) :
    ∑ i ∈ Wall P ℓ ωs φ hD hLv hlev ω T, jmp P ℓ ωs φ ω i.1 i.2 * g i =
      ∑ j : Fin P.D, ∑ i ∈ Wj P ℓ ωs φ hD hLv hlev ω T j, jmp P ℓ ωs φ ω i.1 i.2 * g i := by
  classical
  unfold Wj
  rw [Finset.sum_fiberwise (s := (Wall P ℓ ωs φ hD hLv hlev ω T).filter
      (fun i => curT P.E P.thr0 P.D P.Bt i.1 i.2 ≠ curT P.E P.thr0 P.D P.Bt i.1 (i.2 - 1)))
    (g := key P hD) (f := fun i => jmp P ℓ ωs φ ω i.1 i.2 * g i)]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  split_ifs with h
  · rfl
  · push_neg at h
    obtain ⟨h0, h1, e0, e1⟩ := rates_wall P ℓ ωs φ hD hLv hlev ω T hlay hfit hi
    have : (⟨_, h0⟩ : Fin P.D) = ⟨_, h1⟩ := Fin.ext h
    unfold jmp
    rw [e0, e1, this, sub_self, zero_mul]

/-- The lead windows of the jumps into one thread have multiplicity at most the total slot count. -/
theorem mult_le (j : Fin P.D) (u : ℕ) :
    (Pool.P0154.mult (Wj P ℓ ωs φ hD hLv hlev ω T j) (fun i => P.E i.1) (fun i => i.2) u : ℝ) ≤
      ∑ j : Fin P.D, (P.sl j : ℝ) := by
  classical
  unfold Pool.P0154.mult
  set F := (Wj P ℓ ωs φ hD hLv hlev ω T j).filter (fun i => P.E i.1 ≤ u ∧ u < i.2)
  by_cases hF : F = ∅
  · rw [hF, Finset.card_empty, Nat.cast_zero]
    exact Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  -- membership facts
  have hmem : ∀ i ∈ F, i ∈ Wall P ℓ ωs φ hD hLv hlev ω T ∧ P.E i.1 ≤ u ∧ u < i.2 ∧
      curT P.E P.thr0 P.D P.Bt i.1 i.2 = j ∧
      curT P.E P.thr0 P.D P.Bt i.1 (i.2 - 1) ≠ j := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiW, hEu, hut⟩ := hi
    unfold Wj at hiW
    rw [Finset.mem_filter, Finset.mem_filter] at hiW
    obtain ⟨⟨hw, hne⟩, hk⟩ := hiW
    obtain ⟨h0, -, -, -⟩ := rates_wall P ℓ ωs φ hD hLv hlev ω T hlay hfit hw
    have hkj : curT P.E P.thr0 P.D P.Bt i.1 i.2 = j := by
      unfold key at hk; rw [dif_pos h0] at hk; rw [← hk]
    exact ⟨hw, hEu, hut, hkj, by rw [← hkj]; exact fun h => hne h.symm⟩
  have hwall : ∀ i ∈ Wall P ℓ ωs φ hD hLv hlev ω T, P.E i.1 < T ∧ i.2 < T ∧ P.E i.1 + 1 ≤ i.2 ∧
      i.2 < Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T i.1 := by
    intro i hi
    unfold Wall at hi
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hi
    exact ⟨hi.1.1.2, hi.1.2, hi.2.1, hi.2.2⟩
  -- u < T, so every thread fits at u
  have huT : u < T := by
    obtain ⟨hw, -, hut, -⟩ := hmem i0 hi0
    have := (hwall i0 hw).2.1
    omega
  -- the first coordinates are distinct active copies at u
  have hinj : Set.InjOn Prod.fst (F : Set (ι × ℕ)) := by
    intro a ha b hb hab
    obtain ⟨hwa, -, -, hja, hna⟩ := hmem a ha
    obtain ⟨hwb, -, -, hjb, hnb⟩ := hmem b hb
    have ea := (hwall a hwa).2.2.1
    have eb := (hwall b hwb).2.2.1
    rw [hab] at ea hja hna
    have := jump_unique P b.1 (show P.E b.1 < a.2 by omega) (show P.E b.1 < b.2 by omega) hja hna hjb hnb
    exact Prod.ext hab this
  have hmaps : Set.MapsTo Prod.fst (F : Set (ι × ℕ)) (active P ℓ ω ωs φ u : Set ι) := by
    intro i hi
    obtain ⟨hw, hEu, hut, -, -⟩ := hmem i hi
    obtain ⟨hxT, -, -, hb⟩ := hwall i hw
    exact ((Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T i.1 hxT).2.2 u huT).2 ⟨hEu, by omega⟩
  have hcard : F.card ≤ (active P ℓ ω ωs φ u).card := Finset.card_le_card_of_injOn Prod.fst hmaps hinj
  exact le_trans (by exact_mod_cast hcard) (card_active_le P ℓ ωs φ (hfit u huT))

/-- The number of jumps into one thread is at most the number of copies entering before `T`. -/
theorem card_Wj_le (j : Fin P.D) :
    (Wj P ℓ ωs φ hD hLv hlev ω T j).card ≤ (univ.filter (fun x => P.E x < T)).card := by
  classical
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro i hi
    have hi' := hi
    unfold Wj Wall at hi'
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product, Finset.mem_filter,
      Finset.mem_univ, true_and] at hi'
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact hi'.1.1.1.1
  · intro a ha b hb hab
    have key_eq : ∀ i ∈ Wj P ℓ ωs φ hD hLv hlev ω T j, P.E i.1 < i.2 ∧
        curT P.E P.thr0 P.D P.Bt i.1 i.2 = j ∧ curT P.E P.thr0 P.D P.Bt i.1 (i.2 - 1) ≠ j := by
      intro i hi
      have hi2 := hi
      unfold Wj at hi2
      rw [Finset.mem_filter, Finset.mem_filter] at hi2
      obtain ⟨⟨hw, hne⟩, hk⟩ := hi2
      obtain ⟨h0, -, -, -⟩ := rates_wall P ℓ ωs φ hD hLv hlev ω T hlay hfit hw
      have hkj : curT P.E P.thr0 P.D P.Bt i.1 i.2 = j := by
        unfold key at hk; rw [dif_pos h0] at hk; rw [← hk]
      unfold Wall at hw
      rw [Finset.mem_filter] at hw
      exact ⟨by omega, hkj, by rw [← hkj]; exact fun h => hne h.symm⟩
    obtain ⟨ea, hja, hna⟩ := key_eq a (Finset.mem_coe.mp ha)
    obtain ⟨eb, hjb, hnb⟩ := key_eq b (Finset.mem_coe.mp hb)
    rw [hab] at ea hja hna
    exact Prod.ext hab (jump_unique P b.1 ea eb hja hna hjb hnb)

/-- A jump into thread `j` happens at a round whose canonical thread is `j` (a thread-`j` restart). -/
theorem canonT_of_mem_Wj (j : Fin P.D) {i : ι × ℕ} (hi : i ∈ Wj P ℓ ωs φ hD hLv hlev ω T j) :
    canonT P.D P.Bt i.2 = j := by
  have hi2 := hi
  unfold Wj at hi2
  rw [Finset.mem_filter, Finset.mem_filter] at hi2
  obtain ⟨⟨hw, hne⟩, hk⟩ := hi2
  obtain ⟨h0, -, -, -⟩ := rates_wall P ℓ ωs φ hD hLv hlev ω T hlay hfit hw
  have hkj : curT P.E P.thr0 P.D P.Bt i.1 i.2 = j := by
    unfold key at hk; rw [dif_pos h0] at hk; rw [← hk]
  unfold Wall at hw
  rw [Finset.mem_filter] at hw
  have hs := curT_succ (E := P.E) (thr0 := P.thr0) (D := P.D) (Bt := P.Bt) (c := i.1) (x := i.2 - 1) (by omega)
  rw [show i.2 - 1 + 1 = i.2 by omega] at hs
  rw [← hkj, hs]
  rw [hs] at hne
  rcases le_total (curT P.E P.thr0 P.D P.Bt i.1 (i.2 - 1)) (canonT P.D P.Bt i.2) with h | h
  · rw [min_eq_left h] at hne; exact absurd rfl hne
  · rw [min_eq_right h]

open Classical in
/-- **Jump count.** The number of jumps into thread `j` is at most `S' = Σ_j sl j` times the number of rounds
`t < T` whose canonical thread is `j`. -/
theorem card_Wj_le_canon (j : Fin P.D) :
    ((Wj P ℓ ωs φ hD hLv hlev ω T j).card : ℝ) ≤
      (∑ j : Fin P.D, (P.sl j : ℝ)) * ((range T).filter (fun t => canonT P.D P.Bt t = j)).card := by
  have hmaps : ∀ i ∈ Wj P ℓ ωs φ hD hLv hlev ω T j,
      i.2 ∈ (range T).filter (fun t => canonT P.D P.Bt t = j) := by
    intro i hi
    have hc := canonT_of_mem_Wj P ℓ ωs φ hD hLv hlev ω T hlay hfit j hi
    unfold Wj Wall at hi
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi.1.1.1.2, hc⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  refine le_trans (Finset.sum_le_sum (g := fun _ => ∑ j : Fin P.D, (P.sl j : ℝ)) fun t ht => ?_)
    (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]))
  rw [Finset.mem_filter, Finset.mem_range] at ht
  -- the copies jumping at `t` are distinct active copies at `t`
  have hcard : ((Wj P ℓ ωs φ hD hLv hlev ω T j).filter (fun i => i.2 = t)).card ≤
      (active P ℓ ω ωs φ t).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro i hi
      rw [Finset.mem_coe, Finset.mem_filter] at hi
      obtain ⟨hiW, rfl⟩ := hi
      unfold Wj Wall at hiW
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and] at hiW
      obtain ⟨⟨⟨⟨hxT, htT⟩, hE, htb⟩, -⟩, -⟩ := hiW
      exact ((Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T i.1 hxT).2.2 i.2 htT).2 ⟨by omega, htb⟩
    · intro a ha b hb hab
      rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      exact Prod.ext hab (ha.2.trans hb.2.symm)
  exact le_trans (by exact_mod_cast hcard) (card_active_le P ℓ ωs φ (hfit t ht.1))

end Facts

open Classical in
/-- **Credit term of P0194's probing bound.** With every thread fitting before `T`, rates positive and antitone in the
thread index, ALG within `ρ₀ + V[a,b) + c·√(b − a)` of BASE on every interval of `[0, T)` (`hint`), and ALG within
`r x t` of every copy `x` over each window `[E x, t)` on which `x` is active (`hA`), the credit sum left by
`Pool.P0223.probe_pathD` is at most `(S'·Σ_j x_j)·(BASE − ALG)[0,T)` plus per-thread slack, `S' = Σ_j sl j`. -/
theorem credit_D (ω : ℕ → RC P) (T : ℕ) (hT : 1 ≤ T) (hlay : Pool.P0191.LayOK P.sl P.lay)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    (hxr : ∀ j, 0 < P.xr j) (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i)
    (v : ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c)
    (hint : ∀ a b, a ≤ b → b ≤ T →
      -Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) a b ≤
        ρ₀ + Pool.P0154.isum v a b + c * Real.sqrt ((b : ℝ) - a))
    (r : ι → ℕ → ℝ)
    (hA : ∀ x t, t ≤ T → P.E x < t → (∀ u, P.E x ≤ u → u < t → x ∈ active P ℓ ω ωs φ u) →
      Pool.P0154.isum (fun u => aPol P ℓ ωs φ ω u) (P.E x) t ≤
        Pool.P0154.isum (fun u => ℓr P ℓ u x) (P.E x) t + r x t) :
    ∑ x ∈ univ.filter (fun x => P.E x < T),
        ∑ t ∈ Ico (P.E x + 1) (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x),
          (Pool.P0209.rateD P ℓ ωs φ ω t x - Pool.P0209.rateD P ℓ ωs φ ω (t - 1) x) *
            max 0 (-Pool.P0154.isum (fun t => ℓr P ℓ t x - bPol P ℓ ω t) (P.E x) t)
      ≤ ((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) 0 T
        + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * (Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * c *
            (Real.sqrt T * Real.sqrt (2 * (Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1))
          + ∑ i ∈ Wj P ℓ ωs φ hD hLv hlev ω T j, max 0 (r i.1 i.2)) := by
  set b := Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T
  set S' := ∑ j : Fin P.D, (P.sl j : ℝ)
  -- rewrite the double sum over (copy, round) as a sum over `Wall`
  have hsum : ∑ x ∈ univ.filter (fun x => P.E x < T), ∑ t ∈ Ico (P.E x + 1) (b x),
        jmp P ℓ ωs φ ω x t * max 0 (lead P ℓ ω x t) =
      ∑ i ∈ Wall P ℓ ωs φ hD hLv hlev ω T, jmp P ℓ ωs φ ω i.1 i.2 * max 0 (lead P ℓ ω i.1 i.2) := by
    unfold Wall
    conv_rhs => rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.mem_filter] at hx
    have hbT : b x ≤ T := (Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T x hx.2).2.1
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext t
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
    · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
  have hS0 : 0 ≤ S' := Finset.sum_nonneg fun j _ => Nat.cast_nonneg _
  show ∑ x ∈ univ.filter (fun x => P.E x < T), ∑ t ∈ Ico (P.E x + 1) (b x),
        jmp P ℓ ωs φ ω x t * max 0 (lead P ℓ ω x t) ≤ _
  rw [hsum, sum_wall_eq P ℓ ωs φ hD hLv hlev ω T hlay hfit]
  refine Pool.P0162.jump_cost_threads (fun i : ι × ℕ => P.E i.1) (fun i => i.2) univ
    (Wj P ℓ ωs φ hD hLv hlev ω T) (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) v ρ₀ S' c P.xr T hT hv hρ₀ hc
    hS0 hint ?_ ?_ (fun j _ => (hxr j).le) (fun i => jmp P ℓ ωs φ ω i.1 i.2) (fun i => lead P ℓ ω i.1 i.2)
    (fun i => r i.1 i.2) ?_ ?_
  · -- window ends ≤ T
    intro j _ i hi
    unfold Wj Wall at hi
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hi
    exact hi.1.1.1.2.le
  · intro j _ u
    exact mult_le P ℓ ωs φ hD hLv hlev ω T hlay hfit j u
  · intro j _ i hi
    exact jmp_bounds P ℓ ωs φ hD hLv hlev ω T hlay hfit hxr hanti j hi
  · -- leads: BASE − x on the window ≤ (BASE − ALG) on the window + ALG's slack against x
    intro j _ i hi
    unfold Wj Wall at hi
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ, true_and] at hi
    obtain ⟨⟨⟨⟨hxT, htT⟩, hE, htb⟩, -⟩, -⟩ := hi
    have hw := (Pool.P0223.win_facts P ℓ ωs φ hD hLv hlev ω T i.1 hxT)
    have halg := hA i.1 i.2 htT.le (by omega)
      (fun u h1 h2 => (hw.2.2 u (by omega)).2 ⟨h1, by omega⟩)
    exact Pool.P0154.lead_le (fun u => bPol P ℓ ω u) (fun u => aPol P ℓ ωs φ ω u) (fun u => ℓr P ℓ u i.1)
      (P.E i.1) i.2 (r i.1 i.2) halg

open Classical in
/-- **P0194's probing term, pathwise, with the credit absorbed** (`probe_pathD` + `credit_D`): on the event that every
thread fits before `T` and the slot and `B̂` good events hold, the probing term is at most
`Σ_x (final rate)·(margin + widths + Bmin)` plus `(S'·Σ_j x_j)·(BASE − ALG)[0,T)` plus the per-thread slack of
`credit_D`, given ALG's interval guarantees `hint` (against BASE) and `hA` (against each copy over its active window). -/
theorem probe_credit_pathD (rc0 : RC P) (ω : ℕ → RC P) (T : ℕ) (hT : 1 ≤ T) {L : ℝ} (hL : 0 < L)
    (hB : 0 < P.Bmin) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j)
    (hanti : ∀ i j : Fin P.D, i ≤ j → P.xr j ≤ P.xr i)
    (hcB : 0 ≤ P.cB) (hΛ0 : ∀ x c, 0 ≤ P.Λ x c)
    (hfit : ∀ t < T, Fits P.Lv P.sl (sp P ℓ ω ωs φ t))
    (hgS : ∀ x, Pool.P0158.GoodV (Pool.P0203.DS P ℓ ωs φ rc0 x) (Pool.P0203.gateS P ℓ ωs φ rc0 x)
      (Pool.P0203.rS P x) (Pool.P0158.rmax1 (Pool.P0203.rS P x)) L T (Pool.P0203.pre P ω T))
    (hgB : Pool.P0158.GoodV (Pool.P0216.DB P ℓ rc0) (fun _ _ => true) (fun _ => P.cB)
      (Pool.P0158.rmax1 (fun _ => P.cB)) L T (Pool.P0203.pre P ω T))
    (v : ℕ → ℝ) (ρ₀ c : ℝ) (hv : ∀ u, 0 ≤ v u) (hρ₀ : 0 ≤ ρ₀) (hc : 0 ≤ c)
    (hint : ∀ a b, a ≤ b → b ≤ T →
      -Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) a b ≤
        ρ₀ + Pool.P0154.isum v a b + c * Real.sqrt ((b : ℝ) - a))
    (r : ι → ℕ → ℝ)
    (hA : ∀ x t, t ≤ T → P.E x < t → (∀ u, P.E x ≤ u → u < t → x ∈ active P ℓ ω ωs φ u) →
      Pool.P0154.isum (fun u => aPol P ℓ ωs φ ω u) (P.E x) t ≤
        Pool.P0154.isum (fun u => ℓr P ℓ u x) (P.E x) t + r x t) :
    ∑ u ∈ range T, ∑ s : (Σ j : Fin P.D, Fin (P.sl j)), P.xr s.1 * (slotVal P ℓ ωs φ ω u s - bPol P ℓ ω u) ≤
      ∑ x ∈ univ.filter (fun x => P.E x < T),
          Pool.P0209.rateD P ℓ ωs φ ω (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x - 1) x *
            (Pool.P0223.MOfW P L (Pool.P0223.bOf P ℓ ωs φ hD hLv hlev ω T x) x + P.Bmin)
        + (((∑ j : Fin P.D, (P.sl j : ℝ)) * ∑ j : Fin P.D, P.xr j) *
          Pool.P0154.isum (fun u => bPol P ℓ ω u - aPol P ℓ ωs φ ω u) 0 T
        + ∑ j : Fin P.D, P.xr j * ((∑ j : Fin P.D, (P.sl j : ℝ)) * ρ₀ *
            (2 * (Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1)
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * Pool.P0154.isum v 0 T
          + (∑ j : Fin P.D, (P.sl j : ℝ)) * c *
            (Real.sqrt T * Real.sqrt (2 * (Wj P ℓ ωs φ hD hLv hlev ω T j).card + 1))
          + ∑ i ∈ Wj P ℓ ωs φ hD hLv hlev ω T j, max 0 (r i.1 i.2))) := by
  have h1 := Pool.P0223.probe_pathD P ℓ ωs φ rc0 hD hLv hlev ω T hL hB hlay hxr hanti hcB hΛ0 hfit hgS hgB
  have h2 := credit_D P ℓ ωs φ hD hLv hlev ω T hT hlay hfit hxr hanti v ρ₀ c hv hρ₀ hc hint r hA
  rw [Finset.sum_add_distrib] at h1
  linarith

end Pool.P0223
