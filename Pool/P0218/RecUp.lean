import Pool.P0203.DSlot
import Pool.P0186.RecCert
import Pool.P0207.Rule
import Pool.P0208.Tails

/-!
# The record upper tail (P0186's `hup`) for P0194's process, actual and forced runs

P0186's certificates use, for a record's copy `c`, the upper tail of its RECORD data `recD` while it is not retired
(`hup`): the actual run's data if `c` is sampled, its forced run's data otherwise. For P0194's process in P0207's
regime (layout `sortLay`), the forced run of `c` (P0197's `coup_dz`: layout `lastLay c`, forced sampling/filter bits)
is again a P0194 process: the parameters with layout `lastLay c` (`withLay`) and the bits `forceS ωs c`,
`forceF φ c`. So P0203's concentration applies to it.

* `withLay`: P0194's parameters with another layout. `fRun_eq`: P0168's forced run is that process's pool.
* `incr_zero`: a copy that is neither retired nor a member gains nothing (it holds no slot).
* **`up_tail`**: on P0203's good event for `c` and without thread overflow before `T`, for every `e ≤ T` such that
  `c` is not retired on `[E c, e)`, `Σ_{[E c, e)} incr ≤ Σ ℓ + widV(Σ_{[E c,e)} 1/x_{curT c}, max(1, max 1/x), L)`.
  The rounds where `c` is not a member contribute `−ℓ ≤ 0`.
* **`hup_rec`**: P0186's `hup` (record data `recD`, retired set `recAux`) for P0194's process with `sortLay`, given
  the good events and no overflow in the actual run and in `c`'s forced run.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0156 Pool.P0065 Pool.P0095 Pool.P0203

namespace Pool.P0218

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι)

/-- P0194's parameters with another layout (placing only members of the given set). -/
def withLay (lay' : (j : Fin P.D) → Finset ι → Fin (P.sl j) → Option ι)
    (h : ∀ j V k x, lay' j V k = some x → x ∈ V) : ParD n ι :=
  { P with lay := lay', lay_mem := h }

/-- The copy-last layout of `c` places only members. -/
theorem lastLay_mem (c : ι) : ∀ j V k x, lastLay P.sl c j V k = some x → x ∈ V :=
  (Pool.P0191.layOK_last P.sl c).mem

/-- The parameters of `c`'s forced run. -/
abbrev PL (c : ι) : ParD n ι := withLay P (lastLay P.sl c) (lastLay_mem P c)

variable (ℓ : LossSeq n) (ω : ℕ → RC P) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

theorem sB_PL (c : ι) : ∀ u, sB (PL P c) ℓ ω u = sB P ℓ ω u
  | 0 => rfl
  | u + 1 => by simp only [sB]; rw [sB_PL c u]; rfl

theorem Bh_PL (c : ι) : ∀ u, Bh (PL P c) ℓ ω u = Bh P ℓ ω u
  | 0 => rfl
  | u + 1 => by
    simp only [Bh, bAct]
    rw [Bh_PL c u, sB_PL P ℓ ω c u]
    rfl

theorem rhD_PL (c : ι) : rhD (PL P c) ℓ ω = rhD P ℓ ω := by
  funext u x h
  simp only [rhD, Bh_PL P ℓ ω c]
  rfl

/-- P0168's forced run of `c` (with P0197's `lastLay` update) is the pool of `PL c` with the forced bits. -/
theorem fRun_eq (c : ι) (u : ℕ) :
    Pool.P0168.fRun P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) (lastLay P.sl c) (zc P ω)) ∅ ωs φ c u =
      pool (PL P c) ℓ ω (forceS ωs c) (forceF P.K φ c) u := by
  unfold Pool.P0168.fRun pool
  have h1 : rhD (PL P c) ℓ ω = rhD P ℓ ω := rhD_PL P ℓ ω c
  have h2 : ℓr (PL P c) ℓ = ℓr P ℓ := rfl
  have h3 : zc (PL P c) ω = zc P ω := rfl
  rw [h1, h2, h3]
  rfl

/-- The data of P0194's pool. -/
noncomputable abbrev datOf (Q : ParD n ι) (ℓ : LossSeq n) (ω : ℕ → RC Q) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin Q.K → ι → Bool) :
    ι → ℕ → ℝ :=
  gChat Q.E Q.thr0 Q.θ Q.R Q.K Q.D Q.Lv Q.Bt Q.lev
    (dzUpd Q.D Q.Lv Q.sl 1 1 Q.xr (ℓr Q ℓ) (rhD Q ℓ ω) Q.lay (zc Q ω)) ∅ ωs φ

/-- **A copy that is neither retired nor a member gains nothing**: no slot of any thread shows it. -/
theorem incr_zero (u : ℕ) (c : ι) (hr : c ∉ (pool P ℓ ω ωs φ u).aux)
    (hm : c ∉ members P.D P.Lv (sp P ℓ ω ωs φ u)) :
    Pool.P0105.incrOf (datOf P ℓ ω ωs φ) u c = 0 := by
  unfold Pool.P0105.incrOf
  rw [slotEst_eq_inc P ℓ ωs φ ω u c hr]
  unfold slotEst
  rcases (ω u).1.getD none with _ | ⟨j, k⟩
  · rfl
  · simp only [obsR]
    rcases h : P.lay j (blockMem P.Lv (sp P ℓ ω ωs φ u) j) k with _ | y
    · rfl
    · have hy := P.lay_mem j _ k y h
      have hyc : y ≠ c := by
        rintro rfl
        apply hm
        simp only [members, Finset.mem_biUnion, Finset.mem_range]
        simp only [blockMem, Finset.mem_biUnion, Finset.mem_range] at hy
        obtain ⟨l, hl, hy⟩ := hy
        exact ⟨j, j.2, l, hl, hy⟩
      simp [dzC, hyc]

open Classical in
/-- **Upper tail of a copy's data while it is not retired**, on P0203's good event and without overflow. -/
theorem up_tail (rc0 : RC P) (c : ι) {L : ℝ} (T : ℕ)
    (hgood : Pool.P0158.GoodV (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c)) L T
      (pre P ω T))
    (hfit : ∀ u, u < T → Fits P.Lv P.sl (sp P ℓ ω ωs φ u)) {a e : ℕ} (hae : a ≤ e) (heT : e ≤ T)
    (hnr : ∀ u, a ≤ u → u < e → c ∉ (pool P ℓ ω ωs φ u).aux) :
    ∑ u ∈ Ico a e, Pool.P0105.incrOf (datOf P ℓ ω ωs φ) u c ≤ ∑ u ∈ Ico a e, ℓr P ℓ u c +
      Pool.P0158.widV (∑ u ∈ Ico a e, rS P c u) (Pool.P0158.rmax1 (rS P c) a e) L := by
  have h := goodV_run P ℓ ωs φ rc0 ω c T hgood a e hae heT
  have hpt : ∀ u ∈ Ico a e, Pool.P0105.incrOf (datOf P ℓ ω ωs φ) u c - ℓr P ℓ u c ≤
      if c ∈ active P ℓ ω ωs φ u ∧ Fits P.Lv P.sl (sp P ℓ ω ωs φ u) then
        (gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
            (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ c (u + 1) -
          gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
            (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ c u) - ℓr P ℓ u c
      else 0 := by
    intro u hu
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hu
    split_ifs with hg
    · exact le_rfl
    · have hnm : c ∉ members P.D P.Lv (sp P ℓ ω ωs φ u) := by
        intro hm
        exact hg ⟨by unfold active; exact Finset.mem_sdiff.2 ⟨hm, hnr u h1 h2⟩, hfit u (by omega)⟩
      rw [incr_zero P ℓ ω ωs φ u c (hnr u h1 h2) hnm]
      unfold ℓr; cases ℓ u (P.arm c) <;> simp
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_sub_distrib] at hsum
  have := (abs_lt.1 h).2
  linarith

/-- A copy is never retired at its entry round (P0207's `dz_E_lt_of_mem_aux`). -/
theorem not_aux_entry (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (c : ι) :
    c ∉ (pool P ℓ ω ωs φ (P.E c)).aux := fun h =>
  lt_irrefl _ (Pool.P0207.dz_E_lt_of_mem_aux P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.E P.thr0 P.θ P.R P.K P.Bt
    P.lev P.lay (zc P ω) ωs φ hD hLv hlev (P.E c) h)

open Classical in
/-- **The record upper tail of P0186's `hup` for P0194's process, in `widV` form.** The shape is P0186's (`recD`,
`recAux` with P0197's `U`, `A0`) EXCEPT the width: here it is P0158's `widV(Σ_{[E c,e)} 1/x_{curT c}, rmax1, L)`,
which depends on the copy's thread path, not a single length-only `W (e − E c)`; `hup_len` gives P0186's exact form
via a rate floor. The record's data are the actual run's for a sampled copy
and its forced run's (layout `lastLay c`, forced bits) otherwise (P0186's `recD`/`recAux` with P0197's `U`, `A0`).
Given P0203's good event and no overflow in the actual run (for a sampled copy) or in the forced run (otherwise),
for every `e ≤ T` such that the copy is not retired in its record's run on `(E c, e)`:
`Σ_{[E c, e)} incrOf(recD c) ≤ Σ ℓ + widV(Σ_{[E c, e)} 1/x_{curT c}, max(1, max 1/x), L)`. -/
theorem hup_rec (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (rc0 : RC P) (c : ι)
    {L : ℝ} (T : ℕ)
    (hgA : ωs c = true → Pool.P0158.GoodV (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c) (rS P c)
      (Pool.P0158.rmax1 (rS P c)) L T (pre P ω T))
    (hfA : ωs c = true → ∀ u, u < T → Fits P.Lv P.sl (sp P ℓ ω ωs φ u))
    (hgF : ωs c = false → Pool.P0158.GoodV (DS (PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 c)
      (gateS (PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c)) L T
      (pre (PL P c) ω T))
    (hfF : ωs c = false → ∀ u, u < T → Fits P.Lv P.sl (sp (PL P c) ℓ ω (forceS ωs c) (forceF P.K φ c) u))
    (e : ℕ) (hce : P.E c ≤ e) (heT : e ≤ T)
    (hnr : ∀ u, P.E c < u → u < e → c ∉ Pool.P0186.recAux P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅
      (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) (lastLay P.sl c') (zc P ω)) (fun _ => ∅)
      ωs φ c u) :
    ∑ u ∈ Ico (P.E c) e, Pool.P0105.incrOf (Pool.P0186.recD P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅
      (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) (lastLay P.sl c') (zc P ω)) (fun _ => ∅)
      ωs φ c) u c ≤ ∑ u ∈ Ico (P.E c) e, ℓr P ℓ u c +
      Pool.P0158.widV (∑ u ∈ Ico (P.E c) e, rS P c u) (Pool.P0158.rmax1 (rS P c) (P.E c) e) L := by
  by_cases hs : ωs c = true
  · have hrec : Pool.P0186.recD P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
        (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅
        (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) (lastLay P.sl c') (zc P ω)) (fun _ => ∅)
        ωs φ c = datOf P ℓ ω ωs φ := by
      unfold Pool.P0186.recD; rw [if_pos hs]
    rw [hrec]
    refine up_tail P ℓ ω ωs φ rc0 c T (hgA hs) (hfA hs) hce heT fun u h1 h2 => ?_
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; exact not_aux_entry P ℓ ω ωs φ hD hLv hlev c
    · have := hnr u h h2
      unfold Pool.P0186.recAux at this; rw [if_pos hs] at this
      exact this
  · have hs' : ωs c = false := by simpa using hs
    have hrec : Pool.P0186.recD P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
        (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅
        (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) (lastLay P.sl c') (zc P ω)) (fun _ => ∅)
        ωs φ c = datOf (PL P c) ℓ ω (forceS ωs c) (forceF P.K φ c) := by
      unfold Pool.P0186.recD Pool.P0168.fChat
      rw [if_neg hs]
      unfold datOf
      rw [rhD_PL P ℓ ω c]
      rfl
    rw [hrec]
    refine up_tail (PL P c) ℓ ω (forceS ωs c) (forceF P.K φ c) rc0 c T (hgF hs') (hfF hs') hce heT
      fun u h1 h2 => ?_
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · subst h; exact not_aux_entry (PL P c) ℓ ω (forceS ωs c) (forceF P.K φ c) hD hLv hlev c
    · have := hnr u h h2
      unfold Pool.P0186.recAux at this; rw [if_neg hs] at this
      rw [← fRun_eq P ℓ ω ωs φ c u]
      exact this

open Classical in
/-- **P0186's `hup` in its exact length-only form** (`W (e − E c)` with ONE monotone, nonnegative `W`, uniform over the
copies): with a rate floor `xmin ∈ (0, 1]` (every `x_j ≥ xmin`), `hup_rec`'s width is majorized by P0208's
`widV_le_len`, giving `W(m) = 2√(L·m/xmin) + 2L/xmin`. This majorant uses the smallest rate, so it is large for
records in the finest threads; a thread-aware majorant needs the occupancy bound (P0208's `widV_le_sqrt_occ`). -/
theorem hup_len (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (rc0 : RC P) (c : ι)
    {L xmin : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ P.xr j) (T : ℕ)
    (hgA : ωs c = true → Pool.P0158.GoodV (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c) (rS P c)
      (Pool.P0158.rmax1 (rS P c)) L T (pre P ω T))
    (hfA : ωs c = true → ∀ u, u < T → Fits P.Lv P.sl (sp P ℓ ω ωs φ u))
    (hgF : ωs c = false → Pool.P0158.GoodV (DS (PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 c)
      (gateS (PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c)) L T
      (pre (PL P c) ω T))
    (hfF : ωs c = false → ∀ u, u < T → Fits P.Lv P.sl (sp (PL P c) ℓ ω (forceS ωs c) (forceF P.K φ c) u))
    (e : ℕ) (hce : P.E c ≤ e) (heT : e ≤ T)
    (hnr : ∀ u, P.E c < u → u < e → c ∉ Pool.P0186.recAux P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅
      (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) (lastLay P.sl c') (zc P ω)) (fun _ => ∅)
      ωs φ c u) :
    ∑ u ∈ Ico (P.E c) e, Pool.P0105.incrOf (Pool.P0186.recD P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅
      (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) (lastLay P.sl c') (zc P ω)) (fun _ => ∅)
      ωs φ c) u c ≤ ∑ u ∈ Ico (P.E c) e, ℓr P ℓ u c +
      (fun m : ℕ => 2 * √(L * ((m : ℝ) / xmin)) + 2 * L / xmin) (e - P.E c) :=
  (hup_rec P ℓ ω ωs φ hD hLv hlev rc0 c T hgA hfA hgF hfF e hce heT hnr).trans
    (add_le_add le_rfl (Pool.P0208.widV_le_len P c hxm hxm1 hL hxr (P.E c) e))

/-- The length-only width of `hup_len` is nonnegative and monotone (P0186's `hW0`, `hWm`). -/
theorem Wlen_mono_nonneg {L xmin : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) :
    Monotone (fun m : ℕ => 2 * √(L * ((m : ℝ) / xmin)) + 2 * L / xmin) ∧
      ∀ m : ℕ, 0 ≤ 2 * √(L * ((m : ℝ) / xmin)) + 2 * L / xmin := by
  refine ⟨fun m m' h => ?_, fun m => by positivity⟩
  have : L * ((m : ℝ) / xmin) ≤ L * ((m' : ℝ) / xmin) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by exact_mod_cast h) hxm.le) hL
  have := Real.sqrt_le_sqrt this
  simp only
  linarith

theorem wR_PL (c : ι) (rc : RC P) : wR (PL P c) rc = wR P rc := by
  rcases rc with ⟨κ, d, y, z⟩
  rcases κ with _ | _ | ⟨j, k⟩ <;> rfl

/-- The forced run's coin law is the actual one (same round weights). -/
theorem wgt_PL (hL : P.IsLaw) (hN : 0 < P.N) (c : ι) {T : ℕ} (ω : Fin T → RC P) :
    Pool.P0092.wgt (nuD (PL P c) hL hN) ω = Pool.P0092.wgt (nuD P hL hN) ω := by
  unfold Pool.P0092.wgt
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [nuD_toReal P hL hN, ← wR_PL P c]
  exact nuD_toReal (PL P c) hL hN (ω i)

open Classical in
/-- **All record events at once.** Over P0194's round coins, with probability at least `1 − 2|ι|·2(T+1)²e^{−L}`,
P0203's good event holds for every copy in the actual run AND for every copy in its own forced run. -/
theorem prob_not_goodRec (hL : P.IsLaw) (hN : 0 < P.N) (hD : 0 < P.D) (hLv : 0 < P.Lv)
    (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (hlay : Pool.P0191.LayOK P.sl P.lay) (hxr : ∀ j, 0 < P.xr j)
    (hxr1 : ∀ j, P.xr j ≤ 1) (rc0 : RC P) {L : ℝ} (hLp : 0 < L) (T : ℕ) :
    (∑ ω : Fin T → RC P, Pool.P0092.wgt (nuD P hL hN) ω *
      if (∀ c, Pool.P0158.GoodV (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c))
            L T ω) ∧
          (∀ c, Pool.P0158.GoodV (DS (PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 c)
            (gateS (PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c)) L T ω)
      then (0 : ℝ) else 1) ≤
      2 * (Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L))) := by
  have hw : ∀ ω : Fin T → RC P, 0 ≤ Pool.P0092.wgt (nuD P hL hN) ω :=
    fun ω => Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  set GA : (Fin T → RC P) → Prop := fun ω => ∀ c, Pool.P0158.GoodV (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c)
    (rS P c) (Pool.P0158.rmax1 (rS P c)) L T ω with hGA
  set GF : ι → (Fin T → RC P) → Prop := fun c ω => Pool.P0158.GoodV (DS (PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 c)
    (gateS (PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c)) L T ω with hGF
  have hA := prob_not_goodDS_all P ℓ ωs φ rc0 hL hN hD hLv hlev hlay hxr hxr1 hLp T
  have hF : ∀ c, (∑ ω : Fin T → RC P, Pool.P0092.wgt (nuD P hL hN) ω * if GF c ω then (0 : ℝ) else 1) ≤
      2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := by
    intro c
    have h := prob_not_goodDS (PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 hL hN hD hLv hlev
      (Pool.P0191.layOK_last P.sl c) hxr hxr1 c hLp T
    convert h using 1
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [wgt_PL P hL hN c ω]
    rfl
  calc _ ≤ ∑ ω : Fin T → RC P, Pool.P0092.wgt (nuD P hL hN) ω *
        ((if GA ω then (0 : ℝ) else 1) + ∑ c : ι, (if GF c ω then (0 : ℝ) else 1)) := by
        refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hw ω)
        have hnn : ∀ c, (0 : ℝ) ≤ if GF c ω then (0 : ℝ) else 1 := fun c => by split_ifs <;> norm_num
        have hS := Finset.sum_nonneg fun c (_ : c ∈ (Finset.univ : Finset ι)) => hnn c
        by_cases hall : GA ω ∧ ∀ c, GF c ω
        · rw [if_pos hall]
          have : (0 : ℝ) ≤ if GA ω then (0 : ℝ) else 1 := by split_ifs <;> norm_num
          linarith
        · rw [if_neg hall]
          by_cases hga : GA ω
          · have : ¬ ∀ c, GF c ω := fun hf => hall ⟨hga, hf⟩
            push_neg at this
            obtain ⟨c, hc⟩ := this
            have h1 := Finset.single_le_sum (f := fun c => if GF c ω then (0 : ℝ) else 1) (fun c _ => hnn c)
              (Finset.mem_univ c)
            simp only [hc, if_false] at h1
            rw [if_pos hga]; linarith
          · rw [if_neg hga]; linarith
    _ = (∑ ω : Fin T → RC P, Pool.P0092.wgt (nuD P hL hN) ω * if GA ω then (0 : ℝ) else 1) +
        ∑ c : ι, ∑ ω : Fin T → RC P, Pool.P0092.wgt (nuD P hL hN) ω * (if GF c ω then (0 : ℝ) else 1) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    _ ≤ Fintype.card ι * (2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L)) +
        ∑ _c : ι, 2 * ((T : ℝ) + 1) ^ 2 * Real.exp (-L) := add_le_add hA (Finset.sum_le_sum fun c _ => hF c)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Pool.P0218
