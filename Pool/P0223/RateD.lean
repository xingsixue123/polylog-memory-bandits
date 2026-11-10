import Pool.P0209.ProbeD
import Pool.P0215.Interval
import Pool.P0191.DZConc

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0065

namespace Pool.P0223

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n) (ω : ℕ → RC P)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

theorem occAtS_eq_some {u : ℕ} {s : Σ j : Fin P.D, Fin (P.sl j)} {x : ι} :
    occAtS P ℓ ω ωs φ u s = some x ↔
      P.lay s.1 (blockMem P.Lv (sp P ℓ ω ωs φ u) s.1) s.2 = some x ∧ x ∉ (pool P ℓ ω ωs φ u).aux := by
  unfold occAtS
  rcases h : P.lay s.1 (blockMem P.Lv (sp P ℓ ω ωs φ u) s.1) s.2 with _ | y
  · simp
  · simp only [Option.some.injEq]
    split_ifs with hy
    · simp only [reduceCtorEq, false_iff, not_and, not_not]
      intro e; subst e; exact hy
    · constructor
      · intro e; cases e; exact ⟨rfl, hy⟩
      · rintro ⟨e, -⟩; rw [e]

theorem mem_members_of_block {u : ℕ} {j : Fin P.D} {x : ι} (h : x ∈ blockMem P.Lv (sp P ℓ ω ωs φ u) j) :
    x ∈ Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u) := by
  unfold blockMem at h
  unfold Pool.P0095.members
  simp only [Finset.mem_biUnion, Finset.mem_range] at h ⊢
  exact ⟨j, j.2, h⟩

/-- An inactive copy has rate `0`. -/
theorem rateD_inactive (hlay : Pool.P0191.LayOK P.sl P.lay) {u : ℕ} {x : ι} (hx : x ∉ active P ℓ ω ωs φ u) :
    Pool.P0209.rateD P ℓ ωs φ ω u x = 0 := by
  unfold Pool.P0209.rateD
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [if_neg]
  intro h
  rw [occAtS_eq_some] at h
  apply hx
  unfold active
  rw [Finset.mem_sdiff]
  exact ⟨mem_members_of_block P ℓ ω ωs φ (hlay.mem _ _ _ _ h.1), h.2⟩

variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
include hD hLv hlev

/-- Block membership pins the thread: a member of thread `j`'s block at round `u` sits in its current thread. -/
theorem block_thread {u : ℕ} {j : Fin P.D} {x : ι} (h : x ∈ blockMem P.Lv (sp P ℓ ω ωs φ u) j) :
    (j : ℕ) = curT P.E P.thr0 P.D P.Bt x u := by
  unfold blockMem at h
  simp only [Finset.mem_biUnion, Finset.mem_range] at h
  obtain ⟨l, -, hl⟩ := h
  exact (Pool.P0215.sp_ok P ℓ ω ωs φ hD hLv hlev u x j l hl).2.1

/-- An active copy's current thread is a thread index. -/
theorem curT_lt {u : ℕ} {x : ι} (hx : x ∈ active P ℓ ω ωs φ u) : curT P.E P.thr0 P.D P.Bt x u < P.D := by
  unfold active at hx
  rw [Finset.mem_sdiff, Pool.P0215.mem_members_iff P ℓ ω ωs φ hD hLv hlev] at hx
  obtain ⟨⟨r, l, h⟩, -⟩ := hx
  obtain ⟨-, hr, -, hrD⟩ := Pool.P0215.sp_ok P ℓ ω ωs φ hD hLv hlev u x r l h
  rw [← hr]; exact hrD

/-- **Rate of an active copy**: when every thread fits and the layouts place each member once, an active copy's rate
is the slot weight of its current thread. -/
theorem rateD_active (hlay : Pool.P0191.LayOK P.sl P.lay) {u : ℕ} (hfit : Fits P.Lv P.sl (sp P ℓ ω ωs φ u))
    {x : ι} (hx : x ∈ active P ℓ ω ωs φ u) :
    Pool.P0209.rateD P ℓ ωs φ ω u x = P.xr ⟨curT P.E P.thr0 P.D P.Bt x u, curT_lt P ℓ ω ωs φ hD hLv hlev hx⟩ := by
  classical
  set j0 : Fin P.D := ⟨curT P.E P.thr0 P.D P.Bt x u, curT_lt P ℓ ω ωs φ hD hLv hlev hx⟩
  have hret : x ∉ (pool P ℓ ω ωs φ u).aux := (Finset.mem_sdiff.mp hx).2
  have hmem : x ∈ blockMem P.Lv (sp P ℓ ω ωs φ u) j0 := by
    have h := (Finset.mem_sdiff.mp hx).1
    rw [Pool.P0215.mem_members_iff P ℓ ω ωs φ hD hLv hlev] at h
    obtain ⟨r, l, hrl⟩ := h
    obtain ⟨-, hr, hl, -⟩ := Pool.P0215.sp_ok P ℓ ω ωs φ hD hLv hlev u x r l hrl
    unfold blockMem
    simp only [Finset.mem_biUnion, Finset.mem_range]
    refine ⟨l, hl, ?_⟩
    have : (j0 : ℕ) = r := hr.symm
    rw [this]; exact hrl
  unfold Pool.P0209.rateD
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j0]
  · have : ∀ k : Fin (P.sl j0), (if occAtS P ℓ ω ωs φ u ⟨j0, k⟩ = some x then P.xr j0 else 0)
        = if P.lay j0 (blockMem P.Lv (sp P ℓ ω ωs φ u) j0) k = some x then P.xr j0 else 0 := by
      intro k
      simp only [occAtS_eq_some, hret, not_false_eq_true, and_true]
    rw [Finset.sum_congr rfl fun k _ => this k, ← Finset.sum_filter, Finset.sum_const,
      hlay.one j0 _ x (hfit j0) hmem, one_smul]
  · intro j _ hj
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]
    intro h
    rw [occAtS_eq_some] at h
    have hb := block_thread P ℓ ω ωs φ hD hLv hlev (hlay.mem _ _ _ _ h.1)
    exact hj (Fin.ext hb)
  · simp

end Pool.P0223
