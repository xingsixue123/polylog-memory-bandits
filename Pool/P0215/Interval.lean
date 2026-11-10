import Pool.P0194.Proc
import Pool.P0186.RecCert

open Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0065

namespace Pool.P0215

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n) (ω : ℕ → RC P)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- P0194's pools are P0065's `tpools` on the process's own data. -/
lemma pool_pools_eq (u : ℕ) : (pool P ℓ ω ωs φ u).pools =
    tpools P.E P.thr0 (Pool.P0156.gChat P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (Pool.P0176.dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ)
      P.θ P.R P.K P.D P.Lv P.Bt P.lev ωs φ u :=
  Pool.P0156.gRun_pools_eq _ _ _ _ _ _ _ _ _ _ _ _ _ u

/-- Retirement is permanent in P0194's pool. -/
lemma aux_succ (u : ℕ) : (pool P ℓ ω ωs φ u).aux ⊆ (pool P ℓ ω ωs φ (u + 1)).aux := by
  intro x hx
  show x ∈ (Pool.P0176.dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω) u _ _ _).2
  simp only [Pool.P0176.dzUpd, Pool.P0176.dzUpdO, Finset.mem_union]
  exact Or.inl hx

lemma aux_mono {u v : ℕ} (huv : u ≤ v) : (pool P ℓ ω ωs φ u).aux ⊆ (pool P ℓ ω ωs φ v).aux := by
  induction v, huv using Nat.le_induction with
  | base => exact le_rfl
  | succ v _ ih => exact ih.trans (aux_succ P ℓ ω ωs φ v)

variable (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
include hD hLv hlev

/-- Start-pool membership at `u` implies entry no later than `u`, and the indices are in range. -/
lemma sp_ok (u : ℕ) : StartOK P.E P.thr0 P.D P.Lv P.Bt u (sp P ℓ ω ωs φ u) := by
  unfold sp
  rw [pool_pools_eq]
  exact start_ok hD hLv (tpools_ok hD hLv hlev ωs φ u) ωs

lemma mem_members_iff (u : ℕ) (x : ι) :
    x ∈ Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u) ↔ ∃ r ℓ', x ∈ sp P ℓ ω ωs φ u r ℓ' := by
  unfold Pool.P0095.members
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨r, -, l, -, h⟩; exact ⟨r, l, h⟩
  · rintro ⟨r, l, h⟩
    obtain ⟨-, -, hl, hr⟩ := sp_ok P ℓ ω ωs φ hD hLv hlev u x r l h
    exact ⟨r, hr, l, hl, h⟩

lemma E_le_of_active {u : ℕ} {x : ι} (h : x ∈ active P ℓ ω ωs φ u) : P.E x ≤ u := by
  unfold active at h
  rw [Finset.mem_sdiff, mem_members_iff P ℓ ω ωs φ hD hLv hlev] at h
  obtain ⟨⟨r, l, h⟩, -⟩ := h
  exact (sp_ok P ℓ ω ωs φ hD hLv hlev u x r l h).1

/-- Once out of the start pools after its entry, a copy never comes back. -/
lemma not_mem_succ {u : ℕ} {x : ι} (hEu : P.E x ≤ u)
    (h : x ∉ Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u)) :
    x ∉ Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ (u + 1)) := by
  rw [mem_members_iff P ℓ ω ωs φ hD hLv hlev] at h ⊢
  push_neg at h ⊢
  -- not in the pools at boundary u + 1
  have hP : ∀ r l, x ∉ (pool P ℓ ω ωs φ (u + 1)).pools r l := by
    intro r l hx
    rw [pool_pools_eq] at hx
    simp only [tpools] at hx
    split_ifs at hx with hdvd
    · obtain ⟨⟨j', hj'⟩, -⟩ := mem_mergeUpTo _ _ _ _ hx
      apply h r j'
      unfold sp; rw [pool_pools_eq]; exact hj'
    · apply h r l
      unfold sp; rw [pool_pools_eq]; exact hx
  intro r l
  unfold sp
  exact not_mem_startPools_of_not_alive hD hP (by omega) r l

/-- **Downward closure.** An active copy at `t2` is active at every `t ∈ [E x, t2]`. -/
lemma active_of_le {x : ι} {t t2 : ℕ} (h2 : x ∈ active P ℓ ω ωs φ t2) (hEt : P.E x ≤ t) (htt : t ≤ t2) :
    x ∈ active P ℓ ω ωs φ t := by
  unfold active at h2 ⊢
  rw [Finset.mem_sdiff] at h2 ⊢
  refine ⟨?_, fun hr => h2.2 (aux_mono P ℓ ω ωs φ htt hr)⟩
  by_contra hnot
  have : ∀ k, x ∉ Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ (t + k)) := by
    intro k
    induction k with
    | zero => simpa using hnot
    | succ k ih => exact not_mem_succ P ℓ ω ωs φ hD hLv hlev (le_trans hEt (Nat.le_add_right t k)) ih
  have := this (t2 - t)
  rw [show t + (t2 - t) = t2 by omega] at this
  exact this h2.1

/-- **Active interval (P0198 for P0194).** A copy active at some round before `T` is active exactly on
`[E x, b)` within the horizon, for some `b` with `E x ≤ b ≤ T`. -/
theorem active_interval (T : ℕ) (x : ι) (hx : ∃ t < T, x ∈ active P ℓ ω ωs φ t) :
    ∃ b, P.E x ≤ b ∧ b ≤ T ∧ ∀ t < T, (x ∈ active P ℓ ω ωs φ t ↔ P.E x ≤ t ∧ t < b) := by
  classical
  obtain ⟨t0, ht0, ha0⟩ := hx
  have hE0 := E_le_of_active P ℓ ω ωs φ hD hLv hlev ha0
  by_cases hex : ∃ t, P.E x ≤ t ∧ t < T ∧ x ∉ active P ℓ ω ωs φ t
  · refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1.le, fun t ht => ?_⟩
    constructor
    · intro hat
      refine ⟨E_le_of_active P ℓ ω ωs φ hD hLv hlev hat, ?_⟩
      by_contra hge
      push_neg at hge
      exact (Nat.find_spec hex).2.2
        (active_of_le P ℓ ω ωs φ hD hLv hlev hat (Nat.find_spec hex).1 hge)
    · rintro ⟨hEt, htb⟩
      by_contra hna
      exact Nat.find_min hex htb ⟨hEt, ht, hna⟩
  · push_neg at hex
    refine ⟨T, by omega, le_rfl, fun t ht => ⟨fun hat => ⟨E_le_of_active P ℓ ω ωs φ hD hLv hlev hat, ht⟩,
      fun h => hex t h.1 ht⟩⟩

/-- **Bridge to P0186.** For P0194's pool, P0186's active presence `PresAct x s s'` on the dzRun inside P0194 is
exactly "active at every round of `[s, s')`" (P0194's `active`). -/
theorem presAct_iff (x : ι) (s s' : ℕ) :
    Pool.P0186.PresAct P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (Pool.P0176.dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ x s s' ↔
      ∀ u, s ≤ u → u < s' → x ∈ active P ℓ ω ωs φ u := by
  unfold Pool.P0186.PresAct Pool.P0186.PresA
  constructor
  · rintro ⟨h1, h2⟩ u hu1 hu2
    unfold active
    rw [Finset.mem_sdiff, mem_members_iff P ℓ ω ωs φ hD hLv hlev]
    exact ⟨h1 u hu1 hu2, h2 u hu1 hu2⟩
  · intro h
    refine ⟨fun u hu1 hu2 => ?_, fun u hu1 hu2 => ?_⟩
    · have := h u hu1 hu2
      unfold active at this
      rw [Finset.mem_sdiff, mem_members_iff P ℓ ω ωs φ hD hLv hlev] at this
      exact this.1
    · have := h u hu1 hu2
      unfold active at this
      rw [Finset.mem_sdiff] at this
      exact this.2

end Pool.P0215
