import Pool.P0201.Machine

/-!
# C10: the dzRun machine runs P0194's process (pathwise correspondence)
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0065 Pool.P0052 Pool.P0194 Pool.P0201

namespace Pool.P0206

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (m : MPar n ι)
  (ℓ : LossSeq n) (ω : ℕ → Yc m × Zc m)
/-- P0194's round coins read off the machine's coins (process round `u` = machine round `u + 1`). -/
def ωR (u : ℕ) : RC m.P := ((ω (u + 1)).1.1, (ω (u + 1)).1.2.1, (ω (u + 1)).1.2.2, (ω (u + 1)).2.1)
/-- The process's losses: process round `u` is machine round `u + 1`. -/
def sh (ℓ : LossSeq n) : LossSeq n := fun u => ℓ (u + 1)
/-- Sampling coins: copy `c` is sampled by the update coin of machine round `E c` (the dummy round `0` for `E c = 0`). -/
def ωsM (c : ι) : Bool := (ω (m.P.E c)).2.2 (Sum.inr c)
/-- Filter coins: merges at the end of process round `a` read the update coin of machine round `a + 1`. -/
def φM (r a : ℕ) : ℕ → Fin m.P.K → ι → Bool := Pool.P0104.φz (pp m) (ω (a + 1)).2.2 r a
/-- The process state at boundary `u`. -/
noncomputable abbrev Zr (u : ℕ) := pool m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u
/-- The process start pools of round `u`. -/
noncomputable abbrev SPu (u : ℕ) := sp m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u
/-- BASE's loss count before round `u`. -/
def kBc : ℕ → ℕ
  | 0 => 0
  | u + 1 => kBc u + if isB m.P (ωR m ω u).1 then (sh ℓ u (bAct m.P (sh ℓ) (ωR m ω) u)).toNat else 0
theorem Bh_eq : ∀ u, Bh m.P (sh ℓ) (ωR m ω) u = m.P.cB * (kBc m ℓ ω u : ℝ)
  | 0 => by simp [Bh, kBc]
  | u + 1 => by
    rw [Bh, Bh_eq u, kBc]
    split_ifs <;> push_cast <;> ring
theorem kBc_le : ∀ u, kBc m ℓ ω u ≤ u
  | 0 => le_rfl
  | u + 1 => by
    have := kBc_le u
    rw [kBc]
    split_ifs
    · have : (sh ℓ u (bAct m.P (sh ℓ) (ωR m ω) u)).toNat ≤ 1 := by cases sh ℓ u (bAct m.P (sh ℓ) (ωR m ω) u) <;> simp
      omega
    · omega
/-- Regime of the correspondence. -/
structure Hyp : Prop where
  hD : 0 < m.P.D
  hLv : 0 < m.P.Lv
  hlev : ∀ r a, m.P.lev r a + 1 < m.P.Lv
  hkx : ∀ j, 0 < m.kx j ∧ m.P.xr j = 1 / (m.kx j : ℝ)

variable {m}
theorem SPu_ok (h : Hyp m) (u : ℕ) :
    StartOK m.P.E m.P.thr0 m.P.D m.P.Lv m.P.Bt u (SPu m ℓ ω u) := by
  show StartOK _ _ _ _ _ u (startPools _ _ _ _ _ _ u (Zr m ℓ ω u).pools)
  rw [show (Zr m ℓ ω u).pools = _ from Pool.P0156.gRun_pools_eq _ _ _ _ _ _ _ _ _ _ _ _ _ u]
  exact start_ok h.hD h.hLv (tpools_ok h.hD h.hLv h.hlev _ _ u) _
theorem SPu_inRange (h : Hyp m) (u : ℕ) : Pool.P0104.InRange (pp m) (SPu m ℓ ω u) := by
  intro r l hr
  ext c
  simp only [Finset.notMem_empty, iff_false]
  intro hc
  have := SPu_ok ℓ ω h u c r l hc
  change m.P.D ≤ r ∨ m.P.Lv ≤ l at hr
  omega
theorem SPu_E_le (h : Hyp m) {u r l : ℕ} {c : ι} (hc : c ∈ SPu m ℓ ω u r l) : m.P.E c ≤ u :=
  (SPu_ok ℓ ω h u c r l hc).1
theorem mem_members_SPu (h : Hyp m) {u : ℕ} {c : ι} :
    c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω u) ↔ ∃ r l, c ∈ SPu m ℓ ω u r l := by
  simp only [Pool.P0095.members, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨r, _, l, _, hc⟩; exact ⟨r, l, hc⟩
  · rintro ⟨r, l, hc⟩
    have := SPu_ok ℓ ω h u c r l hc
    exact ⟨r, this.2.2.2, l, this.2.2.1, hc⟩
/-- The invariant: the machine's state at round `u` holds the process's start pools, the data since entry, the
retired flags and BASE counts at entry, BASE's state and count, ALG's state and the clock. -/
def Inv (u : ℕ) (s : St m) : Prop :=
  s.1.1.1 = Pool.P0104.mkP (pp m) (SPu m ℓ ω u) ∧
  (∀ c ∈ Pool.P0078.U s.1.1, ∀ d ∈ Pool.P0078.U s.1.1, m.P.E c ≤ m.P.E d →
    ((s.1.1.2.1 c d : ℕ) : ℝ) = (Zr m ℓ ω u).est c u - (Zr m ℓ ω u).est c (m.P.E d)) ∧
  (∀ c ∈ Pool.P0078.U s.1.1, retF m s.1.1 c = (if c ∈ (Zr m ℓ ω u).aux then 1 else 0) ∧
    (kE m s.1.1 c : ℕ) = kBc m ℓ ω (m.P.E c)) ∧
  s.2.1 = sB m.P (sh ℓ) (ωR m ω) u ∧ (s.2.2.1 : ℕ) = kBc m ℓ ω u ∧
  s.2.2.2.1 = sA m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u ∧ (s.2.2.2.2 : ℕ) = u + 1

section InvLemmas

variable {ℓ ω} {u : ℕ} {s : St m}
theorem clock_ne (hs : Inv ℓ ω u s) : (s.2.2.2.2 : ℕ) ≠ 0 := by rw [hs.2.2.2.2.2.2]; omega
theorem rd_of_inv (hs : Inv ℓ ω u s) : rd m s = u := by unfold rd; rw [hs.2.2.2.2.2.2]; omega
theorem U_of_inv (h : Hyp m) (hs : Inv ℓ ω u s) (c : ι) :
    c ∈ Pool.P0078.U s.1.1 ↔ c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω u) := by
  rw [Pool.P0078.U, hs.1, Pool.P0104.mem_U_mkP (pp m) h.hD h.hLv (SPu_inRange ℓ ω h u),
    mem_members_SPu ℓ ω h]
theorem memb_of_inv (h : Hyp m) (hs : Inv ℓ ω u s) :
    memb m s.1.1 = Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω u) := by
  unfold memb
  congr 1
  funext r l
  exact Pool.P0104.pl_eq_of (pp m) h.hD h.hLv (SPu_inRange ℓ ω h u) s.1.1 hs.1 r l
theorem retS_of_inv (h : Hyp m) (hs : Inv ℓ ω u s) (c : ι) :
    c ∈ retS m s.1.1 ↔ c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω u) ∧ c ∈ (Zr m ℓ ω u).aux := by
  unfold retS
  rw [Finset.mem_filter, memb_of_inv h hs]
  constructor
  · rintro ⟨hm, hr⟩
    refine ⟨hm, ?_⟩
    have := (hs.2.2.1 c ((U_of_inv h hs c).2 hm)).1
    rw [hr] at this
    by_contra hx
    rw [if_neg hx] at this
    exact absurd this (by decide)
  · rintro ⟨hm, hx⟩
    refine ⟨hm, ?_⟩
    rw [(hs.2.2.1 c ((U_of_inv h hs c).2 hm)).1, if_pos hx]
theorem actv_of_inv (h : Hyp m) (hs : Inv ℓ ω u s) :
    actv m s.1.1 = active m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u := by
  ext c
  unfold actv active
  simp only [Finset.mem_sdiff]
  rw [memb_of_inv h hs, retS_of_inv h hs]
  constructor
  · rintro ⟨hm, hr⟩; exact ⟨hm, fun hx => hr ⟨hm, hx⟩⟩
  · rintro ⟨hm, hx⟩; exact ⟨hm, fun hr => hx hr.2⟩
theorem bA_of_inv (hs : Inv ℓ ω u s) : bA m s (ω (u + 1)).1 = bAct m.P (sh ℓ) (ωR m ω) u := by
  unfold bA bAct; rw [hs.2.2.2.1]; rfl
theorem blk_of_inv (h : Hyp m) (hs : Inv ℓ ω u s) (j : ℕ) :
    blk m s.1.1 j = Pool.P0176.blockMem m.P.Lv (SPu m ℓ ω u) j := by
  unfold blk Pool.P0176.blockMem
  congr 1
  funext l
  exact Pool.P0104.pl_eq_of (pp m) h.hD h.hLv (SPu_inRange ℓ ω h u) s.1.1 hs.1 j l
theorem occM_of_inv (h : Hyp m) (hs : Inv ℓ ω u s) (sl : Σ j : Fin m.P.D, Fin (m.P.sl j)) :
    occM m s sl = occAtS m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u sl := by
  unfold occM occAtS
  rw [blk_of_inv h hs]
  rcases ho : m.P.lay sl.1 (Pool.P0176.blockMem m.P.Lv (SPu m ℓ ω u) sl.1) sl.2 with _ | c
  · rfl
  · simp only
    have hm : c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω u) :=
      Pool.P0176.mem_blockMem_members m.P.Lv sl.1.2 (m.P.lay_mem _ _ _ _ ho)
    by_cases hx : c ∈ (Zr m ℓ ω u).aux
    · rw [if_pos ((retS_of_inv h hs c).2 ⟨hm, hx⟩), if_pos hx]
    · rw [if_neg (fun hr => hx ((retS_of_inv h hs c).1 hr).2), if_neg hx]
theorem chM_of_inv (h : Hyp m) (hs : Inv ℓ ω u s) :
    chM m s (ω (u + 1)).1 = algCh m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u := by
  unfold chM algCh; rw [actv_of_inv h hs, hs.2.2.2.2.2.1]; rfl
/-- **The machine plays the process's arm.** -/
theorem playM_of_inv (h : Hyp m) (hs : Inv ℓ ω u s) :
    playM m s (ω (u + 1)).1 = play m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u := by
  have harm : ∀ o, armM m s (ω (u + 1)).1 o = armOf m.P (sh ℓ) (ωR m ω) u o := by
    intro o; cases o with
    | none => exact bA_of_inv hs
    | some c => rfl
  rw [playM_of_ne (clock_ne hs)]
  rcases hk : (ω (u + 1)).1.1 with _ | _ | sl
  · simp only [play, ωR, hk]; exact bA_of_inv hs
  · simp only [play, ωR, hk]; rw [harm, chM_of_inv h hs]
  · simp only [play, ωR, hk]; rw [harm, occM_of_inv h hs]

end InvLemmas

section ProcStep

variable {ℓ ω}
/-- The process increment of round `u` (P0176's `dzIncO`). -/
noncomputable def incZ (u : ℕ) (c : ι) : ℝ :=
  Pool.P0176.dzIncO m.P.D 1 1 m.P.xr (ℓr m.P (sh ℓ)) u (Zr m ℓ ω u).aux
    (fun t => Pool.P0176.obsR m.P.D m.P.Lv m.P.sl m.P.lay (SPu m ℓ ω u) (zc m.P (ωR m ω) u t)) c
theorem Zr_succ_est (u : ℕ) : (Zr m ℓ ω (u + 1)).est = Pool.P0156.gStep u (incZ (ℓ := ℓ) (ω := ω) u)
    (Zr m ℓ ω u).est := rfl
theorem Zr_succ_pools (u r : ℕ) : (Zr m ℓ ω (u + 1)).pools r =
    if m.P.Bt r ∣ u + 1 then
      mergeUpTo m.P.E (Zr m ℓ ω (u + 1)).est m.P.θ m.P.R m.P.K (φM m ω r) u (m.P.lev r u) (SPu m ℓ ω u r)
    else SPu m ℓ ω u r := rfl
theorem est_succ_top (u : ℕ) (c : ι) :
    (Zr m ℓ ω (u + 1)).est c (u + 1) = (Zr m ℓ ω u).est c u + incZ (ℓ := ℓ) (ω := ω) u c := by
  rw [Zr_succ_est]; simp [Pool.P0156.gStep]
theorem est_succ_le {u t : ℕ} (ht : t ≤ u) (c : ι) :
    (Zr m ℓ ω (u + 1)).est c t = (Zr m ℓ ω u).est c t := by
  rw [Zr_succ_est]; simp [Pool.P0156.gStep, ht]
theorem mem_aux_succ' (u : ℕ) (c : ι) :
    c ∈ (Zr m ℓ ω (u + 1)).aux ↔ c ∈ (Zr m ℓ ω u).aux ∨
      (c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω u) ∧
        rhD m.P (sh ℓ) (ωR m ω) u c ((Zr m ℓ ω (u + 1)).est c) = true) := by
  show c ∈ (Pool.P0176.dzUpd m.P.D m.P.Lv m.P.sl 1 1 m.P.xr (ℓr m.P (sh ℓ)) (rhD m.P (sh ℓ) (ωR m ω)) m.P.lay
    (zc m.P (ωR m ω)) u (SPu m ℓ ω u) (Zr m ℓ ω u).est (Zr m ℓ ω u).aux).2 ↔ _
  simp only [Pool.P0176.dzUpd, Pool.P0176.dzUpdO, Finset.mem_union, Finset.mem_filter]
  rfl
/-- Retired copies were members before. -/
theorem E_lt_of_aux (h : Hyp m) : ∀ {u : ℕ} {c : ι}, c ∈ (Zr m ℓ ω u).aux → m.P.E c < u
  | 0, c, hc => by
    have h0 : (Zr m ℓ ω 0).aux = ∅ := rfl
    rw [h0] at hc; simp at hc
  | u + 1, c, hc => by
    rcases (mem_aux_succ' u c).1 hc with hc | ⟨hm, _⟩
    · have := E_lt_of_aux h hc; omega
    · obtain ⟨r, l, hrl⟩ := (mem_members_SPu ℓ ω h).1 hm
      have := SPu_E_le ℓ ω h hrl; omega
/-- A copy in the start pools of round `u + 1` but not of round `u` entered at `u + 1`. -/
theorem E_of_new (h : Hyp m) {u : ℕ} {c : ι}
    (h1 : c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω (u + 1)))
    (h0 : c ∉ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω u)) : m.P.E c = u + 1 := by
  obtain ⟨r, l, hc⟩ := (mem_members_SPu ℓ ω h).1 h1
  have hle := SPu_E_le ℓ ω h hc
  by_contra hne
  have hnot : ∀ r l, c ∉ (Zr m ℓ ω (u + 1)).pools r l := by
    intro r' l' hc'
    apply h0
    rw [mem_members_SPu ℓ ω h]
    rw [Zr_succ_pools] at hc'
    split_ifs at hc'
    · obtain ⟨i, hi⟩ := Pool.P0063.mem_mergeUpTo _ _ _ _ _ _ _ _ _ _ c hc'
      exact ⟨r', i, hi⟩
    · exact ⟨r', l', hc'⟩
  exact not_mem_startPools_of_not_alive h.hD hnot hne r l hc
theorem est_eq_sum (c : ι) : ∀ u, ∀ t ≤ u, (Zr m ℓ ω u).est c t = ∑ w ∈ range t, incZ (ℓ := ℓ) (ω := ω) w c
  | 0, t, ht => by
    rw [Nat.le_zero.mp ht]; simp [Zr, pool, Pool.P0156.gRun]
  | u + 1, t, ht => by
    rcases Nat.lt_or_eq_of_le ht with ht | ht
    · rw [est_succ_le (by omega)]; exact est_eq_sum c u t (by omega)
    · subst ht; rw [est_succ_top, est_eq_sum c u u le_rfl, Finset.sum_range_succ]

end ProcStep

section Step

variable {ℓ ω} {u : ℕ} {s : St m}
/-- The observed bit of round `u`. -/
noncomputable abbrev bU (s : St m) : Bool := ℓ (u + 1) (playM m s (ω (u + 1)).1)
/-- **The machine's increments are the process's** on the start-pool members. -/
theorem βM_eq (h : Hyp m) (hs : Inv ℓ ω u s) {c : ι}
    (hc : c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω u)) :
    ((βM m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) c : ℕ) : ℝ) = incZ (ℓ := ℓ) (ω := ω) u c := by
  unfold βM incZ Pool.P0176.dzIncO
  by_cases hx : c ∈ (Zr m ℓ ω u).aux
  · rw [if_pos ((retS_of_inv h hs c).2 ⟨hc, hx⟩), if_pos hx]; simp
  · rw [if_neg (fun hr => hx ((retS_of_inv h hs c).1 hr).2), if_neg hx]
    rw [Fin.sum_univ_one]
    simp only [zc, ωR]
    rcases hk : (ω (u + 1)).1.1 with _ | _ | sl
    · simp [Pool.P0176.obsR, Pool.P0176.dzC]
    · simp [Pool.P0176.obsR, Pool.P0176.dzC]
    · simp only [Option.getD_some]
      rw [blk_of_inv h hs]
      rcases ho : m.P.lay sl.1 (Pool.P0176.blockMem m.P.Lv (SPu m ℓ ω u) sl.1) sl.2 with _ | y
      · simp [Pool.P0176.obsR, Pool.P0176.dzC, ho]
      · by_cases hyc : y = c
        · subst hyc
          have hplay : playM m s (ω (u + 1)).1 = m.P.arm y := by
            rw [playM_of_inv h hs]
            simp only [play, ωR, hk]
            unfold occAtS
            rw [ho]
            simp only [if_neg hx]
            rfl
          simp only [Pool.P0176.obsR, ho, Option.map_some, Pool.P0176.dzC, if_true]
          unfold bU ℓr
          rw [hplay, (h.hkx sl.1).2]
          have hk0 : (m.kx sl.1 : ℝ) ≠ 0 := by exact_mod_cast (h.hkx sl.1).1.ne'
          simp only [Nat.mul_one, Nat.add_zero, Fin.val_zero]
          push_cast
          field_simp
          rfl
        · simp [Pool.P0176.obsR, Pool.P0176.dzC, ho, hyc]
theorem bp_le (hU : ∀ d ∈ Pool.P0078.U s.1.1, m.P.E d ≤ u) {e : ℕ}
    (he : e ∈ Pool.P0068.bp m.P.E (u + 1) (Pool.P0078.U s.1.1)) : e ≤ u + 1 := by
  rcases he with rfl | ⟨g, hg, rfl⟩
  · exact le_rfl
  · have := hU g hg; omega
/-- The rebuilt cover data agree with the process data on every interval a merge reads. -/
theorem agree_Cm (h : Hyp m) (hs : Inv ℓ ω u s) :
    Pool.P0068.AgreeOn m.P.E
      (Pool.P0104.Cm (pp m) (Pool.P0078.U s.1.1)
        (fun c d => (s.1.1.2.1 c d : ℕ) + βM m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) c) u)
      (Zr m ℓ ω (u + 1)).est (Pool.P0078.U s.1.1) (Pool.P0068.bp m.P.E (u + 1) (Pool.P0078.U s.1.1)) := by
  have hUE : ∀ d ∈ Pool.P0078.U s.1.1, m.P.E d ≤ u := fun d hd => by
    obtain ⟨r, l, hrl⟩ := (mem_members_SPu ℓ ω h).1 ((U_of_inv h hs d).1 hd)
    exact SPu_E_le ℓ ω h hrl
  have hDt : ∀ c ∈ Pool.P0078.U s.1.1, ∀ d ∈ Pool.P0078.U s.1.1, (pp m).E c ≤ (pp m).E d →
      ((((s.1.1.2.1 c d : ℕ) + βM m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) c : ℕ)) : ℝ) =
        ∑ w ∈ Ico ((pp m).E d) (u + 1), incZ (ℓ := ℓ) (ω := ω) w c := by
    intro c hc d hd hcd
    push_cast
    rw [hs.2.1 c hc d hd hcd, βM_eq h hs ((U_of_inv h hs c).1 hc),
      est_eq_sum c u u le_rfl, est_eq_sum c u _ (hUE d hd)]
    show _ = ∑ w ∈ Ico (m.P.E d) (u + 1), incZ (ℓ := ℓ) (ω := ω) w c
    rw [Finset.sum_Ico_succ_top (hUE d hd), Finset.sum_Ico_eq_sub _ (hUE d hd)]
  have hag := Pool.P0104.agreeOn_Cm (p := pp m) hUE hDt
  intro f hf e₁ he₁ e₂ he₂ h1 h2
  rw [hag f hf e₁ he₁ e₂ he₂ h1 h2]
  unfold Pool.P0030.Lint Pool.P0061.cumL
  rw [est_eq_sum f (u + 1) e₂ (bp_le hUE he₂), est_eq_sum f (u + 1) e₁ (bp_le hUE he₁)]
/-- Sampling for round `u + 1` reads only the update coin of round `u` of copies entering at `u + 1`. -/
theorem startPools_ωz' (h : Hyp m) (P : ℕ → ℕ → Finset ι) :
    startPools m.P.E m.P.thr0 m.P.D m.P.Lv m.P.Bt (Pool.P0104.ωz (pp m) (ω (u + 1)).2.2) (u + 1) P =
      startPools m.P.E m.P.thr0 m.P.D m.P.Lv m.P.Bt (ωsM m ω) (u + 1) P := by
  have : newAtT m.P.E m.P.thr0 (Pool.P0104.ωz (pp m) (ω (u + 1)).2.2) (u + 1) =
      newAtT m.P.E m.P.thr0 (ωsM m ω) (u + 1) := by
    funext r
    unfold newAtT
    refine Finset.filter_congr fun c _ => ?_
    simp only [Pool.P0104.ωz, ωsM]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h1]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h1] at h3; exact h3⟩
  unfold startPools sample
  rw [this]
/-- **Pool step**: the machine's merges (cover data rebuilt from the table) and the inheritance/sampling with the
round's update coin give the process's start pools of round `u + 1`. -/
theorem pools_step (h : Hyp m) (hs : Inv ℓ ω u s) :
    startPools m.P.E m.P.thr0 m.P.D m.P.Lv m.P.Bt (Pool.P0104.ωz (pp m) (ω (u + 1)).2.2) (u + 1) (fun r =>
      if m.P.Bt r ∣ u + 1 then
        mergeUpTo m.P.E (Pool.P0104.Cm (pp m) (Pool.P0078.U s.1.1)
          (fun c d => (s.1.1.2.1 c d : ℕ) + βM m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) c) u)
          m.P.θ m.P.R m.P.K (Pool.P0104.φz (pp m) (ω (u + 1)).2.2 r) u (m.P.lev r u) (Pool.P0104.pl (pp m) s.1.1 r)
      else Pool.P0104.pl (pp m) s.1.1 r) = SPu m ℓ ω (u + 1) := by
  rw [startPools_ωz' h]
  show _ = startPools _ _ _ _ _ _ (u + 1) (Zr m ℓ ω (u + 1)).pools
  congr 1
  funext r
  rw [Zr_succ_pools]
  have hpl : Pool.P0104.pl (pp m) s.1.1 r = SPu m ℓ ω u r := funext fun l =>
    Pool.P0104.pl_eq_of (pp m) h.hD h.hLv (SPu_inRange ℓ ω h u) s.1.1 hs.1 r l
  rw [hpl]
  split_ifs
  · refine (Pool.P0078.mergeUpTo_congrC (pp m).E _ _ (pp m).θ (pp m).R (pp m).K
      (Pool.P0104.φz (pp m) (ω (u + 1)).2.2 r) u _ (agree_Cm h hs) (m.P.lev r u)
      (SPu m ℓ ω u r) (fun l c hc => (U_of_inv h hs c).2 ((mem_members_SPu ℓ ω h).2 ⟨r, l, hc⟩))).trans ?_
    exact Pool.P0104.mergeUpTo_congr_time (pp m) (φ := Pool.P0104.φz (pp m) (ω (u + 1)).2.2 r) (φ' := φM m ω r) u
      rfl _ _
  · rfl
theorem incZ_bounds (h : Hyp m) {W : ℕ} (hW1 : 1 ≤ W) (hW : ∀ j, m.kx j ≤ W) (v : ℕ) (c : ι) :
    0 ≤ incZ (ℓ := ℓ) (ω := ω) v c ∧ incZ (ℓ := ℓ) (ω := ω) v c ≤ W := by
  unfold incZ Pool.P0176.dzIncO
  split_ifs
  · exact ⟨zero_le_one, by exact_mod_cast hW1⟩
  · rw [Fin.sum_univ_one]
    simp only [Pool.P0176.dzC]
    split
    · exact ⟨le_rfl, by positivity⟩
    · next j y _ =>
      split_ifs
      · rw [(h.hkx j).2, div_div_eq_mul_div, div_one]
        unfold ℓr
        have hb : ((sh ℓ (v * 1 + ↑(0 : Fin 1)) (m.P.arm c)).toNat : ℝ) ≤ 1 := by
          cases sh ℓ (v * 1 + ↑(0 : Fin 1)) (m.P.arm c) <;> simp
        have hk : (m.kx j : ℝ) ≤ W := by exact_mod_cast hW j
        constructor
        · positivity
        · calc ((sh ℓ (v * 1 + ↑(0 : Fin 1)) (m.P.arm c)).toNat : ℝ) * (m.kx j : ℝ) ≤ 1 * (m.kx j : ℝ) :=
              mul_le_mul_of_nonneg_right hb (by positivity)
            _ ≤ W := by rw [one_mul]; exact hk
      · exact ⟨le_rfl, by positivity⟩
theorem kBn_eq (h : Hyp m) (hs : Inv ℓ ω u s) :
    kBn m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) = kBc m ℓ ω (u + 1) := by
  unfold kBn
  rw [kBc, ← hs.2.2.2.2.1]
  show (if isB m.P (ω (u + 1)).1.1 = true then _ else _) = _ + if isB m.P (ω (u + 1)).1.1 = true then _ else 0
  by_cases hb : isB m.P (ω (u + 1)).1.1 = true
  · rw [if_pos hb, if_pos hb]
    have hn : (ω (u + 1)).1.1 = none := by
      unfold isB at hb; exact Option.isNone_iff_eq_none.mp hb
    have : playM m s (ω (u + 1)).1 = bAct m.P (sh ℓ) (ωR m ω) u := by
      rw [playM_of_inv h hs]; simp only [play, ωR, hn]
    unfold bU; rw [this]; rfl
  · rw [if_neg hb, if_neg hb]; simp
/-- The raw pool data after round `u`. -/
noncomputable abbrev rawN (s : St m) : Raw m := poolUpd m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) (ω (u + 1)).2.2
theorem rawN_fst (h : Hyp m) (hs : Inv ℓ ω u s) :
    (rawN (ℓ := ℓ) (ω := ω) (u := u) s).1 = Pool.P0104.mkP (pp m) (SPu m ℓ ω (u + 1)) := by
  have hc : rd m s = u := rd_of_inv hs
  simp only [rawN, poolUpd, hc]
  rw [pools_step h hs]
theorem mem_U_rawN (h : Hyp m) (hs : Inv ℓ ω u s) (c : ι) :
    c ∈ Pool.P0078.U (rawN (ℓ := ℓ) (ω := ω) (u := u) s) ↔
      c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω (u + 1)) := by
  rw [Pool.P0078.U, rawN_fst h hs, Pool.P0104.mem_U_mkP (pp m) h.hD h.hLv (SPu_inRange ℓ ω h (u + 1)),
    mem_members_SPu ℓ ω h]
theorem rawN_table (h : Hyp m) (hs : Inv ℓ ω u s) (c d : ι) :
    (rawN (ℓ := ℓ) (ω := ω) (u := u) s).2.1 c d =
      if c ∈ Pool.P0078.U (rawN (ℓ := ℓ) (ω := ω) (u := u) s) ∧ d ∈ Pool.P0078.U (rawN (ℓ := ℓ) (ω := ω) (u := u) s) ∧
          c ∈ Pool.P0078.U s.1.1 ∧ d ∈ Pool.P0078.U s.1.1 then
        Pool.P0104.capF m.TT ((s.1.1.2.1 c d : ℕ) + βM m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) c) else 0 := by
  have hc : rd m s = u := rd_of_inv hs
  have hU := rawN_fst h hs
  simp only [rawN, poolUpd, hc]
  congr
theorem rawN_code (h : Hyp m) (hs : Inv ℓ ω u s) (c : ι) :
    (rawN (ℓ := ℓ) (ω := ω) (u := u) s).2.2 c =
      if c ∈ Pool.P0078.U (rawN (ℓ := ℓ) (ω := ω) (u := u) s) then
        Pool.P0104.encH (pp m) (fun _ => if c ∈ Pool.P0078.U s.1.1 then
          ((if c ∈ retN m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) then 1 else 0), kE m s.1.1 c)
          else (0, Pool.P0104.capF m.TB (kBn m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s))))
      else 0 := by
  have hc : rd m s = u := rd_of_inv hs
  have hU := rawN_fst h hs
  simp only [rawN, poolUpd, hc]
  congr
theorem E_le_of_U (h : Hyp m) (hs : Inv ℓ ω u s) {d : ι} (hd : d ∈ Pool.P0078.U s.1.1) : m.P.E d ≤ u := by
  obtain ⟨r, l, hrl⟩ := (mem_members_SPu ℓ ω h).1 ((U_of_inv h hs d).1 hd)
  exact SPu_E_le ℓ ω h hrl
/-- The updated table entry is the process data since the later entry. -/
theorem tab_step (h : Hyp m) (hs : Inv ℓ ω u s) {c d : ι} (hc : c ∈ Pool.P0078.U s.1.1)
    (hd : d ∈ Pool.P0078.U s.1.1) (hcd : m.P.E c ≤ m.P.E d) :
    ((((s.1.1.2.1 c d : ℕ) + βM m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) c : ℕ)) : ℝ) =
      (Zr m ℓ ω (u + 1)).est c (u + 1) - (Zr m ℓ ω (u + 1)).est c (m.P.E d) := by
  push_cast
  rw [hs.2.1 c hc d hd hcd, βM_eq h hs ((U_of_inv h hs c).1 hc), est_succ_top,
    est_succ_le (E_le_of_U h hs hd)]
  ring
theorem data_le (h : Hyp m) {W : ℕ} (hW1 : 1 ≤ W) (hW : ∀ j, m.kx j ≤ W) (c : ι) {e : ℕ}
    (he : e ≤ u + 1) :
    0 ≤ (Zr m ℓ ω (u + 1)).est c (u + 1) - (Zr m ℓ ω (u + 1)).est c e ∧
      (Zr m ℓ ω (u + 1)).est c (u + 1) - (Zr m ℓ ω (u + 1)).est c e ≤ (u + 1) * W := by
  rw [est_eq_sum c (u + 1) (u + 1) le_rfl, est_eq_sum c (u + 1) e he, ← Finset.sum_Ico_eq_sub _ he]
  constructor
  · exact Finset.sum_nonneg fun w _ => (incZ_bounds h hW1 hW w c).1
  · calc ∑ w ∈ Ico e (u + 1), incZ (ℓ := ℓ) (ω := ω) w c ≤ ∑ w ∈ Ico e (u + 1), (W : ℝ) :=
          Finset.sum_le_sum fun w _ => (incZ_bounds h hW1 hW w c).2
      _ = ((u + 1 - e : ℕ) : ℝ) * W := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (u + 1) * W := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (u + 1 - e : ℕ) ≤ u + 1 := Nat.sub_le _ _
          exact_mod_cast this
theorem capF_val {M v : ℕ} (hv : v ≤ M) : (Pool.P0104.capF M v : ℕ) = v := by
  simp [Pool.P0104.capF, hv]
/-- The machine's retirement rule is the process's rule (b″). -/
theorem retN_iff (h : Hyp m) (hs : Inv ℓ ω u s) {c : ι}
    (hc : c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω u)) :
    c ∈ retN m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) ↔ c ∈ (Zr m ℓ ω (u + 1)).aux := by
  have hcU := (U_of_inv h hs c).2 hc
  have hE : m.P.E c ≤ u := E_le_of_U h hs hcU
  have hrh : rhM m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) c =
      rhD m.P (sh ℓ) (ωR m ω) u c ((Zr m ℓ ω (u + 1)).est c) := by
    unfold rhM rhD
    rw [rd_of_inv hs, tab_step h hs hcU hcU le_rfl, Bh_eq, Bh_eq, kBn_eq h hs, (hs.2.2.1 c hcU).2]
    simp [hE]
  unfold retN
  rw [Finset.mem_union, Finset.mem_filter, retS_of_inv h hs, memb_of_inv h hs, hrh, mem_aux_succ']
  constructor
  · rintro (⟨_, hx⟩ | hx)
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (hx | hx)
    · exact Or.inl ⟨hc, hx⟩
    · exact Or.inr hx
/-- **One round of the machine preserves the invariant** (caps large enough, the next start pools fit). -/
theorem inv_step (h : Hyp m) {W : ℕ} (hW1 : 1 ≤ W) (hW : ∀ j, m.kx j ≤ W) (hTT : (u + 1) * W ≤ m.TT)
    (hTB : u + 1 ≤ m.TB) (hTc : u + 1 + 1 ≤ m.Tc)
    (hfit : (Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω (u + 1))).card ≤ m.Ns) (hs : Inv ℓ ω u s) :
    Inv ℓ ω (u + 1) (updM m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) (ω (u + 1)).2) := by
  set x := rawN (ℓ := ℓ) (ω := ω) (u := u) s with hxdef
  have hUx : ∀ c, c ∈ Pool.P0078.U x ↔ c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω (u + 1)) :=
    mem_U_rawN h hs
  have hvalid : Pool.P0078.Valid m.Ns x := by
    unfold Pool.P0078.Valid
    refine ⟨?_, ?_, ?_⟩
    · have : Pool.P0078.U x = Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω (u + 1)) := Finset.ext hUx
      show (Pool.P0078.U x).card ≤ m.Ns
      rw [this]; exact hfit
    · intro c d hcd
      rw [hxdef, rawN_table h hs]
      refine if_neg ?_
      rintro ⟨hc, hd, -⟩
      rcases hcd with hcd | hcd
      · exact hcd hc
      · exact hcd hd
    · intro c hc
      rw [hxdef, rawN_code h hs, if_neg hc]
  have hval : (Pool.P0104.validate (pp m) x).1 = x := by
    unfold Pool.P0104.validate; rw [dif_pos (show Pool.P0078.Valid (pp m).Ns x from hvalid)]
  rw [updM_of_ne (clock_ne hs)]
  have hs1 : (Pool.P0104.validate (pp m) (poolUpd m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s)
      (ω (u + 1)).2.2)).1 = x := hval
  have hkB : (kBn m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s)) = kBc m ℓ ω (u + 1) := kBn_eq h hs
  have hkBle : kBc m ℓ ω (u + 1) ≤ m.TB := (kBc_le m ℓ ω (u + 1)).trans hTB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs1]; exact rawN_fst h hs
  · intro c hc d hd hcd
    rw [hs1] at hc hd ⊢
    rw [hxdef, rawN_table h hs]
    have hcN := (hUx c).1 hc
    have hdN := (hUx d).1 hd
    by_cases hold : c ∈ Pool.P0078.U s.1.1 ∧ d ∈ Pool.P0078.U s.1.1
    · rw [if_pos ⟨hc, hd, hold.1, hold.2⟩]
      have hreal := tab_step h hs hold.1 hold.2 hcd
      have hb := data_le (ℓ := ℓ) (ω := ω) h hW1 hW c (e := m.P.E d) (Nat.le_succ_of_le (E_le_of_U h hs hold.2))
      have hle : (s.1.1.2.1 c d : ℕ) + βM m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) c ≤ m.TT := by
        have h1 : ((((s.1.1.2.1 c d : ℕ) + βM m s (ω (u + 1)).1 (bU (ℓ := ℓ) (ω := ω) (u := u) s) c : ℕ)) : ℝ) ≤
            ((m.TT : ℕ) : ℝ) := by
          rw [hreal]
          calc _ ≤ ((u : ℝ) + 1) * W := hb.2
            _ ≤ _ := by exact_mod_cast hTT
        exact_mod_cast h1
      rw [capF_val hle, hreal]
    · rw [if_neg (fun h' => hold ⟨h'.2.2.1, h'.2.2.2⟩)]
      have hEd : m.P.E d ≤ u + 1 := by
        obtain ⟨r, l, hrl⟩ := (mem_members_SPu ℓ ω h).1 hdN
        exact SPu_E_le ℓ ω h hrl
      have hEeq : m.P.E d = u + 1 := by
        by_cases hc0 : c ∈ Pool.P0078.U s.1.1
        · have hd0 : d ∉ Pool.P0078.U s.1.1 := fun hd0 => hold ⟨hc0, hd0⟩
          exact E_of_new h hdN (fun hm => hd0 ((U_of_inv h hs d).2 hm))
        · have := E_of_new h hcN (fun hm => hc0 ((U_of_inv h hs c).2 hm))
          omega
      rw [hEeq]; simp
  · intro c hc
    rw [hs1] at hc ⊢
    unfold retF kE
    rw [hxdef, rawN_code h hs, if_pos hc, Pool.P0104.decH_encH]
    by_cases hold : c ∈ Pool.P0078.U s.1.1
    · simp only [if_pos hold]
      refine ⟨?_, (hs.2.2.1 c hold).2⟩
      by_cases hr : c ∈ (Zr m ℓ ω (u + 1)).aux
      · rw [if_pos ((retN_iff h hs ((U_of_inv h hs c).1 hold)).2 hr), if_pos hr]; exact rfl
      · rw [if_neg (fun h' => hr ((retN_iff h hs ((U_of_inv h hs c).1 hold)).1 h')), if_neg hr]; exact rfl
    · simp only [if_neg hold]
      have hEc := E_of_new h ((hUx c).1 hc) (fun hm => hold ((U_of_inv h hs c).2 hm))
      have hna : c ∉ (Zr m ℓ ω (u + 1)).aux := fun ha => by have := E_lt_of_aux h ha; omega
      rw [if_neg hna, hEc, hkB]
      exact ⟨rfl, capF_val hkBle⟩
  · show (if isB m.P (ω (u + 1)).1.1 then _ else _) = sB m.P (sh ℓ) (ωR m ω) (u + 1)
    rw [sB, ← hs.2.2.2.1]
    show _ = if isB m.P (ω (u + 1)).1.1 then _ else _
    by_cases hb : isB m.P (ω (u + 1)).1.1 = true
    · rw [if_pos hb, if_pos hb]
      have hn : (ω (u + 1)).1.1 = none := by
        unfold isB at hb; exact Option.isNone_iff_eq_none.mp hb
      have : playM m s (ω (u + 1)).1 = m.P.AB.act 0 s.2.1 (ω (u + 1)).1.2.2 := by
        rw [playM_of_ne (clock_ne hs)]; simp only [hn]; rfl
      unfold bU; rw [this]; rfl
    · rw [if_neg hb, if_neg hb]
  · show (Pool.P0104.capF m.TB _ : ℕ) = _
    rw [hkB, capF_val hkBle]
  · show (if isE m.P (ω (u + 1)).1.1 then _ else _) = sA m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) (u + 1)
    rw [sA, ← hs.2.2.2.2.2.1, actv_of_inv h hs]
    show _ = if isE m.P (ω (u + 1)).1.1 then _ else _
    by_cases he : isE m.P (ω (u + 1)).1.1 = true
    · rw [if_pos he, if_pos he]
      have hn : (ω (u + 1)).1.1 = some none := by
        unfold isE at he; simpa using he
      have hp : playM m s (ω (u + 1)).1 = armM m s (ω (u + 1)).1 (chM m s (ω (u + 1)).1) := by
        rw [playM_of_ne (clock_ne hs)]; simp only [hn]
      have hch := chM_of_inv h hs
      have harm : ∀ o, armM m s (ω (u + 1)).1 o = armOf m.P (sh ℓ) (ωR m ω) u o := by
        intro o; cases o with
        | none => exact bA_of_inv hs
        | some c => rfl
      unfold bU
      rw [hp, harm, hch]
      unfold algCh
      rw [← hs.2.2.2.2.2.1]
      rfl
    · rw [if_neg he, if_neg he]
  · show (Pool.P0104.capF m.Tc ((s.2.2.2.2 : ℕ) + 1) : ℕ) = u + 1 + 1
    rw [hs.2.2.2.2.2.2, capF_val hTc]

end Step

end Pool.P0206

namespace Pool.P0206

open Finset Pool.P0001 Pool.P0050 Pool.P0065 Pool.P0052 Pool.P0194 Pool.P0201

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {m : MPar n ι}
  {ℓ : LossSeq n} {ω : ℕ → Yc m × Zc m}
/-- The machine state after the dummy round `0` (the copies of process round `0` sampled with round `0`'s update coin). -/
theorem inv_zero (h : Hyp m) (hTc : 1 ≤ m.Tc)
    (hfit : (Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω 0)).card ≤ m.Ns) :
    Inv ℓ ω 0 ((mach m).upd 0 (mach m).s0 (ω 0).1 (ℓ 0 ((mach m).act 0 (mach m).s0 (ω 0).1)) (ω 0).2) := by
  have hc0 : ((mach m).s0.2.2.2.2 : ℕ) = 0 := rfl
  have hupd : (mach m).upd 0 (mach m).s0 (ω 0).1 (ℓ 0 ((mach m).act 0 (mach m).s0 (ω 0).1)) (ω 0).2 =
      (Pool.P0104.validate (pp m) (initPool m (ω 0).2.2), m.P.AB.s0, 0, m.P.sA0, Pool.P0104.capF m.Tc 1) := by
    simp only [mach]
    unfold updM
    rw [if_pos (show ((0 : Fin (m.Tc + 1)) : ℕ) = 0 from rfl)]
  rw [hupd]
  -- the sampled pools are the process's round-0 start pools
  have hsp : Pool.P0065.startPools m.P.E m.P.thr0 m.P.D m.P.Lv m.P.Bt (Pool.P0104.ωz (pp m) (ω 0).2.2) 0
      (fun _ _ => ∅) = SPu m ℓ ω 0 := by
    show _ = Pool.P0065.startPools _ _ _ _ _ _ 0 (Zr m ℓ ω 0).pools
    have hp0 : (Zr m ℓ ω 0).pools = fun _ _ => ∅ := rfl
    rw [hp0]
    have : newAtT m.P.E m.P.thr0 (Pool.P0104.ωz (pp m) (ω 0).2.2) 0 = newAtT m.P.E m.P.thr0 (ωsM m ω) 0 := by
      funext r
      unfold newAtT
      refine Finset.filter_congr fun c _ => ?_
      simp only [Pool.P0104.ωz, ωsM]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h1]; exact h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h1] at h3; exact h3⟩
    unfold startPools sample
    rw [this]
  have hI1 : (initPool m (ω 0).2.2).1 = Pool.P0104.mkP (pp m) (SPu m ℓ ω 0) := by
    simp only [initPool]; rw [hsp]
  have hU : ∀ c, c ∈ Pool.P0078.U (initPool m (ω 0).2.2) ↔ c ∈ Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω 0) := by
    intro c
    rw [Pool.P0078.U, hI1, Pool.P0104.mem_U_mkP (pp m) h.hD h.hLv (SPu_inRange ℓ ω h 0), mem_members_SPu ℓ ω h]
  have hvalid : Pool.P0078.Valid m.Ns (initPool m (ω 0).2.2) := by
    unfold Pool.P0078.Valid
    refine ⟨?_, fun _ _ _ => rfl, fun c hc => ?_⟩
    · rw [show Pool.P0078.U (initPool m (ω 0).2.2) = Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω 0) from
        Finset.ext hU]
      exact hfit
    · show (if c ∈ Finset.univ.biUnion (initPool m (ω 0).2.2).1 then _ else 0) = 0
      exact if_neg hc
  have hval : (Pool.P0104.validate (pp m) (initPool m (ω 0).2.2)).1 = initPool m (ω 0).2.2 := by
    unfold Pool.P0104.validate
    split
    · rfl
    · next hv => exact absurd hvalid hv
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · show (Pool.P0104.validate (pp m) (initPool m (ω 0).2.2)).1.1 = _
    rw [hval, hI1]
  · intro c _ d _ _
    show (((Pool.P0104.validate (pp m) (initPool m (ω 0).2.2)).1.2.1 c d : ℕ) : ℝ) = _
    rw [hval]
    show ((0 : ℕ) : ℝ) = (Zr m ℓ ω 0).est c 0 - (Zr m ℓ ω 0).est c (m.P.E d)
    have he : (Zr m ℓ ω 0).est = fun _ _ => 0 := rfl
    rw [he]; simp
  · intro c hc
    show retF m (Pool.P0104.validate (pp m) (initPool m (ω 0).2.2)).1 c = _ ∧
      (kE m (Pool.P0104.validate (pp m) (initPool m (ω 0).2.2)).1 c : ℕ) = _
    rw [hval] at hc ⊢
    unfold retF kE
    have hcode : (initPool m (ω 0).2.2).2.2 c = Pool.P0104.encH (pp m) (fun _ => (0, 0)) := by
      show (if c ∈ Finset.univ.biUnion (initPool m (ω 0).2.2).1 then _ else 0) = _
      exact if_pos hc
    rw [hcode, Pool.P0104.decH_encH]
    have haux : (Zr m ℓ ω 0).aux = ∅ := rfl
    have hE0 : m.P.E c = 0 := by
      obtain ⟨r, l, hrl⟩ := (mem_members_SPu ℓ ω h).1 ((hU c).1 hc)
      have := SPu_E_le ℓ ω h hrl; omega
    rw [haux, hE0]
    exact ⟨rfl, rfl⟩
  · show (Pool.P0104.capF m.Tc 1 : ℕ) = 0 + 1
    exact capF_val hTc
/-- **The machine runs P0194's process** (process round `u` = machine round `u + 1`, process losses `ℓ(u+1)`) on every
coin path whose start pools fit, while the caps hold: before machine round `u + 1` its state satisfies `Inv u`. -/
theorem run_inv (h : Hyp m) {W : ℕ} (hW1 : 1 ≤ W) (hW : ∀ j, m.kx j ≤ W) :
    ∀ u, u * W ≤ m.TT → u ≤ m.TB → u + 1 ≤ m.Tc →
      (∀ v ≤ u, (Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω v)).card ≤ m.Ns) →
      Inv ℓ ω u ((mach m).run ℓ ω (u + 1))
  | 0, _, _, hTc, hfit => inv_zero h hTc (hfit 0 le_rfl)
  | u + 1, hTT, hTB, hTc, hfit => by
    have ih := run_inv h hW1 hW u
      (le_trans (Nat.mul_le_mul_right _ (Nat.le_succ u)) hTT) (by omega) (by omega)
      (fun v hv => hfit v (by omega))
    exact inv_step h hW1 hW hTT hTB hTc (hfit (u + 1) le_rfl) ih
/-- On such paths the machine's arm at machine round `u + 1` is the process's arm at process round `u`. -/
theorem act_run (h : Hyp m) {W : ℕ} (hW1 : 1 ≤ W) (hW : ∀ j, m.kx j ≤ W) (u : ℕ)
    (hTT : u * W ≤ m.TT) (hTB : u ≤ m.TB) (hTc : u + 1 ≤ m.Tc)
    (hfit : ∀ v ≤ u, (Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω v)).card ≤ m.Ns) :
    (mach m).act (u + 1) ((mach m).run ℓ ω (u + 1)) (ω (u + 1)).1 = play m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u :=
  playM_of_inv h (run_inv h hW1 hW u hTT hTB hTc hfit)

/-! ### Under P0201's exported regime `MPar.Intended` -/

section Intended

variable {T : ℕ}
theorem hyp_of_intended (hI : m.Intended T) : Hyp m where
  hD := hI.hD
  hLv := hI.hLv
  hlev := hI.hlev
  hkx j := by
    refine ⟨hI.kx_pos j, ?_⟩
    have h1 := hI.kx_xr j
    have h2 : (m.kx j : ℝ) ≠ 0 := by exact_mod_cast (hI.kx_pos j).ne'
    field_simp
    linarith
/-- The largest inverse slot weight. -/
def kmax (m : MPar n ι) : ℕ := Finset.univ.sup m.kx
theorem kx_le_kmax (j : Fin m.P.D) : m.kx j ≤ kmax m := Finset.le_sup (Finset.mem_univ j)
theorem one_le_kmax (hI : m.Intended T) : 1 ≤ kmax m :=
  le_trans (hI.kx_pos ⟨0, hI.hD⟩) (kx_le_kmax _)
theorem mul_kmax_le (hI : m.Intended T) {u : ℕ} (hu : u ≤ T) : u * kmax m ≤ m.TT := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨⟨0, hI.hD⟩, Finset.mem_univ _⟩ m.kx
  rw [kmax, hj]
  calc u * m.kx j ≤ T * (m.kx j + 1) := Nat.mul_le_mul hu (Nat.le_succ _)
    _ ≤ m.TT := hI.hTT j
/-- **The machine runs P0194's process** (state form): under `MPar.Intended m T`, for every process round `u < T` on
which all start pools so far fit in `Ns`, the machine's state before machine round `u + 1` satisfies `Inv`. -/
theorem run_inv_of_intended (hI : m.Intended T) {u : ℕ} (hu : u < T)
    (hfit : ∀ v ≤ u, (Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω v)).card ≤ m.Ns) :
    Inv ℓ ω u ((mach m).run ℓ ω (u + 1)) :=
  run_inv (hyp_of_intended hI) (one_le_kmax hI) kx_le_kmax u (mul_kmax_le hI hu.le)
    (by have := hI.hTB; omega) (by have := hI.hTc; omega) hfit
/-- **The machine runs P0194's process** (action form): under `MPar.Intended m T`, at every process round `u < T` on
which all start pools so far fit in `Ns`, the machine's arm at machine round `u + 1` is P0194's play at round `u`. -/
theorem act_run_of_intended (hI : m.Intended T) {u : ℕ} (hu : u < T)
    (hfit : ∀ v ≤ u, (Pool.P0095.members m.P.D m.P.Lv (SPu m ℓ ω v)).card ≤ m.Ns) :
    (mach m).act (u + 1) ((mach m).run ℓ ω (u + 1)) (ω (u + 1)).1 =
      play m.P (sh ℓ) (ωR m ω) (ωsM m ω) (φM m ω) u :=
  act_run (hyp_of_intended hI) (one_le_kmax hI) kx_le_kmax u (mul_kmax_le hI hu.le)
    (by have := hI.hTB; omega) (by have := hI.hTc; omega) hfit

end Intended

end Pool.P0206


