import Pool.P0104.Basic

/-!
# The threaded machine (P0104) runs P0065's threaded process with P0089's Hedge: correspondence on good runs

Coin path `zz : ℕ → Jd p → Bool` (day `t` uses the coin `zz t`), loss sequence `ℓs`, unit `a` = day `a + 1`.

* The ideal objects: `lvU`/`cuT` (unit losses), `ωsT`/`φT` (the coins the process reads: copy `c` is sampled by
  the coin of day `E c`, merges at the end of unit `a` read the coin of day `a + 1`), `TP` (P0065's `tpools` with
  exact cumulative losses), `SP` (its start pools), `presentT`.
* The ideal Hedge: specialists `Sp p = P0089.Spec ι L`, `awT` (P0089's `specAw` for `presentT`), `bT`, and `stH`
  (P0096's integer state, uniform prior). `bstart`, `spec c l a` (the awake specialist of copy `c` at level `l`),
  `awT_iff`, `sum_awake` (sums over awake specialists are sums over (present copy, level)).
* `Inv a x`: the stored sub-pools are `SP a` (flattened), the table holds `Σ_{w ∈ [E d, a)} loss_w(c)`, and the Hedge
  data of every present copy and level equal `stH a (spec c l a)`. `Hyp p NE`: the regime (`0 < D`, `0 < Lv`,
  `lev r a + 1 < Lv`, `NE ≤ 2^L`, `NE ≤ TT`, `NE ≤ NN`, `NE·(η/δ + 1/2) ≤ MM`, `0 ≤ η`, `0 < δ`).
* Steps: `pools_step` (merges with the table-rebuilt covers and sampling give `SP (a+1)`, via P0104's
  `agreeOn_Cm`), `kM_eq` (the machine's grid increment is P0096's `kinc`), `stH_cont`/`stH_reset` (Hedge
  continuation and restart), **`inv_step`**, `inv_zero`.
* **`run_inv`**: on every coin path whose start pools have at most `Ns` copies at every unit `≤ a < NE`, the
  machine's state after day `a` (`runZ … (a+1)`) satisfies `Inv a`.
* `E_playL`, **`dayLoss_eq`**: on such a unit with a nonempty pool, the machine's expected loss on day `a + 1` is
  P0089's `palgLoss` at round `a` (perturbation P0096's `ρM`).
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0030 Pool.P0042 Pool.P0052 Pool.P0065 Pool.P0104

namespace Pool.P0113


variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (p : Prm n ι) {NE : ℕ}

section Ideal

variable (ℓs : LossSeq n) (zz : ℕ → Jd p → Bool)

/-- Loss bit of copy `c` in unit `a` (day `a + 1`). -/
def lvU (a : ℕ) (c : ι) : ℕ := (ℓs (a + 1) (p.arm c)).toNat

/-- Unit losses as reals. -/
noncomputable def cuT (a : ℕ) (c : ι) : ℝ := (lvU p ℓs a c : ℝ)

/-- Sampling coins of the ideal process: copy `c` is sampled by the coin of day `E c`. -/
def ωsT (c : ι) : Bool := zz (p.E c) (Sum.inr c)

/-- Filter coins of the ideal process: merges at the end of unit `a` read the coin of day `a + 1`. -/
def φT (r a : ℕ) : ℕ → Fin p.K → ι → Bool := φz p (zz (a + 1)) r a

/-- The ideal threaded process (P0065) with exact cumulative losses. -/
noncomputable def TP (a : ℕ) : ℕ → ℕ → Finset ι :=
  tpools p.E p.thr0 (Pool.P0061.cumL (cuT p ℓs)) p.θ p.R p.K p.D p.Lv p.Bt p.lev (ωsT p zz) (φT p zz) a

/-- Its start pools. -/
noncomputable def SP (a : ℕ) : ℕ → ℕ → Finset ι :=
  startPools p.E p.thr0 p.D p.Lv p.Bt (ωsT p zz) a (TP p ℓs zz a)

/-- Presence in the start pools. -/
def presentT (a : ℕ) (f : ι) : Prop := ∃ r ℓ, f ∈ SP p ℓs zz a r ℓ

variable {p}

theorem SP_ok (hD : 0 < p.D) (hLv : 0 < p.Lv) (hlev : ∀ r a, p.lev r a + 1 < p.Lv) (a : ℕ) :
    StartOK p.E p.thr0 p.D p.Lv p.Bt a (SP p ℓs zz a) :=
  start_ok hD hLv (tpools_ok hD hLv hlev (ωsT p zz) (φT p zz) a) (ωsT p zz)

theorem SP_inRange (hD : 0 < p.D) (hLv : 0 < p.Lv) (hlev : ∀ r a, p.lev r a + 1 < p.Lv) (a : ℕ) :
    InRange p (SP p ℓs zz a) := by
  intro r ℓ h
  ext c
  simp only [Finset.notMem_empty, iff_false]
  intro hc
  have := SP_ok ℓs zz hD hLv hlev a c r ℓ hc
  omega

theorem SP_E_le (hD : 0 < p.D) (hLv : 0 < p.Lv) (hlev : ∀ r a, p.lev r a + 1 < p.Lv) {a r ℓ : ℕ} {c : ι}
    (hc : c ∈ SP p ℓs zz a r ℓ) : p.E c ≤ a :=
  (SP_ok ℓs zz hD hLv hlev a c r ℓ hc).1

/-- Sampling at unit `e` reads only the coins of copies entering at `e`. -/
theorem startPools_ωz (e : ℕ) (P : ℕ → ℕ → Finset ι) :
    startPools p.E p.thr0 p.D p.Lv p.Bt (ωz p (zz e)) e P = startPools p.E p.thr0 p.D p.Lv p.Bt (ωsT p zz) e P := by
  have : newAtT p.E p.thr0 (ωz p (zz e)) e = newAtT p.E p.thr0 (ωsT p zz) e := by
    funext r
    unfold newAtT
    refine Finset.filter_congr fun c _ => ?_
    simp only [ωz, ωsT]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h1]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by rw [h1] at h3; exact h3⟩
  unfold startPools sample
  rw [this]

theorem TP_succ (a : ℕ) (r : ℕ) : TP p ℓs zz (a + 1) r =
    if p.Bt r ∣ a + 1 then
      mergeUpTo p.E (Pool.P0061.cumL (cuT p ℓs)) p.θ p.R p.K (φT p zz r) a (p.lev r a) (SP p ℓs zz a r)
    else SP p ℓs zz a r := rfl

/-- A copy present at unit `a + 1` but not at unit `a` entered at `a + 1`. -/
theorem E_of_new (hD : 0 < p.D) (hLv : 0 < p.Lv) (hlev : ∀ r a, p.lev r a + 1 < p.Lv) {a : ℕ} {c : ι}
    (h1 : presentT p ℓs zz (a + 1) c) (h0 : ¬ presentT p ℓs zz a c) : p.E c = a + 1 := by
  obtain ⟨r, ℓ, hc⟩ := h1
  have hle := SP_E_le ℓs zz hD hLv hlev hc
  by_contra hne
  have hnot : ∀ r ℓ, c ∉ TP p ℓs zz (a + 1) r ℓ := by
    intro r' ℓ' hc'
    apply h0
    rw [TP_succ] at hc'
    split_ifs at hc'
    · obtain ⟨i, hi⟩ := Pool.P0063.mem_mergeUpTo _ _ _ _ _ _ _ _ _ _ c hc'
      exact ⟨r', i, hi⟩
    · exact ⟨r', ℓ', hc'⟩
  exact not_mem_startPools_of_not_alive hD hnot hne r ℓ hc

end Ideal

section HedgeIdeal

variable (ℓs : LossSeq n) (zz : ℕ → Jd p → Bool)

/-- Specialists: (copy, dyadic level, block start). -/
abbrev Sp := Pool.P0089.Spec ι p.L

/-- Awake specialists of the ideal Hedge. -/
noncomputable def awT : ℕ → Sp p → Bool := Pool.P0089.specAw (L := p.L) (presentT p ℓs zz)

/-- Integer losses of the specialists. -/
def bT (a : ℕ) (s : Sp p) : ℕ := lvU p ℓs a s.1

/-- The ideal Hedge's integer state (P0096), uniform prior. -/
noncomputable def stH (a : ℕ) : Sp p → ℕ × ℤ :=
  Pool.P0096.st (fun _ => (1 : ℝ)) p.η p.δ (awT p ℓs zz) (bT p ℓs) a

/-- Aligned start of the level-`l` block containing `a`. -/
def bstart (a l : ℕ) : ℕ := a / 2 ^ l * 2 ^ l

/-- The specialist of copy `c` at level `l` awake at unit `a`. -/
def spec (c : ι) (l : Fin (p.L + 1)) (a : ℕ) : Sp p :=
  (c, (l, ⟨bstart a l % 2 ^ p.L, Nat.mod_lt _ (pow_pos two_pos _)⟩))

variable {p}

theorem bstart_le (a l : ℕ) : bstart a l ≤ a := Nat.div_mul_le_self a (2 ^ l)

theorem bstart_dvd (a l : ℕ) : 2 ^ l ∣ bstart a l := Dvd.intro_left _ rfl

theorem lt_bstart_add (a l : ℕ) : a < bstart a l + 2 ^ l := by
  unfold bstart
  have h := Nat.div_add_mod a (2 ^ l)
  have := Nat.mod_lt a (pow_pos two_pos l)
  rw [Nat.mul_comm] at h
  omega

/-- The aligned block containing `a` is unique. -/
theorem eq_bstart {a l st : ℕ} (h1 : 2 ^ l ∣ st) (h2 : st ≤ a) (h3 : a < st + 2 ^ l) : st = bstart a l := by
  obtain ⟨k, rfl⟩ := h1
  unfold bstart
  have : a / 2 ^ l = k := Nat.div_eq_of_lt_le (by rw [Nat.mul_comm] at h2; exact h2)
    (by rw [Nat.mul_comm] at h3; rw [Nat.succ_mul]; exact h3)
  rw [this, Nat.mul_comm]

theorem awT_iff {a : ℕ} (ha : a < 2 ^ p.L) (s : Sp p) :
    awT p ℓs zz a s = true ↔ presentT p ℓs zz a s.1 ∧ s = spec p s.1 s.2.1 a := by
  obtain ⟨c, l, st⟩ := s
  simp only [awT, Pool.P0089.specAw, decide_eq_true_eq, spec]
  have hb : bstart a l % 2 ^ p.L = bstart a l := Nat.mod_eq_of_lt (lt_of_le_of_lt (bstart_le a l) ha)
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h4, ?_⟩
    have := eq_bstart h1 h2 h3
    simp only [Prod.mk.injEq, true_and]
    exact Fin.ext (by simp only; rw [hb]; exact this)
  · rintro ⟨h4, h⟩
    simp only [Prod.mk.injEq, true_and] at h
    have hst : (st : ℕ) = bstart a l := by rw [h]; simp only; exact hb
    rw [hst]
    exact ⟨bstart_dvd a l, bstart_le a l, lt_bstart_add a l, h4⟩

theorem spec_inj {a : ℕ} {c c' : ι} {l l' : Fin (p.L + 1)} (h : spec p c l a = spec p c' l' a) :
    c = c' ∧ l = l' := by
  simp only [spec, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1⟩

/-- Sums over the awake specialists are sums over (present copy, level). -/
theorem sum_awake {a : ℕ} (ha : a < 2 ^ p.L) (U : Finset ι) (hU : ∀ c, c ∈ U ↔ presentT p ℓs zz a c)
    (F : Sp p → ℝ) :
    ∑ s, (if awT p ℓs zz a s = true then F s else 0) = ∑ c ∈ U, ∑ l, F (spec p c l a) := by
  classical
  rw [← Finset.sum_filter]
  have hset : Finset.univ.filter (fun s => awT p ℓs zz a s = true) =
      (U ×ˢ (Finset.univ : Finset (Fin (p.L + 1)))).image (fun x => spec p x.1 x.2 a) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_product,
      and_true, Prod.exists]
    rw [awT_iff ℓs zz ha]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨s.1, s.2.1, (hU _).2 h1, h2.symm⟩
    · rintro ⟨c, l, hc, rfl⟩
      refine ⟨(hU c).1 hc, rfl⟩
  rw [hset, Finset.sum_image (fun x _ y _ h => by
    obtain ⟨h1, h2⟩ := spec_inj h
    exact Prod.ext h1 h2), Finset.sum_product]

end HedgeIdeal

section Inv

variable (ℓs : LossSeq n) (zz : ℕ → Jd p → Bool)

/-- **The invariant** of the machine's data at unit `a` (state after day `a`): the stored sub-pools are the
ideal start pools, the table holds the true losses `D c d = Σ_{w ∈ [E d, a)} loss_w(c)`, and the Hedge data of
each present copy and level are the ideal Hedge's integer state of its awake specialist. -/
def Inv (a : ℕ) (x : Raw p) : Prop :=
  x.1 = mkP p (SP p ℓs zz a) ∧
  (∀ c ∈ Pool.P0078.U x, ∀ d ∈ Pool.P0078.U x, p.E c ≤ p.E d →
    (x.2.1 c d : ℕ) = ∑ w ∈ Ico (p.E d) a, lvU p ℓs w c) ∧
  (∀ c ∈ Pool.P0078.U x, ∀ l, hN p x c l = (stH p ℓs zz a (spec p c l a)).1 ∧
    ((hM p x c l : ℕ) : ℤ) = (stH p ℓs zz a (spec p c l a)).2)

/-- Parameter hypotheses for the correspondence up to unit `NE`. -/
structure Hyp (p : Prm n ι) (NE : ℕ) : Prop where
  hD : 0 < p.D
  hLv : 0 < p.Lv
  hlev : ∀ r a, p.lev r a + 1 < p.Lv
  hL : NE ≤ 2 ^ p.L
  hTT : NE ≤ p.TT
  hNN : NE ≤ p.NN
  hMM : (NE : ℝ) * (p.η * 1 / p.δ + 1 / 2) ≤ p.MM
  hη : 0 ≤ p.η
  hδ : 0 < p.δ

variable {p ℓs zz}

theorem mem_U_of_inv {a : ℕ} {x : Raw p} (h : Hyp p NE) (hx : Inv p ℓs zz a x) {c : ι} :
    c ∈ Pool.P0078.U x ↔ presentT p ℓs zz a c := by
  rw [Pool.P0078.U, hx.1, mem_U_mkP p h.hD h.hLv (SP_inRange ℓs zz h.hD h.hLv h.hlev a)]
  rfl

theorem lvU_le (a : ℕ) (c : ι) : lvU p ℓs a c ≤ 1 := by
  unfold lvU; cases ℓs (a + 1) (p.arm c) <;> simp

/-- The machine's grid increment is the ideal Hedge's. -/
theorem kM_eq {a : ℕ} {x : Raw p} (h : Hyp p NE) (ha : a < NE) (hx : Inv p ℓs zz a x) {β : ι → ℕ}
    (hβ : ∀ c ∈ Pool.P0078.U x, β c = lvU p ℓs a c) :
    kM p x β = Pool.P0096.kinc p.η p.δ (Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ (stH p ℓs zz a))
      (awT p ℓs zz a) (fun s => (bT p ℓs a s : ℝ)) := by
  have haL : a < 2 ^ p.L := lt_of_lt_of_le ha h.hL
  have hU : ∀ c, c ∈ Pool.P0078.U x ↔ presentT p ℓs zz a c := fun c => mem_U_of_inv h hx
  have hw : ∀ c ∈ Pool.P0078.U x, ∀ l, Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ (stH p ℓs zz a)
      (spec p c l a) = wM p x c l := by
    intro c hc l
    obtain ⟨h1, h2⟩ := hx.2.2 c hc l
    unfold Pool.P0096.wOf wM
    rw [one_mul, ← h1, ← h2]
    push_cast; ring_nf
  unfold kM Pool.P0096.kinc Pool.P0019.awakeMass Pool.P0019.expMass
  rw [sum_awake ℓs zz haL _ hU, sum_awake ℓs zz haL _ hU]
  unfold totW
  have e1 : ∑ c ∈ Pool.P0078.U x, ∑ l, wM p x c l = ∑ c ∈ Pool.P0078.U x, ∑ l,
      Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ (stH p ℓs zz a) (spec p c l a) :=
    Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun l _ => (hw c hc l).symm
  have e2 : ∑ c ∈ Pool.P0078.U x, ∑ l, wM p x c l * Real.exp (-p.η * β c) = ∑ c ∈ Pool.P0078.U x, ∑ l,
      Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ (stH p ℓs zz a) (spec p c l a) *
        Real.exp (-p.η * (fun s => (bT p ℓs a s : ℝ)) (spec p c l a)) :=
    Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun l _ => by
      rw [hw c hc l, hβ c hc]; rfl
  rw [e1, e2]

end Inv

section HedgeStep

variable {p ℓs zz}

theorem bstart_succ {a l : ℕ} (h : ¬ 2 ^ l ∣ a + 1) : bstart (a + 1) l = bstart a l := by
  refine (eq_bstart (bstart_dvd a l) (by have := bstart_le a l; omega) ?_).symm
  have h1 := lt_bstart_add a l
  rcases Nat.lt_or_ge (a + 1) (bstart a l + 2 ^ l) with h2 | h2
  · exact h2
  · exfalso; apply h
    have : a + 1 = bstart a l + 2 ^ l := by omega
    rw [this]; exact Nat.dvd_add (bstart_dvd a l) dvd_rfl

theorem bstart_self {a l : ℕ} (h : 2 ^ l ∣ a + 1) : bstart (a + 1) l = a + 1 :=
  (eq_bstart h le_rfl (by have := pow_pos (two_pos : (0 : ℕ) < 2) l; omega)).symm

/-- A continuing specialist (copy present, block not ending) is the same specialist, and awake. -/
theorem spec_cont {a : ℕ} {c : ι} {l : Fin (p.L + 1)} (h : ¬ 2 ^ (l : ℕ) ∣ a + 1) :
    spec p c l (a + 1) = spec p c l a := by
  simp only [spec, bstart_succ h]

/-- **Hedge step, continuing specialist.** -/
theorem stH_cont {a : ℕ} (haL : a < 2 ^ p.L) {c : ι} {l : Fin (p.L + 1)} (hc : presentT p ℓs zz a c)
    (hb : ¬ 2 ^ (l : ℕ) ∣ a + 1) :
    stH p ℓs zz (a + 1) (spec p c l (a + 1)) =
      ((stH p ℓs zz a (spec p c l a)).1 + lvU p ℓs a c,
       (stH p ℓs zz a (spec p c l a)).2 + Pool.P0096.kinc p.η p.δ
          (Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ (stH p ℓs zz a)) (awT p ℓs zz a)
          (fun s => (bT p ℓs a s : ℝ))) := by
  rw [spec_cont hb]
  have haw : awT p ℓs zz a (spec p c l a) = true := (awT_iff ℓs zz haL _).2 ⟨hc, rfl⟩
  simp only [stH, Pool.P0096.st, haw, if_true]
  rfl

/-- **Hedge step, fresh specialist** (new copy or new block): its integer state is `(0, 0)`. -/
theorem stH_reset (h : Hyp p NE) {a : ℕ} (haL : a + 1 < 2 ^ p.L) {c : ι} {l : Fin (p.L + 1)}
    (hc1 : presentT p ℓs zz (a + 1) c) (hcase : ¬ (presentT p ℓs zz a c ∧ ¬ 2 ^ (l : ℕ) ∣ a + 1)) :
    stH p ℓs zz (a + 1) (spec p c l (a + 1)) = (0, 0) := by
  unfold stH
  refine Pool.P0096.st_of_never fun s hs => ?_
  by_contra hne
  have haw : awT p ℓs zz s (spec p c l (a + 1)) = true := by simpa using hne
  have hsL : s < 2 ^ p.L := by omega
  obtain ⟨hpres, hsp⟩ := (awT_iff ℓs zz hsL _).1 haw
  simp only [spec, Prod.mk.injEq, Fin.mk.injEq, true_and] at hsp
  have hb1 : bstart (a + 1) l % 2 ^ p.L = bstart (a + 1) l :=
    Nat.mod_eq_of_lt (lt_of_le_of_lt (bstart_le _ _) haL)
  have hb2 : bstart s l % 2 ^ p.L = bstart s l := Nat.mod_eq_of_lt (lt_of_le_of_lt (bstart_le _ _) hsL)
  rw [hb1, hb2] at hsp
  -- the block of `s` starts at the block start of `a + 1`
  have hsle : bstart (a + 1) l ≤ s := by rw [hsp]; exact bstart_le s l
  by_cases hdv : 2 ^ (l : ℕ) ∣ a + 1
  · rw [bstart_self hdv] at hsle; omega
  · have hna : ¬ presentT p ℓs zz a c := fun hp => hcase ⟨hp, hdv⟩
    have hE := E_of_new ℓs zz h.hD h.hLv h.hlev hc1 hna
    obtain ⟨r, ℓ, hm⟩ := hpres
    change c ∈ SP p ℓs zz s r ℓ at hm
    have := SP_E_le ℓs zz h.hD h.hLv h.hlev hm
    omega

end HedgeStep

section Step

variable {p ℓs zz}

/-- The machine's merges and sampling at the end of unit `a` produce the ideal start pools of `a + 1`. -/
theorem pools_step (h : Hyp p NE) {a : ℕ} {x : Raw p} (hx : Inv p ℓs zz a x) {β : ι → ℕ}
    (hβ : ∀ c ∈ Pool.P0078.U x, β c = lvU p ℓs a c) :
    startPools p.E p.thr0 p.D p.Lv p.Bt (ωz p (zz (a + 1))) (a + 1) (fun r =>
      if p.Bt r ∣ a + 1 then
        mergeUpTo p.E (Cm p (Pool.P0078.U x) (fun c d => (x.2.1 c d : ℕ) + β c) a) p.θ p.R p.K
          (φz p (zz (a + 1)) r) a (p.lev r a) (pl p x r)
      else pl p x r) = SP p ℓs zz (a + 1) := by
  have hUx : ∀ c, c ∈ Pool.P0078.U x ↔ presentT p ℓs zz a c := fun c => mem_U_of_inv h hx
  have hUE : ∀ d ∈ Pool.P0078.U x, p.E d ≤ a := fun d hd => by
    obtain ⟨r, ℓ, hm⟩ := (hUx d).1 hd
    exact SP_E_le ℓs zz h.hD h.hLv h.hlev hm
  have hpl : ∀ r, pl p x r = SP p ℓs zz a r := fun r => funext fun ℓ =>
    pl_eq_of p h.hD h.hLv (SP_inRange ℓs zz h.hD h.hLv h.hlev a) x hx.1 r ℓ
  have hDt : ∀ c ∈ Pool.P0078.U x, ∀ d ∈ Pool.P0078.U x, p.E c ≤ p.E d →
      (((x.2.1 c d : ℕ) + β c : ℕ) : ℝ) = ∑ w ∈ Ico (p.E d) (a + 1), cuT p ℓs w c := by
    intro c hc d hd hcd
    rw [hx.2.1 c hc d hd hcd, hβ c hc, Finset.sum_Ico_succ_top (hUE d hd)]
    push_cast
    rfl
  have hag := agreeOn_Cm hUE hDt
  rw [startPools_ωz]
  unfold SP
  congr 1
  funext r
  rw [TP_succ, hpl r]
  split_ifs
  · rw [Pool.P0078.mergeUpTo_congrC p.E _ _ p.θ p.R p.K _ a _ hag (p.lev r a) (SP p ℓs zz a r)
      (fun ℓ c hc => (hUx c).2 ⟨r, ℓ, hc⟩)]
    exact mergeUpTo_congr_time p (φ := φz p (zz (a + 1)) r) (φ' := φT p zz r) a rfl _ _
  · rfl

/-- **One day of the machine preserves the invariant** (on a good unit: the new start pools have at most
`Ns` copies). -/
theorem inv_step [NeZero n] (h : Hyp p NE) {a : ℕ} (ha : a + 1 < NE) (x : St p) (hx : Inv p ℓs zz a x.1)
    (hg : (Finset.univ.biUnion (mkP p (SP p ℓs zz (a + 1)))).card ≤ p.Ns) :
    Inv p ℓs zz (a + 1)
      (validate p (unitEnd p x.1 a (bitOf p x.1 (fun k => ℓs (a + 1) (qry p x.1 k))) (zz (a + 1)))).1 := by
  classical
  set β := bitOf p x.1 (fun k => ℓs (a + 1) (qry p x.1 k)) with hβdef
  have hβ : ∀ c ∈ Pool.P0078.U x.1, β c = lvU p ℓs a c := fun c hc => bitOf_eq x.2 _ hc
  have hUx : ∀ c, c ∈ Pool.P0078.U x.1 ↔ presentT p ℓs zz a c := fun c => mem_U_of_inv h hx
  have hUE : ∀ d ∈ Pool.P0078.U x.1, p.E d ≤ a := fun d hd => by
    obtain ⟨r, ℓ, hm⟩ := (hUx d).1 hd
    exact SP_E_le ℓs zz h.hD h.hLv h.hlev hm
  set y := unitEnd p x.1 a β (zz (a + 1)) with hydef
  have hy1 : y.1 = mkP p (SP p ℓs zz (a + 1)) := by
    rw [hydef, unitEnd_fst]
    exact congrArg (mkP p) (pools_step h hx hβ)
  have hUy : ∀ c, c ∈ Pool.P0078.U y ↔ presentT p ℓs zz (a + 1) c := by
    intro c
    rw [Pool.P0078.U, hy1, mem_U_mkP p h.hD h.hLv (SP_inRange ℓs zz h.hD h.hLv h.hlev (a + 1))]
    rfl
  have hvalid : Pool.P0078.Valid p.Ns y := by
    refine ⟨?_, fun c d hcd => ?_, fun c hc => ?_⟩
    · rw [Pool.P0078.U, hy1]; exact hg
    · rw [hydef, unitEnd_table, if_neg]
      rintro ⟨h1, h2, -⟩
      rcases hcd with h' | h' <;> exact h' (by rw [hydef]; assumption)
    · rw [hydef, unitEnd_hedge, if_neg]
      exact fun h' => hc (by rw [hydef]; exact h')
  have hval : (validate p y).1 = y := by unfold validate; rw [dif_pos hvalid]
  rw [hval]
  have haNE : a < NE := by omega
  refine ⟨hy1, ?_, ?_⟩
  · -- the table
    intro c hc d hd hcd
    have hc' : c ∈ Finset.univ.biUnion y.1 := hc
    have hd' : d ∈ Finset.univ.biUnion y.1 := hd
    rw [hydef] at hc' hd'
    rw [hydef, unitEnd_table]
    by_cases hcx : c ∈ Pool.P0078.U x.1 <;> by_cases hdx : d ∈ Pool.P0078.U x.1
    · rw [if_pos ⟨hc', hd', hcx, hdx⟩]
      have hsum : (x.1.2.1 c d : ℕ) + β c = ∑ w ∈ Ico (p.E d) (a + 1), lvU p ℓs w c := by
        rw [hx.2.1 c hcx d hdx hcd, hβ c hcx, Finset.sum_Ico_succ_top (hUE d hdx)]
      have hle : ∑ w ∈ Ico (p.E d) (a + 1), lvU p ℓs w c ≤ p.TT := by
        calc ∑ w ∈ Ico (p.E d) (a + 1), lvU p ℓs w c ≤ ∑ _w ∈ Ico (p.E d) (a + 1), 1 :=
              Finset.sum_le_sum fun w _ => lvU_le w c
          _ ≤ a + 1 := by simp
          _ ≤ p.TT := by have := h.hTT; omega
      simp only [capF, hsum, min_eq_left hle]
    · rw [if_neg (fun h' => hdx h'.2.2.2)]
      have hEd := E_of_new ℓs zz h.hD h.hLv h.hlev ((hUy d).1 hd) (fun hp => hdx ((hUx d).2 hp))
      rw [hEd]; simp
    · exfalso
      have hEc := E_of_new ℓs zz h.hD h.hLv h.hlev ((hUy c).1 hc) (fun hp => hcx ((hUx c).2 hp))
      have := hUE d hdx
      omega
    · rw [if_neg (fun h' => hdx h'.2.2.2)]
      have hEd := E_of_new ℓs zz h.hD h.hLv h.hlev ((hUy d).1 hd) (fun hp => hdx ((hUx d).2 hp))
      rw [hEd]; simp
  · -- the Hedge data
    intro c hc l
    have hc' : c ∈ Finset.univ.biUnion y.1 := hc
    have hdec : decH p (y.2.2 c) l = (if c ∈ Pool.P0078.U x.1 ∧ ¬ 2 ^ (l : ℕ) ∣ a + 1 then
        (capF p.NN (hN p x.1 c l + β c), capF p.MM ((hM p x.1 c l + kM p x.1 β).toNat)) else (0, 0)) := by
      rw [hydef] at hc' ⊢
      rw [unitEnd_hedge, if_pos hc', decH_encH]
    have hb1 : ∀ t (j : Sp p), bT p ℓs t j ≤ 1 := fun t j => lvU_le t j.1
    have hbd := Pool.P0096.st_bounds (q := fun _ => (1 : ℝ)) (aw := awT p ℓs zz) (fun _ => one_pos) h.hη h.hδ
      hb1 (a + 1) (spec p c l (a + 1))
    have hMM := h.hMM
    have hNE : ((a + 1 : ℕ) : ℝ) ≤ NE := by exact_mod_cast ha.le
    have hK : (0 : ℝ) ≤ p.η * 1 / p.δ + 1 / 2 := by have := h.hη; have := h.hδ; positivity
    unfold hN hM
    rw [hdec]
    by_cases hcase : c ∈ Pool.P0078.U x.1 ∧ ¬ 2 ^ (l : ℕ) ∣ a + 1
    · rw [if_pos hcase]
      simp only [hN, hM]
      have haL : a < 2 ^ p.L := lt_of_lt_of_le haNE h.hL
      have hcont := stH_cont (zz := zz) haL ((hUx c).1 hcase.1) hcase.2
      obtain ⟨hN0, hM0⟩ := hx.2.2 c hcase.1 l
      unfold hN at hN0; unfold hM at hM0
      have hk := kM_eq h haNE hx hβ
      unfold stH at hcont hN0 hM0 hk hbd ⊢
      rw [hcont] at hbd ⊢
      simp only [Prod.fst, Prod.snd] at hbd ⊢
      refine ⟨?_, ?_⟩
      · have hle : ((decH p (x.1.2.2 c) l).1 : ℕ) + β c ≤ p.NN := by
          rw [hN0, hβ c hcase.1]
          have := h.hNN; omega
        simp only [capF]
        rw [min_eq_left hle, hN0, hβ c hcase.1]
      · have hv : (((decH p (x.1.2.2 c) l).2 : ℕ) : ℤ) + kM p x.1 β = (Pool.P0096.st (fun _ => (1 : ℝ)) p.η p.δ (awT p ℓs zz)
            (bT p ℓs) a (spec p c l a)).2 + Pool.P0096.kinc p.η p.δ (Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ
              (Pool.P0096.st (fun _ => (1 : ℝ)) p.η p.δ (awT p ℓs zz) (bT p ℓs) a)) (awT p ℓs zz a)
                (fun s => (bT p ℓs a s : ℝ)) := by
          rw [hM0, hk]
        have hnn := hbd.2.1
        have hreal := hbd.2.2
        set v := (Pool.P0096.st (fun _ => (1 : ℝ)) p.η p.δ (awT p ℓs zz) (bT p ℓs) a (spec p c l a)).2 +
          Pool.P0096.kinc p.η p.δ (Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ
            (Pool.P0096.st (fun _ => (1 : ℝ)) p.η p.δ (awT p ℓs zz) (bT p ℓs) a)) (awT p ℓs zz a)
              (fun s => (bT p ℓs a s : ℝ)) with hvdef
        have hvle : v ≤ p.MM := by
          have : (v : ℝ) ≤ p.MM := by
            calc (v : ℝ) ≤ ((a + 1 : ℕ) : ℝ) * (p.η * 1 / p.δ + 1 / 2) := by simpa only [Nat.cast_one] using hreal
              _ ≤ NE * (p.η * 1 / p.δ + 1 / 2) := mul_le_mul_of_nonneg_right hNE hK
              _ ≤ p.MM := hMM
          exact_mod_cast this
        have htn : (((decH p (x.1.2.2 c) l).2 : ℕ) + kM p x.1 β).toNat = v.toNat := by
          rw [← hv]
        simp only [capF]
        rw [htn, min_eq_left (by omega)]
        push_cast
        omega
    · rw [if_neg hcase]
      have hres := stH_reset (zz := zz) h (lt_of_lt_of_le ha h.hL) ((hUy c).1 hc)
        (fun h' => hcase ⟨(hUx c).2 h'.1, h'.2⟩)
      unfold stH at hres ⊢
      rw [hres]
      simp

theorem TP_zero : TP p ℓs zz 0 = fun _ _ => ∅ := rfl

/-- **Day 0 establishes the invariant** (if the copies sampled for unit `0` fit). -/
theorem inv_zero (h : Hyp p NE) (hg : (Finset.univ.biUnion (mkP p (SP p ℓs zz 0))).card ≤ p.Ns) :
    Inv p ℓs zz 0 (validate p (initRaw p (zz 0))).1 := by
  classical
  have hy1 : (initRaw p (zz 0)).1 = mkP p (SP p ℓs zz 0) := by
    show mkP p (startPools p.E p.thr0 p.D p.Lv p.Bt (ωz p (zz 0)) 0 (fun _ _ => ∅)) = _
    rw [startPools_ωz]; rfl
  have hvalid : Pool.P0078.Valid p.Ns (initRaw p (zz 0)) := by
    refine ⟨?_, fun c d _ => rfl, fun c hc => ?_⟩
    · rw [Pool.P0078.U, hy1]; exact hg
    · show (if c ∈ Finset.univ.biUnion (initRaw p (zz 0)).1 then _ else _) = _
      rw [if_neg (show c ∉ Finset.univ.biUnion (initRaw p (zz 0)).1 from hc)]
  have hval : (validate p (initRaw p (zz 0))).1 = initRaw p (zz 0) := by
    unfold validate; rw [dif_pos hvalid]
  rw [hval]
  refine ⟨hy1, fun c _ d _ hcd => ?_, fun c hc l => ?_⟩
  · simp only [Finset.Ico_eq_empty_of_le (Nat.zero_le _), Finset.sum_empty]
    rfl
  · have hc' : c ∈ Finset.univ.biUnion (initRaw p (zz 0)).1 := hc
    have hdec : decH p ((initRaw p (zz 0)).2.2 c) l = (0, 0) := by
      show decH p (if c ∈ Finset.univ.biUnion (initRaw p (zz 0)).1 then encH p (fun _ => (0, 0)) else 0) l = _
      rw [if_pos hc', decH_encH]
    simp only [hN, hM, hdec]
    simp [stH, Pool.P0096.st]

/-- The machine's run driven by the coin path `zz` (day `t` uses the coin `zz t`). -/
noncomputable def runZ [NeZero n] (p : Prm n ι) (ℓs : LossSeq n) (zz : ℕ → Jd p → Bool) {ps q : ℝ}
    (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) : ℕ → St p
  | 0 => ⟨emptyRaw p, valid_empty p⟩
  | t + 1 => (mach p hps hq).upd t (runZ p ℓs zz hps hq t) ((mach p hps hq).bits ℓs t (runZ p ℓs zz hps hq t)) (zz t)

/-- `runZ` is P0064's realized run `QCoinAlg.runFin` of the machine on the coin sequence `zz`
restricted to the first `t` days. -/
theorem runZ_eq_runFin [NeZero n] (p : Prm n ι) (ℓs : LossSeq n) (zz : ℕ → Jd p → Bool) {ps q : ℝ}
    (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    ∀ t, runZ p ℓs zz hps hq t = (mach p hps hq).runFin ℓs t (fun j => zz j)
  | 0 => rfl
  | t + 1 => by
    rw [runZ, runZ_eq_runFin p ℓs zz hps hq t]
    rfl

/-- **Correspondence**: on every coin path whose start pools fit (`≤ Ns` copies) at every unit `≤ a`, the
machine's data after day `a` (state on day `a + 1`) satisfy the invariant at unit `a`. -/
theorem run_inv [NeZero n] {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) (h : Hyp p NE) :
    ∀ a, a < NE → (∀ a' ≤ a, (Finset.univ.biUnion (mkP p (SP p ℓs zz a'))).card ≤ p.Ns) →
      Inv p ℓs zz a (runZ p ℓs zz hps hq (a + 1)).1
  | 0, _, hg => by
    show Inv p ℓs zz 0 (validate p (initRaw p (zz 0))).1
    exact inv_zero h (hg 0 le_rfl)
  | a + 1, ha, hg => by
    have ih := run_inv hps hq h a (by omega) (fun a' ha' => hg a' (by omega))
    show Inv p ℓs zz (a + 1) (validate p (unitEnd p (runZ p ℓs zz hps hq (a + 1)).1 (a + 1 - 1)
      (bitOf p (runZ p ℓs zz hps hq (a + 1)).1 (fun k => ℓs (a + 1) (qry p (runZ p ℓs zz hps hq (a + 1)).1 k)))
        (zz (a + 1)))).1
    exact inv_step h ha _ ih (hg (a + 1) le_rfl)

end Step

section DayLoss

variable {p}

/-- Expected loss of the play law: the weighted average over the pool's specialists. -/
theorem E_playL [NeZero n] (x : Raw p) (hne : (Pool.P0078.U x).Nonempty) (f : Fin n → ℝ) :
    Pool.P0015.E (playL p x) f = (∑ c ∈ Pool.P0078.U x, ∑ l, wM p x c l * f (p.arm c)) / totW p x := by
  classical
  unfold Pool.P0015.E playL
  rw [dif_pos hne]
  simp only [PMF.ofFintype_apply, ENNReal.toReal_ofReal (armW_nonneg p x _)]
  unfold armW
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_fiberwise (Pool.P0078.U x) p.arm (fun c => ∑ l, wM p x c l * f (p.arm c))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [(Finset.mem_filter.mp hc).2, Finset.sum_mul]

variable {ℓs : LossSeq n} {zz : ℕ → Jd p → Bool}

/-- **One day's expected loss is the ideal Hedge's**: on a unit `a` where the invariant holds and the pool is
nonempty, the machine's expected loss on day `a + 1` is P0089's `palgLoss` at round `a` (specialists awake while
their copy is in the ideal start pools, uniform prior, perturbation P0096's `ρM`). -/
theorem dayLoss_eq [NeZero n] (h : Hyp p NE) {a : ℕ} (ha : a < NE) {x : Raw p} (hx : Inv p ℓs zz a x)
    (hne : (Pool.P0078.U x).Nonempty) :
    Pool.P0015.E (playL p x) (fun i => ((ℓs (a + 1) i).toNat : ℝ)) =
      Pool.P0089.palgLoss (fun _ => (1 : ℝ)) p.η (awT p ℓs zz) (Pool.P0089.specLoss (L := p.L) (cuT p ℓs))
        (Pool.P0096.ρM (fun _ => (1 : ℝ)) p.η p.δ (awT p ℓs zz) (bT p ℓs)) a := by
  have haL : a < 2 ^ p.L := lt_of_lt_of_le ha h.hL
  have hU : ∀ c, c ∈ Pool.P0078.U x ↔ presentT p ℓs zz a c := fun c => mem_U_of_inv h hx
  have hw : ∀ c ∈ Pool.P0078.U x, ∀ l, Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ (stH p ℓs zz a)
      (spec p c l a) = wM p x c l := by
    intro c hc l
    obtain ⟨h1, h2⟩ := hx.2.2 c hc l
    unfold Pool.P0096.wOf wM
    rw [one_mul, ← h1, ← h2]
    push_cast; ring_nf
  have hc : Pool.P0089.specLoss (L := p.L) (cuT p ℓs) = fun s j => (bT p ℓs s j : ℝ) := rfl
  rw [E_playL x hne, Pool.P0089.palgLoss, hc]
  have hp : ∀ j, Pool.P0089.pprob (fun _ => (1 : ℝ)) p.η (awT p ℓs zz) (fun s j => (bT p ℓs s j : ℝ))
      (Pool.P0096.ρM (fun _ => (1 : ℝ)) p.η p.δ (awT p ℓs zz) (bT p ℓs)) a j * (bT p ℓs a j : ℝ) =
      if awT p ℓs zz a j = true then
        Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ (stH p ℓs zz a) j * (bT p ℓs a j : ℝ) /
          Pool.P0019.awakeMass (Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ (stH p ℓs zz a)) (awT p ℓs zz a)
      else 0 := by
    intro j
    rw [Pool.P0096.pprob_eq (fun _ => one_pos)]
    split_ifs <;> simp [stH, div_mul_eq_mul_div]
  rw [Finset.sum_congr rfl fun j _ => hp j, sum_awake ℓs zz haL _ hU]
  have hM : Pool.P0019.awakeMass (Pool.P0096.wOf (fun _ => (1 : ℝ)) p.η p.δ (stH p ℓs zz a)) (awT p ℓs zz a) =
      totW p x := by
    unfold Pool.P0019.awakeMass totW
    rw [sum_awake ℓs zz haL _ hU]
    exact Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun l _ => hw c hc l
  rw [hM, Finset.sum_div]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hw c hc l]
  rfl

end DayLoss

end Pool.P0113
