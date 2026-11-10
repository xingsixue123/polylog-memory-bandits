import Pool.P0194.Proc
import Pool.P0104.Basic
import Pool.P0173.StepClass

/-!
# A finite-state homogeneous coin algorithm for P0194's per-thread round-level process (P0166's C10 for `dzRun`)

P0190's machine (merged, for P0181's process) with P0194's round kinds and P0176's per-thread slots:
* `MPar`: P0194's `ParD` and the machine parameters: integer inverse slot weights `kx` (intended `xr j = 1/kx j`, so an
  observed member's increment `ℓ/x_j` is the integer `kx j·ℓ`), the round-kind law `κl` (intended `wK`: `wB`, `wE`,
  `x_j`), stored filter levels `Lf`, capacity `Ns`, caps `TT`, `TB`, `Tc`, sampling/filter probabilities `ps`, `q`.
* `pp m`: P0104's parameters with one Hedge level whose code decodes to (retired flag `retF`, BASE count at entry `kE`),
  as in P0190.
* State `St m` = (P0104's bounded pool state, BASE's state, BASE's count, ALG's state, clock). Action coin `Yc m` =
  (round kind, ALG's draw coin, BASE's action coin): stored by `CoinAlg.toMachine`, small. Update coin `Zc m` =
  (BASE's update coin, P0104's day bits), not stored.
* **Dummy round** (clock `0`, as in P0190): plays BASE's action and samples the copies of process round `0`
  (`initPool`). Machine round `t ≥ 1` runs process round `rd s = t − 1` **only while `t ≤ Tc`** and, for the
  correspondence (follow-up, not proved here), only under `MPar.Intended` and on paths whose start pools fit in `Ns`:
  * `playM`: BASE round ⟹ BASE's action; exploitation ⟹ ALG's draw (`none` ⟹ BASE's action); slot `⟨j, k⟩` ⟹ the
    active occupant of `lay j (blk j) k` (`blk` = P0176's `blockMem` of the stored pools), else BASE's action;
  * `updM`: increments `βM` (retired: `1`; the slot's occupant: `kx j·b`), rule (b″) `rhM`, retirement `retN`,
    P0104-style merges and P0065 inheritance/sampling (`poolUpd`), BASE on BASE rounds, ALG on exploitation rounds.
* **Beyond the caps the machine stops following the process** (no claim is made there): the clock saturates at `Tc`
  (then every later round re-runs process round `Tc − 1`, re-merging and re-sampling with fresh bits; with `Tc = 0`
  every round is a dummy round), BASE's count saturates at `TB`, table entries at `TT`, and P0104's `validate` empties
  the pool data when more than `Ns` copies are present.
* `MPar.Intended m T`: the exported regime for `T` process rounds (links `kx`, `κl` to P0194's `xr`, `wK`; P0104's
  regime; caps covering `T` rounds). Not enforced by `MPar`; the follow-up correspondence assumes it.
* `rhM` has no `E x ≤ u` gate (P0194's `rhD` has one): the two agree on stored members only because they have
  entered (`E c ≤ rd`), an invariant the follow-up must carry.
* **`mach m`**, **`mach_hom`** (P0173's `CoinHom`), `memb_eq_U`, `poolUpd_valid`, `validate_poolUpd`, `poolUpd_code`,
  `initPool_valid`, `validate_initPool`, `playM_of_ne`, `updM_of_ne`.
* **`memBits_mach`**, **`memBits_mach_le`**: BASE's bits plus `Ns·log₂(|ι|·2^{Lt+1}·2(TB+1)+1) + Ns²·log₂(TT+1) +
  log₂(TB+1) + log₂|σA| + log₂(Tc+1) + log₂|Kd| + log₂ N`.
-/

open Finset Pool.P0001 Pool.P0050 Pool.P0065 Pool.P0052

namespace Pool.P0201

/-- Machine parameters on top of P0194's per-thread process parameters (`ParD`). -/
structure MPar (n : ℕ) (ι : Type) [LinearOrder ι] [Fintype ι] where
  P : Pool.P0194.ParD n ι
  /-- integer inverse slot weights (intended `xr j = 1 / kx j`) -/
  kx : Fin P.D → ℕ
  /-- law of the round kind (intended weights `wB`, `wE`, `x_j`) -/
  κl : PMF (Pool.P0194.Kd P)
  Lf : ℕ
  Ns : ℕ
  TT : ℕ
  TB : ℕ
  Tc : ℕ
  ps : ℝ
  q : ℝ
  hps : 0 ≤ ps ∧ ps ≤ 1
  hq : 0 ≤ q ∧ q ≤ 1
  [fA : Fintype P.σA]
  [nN : NeZero P.N]

attribute [scoped instance] MPar.fA MPar.nN

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (m : MPar n ι)

/-- **The intended regime** for `T` process rounds. Not enforced by `MPar` and not used in this file; the follow-up
correspondence assumes it (plus start pools fitting in `Ns`, a path property):
* integer inverse slot weights linked to P0194's rates: `kx j > 0` and `kx j · xr j = 1`;
* the round-kind law is P0194's: `κl κ = wK κ` (`wB`, `wE`, `x_j` per slot);
* P0104's pool regime: `0 < D`, `0 < Lv`, `lev r a + 1 < Lv`, `lev r a ≤ Lf`;
* caps covering `T` process rounds (machine rounds `≤ T`): `T ≤ Tc`, `T ≤ TB`, and `T·(kx j + 1) ≤ TT` for every
  thread (data since entry grow by `1` per retired round or `kx j·ℓ` per observed round). -/
structure MPar.Intended (m : MPar n ι) (T : ℕ) : Prop where
  kx_pos : ∀ j, 0 < m.kx j
  kx_xr : ∀ j, (m.kx j : ℝ) * m.P.xr j = 1
  κl_eq : ∀ κ, (m.κl κ).toReal = Pool.P0194.wK m.P κ
  hD : 0 < m.P.D
  hLv : 0 < m.P.Lv
  hlev : ∀ r a, m.P.lev r a + 1 < m.P.Lv
  hLf : ∀ r a, m.P.lev r a ≤ m.Lf
  hTc : T ≤ m.Tc
  hTB : T ≤ m.TB
  hTT : ∀ j, T * (m.kx j + 1) ≤ m.TT

/-- The P0104 parameters used for the pool part (one Hedge level, codes `Fin 2 × Fin (TB+1)`). -/
def pp : Pool.P0104.Prm n ι where
  E := m.P.E
  thr0 := m.P.thr0
  arm := m.P.arm
  D := m.P.D
  Lv := m.P.Lv
  Bt := m.P.Bt
  lev := m.P.lev
  θ := m.P.θ
  R := m.P.R
  K := m.P.K
  Lf := m.Lf
  L := 0
  η := 0
  δ := 1
  Ns := m.Ns
  TT := m.TT
  NN := 1
  MM := m.TB

abbrev Raw := Pool.P0104.Raw (pp m)

/-- Start-pool members stored in the raw data. -/
noncomputable def memb (x : Raw m) : Finset ι := Pool.P0095.members m.P.D m.P.Lv (Pool.P0104.pl (pp m) x)

/-- With `0 < D` and `0 < Lv` every stored sub-pool is some `(r, ℓ)` with `r < D`, `ℓ < Lv`, so the stored members
are exactly the copies present in the raw data. -/
theorem memb_eq_U (hD : 0 < m.P.D) (hLv : 0 < m.P.Lv) (x : Raw m) : memb m x = Pool.P0078.U x := by
  ext c
  simp only [memb, Pool.P0095.members, Finset.mem_biUnion, Finset.mem_range, Pool.P0078.mem_U]
  constructor
  · rintro ⟨r, _, l, _, hc⟩
    unfold Pool.P0104.pl at hc
    split_ifs at hc
    · exact ⟨_, hc⟩
    · simp at hc
  · rintro ⟨k, hk⟩
    have hLt : (pp m).Lt + 1 = m.P.D * m.P.Lv := Pool.P0104.Lt_succ (pp m) hD hLv
    have hkD : k.1 < m.P.D * m.P.Lv := hLt ▸ k.2
    refine ⟨k.1 / m.P.Lv, (Nat.div_lt_iff_lt_mul hLv).2 hkD, k.1 % m.P.Lv, Nat.mod_lt _ hLv, ?_⟩
    have hk' : k.1 / m.P.Lv * m.P.Lv + k.1 % m.P.Lv = k.1 := Nat.div_add_mod' _ _
    unfold Pool.P0104.pl
    have hlt : k.1 / m.P.Lv * (pp m).Lv + k.1 % m.P.Lv < (pp m).Lt + 1 := by
      show k.1 / m.P.Lv * m.P.Lv + k.1 % m.P.Lv < _
      rw [hk']; exact k.2
    rw [dif_pos ⟨Nat.mod_lt _ hLv, hlt⟩]
    have : (⟨k.1 / m.P.Lv * (pp m).Lv + k.1 % m.P.Lv, hlt⟩ : Fin ((pp m).Lt + 1)) = k := Fin.ext hk'
    rw [this]; exact hk

/-- Retired flag of a copy. -/
def retF (x : Raw m) (c : ι) : Fin 2 := (Pool.P0104.decH (pp m) (x.2.2 c) 0).1

/-- BASE count at the entry of a copy. -/
def kE (x : Raw m) (c : ι) : Fin (m.TB + 1) := (Pool.P0104.decH (pp m) (x.2.2 c) 0).2

/-- Retired members. -/
noncomputable def retS (x : Raw m) : Finset ι := (memb m x).filter fun c => retF m x c = 1

/-- Active members. -/
noncomputable def actv (x : Raw m) : Finset ι := memb m x \ retS m x

/-- Machine state. -/
abbrev St := Pool.P0104.St (pp m) × m.P.AB.S × Fin (m.TB + 1) × m.P.σA × Fin (m.Tc + 1)

/-- Action coin: the round kind, ALG's draw coin, BASE's action coin. -/
abbrev Yc := Pool.P0194.Kd m.P × Fin m.P.N × m.P.AB.Y

/-- Update coin. -/
abbrev Zc := m.P.AB.Z × (Pool.P0104.Jd (pp m) → Bool)

/-- BASE's action. -/
def bA (s : St m) (y : Yc m) : Fin n := m.P.AB.act 0 s.2.1 y.2.2

/-- The arm of an ALG choice (`none` = BASE). -/
def armM (s : St m) (y : Yc m) : Option ι → Fin n
  | some c => m.P.arm c
  | none => bA m s y

/-- The process round run by machine round `t ≥ 1` (clock `t`, when `t ≤ Tc`): `t − 1`. -/
def rd (s : St m) : ℕ := (s.2.2.2.2 : ℕ) - 1

/-- The members of thread `j` stored in the raw data (P0176's `blockMem`). -/
def blk (x : Raw m) (j : ℕ) : Finset ι := Pool.P0176.blockMem m.P.Lv (Pool.P0104.pl (pp m) x) j

/-- The active occupant of slot `sl`. -/
noncomputable def occM (s : St m) (sl : Σ j : Fin m.P.D, Fin (m.P.sl j)) : Option ι :=
  match m.P.lay sl.1 (blk m s.1.1 sl.1) sl.2 with
  | some c => if c ∈ retS m s.1.1 then none else some c
  | none => none

/-- ALG's choice. -/
noncomputable def chM (s : St m) (y : Yc m) : Option ι := m.P.draw s.2.2.2.1 (actv m s.1.1) y.2.1

/-- **The play.** At machine round `0` (clock `0`, a dummy round) BASE's action; afterwards the process's play rule
for the round kind. -/
noncomputable def playM (s : St m) (y : Yc m) : Fin n :=
  if (s.2.2.2.2 : ℕ) = 0 then bA m s y else
  match y.1 with
  | none => bA m s y
  | some none => armM m s y (chM m s y)
  | some (some sl) => armM m s y (occM m s sl)

/-- Data increments of the round (observed bit `b`). -/
noncomputable def βM (s : St m) (y : Yc m) (b : Bool) (c : ι) : ℕ :=
  if c ∈ retS m s.1.1 then 1
  else match y.1 with
    | some (some sl) => if m.P.lay sl.1 (blk m s.1.1 sl.1) sl.2 = some c then m.kx sl.1 * b.toNat else 0
    | _ => 0

/-- BASE count after the round. -/
def kBn (s : St m) (y : Yc m) (b : Bool) : ℕ :=
  if Pool.P0194.isB m.P y.1 then (s.2.2.1 : ℕ) + b.toNat else s.2.2.1

/-- Retirement rule (b″) of the round, read off the stored data. Unlike P0194's `rhD` it has no `E x ≤ u` gate: it
agrees with `rhD` only on stored members that have already entered (`E c ≤ rd`), which the follow-up correspondence
must carry in its invariant. -/
noncomputable def rhM (s : St m) (y : Yc m) (b : Bool) (c : ι) : Bool :=
  decide (m.P.Bmin ∣ rd m s + 1) &&
    decide (m.P.Λ c (rd m s) ≤ (((s.1.1.2.1 c c : ℕ) + βM m s y b c : ℕ) : ℝ) -
      (m.P.cB * (kBn m s y b : ℝ) - m.P.cB * ((kE m s.1.1 c : ℕ) : ℝ)))

/-- Retired members after the round. -/
noncomputable def retN (s : St m) (y : Yc m) (b : Bool) : Finset ι :=
  retS m s.1.1 ∪ (memb m s.1.1).filter fun c => rhM m s y b c = true

/-- The pool part of the update (P0104's `unitEnd` with codes = (retired, BASE count at entry)). -/
noncomputable def poolUpd (s : St m) (y : Yc m) (b : Bool) (j : Pool.P0104.Jd (pp m) → Bool) : Raw m :=
  let x := s.1.1
  let u : ℕ := rd m s
  let U := Pool.P0078.U x
  let Dt : ι → ι → ℕ := fun c d => (x.2.1 c d : ℕ) + βM m s y b c
  let P1 : ℕ → ℕ → Finset ι := fun r =>
    if m.P.Bt r ∣ u + 1 then
      mergeUpTo m.P.E (Pool.P0104.Cm (pp m) U Dt u) m.P.θ m.P.R m.P.K (Pool.P0104.φz (pp m) j r) u
        (m.P.lev r u) (Pool.P0104.pl (pp m) x r)
    else Pool.P0104.pl (pp m) x r
  let P2 := startPools m.P.E m.P.thr0 m.P.D m.P.Lv m.P.Bt (Pool.P0104.ωz (pp m) j) (u + 1) P1
  let Q := Pool.P0104.mkP (pp m) P2
  let U2 := Finset.univ.biUnion Q
  (Q,
   fun c d => if c ∈ U2 ∧ d ∈ U2 ∧ c ∈ U ∧ d ∈ U then Pool.P0104.capF m.TT (Dt c d) else 0,
   fun c => if c ∈ U2 then
      Pool.P0104.encH (pp m) (fun _ => if c ∈ U then
        ((if c ∈ retN m s y b then 1 else 0), kE m x c)
        else (0, Pool.P0104.capF m.TB (kBn m s y b)))
     else 0)

open Classical in
/-- The raw pool update vanishes off its own pool, so it is valid as soon as it fits. -/
theorem poolUpd_valid (s : St m) (y : Yc m) (b : Bool) (j : Pool.P0104.Jd (pp m) → Bool)
    (h : (Pool.P0078.U (poolUpd m s y b j)).card ≤ m.Ns) : Pool.P0078.Valid m.Ns (poolUpd m s y b j) := by
  refine ⟨h, fun c d hcd => ?_, fun c hc => ?_⟩
  · show (if c ∈ Pool.P0078.U (poolUpd m s y b j) ∧ d ∈ Pool.P0078.U (poolUpd m s y b j) ∧ _ then _ else 0) = 0
    refine if_neg ?_
    rintro ⟨h1, h2, -⟩
    rcases hcd with h' | h'
    · exact h' h1
    · exact h' h2
  · show (if c ∈ Pool.P0078.U (poolUpd m s y b j) then _ else 0) = 0
    exact if_neg hc

open Classical in
theorem validate_poolUpd (s : St m) (y : Yc m) (b : Bool) (j : Pool.P0104.Jd (pp m) → Bool)
    (h : (Pool.P0078.U (poolUpd m s y b j)).card ≤ m.Ns) :
    (Pool.P0104.validate (pp m) (poolUpd m s y b j)).1 = poolUpd m s y b j := by
  unfold Pool.P0104.validate
  split
  · rfl
  · next hv => exact absurd (poolUpd_valid m s y b j h) hv

/-- Codes after the round: a continuing member keeps its BASE count at entry and gets the new retired flag; a new
member starts not retired with BASE's count after the round. -/
theorem poolUpd_code (s : St m) (y : Yc m) (b : Bool) (j : Pool.P0104.Jd (pp m) → Bool) {c : ι}
    (hc : c ∈ Pool.P0078.U (poolUpd m s y b j)) :
    Pool.P0104.decH (pp m) ((poolUpd m s y b j).2.2 c) 0 =
      if c ∈ Pool.P0078.U s.1.1 then ((if c ∈ retN m s y b then 1 else 0), kE m s.1.1 c)
      else (0, Pool.P0104.capF m.TB (kBn m s y b)) := by
  show Pool.P0104.decH (pp m) (if c ∈ Pool.P0078.U (poolUpd m s y b j) then Pool.P0104.encH (pp m) _ else 0) 0 = _
  rw [if_pos hc, Pool.P0104.decH_encH]
  congr

/-- The pool data after the dummy round `0`: the copies entering at process round `0`, not retired, BASE count `0`. -/
noncomputable def initPool (j : Pool.P0104.Jd (pp m) → Bool) : Raw m :=
  let Q := Pool.P0104.mkP (pp m) (Pool.P0065.startPools m.P.E m.P.thr0 m.P.D m.P.Lv m.P.Bt
    (Pool.P0104.ωz (pp m) j) 0 (fun _ _ => ∅))
  (Q, fun _ _ => 0, fun c => if c ∈ Finset.univ.biUnion Q then Pool.P0104.encH (pp m) (fun _ => (0, 0)) else 0)

open Classical in
theorem initPool_valid (j : Pool.P0104.Jd (pp m) → Bool) (h : (Pool.P0078.U (initPool m j)).card ≤ m.Ns) :
    Pool.P0078.Valid m.Ns (initPool m j) :=
  ⟨h, fun _ _ _ => rfl, fun c hc => if_neg hc⟩

open Classical in
theorem validate_initPool (j : Pool.P0104.Jd (pp m) → Bool) (h : (Pool.P0078.U (initPool m j)).card ≤ m.Ns) :
    (Pool.P0104.validate (pp m) (initPool m j)).1 = initPool m j := by
  unfold Pool.P0104.validate
  split
  · rfl
  · next hv => exact absurd (initPool_valid m j h) hv

/-- **The update.** Machine round `0` only samples the copies of process round `0`; machine round `t ≥ 1` runs process
round `t − 1` while `t ≤ Tc` (the clock saturates at `Tc`; see the module docstring for the caps). -/
noncomputable def updM (s : St m) (y : Yc m) (b : Bool) (z : Zc m) : St m :=
  if (s.2.2.2.2 : ℕ) = 0 then
    (Pool.P0104.validate (pp m) (initPool m z.2), s.2.1, s.2.2.1, s.2.2.2.1, Pool.P0104.capF m.Tc 1) else
  (Pool.P0104.validate (pp m) (poolUpd m s y b z.2),
   (if Pool.P0194.isB m.P y.1 then m.P.AB.upd 0 s.2.1 y.2.2 b z.1 else s.2.1),
   Pool.P0104.capF m.TB (kBn m s y b),
   (if Pool.P0194.isE m.P y.1 then
      m.P.updA s.2.2.2.1 (actv m s.1.1) y.2.1 (chM m s y) b else s.2.2.2.1),
   Pool.P0104.capF m.Tc ((s.2.2.2.2 : ℕ) + 1))

/-- Action-coin law: the round-kind law `κl`, a uniform draw coin, BASE's action law. -/
noncomputable def μM : PMF (Yc m) :=
  m.κl.bind fun a =>
    (Pool.P0015.unif m.P.N (NeZero.pos _)).bind fun d => m.P.AB.μ.map fun yb => (a, d, yb)

/-- Update-coin law: BASE's update law and P0104's day bits. -/
noncomputable def νM : PMF (Zc m) :=
  m.P.AB.ν.bind fun zb =>
    (Pool.P0051.bernVec (Pool.P0104.qd (pp m) m.ps m.q) (Pool.P0104.qd_mem (pp m) m.hps m.hq)).map
      fun j => (zb, j)

open Classical in
/-- **The machine** (homogeneous: the rules ignore the round index; the clock is in the state). -/
noncomputable def mach : CoinAlg n where
  S := St m
  Y := Yc m
  Z := Zc m
  μ := μM m
  ν := νM m
  s0 := (⟨Pool.P0104.emptyRaw (pp m), Pool.P0104.valid_empty (pp m)⟩, m.P.AB.s0, 0, m.P.sA0, 0)
  act _ s y := playM m s y
  upd _ s y b z := updM m s y b z

theorem mach_hom : Pool.P0173.CoinHom (mach m) := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩

/-! ### Memory -/



open Classical in
theorem card_state :
    Fintype.card (mach m).toMachine.State =
      (Fintype.card (Pool.P0104.St (pp m)) * (m.TB + 1) * Fintype.card m.P.σA * (m.Tc + 1) * Fintype.card (Pool.P0194.Kd m.P) * m.P.N) *
        (Fintype.card m.P.AB.S * Fintype.card m.P.AB.Y) := by
  rw [show Fintype.card (mach m).toMachine.State = Fintype.card (St m × Yc m) from
    Fintype.card_congr (Equiv.refl _)]
  simp only [St, Yc, Fintype.card_prod, Fintype.card_fin]
  ring

open Classical in
theorem card_base : Fintype.card m.P.AB.toMachine.State = Fintype.card m.P.AB.S * Fintype.card m.P.AB.Y := by
  rw [show Fintype.card m.P.AB.toMachine.State = Fintype.card (m.P.AB.S × m.P.AB.Y) from
    Fintype.card_congr (Equiv.refl _), Fintype.card_prod]

open Classical in
/-- **Memory**: BASE's bits plus the pool state (P0078's count), BASE's count, ALG's state, the clock and the
round-kind/draw coins. -/
theorem memBits_mach :
    (mach m).toMachine.memBits = m.P.AB.toMachine.memBits +
      (Real.logb 2 (Fintype.card (Pool.P0104.St (pp m))) + Real.logb 2 (m.TB + 1) +
        Real.logb 2 (Fintype.card m.P.σA) + Real.logb 2 (m.Tc + 1) + Real.logb 2 (Fintype.card (Pool.P0194.Kd m.P)) + Real.logb 2 m.P.N) := by
  unfold Machine.memBits
  have hA : 0 < Fintype.card m.P.AB.S * Fintype.card m.P.AB.Y :=
    Nat.mul_pos (Fintype.card_pos_iff.2 ⟨m.P.AB.s0⟩)
      (Fintype.card_pos_iff.2 ⟨(m.P.AB.μ.support_nonempty).some⟩)
  have h1 : 0 < Fintype.card (Pool.P0104.St (pp m)) :=
    Fintype.card_pos_iff.2 ⟨⟨Pool.P0104.emptyRaw (pp m), Pool.P0104.valid_empty (pp m)⟩⟩
  have h2 : 0 < Fintype.card m.P.σA := Fintype.card_pos_iff.2 ⟨m.P.sA0⟩
  have hS : 0 < Fintype.card (Pool.P0194.Kd m.P) := Fintype.card_pos_iff.2 ⟨none⟩
  have hN : 0 < m.P.N := NeZero.pos _
  rw [card_state, card_base]
  have r1 : (0 : ℝ) < Fintype.card (Pool.P0104.St (pp m)) := by exact_mod_cast h1
  have r2 : (0 : ℝ) < Fintype.card m.P.σA := by exact_mod_cast h2
  have rS : (0 : ℝ) < Fintype.card (Pool.P0194.Kd m.P) := by exact_mod_cast hS
  have rN : (0 : ℝ) < m.P.N := by exact_mod_cast hN
  have rA : (0 : ℝ) < (Fintype.card m.P.AB.S * Fintype.card m.P.AB.Y : ℕ) := by exact_mod_cast hA
  have rB : (0 : ℝ) < (m.TB : ℝ) + 1 := by positivity
  have rC : (0 : ℝ) < (m.Tc : ℝ) + 1 := by positivity
  push_cast at rA ⊢
  rw [Real.logb_mul (by positivity) rA.ne', Real.logb_mul (by positivity) rN.ne',
    Real.logb_mul (by positivity) rS.ne', Real.logb_mul (by positivity) rC.ne',
    Real.logb_mul (by positivity) r2.ne', Real.logb_mul r1.ne' rB.ne']
  ring

open Classical in
theorem memBits_mach_le :
    (mach m).toMachine.memBits ≤ m.P.AB.toMachine.memBits +
      (m.Ns * Real.logb 2 (Fintype.card ι * 2 ^ ((pp m).Lt + 1) * (2 * (m.TB + 1)) + 1) +
        (m.Ns * m.Ns : ℕ) * Real.logb 2 (m.TT + 1) + Real.logb 2 (m.TB + 1) +
        Real.logb 2 (Fintype.card m.P.σA) + Real.logb 2 (m.Tc + 1) + Real.logb 2 (Fintype.card (Pool.P0194.Kd m.P)) + Real.logb 2 m.P.N) := by
  rw [memBits_mach]
  have hcard := Pool.P0078.card_PState_le (ι := ι) (Lt := (pp m).Lt) (Ns := m.Ns) (TT := m.TT) (BB := (pp m).BB)
  have hBB : (pp m).BB + 1 = 2 * (m.TB + 1) := by
    rw [(pp m).BB_succ]; simp [Pool.P0104.Prm.HB, pp]
  have hcard' : Fintype.card (Pool.P0104.St (pp m)) ≤
      (Fintype.card ι * 2 ^ ((pp m).Lt + 1) * (2 * (m.TB + 1)) + 1) ^ m.Ns * (m.TT + 1) ^ (m.Ns * m.Ns) :=
    calc _ ≤ _ := hcard
      _ = _ := by rw [hBB]
  have h1 : 0 < Fintype.card (Pool.P0104.St (pp m)) :=
    Fintype.card_pos_iff.2 ⟨⟨Pool.P0104.emptyRaw (pp m), Pool.P0104.valid_empty (pp m)⟩⟩
  have hle : Real.logb 2 (Fintype.card (Pool.P0104.St (pp m))) ≤
      m.Ns * Real.logb 2 (Fintype.card ι * 2 ^ ((pp m).Lt + 1) * (2 * (m.TB + 1)) + 1) +
        (m.Ns * m.Ns : ℕ) * Real.logb 2 (m.TT + 1) := by
    calc Real.logb 2 (Fintype.card (Pool.P0104.St (pp m)))
        ≤ Real.logb 2 (((Fintype.card ι * 2 ^ ((pp m).Lt + 1) * (2 * (m.TB + 1)) + 1) ^ m.Ns *
            (m.TT + 1) ^ (m.Ns * m.Ns) : ℕ)) := by
          apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast h1)
          exact_mod_cast hcard'
      _ = _ := by
          push_cast
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]
          push_cast; ring
  linarith

end Pool.P0201

namespace Pool.P0201

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] {m : MPar n ι}

/-- The play after the dummy round. -/
theorem playM_of_ne {s : St m} (h : (s.2.2.2.2 : ℕ) ≠ 0) (y : Yc m) :
    playM m s y = match y.1 with
      | none => bA m s y
      | some none => armM m s y (chM m s y)
      | some (some sl) => armM m s y (occM m s sl) := by
  unfold playM; rw [if_neg h]

/-- The update after the dummy round. -/
theorem updM_of_ne {s : St m} (h : (s.2.2.2.2 : ℕ) ≠ 0) (y : Yc m) (b : Bool) (z : Zc m) :
    updM m s y b z =
      (Pool.P0104.validate (pp m) (poolUpd m s y b z.2),
       (if Pool.P0194.isB m.P y.1 then m.P.AB.upd 0 s.2.1 y.2.2 b z.1 else s.2.1),
       Pool.P0104.capF m.TB (kBn m s y b),
       (if Pool.P0194.isE m.P y.1 then
          m.P.updA s.2.2.2.1 (actv m s.1.1) y.2.1 (chM m s y) b else s.2.2.2.1),
       Pool.P0104.capF m.Tc ((s.2.2.2.2 : ℕ) + 1)) := by
  unfold updM; rw [if_neg h]

end Pool.P0201
