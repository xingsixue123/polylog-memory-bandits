import Pool.P0078.Machine
import Pool.P0096.State
import Pool.P0065.Threads

/-!
# The threaded K-query pool learner as a P0064 machine: definition and memory

A `QCoinAlg` (P0064) with `Ns` free queries per day that is designed to run P0065's threaded pool process
(Peng–Rubinstein's Algorithm 8 with inheritance) with P0089's dyadic sleeping-experts Hedge in P0096's
integer form. Unit `a` of the process is day `a + 1` (one day per unit); day `0` plays an arbitrary arm and
samples the copies of unit `0`.

* `Prm`: the parameters (copy data `E`, `thr0`, `arm`; threads, levels, epoch lengths, merge schedule; merge
  margin, chain length, filter iterations, stored filter levels; Hedge levels, rate, grid step; capacity and
  bounds of the stored integers).
* State: P0078's bounded state space `PState` (at most `Ns` copies): sub-pools (the `D·Lv` thread/level
  sub-pools flattened, `pl`, `mkP`), a pairwise table (loss of `c` since the entry of `d`), and per copy a
  Hedge code (`hEquiv`, `decH`, `encH`): for each dyadic level the loss count and the summed grid increments
  (P0096's `(n, m)`) of the copy's awake specialist.
* Play (`playL`): Hedge over the pool's specialists `(c, l)` with weights `exp (-η n + δ m)` (`wM`, `armW`).
* Queries (`qry`): the arms of the sorted pool; `bitOf` reads a copy's bit.
* Update (`unitEnd`): add the day's bits; merges of every thread whose epoch ends (P0052's `mergeUpTo` with
  cover data `Cm` rebuilt from the table); P0065's inheritance and sampling (`startPools`); Hedge data
  continue (grid increment `kM`) or restart at `(0, 0)`. Invalid results reset the state (`validate`).
* `mach`: the machine; **`memBits_mach_le`**: `log₂ |states| ≤ Ns·log₂(|ι|·2^{Lt+1}·HB + 1) + Ns²·log₂(TT + 1)`.

No correspondence with P0065's process is proved here (see `Basic.lean` for the lemmas it uses).

**Clock.** The update reads the day index (`t = 0`, the unit `t - 1`, the merge schedule `Bt r ∣ a + 1`, the levels
`lev r a`, the dyadic block ends `2 ^ l ∣ a + 1`). `memBits_mach_le` counts the state set only; a homogeneous
machine (P0001's `withClock`) costs `log₂ (T + 1)` more bits.

**Intended regime (NOT enforced by `Prm`; `mach` and `memBits_mach_le` hold for all parameters).** The design
silently saturates or truncates outside this regime, and a correspondence with P0065/P0089 will need:
* `0 < D` and `0 < Lv` (otherwise `Lt = 0` by truncated subtraction and, with `Lv = 0`, `pl` is always `∅`);
* `lev r a + 1 < Lv` for all merging `r, a` (otherwise `mkP` drops the merged copies at level `lev r a + 1`);
* `lev r a ≤ Lf` (otherwise `φz` gives constant-false filter coins: such a merge covers nobody);
* table, loss-count and grid-sum bounds large enough that `capF` never saturates (`TT`, `NN` at least the horizon,
  `MM` at least the largest grid sum), and a horizon at most `2 ^ L` (dyadic blocks of P0089);
* `0 ≤ η` and `0 < δ` (then `kM ≥ 0`, `kM_nonneg`, so the `toNat` in `unitEnd` is exact).
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0030 Pool.P0042 Pool.P0052 Pool.P0065

namespace Pool.P0104

/-- Parameters of the threaded K-query pool learner. -/
structure Prm (n : ℕ) (ι : Type) where
  /-- entry unit, entry thread and arm of a copy -/
  E : ι → ℕ
  thr0 : ι → ℕ
  arm : ι → Fin n
  /-- threads, levels per thread, epoch lengths, merge schedule -/
  D : ℕ
  Lv : ℕ
  Bt : ℕ → ℕ
  lev : ℕ → ℕ → ℕ
  /-- merge parameters: margin, chain length, filter iterations, filter levels stored in the coins -/
  θ : ℝ
  R : ℕ
  K : ℕ
  Lf : ℕ
  /-- Hedge: dyadic levels, learning rate, grid step -/
  L : ℕ
  η : ℝ
  δ : ℝ
  /-- capacity (copies), table bound, Hedge data bounds -/
  Ns : ℕ
  TT : ℕ
  NN : ℕ
  MM : ℕ

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (p : Prm n ι)

/-- Number of stored sub-pools minus one. -/
def Prm.Lt : ℕ := p.D * p.Lv - 1

/-- Size of the Hedge code of a copy. -/
def Prm.HB : ℕ := ((p.NN + 1) * (p.MM + 1)) ^ (p.L + 1)

/-- Hedge code bound. -/
def Prm.BB : ℕ := p.HB - 1

theorem Prm.HB_pos : 0 < p.HB := pow_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) _

theorem Prm.BB_succ : p.BB + 1 = p.HB := Nat.sub_add_cancel p.HB_pos

/-- Raw machine data (P0078's `Raw`): sub-pools, pairwise table, Hedge codes. -/
abbrev Raw := Pool.P0078.Raw ι p.Lt p.TT p.BB

/-- Machine states: valid raw data (at most `Ns` copies; tables vanish off the pool). -/
abbrev St := Pool.P0078.PState ι p.Lt p.Ns p.TT p.BB

/-! ### Sub-pools as an `ℕ × ℕ`-indexed family -/

/-- Sub-pool `(r, ℓ)` of the raw data (empty outside the stored range). -/
def pl (x : Raw p) (r ℓ : ℕ) : Finset ι :=
  if h : ℓ < p.Lv ∧ r * p.Lv + ℓ < p.Lt + 1 then x.1 ⟨r * p.Lv + ℓ, h.2⟩ else ∅

/-- Flatten an `ℕ × ℕ`-indexed family into the stored sub-pools. -/
def mkP (P : ℕ → ℕ → Finset ι) : Fin (p.Lt + 1) → Finset ι := fun k => P (k.1 / p.Lv) (k.1 % p.Lv)

theorem pl_mkP {P : ℕ → ℕ → Finset ι} (x : Raw p) (hx : x.1 = mkP p P) {r ℓ : ℕ} (hℓ : ℓ < p.Lv)
    (hr : r * p.Lv + ℓ < p.Lt + 1) : pl p x r ℓ = P r ℓ := by
  unfold pl
  rw [dif_pos ⟨hℓ, hr⟩, hx]
  simp only [mkP]
  have hLv : 0 < p.Lv := by omega
  congr 1
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hLv, Nat.div_eq_of_lt hℓ, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hℓ]

/-! ### Hedge codes -/

/-- Hedge codes: per dyadic level, the loss count and the summed grid increments. -/
def hEquiv : Fin (p.BB + 1) ≃ (Fin (p.L + 1) → Fin (p.NN + 1) × Fin (p.MM + 1)) :=
  (finCongr p.BB_succ).trans (finFunctionFinEquiv.symm.trans
    (Equiv.arrowCongr (Equiv.refl _) finProdFinEquiv.symm))

/-- Decode a Hedge code. -/
def decH (v : Fin (p.BB + 1)) : Fin (p.L + 1) → Fin (p.NN + 1) × Fin (p.MM + 1) := hEquiv p v

/-- Encode per-level data as a Hedge code. -/
def encH (f : Fin (p.L + 1) → Fin (p.NN + 1) × Fin (p.MM + 1)) : Fin (p.BB + 1) := (hEquiv p).symm f

theorem decH_encH (f : Fin (p.L + 1) → Fin (p.NN + 1) × Fin (p.MM + 1)) : decH p (encH p f) = f :=
  (hEquiv p).apply_symm_apply f

/-! ### Queries -/

/-- The sorted pool. -/
noncomputable def lst (x : Raw p) : List ι := (Pool.P0078.U x).sort (· ≤ ·)

/-- The queried arm of slot `k`. -/
noncomputable def qry [NeZero n] (x : Raw p) (k : Fin p.Ns) : Fin n :=
  if h : k.1 < (lst p x).length then p.arm (lst p x)[k.1] else ⟨0, NeZero.pos n⟩

/-- The queried bit of copy `c` (as `0`/`1`). -/
noncomputable def bitOf (x : Raw p) (o : Fin p.Ns → Bool) (c : ι) : ℕ :=
  if h : (lst p x).idxOf c < p.Ns then (if o ⟨_, h⟩ then 1 else 0) else 0

/-! ### Hedge over the stored data -/

/-- Loss count and grid sum of copy `c` at dyadic level `l`. -/
def hN (x : Raw p) (c : ι) (l : Fin (p.L + 1)) : ℕ := (decH p (x.2.2 c) l).1
def hM (x : Raw p) (c : ι) (l : Fin (p.L + 1)) : ℕ := (decH p (x.2.2 c) l).2

/-- Weight of the specialist `(c, l)` of a pool copy. -/
noncomputable def wM (x : Raw p) (c : ι) (l : Fin (p.L + 1)) : ℝ :=
  Real.exp (-p.η * hN p x c l + p.δ * hM p x c l)

/-- Total weight of the pool's specialists. -/
noncomputable def totW (x : Raw p) : ℝ := ∑ c ∈ Pool.P0078.U x, ∑ l, wM p x c l

/-- Arm law of the play. -/
noncomputable def armW (x : Raw p) (i : Fin n) : ℝ :=
  (∑ c ∈ (Pool.P0078.U x).filter (fun c => p.arm c = i), ∑ l, wM p x c l) / totW p x

theorem armW_nonneg (x : Raw p) (i : Fin n) : 0 ≤ armW p x i := by
  unfold armW totW wM
  apply div_nonneg <;> apply Finset.sum_nonneg <;> intro c _ <;> apply Finset.sum_nonneg <;>
    intro l _ <;> exact (Real.exp_pos _).le

theorem totW_pos {x : Raw p} (hne : (Pool.P0078.U x).Nonempty) : 0 < totW p x :=
  Finset.sum_pos (fun c _ => Finset.sum_pos (fun l _ => Real.exp_pos _) Finset.univ_nonempty) hne

theorem sum_armW (x : Raw p) (hne : (Pool.P0078.U x).Nonempty) : ∑ i, armW p x i = 1 := by
  unfold armW
  rw [← Finset.sum_div, div_eq_one_iff_eq (totW_pos p hne).ne']
  unfold totW
  rw [← Finset.sum_fiberwise (Pool.P0078.U x) p.arm (fun c => ∑ l, wM p x c l)]

open Classical in
/-- The play law. -/
noncomputable def playL [NeZero n] (x : Raw p) : PMF (Fin n) :=
  if hne : (Pool.P0078.U x).Nonempty then
    PMF.ofFintype (fun i => ENNReal.ofReal (armW p x i)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => armW_nonneg p x i), sum_armW p x hne,
        ENNReal.ofReal_one])
  else PMF.pure ⟨0, NeZero.pos n⟩

/-- The machine's grid increment of the normaliser after the loss bits `β`. -/
noncomputable def kM (x : Raw p) (β : ι → ℕ) : ℤ :=
  round (Real.log (totW p x / ∑ c ∈ Pool.P0078.U x, ∑ l, wM p x c l * Real.exp (-p.η * β c)) / p.δ)

/-! ### Update -/

/-- Update-coin coordinates of one day: filter bits `(thread, level, iteration, copy)` and sampling bits. -/
abbrev Jd := (Fin p.D × Fin (p.Lf + 1) × Fin p.K × ι) ⊕ ι

/-- Filter coins of thread `r` read off a day's coin. -/
def φz (z : Jd p → Bool) (r : ℕ) : ℕ → ℕ → Fin p.K → ι → Bool := fun _ ℓ k c =>
  if h : r < p.D ∧ ℓ < p.Lf + 1 then z (Sum.inl (⟨r, h.1⟩, ⟨ℓ, h.2⟩, k, c)) else false

/-- Sampling coins of a day's coin. -/
def ωz (z : Jd p → Bool) : ι → Bool := fun c => z (Sum.inr c)

open Classical in
/-- Cover data rebuilt from the table at the merge time `a + 1`: `-D c d` at the entry of a pool copy `d`. -/
noncomputable def Cm (U : Finset ι) (Dt : ι → ι → ℕ) (a : ℕ) (c : ι) (u : ℕ) : ℝ :=
  if u = a + 1 then 0 else
    if h : ∃ d ∈ U, p.E d = u then -((Dt c h.choose : ℕ) : ℝ) else 0

/-- Capped cast to `Fin (m + 1)`. -/
def capF (m v : ℕ) : Fin (m + 1) := ⟨min v m, Nat.lt_succ_of_le (min_le_right _ _)⟩

open Classical in
/-- End of unit `a` (day `a + 1`), with loss bits `β` of the pool copies and the day's coin `z`:
* table and Hedge data add the day's bits (Hedge: and the grid increment `kM`),
* every thread whose epoch ends merges its levels `0..lev r a` (P0052's `mergeUpTo`, cover data `Cm`),
* inheritance and sampling of unit `a + 1` (P0065's `startPools`),
* Hedge data of a continuing specialist (copy present before and after, block not ending) is kept, other
  specialists start at `(0, 0)`; tables of new copies start at `0`. -/
noncomputable def unitEnd (x : Raw p) (a : ℕ) (β : ι → ℕ) (z : Jd p → Bool) : Raw p :=
  let U := Pool.P0078.U x
  let Dt : ι → ι → ℕ := fun c d => (x.2.1 c d : ℕ) + β c
  let P1 : ℕ → ℕ → Finset ι := fun r =>
    if p.Bt r ∣ a + 1 then
      mergeUpTo p.E (Cm p U Dt a) p.θ p.R p.K (φz p z r) a (p.lev r a) (pl p x r)
    else pl p x r
  let P2 := startPools p.E p.thr0 p.D p.Lv p.Bt (ωz p z) (a + 1) P1
  let Q := mkP p P2
  let U2 := Finset.univ.biUnion Q
  let k := kM p x β
  (Q,
   fun c d => if c ∈ U2 ∧ d ∈ U2 ∧ c ∈ U ∧ d ∈ U then capF p.TT (Dt c d) else 0,
   fun c => if c ∈ U2 then
      encH p (fun l => if c ∈ U ∧ ¬ 2 ^ (l : ℕ) ∣ a + 1 then
        (capF p.NN (hN p x c l + β c), capF p.MM ((hM p x c l + k).toNat)) else (0, 0))
     else 0)

open Classical in
/-- Day `0`: the copies sampled for unit `0`. -/
noncomputable def initRaw (z : Jd p → Bool) : Raw p :=
  let Q := mkP p (startPools p.E p.thr0 p.D p.Lv p.Bt (ωz p z) 0 (fun _ _ => ∅))
  (Q, fun _ _ => 0, fun c => if c ∈ Finset.univ.biUnion Q then encH p (fun _ => (0, 0)) else 0)

/-- The empty data. -/
def emptyRaw : Raw p := (fun _ => ∅, fun _ _ => 0, fun _ => 0)

theorem valid_empty : Pool.P0078.Valid p.Ns (emptyRaw p) := by
  refine ⟨?_, fun _ _ _ => rfl, fun _ _ => rfl⟩
  show (univ.biUnion fun _ => (∅ : Finset ι)).card ≤ p.Ns
  rw [show (univ.biUnion fun _ => (∅ : Finset ι)) = ∅ by ext; simp]
  simp

open Classical in
/-- Keep valid data, reset invalid data. -/
noncomputable def validate (y : Raw p) : St p :=
  if h : Pool.P0078.Valid p.Ns y then ⟨y, h⟩ else ⟨emptyRaw p, valid_empty p⟩

/-- Coordinate probabilities of a day's coin: `q` on filter bits, `ps` on sampling bits. -/
def qd (ps q : ℝ) : Jd p → ℝ := Sum.elim (fun _ => q) (fun _ => ps)

theorem qd_mem {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) (j : Jd p) :
    0 ≤ qd p ps q j ∧ qd p ps q j ≤ 1 := by
  cases j <;> simp [qd, hps, hq]

open Classical in
/-- **The threaded K-query pool learner** (`Ns` queries per day; the update ignores the played arm).
Day `0` plays an arbitrary arm and samples the copies of unit `0`; unit `a` is day `a + 1`. -/
noncomputable def mach [NeZero n] {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    Pool.P0064.QCoinAlg n p.Ns where
  S := St p
  Z := Jd p → Bool
  ν := Pool.P0051.bernVec (qd p ps q) (qd_mem p hps hq)
  s0 := ⟨emptyRaw p, valid_empty p⟩
  play _ s := playL p s.1
  query _ s := qry p s.1
  upd t s o z := if t = 0 then validate p (initRaw p z)
    else validate p (unitEnd p s.1 (t - 1) (bitOf p s.1 o) z)

open Classical Pool.P0064 in
/-- **Memory**: `log₂ |states| ≤ Ns·log₂(|ι|·2^{Lt+1}·HB + 1) + Ns²·log₂(TT + 1)` (P0078's state count). -/
theorem memBits_mach_le [NeZero n] {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) :
    (mach p hps hq).toQ.memBits ≤
      p.Ns * Real.logb 2 (Fintype.card ι * 2 ^ (p.Lt + 1) * p.HB + 1) +
        (p.Ns * p.Ns : ℕ) * Real.logb 2 (p.TT + 1) := by
  rw [Pool.P0064.memBits_toQ]
  have hcard := Pool.P0078.card_PState_le (ι := ι) (Lt := p.Lt) (Ns := p.Ns) (TT := p.TT) (BB := p.BB)
  rw [show Fintype.card ι * 2 ^ (p.Lt + 1) * (p.BB + 1) = Fintype.card ι * 2 ^ (p.Lt + 1) * p.HB by
    rw [p.BB_succ]] at hcard
  have hpos : 0 < Fintype.card (St p) := Fintype.card_pos_iff.2 ⟨⟨emptyRaw p, valid_empty p⟩⟩
  calc Real.logb 2 (Fintype.card (mach p hps hq).S)
      ≤ Real.logb 2 (((Fintype.card ι * 2 ^ (p.Lt + 1) * p.HB + 1) ^ p.Ns * (p.TT + 1) ^ (p.Ns * p.Ns) : ℕ)) := by
        apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hpos)
        exact_mod_cast hcard
    _ = _ := by
        push_cast
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow]
        push_cast; ring

end Pool.P0104
