import Pool.P0064.QCoin
import Pool.P0078.Machine
import Pool.P0065.Threads
import Pool.P0082.Count
import Pool.P0051.CoinProc
import Pool.P0102.Learner
import Pool.P0121.State

/-!
# The threaded (boosted) Peng–Rubinstein K-query learner as a finite-state machine

Units are days: unit `a` is played on day `a + 1`; day `0` samples the copies of unit `0`.
Copies `Cp n NE D = Fin (NE * D * n)`: copy `c` enters at unit `E c = c / (D n)` on thread `thr0 c = (c / n) % D`
with arm `arm c = c % n`.

The state (`Pool.P0121.TS.GState`) stores, for at most `Ns` present copies, a label: the pool mask
(`Fin D → Fin Lv → Bool`) and P0102's learner data (`L + 1` pairs: integer loss since the level-`ℓ` specialist
woke, grid index at the wake); a pairwise table `tab c d` = loss of `c` since unit `E d`; and P0102's global grid
index `kL`.
* Play (`playL`): P0102's machine weights aggregated by arm.
* Queries (`qry`): the arms of the sorted present copies.
* Update of day `a + 1` (`stepRaw`): add the queried bits (table, learner losses, grid index by P0102's `inc`);
  P0065's merges of the threads whose epoch ends at unit `a` with the cover data `Cm` rebuilt from the table; P0065's
  inheritance and sampling for unit `a + 1`; learner restarts (new copies, new aligned blocks). Results with more
  than `Ns` copies reset the state (`validate`), so the memory bound holds on every path.
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0030 Pool.P0042 Pool.P0052 Pool.P0065 Pool.P0121.TS

namespace Pool.P0121.TM

variable (n NE D : ℕ) [NeZero n]

/-- Copies. -/
abbrev Cp := Fin (NE * D * n)

/-- Entry unit of a copy. -/
def E (c : Cp n NE D) : ℕ := c.1 / (D * n)

/-- Entry thread of a copy. -/
def thr0 (c : Cp n NE D) : ℕ := c.1 / n % D

/-- Arm of a copy. -/
def arm (c : Cp n NE D) : Fin n := ⟨c.1 % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem E_mono : Monotone (E n NE D) := fun _ _ h => Nat.div_le_div_right h

/-- Labels: pool mask and learner data. -/
abbrev Lb (D Lv L M : ℕ) := (Fin D → Fin Lv → Bool) × (Fin (L + 1) → Fin (2 ^ L + 1) × Fin (M + 1))

/-- Day coins: filter bits `(r, ℓ, k, c)` of the merges ending the current unit and sampling bits `c` of the next
unit. -/
abbrev Jd (Lt K : ℕ) := (Fin D × Fin (Lt + 1) × Fin K × Cp n NE D) ⊕ Cp n NE D

variable {n NE D}
variable {Lv L M Lt K R : ℕ} (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (θ η ε : ℝ) (Ns : ℕ)

/-- Raw machine data. -/
abbrev RawT (n NE D Lv L M : ℕ) := Raw (Cp n NE D) (Lb D Lv L M) (Fin (M + 1)) NE

/-- Machine states. -/
abbrev StT (n NE D Lv L M Ns : ℕ) := GState (Cp n NE D) (Lb D Lv L M) (Fin (M + 1)) Ns NE

/-- The empty data. -/
def emptyT : RawT n NE D Lv L M := (fun _ => none, fun _ _ => 0, 0)

theorem valid_emptyT : Valid Ns (emptyT (n := n) (NE := NE) (D := D) (Lv := Lv) (L := L) (M := M)) := by
  refine ⟨?_, fun _ _ _ => rfl⟩
  have : U (emptyT (n := n) (NE := NE) (D := D) (Lv := Lv) (L := L) (M := M)) = ∅ := by
    ext c; simp [U, emptyT]
  rw [this]; simp

open Classical in
/-- Keep valid data, reset invalid data. -/
noncomputable def validate (y : RawT n NE D Lv L M) : StT n NE D Lv L M Ns :=
  if h : Valid Ns y then ⟨y, h⟩ else ⟨emptyT, valid_emptyT Ns⟩

/-- Pool mask of a label. -/
def mk (o : Option (Lb D Lv L M)) (r : Fin D) (ℓ : Fin Lv) : Bool :=
  match o with
  | some v => v.1 r ℓ
  | none => false

/-- The pools of the data, as an `ℕ × ℕ`-indexed family (empty off `r < D`, `ℓ < Lv`). -/
noncomputable def Pn (x : RawT n NE D Lv L M) (r ℓ : ℕ) : Finset (Cp n NE D) :=
  if h : r < D ∧ ℓ < Lv then univ.filter fun c => mk (x.1 c) ⟨r, h.1⟩ ⟨ℓ, h.2⟩ = true else ∅

/-- Learner data of a label at level `ℓ`. -/
def ldo (o : Option (Lb D Lv L M)) (ℓ : ℕ) : ℕ × ℕ :=
  match o with
  | some v => if h : ℓ < L + 1 then (((v.2 ⟨ℓ, h⟩).1 : ℕ), ((v.2 ⟨ℓ, h⟩).2 : ℕ)) else (0, 0)
  | none => (0, 0)

/-- Learner data of a copy at level `ℓ`. -/
def ld (x : RawT n NE D Lv L M) (c : Cp n NE D) (ℓ : ℕ) : ℕ × ℕ := ldo (x.1 c) ℓ

/-- Grid index. -/
def kLx (x : RawT n NE D Lv L M) : ℕ := x.2.2

/-- The sorted present copies. -/
noncomputable def lst (x : RawT n NE D Lv L M) : List (Cp n NE D) := srt x

/-- The queried arm of slot `k`. -/
noncomputable def qry (x : RawT n NE D Lv L M) (k : Fin Ns) : Fin n :=
  if h : k.1 < (lst x).length then arm n NE D (lst x)[k.1] else ⟨0, NeZero.pos n⟩

/-- The queried bit of copy `c` (its slot). -/
noncomputable def bitOf (x : RawT n NE D Lv L M) (o : Fin Ns → Bool) (c : Cp n NE D) : Bool :=
  if h : (lst x).idxOf c < Ns then o ⟨_, h⟩ else false

/-- P0102's machine weight of copy `c` at level `ℓ`. -/
noncomputable def wgt (x : RawT n NE D Lv L M) (c : Cp n NE D) (ℓ : ℕ) : ℝ :=
  Pool.P0102.mw η ε (fun _ => kLx x) (fun _ => ld x) 0 c ℓ

/-- P0102's awake mass. -/
noncomputable def mass (x : RawT n NE D Lv L M) : ℝ :=
  Pool.P0102.mA L (fun _ => U x) η ε (fun _ => kLx x) (fun _ => ld x) 0

/-- Arm law of the learner. -/
noncomputable def armW (x : RawT n NE D Lv L M) (i : Fin n) : ℝ :=
  (∑ c ∈ (U x).filter (fun c => arm n NE D c = i), ∑ ℓ : Fin (L + 1), wgt η ε x c ℓ) / mass (L := L) η ε x

theorem armW_nonneg (x : RawT n NE D Lv L M) (i : Fin n) : 0 ≤ armW η ε x i := by
  unfold armW mass Pool.P0102.mA
  apply div_nonneg <;> apply Finset.sum_nonneg <;> intro c _ <;> apply Finset.sum_nonneg <;>
    intro ℓ _ <;> exact (Pool.P0102.mw_pos _ _ _).le

theorem sum_armW (x : RawT n NE D Lv L M) (hne : (U x).Nonempty) : ∑ i, armW η ε x i = 1 := by
  unfold armW
  rw [← Finset.sum_div]
  have hpos : 0 < mass (L := L) η ε x := Pool.P0102.mA_pos (u := 0) hne
  rw [div_eq_one_iff_eq hpos.ne']
  rw [Finset.sum_fiberwise (U x) (arm n NE D) (fun c => ∑ ℓ : Fin (L + 1), wgt η ε x c ℓ)]
  rfl

open Classical in
/-- The play law. -/
noncomputable def playL (x : RawT n NE D Lv L M) : PMF (Fin n) :=
  if hne : (U x).Nonempty then
    PMF.ofFintype (fun i => ENNReal.ofReal (armW η ε x i)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => armW_nonneg η ε x i), sum_armW η ε x hne,
        ENNReal.ofReal_one])
  else PMF.pure ⟨0, NeZero.pos n⟩

/-- Bounded addition. -/
abbrev addB {m : ℕ} (v : Fin (m + 1)) (b : Bool) : Fin (m + 1) := Pool.P0078.addB v b

/-- Bounded embedding of a natural number. -/
def capN (m k : ℕ) : Fin (m + 1) := ⟨min k m, Nat.lt_succ_of_le (min_le_right _ _)⟩

open Classical in
/-- Cover data rebuilt from the table at merge time `a + 1`: `-tab c d` for a present copy `d` entering at `u`. -/
noncomputable def Cm (tab : Cp n NE D → Cp n NE D → Fin (NE + 1)) (V : Finset (Cp n NE D)) (a : ℕ)
    (c : Cp n NE D) (u : ℕ) : ℝ :=
  if u = a + 1 then 0 else
    if h : ∃ d ∈ V, E n NE D d = u then -((tab c h.choose : ℕ) : ℝ) else 0

/-- Filter coins of a day coin, as a P0065 per-thread family. -/
def φz (z : Jd n NE D Lt K → Bool) (r : ℕ) : ℕ → ℕ → Fin K → Cp n NE D → Bool :=
  fun _ ℓ k c => if h : r < D ∧ ℓ < Lt + 1 then z (Sum.inl (⟨r, h.1⟩, ⟨ℓ, h.2⟩, k, c)) else false

/-- Sampling coins of a day coin. -/
def ωz (z : Jd n NE D Lt K → Bool) : Cp n NE D → Bool := fun c => z (Sum.inr c)

open Classical in
/-- The new labels after the start operations of unit `a + 1`: the mask of the start pools `P2`, and the learner
data (accumulate for surviving specialists, restart otherwise; `k'` = new grid index). -/
noncomputable def newLab (x : RawT n NE D Lv L M) (bt : Cp n NE D → Bool) (a : ℕ) (k' : Fin (M + 1))
    (P2 : ℕ → ℕ → Finset (Cp n NE D)) (c : Cp n NE D) : Option (Lb D Lv L M) :=
  if ∃ (r : Fin D) (ℓ : Fin Lv), c ∈ P2 r ℓ then
    some (fun r ℓ => decide (c ∈ P2 r ℓ), fun ℓ =>
      match x.1 c with
      | some v => if ¬ 2 ^ (ℓ : ℕ) ∣ a + 1 then (addB (v.2 ℓ).1 (bt c), (v.2 ℓ).2) else (0, k')
      | none => (0, k'))
  else none

/-- New grid index after the losses of the day (P0102's `inc`, capped at `M`). -/
noncomputable def kNew (x : RawT n NE D Lv L M) (o : Fin Ns → Bool) : Fin (M + 1) :=
  capN M (kLx x + Pool.P0102.inc L (fun _ => U x) (fun _ c => (bitOf Ns x o c).toNat) η ε (fun _ => kLx x)
    (fun _ => ld x) 0)

/-- Table after the losses of the day. -/
noncomputable def tabN (x : RawT n NE D Lv L M) (o : Fin Ns → Bool) : Cp n NE D → Cp n NE D → Fin (NE + 1) :=
  fun c d => addB (x.2.1 c d) (bitOf Ns x o c)

open Classical in
/-- Pools after the merges ending unit `a`. -/
noncomputable def P1Of (x : RawT n NE D Lv L M) (a : ℕ) (o : Fin Ns → Bool) (z : Jd n NE D Lt K → Bool) :
    ℕ → ℕ → Finset (Cp n NE D) := fun r =>
  if Bt r ∣ a + 1 then mergeUpTo (E n NE D) (Cm (tabN Ns x o) (U x) a) θ R K (φz z r) a (lev r a) (Pn x r)
  else Pn x r

/-- Start pools of unit `a + 1`. -/
noncomputable def P2Of (x : RawT n NE D Lv L M) (a : ℕ) (o : Fin Ns → Bool) (z : Jd n NE D Lt K → Bool) :
    ℕ → ℕ → Finset (Cp n NE D) :=
  startPools (E n NE D) (thr0 n NE D) D Lv Bt (ωz z) (a + 1) (P1Of (R := R) Bt lev θ Ns x a o z)

open Classical in
/-- **One day's update** for unit `a` (day `a + 1`): learner and table update with the queried bits, merges at the
end of unit `a`, start operations of unit `a + 1`. -/
noncomputable def stepRaw (x : RawT n NE D Lv L M) (a : ℕ) (o : Fin Ns → Bool) (z : Jd n NE D Lt K → Bool) :
    RawT n NE D Lv L M :=
  (newLab x (bitOf Ns x o) a (kNew η ε Ns x o) (P2Of (R := R) Bt lev θ Ns x a o z),
   fun c d => if (newLab x (bitOf Ns x o) a (kNew η ε Ns x o) (P2Of (R := R) Bt lev θ Ns x a o z) c).isSome ∧
     (newLab x (bitOf Ns x o) a (kNew η ε Ns x o) (P2Of (R := R) Bt lev θ Ns x a o z) d).isSome ∧
     c ∈ U x ∧ d ∈ U x then tabN Ns x o c d else 0,
   kNew η ε Ns x o)

open Classical in
/-- Initial data (day `0`): P0065's start pools of unit `0`, all learner data `(0, 0)`. -/
noncomputable def initRaw (z : Jd n NE D Lt K → Bool) : RawT n NE D Lv L M :=
  let P2 := startPools (E n NE D) (thr0 n NE D) D Lv Bt (ωz z) 0 (fun _ _ => ∅)
  (fun c => if ∃ (r : Fin D) (ℓ : Fin Lv), c ∈ P2 r ℓ then some (fun r ℓ => decide (c ∈ P2 r ℓ), fun _ => (0, 0))
    else none, fun _ _ => 0, 0)

/-- Coordinate probabilities of a day coin. -/
def qd (ps q : ℝ) : Jd n NE D Lt K → ℝ := Sum.elim (fun _ => q) (fun _ => ps)

theorem qd_mem {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) (j : Jd n NE D Lt K) :
    0 ≤ qd ps q j ∧ qd ps q j ≤ 1 := by
  cases j <;> simp [qd, hps, hq]

open Classical in
/-- **The threaded K-query pool learner** (`Ns` queries per day; the update ignores the played arm). -/
noncomputable def tmach {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1) : Pool.P0064.QCoinAlg n Ns where
  S := StT n NE D Lv L M Ns
  Z := Jd n NE D Lt K → Bool
  ν := Pool.P0051.bernVec (qd ps q) (qd_mem hps hq)
  s0 := ⟨emptyT, valid_emptyT Ns⟩
  play _ s := playL η ε s.1
  query _ s := qry Ns s.1
  upd t s o z := if t = 0 then validate Ns (initRaw Bt z)
    else validate Ns (stepRaw (R := R) Bt lev θ η ε Ns s.1 (t - 1) o z)

end Pool.P0121.TM
