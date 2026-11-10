import Pool.P0064.QCoin
import Pool.P0078.State
import Pool.P0068.Locality
import Pool.P0061.Process
import Pool.P0063.GoodRunProb
import Pool.P0051.CoinProc

/-!
# The Peng–Rubinstein K-query baseline as a finite-state machine that runs P0052's sub-pool process

Copies `Cp n NE = Fin (NE * n)`: copy `c` is arm `c % n` (`arm`) entering at epoch `c / n` (`E`).
`mach` is a P0064 `QCoinAlg` with `Ns` queries per day and state type `St Ns` (`State.lean`: sub-pools at
levels `0..Lt`, the table `D c d` = loss of `c` since the entry epoch of `d`, the in-epoch losses `ep c`, all supported
on at most `Ns` copies). Day `0` plays an arbitrary arm and its update samples the copies of epoch `0`; epoch `a`
occupies days `aB+1, …, aB+B`.
* Play (`playL`): Hedge over the copies of the pool with weights `exp (-η · ep c)`.
* Queries (`qry`): the arm of each slot of the sorted pool.
* Update: add the queried bits (`dayUpd`). At the end of epoch `a` (`epochEnd`): P0052's merges at levels
  `0..lev a`, with the cover data `Cm` rebuilt from the table `D`, then the copies sampled for epoch `a+1` join
  level `0`. Results with more than `Ns` copies reset the state (`validate`), so the memory bound holds on every path.

Main result `run_inv`: on every coin path on which every epoch so far is `Good` (P0052's start pools have no copy
above level `Lt` and at most `Ns` copies), the machine's state at day `aB + r + 1` is P0052's start pool of epoch
`a`, driven by the slot array `Φ` read off the machine's coins, and its tables hold the true in-lifetime losses
(`Inv`). The merges with `Cm` equal those with the true cumulative losses by P0068's breakpoint locality
(`agreeOn_Cm`, `mergeUpTo_congrC`).
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0030 Pool.P0042 Pool.P0052

namespace Pool.P0078

variable (n NE B Lt K R : ℕ) [NeZero n]

/-- Copies. -/
abbrev Cp := Fin (NE * n)

/-- Entry epoch of a copy. -/
def E (c : Cp n NE) : ℕ := c.1 / n

/-- Arm of a copy. -/
def arm (c : Cp n NE) : Fin n := ⟨c.1 % n, Nat.mod_lt _ (NeZero.pos n)⟩

theorem E_mono : Monotone (E n NE) := fun _ _ h => Nat.div_le_div_right h

/-- Update-coin coordinates of one day: filter bits `(ℓ, k, c)` and sampling bits `c`. -/
abbrev Jd := (Fin (Lt + 1) × Fin K × Cp n NE) ⊕ Cp n NE

variable {n NE B Lt K R}

section Defs

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ)

/-- Machine states. -/
abbrev St := PState (Cp n NE) Lt Ns (NE * B) B

/-- The empty state. -/
def emptyRaw : Raw (Cp n NE) Lt (NE * B) B := (fun _ => ∅, fun _ _ => 0, fun _ => 0)

theorem valid_empty : Valid Ns (emptyRaw (n := n) (NE := NE) (B := B) (Lt := Lt)) := by
  refine ⟨?_, fun _ _ _ => rfl, fun _ _ => rfl⟩
  show (univ.biUnion fun _ => (∅ : Finset (Cp n NE))).card ≤ Ns
  rw [show (univ.biUnion fun _ => (∅ : Finset (Cp n NE))) = ∅ by ext; simp]
  simp

open Classical in
/-- Keep valid data, reset invalid data. -/
noncomputable def validate (y : Raw (Cp n NE) Lt (NE * B) B) : St (n := n) (NE := NE) (B := B) (Lt := Lt) Ns :=
  if h : Valid Ns y then ⟨y, h⟩ else ⟨emptyRaw, valid_empty Ns⟩

/-- The sorted pool. -/
noncomputable def lst (x : Raw (Cp n NE) Lt (NE * B) B) : List (Cp n NE) := (U x).sort (· ≤ ·)

/-- The queried arm of slot `k`. -/
noncomputable def qry (x : Raw (Cp n NE) Lt (NE * B) B) (k : Fin Ns) : Fin n :=
  if h : k.1 < (lst x).length then arm n NE (lst x)[k.1] else ⟨0, NeZero.pos n⟩

/-- The queried bit of copy `c` (its slot). -/
noncomputable def bitOf (x : Raw (Cp n NE) Lt (NE * B) B) (o : Fin Ns → Bool) (c : Cp n NE) : Bool :=
  if h : (lst x).idxOf c < Ns then o ⟨_, h⟩ else false

/-- Bounded addition in `Fin (m + 1)`. -/
def addB {m : ℕ} (v : Fin (m + 1)) (b : Bool) : Fin (m + 1) :=
  ⟨min (v.1 + if b then 1 else 0) m, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- Add one day's queried bits. -/
noncomputable def dayUpd (x : Raw (Cp n NE) Lt (NE * B) B) (o : Fin Ns → Bool) : Raw (Cp n NE) Lt (NE * B) B :=
  (x.1,
   fun c d => if c ∈ U x ∧ d ∈ U x then addB (x.2.1 c d) (bitOf Ns x o c) else 0,
   fun c => if c ∈ U x then addB (x.2.2 c) (bitOf Ns x o c) else 0)

theorem U_dayUpd (x : Raw (Cp n NE) Lt (NE * B) B) (o : Fin Ns → Bool) : U (dayUpd Ns x o) = U x := rfl

theorem valid_dayUpd {x : Raw (Cp n NE) Lt (NE * B) B} (hx : Valid Ns x) (o : Fin Ns → Bool) :
    Valid Ns (dayUpd Ns x o) := by
  refine ⟨hx.1, fun c d hcd => ?_, fun c hc => ?_⟩
  · show (if c ∈ U x ∧ d ∈ U x then _ else _) = _
    rw [if_neg]; tauto
  · show (if c ∈ U x then _ else _) = _
    rw [if_neg (show c ∉ U x from hc)]

open Classical in
/-- Cover data rebuilt from the table at merge time `a + 1`: `-D c d` for a pool copy `d` entering at `u`. -/
noncomputable def Cm (x : Raw (Cp n NE) Lt (NE * B) B) (a : ℕ) (c : Cp n NE) (u : ℕ) : ℝ :=
  if u = a + 1 then 0 else
    if h : ∃ d ∈ U x, E n NE d = u then -((x.2.1 c h.choose : ℕ) : ℝ) else 0

/-- Sub-pools as an `ℕ`-indexed family (empty above `Lt`). -/
def Pf (x : Raw (Cp n NE) Lt (NE * B) B) (ℓ : ℕ) : Finset (Cp n NE) :=
  if h : ℓ < Lt + 1 then x.1 ⟨ℓ, h⟩ else ∅

/-- Filter coins of the epoch-end coin. -/
def φz (zf : Fin (Lt + 1) → Fin K → Cp n NE → Bool) : ℕ → ℕ → Fin K → Cp n NE → Bool :=
  fun _ ℓ k c => if h : ℓ < Lt + 1 then zf ⟨ℓ, h⟩ k c else false

open Classical in
/-- End of epoch `a`: merges at levels `0..lev a`, then the copies sampled for epoch `a + 1` join level `0`. -/
noncomputable def epochEnd (x : Raw (Cp n NE) Lt (NE * B) B) (a : ℕ) (z : Jd n NE Lt K → Bool) :
    Raw (Cp n NE) Lt (NE * B) B :=
  let P1 := mergeUpTo (E n NE) (Cm x a) θ R K (φz (fun ℓ k c => z (Sum.inl (ℓ, k, c)))) a (lev a) (Pf x)
  let N := newAt (E n NE) (fun c => z (Sum.inr c)) (a + 1)
  let P2 : Fin (Lt + 1) → Finset (Cp n NE) := fun ℓ => Function.update P1 0 (P1 0 ∪ N) ℓ
  (P2,
   fun c d => if c ∈ univ.biUnion P2 ∧ d ∈ univ.biUnion P2 ∧ d ∉ N then x.2.1 c d else 0,
   fun _ => 0)

/-- Initial data: the copies sampled for epoch `0` at level `0`. -/
noncomputable def initRaw (s : Cp n NE → Bool) : Raw (Cp n NE) Lt (NE * B) B :=
  (fun ℓ => if ℓ.1 = 0 then newAt (E n NE) s 0 else ∅, fun _ _ => 0, fun _ => 0)

/-- Hedge weights of the pool copies. -/
noncomputable def wt (x : Raw (Cp n NE) Lt (NE * B) B) (c : Cp n NE) : ℝ :=
  if c ∈ U x then Real.exp (-η * (x.2.2 c : ℕ)) else 0

/-- Arm law of Hedge over the pool copies. -/
noncomputable def armW (x : Raw (Cp n NE) Lt (NE * B) B) (i : Fin n) : ℝ :=
  (∑ c ∈ (U x).filter (fun c => arm n NE c = i), wt η x c) / ∑ c ∈ U x, wt η x c

theorem armW_nonneg (x : Raw (Cp n NE) Lt (NE * B) B) (i : Fin n) : 0 ≤ armW η x i := by
  unfold armW
  apply div_nonneg <;> apply Finset.sum_nonneg <;> intro c _ <;> unfold wt <;> split_ifs <;>
    first | exact (Real.exp_pos _).le | exact le_refl _

theorem sum_armW (x : Raw (Cp n NE) Lt (NE * B) B) (hne : (U x).Nonempty) : ∑ i, armW η x i = 1 := by
  unfold armW
  rw [← Finset.sum_div]
  have hpos : 0 < ∑ c ∈ U x, wt η x c := by
    apply Finset.sum_pos _ hne
    intro c hc; unfold wt; rw [if_pos hc]; exact Real.exp_pos _
  rw [div_eq_one_iff_eq hpos.ne']
  rw [← Finset.sum_fiberwise (U x) (arm n NE) (wt η x)]

open Classical in
/-- The play law. -/
noncomputable def playL (x : Raw (Cp n NE) Lt (NE * B) B) : PMF (Fin n) :=
  if hne : (U x).Nonempty then
    PMF.ofFintype (fun i => ENNReal.ofReal (armW η x i)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => armW_nonneg η x i), sum_armW η x hne, ENNReal.ofReal_one])
  else PMF.pure ⟨0, NeZero.pos n⟩

end Defs


section Lemmas

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ)

theorem lst_length_le {x : Raw (Cp n NE) Lt (NE * B) B} (hx : Valid Ns x) : (lst x).length ≤ Ns := by
  unfold lst; rw [Finset.length_sort]; exact hx.1

theorem mem_lst {x : Raw (Cp n NE) Lt (NE * B) B} {c : Cp n NE} : c ∈ lst x ↔ c ∈ U x := by
  unfold lst; exact Finset.mem_sort _

/-- The queried bit of a pool copy is the loss bit of its arm. -/
theorem bitOf_eq {x : Raw (Cp n NE) Lt (NE * B) B} (hx : Valid Ns x) (v : Fin n → Bool) {c : Cp n NE}
    (hc : c ∈ U x) : bitOf Ns x (fun k => v (qry Ns x k)) c = v (arm n NE c) := by
  have hmem : c ∈ lst x := mem_lst.mpr hc
  have hlt : (lst x).idxOf c < (lst x).length := List.idxOf_lt_length_iff.mpr hmem
  have hNs : (lst x).idxOf c < Ns := lt_of_lt_of_le hlt (lst_length_le Ns hx)
  unfold bitOf qry
  rw [dif_pos hNs]
  simp only [dif_pos hlt, List.getElem_idxOf hlt]

/-- Days of epochs `[u, v)` regrouped by epoch. -/
theorem sum_Ico_mul (f : ℕ → ℕ) (u : ℕ) : ∀ v, u ≤ v →
    ∑ w ∈ Ico (u * B) (v * B), f w = ∑ e ∈ Ico u v, ∑ r ∈ range B, f (e * B + r) := by
  intro v huv
  induction v, huv using Nat.le_induction with
  | base => simp
  | succ v huv ih =>
    rw [Finset.sum_Ico_succ_top huv, ← ih, Nat.succ_mul,
      ← Finset.sum_Ico_consecutive _ (Nat.mul_le_mul_right B huv) (Nat.le_add_right _ _)]
    congr 1
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [add_tsub_cancel_left]

theorem addB_val {m : ℕ} (v : Fin (m + 1)) (b : Bool) (h : v.1 + (if b then 1 else 0) ≤ m) :
    (addB v b : ℕ) = v.1 + if b then 1 else 0 := by
  simp [addB, min_eq_left h]

end Lemmas


section Alg

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) {ps p : ℝ}

/-- Coordinate probabilities of a day's update coin. -/
def qd (ps p : ℝ) : Jd n NE Lt K → ℝ := Sum.elim (fun _ => p) (fun _ => ps)

theorem qd_mem (hps : 0 ≤ ps ∧ ps ≤ 1) (hp : 0 ≤ p ∧ p ≤ 1) (j : Jd n NE Lt K) :
    0 ≤ qd ps p j ∧ qd ps p j ≤ 1 := by
  cases j <;> simp [qd, hps, hp]

open Classical in
/-- **The K-query pool learner** (`Ns` queries per day, update ignores the played arm). Day `0` plays an arbitrary
arm and its update samples the copies of epoch `0`; epoch `a` then occupies days `aB+1, …, aB+B`. -/
noncomputable def mach (hps : 0 ≤ ps ∧ ps ≤ 1) (hp : 0 ≤ p ∧ p ≤ 1) : Pool.P0064.QCoinAlg n Ns where
  S := St (n := n) (NE := NE) (B := B) (Lt := Lt) Ns
  Z := Jd n NE Lt K → Bool
  ν := Pool.P0051.bernVec (qd ps p) (qd_mem hps hp)
  s0 := ⟨emptyRaw, valid_empty Ns⟩
  play _ s := playL η s.1
  query _ s := qry Ns s.1
  upd t s o z := if t = 0 then validate Ns (initRaw (fun c => z (Sum.inr c)))
    else if (t - 1) % B = B - 1 then validate Ns (epochEnd (R := R) θ lev (dayUpd Ns s.1 o) ((t - 1) / B) z)
    else ⟨dayUpd Ns s.1 o, valid_dayUpd Ns s.2 o⟩

end Alg


section Congr

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E' : ι → ℕ) (C C' : ι → ℕ → ℝ) (θ : ℝ) (R K : ℕ)

/-- Merges with two cover data that agree on every interval read inside `Q` coincide. -/
theorem mergeUpTo_congrC (φ : ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) (Q : Finset ι)
    (hQ : Pool.P0068.AgreeOn E' C C' Q (Pool.P0068.bp E' (a + 1) Q)) :
    ∀ m (P : ℕ → Finset ι), (∀ ℓ, P ℓ ⊆ Q) →
      mergeUpTo E' C θ R K φ a m P = mergeUpTo E' C' θ R K φ a m P := by
  have hone : ∀ ℓ (P : ℕ → Finset ι), (∀ ℓ, P ℓ ⊆ Q) →
      mergeOne E' C θ R K φ a ℓ P = mergeOne E' C' θ R K φ a ℓ P := by
    intro ℓ P hP
    unfold mergeOne
    have hsub : P (ℓ + 1) ∪ P ℓ ⊆ Q := Finset.union_subset (hP _) (hP _)
    rw [Pool.P0068.iter_congr θ R _ ((hQ.mono hsub).mono_set (Pool.P0068.bp_mono hsub)) K (φ a ℓ)]
  intro m
  induction m with
  | zero => intro P hP; exact hone 0 P hP
  | succ m ih =>
    intro P hP
    simp only [mergeUpTo]
    rw [ih P hP]
    apply hone
    intro ℓ c hc
    obtain ⟨i, hi⟩ := Pool.P0063.mem_mergeUpTo E' C' θ R K φ a m P ℓ c hc
    exact hP i hi

end Congr


section Inv

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) (ℓs : LossSeq n)

/-- Loss bit as a natural number. -/
def lv (t : ℕ) (i : Fin n) : ℕ := (ℓs t i).toNat

/-- Epoch loss of a copy. -/
def epL (u : ℕ) (c : Cp n NE) : ℝ := ∑ r ∈ range B, (lv ℓs (u * B + r) (arm n NE c) : ℝ)

/-- True cumulative epoch losses (P0061's `cumL`). -/
noncomputable def Ctrue : Cp n NE → ℕ → ℝ := Pool.P0061.cumL (epL (B := B) ℓs)

/-- The slot array (P0063) read off the machine's coins. -/
def Φ (x : Cp n NE → Bool) (zz : ℕ → Jd n NE Lt K → Bool) : Pool.P0063.Slot NE Lt K → Cp n NE → Bool
  | Sum.inl a, c => if a.1 = 0 then x c else zz (a.1 * B - 1) (Sum.inr c)
  | Sum.inr (a, ℓ, k), c => zz (a.1 * B + B - 1) (Sum.inl (ℓ, k, c))

/-- P0052's start pools of the run driven by the slot array `ω`. -/
noncomputable abbrev SP (ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool) (a : ℕ) : ℕ → Finset (Cp n NE) :=
  Pool.P0061.startPool (E n NE) (Ctrue (B := B) ℓs) θ R K lev
    (Pool.P0063.ωsOf (E n NE) K ω) (Pool.P0063.φOf K ω) a

/-- Good epoch: no copies above level `Lt` (a deterministic condition: needs `lev a + 1 ≤ Lt`), at most `Ns` copies. -/
def Good (ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool) (a : ℕ) : Prop :=
  (∀ ℓ, Lt + 1 ≤ ℓ → SP (B := B) (R := R) θ lev ℓs ω a ℓ = ∅) ∧
    (univ.biUnion fun ℓ : Fin (Lt + 1) => SP (B := B) (R := R) θ lev ℓs ω a ℓ).card ≤ Ns

/-- The invariant at day `a B + r`. -/
def Inv (ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool) (a r : ℕ) (x : Raw (Cp n NE) Lt (NE * B) B) : Prop :=
  (∀ ℓ : Fin (Lt + 1), x.1 ℓ = SP (B := B) (R := R) θ lev ℓs ω a ℓ) ∧
  (∀ c ∈ U x, ∀ d ∈ U x, E n NE c ≤ E n NE d →
    (x.2.1 c d : ℕ) = ∑ w ∈ Ico (E n NE d * B) (a * B + r), lv ℓs w (arm n NE c)) ∧
  ∀ c ∈ U x, (x.2.2 c : ℕ) = ∑ w ∈ Ico (a * B) (a * B + r), lv ℓs w (arm n NE c)

end Inv


section InvLemmas

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) (ℓs : LossSeq n)

theorem E_lt (c : Cp n NE) : E n NE c < NE := by
  unfold E
  have h : c.1 < NE * n := c.2
  have h' : c.1 < n * NE := by linarith [Nat.mul_comm NE n]
  exact Nat.div_lt_of_lt_mul h'

theorem ωsOf_Φ (x : Cp n NE → Bool) (zz : ℕ → Jd n NE Lt K → Bool) (c : Cp n NE) :
    Pool.P0063.ωsOf (E n NE) K (Φ (B := B) x zz) c =
      if E n NE c = 0 then x c else zz (E n NE c * B - 1) (Sum.inr c) := by
  unfold Pool.P0063.ωsOf
  rw [dif_pos (E_lt c)]
  rfl

theorem newAt_Φ_zero (x : Cp n NE → Bool) (zz : ℕ → Jd n NE Lt K → Bool) :
    newAt (E n NE) (Pool.P0063.ωsOf (E n NE) K (Φ (B := B) x zz)) 0 = newAt (E n NE) x 0 := by
  ext c
  simp only [newAt, Finset.mem_filter, Finset.mem_univ, true_and, ωsOf_Φ]
  constructor
  · rintro ⟨h1, h2⟩; rw [if_pos h1] at h2; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; rw [if_pos h1]; exact ⟨h1, h2⟩

theorem newAt_Φ_succ (x : Cp n NE → Bool) (zz : ℕ → Jd n NE Lt K → Bool) (a : ℕ) :
    newAt (E n NE) (Pool.P0063.ωsOf (E n NE) K (Φ (B := B) x zz)) (a + 1) =
      newAt (E n NE) (fun c => zz (a * B + B - 1) (Sum.inr c)) (a + 1) := by
  ext c
  simp only [newAt, Finset.mem_filter, Finset.mem_univ, true_and, ωsOf_Φ]
  have e : (a + 1) * B - 1 = a * B + B - 1 := by rw [Nat.succ_mul]
  constructor
  · rintro ⟨h1, h2⟩; rw [if_neg (by omega), h1, e] at h2; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩; rw [if_neg (by omega), h1, e]; exact h2

theorem φz_Φ (x : Cp n NE → Bool) (zz : ℕ → Jd n NE Lt K → Bool) (a : ℕ) (ha : a < NE) (ℓ : ℕ)
    (hℓ : ℓ < Lt + 1) :
    φz (fun ℓ k c => zz (a * B + B - 1) (Sum.inl (ℓ, k, c))) a ℓ =
      Pool.P0063.φOf K (Φ (B := B) x zz) a ℓ := by
  funext k c
  unfold φz Pool.P0063.φOf
  rw [dif_pos hℓ, dif_pos ⟨ha, hℓ⟩]
  rfl

theorem E_le_of_mem_SP (ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool) (a ℓ : ℕ) (c : Cp n NE)
    (hc : c ∈ SP (B := B) (R := R) θ lev ℓs ω a ℓ) : E n NE c ≤ a :=
  Pool.P0063.E_le_of_mem_beforeMerge (E n NE) _ θ R K lev _ _ a 0 ℓ c hc

end InvLemmas


section InitInv

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) (ℓs : LossSeq n)

theorem U_of_P {x : Raw (Cp n NE) Lt (NE * B) B} {ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool} {a : ℕ}
    (h : ∀ ℓ : Fin (Lt + 1), x.1 ℓ = SP (B := B) (R := R) θ lev ℓs ω a ℓ) :
    U x = univ.biUnion fun ℓ : Fin (Lt + 1) => SP (B := B) (R := R) θ lev ℓs ω a ℓ := by
  unfold U
  congr 1
  funext ℓ
  exact h ℓ

theorem SP_zero (ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool) (ℓ : ℕ) :
    SP (B := B) (R := R) θ lev ℓs ω 0 ℓ =
      if ℓ = 0 then newAt (E n NE) (Pool.P0063.ωsOf (E n NE) K ω) 0 else ∅ := by
  show Function.update (pools (E n NE) _ θ R K lev _ _ 0) 0 _ ℓ = _
  by_cases h : ℓ = 0
  · subst h; simp [pools]
  · rw [Function.update_of_ne h, if_neg h]; rfl

theorem init_inv (x : Cp n NE → Bool) (zz : ℕ → Jd n NE Lt K → Bool)
    (hg : Good (B := B) Ns θ lev ℓs (R := R) (Φ (B := B) x zz) 0) :
    Valid Ns (initRaw (B := B) (Lt := Lt) x) ∧
      Inv θ lev ℓs (R := R) (Φ (B := B) x zz) 0 0 (initRaw (B := B) (Lt := Lt) x) := by
  have hP : ∀ ℓ : Fin (Lt + 1), (initRaw (B := B) (Lt := Lt) x).1 ℓ =
      SP (B := B) (R := R) θ lev ℓs (Φ (B := B) x zz) 0 ℓ := by
    intro ℓ
    rw [SP_zero, newAt_Φ_zero]
    rfl
  refine ⟨⟨?_, fun _ _ _ => rfl, fun _ _ => rfl⟩, hP, ?_, ?_⟩
  · rw [U_of_P θ lev ℓs hP]; exact hg.2
  · intro c _ d _ _
    simp [initRaw]
  · intro c _
    simp [initRaw]

end InitInv


section DayInv

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) (ℓs : LossSeq n)

theorem lv_le_one (t : ℕ) (i : Fin n) : lv ℓs t i ≤ 1 := by
  unfold lv; cases ℓs t i <;> simp

theorem sum_lv_le (m k : ℕ) (i : Fin n) : ∑ w ∈ Ico m k, lv ℓs w i ≤ k - m := by
  calc ∑ w ∈ Ico m k, lv ℓs w i ≤ ∑ _w ∈ Ico m k, 1 := Finset.sum_le_sum fun w _ => lv_le_one ℓs w i
    _ = k - m := by simp

theorem toNat_eq_ite (b : Bool) : b.toNat = if b then 1 else 0 := by cases b <;> rfl

theorem day_inv {x : Raw (Cp n NE) Lt (NE * B) B} (hx : Valid Ns x)
    {ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool} {a r : ℕ}
    (hinv : Inv θ lev ℓs (R := R) ω a r x) (hr : a * B + r < NE * B) (hrB : r < B) :
    Inv θ lev ℓs (R := R) ω a (r + 1) (dayUpd Ns x (fun k => ℓs (a * B + r) (qry Ns x k))) := by
  have hEa : ∀ d ∈ U x, E n NE d ≤ a := by
    intro d hd
    rw [U_of_P θ lev ℓs hinv.1] at hd
    obtain ⟨ℓ, -, hℓ⟩ := Finset.mem_biUnion.mp hd
    exact E_le_of_mem_SP θ lev ℓs ω a ℓ d hℓ
  refine ⟨hinv.1, ?_, ?_⟩
  · intro c hc d hd hcd
    have hc : c ∈ U x := hc
    have hd : d ∈ U x := hd
    show ((if c ∈ U x ∧ d ∈ U x then addB (x.2.1 c d) (bitOf Ns x _ c) else 0 : Fin _) : ℕ) = _
    rw [if_pos ⟨hc, hd⟩, bitOf_eq Ns hx (ℓs (a * B + r)) hc]
    have h0 := hinv.2.1 c hc d hd hcd
    have hle : E n NE d * B ≤ a * B + r := le_trans (Nat.mul_le_mul_right B (hEa d hd)) (Nat.le_add_right _ _)
    rw [addB_val, h0, ← add_assoc, Finset.sum_Ico_succ_top hle, ← toNat_eq_ite]
    · rfl
    · rw [h0]
      have := sum_lv_le ℓs (E n NE d * B) (a * B + r) (arm n NE c)
      split_ifs <;> omega
  · intro c hc
    have hc : c ∈ U x := hc
    show ((if c ∈ U x then addB (x.2.2 c) (bitOf Ns x _ c) else 0 : Fin _) : ℕ) = _
    rw [if_pos hc, bitOf_eq Ns hx (ℓs (a * B + r)) hc]
    have h0 := hinv.2.2 c hc
    rw [addB_val, h0, ← add_assoc, Finset.sum_Ico_succ_top (Nat.le_add_right _ _), ← toNat_eq_ite]
    · rfl
    · rw [h0]
      have := sum_lv_le ℓs (a * B) (a * B + r) (arm n NE c)
      split_ifs <;> omega

end DayInv


section EndInv

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) (ℓs : LossSeq n)

/-- Day sums of a copy's losses equal differences of `Ctrue`. -/
theorem Ctrue_sub (i : Cp n NE) (u v : ℕ) (huv : u ≤ v) :
    Ctrue (B := B) ℓs i v - Ctrue (B := B) ℓs i u =
      ((∑ w ∈ Ico (u * B) (v * B), lv ℓs w (arm n NE i) : ℕ) : ℝ) := by
  have h1 := Pool.P0061.Lint_cumL (epL (B := B) ℓs) i huv
  unfold Pool.P0030.Lint at h1
  unfold Ctrue
  rw [h1, sum_Ico_mul (B := B) _ u v huv]
  push_cast
  rfl

theorem agreeOn_Cm {x : Raw (Cp n NE) Lt (NE * B) B} {ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool} {a : ℕ}
    (hinv : Inv θ lev ℓs (R := R) ω a B x) :
    Pool.P0068.AgreeOn (E n NE) (Ctrue (B := B) ℓs) (Cm x a) (U x) (Pool.P0068.bp (E n NE) (a + 1) (U x)) := by
  classical
  have hEa : ∀ d ∈ U x, E n NE d ≤ a := by
    intro d hd
    rw [U_of_P θ lev ℓs hinv.1] at hd
    obtain ⟨ℓ, -, hℓ⟩ := Finset.mem_biUnion.mp hd
    exact E_le_of_mem_SP θ lev ℓs ω a ℓ d hℓ
  have key : ∀ i ∈ U x, ∀ u ∈ Pool.P0068.bp (E n NE) (a + 1) (U x), E n NE i ≤ u →
      Cm x a i u = Ctrue (B := B) ℓs i u - Ctrue (B := B) ℓs i (a + 1) := by
    intro i hi u hu hiu
    unfold Cm
    by_cases hua : u = a + 1
    · rw [if_pos hua, hua, sub_self]
    · rw [if_neg hua]
      have hex : ∃ d ∈ U x, E n NE d = u := by
        rcases hu with h | ⟨d, hd, hdu⟩
        · exact absurd h hua
        · exact ⟨d, hd, hdu⟩
      rw [dif_pos hex]
      obtain ⟨hdU, hdE⟩ := hex.choose_spec
      have hD := hinv.2.1 i hi hex.choose hdU (by rw [hdE]; exact hiu)
      rw [hD, hdE]
      have hle : u ≤ a + 1 := by have := hEa _ hdU; omega
      rw [← neg_sub, Ctrue_sub ℓs i u (a + 1) hle, Nat.succ_mul]
  intro i hi u hu v hv hiu huv
  unfold Pool.P0030.Lint
  rw [key i hi u hu hiu, key i hi v hv (hiu.trans huv)]
  ring

theorem Pf_eq {x : Raw (Cp n NE) Lt (NE * B) B} {ω : Pool.P0063.Slot NE Lt K → Cp n NE → Bool} {a r : ℕ}
    (hinv : Inv θ lev ℓs (R := R) ω a r x) (hg : Good (B := B) Ns θ lev ℓs (R := R) ω a) :
    Pf x = SP (B := B) (R := R) θ lev ℓs ω a := by
  funext ℓ
  unfold Pf
  split_ifs with h
  · exact hinv.1 ⟨ℓ, h⟩
  · exact (hg.1 ℓ (by omega)).symm

theorem end_inv {x' : Raw (Cp n NE) Lt (NE * B) B} (xx : Cp n NE → Bool) (zz : ℕ → Jd n NE Lt K → Bool)
    {a : ℕ} (ha : a + 1 < NE) (hlev : lev a < Lt + 1)
    (hinv : Inv θ lev ℓs (R := R) (Φ (B := B) xx zz) a B x')
    (hga : Good (B := B) Ns θ lev ℓs (R := R) (Φ (B := B) xx zz) a)
    (hg1 : Good (B := B) Ns θ lev ℓs (R := R) (Φ (B := B) xx zz) (a + 1)) :
    Valid Ns (epochEnd (R := R) θ lev x' a (zz (a * B + B - 1))) ∧
      Inv θ lev ℓs (R := R) (Φ (B := B) xx zz) (a + 1) 0 (epochEnd (R := R) θ lev x' a (zz (a * B + B - 1))) := by
  classical
  set ω := Φ (B := B) xx zz with hω
  set z := zz (a * B + B - 1)
  have hP1 : mergeUpTo (E n NE) (Cm x' a) θ R K (φz (fun ℓ k c => z (Sum.inl (ℓ, k, c)))) a (lev a) (Pf x') =
      pools (E n NE) (Ctrue (B := B) ℓs) θ R K lev (Pool.P0063.ωsOf (E n NE) K ω) (Pool.P0063.φOf K ω) (a + 1) := by
    rw [Pf_eq Ns θ lev ℓs hinv hga]
    rw [← mergeUpTo_congrC (E n NE) (Ctrue (B := B) ℓs) (Cm x' a) θ R K _ a (U x')
      (agreeOn_Cm θ lev ℓs hinv) (lev a) _ ?_]
    · rw [Pool.P0063.mergeUpTo_congr (E n NE) _ θ R K _ (Pool.P0063.φOf K ω) a (lev a)
        (fun ℓ hℓ => φz_Φ xx zz a (by omega) ℓ (by omega))]
      rfl
    · intro ℓ c hc
      rw [U_of_P θ lev ℓs hinv.1]
      by_cases hℓ : ℓ < Lt + 1
      · exact Finset.mem_biUnion.mpr ⟨⟨ℓ, hℓ⟩, Finset.mem_univ _, hc⟩
      · rw [hga.1 ℓ (by omega)] at hc; simp at hc
  have hN : newAt (E n NE) (fun c => z (Sum.inr c)) (a + 1) =
      newAt (E n NE) (Pool.P0063.ωsOf (E n NE) K ω) (a + 1) := (newAt_Φ_succ xx zz a).symm
  have hP : ∀ ℓ : Fin (Lt + 1), (epochEnd (R := R) θ lev x' a z).1 ℓ = SP (B := B) (R := R) θ lev ℓs ω (a + 1) ℓ := by
    intro ℓ
    show Function.update (mergeUpTo (E n NE) (Cm x' a) θ R K _ a (lev a) (Pf x')) 0 _ ℓ = _
    rw [hP1, hN]
    rfl
  have hU : U (epochEnd (R := R) θ lev x' a z) = univ.biUnion fun ℓ : Fin (Lt + 1) =>
      SP (B := B) (R := R) θ lev ℓs ω (a + 1) ℓ := U_of_P θ lev ℓs hP
  set N := newAt (E n NE) (fun c => z (Sum.inr c)) (a + 1) with hNdef
  set P1 := mergeUpTo (E n NE) (Cm x' a) θ R K (φz (fun ℓ k c => z (Sum.inl (ℓ, k, c)))) a (lev a) (Pf x')
  have hold : ∀ c ∈ U (epochEnd (R := R) θ lev x' a z), c ∉ N → c ∈ U x' := by
    intro c hc hcN
    obtain ⟨ℓ, -, hℓ⟩ := Finset.mem_biUnion.mp hc
    have hℓ' : c ∈ Function.update P1 0 (P1 0 ∪ N) ℓ := hℓ
    have hc1 : ∃ j, c ∈ P1 j := by
      by_cases h0 : (ℓ : ℕ) = 0
      · rw [h0, Function.update_self] at hℓ'
        rcases Finset.mem_union.mp hℓ' with h | h
        · exact ⟨0, h⟩
        · exact absurd h hcN
      · rw [Function.update_of_ne h0] at hℓ'; exact ⟨ℓ, hℓ'⟩
    obtain ⟨j, hj⟩ := hc1
    obtain ⟨i, hi⟩ := Pool.P0063.mem_mergeUpTo (E n NE) (Cm x' a) θ R K _ a (lev a) (Pf x') j c hj
    unfold Pf at hi
    split_ifs at hi with hil
    · exact Finset.mem_biUnion.mpr ⟨⟨i, hil⟩, Finset.mem_univ _, hi⟩
    · simp at hi
  have hEa : ∀ d ∈ U x', E n NE d ≤ a := by
    intro d hd
    rw [U_of_P θ lev ℓs hinv.1] at hd
    obtain ⟨ℓ, -, hℓ⟩ := Finset.mem_biUnion.mp hd
    exact E_le_of_mem_SP θ lev ℓs ω a ℓ d hℓ
  have hEN : ∀ c ∈ N, E n NE c = a + 1 := by
    intro c hc
    simp only [hNdef, newAt, Finset.mem_filter] at hc
    exact hc.2.1
  refine ⟨⟨by rw [hU]; exact hg1.2, ?_, fun _ _ => rfl⟩, hP, ?_, ?_⟩
  · intro c d hcd
    show (if c ∈ U (epochEnd (R := R) θ lev x' a z) ∧ d ∈ U (epochEnd (R := R) θ lev x' a z) ∧ d ∉ N
      then x'.2.1 c d else 0) = 0
    rw [if_neg]; tauto
  · intro c hc d hd hcd
    show ((if c ∈ U (epochEnd (R := R) θ lev x' a z) ∧ d ∈ U (epochEnd (R := R) θ lev x' a z) ∧ d ∉ N
      then x'.2.1 c d else 0 : Fin _) : ℕ) = _
    by_cases hdN : d ∈ N
    · rw [if_neg (by tauto), hEN d hdN]
      simp
    · rw [if_pos ⟨hc, hd, hdN⟩]
      have hd' := hold d hd hdN
      have hcN : c ∉ N := by
        intro hcN; have := hEN c hcN; have := hEa d hd'; omega
      have hc' := hold c hc hcN
      rw [hinv.2.1 c hc' d hd' hcd, Nat.succ_mul, Nat.add_zero]
  · intro c _
    show ((0 : Fin _) : ℕ) = _
    simp

end EndInv


section RunInv

variable (Ns : ℕ) (θ η : ℝ) (lev : ℕ → ℕ) (ℓs : LossSeq n) {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1)
  (hp : 0 ≤ p ∧ p ≤ 1)

/-- **The machine follows P0052's process on good runs.** Write `zf` for the update coins. At day `t + 1`
(`t = aB + r`), if every epoch up to `a` is good for the slot array `Φ (zf 0 ∘ inr) (zf ∘ succ)`, the state's
sub-pools are P0052's start pools of epoch `a` and its tables hold the true in-lifetime losses of the shifted loss
sequence `u ↦ ℓ (u + 1)`. -/
theorem run_inv (hB : 0 < B) (hlev : ∀ a < NE, lev a < Lt + 1) (ℓ : LossSeq n) (zf : ℕ → Jd n NE Lt K → Bool) :
    ∀ t, t < NE * B →
      (∀ a ≤ t / B, Good (B := B) Ns θ lev (fun u => ℓ (u + 1)) (R := R)
        (Φ (B := B) (fun c => zf 0 (Sum.inr c)) (fun u => zf (u + 1))) a) →
      Inv θ lev (fun u => ℓ (u + 1)) (R := R) (Φ (B := B) (fun c => zf 0 (Sum.inr c)) (fun u => zf (u + 1)))
        (t / B) (t % B) ((mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ (t + 1) (fun i => zf i)).1 := by
  set ℓs : LossSeq n := fun u => ℓ (u + 1) with hℓs
  set xx : Cp n NE → Bool := fun c => zf 0 (Sum.inr c)
  set zz : ℕ → Jd n NE Lt K → Bool := fun u => zf (u + 1)
  intro t
  induction t with
  | zero =>
    intro _ hg
    have h0 := init_inv Ns θ lev ℓs (R := R) xx zz (hg 0 (Nat.zero_le _))
    have : ((mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ 1 (fun i => zf i)).1 = initRaw xx := by
      show (validate Ns (initRaw (fun c => zf 0 (Sum.inr c)))).1 = _
      unfold validate; rw [dif_pos h0.1]
    rw [this, Nat.zero_div, Nat.zero_mod]
    exact h0.2
  | succ t ih =>
    intro ht hg
    set a := t / B with ha
    set r := t % B with hr
    have htr : r + B * a = t := by rw [ha, hr]; exact Nat.mod_add_div t B
    have hrB : r < B := Nat.mod_lt t hB
    have hab : a * B = B * a := Nat.mul_comm _ _
    have hgt : ∀ a' ≤ t / B, Good (B := B) Ns θ lev ℓs (R := R) (Φ (B := B) xx zz) a' := by
      intro a' h'; exact hg a' (le_trans h' (Nat.div_le_div_right (Nat.le_succ t)))
    have hinv := ih (by omega) hgt
    set s := (mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ (t + 1) (fun i => zf i) with hs
    have hrun : (mach (B := B) (R := R) Ns θ η lev hps hp).runFin ℓ (t + 2) (fun i => zf i) =
        (mach (B := B) (R := R) Ns θ η lev hps hp).upd (t + 1) s
          (fun k => ℓs t (qry Ns s.1 k)) (zz t) := rfl
    have hday := day_inv Ns θ lev ℓs s.2 hinv (by omega) hrB
    have htB : a * B + r = t := by rw [Nat.mul_comm]; omega
    rw [htB] at hday
    rw [hrun]
    have hsub : t + 1 - 1 = t := rfl
    by_cases hlast : t % B = B - 1
    · have hdm : (t + 1) / B = a + 1 ∧ (t + 1) % B = 0 :=
        (Nat.div_mod_unique hB).mpr ⟨by have h' := hlast; rw [← hr] at h'; rw [Nat.mul_succ]; omega, hB⟩
      have hupd : (mach (B := B) (R := R) Ns θ η lev hps hp).upd (t + 1) s (fun k => ℓs t (qry Ns s.1 k)) (zz t) =
          validate Ns (epochEnd (R := R) θ lev (dayUpd Ns s.1 (fun k => ℓs t (qry Ns s.1 k))) a (zz t)) := by
        show (if t + 1 = 0 then validate Ns (initRaw (fun c => zz t (Sum.inr c)))
          else if (t + 1 - 1) % B = B - 1 then
            validate Ns (epochEnd (R := R) θ lev (dayUpd Ns s.1 (fun k => ℓs t (qry Ns s.1 k))) ((t + 1 - 1) / B) (zz t))
          else ⟨dayUpd Ns s.1 (fun k => ℓs t (qry Ns s.1 k)), valid_dayUpd Ns s.2 _⟩) = _
        rw [if_neg (Nat.succ_ne_zero t), if_pos (show (t + 1 - 1) % B = B - 1 from hlast)]
        rfl
      rw [hupd, hdm.1, hdm.2]
      have hrB1 : r + 1 = B := by rw [hr, hlast]; omega
      rw [hrB1] at hday
      have hNE : a + 1 < NE := by
        have : (a + 1) * B ≤ t + 1 := by rw [Nat.succ_mul]; omega
        by_contra hh; push Not at hh
        have := Nat.mul_le_mul_right B hh
        omega
      have hz : zz t = zz (a * B + B - 1) := by congr 1; omega
      rw [hz]
      have hend := end_inv Ns θ lev ℓs (R := R) xx zz hNE (hlev a (by omega)) hday
        (hgt a le_rfl) (hg (a + 1) (by rw [hdm.1]))
      unfold validate; rw [dif_pos hend.1]
      exact hend.2
    · have hdm : (t + 1) / B = a ∧ (t + 1) % B = r + 1 :=
        (Nat.div_mod_unique hB).mpr ⟨by omega, by omega⟩
      have hupd : (mach (B := B) (R := R) Ns θ η lev hps hp).upd (t + 1) s (fun k => ℓs t (qry Ns s.1 k)) (zz t) =
          ⟨dayUpd Ns s.1 (fun k => ℓs t (qry Ns s.1 k)), valid_dayUpd Ns s.2 _⟩ := by
        show (if t + 1 = 0 then validate Ns (initRaw (fun c => zz t (Sum.inr c)))
          else if (t + 1 - 1) % B = B - 1 then
            validate Ns (epochEnd (R := R) θ lev (dayUpd Ns s.1 (fun k => ℓs t (qry Ns s.1 k))) ((t + 1 - 1) / B) (zz t))
          else ⟨dayUpd Ns s.1 (fun k => ℓs t (qry Ns s.1 k)), valid_dayUpd Ns s.2 _⟩) = _
        rw [if_neg (Nat.succ_ne_zero t), if_neg (show ¬ (t + 1 - 1) % B = B - 1 from hlast)]
      rw [hupd, hdm.1, hdm.2]
      exact hday

end RunInv


end Pool.P0078
