import Pool.P0181.Proc
import Pool.P0176.DZProc
import Pool.P0173.StepClass

/-!
# The round-level process of the one-level step on P0176's per-thread process `dzRun` (units = rounds)

P0181's round-level process, with P0176's per-thread slots and rates instead of P0156's `zRun` (whose layout has no
unit argument, so P0150's thread-dependent rates are not expressible there). One unit = one round (`B = 1`), the fake
increment of a retired copy is `Bm = 1`, the copy losses are `ℓr u x = ℓ_u(arm x)`.

Every round draws a round coin `(κ, d, yB, zB)`:
* the kind `κ : Option (RT D sl)`: `none` = BASE round, `some none` = exploitation round, `some (some ⟨j, k⟩)` = slot
  `k` of thread `j` (P0176's round type); its weight is `wB`, `wE`, `x_j` respectively;
* ALG's draw coin `d : Fin N` (uniform), BASE's action and update coins.

* **BASE** (a P0050 coin algorithm, rules at round `0`) updates on BASE rounds; `Bh` is its estimated policy loss.
* **Pool**: P0176's `dzRun` with the round's slot coin `κ.getD none` (BASE and exploitation rounds are P0176's `none`)
  and rule (b″) `rhD`, gated to `E x ≤ u` and `Bmin ∣ u + 1`, reading `Bh`.
* **ALG**: abstract, updated on exploitation rounds.
* **Plays**: slot round ⟹ the active occupant's arm (BASE's action on an empty or retired slot); BASE round ⟹ BASE's
  action; exploitation ⟹ ALG's draw (`none` = BASE's action).
-/

open Finset Pool.P0001 Pool.P0050

namespace Pool.P0194

/-- Parameters. -/
structure ParD (n : ℕ) (ι : Type) [LinearOrder ι] [Fintype ι] where
  E : ι → ℕ
  thr0 : ι → ℕ
  θ : ℝ
  R : ℕ
  K : ℕ
  D : ℕ
  Lv : ℕ
  Bt : ℕ → ℕ
  lev : ℕ → ℕ → ℕ
  /-- slots per thread and per-slot weight (rate) of each thread -/
  sl : Fin D → ℕ
  xr : Fin D → ℝ
  /-- per-thread layout. A member may hold several slots of its thread; its data then grow by `ℓ/x_j` per drawn
  slot, so they are unbiased estimates of its losses only for layouts with at most one slot per member
  (`ParD.OneSlot`). -/
  lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι
  arm : ι → Fin n
  /-- weights of BASE and exploitation rounds. `ParD` does NOT require the round-kind weights to form a probability
  law; see `ParD.IsLaw` (`wB, wE, x_j ≥ 0`, `wB + wE + Σ_j sl_j·x_j = 1`). -/
  wB : ℝ
  wE : ℝ
  /-- BASE's estimate factor; the intended value is `cB = 1/wB` (then, under `ParD.IsLaw`, `B̂` is an unbiased
  estimate of BASE's policy loss). Not enforced. -/
  cB : ℝ
  Bmin : ℕ
  Λ : ι → ℕ → ℝ
  /-- BASE, a P0050 coin algorithm, always run with its round-`0` rules: this is the algorithm's own behaviour only
  when it is homogeneous (P0173's `CoinHom`); for a time-dependent `AB` the process runs a different algorithm. -/
  AB : CoinAlg n
  N : ℕ
  σA : Type
  sA0 : σA
  draw : σA → Finset ι → Fin N → Option ι
  updA : σA → Finset ι → Fin N → Option ι → Bool → σA
  /-- The layout places only members of the given set. -/
  lay_mem : ∀ j V k x, lay j V k = some x → x ∈ V
  /-- ALG draws only from the set it is given (active members) or the meta-arm. -/
  draw_mem : ∀ σ V d x, draw σ V d = some x → x ∈ V

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι)

/-- Round kinds: `none` = BASE, `some none` = exploitation, `some (some s)` = slot `s`. -/
abbrev Kd := Option (Pool.P0176.RT P.D P.sl)

/-- Round coins. -/
abbrev RC := Kd P × Fin P.N × P.AB.Y × P.AB.Z

/-- BASE round. -/
def isB (κ : Kd P) : Bool := κ.isNone

/-- Exploitation round. -/
def isE (κ : Kd P) : Bool := κ == some none

variable (ℓ : LossSeq n) (ω : ℕ → RC P)

/-- BASE's state before round `u`. -/
def sB : ℕ → P.AB.S
  | 0 => P.AB.s0
  | u + 1 => if isB P (ω u).1 then
      P.AB.upd 0 (sB u) (ω u).2.2.1 (ℓ u (P.AB.act 0 (sB u) (ω u).2.2.1)) (ω u).2.2.2 else sB u

/-- BASE's action at round `u`. -/
def bAct (u : ℕ) : Fin n := P.AB.act 0 (sB P ℓ ω u) (ω u).2.2.1

/-- BASE's estimated policy loss before round `u`. -/
noncomputable def Bh : ℕ → ℝ
  | 0 => 0
  | u + 1 => Bh u + if isB P (ω u).1 then P.cB * ((ℓ u (bAct P ℓ ω u)).toNat : ℝ) else 0

/-- The copies' losses (P0176's `ℓr`). -/
noncomputable def ℓr (u : ℕ) (x : ι) : ℝ := ((ℓ u (P.arm x)).toNat : ℝ)

/-- The slot coins of the units (P0176's `z`, one round per unit). -/
def zc (u : ℕ) : Fin 1 → Pool.P0176.RT P.D P.sl := fun _ => (ω u).1.getD none

/-- Rule (b″) at multiples of `Bmin`. -/
noncomputable def rhD (u : ℕ) (x : ι) (h : ℕ → ℝ) : Bool :=
  decide (P.E x ≤ u) && decide (P.Bmin ∣ u + 1) && decide (P.Λ x u ≤ h (u + 1) - h (P.E x) -
    (Bh P ℓ ω (u + 1) - Bh P ℓ ω (P.E x)))

variable (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- The pool process (P0176's `dzRun`, `B = 1`, `Bm = 1`) at the start of round `u`. -/
noncomputable def pool (u : ℕ) :=
  Pool.P0176.dzRun P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.E P.thr0 P.θ P.R P.K P.Bt P.lev P.lay (zc P ω) ωs φ u

/-- The start pools of round `u`. -/
noncomputable def sp (u : ℕ) : ℕ → ℕ → Finset ι :=
  Pool.P0065.startPools P.E P.thr0 P.D P.Lv P.Bt ωs u (pool P ℓ ω ωs φ u).pools

/-- The active members at round `u`. -/
noncomputable def active (u : ℕ) : Finset ι :=
  Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u) \ (pool P ℓ ω ωs φ u).aux

/-- The arm of a choice (`none` = BASE's action). -/
def armOf (u : ℕ) : Option ι → Fin n
  | some x => P.arm x
  | none => bAct P ℓ ω u

/-- ALG's state before round `u`. -/
noncomputable def sA : ℕ → P.σA
  | 0 => P.sA0
  | u + 1 =>
    if isE P (ω u).1 then
      P.updA (sA u) (active P ℓ ω ωs φ u) (ω u).2.1
        (P.draw (sA u) (active P ℓ ω ωs φ u) (ω u).2.1)
        (ℓ u (armOf P ℓ ω u (P.draw (sA u) (active P ℓ ω ωs φ u) (ω u).2.1)))
    else sA u

/-- ALG's choice at round `u`. -/
noncomputable def algCh (u : ℕ) : Option ι := P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) (ω u).2.1

/-- The active occupant of slot `s` at round `u`. -/
noncomputable def occAtS (u : ℕ) (s : Σ j : Fin P.D, Fin (P.sl j)) : Option ι :=
  match P.lay s.1 (Pool.P0176.blockMem P.Lv (sp P ℓ ω ωs φ u) s.1) s.2 with
  | some x => if x ∈ (pool P ℓ ω ωs φ u).aux then none else some x
  | none => none

/-- The arm played at round `u`. -/
noncomputable def play (u : ℕ) : Fin n :=
  match (ω u).1 with
  | none => bAct P ℓ ω u
  | some none => armOf P ℓ ω u (algCh P ℓ ω ωs φ u)
  | some (some s) => armOf P ℓ ω u (occAtS P ℓ ω ωs φ u s)

/-! ### Causality -/

/-- Two coin sequences agree before round `u`. -/
def Agree (ω ω' : ℕ → RC P) (u : ℕ) : Prop := ∀ v < u, ω v = ω' v

variable {P ℓ}

theorem Agree.mono {ω ω' : ℕ → RC P} {u v : ℕ} (h : Agree P ω ω' u) (hv : v ≤ u) : Agree P ω ω' v :=
  fun w hw => h w (by omega)

theorem sB_congr {ω ω' : ℕ → RC P} : ∀ u, Agree P ω ω' u → sB P ℓ ω u = sB P ℓ ω' u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro h
    simp only [sB]
    rw [ih (h.mono (by omega)), h u (by omega)]

theorem bAct_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' (u + 1)) : bAct P ℓ ω u = bAct P ℓ ω' u := by
  simp only [bAct]; rw [sB_congr u (h.mono (by omega)), h u (by omega)]

theorem Bh_congr {ω ω' : ℕ → RC P} : ∀ u, Agree P ω ω' u → Bh P ℓ ω u = Bh P ℓ ω' u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro h
    simp only [Bh]
    rw [ih (h.mono (by omega)), h u (by omega), bAct_congr u h]

theorem pool_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' u) :
    pool P ℓ ω ωs φ u = pool P ℓ ω' ωs φ u := by
  unfold pool Pool.P0176.dzRun
  apply Pool.P0181.gRun_congr_upd
  intro a ha
  funext sp est ret
  have hz : zc P ω a = zc P ω' a := by unfold zc; rw [h a ha]
  have hrh : rhD P ℓ ω a = rhD P ℓ ω' a := by
    funext x hh
    simp only [rhD]
    by_cases hx : P.E x ≤ a
    · rw [Bh_congr (a + 1) (h.mono (by omega)), Bh_congr (P.E x) (h.mono (by omega))]
    · simp [hx]
  simp only [Pool.P0176.dzUpd, Pool.P0176.dzUpdO, hz, hrh]

theorem sp_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' u) :
    sp P ℓ ω ωs φ u = sp P ℓ ω' ωs φ u := by
  unfold sp; rw [pool_congr ωs φ u h]

theorem active_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' u) :
    active P ℓ ω ωs φ u = active P ℓ ω' ωs φ u := by
  unfold active; rw [sp_congr ωs φ u h, pool_congr ωs φ u h]

theorem armOf_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' (u + 1)) (e : Option ι) :
    armOf P ℓ ω u e = armOf P ℓ ω' u e := by
  cases e with
  | some x => rfl
  | none => exact bAct_congr u h

theorem sA_congr {ω ω' : ℕ → RC P} : ∀ u, Agree P ω ω' u → sA P ℓ ω ωs φ u = sA P ℓ ω' ωs φ u := by
  intro u
  induction u with
  | zero => intro _; rfl
  | succ u ih =>
    intro h
    simp only [sA]
    rw [ih (h.mono (by omega)), active_congr ωs φ u (h.mono (by omega)), h u (by omega),
      armOf_congr u h]

theorem occAtS_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' u) (s : Σ j : Fin P.D, Fin (P.sl j)) :
    occAtS P ℓ ω ωs φ u s = occAtS P ℓ ω' ωs φ u s := by
  unfold occAtS; rw [sp_congr ωs φ u h, pool_congr ωs φ u h]

theorem algCh_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' (u + 1)) :
    algCh P ℓ ω ωs φ u = algCh P ℓ ω' ωs φ u := by
  unfold algCh; rw [sA_congr ωs φ u (h.mono (by omega)), active_congr ωs φ u (h.mono (by omega)), h u (by omega)]

/-- The play at round `u` reads only the coins of rounds `≤ u`. -/
theorem play_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' (u + 1)) :
    play P ℓ ω ωs φ u = play P ℓ ω' ωs φ u := by
  unfold play
  rw [h u (by omega), funext (occAtS_congr ωs φ u (h.mono (by omega))), algCh_congr ωs φ u h,
    bAct_congr u h, funext (armOf_congr (ℓ := ℓ) u h)]

/-! ### The per-round loss identity (C1) -/

variable (P ℓ)

/-- Weight of a round kind. -/
def wK : Kd P → ℝ
  | none => P.wB
  | some none => P.wE
  | some (some s) => P.xr s.1

/-- Weight of a round coin. -/
noncomputable def wR (rc : RC P) : ℝ :=
  wK P rc.1 * (1 / (P.N : ℝ)) * (P.AB.μ rc.2.2.1).toReal * (P.AB.ν rc.2.2.2).toReal

/-- The `wR`-weighted loss of round `u` given the coins before `u` (the coin of round `u` is redrawn). It is the
expected loss of round `u` given the past only when the round weights form a law (`ParD.IsLaw`; then `sum_wR`,
`condLoss_mem_Icc`); for arbitrary weights it is just a weighted sum. -/
noncomputable def condLoss (ω : ℕ → RC P) (u : ℕ) : ℝ :=
  ∑ rc : RC P, wR P rc * ((ℓ u (play P ℓ (Function.update ω u rc) ωs φ u)).toNat : ℝ)

/-- BASE's policy loss at round `u`. -/
noncomputable def bPol (ω : ℕ → RC P) (u : ℕ) : ℝ :=
  ∑ yB : P.AB.Y, (P.AB.μ yB).toReal * ((ℓ u (P.AB.act 0 (sB P ℓ ω u) yB)).toNat : ℝ)

/-- ALG's policy loss at round `u`. -/
noncomputable def aPol (ω : ℕ → RC P) (u : ℕ) : ℝ :=
  ∑ d : Fin P.N, (1 / (P.N : ℝ)) * ∑ yB : P.AB.Y, (P.AB.μ yB).toReal *
    ((ℓ u (match P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) d with
      | some x => P.arm x
      | none => P.AB.act 0 (sB P ℓ ω u) yB)).toNat : ℝ)

/-- Value of slot `s` at round `u`: the active occupant's loss, or BASE's policy loss. -/
noncomputable def slotVal (ω : ℕ → RC P) (u : ℕ) (s : Σ j : Fin P.D, Fin (P.sl j)) : ℝ :=
  match occAtS P ℓ ω ωs φ u s with
  | some x => ((ℓ u (P.arm x)).toNat : ℝ)
  | none => bPol P ℓ ω u

lemma agree_update (ω : ℕ → RC P) (u : ℕ) (rc : RC P) : Agree P (Function.update ω u rc) ω u := by
  intro v hv; rw [Function.update_of_ne (by omega)]

/-- The play at round `u` with the coin of round `u` redrawn as `rc`. -/
theorem play_update (ω : ℕ → RC P) (u : ℕ) (rc : RC P) :
    play P ℓ (Function.update ω u rc) ωs φ u =
      match rc.1 with
      | none => P.AB.act 0 (sB P ℓ ω u) rc.2.2.1
      | some none => (match P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) rc.2.1 with
          | some x => P.arm x
          | none => P.AB.act 0 (sB P ℓ ω u) rc.2.2.1)
      | some (some s) => (match occAtS P ℓ ω ωs φ u s with
          | some x => P.arm x
          | none => P.AB.act 0 (sB P ℓ ω u) rc.2.2.1) := by
  have hA := agree_update P ω u rc
  have hu : Function.update ω u rc u = rc := Function.update_self _ _ _
  have hb : bAct P ℓ (Function.update ω u rc) u = P.AB.act 0 (sB P ℓ ω u) rc.2.2.1 := by
    simp only [bAct]; rw [sB_congr u hA, hu]
  unfold play
  rw [hu]
  rcases rc with ⟨κ, d, yB, zB⟩
  rcases κ with _ | _ | s
  · exact hb
  · unfold algCh
    rw [sA_congr ωs φ u hA, active_congr ωs φ u hA, hu]
    rcases P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) d with _ | x
    · simp [armOf, hb]
    · simp [armOf]
  · simp only []
    rw [occAtS_congr ωs φ u hA]
    rcases occAtS P ℓ ω ωs φ u s with _ | x
    · simp [armOf, hb]
    · simp [armOf]

/-- **Per-round loss identity (C1).** The weighted round loss `condLoss` equals
`wB·bPol + wE·aPol + Σ_s x_{thread s}·slotVal s`. This holds for arbitrary weights; `condLoss` is the expected loss of
round `u` given the earlier coins only under `ParD.IsLaw`. -/
theorem condLoss_eq (hN : 0 < P.N) (ω : ℕ → RC P) (u : ℕ) :
    condLoss P ℓ ωs φ ω u = P.wB * bPol P ℓ ω u + P.wE * aPol P ℓ ωs φ ω u +
      ∑ s : Σ j : Fin P.D, Fin (P.sl j), P.xr s.1 * slotVal P ℓ ωs φ ω u s := by
  have hμ : ∑ yB : P.AB.Y, (P.AB.μ yB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.μ
  have hν : ∑ zB : P.AB.Z, (P.AB.ν zB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.ν
  have hconst : ∀ X : ℝ, ∑ _d : Fin P.N, 1 / (P.N : ℝ) * X = X := by
    intro X
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- the update coin sums out
  have hz : ∀ (κ : Kd P) (d : Fin P.N) (yB : P.AB.Y) (c : ℝ),
      ∑ zB : P.AB.Z, wR P (κ, d, yB, zB) * c = wK P κ * ((1 : ℝ) / (P.N : ℝ)) * (P.AB.μ yB).toReal * c := by
    intro κ d yB c
    unfold wR
    simp only []
    rw [← Finset.sum_mul, ← Finset.mul_sum, hν]; ring
  -- a draw-coin-independent integrand sums out
  have hd : ∀ (c : ℝ) (g : P.AB.Y → ℝ),
      ∑ _d : Fin P.N, ∑ yB : P.AB.Y, c * ((1 : ℝ) / (P.N : ℝ)) * (P.AB.μ yB).toReal * g yB =
        c * ∑ yB : P.AB.Y, (P.AB.μ yB).toReal * g yB := by
    intro c g
    rw [← hconst (c * ∑ yB : P.AB.Y, (P.AB.μ yB).toReal * g yB)]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    ring
  unfold condLoss
  simp only [play_update]
  rw [show (∑ rc : RC P, wR P rc * ((ℓ u (match rc.1 with
      | none => P.AB.act 0 (sB P ℓ ω u) rc.2.2.1
      | some none => (match P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) rc.2.1 with
          | some x => P.arm x
          | none => P.AB.act 0 (sB P ℓ ω u) rc.2.2.1)
      | some (some s) => (match occAtS P ℓ ω ωs φ u s with
          | some x => P.arm x
          | none => P.AB.act 0 (sB P ℓ ω u) rc.2.2.1))).toNat : ℝ)) =
    ∑ κ : Kd P, ∑ d : Fin P.N, ∑ yB : P.AB.Y, ∑ zB : P.AB.Z, wR P (κ, d, yB, zB) * ((ℓ u (match κ with
      | none => P.AB.act 0 (sB P ℓ ω u) yB
      | some none => (match P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) d with
          | some x => P.arm x
          | none => P.AB.act 0 (sB P ℓ ω u) yB)
      | some (some s) => (match occAtS P ℓ ω ωs φ u s with
          | some x => P.arm x
          | none => P.AB.act 0 (sB P ℓ ω u) yB))).toNat : ℝ) from by
    simp only [Fintype.sum_prod_type]]
  simp only [hz]
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [wK, Nat.cast_one]
  have hB : ∑ d : Fin P.N, ∑ yB : P.AB.Y, P.wB * ((1 : ℝ) / (P.N : ℝ)) * (P.AB.μ yB).toReal *
      ((ℓ u (P.AB.act 0 (sB P ℓ ω u) yB)).toNat : ℝ) = P.wB * bPol P ℓ ω u := by
    rw [hd]; rfl
  have hE : ∑ d : Fin P.N, ∑ yB : P.AB.Y, P.wE * ((1 : ℝ) / (P.N : ℝ)) * (P.AB.μ yB).toReal *
      ((ℓ u (match P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) d with
          | some x => P.arm x
          | none => P.AB.act 0 (sB P ℓ ω u) yB)).toNat : ℝ) = P.wE * aPol P ℓ ωs φ ω u := by
    unfold aPol
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun yB _ => ?_
    ring
  have hS : ∀ s : Σ j : Fin P.D, Fin (P.sl j), ∑ d : Fin P.N, ∑ yB : P.AB.Y, P.xr s.1 * ((1 : ℝ) / (P.N : ℝ)) *
      (P.AB.μ yB).toReal * ((ℓ u (match occAtS P ℓ ω ωs φ u s with
          | some x => P.arm x
          | none => P.AB.act 0 (sB P ℓ ω u) yB)).toNat : ℝ) = P.xr s.1 * slotVal P ℓ ωs φ ω u s := by
    intro s
    rw [hd]
    unfold slotVal
    rcases occAtS P ℓ ω ωs φ u s with _ | x
    · rfl
    · simp only; rw [← Finset.sum_mul, hμ, one_mul]
  rw [hB, hE, Finset.sum_congr rfl fun s _ => hS s]
  ring

/-! ### Well-formedness predicates -/

/-- The round-kind weights form a probability law: `wB, wE, x_j ≥ 0` and `wB + wE + Σ_j sl_j·x_j = 1`. -/
def ParD.IsLaw : Prop :=
  0 ≤ P.wB ∧ 0 ≤ P.wE ∧ (∀ j, 0 ≤ P.xr j) ∧ P.wB + P.wE + ∑ j, (P.sl j : ℝ) * P.xr j = 1

/-- Every member holds at most one slot of its thread (needed for the slot data `ℓ/x_j` to be unbiased). -/
def ParD.OneSlot : Prop := ∀ j V k k' x, P.lay j V k = some x → P.lay j V k' = some x → k = k'

/-- The intended parameters: a law of round kinds, `cB = 1/wB`, one slot per member, a homogeneous BASE. -/
def ParD.Intended : Prop := P.IsLaw ∧ P.cB * P.wB = 1 ∧ P.OneSlot ∧ Pool.P0173.CoinHom P.AB

theorem sum_wK : ∑ κ : Kd P, wK P κ = P.wB + P.wE + ∑ j, (P.sl j : ℝ) * P.xr j := by
  rw [Fintype.sum_option, Fintype.sum_option, Fintype.sum_sigma]
  simp only [wK, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem wR_nonneg (hL : P.IsLaw) (rc : RC P) : 0 ≤ wR P rc := by
  have hk : 0 ≤ wK P rc.1 := by
    rcases rc with ⟨_ | _ | s, _⟩
    · exact hL.1
    · exact hL.2.1
    · exact hL.2.2.1 s.1
  unfold wR
  have : 0 ≤ (1 / (P.N : ℝ)) := by positivity
  positivity

/-- **Under `ParD.IsLaw` the round-coin weights form a probability law.** -/
theorem sum_wR (hL : P.IsLaw) (hN : 0 < P.N) : ∑ rc : RC P, wR P rc = 1 := by
  have hμ : ∑ yB : P.AB.Y, (P.AB.μ yB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.μ
  have hν : ∑ zB : P.AB.Z, (P.AB.ν zB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.ν
  have hN' : (0 : ℝ) < P.N := by exact_mod_cast hN
  simp only [Fintype.sum_prod_type, wR]
  have : ∀ κ : Kd P, ∑ _d : Fin P.N, ∑ yB : P.AB.Y, ∑ zB : P.AB.Z,
      wK P κ * (1 / (P.N : ℝ)) * (P.AB.μ yB).toReal * (P.AB.ν zB).toReal = wK P κ := by
    intro κ
    simp only [← Finset.mul_sum, hν, mul_one, ← Finset.sum_mul, hμ, one_mul]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [Finset.sum_congr rfl fun κ _ => this κ, sum_wK]
  exact hL.2.2.2

/-- **Under `ParD.IsLaw`, `condLoss` is an expected loss**: it lies in `[0, 1]`. -/
theorem condLoss_mem_Icc (hL : P.IsLaw) (hN : 0 < P.N) (ω : ℕ → RC P) (u : ℕ) :
    0 ≤ condLoss P ℓ ωs φ ω u ∧ condLoss P ℓ ωs φ ω u ≤ 1 := by
  have hb : ∀ b : Bool, (0 : ℝ) ≤ (b.toNat : ℝ) ∧ (b.toNat : ℝ) ≤ 1 := by intro b; cases b <;> simp
  unfold condLoss
  constructor
  · exact Finset.sum_nonneg fun rc _ => mul_nonneg (wR_nonneg P hL rc) (hb _).1
  · calc _ ≤ ∑ rc : RC P, wR P rc * 1 :=
          Finset.sum_le_sum fun rc _ => mul_le_mul_of_nonneg_left (hb _).2 (wR_nonneg P hL rc)
      _ = 1 := by simp only [mul_one]; exact sum_wR P hL hN

end Pool.P0194
