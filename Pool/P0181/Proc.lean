import Pool.P0156.ZRun
import Pool.P0050.CoinAlg
import Pool.P0092.Azuma

/-!
# The round-level process of the one-level step (P0166's concrete process), pathwise

Units are rounds. Every round draws a round coin `(y, d, yB, zB)`: a position `y : Fin S`, ALG's draw coin
`d : Fin N`, and BASE's action/update coins. Positions are member slots (`isSlot`), BASE positions (`isBase`) or
exploitation positions (the rest).

* **BASE** (a P0050 coin algorithm `AB`, rules at round `0`) updates only on BASE rounds;
  `bAct u` is its action at round `u` (its action coin of the round), `Bh u` its estimated policy loss before `u`.
* **Pool**: P0156's retirement process `zRun` with `s = S`, position coins `y`, data `Lz u x = Lw u x · ℓ_u(arm x)`
  (the observed member gains `S·Lw·ℓ`), and the retirement rule `rhZ`: at multiples of `Bmin` only, retire `x` when
  its data since entry exceed BASE's estimate since entry by `Λ x u`.
* **ALG**: an abstract learner (state `σA`, draw rule, update rule), updated on exploitation rounds only.
* **Plays**: occupied active slot ⟹ the member's arm; empty or retired slot, BASE round ⟹ BASE's action;
  exploitation ⟹ ALG's draw (`none` = the BASE meta-arm, played with BASE's action).
-/

open Finset Pool.P0001 Pool.P0050

namespace Pool.P0181

/-- Parameters of the process. The last four fields are well-formedness conditions making the process
single-query: the pool's data, BASE's update and B̂ read only the loss of the arm played in the round.
`cB` is free; the intended value (B̂ unbiased for BASE's policy loss) is `cB = S / #{y | isBase y}`.
BASE's rules are always applied at round index `0`: this is BASE's own run only for a homogeneous BASE
(P0173's `CoinHom`), which is the intended use. -/
structure Par (n : ℕ) (ι : Type) [LinearOrder ι] [Fintype ι] where
  E : ι → ℕ
  thr0 : ι → ℕ
  θ : ℝ
  R : ℕ
  K : ℕ
  D : ℕ
  Lv : ℕ
  Bt : ℕ → ℕ
  lev : ℕ → ℕ → ℕ
  S : ℕ
  N : ℕ
  occ : Finset ι → Fin S → Option ι
  arm : ι → Fin n
  Lw : ℕ → ι → ℝ
  isSlot : Fin S → Bool
  isBase : Fin S → Bool
  /-- B̂'s factor; intended `S / #{y | isBase y}`. -/
  cB : ℝ
  Bmin : ℕ
  Λ : ι → ℕ → ℝ
  AB : CoinAlg n
  σA : Type
  sA0 : σA
  draw : σA → Finset ι → Fin N → Option ι
  updA : σA → Finset ι → Fin N → Option ι → Bool → σA
  /-- Single query: the layout places members on slot positions only (the pool observes only played arms). -/
  occ_slot : ∀ V y x, occ V y = some x → isSlot y = true
  /-- The layout places only members of the given set. -/
  occ_mem : ∀ V y x, occ V y = some x → x ∈ V
  /-- Slot and BASE positions are disjoint (BASE observes only its own played action). -/
  slot_base : ∀ y, isSlot y = true → isBase y = false
  /-- ALG draws only from the set it is given (active members) or the meta-arm. -/
  draw_mem : ∀ σ V d x, draw σ V d = some x → x ∈ V

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : Par n ι)

/-- Round coins. -/
abbrev RC := Fin P.S × Fin P.N × P.AB.Y × P.AB.Z

variable (ℓ : LossSeq n) (ω : ℕ → RC P)

/-- BASE's state before round `u` (it updates on BASE rounds only). -/
def sB : ℕ → P.AB.S
  | 0 => P.AB.s0
  | u + 1 => if P.isBase (ω u).1 then
      P.AB.upd 0 (sB u) (ω u).2.2.1 (ℓ u (P.AB.act 0 (sB u) (ω u).2.2.1)) (ω u).2.2.2 else sB u

/-- BASE's action at round `u` (its action coin of round `u`). -/
def bAct (u : ℕ) : Fin n := P.AB.act 0 (sB P ℓ ω u) (ω u).2.2.1

/-- BASE's estimated policy loss before round `u`. -/
noncomputable def Bh : ℕ → ℝ
  | 0 => 0
  | u + 1 => Bh u + if P.isBase (ω u).1 then P.cB * ((ℓ u (bAct P ℓ ω u)).toNat : ℝ) else 0

/-- The pool's per-round data. -/
noncomputable def Lz (u : ℕ) (x : ι) : ℝ := P.Lw u x * ((ℓ u (P.arm x)).toNat : ℝ)

/-- Rule (b″) at multiples of `Bmin`: retire when the own data since entry exceed BASE's estimate since entry
by `Λ x u`. -/
noncomputable def rhZ (u : ℕ) (x : ι) (h : ℕ → ℝ) : Bool :=
  decide (P.E x ≤ u) && decide (P.Bmin ∣ u + 1) && decide (P.Λ x u ≤ h (u + 1) - h (P.E x) -
    (Bh P ℓ ω (u + 1) - Bh P ℓ ω (P.E x)))

variable (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

/-- The pool process (P0156's `zRun`) at the start of round `u`. -/
noncomputable def pool (u : ℕ) :=
  Pool.P0156.zRun P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev P.S (Lz P ℓ) P.occ (fun v => (ω v).1)
    (rhZ P ℓ ω) ωs φ u

/-- The start pools of round `u`. -/
noncomputable def sp (u : ℕ) : ℕ → ℕ → Finset ι :=
  Pool.P0065.startPools P.E P.thr0 P.D P.Lv P.Bt ωs u (pool P ℓ ω ωs φ u).pools

/-- The active members (start-pool members not retired) at round `u`. -/
noncomputable def active (u : ℕ) : Finset ι :=
  Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u) \ (pool P ℓ ω ωs φ u).aux

/-- The arm of ALG's choice (`none` = BASE meta-arm). -/
def armOf (u : ℕ) : Option ι → Fin n
  | some x => P.arm x
  | none => bAct P ℓ ω u

/-- Exploitation round. -/
def isExp (y : Fin P.S) : Bool := !(P.isSlot y || P.isBase y)

/-- ALG's state before round `u` (updated on exploitation rounds only). -/
noncomputable def sA : ℕ → P.σA
  | 0 => P.sA0
  | u + 1 =>
    if isExp P (ω u).1 then
      P.updA (sA u) (active P ℓ ω ωs φ u) (ω u).2.1
        (P.draw (sA u) (active P ℓ ω ωs φ u) (ω u).2.1)
        (ℓ u (armOf P ℓ ω u (P.draw (sA u) (active P ℓ ω ωs φ u) (ω u).2.1)))
    else sA u

/-- ALG's choice at round `u` (meaningful on exploitation rounds). -/
noncomputable def algCh (u : ℕ) : Option ι := P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) (ω u).2.1

/-- The slot outcome at round `u`: the occupant of the drawn position if it is an active member. -/
noncomputable def slotOcc (u : ℕ) : Option ι :=
  match P.occ (Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u)) (ω u).1 with
  | some x => if x ∈ (pool P ℓ ω ωs φ u).aux then none else some x
  | none => none

/-- The arm played at round `u`. -/
noncomputable def play (u : ℕ) : Fin n :=
  if P.isSlot (ω u).1 then armOf P ℓ ω u (slotOcc P ℓ ω ωs φ u)
  else if P.isBase (ω u).1 then bAct P ℓ ω u
  else armOf P ℓ ω u (algCh P ℓ ω ωs φ u)


/-! ### Causality -/

section Congr

variable {ι' : Type*} [LinearOrder ι'] [Fintype ι'] (E' thr0' : ι' → ℕ) (θ' : ℝ) (R' K' D' Lv' : ℕ)
  (Bt' : ℕ → ℕ) (lev' : ℕ → ℕ → ℕ) {σ : Type*}

/-- `gRun` at boundary `a` reads the update rule only at units `< a`. -/
theorem gRun_congr_upd {upd upd' : ℕ → (ℕ → ℕ → Finset ι') → (ι' → ℕ → ℝ) → σ → (ι' → ℝ) × σ} (aux0 : σ)
    (ωs' : ι' → Bool) (φ' : ℕ → ℕ → ℕ → Fin K' → ι' → Bool) :
    ∀ a, (∀ a' < a, upd a' = upd' a') →
      Pool.P0156.gRun E' thr0' θ' R' K' D' Lv' Bt' lev' upd aux0 ωs' φ' a =
        Pool.P0156.gRun E' thr0' θ' R' K' D' Lv' Bt' lev' upd' aux0 ωs' φ' a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have ih' := ih (fun a' ha' => h a' (by omega))
    simp only [Pool.P0156.gRun]
    rw [ih', h a (by omega)]

end Congr

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
  unfold pool Pool.P0156.zRun
  apply gRun_congr_upd
  intro a ha
  funext sp est ret
  simp only [Pool.P0156.zUpd, Pool.P0156.zIncr]
  have hy : (ω a).1 = (ω' a).1 := by rw [h a ha]
  have hz : ∀ sp ret, Pool.P0156.zIncr P.D P.Lv P.S (Lz P ℓ) P.occ (fun v => (ω v).1) a sp ret =
      Pool.P0156.zIncr P.D P.Lv P.S (Lz P ℓ) P.occ (fun v => (ω' v).1) a sp ret := by
    intro sp ret; unfold Pool.P0156.zIncr; simp only [hy]
  have hrh : rhZ P ℓ ω a = rhZ P ℓ ω' a := by
    funext x hh
    simp only [rhZ]
    by_cases hx : P.E x ≤ a
    · rw [Bh_congr (a + 1) (h.mono (by omega)), Bh_congr (P.E x) (h.mono (by omega))]
    · simp [hx]
  rw [hz, hrh]

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

theorem slotOcc_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' (u + 1)) :
    slotOcc P ℓ ω ωs φ u = slotOcc P ℓ ω' ωs φ u := by
  unfold slotOcc; rw [sp_congr ωs φ u (h.mono (by omega)), pool_congr ωs φ u (h.mono (by omega)), h u (by omega)]

theorem algCh_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' (u + 1)) :
    algCh P ℓ ω ωs φ u = algCh P ℓ ω' ωs φ u := by
  unfold algCh; rw [sA_congr ωs φ u (h.mono (by omega)), active_congr ωs φ u (h.mono (by omega)), h u (by omega)]

/-- The play at round `u` reads only the coins of rounds `≤ u`. -/
theorem play_congr {ω ω' : ℕ → RC P} (u : ℕ) (h : Agree P ω ω' (u + 1)) :
    play P ℓ ω ωs φ u = play P ℓ ω' ωs φ u := by
  unfold play
  rw [h u (by omega), slotOcc_congr ωs φ u h, algCh_congr ωs φ u h, bAct_congr u h,
    funext (armOf_congr (ℓ := ℓ) u h)]


/-! ### The per-round loss identity (C1) -/

open scoped Pool.P0050

variable (P ℓ)

/-- Weight of a round coin: uniform position and draw coin, BASE's coin laws. -/
noncomputable def wR (rc : RC P) : ℝ :=
  (1 / (P.S : ℝ)) * (1 / (P.N : ℝ)) * (P.AB.μ rc.2.2.1).toReal * (P.AB.ν rc.2.2.2).toReal

/-- Expected loss of round `u` given the coins before `u` (the coin of round `u` is redrawn). -/
noncomputable def condLoss (ω : ℕ → RC P) (u : ℕ) : ℝ :=
  ∑ rc : RC P, wR P rc * ((ℓ u (play P ℓ (Function.update ω u rc) ωs φ u)).toNat : ℝ)

/-- BASE's policy loss at round `u`. -/
noncomputable def bPol (ω : ℕ → RC P) (u : ℕ) : ℝ :=
  ∑ yB : P.AB.Y, (P.AB.μ yB).toReal * ((ℓ u (P.AB.act 0 (sB P ℓ ω u) yB)).toNat : ℝ)

/-- ALG's policy loss at round `u` (the BASE meta-arm plays BASE's action). -/
noncomputable def aPol (ω : ℕ → RC P) (u : ℕ) : ℝ :=
  ∑ d : Fin P.N, (1 / (P.N : ℝ)) * ∑ yB : P.AB.Y, (P.AB.μ yB).toReal *
    ((ℓ u (match P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) d with
      | some x => P.arm x
      | none => P.AB.act 0 (sB P ℓ ω u) yB)).toNat : ℝ)

/-- The occupant of position `y` at round `u`, if it is an active member. -/
noncomputable def occAt (ω : ℕ → RC P) (u : ℕ) (y : Fin P.S) : Option ι :=
  match P.occ (Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u)) y with
  | some x => if x ∈ (pool P ℓ ω ωs φ u).aux then none else some x
  | none => none

/-- Value of position `y` at round `u`. -/
noncomputable def posVal (ω : ℕ → RC P) (u : ℕ) (y : Fin P.S) : ℝ :=
  if P.isSlot y then
    (match occAt P ℓ ωs φ ω u y with
      | some x => ((ℓ u (P.arm x)).toNat : ℝ)
      | none => bPol P ℓ ω u)
  else if P.isBase y then bPol P ℓ ω u else aPol P ℓ ωs φ ω u


lemma agree_update (ω : ℕ → RC P) (u : ℕ) (rc : RC P) : Agree P (Function.update ω u rc) ω u := by
  intro v hv; rw [Function.update_of_ne (by omega)]

/-- The play at round `u` with the coin of round `u` redrawn as `rc`. -/
theorem play_update (ω : ℕ → RC P) (u : ℕ) (rc : RC P) :
    play P ℓ (Function.update ω u rc) ωs φ u =
      if P.isSlot rc.1 then
        (match occAt P ℓ ωs φ ω u rc.1 with
          | some x => P.arm x
          | none => P.AB.act 0 (sB P ℓ ω u) rc.2.2.1)
      else if P.isBase rc.1 then P.AB.act 0 (sB P ℓ ω u) rc.2.2.1
      else (match P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) rc.2.1 with
          | some x => P.arm x
          | none => P.AB.act 0 (sB P ℓ ω u) rc.2.2.1) := by
  have hA := agree_update P ω u rc
  have hu : Function.update ω u rc u = rc := Function.update_self _ _ _
  have hb : bAct P ℓ (Function.update ω u rc) u = P.AB.act 0 (sB P ℓ ω u) rc.2.2.1 := by
    simp only [bAct]; rw [sB_congr u hA, hu]
  unfold play
  rw [hu]
  split_ifs with h1 h2
  · unfold slotOcc occAt
    rw [sp_congr ωs φ u hA, pool_congr ωs φ u hA, hu]
    rcases P.occ (Pool.P0095.members P.D P.Lv (sp P ℓ ω ωs φ u)) rc.1 with _ | x
    · simp [armOf, hb]
    · by_cases hx : x ∈ (pool P ℓ ω ωs φ u).aux <;> simp [hx, armOf, hb]
  · exact hb
  · unfold algCh
    rw [sA_congr ωs φ u hA, active_congr ωs φ u hA, hu]
    rcases P.draw (sA P ℓ ω ωs φ u) (active P ℓ ω ωs φ u) rc.2.1 with _ | x
    · simp [armOf, hb]
    · simp [armOf]

/-- **Per-round loss identity (C1).** The expected loss of round `u` given the earlier coins is the average of the
position values: active occupants' losses on slots (BASE's policy loss on empty or retired slots), BASE's policy
loss on BASE positions, ALG's policy loss on exploitation positions. -/
theorem condLoss_eq (hN : 0 < P.N) (ω : ℕ → RC P) (u : ℕ) :
    condLoss P ℓ ωs φ ω u = (1 / (P.S : ℝ)) * ∑ y : Fin P.S, posVal P ℓ ωs φ ω u y := by
  have hμ : ∑ yB : P.AB.Y, (P.AB.μ yB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.μ
  have hν : ∑ zB : P.AB.Z, (P.AB.ν zB).toReal = 1 := Pool.P0092.sum_toReal_one P.AB.ν
  have hNd : ∑ _d : Fin P.N, (1 / (P.N : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  unfold condLoss
  simp only [play_update]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type, wR]
  -- sum out the update coin
  have hz : ∀ (yB : P.AB.Y) (c : ℝ),
      ∑ zB : P.AB.Z, (1 / (P.S : ℝ)) * (1 / (P.N : ℝ)) * (P.AB.μ yB).toReal * (P.AB.ν zB).toReal * c =
        (1 / (P.S : ℝ)) * ((1 / (P.N : ℝ)) * ((P.AB.μ yB).toReal * c)) := by
    intro yB c
    rw [← Finset.sum_mul, ← Finset.mul_sum, hν]; ring
  simp only [hz]
  simp only [← Finset.mul_sum]
  congr 1
  unfold posVal
  have hconst : ∀ X : ℝ, 1 / (P.N : ℝ) * ∑ _d : Fin P.N, X = X := by
    intro X
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  by_cases h1 : P.isSlot y = true
  · simp only [h1, if_true]
    rw [hconst]
    rcases occAt P ℓ ωs φ ω u y with _ | x
    · rfl
    · simp only; rw [← Finset.sum_mul, hμ, one_mul]
  · simp only [h1, Bool.false_eq_true, if_false]
    by_cases h2 : P.isBase y = true
    · simp only [h2, if_true]
      rw [hconst]; rfl
    · simp only [h2, Bool.false_eq_true, if_false]
      unfold aPol
      rw [Finset.mul_sum]
      simp only [Nat.cast_one]

end Pool.P0181
