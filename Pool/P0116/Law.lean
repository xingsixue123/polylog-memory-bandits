import Pool.P0113.Corr
import Pool.P0084.Machine
import Pool.P0091.Exp

/-!
# The threaded machine's expected loss under the coin-array law

* `σT`/`σT_inj`: where each bit of P0091's coin array (P0082's `SlotC × ι`) sits among the machine's day coins
  (sampling bit of unit `e` on day `e`, filter bits of the merges ending unit `a` on day `a + 1`); `arrOf`.
* `zzE ω`: the day coins, then all-`false` coins. With it the machine's ideal process (P0113's `TP`) is EXACTLY
  the array-driven process of P0091 (`ωsT_zzE`, `φT_zzE`, `SP_zzE`, `presentT_zzE`), when every copy enters
  before `NE`.
* The array side: `SPA`, `presentA`, the ideal learner's loss `Aid` (P0089's finite-precision Hedge with P0096's
  perturbation `ρM` while some copy is present, arm `0` otherwise, `0` from `NE` on), `BadA` (some start pool
  before `NE` exceeds the capacity).
* `path_le`: pathwise, days `0..NE` cost at most `1 + Σ_{a<NE} Aid a`, or `1 + NE` on a bad array.
* `W_eq_bw`, **`sum_expLoss_le`**: `Σ_{t ≤ NE} expLoss ≤ 1 + E_{pC ps q}[Σ_{a<NE} Aid a + NE·[BadA]]`.
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0030 Pool.P0042 Pool.P0052 Pool.P0065 Pool.P0104 Pool.P0113

namespace Pool.P0116


variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (p : Prm n ι) (NE : ℕ)

/-- The coin array of P0082/P0091 (sampling slots per unit, filter slots per (unit, thread, level,
iteration)), indexed with the copy. -/
abbrev Arr := Pool.P0082.SlotC NE p.D p.Lf p.K × ι

/-- Where each array bit sits among the machine's day coins: the sampling bit of unit `e` on day `e`, the
filter bits of the merges at the end of unit `a` on day `a + 1`. -/
def σT : Arr p NE → Fin (NE + 1) × Jd p
  | (Sum.inl e, c) => (Fin.castSucc e, Sum.inr c)
  | (Sum.inr (a, r, ℓ, k), c) => (a.succ, Sum.inl (r, ℓ, k, c))

theorem σT_inj : Function.Injective (σT p NE) := by
  rintro ⟨s, c⟩ ⟨s', c'⟩ h
  rcases s with e | ⟨a, r, ℓ, k⟩ <;> rcases s' with e' | ⟨a', r', ℓ', k'⟩ <;>
    simp only [σT, Prod.mk.injEq, reduceCtorEq, and_false, Sum.inr.injEq, Sum.inl.injEq] at h
  · rw [Fin.castSucc_inj.mp h.1, h.2]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rw [Fin.succ_inj.mp h1, h2, h3, h4, h5]

/-- The array read off the machine's coins. -/
def arrOf (ω : Fin (NE + 1) → Jd p → Bool) : Arr p NE → Bool := fun x => ω (σT p NE x).1 (σT p NE x).2

/-- The machine's coin path: the day coins, then all-`false` coins. -/
def zzE (ω : Fin (NE + 1) → Jd p → Bool) : ℕ → Jd p → Bool := Pool.P0084.ext (fun _ => false) ω

variable {p NE}

theorem ωsT_zzE (hEN : ∀ c, p.E c < NE) (ω : Fin (NE + 1) → Jd p → Bool) :
    ωsT p (zzE p NE ω) = Pool.P0082.ωsC p.E NE p.D p.Lf p.K (arrOf p NE ω) := by
  funext c
  have h := hEN c
  simp only [ωsT, zzE, Pool.P0084.ext, Pool.P0082.ωsC, dif_pos h, dif_pos (show p.E c < NE + 1 by omega), arrOf, σT]
  rfl

theorem φT_zzE (ω : Fin (NE + 1) → Jd p → Bool) :
    φT p (zzE p NE ω) = Pool.P0082.φC NE p.D p.Lf p.K (arrOf p NE ω) := by
  funext r a ℓ k c
  simp only [φT, φz, Pool.P0082.φC, zzE, Pool.P0084.ext]
  split_ifs with h1 h2 h3 h4 <;> first | rfl | (exfalso; omega) | (exfalso; tauto) | skip

section ArraySide

variable (p NE)
variable (ℓs : LossSeq n)

/-- Start pools of the array-driven threaded process (P0091's objects). -/
noncomputable def SPA (ω' : Arr p NE → Bool) (a : ℕ) : ℕ → ℕ → Finset ι :=
  startPools p.E p.thr0 p.D p.Lv p.Bt (Pool.P0082.ωsC p.E NE p.D p.Lf p.K ω') a
    (tpools p.E p.thr0 (Pool.P0061.cumL (cuT p ℓs)) p.θ p.R p.K p.D p.Lv p.Bt p.lev
      (Pool.P0082.ωsC p.E NE p.D p.Lf p.K ω') (Pool.P0082.φC NE p.D p.Lf p.K ω') a)

/-- Presence in the array-driven start pools. -/
def presentA (ω' : Arr p NE → Bool) (a : ℕ) (f : ι) : Prop := ∃ r ℓ, f ∈ SPA p NE ℓs ω' a r ℓ

open Classical in
/-- **The ideal learner's loss** on unit `a` of the array-driven run: P0089's finite-precision dyadic Hedge
(perturbation P0096's `ρM`) if some copy is present, the loss of arm `0` otherwise; `0` from unit `NE` on. -/
noncomputable def Aid [NeZero n] (ω' : Arr p NE → Bool) (a : ℕ) : ℝ :=
  if a < NE then
    (if ∃ f, presentA p NE ℓs ω' a f then
      Pool.P0089.palgLoss (fun _ => (1 : ℝ)) p.η (Pool.P0089.specAw (L := p.L) (presentA p NE ℓs ω'))
        (Pool.P0089.specLoss (L := p.L) (cuT p ℓs))
        (Pool.P0096.ρM (fun _ => (1 : ℝ)) p.η p.δ (Pool.P0089.specAw (L := p.L) (presentA p NE ℓs ω'))
          (bT p ℓs)) a
     else ((ℓs (a + 1) ⟨0, NeZero.pos n⟩).toNat : ℝ))
  else 0

/-- A bad array: some start pool before `NE` exceeds the capacity. -/
def BadA (ω' : Arr p NE → Bool) : Prop :=
  ∃ a < NE, p.Ns < (Finset.univ.biUnion (mkP p (SPA p NE ℓs ω' a))).card

variable {p NE ℓs}

theorem SP_zzE (hEN : ∀ c, p.E c < NE) (ω : Fin (NE + 1) → Jd p → Bool) :
    SP p ℓs (zzE p NE ω) = SPA p NE ℓs (arrOf p NE ω) := by
  funext a
  unfold SP TP SPA
  rw [ωsT_zzE hEN, φT_zzE]

theorem presentT_zzE (hEN : ∀ c, p.E c < NE) (ω : Fin (NE + 1) → Jd p → Bool) :
    presentT p ℓs (zzE p NE ω) = presentA p NE ℓs (arrOf p NE ω) := by
  funext a f
  unfold presentT presentA
  rw [SP_zzE hEN]

end ArraySide

section Path

theorem Aid_nonneg [NeZero n] (ℓs : LossSeq n) (ω' : Arr p NE → Bool) (a : ℕ) : 0 ≤ Aid p NE ℓs ω' a := by
  unfold Aid
  split_ifs
  · unfold Pool.P0089.palgLoss
    exact Finset.sum_nonneg fun j _ => mul_nonneg (Pool.P0089.pprob_nonneg (fun _ => one_pos) _ _)
      (Nat.cast_nonneg _)
  · exact Nat.cast_nonneg _
  · exact le_rfl

open Classical in
/-- **Pathwise**: over days `0, …, NE`, the machine's expected losses are at most `1 + Σ_{a<NE} Aid a` on a good
array, and at most `1 + NE` otherwise. -/
theorem path_le [NeZero n] (h : Hyp p NE) (hEN : ∀ c, p.E c < NE) {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1)
    (hq : 0 ≤ q ∧ q ≤ 1) (ℓs : LossSeq n) (ω : Fin (NE + 1) → Jd p → Bool) :
    ∑ t ∈ range (NE + 1), Pool.P0015.E (playL p (runZ p ℓs (zzE p NE ω) hps hq t).1)
        (fun i => ((ℓs t i).toNat : ℝ)) ≤
      1 + ∑ a ∈ range NE, Aid p NE ℓs (arrOf p NE ω) a +
        NE * (if BadA p NE ℓs (arrOf p NE ω) then 1 else 0) := by
  classical
  have hle1 : ∀ t (x : Raw p), Pool.P0015.E (playL p x) (fun i => ((ℓs t i).toNat : ℝ)) ≤ 1 :=
    fun t x => Pool.P0084.E_le_one _ _ fun i => by cases ℓs t i <;> simp
  rw [Finset.sum_range_succ']
  have h0 := hle1 0 (runZ p ℓs (zzE p NE ω) hps hq 0).1
  have hA0 : 0 ≤ ∑ a ∈ range NE, Aid p NE ℓs (arrOf p NE ω) a :=
    Finset.sum_nonneg fun a _ => Aid_nonneg ℓs _ a
  by_cases hb : BadA p NE ℓs (arrOf p NE ω)
  · rw [if_pos hb, mul_one]
    have : ∑ a ∈ range NE, Pool.P0015.E (playL p (runZ p ℓs (zzE p NE ω) hps hq (a + 1)).1)
        (fun i => ((ℓs (a + 1) i).toNat : ℝ)) ≤ ∑ _a ∈ range NE, (1 : ℝ) :=
      Finset.sum_le_sum fun a _ => hle1 _ _
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
    linarith
  · rw [if_neg hb, mul_zero, add_zero]
    have hgood : ∀ a < NE, (Finset.univ.biUnion (mkP p (SPA p NE ℓs (arrOf p NE ω) a))).card ≤ p.Ns := by
      intro a ha; by_contra hc; exact hb ⟨a, ha, by omega⟩
    have hday : ∀ a ∈ range NE, Pool.P0015.E (playL p (runZ p ℓs (zzE p NE ω) hps hq (a + 1)).1)
        (fun i => ((ℓs (a + 1) i).toNat : ℝ)) = Aid p NE ℓs (arrOf p NE ω) a := by
      intro a ha
      rw [Finset.mem_range] at ha
      have hinv := run_inv (ℓs := ℓs) (zz := zzE p NE ω) hps hq h a ha (fun a' ha' => by
        rw [SP_zzE hEN]; exact hgood a' (by omega))
      have hU : ∀ c, c ∈ Pool.P0078.U (runZ p ℓs (zzE p NE ω) hps hq (a + 1)).1 ↔
          presentA p NE ℓs (arrOf p NE ω) a c := by
        intro c; rw [mem_U_of_inv h hinv, presentT_zzE hEN]
      unfold Aid
      rw [if_pos ha]
      by_cases hne : ∃ f, presentA p NE ℓs (arrOf p NE ω) a f
      · rw [if_pos hne]
        obtain ⟨f, hf⟩ := hne
        rw [dayLoss_eq h ha hinv ⟨f, (hU f).2 hf⟩]
        unfold awT
        rw [presentT_zzE hEN]
      · rw [if_neg hne]
        have hemp : ¬ (Pool.P0078.U (runZ p ℓs (zzE p NE ω) hps hq (a + 1)).1).Nonempty := by
          rintro ⟨c, hc⟩; exact hne ⟨c, (hU c).1 hc⟩
        unfold playL
        rw [dif_neg hemp, Pool.P0064.E_pure']
    rw [Finset.sum_congr rfl hday]
    linarith

end Path

section Law

open Pool.P0046

attribute [local instance] Pool.P0082.coinFintype

/-- The day-coin space is finite (the nesting is too deep for default instance search). -/
noncomputable def dayFintype : Fintype (Fin (NE + 1) × Jd p → Bool) :=
  @Pi.instFintype _ _ instDecidableEqProd inferInstance (fun _ => inferInstance)

attribute [local instance] dayFintype

theorem zzE_lt (ω : Fin (NE + 1) → Jd p → Bool) {i : ℕ} (hi : i < NE + 1) : zzE p NE ω i = ω ⟨i, hi⟩ := by
  simp [zzE, Pool.P0084.ext, hi]
open scoped Pool.P0064

theorem W_eq_bw [NeZero n] {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)
    (ω : Fin (NE + 1) → Jd p → Bool) :
    (mach p hps hq).W ω = bw (fun tj : Fin (NE + 1) × Jd p => qd p ps q tj.2) (fun tj => ω tj.1 tj.2) := by
  unfold Pool.P0064.QCoinAlg.W
  rw [← Pool.P0084.prod_bw_curry]
  apply Fintype.prod_congr; intro t
  show (Pool.P0051.bernVec (qd p ps q) (qd_mem p hps hq) (ω t)).toReal = _
  rw [Pool.P0051.bernVec_apply]
  rfl

open Classical in
/-- **Expected loss of the threaded machine** over days `0, …, NE`: at most `1 + E[Σ_{a<NE} Aid a + NE·[bad]]`
under P0091's coin-array law `pC ps q` (the array bits are the machine's day-coin bits at `σT`). -/
theorem sum_expLoss_le [NeZero n] (h : Hyp p NE) (hEN : ∀ c, p.E c < NE) {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1)
    (hq : 0 ≤ q ∧ q ≤ 1) (ℓs : LossSeq n) :
    ∑ t ∈ range (NE + 1), (mach p hps hq).toQ.expLoss ℓs t ≤
      1 + ∑ ω' : Arr p NE → Bool, Pool.P0048.wtv (Pool.P0091.pC ps q) ω' *
        (∑ a ∈ range NE, Aid p NE ℓs ω' a + NE * (if BadA p NE ℓs ω' then 1 else 0)) := by
  set A := mach p hps hq with hA
  have hW0 : ∀ (T : ℕ) (ω : Fin T → A.Z), 0 ≤ A.W ω := fun _ _ =>
    Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  set G : (Arr p NE → Bool) → ℝ := fun ω' =>
    ∑ a ∈ range NE, Aid p NE ℓs ω' a + NE * (if BadA p NE ℓs ω' then 1 else 0) with hG
  have hday : ∀ t ∈ range (NE + 1), A.toQ.expLoss ℓs t =
      ∑ ω : Fin (NE + 1) → A.Z, A.W ω * Pool.P0015.E (playL p (runZ p ℓs (zzE p NE ω) hps hq t).1)
        (fun i => ((ℓs t i).toNat : ℝ)) := by
    intro t ht
    have ht' : t ≤ NE + 1 := by have := Finset.mem_range.mp ht; omega
    rw [Pool.P0064.expLoss_eq, ← Pool.P0084.sum_W_restrict A t _ (NE + 1) ht']
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hfun : (fun i : Fin t => ω (Fin.castLE ht' i)) = fun i : Fin t => zzE p NE ω (i : ℕ) := by
      funext i
      rw [zzE_lt ω (lt_of_lt_of_le i.2 ht')]
      rfl
    rw [hfun, ← runZ_eq_runFin p ℓs (zzE p NE ω) hps hq t]
    rfl
  rw [Finset.sum_congr rfl hday, Finset.sum_comm]
  calc ∑ ω : Fin (NE + 1) → A.Z, ∑ t ∈ range (NE + 1), A.W ω *
        Pool.P0015.E (playL p (runZ p ℓs (zzE p NE ω) hps hq t).1) (fun i => ((ℓs t i).toNat : ℝ))
      ≤ ∑ ω : Fin (NE + 1) → A.Z, A.W ω * (1 + G (arrOf p NE ω)) := by
        refine Finset.sum_le_sum fun ω _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (hW0 _ ω)
        have := path_le h hEN hps hq ℓs ω
        simp only [hG]
        linarith
    _ = 1 + ∑ ω : Fin (NE + 1) → A.Z, A.W ω * G (arrOf p NE ω) := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib]
        rw [Pool.P0064.sum_W]
    _ = 1 + ∑ y : Fin (NE + 1) × Jd p → Bool,
          bw (fun tj : Fin (NE + 1) × Jd p => qd p ps q tj.2) y * G (y ∘ σT p NE) := by
        congr 1
        refine Fintype.sum_equiv (Equiv.curry (Fin (NE + 1)) (Jd p) Bool).symm _ _ ?_
        intro ω
        rw [W_eq_bw hps hq ω]
        rfl
    _ = 1 + ∑ ω' : Arr p NE → Bool, bw (fun x => qd p ps q (σT p NE x).2) ω' * G ω' := by
        congr 1
        exact Pool.P0084.sum_bw_comp _ (σT p NE) (σT_inj p NE) G
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun ω' _ => ?_
        congr 1
        unfold bw Pool.P0048.wtv Pool.P0048.cw
        refine Finset.prod_congr rfl fun x _ => ?_
        rcases x with ⟨e | ⟨a, r, ℓ, k⟩, c⟩ <;> rfl

end Law

end Pool.P0116
