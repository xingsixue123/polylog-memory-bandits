import Pool.P0121.Run
import Pool.P0084.Machine
import Pool.P0091.Exp

/-!
# Expected loss of the threaded machine: the learner's per-unit loss on the abstract process, under P0082/P0091's
# coin-array law

* `Aw ℓ ω u`: the learner's expected loss on unit `u < NE` of the abstract run of the coin array `ω`: P0089's
  `palgLoss` (P0102's ideal learner along P0065's start pools) if some copy is present, the loss of arm `0` otherwise.
* `dayLoss_eq`: on a day of a good run, the machine's expected loss is `Aw`.
* `path_le`: pathwise, the machine's expected losses over days `1, …, NE` are at most `Ψ ω` (`Σ_u Aw` if every unit is
  good, `NE` otherwise).
* `sum_expLoss_le`: `Σ_{t ≤ NE} expLoss ≤ 1 + Σ_ω wtv (pC ps q) ω · Ψ ω`.
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0030 Pool.P0042 Pool.P0052 Pool.P0065 Pool.P0121.TS Pool.P0121.TM Pool.P0121.TMRun

namespace Pool.P0121.TL

variable {n NE D : ℕ} [NeZero n] {Lv L M Lt K R : ℕ} (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (θ η ε : ℝ) (Ns : ℕ)

section Def

variable (ℓ : LossSeq n) (ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool)

/-- The ideal grid indices. -/
noncomputable abbrev kLi : ℕ → ℕ := fun u => (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω u).1

/-- The ideal per-copy learner data. -/
noncomputable abbrev lwi : ℕ → Cp n NE D → ℕ → ℕ × ℕ := fun u => (idl (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω u).2

open Classical in
/-- **The learner's loss on unit `u`** of the abstract run. -/
noncomputable def Aw (u : ℕ) : ℝ :=
  if u < NE then
    (if (pr (Lv := Lv) (R := R) Bt lev θ ℓ ω u).Nonempty then
      Pool.P0089.palgLoss (fun _ => (1 : ℝ)) η (Pool.P0102.aw L (pr (Lv := Lv) (R := R) Bt lev θ ℓ ω))
        (Pool.P0102.cs L (bt ℓ))
        (Pool.P0102.rho L (pr (Lv := Lv) (R := R) Bt lev θ ℓ ω) (bt ℓ) η ε
          (kLi (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω) (lwi (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω)) u
    else ((ℓ (u + 1) ⟨0, NeZero.pos n⟩).toNat : ℝ))
  else 0

end Def

section DayLoss

variable (ℓ : LossSeq n) (ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool)

theorem E_playL (x : RawT n NE D Lv L M) (hne : (U x).Nonempty) (f : Fin n → ℝ) :
    Pool.P0015.E (playL η ε x) f =
      (∑ c ∈ U x, (∑ j : Fin (L + 1), wgt η ε x c j) * f (arm n NE D c)) / mass (L := L) η ε x := by
  classical
  unfold Pool.P0015.E playL
  rw [dif_pos hne]
  simp only [PMF.ofFintype_apply, ENNReal.toReal_ofReal (armW_nonneg η ε x _)]
  unfold armW
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_fiberwise (U x) (arm n NE D) (fun c => (∑ j : Fin (L + 1), wgt η ε x c j) * f (arm n NE D c))]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro c hc
  rw [(Finset.mem_filter.mp hc).2]

/-- **One day's expected loss is the learner's**: on unit `a` of a good run with a nonempty pool. -/
theorem dayLoss_eq (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) {a : ℕ} (ha : a < NE)
    (haL : a < 2 ^ L) {x : RawT n NE D Lv L M} (hinv : Inv (L := L) (R := R) Bt lev θ η ε ℓ ω a x)
    (hne : (U x).Nonempty) :
    Pool.P0015.E (playL η ε x) (fun i => ((ℓ (a + 1) i).toNat : ℝ)) = Aw (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω a := by
  classical
  have hU := hinv.2.1
  have hne' : (pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a).Nonempty := by rw [← hU]; exact hne
  unfold Aw
  rw [if_pos ha, if_pos hne',
    Pool.P0102.palgLoss_eq (Pool.P0121.TMI.ideal_rec L _ (bt ℓ) η ε) (hent Bt lev θ ℓ ω hD hLv hlev) haL,
    E_playL η ε x hne]
  have hw : ∀ c ∈ U x, ∀ j : Fin (L + 1), wgt η ε x c j =
      Pool.P0102.mw η ε (kLi (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω) (lwi (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω) a c j := by
    intro c hc j
    unfold wgt Pool.P0102.mw
    beta_reduce
    rw [hinv.2.2.2.2 c hc j j.2, hinv.2.2.2.1]
  have hm : mass (L := L) η ε x = Pool.P0102.mA L (pr (Lv := Lv) (R := R) Bt lev θ ℓ ω) η ε
      (kLi (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω) (lwi (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω) a := by
    unfold mass Pool.P0102.mA
    simp only
    rw [← hU]
    exact Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun j _ => hw c hc j
  rw [hm, ← hU]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.sum_congr rfl fun j _ => hw c hc j]
  rfl

theorem palgLoss_le_one {ι : Type} [Fintype ι] {η' : ℝ} {aw' : ℕ → ι → Bool} {c : ℕ → ι → ℝ} {ρ : ℕ → ℝ}
    (hc0 : ∀ t j, 0 ≤ c t j) (hc1 : ∀ t j, c t j ≤ 1) (t : ℕ) :
    Pool.P0089.palgLoss (fun _ => (1 : ℝ)) η' aw' c ρ t ≤ 1 := by
  unfold Pool.P0089.palgLoss
  have hp := Pool.P0089.pprob_nonneg (q := fun _ => (1 : ℝ)) (η := η') (aw := aw') (c := c) (ρ := ρ)
    (fun _ => one_pos) t
  by_cases hex : ∃ i, aw' t i = true
  · obtain ⟨i, hi⟩ := hex
    have hs := Pool.P0089.sum_pprob (q := fun _ => (1 : ℝ)) (η := η') (c := c) (ρ := ρ) (fun _ => one_pos) t hi
    calc ∑ j, Pool.P0089.pprob (fun _ => (1 : ℝ)) η' aw' c ρ t j * c t j
        ≤ ∑ j, Pool.P0089.pprob (fun _ => (1 : ℝ)) η' aw' c ρ t j * 1 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hc1 t j) (hp j)
      _ = 1 := by simp only [mul_one]; exact hs
  · push Not at hex
    have : ∀ j, Pool.P0089.pprob (fun _ => (1 : ℝ)) η' aw' c ρ t j = 0 := by
      intro j; simp [Pool.P0089.pprob, hex j]
    simp [this]

theorem palgLoss_nonneg {ι : Type} [Fintype ι] {η' : ℝ} {aw' : ℕ → ι → Bool} {c : ℕ → ι → ℝ} {ρ : ℕ → ℝ}
    (hc0 : ∀ t j, 0 ≤ c t j) (t : ℕ) : 0 ≤ Pool.P0089.palgLoss (fun _ => (1 : ℝ)) η' aw' c ρ t :=
  Finset.sum_nonneg fun j _ => mul_nonneg (Pool.P0089.pprob_nonneg (fun _ => one_pos) t j) (hc0 t j)

theorem cs_mem (t : ℕ) (j : Pool.P0089.Spec (Cp n NE D) L) :
    0 ≤ Pool.P0102.cs L (bt ℓ) t j ∧ Pool.P0102.cs L (bt ℓ) t j ≤ 1 := by
  unfold Pool.P0102.cs Pool.P0089.specLoss
  beta_reduce
  have := bt_le_one ℓ t j.1
  constructor
  · positivity
  · exact_mod_cast this

theorem Aw_mem (u : ℕ) : 0 ≤ Aw (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω u ∧
    Aw (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω u ≤ 1 := by
  classical
  unfold Aw
  split_ifs with h1 h2
  · exact ⟨palgLoss_nonneg (fun t j => (cs_mem ℓ t j).1) u,
      palgLoss_le_one (fun t j => (cs_mem ℓ t j).1) (fun t j => (cs_mem ℓ t j).2) u⟩
  · cases ℓ (u + 1) ⟨0, NeZero.pos n⟩ <;> simp
  · norm_num

end DayLoss

section Total

variable {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)

open Classical in
/-- The pathwise cost of a coin array: the learner's losses if every unit is good, `NE` otherwise. -/
noncomputable def Ψ (ℓ : LossSeq n) (ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool) : ℝ :=
  if ∀ a < NE, Good (Lv := Lv) (R := R) Bt lev θ Ns ℓ ω a then
    ∑ u ∈ range NE, Aw (Lv := Lv) (L := L) (R := R) Bt lev θ η ε ℓ ω u
  else NE

/-- **Pathwise loss of the machine** on days `1, …, NE`. -/
theorem path_le (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hlevLt : ∀ r a, lev r a < Lt + 1) (hη : 0 ≤ η) (hε : 0 < ε) (hM : NE * ⌊η / ε⌋₊ ≤ M) (hNL : NE ≤ 2 ^ L)
    (ℓ : LossSeq n) (zf : ℕ → Jd n NE D Lt K → Bool) :
    ∑ t ∈ range NE, Pool.P0015.E ((tmach (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE)
        (D := D) Bt lev θ η ε Ns hps hq).play (t + 1)
        ((tmach (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE) (D := D) Bt lev θ η ε Ns
          hps hq).runFin ℓ (t + 1) (fun i => zf i)))
        (fun i => ((ℓ (t + 1) i).toNat : ℝ)) ≤
      Ψ (Lv := Lv) (L := L) (R := R) Bt lev θ η ε Ns ℓ (Φ zf) := by
  classical
  set A := tmach (n := n) (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE) (D := D) Bt lev θ η ε Ns
    hps hq with hA
  have hle1 : ∀ t, Pool.P0015.E (A.play (t + 1) (A.runFin ℓ (t + 1) (fun i => zf i)))
      (fun i => ((ℓ (t + 1) i).toNat : ℝ)) ≤ 1 := by
    intro t
    apply Pool.P0084.E_le_one
    intro i; cases ℓ (t + 1) i <;> simp
  unfold Ψ
  split_ifs with hg
  · apply Finset.sum_le_sum; intro a ha
    have ha' : a < NE := Finset.mem_range.mp ha
    have hinv := run_inv (L := L) Bt lev θ η ε Ns ℓ hps hq hD hLv hlev hlevLt hη hε hM zf a ha'
      (fun a' h => hg a' (by omega))
    apply le_of_eq
    show Pool.P0015.E (playL η ε (A.runFin ℓ (a + 1) (fun i => zf i)).1) _ = _
    by_cases hne : (U (A.runFin ℓ (a + 1) (fun i => zf i)).1).Nonempty
    · exact dayLoss_eq Bt lev θ η ε ℓ (Φ zf) hD hLv hlev ha' (lt_of_lt_of_le ha' hNL) hinv hne
    · have hpr : ¬ (pr (Lv := Lv) (R := R) Bt lev θ ℓ (Φ zf) a).Nonempty := by rw [← hinv.2.1]; exact hne
      unfold playL Aw
      rw [dif_neg hne, if_pos ha', if_neg hpr, Pool.P0064.E_pure']
  · calc _ ≤ ∑ _t ∈ range NE, (1 : ℝ) := Finset.sum_le_sum fun t _ => hle1 t
      _ = NE := by simp

end Total

/-- The day-coin space is finite (nested too deep for default instance search). -/
noncomputable def dayFintype (n NE D Lt K : ℕ) : Fintype (Fin (NE + 1) × Jd n NE D Lt K → Bool) :=
  @Pi.instFintype _ _ instDecidableEqProd inferInstance (fun _ => inferInstance)

section Final

attribute [local instance] Pool.P0082.coinFintype dayFintype

open Pool.P0046
open scoped Pool.P0064

variable {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)

/-- Where each coin of P0082's array sits among the machine's day coins: sampling bits of unit `a` on day `a`,
filter bits of the merges ending unit `a` on day `a + 1`. -/
def σ : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Fin (NE + 1) × Jd n NE D Lt K
  | (Sum.inl a, c) => (⟨a.1, by omega⟩, Sum.inr c)
  | (Sum.inr (a, r, j, k), c) => (⟨a.1 + 1, by omega⟩, Sum.inl (r, j, k, c))

theorem σ_inj : Function.Injective (σ (n := n) (NE := NE) (D := D) (Lt := Lt) (K := K)) := by
  rintro ⟨s, c⟩ ⟨s', c'⟩ h
  rcases s with a | ⟨a, r, j, k⟩ <;> rcases s' with a' | ⟨a', r', j', k'⟩ <;>
    simp only [σ, Prod.mk.injEq, Fin.mk.injEq, reduceCtorEq, and_false, Sum.inr.injEq, Sum.inl.injEq] at h
  · rw [Fin.ext h.1, h.2]
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    rw [Fin.ext (by omega : a.1 = a'.1), h2, h3, h4, h5]

theorem Φ_ext (d : Jd n NE D Lt K → Bool) (ω : Fin (NE + 1) → Jd n NE D Lt K → Bool) :
    Φ (Pool.P0084.ext d ω) = fun sc => ω (σ sc).1 (σ sc).2 := by
  funext sc
  rcases sc with ⟨a | ⟨a, r, j, k⟩, c⟩
  · simp only [Φ, σ, Pool.P0084.ext]
    rw [dif_pos (by omega)]
  · simp only [Φ, σ, Pool.P0084.ext]
    rw [dif_pos (by omega)]

theorem W_eq_bw (ω : Fin (NE + 1) → Jd n NE D Lt K → Bool) :
    (tmach (n := n) (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE) (D := D) Bt lev θ η ε Ns
      hps hq).W ω = bw (fun tj : Fin (NE + 1) × Jd n NE D Lt K => qd ps q tj.2) (fun tj => ω tj.1 tj.2) := by
  unfold Pool.P0064.QCoinAlg.W
  rw [← Pool.P0084.prod_bw_curry]
  apply Fintype.prod_congr; intro t
  show (Pool.P0051.bernVec (qd ps q) (qd_mem hps hq) (ω t)).toReal = _
  rw [Pool.P0051.bernVec_apply]
  rfl

theorem wtv_eq_bw (p : Pool.P0082.SlotC NE D Lt K × Cp n NE D → ℝ) (ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool) :
    Pool.P0048.wtv p ω = bw p ω := rfl

/-- **Expected loss of the threaded machine.** Over days `0, …, NE`, its expected loss is at most `1 + E_ω[Ψ ω]`,
where `ω` is P0082's coin array with P0091's law `wtv (pC ps q)`. -/
theorem sum_expLoss_le (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hlevLt : ∀ r a, lev r a < Lt + 1) (hη : 0 ≤ η) (hε : 0 < ε) (hM : NE * ⌊η / ε⌋₊ ≤ M) (hNL : NE ≤ 2 ^ L)
    (ℓ : LossSeq n) :
    ∑ t ∈ range (NE + 1), (tmach (n := n) (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE)
        (D := D) Bt lev θ η ε Ns hps hq).toQ.expLoss ℓ t ≤
      1 + ∑ ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool,
        Pool.P0048.wtv (Pool.P0091.pC ps q) ω * Ψ (Lv := Lv) (L := L) (R := R) Bt lev θ η ε Ns ℓ ω := by
  classical
  set A := tmach (n := n) (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE) (D := D) Bt lev θ η ε
    Ns hps hq with hA
  have hW0 : ∀ (T : ℕ) (ω : Fin T → A.Z), 0 ≤ A.W ω := fun _ _ =>
    Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg
  rw [Finset.sum_range_succ', add_comm]
  apply add_le_add
  · rw [Pool.P0064.expLoss_eq]
    calc _ ≤ ∑ ω : Fin 0 → A.Z, A.W ω * 1 :=
          Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
            (Pool.P0084.E_le_one _ _ fun i => by cases ℓ 0 i <;> simp) (hW0 _ ω)
      _ = 1 := by simp only [mul_one]; exact Pool.P0064.sum_W A 0
  · have hday : ∀ t ∈ range NE, A.toQ.expLoss ℓ (t + 1) =
        ∑ ω : Fin (NE + 1) → A.Z, A.W ω * Pool.P0015.E (A.play (t + 1) (A.runFin ℓ (t + 1)
          (fun i => Pool.P0084.ext (ω ⟨0, Nat.succ_pos _⟩) ω i)))
          (fun i => ((ℓ (t + 1) i).toNat : ℝ)) := by
      intro t ht
      have ht' : t + 1 ≤ NE + 1 := by have := Finset.mem_range.mp ht; omega
      rw [Pool.P0064.expLoss_eq, ← Pool.P0084.sum_W_restrict A (t + 1) _ (NE + 1) ht']
      apply Finset.sum_congr rfl; intro ω _
      have hfun : (fun i : Fin (t + 1) => ω (Fin.castLE ht' i)) =
          fun i : Fin (t + 1) => Pool.P0084.ext (ω ⟨0, Nat.succ_pos _⟩) ω (i : ℕ) := by
        funext i; unfold Pool.P0084.ext
        rw [dif_pos (lt_of_lt_of_le i.2 ht')]
        rfl
      rw [hfun]
    rw [Finset.sum_congr rfl hday, Finset.sum_comm]
    calc ∑ ω : Fin (NE + 1) → A.Z, ∑ t ∈ range NE, A.W ω * Pool.P0015.E
          (A.play (t + 1) (A.runFin ℓ (t + 1) (fun i => Pool.P0084.ext (ω ⟨0, Nat.succ_pos _⟩) ω i)))
            (fun i => ((ℓ (t + 1) i).toNat : ℝ))
        ≤ ∑ ω : Fin (NE + 1) → A.Z, A.W ω * Ψ (Lv := Lv) (L := L) (R := R) Bt lev θ η ε Ns ℓ
            (fun sc => ω (σ sc).1 (σ sc).2) := by
          apply Finset.sum_le_sum; intro ω _
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (hW0 _ ω)
          have := path_le (R := R) Bt lev θ η ε Ns hps hq hD hLv hlev hlevLt hη hε hM hNL ℓ
            (Pool.P0084.ext (ω ⟨0, Nat.succ_pos _⟩) ω)
          refine this.trans (le_of_eq ?_)
          congr 1
          exact Φ_ext _ _
      _ = ∑ y : Fin (NE + 1) × Jd n NE D Lt K → Bool,
            bw (fun tj : Fin (NE + 1) × Jd n NE D Lt K => qd ps q tj.2) y *
              Ψ (Lv := Lv) (L := L) (R := R) Bt lev θ η ε Ns ℓ (fun sc => y (σ sc)) := by
          refine Fintype.sum_equiv (Equiv.curry (Fin (NE + 1)) (Jd n NE D Lt K) Bool).symm _ _ ?_
          intro ω
          rw [W_eq_bw Bt lev θ η ε Ns hps hq ω]
          rfl
      _ = ∑ ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool, Pool.P0048.wtv (Pool.P0091.pC ps q) ω * Ψ (Lv := Lv) (L := L) (R := R) Bt lev θ η ε Ns ℓ ω := by
          refine (Pool.P0084.sum_bw_comp _ σ σ_inj
            (fun y' => Ψ (Lv := Lv) (L := L) (R := R) Bt lev θ η ε Ns ℓ y')).trans ?_
          apply Finset.sum_congr rfl; intro ω _
          rw [wtv_eq_bw]
          congr 2
          funext sc
          rcases sc with ⟨a | ⟨a, r, j, k⟩, c⟩ <;> rfl

end Final

end Pool.P0121.TL
