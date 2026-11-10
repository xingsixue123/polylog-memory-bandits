import Pool.P0121.Loss

/-!
# Regret of the threaded machine: assembly with P0091 (abstract parameters)
-/

open Finset Pool.P0001 Pool.P0015 Pool.P0030 Pool.P0042 Pool.P0052 Pool.P0065 Pool.P0121.TS Pool.P0121.TM Pool.P0121.TMRun
  Pool.P0121.TL

namespace Pool.P0121.TA

variable {n NE D : ℕ} [NeZero n] {Lv L M Lt K R : ℕ} (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (θ η ε : ℝ) (Ns : ℕ)

section Good

variable {ι : Type} [LinearOrder ι] [Fintype ι] {E' thr0' : ι → ℕ}

/-- Membership in the start pools: an old copy, or a sampled new one. -/
theorem mem_startPools' {ωs' : ι → Bool} {a : ℕ} {P : ℕ → ℕ → Finset ι} {c : ι} {r j : ℕ}
    (h : c ∈ startPools E' thr0' D Lv Bt ωs' a P r j) :
    (∃ r' j', c ∈ P r' j') ∨ (∃ r', r' < D ∧ Bt r' ∣ a ∧ c ∈ newAtT E' thr0' ωs' a r') := by
  unfold startPools sample at h
  split_ifs at h with h1
  · rcases Finset.mem_union.1 h with h | h
    · left
      unfold inherit at h
      split_ifs at h with h2 h3 h4
      · exact ⟨_, _, h⟩
      · rcases Finset.mem_union.1 h with h | h
        · exact ⟨_, _, h⟩
        · obtain ⟨r', -, hr'⟩ := Finset.mem_biUnion.1 h
          obtain ⟨j', -, hj'⟩ := Finset.mem_biUnion.1 hr'
          exact ⟨_, _, hj'⟩
      · exact ⟨_, _, h⟩
      · simp at h
    · right
      exact ⟨r, h1.2.2, h1.2.1, h⟩
  · left
    unfold inherit at h
    split_ifs at h with h2 h3 h4
    · exact ⟨_, _, h⟩
    · rcases Finset.mem_union.1 h with h | h
      · exact ⟨_, _, h⟩
      · obtain ⟨r', -, hr'⟩ := Finset.mem_biUnion.1 h
        obtain ⟨j', -, hj'⟩ := Finset.mem_biUnion.1 hr'
        exact ⟨_, _, hj'⟩
    · exact ⟨_, _, h⟩
    · simp at h

end Good

section Card

variable (ℓ : LossSeq n) (ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool)

/-- **On a good run every unit has at most `D·Lv·S' + D·s0` present copies** (`S' = s0 + D·Lv·S`). -/
theorem card_pr_le (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (s0 : ℕ) (M0 ρK S : ℝ)
    (hρK : 0 ≤ ρK) (hM0S : M0 ≤ S) (hS0 : 0 ≤ S) (hρS : ρK * (S + (s0 + D * Lv * S)) ≤ S)
    (hgood : Pool.P0073.GoodRunT (E n NE D) (thr0 n NE D) (Pool.P0061.cumL (cu ℓ)) θ R K D Lv Bt lev
      (Pool.P0082.ωsC (E n NE D) NE D Lt K ω) (Pool.P0082.φC NE D Lt K ω) NE s0 M0 ρK)
    {a : ℕ} (ha : a < NE) :
    ((pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a).card : ℝ) ≤ D * Lv * (s0 + D * Lv * S) + D * s0 := by
  classical
  have hcard := Pool.P0073.tpools_card_le hB hLv hlev _ _ NE s0 M0 ρK S hρK hgood hM0S hS0 hρS a ha.le
  set P := tp (Lv := Lv) (R := R) Bt lev θ ℓ ω a with hP
  have hsub : pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a ⊆
      ((range D).biUnion fun r => (range Lv).biUnion fun j => P r j) ∪
        ((range D).filter (fun r => Bt r ∣ a)).biUnion
          (fun r => newAtT (E n NE D) (thr0 n NE D) (Pool.P0082.ωsC (E n NE D) NE D Lt K ω) a r) := by
    intro c hc
    obtain ⟨r, j, h⟩ := (mem_pr Bt lev θ ℓ ω).1 hc
    rcases mem_startPools' Bt h with ⟨r', j', h'⟩ | ⟨r', hr', hdv, h'⟩
    · obtain ⟨-, -, hj', hr''⟩ := tpools_ok hB.hD hLv hlev _ _ a c r' j' h'
      exact Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨r', Finset.mem_range.2 hr'',
        Finset.mem_biUnion.2 ⟨j', Finset.mem_range.2 hj', h'⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨r', Finset.mem_filter.2
        ⟨Finset.mem_range.2 hr', hdv⟩, h'⟩)
  have h1 : (((range D).biUnion fun r => (range Lv).biUnion fun j => P r j).card : ℝ) ≤
      D * Lv * (s0 + D * Lv * S) := by
    have hpool : ∀ r j, ((P r j).card : ℝ) ≤ s0 + D * Lv * S := by
      intro r j
      by_cases hj : j = 0
      · subst hj; exact hcard.2.1 r
      · refine (hcard.1 r j hj).trans ?_
        have : (1 : ℝ) ≤ D * Lv := by
          have : (1 : ℕ) ≤ D * Lv := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hB.hD.ne' hLv.ne')
          exact_mod_cast this
        nlinarith [Nat.cast_nonneg (α := ℝ) s0]
    calc (((range D).biUnion fun r => (range Lv).biUnion fun j => P r j).card : ℝ)
        ≤ ∑ r ∈ range D, ∑ j ∈ range Lv, ((P r j).card : ℝ) := by
          refine (Nat.cast_le.2 (Finset.card_biUnion_le)).trans ?_
          push_cast
          exact Finset.sum_le_sum fun r _ => by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ range D, ∑ _j ∈ range Lv, ((s0 : ℝ) + D * Lv * S) :=
          Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun j _ => hpool r j
      _ = D * Lv * (s0 + D * Lv * S) := by simp; ring
  have h2 : ((((range D).filter (fun r => Bt r ∣ a)).biUnion
      (fun r => newAtT (E n NE D) (thr0 n NE D) (Pool.P0082.ωsC (E n NE D) NE D Lt K ω) a r)).card : ℝ) ≤
      D * s0 := by
    calc _ ≤ ∑ r ∈ (range D).filter (fun r => Bt r ∣ a),
          ((newAtT (E n NE D) (thr0 n NE D) (Pool.P0082.ωsC (E n NE D) NE D Lt K ω) a r).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ (range D).filter (fun r => Bt r ∣ a), (s0 : ℝ) := by
          refine Finset.sum_le_sum fun r hr => ?_
          rw [Finset.mem_filter, Finset.mem_range] at hr
          exact_mod_cast hgood.1 a ha r hr.1 hr.2
      _ ≤ ∑ _r ∈ range D, (s0 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
      _ = D * s0 := by simp
  calc ((pr (Lv := Lv) (R := R) Bt lev θ ℓ ω a).card : ℝ)
      ≤ ((((range D).biUnion fun r => (range Lv).biUnion fun j => P r j) ∪
        ((range D).filter (fun r => Bt r ∣ a)).biUnion
          (fun r => newAtT (E n NE D) (thr0 n NE D) (Pool.P0082.ωsC (E n NE D) NE D Lt K ω) a r)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ _ := by
        refine (Nat.cast_le.2 (Finset.card_union_le _ _)).trans ?_
        push_cast
        linarith

end Card

section Copies

/-- The copy of arm `i` entering at unit `a` on thread `j` (indices reduced modulo `NE`, `D`). -/
def cop (hNE : 0 < NE) (hD : 0 < D) (j a : ℕ) (i : Fin n) : Cp n NE D :=
  ⟨((a % NE) * D + j % D) * n + i, by
    have h1 := Nat.mod_lt a hNE
    have h2 := Nat.mod_lt j hD
    have h3 := i.2
    calc ((a % NE) * D + j % D) * n + i < ((a % NE) * D + j % D) * n + n := by omega
      _ = ((a % NE) * D + j % D + 1) * n := by ring
      _ ≤ ((a % NE) * D + D) * n := Nat.mul_le_mul_right _ (by omega)
      _ = ((a % NE) + 1) * D * n := by ring
      _ ≤ NE * D * n := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))⟩

theorem E_cop (hNE : 0 < NE) (hD : 0 < D) {j a : ℕ} (hj : j < D) (ha : a < NE) (i : Fin n) :
    Pool.P0121.TM.E n NE D (cop hNE hD j a i) = a := by
  unfold Pool.P0121.TM.E cop
  simp only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hj]
  have hn := NeZero.pos n
  have e : (a * D + j) * n + i = (j * n + i) + a * (D * n) := by ring
  have hlt : j * n + i < D * n := by
    have := i.2
    calc j * n + i < j * n + n := by omega
      _ = (j + 1) * n := by ring
      _ ≤ D * n := Nat.mul_le_mul_right _ hj
  rw [e, Nat.add_mul_div_right _ _ (Nat.mul_pos hD hn), Nat.div_eq_of_lt hlt, zero_add]

theorem thr0_cop (hNE : 0 < NE) (hD : 0 < D) {j a : ℕ} (hj : j < D) (ha : a < NE) (i : Fin n) :
    thr0 n NE D (cop hNE hD j a i) = j := by
  unfold thr0 cop
  simp only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hj]
  have hn := NeZero.pos n
  have e : (a * D + j) * n + i = i + (a * D + j) * n := by ring
  rw [e, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt i.2, zero_add, Nat.add_comm, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hj]

theorem arm_cop (hNE : 0 < NE) (hD : 0 < D) {j a : ℕ} (hj : j < D) (ha : a < NE) (i : Fin n) :
    arm n NE D (cop hNE hD j a i) = i := by
  unfold arm cop
  apply Fin.ext
  simp only [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hj]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.2]

end Copies

section Assembly

attribute [local instance] Pool.P0082.coinFintype

/-- The learner's additive constant (P0089's `hedge_interval_hyp` with `δ = ε`, horizon `NE`). -/
noncomputable def αL (n NE D L : ℕ) (η ε : ℝ) : ℝ :=
  (2 * L + 1) * (Real.log (Fintype.card (Pool.P0089.Spec (Cp n NE D) L)) + 2 * ε * NE) / η

variable {Lm : ℕ} {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq : 0 ≤ q ∧ q ≤ 1)

theorem levTh_le (Lm : ℕ) (r a : ℕ) : Pool.P0085.levTh Lm Bt r a ≤ Lm := by
  have := Pool.P0062.levPR_le Lm ((a + 1) / Bt r - 1)
  unfold Pool.P0085.levTh; omega

theorem sum_wtv_pC : ∑ ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool, Pool.P0048.wtv (Pool.P0091.pC ps q) ω = 1 := by
  have h := Pool.P0046.sum_bw2 (Pool.P0073.qOfT (ι := Cp n NE D) (NE := NE) (Lt := Lt) K D ps q)
  rw [← h, ← (Equiv.curry (Pool.P0082.SlotC NE D Lt K) (Cp n NE D) Bool).symm.sum_comp]
  refine Finset.sum_congr rfl fun ω2 _ => ?_
  exact Pool.P0091.wtv_uncurryT ω2

include hps hq in
theorem wtv_nonneg (ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool) :
    0 ≤ Pool.P0048.wtv (Pool.P0091.pC (ι := Cp n NE D) ps q) ω :=
  Finset.prod_nonneg fun x _ => by
    rcases x with ⟨s, c⟩
    unfold Pool.P0048.cw
    cases s <;> split_ifs <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith [hps.1, hps.2, hq.1, hq.2]

include hps hq in
open Classical in
/-- P0073's bad-run bound, transferred to P0082's coin array. -/
theorem fail_le (ℓ : LossSeq n) (hB : BtHyp D Bt) (hLv : 0 < Lv)
    (hlev : ∀ r a, lev r a + 1 < Lv) (hq1' : q ≤ 1)
    (Tmax : ℝ) (hC : ∀ (i : Cp n NE D) a b, a ≤ b → b ≤ NE → 0 ≤ Lint (Pool.P0061.cumL (cu ℓ)) i a b ∧
      Lint (Pool.P0061.cumL (cu ℓ)) i a b ≤ Tmax)
    (hR1 : 1 ≤ R) (hTm : Tmax ≤ 2 ^ (R - 1) * θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt)
    (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => Pool.P0121.TM.E n NE D c = a ∧ thr0 n NE D c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => Pool.P0121.TM.E n NE D c = a ∧ thr0 n NE D c = r).card -
          F.card) * (if s0 < F.card then 1 else 0) ≤ δs) :
    ∑ ω : Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool, Pool.P0048.wtv (Pool.P0091.pC ps q) ω *
      (if Pool.P0073.GoodRunT (Pool.P0121.TM.E n NE D) (thr0 n NE D) (Pool.P0061.cumL (cu ℓ)) θ R K D Lv Bt lev
        (Pool.P0082.ωsC (Pool.P0121.TM.E n NE D) NE D Lt K ω) (Pool.P0082.φC NE D Lt K ω) NE s0 M0
          ((1 - 1 / (4 * R : ℝ)) ^ K) then 0 else 1) ≤
      NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card (Cp n NE D)) q R kk M0 := by
  have h := Pool.P0073.prob_not_goodRunT (Pool.P0121.TM.E n NE D) (thr0 n NE D) (Pool.P0061.cumL (cu ℓ)) θ R K D Lv Bt lev
    M0 kk hps hq.1 hq1' (E_mono n NE D) hB.hD hLv hlev Tmax hC hR1 hTm hM0 hk hp hlevLt s0 δs hs
  refine le_trans (le_of_eq ?_) h
  rw [← (Equiv.curry (Pool.P0082.SlotC NE D Lt K) (Cp n NE D) Bool).symm.sum_comp]
  refine Finset.sum_congr rfl fun ω2 _ => ?_
  simp only [Equiv.curry_symm_apply]
  rw [Pool.P0091.wtv_uncurryT ω2]
  rfl

open Classical in
/-- **Regret of the threaded K-query machine** (abstract parameters): `1 +` P0091's closed form (with P0089/P0102's
learner constants `α = αL`, `β = η/2`, `Bep = 1`) `+ NE·`P0073's bad-run bound. -/
theorem regret_le (hB : BtHyp D Bt) (hLv2 : Lm + 2 ≤ Lv) (hLt : Lm ≤ Lt) (hT : Bt 0 ∣ NE) (hNE : 0 < NE)
    (hη : 0 < η) (hε : 0 < ε) (hM : NE * ⌊η / ε⌋₊ ≤ M) (hNL : NE ≤ 2 ^ L) (hθ : 0 ≤ θ) (hR1 : 1 ≤ R)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ∀ j, j + 1 < D → (Bt j : ℝ) ≤ ρ * Bt (j + 1))
    (hps0 : 0 < ps) (hq1 : q < 1) (Tmax : ℝ) (hTmax : (NE : ℝ) ≤ Tmax) (hTm : Tmax ≤ 2 ^ (R - 1) * θ)
    (M0 : ℝ) (kk : ℕ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * R))
    (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => Pool.P0121.TM.E n NE D c = a ∧ thr0 n NE D c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => Pool.P0121.TM.E n NE D c = a ∧ thr0 n NE D c = r).card -
          F.card) * (if s0 < F.card then 1 else 0) ≤ δs)
    (S : ℕ) (hM0S : M0 ≤ S) (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * (S + (s0 + D * Lv * S)) ≤ S)
    (hNs : D * Lv * (s0 + D * Lv * S) + D * s0 ≤ Ns) (ℓ : LossSeq n) :
    (tmach (n := n) (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R) (NE := NE) (D := D) Bt
      (Pool.P0085.levTh Lm Bt) θ η ε Ns hps hq).toQ.regret ℓ (NE + 1) ≤
      1 + ((θ + R * αL n NE D L η ε) * (NE / Bt 0) + η / 2 * NE + ((θ + R * αL n NE D L η ε) * ρ + 1) *
        ((D * Lv * (s0 + D * Lv * S + 1) : ℝ) / (ps * (1 - q) ^ (K * (D * (2 * Lm + NE / 2 ^ Lm + 1)))) +
          D * NE * (NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card (Cp n NE D)) q R kk M0))) +
      NE * (NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card (Cp n NE D)) q R kk M0) := by
  have hD := hB.hD
  have hLv : 0 < Lv := by omega
  have hlev : ∀ r a, (Pool.P0085.levTh Lm Bt) r a + 1 < Lv := fun r a => by have := levTh_le Bt Lm r a; omega
  have hlevLt : ∀ r a, (Pool.P0085.levTh Lm Bt) r a < Lt + 1 := fun r a => by have := levTh_le Bt Lm r a; omega
  obtain ⟨istar, hbest⟩ := exists_bestLoss_eq ℓ (NE + 1)
  set g : ℕ → ℝ := fun u => ((ℓ (u + 1) istar).toNat : ℝ) with hg
  set W : (Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool) → ℝ := fun ω => Pool.P0048.wtv (Pool.P0091.pC ps q) ω
  have hW0 : ∀ ω, 0 ≤ W ω := wtv_nonneg hps hq
  have hW1 : ∑ ω, W ω = 1 := sum_wtv_pC
  set ρK : ℝ := (1 - 1 / (4 * R : ℝ)) ^ K
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR1
  have hρK0 : 0 ≤ ρK := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR1
    linarith
  set GR : (Pool.P0082.SlotC NE D Lt K × Cp n NE D → Bool) → Prop := fun ω =>
    Pool.P0073.GoodRunT (Pool.P0121.TM.E n NE D) (thr0 n NE D) (Pool.P0061.cumL (cu ℓ)) θ R K D Lv Bt (Pool.P0085.levTh Lm Bt)
      (Pool.P0082.ωsC (Pool.P0121.TM.E n NE D) NE D Lt K ω) (Pool.P0082.φC NE D Lt K ω) NE s0 M0 ρK
  -- (1) the machine's expected loss
  have hloss := sum_expLoss_le (L := L) (M := M) (K := K) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε Ns hps hq hD hLv hlev hlevLt hη.le hε hM hNL ℓ
  -- (2) pathwise cost vs the learner
  have hΨ : ∀ ω, Ψ (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε Ns ℓ ω ≤
      ∑ u ∈ range NE, Aw (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω u + NE * (if GR ω then 0 else 1) := by
    intro ω
    have hA0 : 0 ≤ ∑ u ∈ range NE, Aw (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω u :=
      Finset.sum_nonneg fun u _ => (Aw_mem (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω u).1
    unfold Ψ
    by_cases hgr : GR ω
    · have hall : ∀ a < NE, Good (Lv := Lv) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ Ns ℓ ω a := by
        intro a ha
        have hc := card_pr_le Bt (Pool.P0085.levTh Lm Bt) θ ℓ ω hB hLv hlev s0 M0 ρK (S : ℝ) hρK0 hM0S (Nat.cast_nonneg _) hρS hgr ha
        unfold Good
        have : ((D * Lv * (s0 + D * Lv * S) + D * s0 : ℕ) : ℝ) ≤ Ns := by exact_mod_cast hNs
        push_cast at this
        exact_mod_cast hc.trans this
      rw [if_pos hall, if_pos hgr]; simp
    · rw [if_neg hgr]
      split_ifs <;> linarith
  -- (3) the comparator
  have hcum : ∑ u ∈ range NE, g u ≤ bestLoss ℓ (NE + 1) := by
    rw [hbest]
    unfold cumLoss
    rw [Finset.sum_range_succ']
    have : 0 ≤ ((ℓ 0 istar).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  -- (4) P0091
  have hcard1 : 1 ≤ Fintype.card (Pool.P0089.Spec (Cp n NE D) L) := by
    have : Nonempty (Pool.P0089.Spec (Cp n NE D) L) :=
      ⟨(⟨0, Nat.mul_pos (Nat.mul_pos hNE hD) (NeZero.pos n)⟩, 0, ⟨0, Nat.two_pow_pos L⟩)⟩
    exact Fintype.card_pos
  haveI : Nonempty (Pool.P0089.Spec (Cp n NE D) L) := Fintype.card_pos_iff.1 hcard1
  have hα0 : 0 ≤ αL n NE D L η ε := by
    unfold αL
    have h1 : 0 ≤ Real.log (Fintype.card (Pool.P0089.Spec (Cp n NE D) L)) :=
      Real.log_nonneg (by exact_mod_cast hcard1)
    have h2 : 0 ≤ 2 * ε * NE := by positivity
    positivity
  have hC : ∀ (i : Cp n NE D) a b, a ≤ b → b ≤ NE → 0 ≤ Lint (Pool.P0061.cumL (cu ℓ)) i a b ∧
      Lint (Pool.P0061.cumL (cu ℓ)) i a b ≤ Tmax := by
    intro i a b hab hb
    rw [Pool.P0061.Lint_cumL (cu ℓ) i hab]
    constructor
    · exact Finset.sum_nonneg fun u _ => Nat.cast_nonneg _
    · calc ∑ u ∈ Ico a b, cu ℓ u i ≤ ∑ _u ∈ Ico a b, (1 : ℝ) :=
            Finset.sum_le_sum fun u _ => by unfold cu; exact_mod_cast bt_le_one ℓ u i
        _ = ((b - a : ℕ) : ℝ) := by simp
        _ ≤ NE := by exact_mod_cast (Nat.sub_le b a).trans hb
        _ ≤ Tmax := hTmax
  have hA : ∀ ω f s s', s ≤ s' → (∀ u, s ≤ u → u < s' → ∃ r j,
      f ∈ startPools (Pool.P0121.TM.E n NE D) (thr0 n NE D) D Lv Bt (Pool.P0082.ωsC (Pool.P0121.TM.E n NE D) NE D Lt K ω) u
        (tpools (Pool.P0121.TM.E n NE D) (thr0 n NE D) (Pool.P0061.cumL (cu ℓ)) θ R K D Lv Bt (Pool.P0085.levTh Lm Bt)
          (Pool.P0082.ωsC (Pool.P0121.TM.E n NE D) NE D Lt K ω) (Pool.P0082.φC NE D Lt K ω) u) r j) →
      ∑ u ∈ Finset.Ico s s', Aw (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω u ≤
        ∑ u ∈ Finset.Ico s s', cu ℓ u f + αL n NE D L η ε + η / 2 * ((s' - s : ℕ) : ℝ) := by
    intro ω f s s' hss' hpres
    have hpres' : ∀ u, s ≤ u → u < s' → f ∈ pr (Lv := Lv) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ ℓ ω u := by
      intro u h1 h2
      obtain ⟨r, j, h⟩ := hpres u h1 h2
      exact mem_pr_of Bt (Pool.P0085.levTh Lm Bt) θ ℓ ω hD hLv hlev h
    have hh := Pool.P0089.hedge_interval_hyp (L := L)
      (fun u f => f ∈ pr (Lv := Lv) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ ℓ ω u) (cu ℓ)
      (fun t f => Nat.cast_nonneg _) (fun t f => by unfold cu; exact_mod_cast bt_le_one ℓ t f) hη hε.le
      (Pool.P0102.rho L (pr (Lv := Lv) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ ℓ ω) (bt ℓ) η ε
        (kLi (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω)
        (lwi (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω))
      (fun t => Pool.P0102.rho_abs_le hη.le hε t) NE hNL f s s' hss' hpres'
    refine le_trans (le_of_eq ?_) hh
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Finset.mem_Ico] at hu
    have hne : (pr (Lv := Lv) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ ℓ ω u).Nonempty := ⟨f, hpres' u hu.1 hu.2⟩
    unfold Aw
    by_cases hu' : u < NE
    · rw [if_pos hu', if_pos hne]
      beta_reduce
      rw [if_pos hu']
      rfl
    · rw [if_neg hu']
      beta_reduce
      rw [if_neg hu']
  have h91 := Pool.P0091.expected_regretT (ι := Cp n NE D) (E := Pool.P0121.TM.E n NE D) (thr0 := thr0 n NE D)
    (θ := θ) (R := R) (K := K) (D := D) (Lv := Lv) (Bt := Bt) (NE := NE) (Lt := Lt) (L := Lm)
    hB hLv2 hLt hT (cu ℓ) (fun j a => cop hNE hD j a istar)
    (fun j a hj _ ha => E_cop hNE hD (by omega) ha istar)
    (fun j a hj _ ha => thr0_cop hNE hD (by omega) ha istar)
    g (fun j a u hj _ ha => by unfold cu bt; rw [arm_cop hNE hD (by omega) ha istar])
    (fun ω u => Aw (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω u) (αL n NE D L η ε) (η / 2) 1
    hα0 (by positivity) hθ hR1 zero_le_one hA
    (fun ω u => by
      have h1 := (Aw_mem (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω u).2
      have h2 : 0 ≤ g u := Nat.cast_nonneg _
      linarith)
    ρ hρ0 hρ hps0 hps.2 hq.1 hq1 (E_mono n NE D) Tmax hC hTm M0 kk hM0 hk hp s0 δs hs S hM0S hρS
  -- (5) the bad runs
  have hfail := fail_le (Lt := Lt) (K := K) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ hps hq ℓ hB hLv hlev hq.2 Tmax hC
    hR1 hTm M0 kk hM0 hk hp (fun a _ r _ => by have := levTh_le Bt Lm r a; omega) s0 δs hs
  -- (6) combine
  set Fb := NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card (Cp n NE D)) q R kk M0
  unfold QMachine.regret
  have hsum : ∑ ω, W ω * Ψ (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε Ns ℓ ω ≤
      ∑ ω, W ω * ∑ u ∈ range NE, (Aw (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω u - g u) +
        ∑ u ∈ range NE, g u + NE * Fb := by
    calc ∑ ω, W ω * Ψ (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε Ns ℓ ω
        ≤ ∑ ω, W ω * (∑ u ∈ range NE, Aw (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω u +
            NE * (if GR ω then 0 else 1)) :=
          Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hΨ ω) (hW0 ω)
      _ = ∑ ω, W ω * ∑ u ∈ range NE, (Aw (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω u - g u) +
            (∑ ω, W ω) * ∑ u ∈ range NE, g u + NE * ∑ ω, W ω * (if GR ω then 0 else 1) := by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.sum_sub_distrib]; ring
      _ ≤ _ := by
          rw [hW1, one_mul]
          have : ∑ ω, W ω * (if GR ω then 0 else 1) ≤ Fb := hfail
          have hNE0 : (0 : ℝ) ≤ NE := Nat.cast_nonneg _
          nlinarith
  have htot := hloss.trans (add_le_add_right hsum 1)
  have hreg : ∑ t ∈ range (NE + 1), (tmach (n := n) (Lv := Lv) (L := L) (M := M) (Lt := Lt) (K := K) (R := R)
      (NE := NE) (D := D) Bt (Pool.P0085.levTh Lm Bt) θ η ε Ns hps hq).toQ.expLoss ℓ t - bestLoss ℓ (NE + 1) ≤
      1 + ∑ ω, W ω * ∑ u ∈ range NE, (Aw (Lv := Lv) (L := L) (R := R) Bt (Pool.P0085.levTh Lm Bt) θ η ε ℓ ω u - g u) +
        NE * Fb := by linarith
  refine hreg.trans ?_
  have := h91
  linarith

end Assembly

end Pool.P0121.TA
