import Pool.P0212.Learner
import Pool.P0203.DSlot
import Pool.P0146.IX
import Pool.P0149.IXValue

/-!
# IX one-sided concentration for the concrete ALG of P0194's process (P0186's `hIX` for copies)
-/

namespace Pool.P0220

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) (ℓ : LossSeq n)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin (withAlg P η L N G γ wE ρr).K → ι → Bool)
  (rc0 : RC (withAlg P η L N G γ wE ρr))

/-- ALG's state, typed as the learner state (P0212's `withAlg` is a plain definition, so `σA` is not reducibly
`AState ι`). -/
noncomputable def sAA (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (s : ℕ) : AState ι :=
  sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ s

/-- ALG's draw, typed on P0194's draw coins of the process with this ALG. -/
noncomputable def drawQ (σ : AState ι) (V : Finset ι) (d : Fin (withAlg P η L N G γ wE ρr).N) : Option ι :=
  drawA η L N σ V d

/-- The observation event of expert `x` in round `s` after the coin prefix `ω'`: an exploitation round whose draw is
`x`. -/
noncomputable def obsX (x : Option ι) (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr))
    (z : RC (withAlg P η L N G γ wE ρr)) : Bool :=
  isE (withAlg P η L N G γ wE ρr) z.1 &&
    decide (drawQ P η L N G γ wE ρr (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 ω') s)
      (active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s) z.2.1 = x)

/-- Copy `x`'s loss in round `s` (predictable: it does not read the coins). -/
noncomputable def lossX (x : ι) (s : ℕ) (_ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) : ℝ :=
  ℓr (withAlg P η L N G γ wE ρr) ℓ s x

/-- Copy `x` is active in round `s` (read from the prefix). -/
noncomputable def gateX (x : ι) (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) : Bool :=
  decide (x ∈ active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s)

theorem lossX_mem (x : ι) (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) :
    0 ≤ lossX P η L N G γ wE ρr ℓ x s ω' ∧ lossX P η L N G γ wE ρr ℓ x s ω' ≤ 1 := by
  unfold lossX ℓr; cases ℓ s ((withAlg P η L N G γ wE ρr).arm x) <;> simp

omit [LinearOrder ι] in
/-- Marginalizing P0194's round-coin weights to exploitation rounds and the draw coin. -/
theorem sum_wR_exploit [LinearOrder ι] (Q : ParD n ι) (hN : 0 < Q.N) (g : Fin Q.N → ℝ) :
    ∑ rc : RC Q, wR Q rc * ((if isE Q rc.1 = true then 1 else 0) * g rc.2.1) =
      Q.wE * ∑ d, (1 / (Q.N : ℝ)) * g d := by
  have hμ : ∑ yB : Q.AB.Y, (Q.AB.μ yB).toReal = 1 := Pool.P0092.sum_toReal_one Q.AB.μ
  have hν : ∑ zB : Q.AB.Z, (Q.AB.ν zB).toReal = 1 := Pool.P0092.sum_toReal_one Q.AB.ν
  simp only [Fintype.sum_prod_type, wR]
  have hinner : ∀ (κ : Kd Q) (d : Fin Q.N),
      ∑ yB : Q.AB.Y, ∑ zB : Q.AB.Z, wK Q κ * (1 / (Q.N : ℝ)) * (Q.AB.μ yB).toReal * (Q.AB.ν zB).toReal *
        ((if isE Q κ = true then 1 else 0) * g d) =
      (wK Q κ * (if isE Q κ = true then 1 else 0)) * ((1 / (Q.N : ℝ)) * g d) := by
    intro κ d
    have e : ∀ yB zB, wK Q κ * (1 / (Q.N : ℝ)) * (Q.AB.μ yB).toReal * (Q.AB.ν zB).toReal *
        ((if isE Q κ = true then 1 else 0) * g d) =
        ((wK Q κ * (if isE Q κ = true then 1 else 0)) * ((1 / (Q.N : ℝ)) * g d)) *
          ((Q.AB.μ yB).toReal * (Q.AB.ν zB).toReal) := fun _ _ => by ring
    simp only [e, ← Finset.mul_sum, hν, hμ, mul_one]
  simp only [hinner, ← Finset.mul_sum, ← Finset.sum_mul]
  congr 1
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [isE, wK]
  rw [Finset.sum_eq_zero (fun r _ => by simp)]
  simp

/-- **The observation mass is `wE·p̃(x)`** (exploitation weight times the rounded draw law), before learner time
`2^L`. -/
theorem obsMass_eq (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N) (x : Option ι)
    (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr))
    (hk : (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 ω') s).k < 2 ^ L) :
    Pool.P0146.obsMass (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
        (obsX P η L N G γ wE ρr ℓ ωs φ rc0 x) s ω' =
      (withAlg P η L N G γ wE ρr).wE *
        ptA η L N (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 ω') s)
        (active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s) x := by
  classical
  have hN0 : 0 < N := hN
  have hdraw := Pool.P0179.prob_draw (N := N) (b := (none : Option ι)) hN0
    (pmarg_nonneg η L (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 ω') s)
      (active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s))
    (pmarg_sum η L _ (active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s) hk) x
  unfold Pool.P0146.obsMass
  simp only [Pool.P0203.nuD_toReal]
  have hrw : ∀ z : RC (withAlg P η L N G γ wE ρr), wR (withAlg P η L N G γ wE ρr) z *
      (if obsX P η L N G γ wE ρr ℓ ωs φ rc0 x s ω' z = true then 1 else 0) =
      wR (withAlg P η L N G γ wE ρr) z * ((if isE (withAlg P η L N G γ wE ρr) z.1 = true then 1 else 0) *
        (fun d : Fin (withAlg P η L N G γ wE ρr).N => if drawQ P η L N G γ wE ρr
          (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 ω') s)
          (active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s) d = x then (1 : ℝ) else 0)
          z.2.1) := by
    intro z
    unfold obsX
    by_cases h1 : isE (withAlg P η L N G γ wE ρr) z.1 = true <;>
      by_cases h2 : drawQ P η L N G γ wE ρr (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 ω') s)
        (active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s) z.2.1 = x <;>
      simp [h1, h2]
  rw [Finset.sum_congr rfl fun z _ => hrw z]
  have key := sum_wR_exploit (withAlg P η L N G γ wE ρr) hN (fun d => if drawQ P η L N G γ wE ρr
    (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 ω') s)
    (active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s) d = x then (1 : ℝ) else 0)
  convert key using 1
  congr 1
  symm
  rw [← Finset.mul_sum, Finset.sum_boole]
  unfold ptA
  rw [← hdraw]
  show 1 / (N : ℝ) * ((Finset.univ.filter fun d : Fin N => drawA η L N _ _ d = x).card : ℝ) = _
  rw [div_eq_mul_inv, one_mul, mul_comm, div_eq_mul_inv]
  congr 3
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, drawA_eq η L N _ _ hk]


theorem floor_div_le (G : ℕ) {v : ℝ} (hv : 0 ≤ v) : ((⌊(G : ℝ) * v⌋₊ : ℕ) : ℝ) / G ≤ v := by
  rcases Nat.eq_zero_or_pos G with hG | hG
  · subst hG; simp [hv]
  · have hG' : (0 : ℝ) < G := by exact_mod_cast hG
    rw [div_le_iff₀ hG']
    have := Nat.floor_le (mul_nonneg hG'.le hv)
    linarith

/-- The observation event on the prefix of a full sequence is the actual round's event. -/
theorem obsX_pre (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (u : ℕ) (x : Option ι) :
    obsX P η L N G γ wE ρr ℓ ωs φ rc0 x u (Pool.P0203.pre _ ω u) (ω u) =
      (isE (withAlg P η L N G γ wE ρr) (ω u).1 &&
        decide (algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u = x)) := by
  have hag := Pool.P0203.extD_pre_agree (withAlg P η L N G γ wE ρr) rc0 ω u
  unfold obsX sAA drawQ
  rw [sA_congr ωs φ u hag, active_congr ωs φ u hag]
  rfl

/-- **Pointwise: the round's IX data are below P0146's IX increment** (with IX parameter `wE·γ`), for rounds before a
horizon `T ≤ 2^L`, when `wE` is P0194's exploitation weight. -/
theorem cuR_le_ixEst (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (T : ℕ) (hTL : T ≤ 2 ^ L)
    (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (x : ι) {u : ℕ} (hu : u < T) :
    cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some x) ≤
      Pool.P0146.ixEst (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (lossX P η L N G γ wE ρr ℓ x)
        (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) u (Pool.P0203.pre _ ω (u + 1)) := by
  have hlast : (Pool.P0203.pre _ ω (u + 1)) (Fin.last u) = ω u := rfl
  have hinit := Pool.P0203.init_pre (withAlg P η L N G γ wE ρr) ω u
  have hk : (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 (Pool.P0203.pre _ ω u)) u).k < 2 ^ L := by
    have hag := Pool.P0203.extD_pre_agree (withAlg P η L N G γ wE ρr) rc0 ω u
    unfold sAA
    rw [sA_congr ωs φ u hag, sA_k]
    have : kE P η L N G γ wE ρr ω u ≤ u := by
      unfold kE; exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  have hmass := obsMass_eq P η L N G γ wE ρr ℓ ωs φ rc0 hL hN (some x) u (Pool.P0203.pre _ ω u) hk
  have hl := lossX_mem P η L N G γ wE ρr ℓ x u (Pool.P0203.pre _ ω u)
  have hix0 : 0 ≤ Pool.P0146.ixEst (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
      (lossX P η L N G γ wE ρr ℓ x) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) u
      (Pool.P0203.pre _ ω (u + 1)) := by
    unfold Pool.P0146.ixEst
    rw [hinit]
    refine mul_nonneg hl.1 ?_
    split_ifs
    · rw [hmass]
      have h1 : (withAlg P η L N G γ wE ρr).wE = wE := hwE
      rw [h1]
      have := Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι))
        (p := pmarg η L (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 (Pool.P0203.pre _ ω u)) u)
          (active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 (Pool.P0203.pre _ ω u)) ωs φ u)) (some x)
      unfold ptA
      positivity
    · exact le_rfl
  by_cases hg : gE P η L N G γ wE ρr ω u = true
  · by_cases hch : algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u = some x
    · rw [cuR_eq P η L N G γ wE ρr ℓ ω ωs φ T hu hg]
      unfold Pool.P0146.ixEst
      rw [hinit, hlast, obsX_pre]
      have hgE : isE (withAlg P η L N G γ wE ρr) (ω u).1 = true := hg
      rw [hgE, hch]
      simp only [decide_true, Bool.and_self, if_true]
      rw [hmass]
      have hag := Pool.P0203.extD_pre_agree (withAlg P η L N G γ wE ρr) rc0 ω u
      have hs : sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 (Pool.P0203.pre _ ω u)) u =
          sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u := sA_congr ωs φ u hag
      have ha : active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 (Pool.P0203.pre _ ω u)) ωs φ u =
          active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u := active_congr ωs φ u hag
      rw [hs, ha]
      unfold ixA
      rw [if_pos rfl]
      have h1 : (withAlg P η L N G γ wE ρr).wE = wE := hwE
      rw [h1]
      have hb : ((ℓ u (armOf (withAlg P η L N G γ wE ρr) ℓ ω u (some x))).toNat : ℝ) =
          lossX P η L N G γ wE ρr ℓ x u (Pool.P0203.pre _ ω u) := rfl
      rw [hb]
      set p := ptA η L N (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
        (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) (some x)
      have hp0 : 0 ≤ p := Pool.P0179.pt_nonneg _
      have hden : wE * p + wE * γ = wE * (p + γ) := by ring
      rw [hden, mul_one_div]
      exact floor_div_le G (div_nonneg hl.1 (by positivity))
    · have hz : cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some x) = 0 := by
        rw [cuR_eq P η L N G γ wE ρr ℓ ω ωs φ T hu hg]
        unfold ixA
        rw [if_neg (Ne.symm hch)]
      rw [hz]; exact hix0
  · have hz : cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some x) = 0 := by
      unfold cuR; rw [if_neg hg]
    rw [hz]; exact hix0


omit [Fintype ι] in
/-- Running sums of gated increments on the prefix of a full sequence. -/
theorem runSum_pre_gen [Fintype ι] (Q : ParD n ι) (F : (s : ℕ) → (Fin (s + 1) → RC Q) → ℝ)
    (gate : (s : ℕ) → (Fin s → RC Q) → Bool) (ω : ℕ → RC Q) (a b : ℕ) : ∀ T,
    Pool.P0092.runSum (Pool.P0139.gD F gate a b) T (Pool.P0203.pre Q ω T) =
      ∑ u ∈ Finset.range T, if a ≤ u ∧ u < b ∧ gate u (Pool.P0203.pre Q ω u) = true then
        F u (Pool.P0203.pre Q ω (u + 1)) else 0
  | 0 => by simp [Pool.P0092.runSum]
  | T + 1 => by
    simp only [Pool.P0092.runSum, Finset.sum_range_succ]
    rw [Pool.P0203.init_pre, runSum_pre_gen Q F gate ω a b T]
    congr 1

/-- **IX one-sided bound on the actual run** (P0186's `hIX` shape for copies): if the length-`T` prefix of `ω` is in
P0146's good event for copy `x`, then on every `[a, b) ⊆ [0, T)` the IX data of `x` over its active rounds exceed its
losses over those rounds by less than `Lc/(2·wE·γ)`. -/
theorem ix_run (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (T : ℕ) (hTL : T ≤ 2 ^ L)
    (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (x : ι) {Lc : ℝ}
    (hgood : Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (lossX P η L N G γ wE ρr ℓ x)
      (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T)) (a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T) :
    ∑ u ∈ Finset.Ico a b, (if x ∈ active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u then
        cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some x) else 0) <
      ∑ u ∈ Finset.Ico a b, (if x ∈ active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u then
        ℓr (withAlg P η L N G γ wE ρr) ℓ u x else 0) + Lc / (2 * (wE * γ)) := by
  classical
  have h := Pool.P0146.ixEst_le_of_good _ _ _ _ _ _ hgood hab hbT
  rw [runSum_pre_gen, runSum_pre_gen] at h
  have hgate : ∀ u, gateX P η L N G γ wE ρr ℓ ωs φ rc0 x u (Pool.P0203.pre _ ω u) =
      decide (x ∈ active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) := by
    intro u
    unfold gateX
    rw [active_congr ωs φ u (Pool.P0203.extD_pre_agree (withAlg P η L N G γ wE ρr) rc0 ω u)]
  have hconv : ∀ (F : ℕ → ℝ), (∑ u ∈ Finset.range T, if a ≤ u ∧ u < b ∧
      gateX P η L N G γ wE ρr ℓ ωs φ rc0 x u (Pool.P0203.pre _ ω u) = true then F u else 0) =
      ∑ u ∈ Finset.Ico a b, (if x ∈ active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u then F u else 0) := by
    intro F
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le a) (show a ≤ T by omega),
      ← Finset.sum_Ico_consecutive _ hab hbT]
    rw [Finset.sum_eq_zero (fun u hu => by simp at hu; simp [show ¬ a ≤ u by omega]),
      Finset.sum_eq_zero (s := Finset.Ico b T) (fun u hu => by simp at hu; simp [show ¬ u < b by omega])]
    simp only [zero_add, add_zero]
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Finset.mem_Ico] at hu
    rw [hgate]
    by_cases hx : x ∈ active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u <;> simp [hx, hu.1, hu.2]
  rw [hconv (fun u => Pool.P0146.ixEst _ _ _ _ u (Pool.P0203.pre _ ω (u + 1))),
    hconv (fun u => lossX P η L N G γ wE ρr ℓ x u (Fin.init (Pool.P0203.pre _ ω (u + 1))))] at h
  refine lt_of_le_of_lt (Finset.sum_le_sum fun u hu => ?_) h
  simp only [Finset.mem_Ico] at hu
  split_ifs
  · exact cuR_le_ixEst P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 hwE T hTL ω x (by omega)
  · exact le_rfl


open Classical in
/-- **The IX good events of all copies fail with probability `≤ |ι|·(T+1)²·e^{−Lc}`** over P0194's round coins. -/
theorem prob_not_ixGood_all (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (Lc : ℝ) (T : ℕ) :
    (∑ ω' : Fin T → RC (withAlg P η L N G γ wE ρr), Pool.P0092.wgt (Pool.P0203.nuD _ hL hN) ω' *
      if ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (lossX P η L N G γ wE ρr ℓ x)
        (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T ω'
      then (0 : ℝ) else 1) ≤ Fintype.card ι * (((T : ℝ) + 1) ^ 2 * Real.exp (-Lc)) := by
  have hγ' : 0 < wE * γ := mul_pos hwE0 hγ
  have hpt : ∀ ω' : Fin T → RC (withAlg P η L N G γ wE ρr),
      (if ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (lossX P η L N G γ wE ρr ℓ x)
        (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T ω'
      then (0 : ℝ) else 1) ≤ ∑ x, (if Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
        (lossX P η L N G γ wE ρr ℓ x) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ)
        (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T ω' then (0 : ℝ) else 1) := by
    intro ω'
    split_ifs with h
    · exact Finset.sum_nonneg fun x _ => by split_ifs <;> norm_num
    · push_neg at h
      obtain ⟨x, hx⟩ := h
      calc (1 : ℝ) = if Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
            (lossX P η L N G γ wE ρr ℓ x) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ)
            (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T ω' then (0 : ℝ) else 1 := by rw [if_neg hx]
        _ ≤ _ := Finset.single_le_sum (f := fun x => if Pool.P0146.IXGood
            (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (lossX P η L N G γ wE ρr ℓ x)
            (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T ω'
            then (0 : ℝ) else 1) (fun y _ => by split_ifs <;> norm_num) (Finset.mem_univ x)
  calc _ ≤ ∑ ω' : Fin T → RC (withAlg P η L N G γ wE ρr), Pool.P0092.wgt (Pool.P0203.nuD _ hL hN) ω' *
        ∑ x, (if Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
        (lossX P η L N G γ wE ρr ℓ x) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ)
        (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T ω' then (0 : ℝ) else 1) :=
        Finset.sum_le_sum fun ω' _ => mul_le_mul_of_nonneg_left (hpt ω') (Pool.P0092.wgt_nonneg _ ω')
    _ = ∑ x : ι, ∑ ω' : Fin T → RC (withAlg P η L N G γ wE ρr), Pool.P0092.wgt (Pool.P0203.nuD _ hL hN) ω' *
        (if Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
        (lossX P η L N G γ wE ρr ℓ x) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ)
        (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T ω' then (0 : ℝ) else 1) := by
        simp only [Finset.mul_sum]; rw [Finset.sum_comm]
    _ ≤ ∑ _x : ι, ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) := Finset.sum_le_sum fun x _ =>
        Pool.P0146.prob_not_ixGood _ _ _ hγ' (fun s ω' => (lossX_mem P η L N G γ wE ρr ℓ x s ω').1)
          (fun s ω' => (lossX_mem P η L N G γ wE ρr ℓ x s ω').2) _ Lc T
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]


/-! ### The meta-arm (P0149: random observed value against BASE's policy loss) -/

omit [LinearOrder ι] in
/-- Marginalization with a factor on BASE's action coin. -/
theorem sum_wR_exploit_factor [LinearOrder ι] (Q : ParD n ι) (g : Fin Q.N → ℝ) (h : Q.AB.Y → ℝ) :
    ∑ rc : RC Q, wR Q rc * ((if isE Q rc.1 = true then 1 else 0) * g rc.2.1 * h rc.2.2.1) =
      (Q.wE * ∑ d, (1 / (Q.N : ℝ)) * g d) * ∑ yB, (Q.AB.μ yB).toReal * h yB := by
  have hν : ∑ zB : Q.AB.Z, (Q.AB.ν zB).toReal = 1 := Pool.P0092.sum_toReal_one Q.AB.ν
  simp only [Fintype.sum_prod_type, wR]
  have hinner : ∀ (κ : Kd Q) (d : Fin Q.N) (yB : Q.AB.Y),
      ∑ zB : Q.AB.Z, wK Q κ * (1 / (Q.N : ℝ)) * (Q.AB.μ yB).toReal * (Q.AB.ν zB).toReal *
        ((if isE Q κ = true then 1 else 0) * g d * h yB) =
      (wK Q κ * (if isE Q κ = true then 1 else 0)) * ((1 / (Q.N : ℝ)) * g d) * ((Q.AB.μ yB).toReal * h yB) := by
    intro κ d yB
    have e : ∀ zB, wK Q κ * (1 / (Q.N : ℝ)) * (Q.AB.μ yB).toReal * (Q.AB.ν zB).toReal *
        ((if isE Q κ = true then 1 else 0) * g d * h yB) =
        ((wK Q κ * (if isE Q κ = true then 1 else 0)) * ((1 / (Q.N : ℝ)) * g d) * ((Q.AB.μ yB).toReal * h yB)) *
          (Q.AB.ν zB).toReal := fun _ => by ring
    simp only [e, ← Finset.mul_sum, hν, mul_one]
  simp only [hinner, ← Finset.mul_sum, ← Finset.sum_mul]
  congr 2
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [isE, wK]
  rw [Finset.sum_eq_zero (fun r _ => by simp)]
  simp

/-- The meta-arm's observed value: the loss of BASE's action drawn with the round's coin. -/
noncomputable def YB (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) (z : RC (withAlg P η L N G γ wE ρr)) :
    ℝ :=
  ((ℓ s ((withAlg P η L N G γ wE ρr).AB.act 0 (sB (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') s) z.2.2.1)).toNat : ℝ)

/-- BASE's policy loss in round `s` (predictable). -/
noncomputable def bPolX (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) : ℝ :=
  bPol (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') s

/-- The one-sided mean condition of P0149 holds with equality: the draw coin is independent of the selection. -/
theorem mean_meta (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N) (s : ℕ)
    (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) :
    ∑ z, (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
        (if obsX P η L N G γ wE ρr ℓ ωs φ rc0 none s ω' z then YB P η L N G γ wE ρr ℓ rc0 s ω' z else 0) ≤
      bPolX P η L N G γ wE ρr ℓ rc0 s ω' *
        Pool.P0146.obsMass (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
          (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none) s ω' := by
  classical
  set gd : Fin (withAlg P η L N G γ wE ρr).N → ℝ := fun d => if drawQ P η L N G γ wE ρr
    (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 ω') s)
    (active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') ωs φ s) d = none then (1 : ℝ) else 0
  have hobs : ∀ z, obsX P η L N G γ wE ρr ℓ ωs φ rc0 none s ω' z =
      (isE (withAlg P η L N G γ wE ρr) z.1 && decide (gd z.2.1 = 1)) := by
    intro z; unfold obsX; simp only [gd]; split_ifs with h <;> simp [h]
  have hL1 : ∀ z : RC (withAlg P η L N G γ wE ρr),
      (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
        (if obsX P η L N G γ wE ρr ℓ ωs φ rc0 none s ω' z then YB P η L N G γ wE ρr ℓ rc0 s ω' z else 0) =
      wR (withAlg P η L N G γ wE ρr) z * ((if isE (withAlg P η L N G γ wE ρr) z.1 = true then 1 else 0) * gd z.2.1 *
        (fun yB => ((ℓ s ((withAlg P η L N G γ wE ρr).AB.act 0 (sB (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') s) yB)).toNat : ℝ))
          z.2.2.1) := by
    intro z
    rw [Pool.P0203.nuD_toReal, hobs]
    unfold YB
    by_cases h1 : isE (withAlg P η L N G γ wE ρr) z.1 = true <;> by_cases h2 : gd z.2.1 = 1
    · simp [h1, h2]
    · have : gd z.2.1 = 0 := by simp only [gd] at h2 ⊢; split_ifs at h2 ⊢ <;> simp_all
      simp [h1, h2, this]
    · simp [h1]
    · simp [h1]
  have hR1 : ∀ z : RC (withAlg P η L N G γ wE ρr),
      (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN z).toReal *
        (if obsX P η L N G γ wE ρr ℓ ωs φ rc0 none s ω' z then 1 else 0) =
      wR (withAlg P η L N G γ wE ρr) z * ((if isE (withAlg P η L N G γ wE ρr) z.1 = true then 1 else 0) * gd z.2.1 *
        (fun _ : (withAlg P η L N G γ wE ρr).AB.Y => (1 : ℝ)) z.2.2.1) := by
    intro z
    rw [Pool.P0203.nuD_toReal, hobs]
    by_cases h1 : isE (withAlg P η L N G γ wE ρr) z.1 = true <;> by_cases h2 : gd z.2.1 = 1
    · simp [h1, h2]
    · have : gd z.2.1 = 0 := by simp only [gd] at h2 ⊢; split_ifs at h2 ⊢ <;> simp_all
      simp [h1, h2, this]
    · simp [h1]
    · simp [h1]
  rw [Finset.sum_congr rfl fun z _ => hL1 z]
  unfold Pool.P0146.obsMass
  rw [Finset.sum_congr rfl fun z _ => hR1 z]
  have k1 := sum_wR_exploit_factor (withAlg P η L N G γ wE ρr) gd
    (fun yB => ((ℓ s ((withAlg P η L N G γ wE ρr).AB.act 0
      (sB (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') s) yB)).toNat : ℝ))
  have k2 := sum_wR_exploit_factor (withAlg P η L N G γ wE ρr) gd (fun _ => (1 : ℝ))
  refine le_of_eq ?_
  refine (Eq.trans (by convert k1 using 1) ?_)
  refine (Eq.trans ?_ (congrArg _ (by convert k2.symm using 1)))
  have hμ : ∑ yB : (withAlg P η L N G γ wE ρr).AB.Y, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal * (1 : ℝ) = 1 := by
    simp only [mul_one]; exact Pool.P0092.sum_toReal_one (withAlg P η L N G γ wE ρr).AB.μ
  have hb : ∑ yB : (withAlg P η L N G γ wE ρr).AB.Y, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal *
      ((ℓ s ((withAlg P η L N G γ wE ρr).AB.act 0 (sB (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') s) yB)).toNat : ℝ) =
      bPolX P η L N G γ wE ρr ℓ rc0 s ω' := rfl
  erw [hμ, hb]
  rw [mul_one, mul_comm]



theorem YB_mem (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) (z : RC (withAlg P η L N G γ wE ρr)) :
    0 ≤ YB P η L N G γ wE ρr ℓ rc0 s ω' z ∧ YB P η L N G γ wE ρr ℓ rc0 s ω' z ≤ 1 := by
  unfold YB; constructor
  · positivity
  · cases ℓ s ((withAlg P η L N G γ wE ρr).AB.act 0
      (sB (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 ω') s) z.2.2.1) <;> simp

theorem bPolX_nonneg (s : ℕ) (ω' : Fin s → RC (withAlg P η L N G γ wE ρr)) :
    0 ≤ bPolX P η L N G γ wE ρr ℓ rc0 s ω' :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (by positivity)

/-- **Pointwise, meta-arm: the round's IX data are below P0149's IX increment.** -/
theorem cuR_le_ixEstV (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (T : ℕ) (hTL : T ≤ 2 ^ L)
    (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) {u : ℕ} (hu : u < T) :
    cuR P η L N G γ wE ρr ℓ ω ωs φ T u none ≤
      Pool.P0149.ixEstV (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (YB P η L N G γ wE ρr ℓ rc0)
        (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none) (wE * γ) u (Pool.P0203.pre _ ω (u + 1)) := by
  have hlast : (Pool.P0203.pre _ ω (u + 1)) (Fin.last u) = ω u := rfl
  have hinit := Pool.P0203.init_pre (withAlg P η L N G γ wE ρr) ω u
  have hag := Pool.P0203.extD_pre_agree (withAlg P η L N G γ wE ρr) rc0 ω u
  have hk : (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 (Pool.P0203.pre _ ω u)) u).k < 2 ^ L := by
    unfold sAA
    rw [sA_congr ωs φ u hag, sA_k]
    have : kE P η L N G γ wE ρr ω u ≤ u := by
      unfold kE; exact (Finset.card_filter_le _ _).trans (by simp)
    omega
  have hmass := obsMass_eq P η L N G γ wE ρr ℓ ωs φ rc0 hL hN none u (Pool.P0203.pre _ ω u) hk
  have h1 : (withAlg P η L N G γ wE ρr).wE = wE := hwE
  have hix0 : 0 ≤ Pool.P0149.ixEstV (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
      (YB P η L N G γ wE ρr ℓ rc0) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none) (wE * γ) u
      (Pool.P0203.pre _ ω (u + 1)) := by
    unfold Pool.P0149.ixEstV
    split_ifs
    · rw [hinit, hmass, h1]
      have := Pool.P0179.pt_nonneg (N := N) (b := (none : Option ι))
        (p := pmarg η L (sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 (Pool.P0203.pre _ ω u)) u)
          (active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 (Pool.P0203.pre _ ω u)) ωs φ u)) none
      have hY := (YB_mem P η L N G γ wE ρr ℓ rc0 u (Pool.P0203.pre _ ω u) (ω u)).1
      unfold ptA
      rw [hlast]
      positivity
    · exact le_rfl
  by_cases hg : gE P η L N G γ wE ρr ω u = true
  · by_cases hch : algCh (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u = none
    · rw [cuR_eq P η L N G γ wE ρr ℓ ω ωs φ T hu hg]
      unfold Pool.P0149.ixEstV
      rw [hinit, hlast, obsX_pre]
      have hgE : isE (withAlg P η L N G γ wE ρr) (ω u).1 = true := hg
      rw [hgE, hch]
      simp only [decide_true, Bool.and_self, if_true]
      rw [hmass, h1]
      have hs : sAA P η L N G γ wE ρr ℓ ωs φ (Pool.P0203.extD _ rc0 (Pool.P0203.pre _ ω u)) u =
          sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u := sA_congr ωs φ u hag
      have ha : active (withAlg P η L N G γ wE ρr) ℓ (Pool.P0203.extD _ rc0 (Pool.P0203.pre _ ω u)) ωs φ u =
          active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u := active_congr ωs φ u hag
      rw [hs, ha]
      unfold ixA
      rw [if_pos rfl]
      have hY : ((ℓ u (armOf (withAlg P η L N G γ wE ρr) ℓ ω u none)).toNat : ℝ) =
          YB P η L N G γ wE ρr ℓ rc0 u (Pool.P0203.pre _ ω u) (ω u) := by
        unfold YB armOf bAct
        rw [sB_congr u hag]
      rw [hY]
      set p := ptA η L N (sA (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u)
        (active (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u) none
      have hp0 : 0 ≤ p := Pool.P0179.pt_nonneg _
      have hY0 := (YB_mem P η L N G γ wE ρr ℓ rc0 u (Pool.P0203.pre _ ω u) (ω u)).1
      have hden : wE * p + wE * γ = wE * (p + γ) := by ring
      rw [hden]
      exact floor_div_le G (div_nonneg hY0 (by positivity))
    · have hz : cuR P η L N G γ wE ρr ℓ ω ωs φ T u none = 0 := by
        rw [cuR_eq P η L N G γ wE ρr ℓ ω ωs φ T hu hg]
        unfold ixA
        rw [if_neg (Ne.symm hch)]
      rw [hz]; exact hix0
  · have hz : cuR P η L N G γ wE ρr ℓ ω ωs φ T u none = 0 := by
      unfold cuR; rw [if_neg hg]
    rw [hz]; exact hix0


/-- BASE's policy loss read on the prefix of a full sequence is the run's. -/
theorem bPolX_pre (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (u : ℕ) :
    bPolX P η L N G γ wE ρr ℓ rc0 u (Pool.P0203.pre _ ω u) = bPol (withAlg P η L N G γ wE ρr) ℓ ω u := by
  unfold bPolX bPol
  rw [sB_congr u (Pool.P0203.extD_pre_agree (withAlg P η L N G γ wE ρr) rc0 ω u)]

/-- **IX one-sided bound for the meta-arm on the actual run**: on P0149's good event, on every `[a, b) ⊆ [0, T)`, the
meta-arm's IX data exceed BASE's policy losses by less than `Lc/(2·wE·γ)`. This is P0186's `ActHyp.hIXB` only under
the instantiation `drawn := bPol` (P0186 bounds the meta-arm data by `drawn`): then P0186's `hDr` holds with `WD = 0`,
and its `hfake` asks `bPol ≤` the fake data of retired copies (e.g. `zRun`'s fake `1` per unit). That instantiation is
not stated as a separate declaration here. -/
theorem ix_run_meta (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (T : ℕ) (hTL : T ≤ 2 ^ L)
    (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) {Lc : ℝ}
    (hgood : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
      (YB P η L N G γ wE ρr ℓ rc0) (bPolX P η L N G γ wE ρr ℓ rc0) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (a b : ℕ) (hab : a ≤ b) (hbT : b ≤ T) :
    ∑ u ∈ Finset.Ico a b, cuR P η L N G γ wE ρr ℓ ω ωs φ T u none <
      ∑ u ∈ Finset.Ico a b, bPol (withAlg P η L N G γ wE ρr) ℓ ω u + Lc / (2 * (wE * γ)) := by
  classical
  have h := Pool.P0149.ixEstV_le_of_good _ _ _ _ _ _ _ hgood hab hbT
  rw [runSum_pre_gen, runSum_pre_gen] at h
  have hconv : ∀ (F : ℕ → ℝ), (∑ u ∈ Finset.range T, if a ≤ u ∧ u < b ∧
      (fun (_ : ℕ) (_ : Fin _ → RC (withAlg P η L N G γ wE ρr)) => true) u (Pool.P0203.pre _ ω u) = true then
        F u else 0) = ∑ u ∈ Finset.Ico a b, F u := by
    intro F
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le a) (show a ≤ T by omega),
      ← Finset.sum_Ico_consecutive _ hab hbT]
    rw [Finset.sum_eq_zero (fun u hu => by simp at hu; simp [show ¬ a ≤ u by omega]),
      Finset.sum_eq_zero (s := Finset.Ico b T) (fun u hu => by simp at hu; simp [show ¬ u < b by omega])]
    simp only [zero_add, add_zero]
    refine Finset.sum_congr rfl fun u hu => ?_
    simp only [Finset.mem_Ico] at hu
    simp [hu.1, hu.2]
  rw [hconv (fun u => Pool.P0149.ixEstV _ _ _ _ u (Pool.P0203.pre _ ω (u + 1))),
    hconv (fun u => bPolX P η L N G γ wE ρr ℓ rc0 u (Fin.init (Pool.P0203.pre _ ω (u + 1))))] at h
  simp only [Pool.P0203.init_pre, bPolX_pre] at h
  refine lt_of_le_of_lt (Finset.sum_le_sum fun u hu => ?_) h
  simp only [Finset.mem_Ico] at hu
  exact cuR_le_ixEstV P η L N G γ wE ρr ℓ ωs φ rc0 hL hN hγ hwE0 hwE T hTL ω (by omega)

open Classical in
/-- P0149's good event of the meta-arm fails with probability `≤ (T+1)²·e^{−Lc}`. -/
theorem prob_not_ixGood_meta (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N)
    (hγ : 0 < γ) (hwE0 : 0 < wE) (Lc : ℝ) (T : ℕ) :
    (∑ ω' : Fin T → RC (withAlg P η L N G γ wE ρr), Pool.P0092.wgt (Pool.P0203.nuD _ hL hN) ω' *
      if Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
        (YB P η L N G γ wE ρr ℓ rc0) (bPolX P η L N G γ wE ρr ℓ rc0) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none)
        (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T ω' then (0 : ℝ) else 1) ≤
      ((T : ℝ) + 1) ^ 2 * Real.exp (-Lc) :=
  Pool.P0149.prob_not_ixGoodV _ _ _ _ (mul_pos hwE0 hγ) (fun s ω' z => (YB_mem P η L N G γ wE ρr ℓ rc0 s ω' z).1)
    (fun s ω' z => (YB_mem P η L N G γ wE ρr ℓ rc0 s ω' z).2) (bPolX_nonneg P η L N G γ wE ρr ℓ rc0)
    (mean_meta P η L N G γ wE ρr ℓ ωs φ rc0 hL hN) _ Lc T

end Pool.P0220
