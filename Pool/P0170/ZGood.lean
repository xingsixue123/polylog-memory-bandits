import Pool.P0164.ZCount
import Pool.P0126.FOExp

/-!
# The actual retirement run is good with high probability, and the closed-form bad-point count

* `goodAZ_of_goodRunT`: on P0073's `GoodRunT` for the realized data of P0156's retirement process, the actual run is
  P0164's `GoodAZ` with `S = s0 + D·Lv·S' + 1`, if `s ≥ D·((s0 + D·Lv·S') + (Lv−1)·S') + D·s0 + 1` (P0126's
  `goodA_of_goodRunT`, via P0156's `gRun_pools_eq`).
* `prob_notGoodAZ_le`: for every fixed slot sequence, `P(¬GoodAZ) ≤ NE·D·δs + NE·D·(Lt+1)·K·delta` over P0091's coin
  law (P0156's `prob_not_goodRunT_gen`, P0091's `wtv_uncurryT`).
* **`count_bad_Z_closed`**: P0164's `count_bad_Z` with P0091's `piS_geT` and `prob_notGoodAZ_le`:
  `E[#bad] ≤ D·Lv·(s0 + D·Lv·S' + 1)/(ps(1−q)^{K·D(2Ld+NE/2^Ld+1)}) + D·NE·(NE·D·δs + NE·D·(Lt+1)·K·delta)`.
-/

namespace Pool.P0170

open Finset Pool.P0095 Pool.P0065 Pool.P0082 Pool.P0156 Pool.P0164 Pool.P0105 Pool.P0048

section NotGood

attribute [local instance] coinFintype

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) {NE Lt : ℕ}

theorem goodAZ_of_goodRunT (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (ω2 : Pool.P0073.SlotT NE D Lt K → ι → Bool) (y : ℕ → Fin s) (s0 : ℕ) (M0 ρ : ℝ) (S' : ℕ) (hρ : 0 ≤ ρ)
    (hg : Pool.P0073.GoodRunT E thr0
      (gChat E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occSort s) y rh) ∅ (Pool.P0073.ωsOfT E K D ω2)
        (Pool.P0073.φOfT K D ω2))
      θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) NE s0 M0 ρ)
    (hM0S : M0 ≤ S') (hρS : ρ * ((S' : ℝ) + (s0 + D * Lv * S')) ≤ S')
    (hs : (D : ℝ) * ((s0 + D * Lv * S') + (Lv - 1 : ℕ) * S') + D * s0 + 1 ≤ s) :
    GoodAZ E thr0 θ R K D Lv Bt lev s L rh NE (s0 + D * Lv * S' + 1) (Pool.P0073.ωsOfT E K D ω2)
      (Pool.P0073.φOfT K D ω2) y := by
  have hcard := fun a ha => Pool.P0073.tpools_card_le hB hLv hlev _ _ NE s0 M0 ρ S' hρ hg hM0S (Nat.cast_nonneg _) hρS a ha
  refine ⟨fun u hu => ?_, fun r hr ℓ hℓ => ?_⟩
  · have hpe := gRun_pools_eq E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occSort s) y rh) ∅ (Pool.P0073.ωsOfT E K D ω2)
      (Pool.P0073.φOfT K D ω2) u
    have h := Pool.P0109.members_startPools_card_le E thr0 D Lv Bt (Pool.P0073.ωsOfT E K D ω2) u _ s0 S'
      (s0 + D * Lv * S') (hcard u hu.le).1 (hcard u hu.le).2.1 (fun r hr hd => hg.1 u hu r hr hd)
    rw [← hpe] at h
    have : ((VstZ E thr0 D Lv Bt (Pool.P0073.ωsOfT E K D ω2) u
        (zRun E thr0 θ R K D Lv Bt lev s L (occSort s) y rh (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2)
          u)).card : ℝ) + 1 ≤ s := by
      unfold VstZ; linarith
    exact_mod_cast this
  · have hpe := gRun_pools_eq E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occSort s) y rh) ∅ (Pool.P0073.ωsOfT E K D ω2)
      (Pool.P0073.φOfT K D ω2) NE
    show ((zRun E thr0 θ R K D Lv Bt lev s L (occSort s) y rh (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2)
      NE).pools r ℓ).card + 1 ≤ s0 + D * Lv * S' + 1
    rw [hpe]
    obtain ⟨h1, h2, -⟩ := hcard NE le_rfl
    have hDLv : (S' : ℝ) ≤ D * Lv * S' := by
      have : (1 : ℝ) ≤ D * Lv := by
        have : (1 : ℕ) ≤ D * Lv := Nat.one_le_iff_ne_zero.2 (by have := hB.hD; positivity)
        exact_mod_cast this
      nlinarith [Nat.cast_nonneg (α := ℝ) S']
    rcases Nat.eq_zero_or_pos ℓ with hl | hl
    · subst hl
      have := h2 r
      have : ((tpools E thr0 (gChat E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occSort s) y rh) ∅
          (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2)) θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2)
          (Pool.P0073.φOfT K D ω2) NE r 0).card : ℝ) + 1 ≤ ((s0 + D * Lv * S' + 1 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · have := h1 r ℓ (by omega)
      have : ((tpools E thr0 (gChat E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occSort s) y rh) ∅
          (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2)) θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2)
          (Pool.P0073.φOfT K D ω2) NE r ℓ).card : ℝ) + 1 ≤ ((s0 + D * Lv * S' + 1 : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast this

open Classical in
/-- **The actual retirement run is good except with P0109's probability.** -/
theorem prob_notGoodAZ_le {ps q : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hE : Monotone E) (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (hs1 : 1 ≤ s) (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1)
    (hR : 1 ≤ R) (hT : (s : ℝ) * NE ≤ 2 ^ (R - 1) * θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * R ≤ M0)
    (hk : 4 * R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * R))
    (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S') (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * ((S' : ℝ) + (s0 + D * Lv * S')) ≤ S')
    (hsl : (D : ℝ) * ((s0 + D * Lv * S') + (Lv - 1 : ℕ) * S') + D * s0 + 1 ≤ s) (y : ℕ → Fin s) :
    ∑ ω, Pool.P0048.wtv (Pool.P0091.pC (NE := NE) (D := D) (Lt := Lt) (K := K) ps q) ω *
      (if GoodAZ E thr0 θ R K D Lv Bt lev s L rh NE (s0 + D * Lv * S' + 1) (ωsC E NE D Lt K ω) (φC NE D Lt K ω) y
        then 0 else 1) ≤
      NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0 := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hρ0 : 0 ≤ (1 - 1 / (4 * R : ℝ)) ^ K := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one (by positivity)]
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  rw [← (Equiv.curry (Pool.P0073.SlotT NE D Lt K) ι Bool).symm.sum_comp]
  refine le_trans (Finset.sum_le_sum fun ω2 _ => ?_) (prob_not_goodRunT_gen E thr0 θ R K D Lv Bt lev
    (zUpd D Lv s L (occSort s) y rh) ∅ M0 kk hps hq0 hq1 hE hB.hD hLv hlev (Nat.cast_nonneg s)
    (fun ωs φ a x => zInc_bounds E thr0 θ R K D Lv Bt lev s L (occSort s) y rh ωs φ hs1 hL0 hL1 a x)
    hR hT hM0 hk hp hlevLt s0 δs hs)
  simp only [Equiv.curry_symm_apply]
  rw [Pool.P0091.wtv_uncurryT ω2]
  have hw0 : 0 ≤ Pool.P0046.bw2 (Pool.P0073.qOfT K D ps q) ω2 :=
    Finset.prod_nonneg fun s _ => Finset.prod_nonneg fun c _ => by
      cases s <;> split_ifs <;> simp [Pool.P0073.qOfT] <;> linarith [hps.1, hps.2]
  refine mul_le_mul_of_nonneg_left ?_ hw0
  have hωs : ωsC E NE D Lt K (Function.uncurry ω2) = Pool.P0073.ωsOfT E K D ω2 := rfl
  have hφ : φC NE D Lt K (Function.uncurry ω2) = Pool.P0073.φOfT K D ω2 := rfl
  rw [hωs, hφ]
  by_cases hg : Pool.P0073.GoodRunT E thr0 (gCof E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occSort s) y rh) ∅ ω2)
      θ R K D Lv Bt lev (Pool.P0073.ωsOfT E K D ω2) (Pool.P0073.φOfT K D ω2) NE s0 M0 ((1 - 1 / (4 * R : ℝ)) ^ K)
  · rw [if_pos (goodAZ_of_goodRunT E thr0 θ R K D Lv Bt lev s L rh hB hLv hlev ω2 y s0 M0 _ S' hρ0 hg hM0S hρS hsl)]
    split_ifs; norm_num
  · rw [if_neg hg]; split_ifs <;> norm_num

end NotGood


section Closed

attribute [local instance] coinFintype

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (s : ℕ) (L : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) {NE Lt : ℕ}

open Classical in
/-- **Bad walk points of the retirement process, closed form** (S2's bad-point half with its not-good probability):
with P0085's schedule `levTh Ld Bt`, P0091's coin law `pC ps q`, and `S = s0 + D·Lv·S' + 1`,
`E[#bad] ≤ D·Lv·S/(ps(1−q)^{K·D(2Ld+NE/2^Ld+1)}) + D·NE·(NE·D·δs + NE·D·(Lt+1)·K·delta)`. -/
theorem count_bad_Z_closed [NeZero s] (hB : BtHyp D Bt) {Ld : ℕ} (hLv2 : Ld + 2 ≤ Lv) (hLt : Ld ≤ Lt)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    {ps q : ℝ} (hps0 : 0 < ps) (hps1 : ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hEm : Monotone E) (hs1 : 1 ≤ s) (hL0 : ∀ u x, 0 ≤ L u x) (hL1 : ∀ u x, L u x ≤ 1)
    (hR : 1 ≤ R) (hT : (s : ℝ) * NE ≤ 2 ^ (R - 1) * θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * R ≤ M0)
    (hk : 4 * R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S') (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * ((S' : ℝ) + (s0 + D * Lv * S')) ≤ S')
    (hsl : (D : ℝ) * ((s0 + D * Lv * S') + (Lv - 1 : ℕ) * S') + D * s0 + 1 ≤ s) :
    ∑ ω, Pool.P0048.wtv (Pool.P0091.pC (NE := NE) (D := D) (Lt := Lt) (K := K) ps q) ω *
      ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt)
          (zUpd D Lv s L (occLast s (cstar ja.1 ja.2)) (extY s yy) rh) ∅
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ)
      ≤ (D * Lv * (s0 + D * Lv * S' + 1) : ℝ) / (ps * (1 - q) ^ (K * (D * (2 * Ld + NE / 2 ^ Ld + 1)))) +
        D * NE * (NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0) := by
  have hD := hB.hD
  have hLv : 0 < Lv := by omega
  have hlev : ∀ r a, Pool.P0085.levTh Ld Bt r a + 1 < Lv := fun r a => by
    have := Pool.P0062.levPR_le Ld ((a + 1) / Bt r - 1)
    unfold Pool.P0085.levTh; omega
  have hlevLt : ∀ a < NE, ∀ r < D, Pool.P0085.levTh Ld Bt r a ≤ Lt := fun a _ r _ => by
    have := Pool.P0062.levPR_le Ld ((a + 1) / Bt r - 1)
    unfold Pool.P0085.levTh; omega
  have hp0 : ∀ x : SlotC NE D Lt K × ι, 0 ≤ Pool.P0091.pC ps q x := fun x => by
    rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith
  have hp1 : ∀ x : SlotC NE D Lt K × ι, Pool.P0091.pC ps q x ≤ 1 := fun x => by
    rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith
  set π := ps * (1 - q) ^ (K * (D * (2 * Ld + NE / 2 ^ Ld + 1))) with hπdef
  have hπ : 0 < π := mul_pos hps0 (pow_pos (by linarith) _)
  have hπ1 : π ≤ 1 := by
    have : (1 - q) ^ (K * (D * (2 * Ld + NE / 2 ^ Ld + 1))) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    calc π ≤ 1 * 1 := mul_le_mul hps1 this (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hpi : ∀ (j : Fin D) (a : Fin NE) (h : Bt j ∣ a),
      π ≤ piS (Pool.P0091.pC ps q) (oppSet E thr0 D Bt (Pool.P0085.levTh Ld Bt) NE Lt K (cstar j a)
        (by rw [hE j a (by omega) h a.2]; exact a.2)) oppVal := by
    intro j a h
    have he := hE j a (by omega) h a.2
    have ht := hthr j a (by omega) h a.2
    exact Pool.P0091.piS_geT (E := E) (thr0 := thr0) hB hps0.le hq0 hq1.le (cstar j a) _ (by rw [he, ht]; exact h) (by rw [ht]; exact j.2)
  have h1 := count_bad_Z E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L rh hB hLv hlev cstar hE hthr
    (Pool.P0091.pC ps q) hp0 hp1 π hπ hπ1 hpi (s0 + D * Lv * S' + 1)
  set Pbad := (NE * D * δs + NE * D * (Lt + 1) * K * Pool.P0042.delta (Fintype.card ι) q R kk M0 : ℝ) with hPbad
  have hPna : ∑ ω, Pool.P0048.wtv (Pool.P0091.pC ps q) ω * ∑ yy : Fin NE → Fin s,
      Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      (if GoodAZ E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L rh NE (s0 + D * Lv * S' + 1) (ωsC E NE D Lt K ω)
        (φC NE D Lt K ω) (extY s yy) then 0 else 1) ≤ Pbad := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ yy : Fin NE → Fin s, ∑ ω, Pool.P0048.wtv (Pool.P0091.pC ps q) ω * (Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
          (if GoodAZ E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L rh NE (s0 + D * Lv * S' + 1)
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) then 0 else 1))
        = ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * ∑ ω, Pool.P0048.wtv (Pool.P0091.pC ps q) ω *
          (if GoodAZ E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L rh NE (s0 + D * Lv * S' + 1)
            (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) then 0 else 1) := by
          refine Finset.sum_congr rfl fun yy _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * Pbad :=
          Finset.sum_le_sum fun yy _ => mul_le_mul_of_nonneg_left
            (prob_notGoodAZ_le E thr0 θ R K D Lv Bt (Pool.P0085.levTh Ld Bt) s L rh ⟨hps0.le, hps1⟩ hq0 hq1.le hEm
              hB hLv hlev hs1 hL0 hL1 hR hT M0 kk hM0 hk hp hlevLt s0 δs hs S' hM0S hρS hsl (extY s yy))
            (Pool.P0119.wR_nonneg_s s yy)
      _ = Pbad := by rw [← Finset.sum_mul, Pool.P0126.sum_wR_one, one_mul]
  refine h1.trans ?_
  have hcast : ((D * Lv * (s0 + D * Lv * S' + 1) : ℕ) : ℝ) = (D * Lv * (s0 + D * Lv * S' + 1) : ℝ) := by
    push_cast; ring
  have hDNE : (0 : ℝ) ≤ D * NE := by positivity
  have := mul_le_mul_of_nonneg_left hPna hDNE
  push_cast at this ⊢
  linarith

end Closed

end Pool.P0170
