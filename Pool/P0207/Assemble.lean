import Pool.P0207.Round
import Pool.P0207.Walk
import Pool.P0207.Rule

/-!
# P0194's process: expected walk right-hand side and the rule hypothesis

* `rhXR_eq`: P0194's rule recomputed from the external history is `rhOf` with B̂ recomputed (`BhE`).
Both are stated for the entry-order run (`sortLay`) and copy-last runs with schedule `levTh Ld P.Bt`; they concern
P0194's own process when `P.lay = sortLay P.sl` and `P.lev = levTh Ld P.Bt` (`pool_eq_sort`).

* **`exp_walkRHS_round`**: over P0091's sampling/filter coin law and P0194's round coins, the expectation of the
  right-hand side of P0186's `run_bound_mix` (mixed outcomes of the entry-order run and the forced copy-last runs, rule
  of each coin prefix) is at most `NE·a₀ + M·(count_bad_round's closed form)`.
* **`hrule_round`**: P0186's `hrule` for these runs, with `Bhat u = B̂(u+1) − B̂(u)` (B̂ recomputed from the prefix).
-/

namespace Pool.P0207

open Pool.P0200 Finset Pool.P0001 Pool.P0050 Pool.P0194 Pool.P0176 Pool.P0082 Pool.P0048 Pool.P0065 Pool.P0156 Pool.P0186

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι) (ℓ : LossSeq n)

theorem rhXR_eq (e : ℕ → Option (Bool × P.AB.Y × P.AB.Z)) : rhXR P ℓ e = rhOf P.E P.Bmin P.Λ (BhE P ℓ e) := rfl

attribute [local instance] Pool.P0082.coinFintype

open Classical in
/-- **Expected walk right-hand side for the entry-order/copy-last runs with P0194's rule and coins** (schedule
`levTh Ld P.Bt`). It is about P0194's own process only when `P.lay = sortLay P.sl` and `P.lev = levTh Ld P.Bt`
(`pool_eq_sort`). -/
theorem exp_walkRHS_round (hL : P.IsLaw) (hN : 0 < P.N) (hB : BtHyp P.D P.Bt) {Ld NE Lt : ℕ}
    (hLv2 : Ld + 2 ≤ P.Lv) (hLt : Ld ≤ Lt)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < P.D → P.Bt j ∣ a → a < NE → P.E (cstar j a) = a)
    (hthr : ∀ j a, j < P.D → P.Bt j ∣ a → a < NE → P.thr0 (cstar j a) = j)
    {ps q : ℝ} (hps0 : 0 < ps) (hps1 : ps ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hEm : Monotone P.E) {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ P.xr j) (hBm : (1 : ℝ) ≤ 1 / xmin)
    (hR : 1 ≤ P.R) (hT : 1 / xmin * NE ≤ 2 ^ (P.R - 1) * P.θ) (M0 : ℝ) (kk : ℕ) (hM0 : 16 * P.R ≤ M0)
    (hk : 4 * P.R * kk ≤ M0) (hp : q * (Real.exp 1 - 1) ≤ 1 / (32 * P.R)) (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < P.D →
      ∑ F ∈ (Finset.univ.filter fun c => P.E c = a ∧ P.thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => P.E c = a ∧ P.thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S' : ℕ) (hM0S : M0 ≤ S') (hρS : (1 - 1 / (4 * P.R : ℝ)) ^ P.K * ((S' : ℝ) + (s0 + P.D * P.Lv * S')) ≤ S')
    (hsl : ∀ j, (P.D : ℝ) * ((s0 + P.D * P.Lv * S') + (P.Lv - 1 : ℕ) * S') + P.D * s0 + 1 ≤ P.sl j)
    (a : ℕ → ℝ) (c M : ℝ) (hM0' : 0 ≤ M)
    (hMa : ∀ j, 1 ≤ j → j < P.D → (P.Bt (j - 1) : ℝ) * a j ≤ M) (hMc : c ≤ M) :
    ∑ ω, wtv (Pool.P0091.pC (NE := NE) (D := P.D) (Lt := Lt) (K := P.K) ps q) ω *
      ∑ yy : Fin NE → RC P, Pool.P0070.wR (wR P) yy *
      (NE * a 0 + ∑ j ∈ Finset.Ico 1 P.D, (P.Bt (j - 1) : ℝ) *
          (Pool.P0135.nBadB NE P.Bt (fun τ r => outMix P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt (Pool.P0085.levTh Ld P.Bt)
            (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (sortLay P.sl)
              (zE P.sl 1 (zOfR P) yy)) ∅
            (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (lastLay P.sl c')
              (zE P.sl 1 (zOfR P) yy)) (fun _ => ∅) (P.D - 1) NE
            (ωsC P.E NE P.D Lt P.K ω) (φC NE P.D Lt P.K ω) (cstar r τ)) (j - 1) : ℝ) * a j +
        (Pool.P0135.nBadB NE P.Bt (fun τ r => outMix P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt (Pool.P0085.levTh Ld P.Bt)
            (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (sortLay P.sl)
              (zE P.sl 1 (zOfR P) yy)) ∅
            (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (lastLay P.sl c')
              (zE P.sl 1 (zOfR P) yy)) (fun _ => ∅) (P.D - 1) NE
            (ωsC P.E NE P.D Lt P.K ω) (φC NE P.D Lt P.K ω) (cstar r τ)) (P.D - 1) : ℝ) * c) ≤
      NE * a 0 + M * ((P.D * P.Lv * (s0 + P.D * P.Lv * S' + 1) : ℝ) /
          (ps * (1 - q) ^ (P.K * (P.D * (2 * Ld + NE / 2 ^ Ld + 1)))) +
        P.D * NE * (NE * P.D * δs + NE * P.D * (Lt + 1) * P.K * Pool.P0042.delta (Fintype.card ι) q P.R kk M0)) := by
  have hD := hB.hD
  have hE' : ∀ j a, j ≤ P.D - 1 → P.Bt j ∣ a → a < NE → P.E (cstar j a) = a :=
    fun j a hj => hE j a (by omega)
  have hthr' : ∀ j a, j ≤ P.D - 1 → P.Bt j ∣ a → a < NE → P.thr0 (cstar j a) = j :=
    fun j a hj => hthr j a (by omega)
  have hp0 : ∀ x : SlotC NE P.D Lt P.K × ι, 0 ≤ Pool.P0091.pC ps q x := fun x => by
    rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith
  have hp1 : ∀ x : SlotC NE P.D Lt P.K × ι, Pool.P0091.pC ps q x ≤ 1 := fun x => by
    rcases x with ⟨s, c⟩; cases s <;> simp [Pool.P0091.pC, Pool.P0073.qOfT] <;> linarith
  exact exp_walkRHS_X P.Lv P.sl 1 1 P.xr (ℓr P ℓ) P.E P.thr0 P.θ P.R P.K P.Bt (Pool.P0085.levTh Ld P.Bt)
    (zOfR P) (extR P) none (rhXR P ℓ) (wR P) (wR_nonneg P hL) (sum_wR P hL hN) cstar hE hD
    (Pool.P0091.pC ps q) hp0 hp1 a c M _ hM0' hMa hMc
    (count_bad_round P ℓ hL hN hB hLv2 hLt cstar hE' hthr' hps0 hps1 hq0 hq1 hEm hxmin hx hBm hR hT M0 kk hM0 hk hp
      s0 δs hs S' hM0S hρS hsl)

/-- **P0186's rule hypothesis** for the entry-order/copy-last runs with P0194's rule and B̂ of a coin prefix `yy`
(schedule `levTh Ld P.Bt`; P0207's `dz_hrule`). These are P0194's runs only when `P.lay = sortLay P.sl` and
`P.lev = levTh Ld P.Bt` (`pool_eq_sort`). -/
theorem hrule_round (hD : 0 < P.D) (hLv : 0 < P.Lv) {Ld : ℕ} (hlev : ∀ r a, Pool.P0085.levTh Ld P.Bt r a + 1 < P.Lv)
    {NE : ℕ} (yy : Fin NE → RC P) (T : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)
    (Λ' : ℕ → ℕ → ℝ)
    (hΛ : ∀ c u, Λ' (min (curT P.E P.thr0 P.D P.Bt c (u + 1)) (P.D - 1)) (u + 1 - P.E c) ≤ P.Λ c u) (c : ι) (e : ℕ)
    (hret : RetAt P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt (Pool.P0085.levTh Ld P.Bt)
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (sortLay P.sl) (zE P.sl 1 (zOfR P) yy)) ∅
      (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (lastLay P.sl c')
        (zE P.sl 1 (zOfR P) yy)) (fun _ => ∅) T ωs φ c e) :
    Λ' (min (curT P.E P.thr0 P.D P.Bt c e) (P.D - 1)) (e - P.E c) ≤
      ∑ u ∈ Ico (P.E c) e, Pool.P0105.incrOf (recD P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt (Pool.P0085.levTh Ld P.Bt)
        (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (sortLay P.sl)
          (zE P.sl 1 (zOfR P) yy)) ∅
        (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhXR P ℓ (extE (extR P) none yy)) (lastLay P.sl c')
          (zE P.sl 1 (zOfR P) yy)) (fun _ => ∅) ωs φ c) u c -
      ∑ u ∈ Ico (P.E c) e, (BhE P ℓ (extE (extR P) none yy) (u + 1) - BhE P ℓ (extE (extR P) none yy) u) :=
  dz_hrule P.Lv P.sl 1 1 P.xr (ℓr P ℓ) P.E P.thr0 P.θ P.R P.K P.Bt (Pool.P0085.levTh Ld P.Bt)
    (zE P.sl 1 (zOfR P) yy) P.Bmin P.Λ (BhE P ℓ (extE (extR P) none yy)) hD hLv hlev T ωs φ Λ' hΛ c e hret

end Pool.P0207
