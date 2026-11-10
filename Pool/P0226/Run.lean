import Pool.P0226.Act
import Pool.P0197.Bridge
import Pool.P0207.Assemble

/-!
# The per-run ALG-term bound for P0194's process with P0212's ALG (P0186's `run_bound_mix`, all hypotheses
discharged on the good events)
-/

namespace Pool.P0226

open Finset Pool.P0089 Pool.P0194 Pool.P0001 Pool.P0050 Pool.P0212 Pool.P0220 Pool.P0224

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρr : AState ι → Finset ι → ℝ) (ℓ : LossSeq n)
  (ω : ℕ → RC (withAlg P η L N G γ wE ρr)) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (withAlg P η L N G γ wE ρr).K → ι → Bool) (T : ℕ)

theorem rhD_eq_rhOf : rhD (withAlg P η L N G γ wE ρr) ℓ ω =
    Pool.P0207.rhOf (withAlg P η L N G γ wE ρr).E (withAlg P η L N G γ wE ρr).Bmin (withAlg P η L N G γ wE ρr).Λ
      (Bh (withAlg P η L N G γ wE ρr) ℓ ω) := rfl

theorem aPol_le_one (u : ℕ) : aPol (withAlg P η L N G γ wE ρr) ℓ ωs φ ω u ≤ 1 := by
  have hN : ∑ _d : Fin (withAlg P η L N G γ wE ρr).N, (1 / ((withAlg P η L N G γ wE ρr).N : ℝ)) ≤ 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (withAlg P η L N G γ wE ρr).N with h | h
    · rw [h]; simp
    · have : (0 : ℝ) < (withAlg P η L N G γ wE ρr).N := by exact_mod_cast h
      field_simp; exact le_rfl
  have hμ := Pool.P0092.sum_toReal_one (withAlg P η L N G γ wE ρr).AB.μ
  unfold aPol
  simp only [Nat.cast_one]
  refine le_trans (Finset.sum_le_sum fun d _ => ?_) hN
  refine mul_le_of_le_one_right (by positivity : (0 : ℝ) ≤ 1 / ((withAlg P η L N G γ wE ρr).N : ℝ)) ?_
  calc _ ≤ ∑ yB, ((withAlg P η L N G γ wE ρr).AB.μ yB).toReal * 1 :=
        Finset.sum_le_sum fun yB _ => mul_le_mul_of_nonneg_left (by
          split <;> (cases ℓ u _ <;> simp)) ENNReal.toReal_nonneg
    _ = 1 := by simp only [mul_one]; exact hμ


local notation "QQ" => withAlg P η L N G γ wE ρr

/-- The comparator's truncated losses. -/
noncomputable def gT (i : Fin n) (u : ℕ) : ℝ := if u < T then ((ℓ u i).toNat : ℝ) else 0

variable (rc0 : RC (withAlg P η L N G γ wE ρr))

/-- **Per-run ALG-term bound for P0194's process with P0212's ALG** (P0186's `run_bound_mix`, all its hypotheses
discharged): on the good events of `actHyp_alg` and P0218's record events (for the comparator's copies), with the
entry-order layout, comparator copies of arm `i` on the grid, the rule's margins dominating P0186's `Λ'`, and P0186's
shape conditions on `f a c w Λ'`,
`Σ_{u<T}(aPol − ℓ_u(i) − (η/2)·VR) ≤ T·a 0 + Σ_{1≤j<D} Bt(j−1)·nBad(j−1)·a j + nBad(D−1)·c`. -/
theorem run_bound_alg (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv)
    (hL : (withAlg P η L N G γ wE ρr).IsLaw) (hN : 0 < (withAlg P η L N G γ wE ρr).N) (hη : 0 < η) {δ : ℝ}
    (hδ : 0 ≤ δ) (hρr : ∀ σ V, |ρr σ V| ≤ δ) (hγ : 0 < γ) (hwE0 : 0 < wE) (hwE : P.wE = wE) (hG : 1 ≤ G)
    (hTL : T ≤ 2 ^ L) (hcB0 : 0 ≤ (withAlg P η L N G γ wE ρr).cB)
    {Ls Lb Lc xmin : ℝ} (hLs : 0 ≤ Ls) (hLb : 0 ≤ Lb) (hLc : 0 ≤ Lc) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ (withAlg P η L N G γ wE ρr).xr j)
    (hlay : (withAlg P η L N G γ wE ρr).lay = Pool.P0176.sortLay (withAlg P η L N G γ wE ρr).sl)
    (hS : ∀ f, Pool.P0158.GoodV (Pool.P0203.DS (withAlg P η L N G γ wE ρr) ℓ ωs φ rc0 f)
      (Pool.P0203.gateS (withAlg P η L N G γ wE ρr) ℓ ωs φ rc0 f) (Pool.P0203.rS (withAlg P η L N G γ wE ρr) f)
      (Pool.P0158.rmax1 (Pool.P0203.rS (withAlg P η L N G γ wE ρr) f)) Ls T (Pool.P0203.pre _ ω T))
    (hfit : ∀ u, u < T → Pool.P0176.Fits (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl
      (sp (withAlg P η L N G γ wE ρr) ℓ ω ωs φ u))
    (hB : Pool.P0158.GoodV (Pool.P0216.DB (withAlg P η L N G γ wE ρr) ℓ rc0) (fun _ _ => true)
      (fun _ => (withAlg P η L N G γ wE ρr).cB) (Pool.P0158.rmax1 (fun _ => (withAlg P η L N G γ wE ρr).cB)) Lb T
      (Pool.P0203.pre _ ω T))
    (hX : ∀ x, Pool.P0146.IXGood (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN) (lossX P η L N G γ wE ρr ℓ x)
      (obsX P η L N G γ wE ρr ℓ ωs φ rc0 (some x)) (wE * γ) (gateX P η L N G γ wE ρr ℓ ωs φ rc0 x) Lc T
      (Pool.P0203.pre _ ω T))
    (hXm : Pool.P0149.StepGood (Pool.P0149.ixErrV (Pool.P0203.nuD (withAlg P η L N G γ wE ρr) hL hN)
      (YB P η L N G γ wE ρr ℓ rc0) (bPolX P η L N G γ wE ρr ℓ rc0) (obsX P η L N G γ wE ρr ℓ ωs φ rc0 none)
      (wE * γ)) (fun _ _ => true) (Lc / (2 * (wE * γ))) T (Pool.P0203.pre _ ω T))
    (hA : Pool.P0158.GoodV (DA P η L N G γ wE ρr ℓ ωs φ rc0 hL hN) (fun _ _ => true)
      (fun _ => (1 + 1 / (N * γ)) / wE) (fun _ _ => (1 + 1 / (N * γ)) / wE) Lc T (Pool.P0203.pre _ ω T))
    (bmax : ℝ) (hb0 : 0 ≤ bmax) (hbmax : ∀ u, u < T → biasR P η L N G γ wE ρr ℓ ωs φ ω u ≤ bmax)
    (hθ : 0 ≤ (QQ).θ) (hR1 : 1 ≤ (QQ).R) (hBt : Pool.P0065.BtHyp (QQ).D (QQ).Bt) (hT : (QQ).Bt 0 ∣ T) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).E (cstar j a) = a)
    (hthr : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).thr0 (cstar j a) = j)
    (i : Fin n) (harm : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → (QQ).arm (cstar j a) = i)
    (hgF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false →
      Pool.P0158.GoodV (Pool.P0203.DS (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (withAlg P η L N G γ wE ρr).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.gateS (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ℓ
          (Pool.P0065.forceS ωs (cstar j a)) (Pool.P0065.forceF (withAlg P η L N G γ wE ρr).K φ (cstar j a)) rc0
          (cstar j a))
        (Pool.P0203.rS (withAlg P η L N G γ wE ρr) (cstar j a))
        (Pool.P0158.rmax1 (Pool.P0203.rS (withAlg P η L N G γ wE ρr) (cstar j a))) Ls T
        (Pool.P0203.pre (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ω T))
    (hfF : ∀ j a, j < (QQ).D → (QQ).Bt j ∣ a → a < T → ωs (cstar j a) = false → ∀ u, u < T →
      Pool.P0176.Fits (withAlg P η L N G γ wE ρr).Lv (withAlg P η L N G γ wE ρr).sl
        (sp (Pool.P0218.PL (withAlg P η L N G γ wE ρr) (cstar j a)) ℓ ω (Pool.P0065.forceS ωs (cstar j a))
          (Pool.P0065.forceF (withAlg P η L N G γ wE ρr).K φ (cstar j a)) u))
    (Λ' : ℕ → ℕ → ℝ) (hΛ' : ∀ c u, Λ' (min (Pool.P0065.curT (QQ).E (QQ).thr0 (QQ).D (QQ).Bt c (u + 1)) ((QQ).D - 1)) (u + 1 - (QQ).E c) ≤
      (QQ).Λ c u)
    (ff aa : ℕ → ℝ) (cc : ℝ) (w : ℕ → ℝ) (ha : ∀ j < (QQ).D, 0 ≤ aa j) (hc0 : 0 ≤ cc)
    (hbig : ∀ j < (QQ).D, ∀ m : ℕ, (QQ).Bt j ≤ m → ff m ≤ m * aa j)
    (hsmall : ∀ m : ℕ, m < (QQ).Bt ((QQ).D - 1) → ff m ≤ cc)
    (hf : ∀ m : ℕ, (QQ).θ + (QQ).R * (2 * αT (ι := ι) η L T δ + 2 * (Lc / (2 * (wE * γ))) +
        (2 * √(Ls * ((m : ℝ) / xmin)) + 2 * Ls / xmin)) + (2 * √(Ls * ((m : ℝ) / xmin)) + 2 * Ls / xmin) +
        (Pool.P0158.widV (T * ((1 + 1 / (N * γ)) / wE)) ((1 + 1 / (N * γ)) / wE) Lc + T * bmax) ≤ ff m)
    (hfB : (1 : ℝ) * (QQ).Bt ((QQ).D - 1) ≤ ff ((QQ).Bt ((QQ).D - 1)))
    (hΛ : ∀ j (m : ℕ), (Pool.P0158.widV (T * ((1 + 1 / (N * γ)) / wE)) ((1 + 1 / (N * γ)) / wE) Lc + T * bmax) +
        αT (ι := ι) η L T δ + Lc / (2 * (wE * γ)) + 0 +
        Pool.P0158.widV (m * (withAlg P η L N G γ wE ρr).cB) (max 1 (withAlg P η L N G γ wE ρr).cB) Lb +
        (2 * √(Ls * ((m : ℝ) / xmin)) + 2 * Ls / xmin) + w j ≤ Λ' j m)
    (hw : ∀ i < (QQ).D, ∑ j ∈ Finset.Ico 1 (QQ).D, (if i ≤ j - 1 then ((QQ).Bt (j - 1) : ℝ) * aa j else 0) +
      (if i ≤ (QQ).D - 1 then cc else 0) ≤ w i) :
    ∑ u ∈ Finset.range T, (aPt P η L N G γ wE ρr ℓ ω ωs φ T u - gT ℓ T i u -
        η / 2 * VR P η L N G γ wE ρr ℓ ω ωs φ T u) ≤
      T * aa 0 + ∑ j ∈ Finset.Ico 1 (QQ).D, ((QQ).Bt (j - 1) : ℝ) *
          (Pool.P0135.nBadB T (QQ).Bt (fun τ r => Pool.P0186.outMix (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
            (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (QQ).lay (zc (withAlg P η L N G γ wE ρr) ω)) ∅
            (fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (Pool.P0176.lastLay (QQ).sl c') (zc (withAlg P η L N G γ wE ρr) ω))
            (fun _ => ∅) ((QQ).D - 1) T ωs φ (cstar r τ)) (j - 1) : ℝ) * aa j +
        (Pool.P0135.nBadB T (QQ).Bt (fun τ r => Pool.P0186.outMix (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt (QQ).lev
            (Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (QQ).lay (zc (withAlg P η L N G γ wE ρr) ω)) ∅
            (fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
              (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (Pool.P0176.lastLay (QQ).sl c') (zc (withAlg P η L N G γ wE ρr) ω))
            (fun _ => ∅) ((QQ).D - 1) T ωs φ (cstar r τ)) ((QQ).D - 1) : ℝ) * cc := by
  have H := actHyp_alg P η L N G γ wE ρr ℓ ω ωs φ T rc0 hD hLv hlev hL hN hη hδ hρr hγ hwE0 hwE hG hTL hcB0 hLs hLb
    hLc hxm hxm1 hxr hS hfit hB hX hXm hA bmax hb0 hbmax
  obtain ⟨hWm, hW0⟩ := Pool.P0218.Wlen_mono_nonneg hLs hxm
  refine Pool.P0186.run_bound_mix (U := fun c' => Pool.P0176.dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr
      (ℓr (withAlg P η L N G γ wE ρr) ℓ) (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (Pool.P0176.lastLay (QQ).sl c')
      (zc (withAlg P η L N G γ wE ρr) ω)) (A0 := fun _ => ∅) (Bep := 1) hBt hLv hlev hT cstar hE hthr ?hcoup
    (ℓt P η L N G γ wE ρr ℓ T) (fun u x => cuR P η L N G γ wE ρr ℓ ω ωs φ T u (some x)) (gT ℓ T i) ?hg
    _ _ _ _ _ _ _ _ _ _ Λ' (αT_nonneg (ι := ι) η L T hη hδ) (div_nonneg hLc (by positivity)) hW0 hWm ?hθ ?hR1 H
    ?hup ?hrule ?hBep ff aa cc w ha hc0 hbig hsmall hf hfB hΛ hw
  case hcoup =>
    intro j a hj hdv haT hc
    have := Pool.P0197.coup_dz (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ)
      (rhD (withAlg P η L N G γ wE ρr) ℓ ω) (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).Bt (QQ).lev (zc (withAlg P η L N G γ wE ρr) ω) hc φ
    rw [hlay]
    exact this
  case hg =>
    intro j a u hj hdv haT
    unfold ℓt gT ℓr
    rw [show (withAlg P η L N G γ wE ρr).arm (cstar j a) = i from harm j a hj hdv haT]
  case hθ => exact hθ
  case hR1 => exact hR1
  case hBep =>
    intro u
    have h1 : aPt P η L N G γ wE ρr ℓ ω ωs φ T u ≤ 1 := by
      unfold aPt; split_ifs
      · exact aPol_le_one P η L N G γ wE ρr ℓ ω ωs φ u
      · exact zero_le_one
    have h2 : 0 ≤ gT ℓ T i u := by unfold gT; split_ifs <;> positivity
    have h3 : 0 ≤ η / 2 * VR P η L N G γ wE ρr ℓ ω ωs φ T u :=
      mul_nonneg (by positivity) (VR_nonneg P η L N G γ wE ρr ℓ ω ωs φ T u)
    linarith
  case hup =>
    intro j a hj hdv haT e hae heT hnr
    have hEa := hE j a hj hdv haT
    have h := Pool.P0218.hup_len (withAlg P η L N G γ wE ρr) ℓ ω ωs φ hD hLv hlev rc0 (cstar j a) hLs hxm hxm1 hxr T
      (fun _ => hS (cstar j a)) (fun hs u hu => hfit u hu) (hgF j a hj hdv haT) (hfF j a hj hdv haT) e (by omega) heT
      (by rw [hEa]; exact hnr)
    rw [hEa] at h
    have e1 : ∑ u ∈ Ico a e, ℓr (withAlg P η L N G γ wE ρr) ℓ u (cstar j a) =
        ∑ u ∈ Ico a e, ℓt P η L N G γ wE ρr ℓ T u (cstar j a) :=
      Finset.sum_congr rfl fun u hu => by
        simp only [Finset.mem_Ico] at hu; unfold ℓt; rw [if_pos (by omega)]
    rw [e1] at h
    exact h
  case hrule =>
    intro j a hj hdv haT e hret
    have hEa := hE j a hj hdv haT
    have h := Pool.P0207.dz_hrule (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (withAlg P η L N G γ wE ρr) ℓ) (QQ).E (QQ).thr0
      (QQ).θ (QQ).R (QQ).K (QQ).Bt (QQ).lev (zc (withAlg P η L N G γ wE ρr) ω) (QQ).Bmin (QQ).Λ
      (Bh (withAlg P η L N G γ wE ρr) ℓ ω) hD hLv hlev T ωs φ Λ' hΛ' (cstar j a) e (by rw [← hlay]; exact hret)
    rw [← hlay, hEa] at h
    have e1 : ∑ u ∈ Ico a e, (Bh (withAlg P η L N G γ wE ρr) ℓ ω (u + 1) - Bh (withAlg P η L N G γ wE ρr) ℓ ω u) =
        ∑ u ∈ Ico a e, Pool.P0216.incBD (withAlg P η L N G γ wE ρr) ℓ ω u :=
      Finset.sum_congr rfl fun u _ => by
        rw [Pool.P0216.Bh_sum (withAlg P η L N G γ wE ρr) ℓ ω u (u + 1) (Nat.le_succ u)]
        simp
    rw [e1] at h
    exact h

end Pool.P0226
