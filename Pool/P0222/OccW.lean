import Pool.P0208.Tails
import Pool.P0218.RecUp

/-!
# One occupancy-based length-only width for both P0186 slot tails on P0194's process

P0186 uses ONE monotone width `W : ℕ → ℝ` for the members' lower tail (`hlo`) and the record's upper tail (`hup`).
With P0171's occupancy bound on the thread rates, P0158's interval width of every copy entered by the start of the
interval is at most `Wocc(m) = 2L/xmin + 2√(L·(m·M + Θ·ρT/n))` (`m` = length, `xmin` = rate floor for the range term,
`Θ ≥ thr0`). This keeps the thread benefit (the variance part uses `M`, not `1/xmin`).

* `widV_le_occ`: the width bound for an interval starting at or after the copy's entry.
* `Wocc_mono`: `Wocc` is monotone.
* `hlo_occ`: P0208's `hlo_of_good` with `Wocc`.
* `hup_occ`: P0218's `hup_rec` with `Wocc`.
-/

open Finset Pool.P0001 Pool.P0194 Pool.P0176 Pool.P0065 Pool.P0203 Pool.P0208

namespace Pool.P0222

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι] (P : ParD n ι)

/-- The occupancy-based length-only width. -/
noncomputable def Wocc (L xmin M ρ nn TT Θ : ℝ) (m : ℕ) : ℝ :=
  2 * L / xmin + 2 * √(L * ((m : ℝ) * M + Θ * (ρ * TT / nn)))

theorem Wocc_mono {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M) : Monotone (Wocc L xmin M ρ nn TT Θ) := by
  intro m m' h
  unfold Wocc
  have : (m : ℝ) * M ≤ (m' : ℝ) * M := mul_le_mul_of_nonneg_right (by exact_mod_cast h) hM
  have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith : (m : ℝ) * M + Θ * (ρ * TT / nn) ≤
    (m' : ℝ) * M + Θ * (ρ * TT / nn)) hL)
  linarith

/-- **The width bound** for a copy entered by `s` (or an empty interval). -/
theorem widV_le_occ (f : ι) {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1)
    (hxr : ∀ j, xmin ≤ P.xr j) (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i))) (hΘ : (P.thr0 f : ℝ) ≤ Θ)
    {s s' : ℕ} (hent : s < s' → P.E f ≤ s) :
    Pool.P0158.widV (∑ u ∈ Ico s s', rS P f u) (Pool.P0158.rmax1 (rS P f) s s') L ≤
      Wocc L xmin M ρ nn TT Θ (s' - s) := by
  have hρ₀ : Pool.P0158.rmax1 (rS P f) s s' ≤ 1 / xmin := by
    unfold Pool.P0158.rmax1
    refine max_le (one_le_one_div hxm hxm1) ?_
    have : ((Finset.Ico s s').sup (fun u => Real.toNNReal (rS P f u)) : NNReal) ≤ Real.toNNReal (1 / xmin) :=
      Finset.sup_le fun u _ => Real.toNNReal_le_toNNReal (rS_le P f hxm hxm1 hxr u)
    have h' := (NNReal.coe_le_coe.2 this)
    rwa [Real.coe_toNNReal _ (by positivity)] at h'
  have hcΘ : (P.thr0 f : ℝ) * (ρ * TT / nn) ≤ Θ * (ρ * TT / nn) :=
    mul_le_mul_of_nonneg_right hΘ (by positivity)
  have e : 2 * (1 / xmin) * L = 2 * L / xmin := by ring
  unfold Wocc
  rcases Nat.lt_or_ge s s' with hlt | hge
  · have h := widV_le_sqrt_occ P f hL hn hT hM hB hρ hx0 hx s s' (hent hlt) hρ₀
    have hs : √(L * (((s' - s : ℕ) : ℝ) * M + P.thr0 f * (ρ * TT / nn))) ≤
        √(L * (((s' - s : ℕ) : ℝ) * M + Θ * (ρ * TT / nn))) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by linarith) hL)
    linarith
  · have hI : Finset.Ico s s' = ∅ := Finset.Ico_eq_empty_of_le hge
    rw [hI, Finset.sum_empty]
    unfold Pool.P0158.widV
    simp only [zero_mul, Real.sqrt_zero, mul_zero, zero_add]
    have h1 : Pool.P0158.rmax1 (rS P f) s s' * L ≤ 1 / xmin * L := mul_le_mul_of_nonneg_right hρ₀ hL
    have h2 : (0 : ℝ) ≤ √(L * (((s' - s : ℕ) : ℝ) * M + Θ * (ρ * TT / nn))) := Real.sqrt_nonneg _
    nlinarith

variable (ℓ : LossSeq n) (ω : ℕ → RC P) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin P.K → ι → Bool)

open Classical in
/-- **P0186's `hlo` for P0194's process with the occupancy width `Wocc`** (on P0203's good event, no overflow,
horizon `T`; P0208's `hlo_of_good`). -/
theorem hlo_occ (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (rc0 : RC P)
    {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ P.xr j)
    (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i))) (hΘ : ∀ f, (P.thr0 f : ℝ) ≤ Θ)
    (T : ℕ) (hgood : ∀ f, Pool.P0158.GoodV (DS P ℓ ωs φ rc0 f) (gateS P ℓ ωs φ rc0 f) (rS P f)
      (Pool.P0158.rmax1 (rS P f)) L T (pre P ω T))
    (hfit : ∀ u, u < T → Fits P.Lv P.sl (sp P ℓ ω ωs φ u)) (f : ι) {s s' : ℕ} (hss : s ≤ s') (hs'T : s' ≤ T)
    (hP : Pool.P0186.PresAct P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅ ωs φ f s s') :
    ∑ u ∈ Ico s s', ℓr P ℓ u f ≤ ∑ u ∈ Ico s s', Pool.P0105.incrOf (dat P ℓ ω ωs φ) u f +
      Wocc L xmin M ρ nn TT Θ (s' - s) := by
  refine (hlo_of_good P ℓ ω ωs φ hD hLv hlev rc0 T hgood hfit f hss hs'T hP).trans (add_le_add le_rfl ?_)
  refine widV_le_occ P f hL hxm hxm1 hxr hn hT hM hρ0 hB hρ hx0 hx (hΘ f) fun hlt => ?_
  have hact := (presAct_iff P ℓ ω ωs φ hD hLv hlev f s s').1 hP
  exact E_le_of_active P ℓ ω ωs φ hD hLv hlev (hact s le_rfl hlt)

open Classical in
/-- **P0186's `hup` for P0194's process with the same width `Wocc`** (P0218's `hup_rec`). -/
theorem hup_occ (hD : 0 < P.D) (hLv : 0 < P.Lv) (hlev : ∀ r a, P.lev r a + 1 < P.Lv) (rc0 : RC P) (c : ι)
    {L xmin M ρ nn TT Θ : ℝ} (hL : 0 ≤ L) (hxm : 0 < xmin) (hxm1 : xmin ≤ 1) (hxr : ∀ j, xmin ≤ P.xr j)
    (hn : 0 < nn) (hT : 0 ≤ TT) (hM : 0 ≤ M) (hρ0 : 0 ≤ ρ) (hB : ∀ i, 0 < P.Bt i)
    (hρ : ∀ i, 1 ≤ i → (P.Bt (i - 1) : ℝ) ≤ ρ * P.Bt i) (hx0 : 1 / Pool.P0191.xrN P.xr 0 ≤ M)
    (hx : ∀ i, 1 ≤ i → 1 / Pool.P0191.xrN P.xr i ≤ max M (TT / (nn * P.Bt i))) (hΘ : (P.thr0 c : ℝ) ≤ Θ) (T : ℕ)
    (hgA : ωs c = true → Pool.P0158.GoodV (DS P ℓ ωs φ rc0 c) (gateS P ℓ ωs φ rc0 c) (rS P c)
      (Pool.P0158.rmax1 (rS P c)) L T (pre P ω T))
    (hfA : ωs c = true → ∀ u, u < T → Fits P.Lv P.sl (sp P ℓ ω ωs φ u))
    (hgF : ωs c = false → Pool.P0158.GoodV (DS (Pool.P0218.PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 c)
      (gateS (Pool.P0218.PL P c) ℓ (forceS ωs c) (forceF P.K φ c) rc0 c) (rS P c) (Pool.P0158.rmax1 (rS P c)) L T
      (pre (Pool.P0218.PL P c) ω T))
    (hfF : ωs c = false → ∀ u, u < T →
      Fits P.Lv P.sl (sp (Pool.P0218.PL P c) ℓ ω (forceS ωs c) (forceF P.K φ c) u))
    (e : ℕ) (hce : P.E c ≤ e) (heT : e ≤ T)
    (hnr : ∀ u, P.E c < u → u < e → c ∉ Pool.P0186.recAux P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅
      (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) (lastLay P.sl c') (zc P ω)) (fun _ => ∅)
      ωs φ c u) :
    ∑ u ∈ Ico (P.E c) e, Pool.P0105.incrOf (Pool.P0186.recD P.E P.thr0 P.θ P.R P.K P.D P.Lv P.Bt P.lev
      (dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) P.lay (zc P ω)) ∅
      (fun c' => dzUpd P.D P.Lv P.sl 1 1 P.xr (ℓr P ℓ) (rhD P ℓ ω) (lastLay P.sl c') (zc P ω)) (fun _ => ∅)
      ωs φ c) u c ≤ ∑ u ∈ Ico (P.E c) e, ℓr P ℓ u c + Wocc L xmin M ρ nn TT Θ (e - P.E c) :=
  (Pool.P0218.hup_rec P ℓ ω ωs φ hD hLv hlev rc0 c T hgA hfA hgF hfF e hce heT hnr).trans
    (add_le_add le_rfl (widV_le_occ P c hL hxm hxm1 hxr hn hT hM hρ0 hB hρ hx0 hx hΘ fun _ => le_rfl))

end Pool.P0222
