import Pool.P0250.WalkParam
import Pool.P0259.LevelSplit

/-!
# Horizon congruence of P0186's walk outcomes, and P0250's bad counts as P0259's prefix counts `nbR`

P0156's run up to `T` reads its update only before `T` (`gRun_congr_upd`), hence so do P0186's mixed outcomes
(`outMix_congr`). On the extension of a `T`-coin prefix, P0194's rule and slot coins agree before `T` with P0207's
prefix forms (`rh_z_agree`), so P0250's `nbad` is P0259's `nbR` (entry-order layout, schedule `levTh Ld`;
`nbad_eq_nbR`).
-/

namespace Pool.P0266

open Finset Pool.P0156

section Congr

variable {ι : Type*} [LinearOrder ι] [Fintype ι] {σ : Type*} (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (aux0 : σ)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

/-- **P0156's run up to `T` reads the update only before `T`.** -/
theorem gRun_congr_upd {upd upd' : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → σ → (ι → ℝ) × σ} {T : ℕ}
    (h : ∀ u, u < T → upd u = upd' u) :
    ∀ a, a ≤ T → gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a = gRun E thr0 θ R K D Lv Bt lev upd' aux0 ωs φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro ha
    have hIH := ih (by omega)
    have hu := h a (by omega)
    rw [gRun, gRun, hIH, hu]

end Congr

section Out

open Pool.P0186 Pool.P0168 Pool.P0065

variable {ι : Type*} [LinearOrder ι] [Fintype ι] (E : ι → ℕ) (thr0 : ι → ℕ) (θ : ℝ)
  (R K D Lv : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ) (aux0 : Finset ι)

theorem find_congr {p q : ℕ → Prop} {dp : DecidablePred p} {dq : DecidablePred q} {ep : Decidable (∃ y, p y)}
    {eq : Decidable (∃ y, q y)} (h : p = q) :
    (if hp : ∃ y, p y then some (Nat.find hp) else none) = (if hq : ∃ y, q y then some (Nat.find hq) else none) := by
  subst h
  have h1 : dp = dq := Subsingleton.elim _ _
  have h2 : ep = eq := Subsingleton.elim _ _
  subst h1; subst h2; rfl

variable {upd upd' : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι} {T : ℕ}

theorem aRet_congr (h : ∀ u, u < T → upd u = upd' u) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) :
    aRet E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = aRet E thr0 θ R K D Lv Bt lev upd' aux0 T ωs φ c := by
  unfold aRet
  refine find_congr (funext fun y => propext (and_congr_right fun _ => ?_))
  constructor
  · rintro ⟨h2, h3⟩; refine ⟨h2, ?_⟩; rwa [← gRun_congr_upd E thr0 θ R K D Lv Bt lev aux0 ωs φ h y h2]
  · rintro ⟨h2, h3⟩; refine ⟨h2, ?_⟩; rwa [gRun_congr_upd E thr0 θ R K D Lv Bt lev aux0 ωs φ h y h2]

theorem aRem_congr (h : ∀ u, u < T → upd u = upd' u) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) :
    aRem E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = aRem E thr0 θ R K D Lv Bt lev upd' aux0 T ωs φ c := by
  unfold aRem
  refine find_congr (funext fun y => propext (and_congr_right fun _ => ?_))
  constructor
  · rintro ⟨h2, h3⟩; refine ⟨h2, ?_⟩; rwa [← gRun_congr_upd E thr0 θ R K D Lv Bt lev aux0 ωs φ h y h2]
  · rintro ⟨h2, h3⟩; refine ⟨h2, ?_⟩; rwa [gRun_congr_upd E thr0 θ R K D Lv Bt lev aux0 ωs φ h y h2]

theorem retT_congr (h : ∀ u, u < T → upd u = upd' u) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) :
    retT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = retT E thr0 θ R K D Lv Bt lev upd' aux0 T ωs φ c := by
  unfold retT fRun
  refine find_congr (funext fun y => propext (and_congr_right fun _ => ?_))
  constructor
  · rintro ⟨h2, h3⟩; refine ⟨h2, ?_⟩; rwa [← gRun_congr_upd E thr0 θ R K D Lv Bt lev aux0 _ _ h y h2]
  · rintro ⟨h2, h3⟩; refine ⟨h2, ?_⟩; rwa [gRun_congr_upd E thr0 θ R K D Lv Bt lev aux0 _ _ h y h2]

theorem remT_congr (h : ∀ u, u < T → upd u = upd' u) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) :
    remT E thr0 θ R K D Lv Bt lev upd aux0 T ωs φ c = remT E thr0 θ R K D Lv Bt lev upd' aux0 T ωs φ c := by
  unfold remT fRun
  refine find_congr (funext fun y => propext (and_congr_right fun _ => ?_))
  constructor
  · rintro ⟨h2, h3⟩; refine ⟨h2, ?_⟩; rwa [← gRun_congr_upd E thr0 θ R K D Lv Bt lev aux0 _ _ h y h2]
  · rintro ⟨h2, h3⟩; refine ⟨h2, ?_⟩; rwa [gRun_congr_upd E thr0 θ R K D Lv Bt lev aux0 _ _ h y h2]

/-- **P0186's mixed outcomes read the updates only before the horizon.** -/
theorem outMix_congr {U U' : ι → ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι}
    (h : ∀ u, u < T → upd u = upd' u) (hU : ∀ c u, u < T → U c u = U' c u) (A : ι → Finset ι) (jmax : ℕ)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (c : ι) :
    outMix E thr0 θ R K D Lv Bt lev upd aux0 U A jmax T ωs φ c =
      outMix E thr0 θ R K D Lv Bt lev upd' aux0 U' A jmax T ωs φ c := by
  unfold outMix outA outZ
  rw [aRet_congr E thr0 θ R K D Lv Bt lev aux0 h, aRem_congr E thr0 θ R K D Lv Bt lev aux0 h,
    retT_congr E thr0 θ R K D Lv Bt lev (A c) (hU c), remT_congr E thr0 θ R K D Lv Bt lev (A c) (hU c)]

end Out

section Bridge

open Pool.P0194 Pool.P0212 Pool.P0176 Pool.P0200 Pool.P0186

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ)
  (ℓ : Pool.P0001.LossSeq n) (ωs : ι → Bool)
  (φ : ℕ → ℕ → ℕ → Fin (Pool.P0225.withAlgG P η L N G γ wE ρG).K → ι → Bool) (T : ℕ)
  (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

local notation "QQ" => Pool.P0225.withAlgG P η L N G γ wE ρG

/-- `dzUpd` at unit `a` reads the rule and the slot coins only at `a`. -/
theorem dzUpd_congr {D Lv B : ℕ} {sl : Fin D → ℕ} {Bm : ℝ} {xr : Fin D → ℝ} {ℓr : ℕ → ι → ℝ}
    {rh rh' : ℕ → ι → (ℕ → ℝ) → Bool} (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι)
    {z z' : ℕ → Fin B → RT D sl} (a : ℕ) (hrh : rh a = rh' a) (hz : z a = z' a) :
    dzUpd D Lv sl B Bm xr ℓr rh lay z a = dzUpd D Lv sl B Bm xr ℓr rh' lay z' a := by
  unfold dzUpd dzUpdO
  rw [hrh, hz]

/-- On the extension of a `T`-prefix, P0194's rule and slot coins agree with P0207's prefix forms before `T`. -/
theorem rh_z_agree (yy : Fin T → RC (QQ)) (u : ℕ) (hu : u < T) :
    rhD (QQ) ℓ (Pool.P0210.extR (QQ) rc0 yy) u =
      Pool.P0207.rhXR (QQ) ℓ (extE (Pool.P0207.extR (QQ)) none yy) u ∧
    zc (QQ) (Pool.P0210.extR (QQ) rc0 yy) u = zE (QQ).sl 1 (Pool.P0207.zOfR (QQ)) yy u := by
  constructor
  · rw [Pool.P0207.rhD_eq]
    exact Pool.P0207.causal_rhXR (QQ) ℓ _ _ u fun v hv => by
      simp only [extE, Pool.P0210.extR, dif_pos (show v < T by omega)]
  · funext t
    simp only [zc, zE, extZ, Pool.P0210.extR, dif_pos hu, Pool.P0207.zOfR]

/-- **P0250's bad counts are P0207's prefix counts** (entry-order layout, schedule `levTh Ld`): on the extension of a
`T`-prefix `yy`, P0250's `nbad` equals P0135's `nBadB` of the runs with P0207's prefix rule `rhXR` and slot coins `zE`
(the form of P0207's `count_bad_round` / `exp_walkRHS_round` with `NE = T`). -/
theorem nbad_eq_round {Ld : ℕ} (hlay : (QQ).lay = sortLay (QQ).sl) (hlev : (QQ).lev = Pool.P0085.levTh Ld (QQ).Bt)
    (cstar : ℕ → ℕ → ι) (yy : Fin T → RC (QQ)) (j : ℕ) :
    Pool.P0250.nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 yy) ωs φ T cstar j =
      (Pool.P0135.nBadB T (QQ).Bt (fun τ r => outMix (QQ).E (QQ).thr0 (QQ).θ (QQ).R (QQ).K (QQ).D (QQ).Lv (QQ).Bt
        (Pool.P0085.levTh Ld (QQ).Bt)
        (dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (QQ) ℓ)
          (Pool.P0207.rhXR (QQ) ℓ (extE (Pool.P0207.extR (QQ)) none yy)) (sortLay (QQ).sl)
          (zE (QQ).sl 1 (Pool.P0207.zOfR (QQ)) yy)) ∅
        (fun c' => dzUpd (QQ).D (QQ).Lv (QQ).sl 1 1 (QQ).xr (ℓr (QQ) ℓ)
          (Pool.P0207.rhXR (QQ) ℓ (extE (Pool.P0207.extR (QQ)) none yy)) (lastLay (QQ).sl c')
          (zE (QQ).sl 1 (Pool.P0207.zOfR (QQ)) yy))
        (fun _ => ∅) ((QQ).D - 1) T ωs φ (cstar r τ)) j : ℝ) := by
  unfold Pool.P0250.nbad
  rw [hlay, hlev]
  congr 2
  funext τ r
  refine outMix_congr _ _ _ _ _ _ _ _ _ _ (fun u hu => ?_) (fun c u hu => ?_) _ _ _ _ _
  · obtain ⟨h1, h2⟩ := rh_z_agree P η L N G γ wE ρG ℓ T rc0 yy u hu
    exact dzUpd_congr _ u h1 h2
  · obtain ⟨h1, h2⟩ := rh_z_agree P η L N G γ wE ρG ℓ T rc0 yy u hu
    exact dzUpd_congr _ u h1 h2

end Bridge

section NbR

open Pool.P0194 Pool.P0212 Pool.P0176 Pool.P0200 Pool.P0186

variable {n : ℕ} {ι : Type} [LinearOrder ι] [Fintype ι]
  (P : ParD n ι) (η : ℝ) (L N G : ℕ) (γ wE : ℝ) (ρG : AState ι → Finset ι → Option ι → Bool → ℝ)
  (ℓ : Pool.P0001.LossSeq n) (T : ℕ) (rc0 : RC (Pool.P0225.withAlgG P η L N G γ wE ρG))

local notation "QQ" => Pool.P0225.withAlgG P η L N G γ wE ρG

/-- **P0250's `nbad` on the array's sampling/filter bits is P0259's `nbR`** (entry-order layout, schedule `levTh Ld`). -/
theorem nbad_eq_nbR {Ld Lf : ℕ} (hlay : (QQ).lay = sortLay (QQ).sl) (hlev : (QQ).lev = Pool.P0085.levTh Ld (QQ).Bt)
    (cstar : ℕ → ℕ → ι) (arr : Pool.P0082.SlotC T (QQ).D Lf (QQ).K × ι → Bool) (yy : Fin T → RC (QQ)) (j : ℕ) :
    Pool.P0250.nbad P η L N G γ wE ρG ℓ (Pool.P0210.extR (QQ) rc0 yy) (Pool.P0082.ωsC (QQ).E T (QQ).D Lf (QQ).K arr)
        (Pool.P0082.φC T (QQ).D Lf (QQ).K arr) T cstar j =
      (Pool.P0259.nbR (QQ) ℓ Ld T Lf cstar arr yy j : ℝ) :=
  nbad_eq_round P η L N G γ wE ρG ℓ _ _ T rc0 hlay hlev cstar yy j

end NbR

end Pool.P0266
