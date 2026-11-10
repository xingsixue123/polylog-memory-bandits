import Pool.P0185.DZCount
import Pool.P0181.Proc

/-!
# The in-law step for `dzRun` when the retirement rule reads EXTERNAL coin information

P0176/P0185's in-law step and bad-point count are stated for a FIXED retirement rule. In the round-level processes
(P0181, P0194) the rule (b″) reads BASE's estimate `B̂`, which depends on the round coins. Here every unit draws a coin
`y : Y` (weight `μ`); the pool sees only its slot part `zOf y`, and the rule reads only an "external" part `ext y`
(e.g. whether the round is a BASE round, and BASE's coins), through a rule family `rhX e` that is causal in the
external history `e`. If the blockwise slot permutations of P0176 act on `Y`, preserving `μ` and `ext` and acting on
`zOf` as `permRT`, then the entry-order run and the copy-last run have the same law, exactly as for a fixed rule.
-/

namespace Pool.P0200

open Finset Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0156 Pool.P0176

section Congr

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ)
  (ℓr : ℕ → ι → ℝ) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

/-- **Causality in the rule.** `dzRun` at unit `a` reads the rule only at units `< a`. -/
theorem dzRun_congr_rh (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (z : ℕ → Fin B → RT D sl)
    {rh rh' : ℕ → ι → (ℕ → ℝ) → Bool} : ∀ a, (∀ a' < a, rh a' = rh' a') →
      dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a =
        dzRun Lv sl B Bm xr ℓr rh' E thr0 θ R K Bt lev lay z ωs φ a := by
  intro a h
  unfold dzRun
  refine Pool.P0181.gRun_congr_upd E thr0 θ R K D Lv Bt lev ∅ ωs φ a fun a' ha' => ?_
  funext sp est ret
  simp only [dzUpd, dzUpdO, h a' ha']

end Congr

section Law

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ)
  (ℓr : ℕ → ι → ℝ) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
  {Y X : Type} (zOf : Y → Fin B → RT D sl) (ext : Y → X) (xd : X)
  (rhX : (ℕ → X) → ℕ → ι → (ℕ → ℝ) → Bool)

/-- A rule family is causal when the rule at unit `a` reads the external history only at units `≤ a`. -/
def Causal : Prop := ∀ e e' : ℕ → X, ∀ a, (∀ v ≤ a, e v = e' v) → rhX e a = rhX e' a

/-- The external history of finitely many unit coins (`xd` after them). -/
def extE {T : ℕ} (ω : Fin T → Y) : ℕ → X := fun u => if h : u < T then ext (ω ⟨u, h⟩) else xd

/-- The slot coins of finitely many unit coins (non-slot rounds after them). -/
def zE {T : ℕ} (ω : Fin T → Y) : ℕ → Fin B → RT D sl := extZ sl B (fun u => zOf (ω u))

/-- The extended step: the trajectory step of P0176 with the rule of the external history so far, which it records. -/
noncomputable def stX (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (u : ℕ)
    (st : (ℕ → GSt ι (Finset ι)) × (ℕ → X)) (y : Y) : (ℕ → GSt ι (Finset ι)) × (ℕ → X) :=
  (trStepD Lv sl B Bm xr ℓr (rhX (Function.update st.2 u (ext y))) E thr0 θ R K Bt lev ωs φ lay u st.1 (zOf y),
   Function.update st.2 u (ext y))

theorem extE_snoc_eq {T : ℕ} (ω : Fin (T + 1) → Y) :
    Function.update (extE ext xd (Fin.init ω)) T (ext (ω (Fin.last T))) = extE ext xd ω := by
  funext u
  rcases lt_trichotomy u T with h | h | h
  · rw [Function.update_of_ne (by omega)]
    simp only [extE, dif_pos h, dif_pos (show u < T + 1 by omega)]
    rfl
  · subst h
    rw [Function.update_self]
    simp only [extE, dif_pos (show u < u + 1 by omega)]
    rfl
  · rw [Function.update_of_ne (by omega)]
    simp only [extE, dif_neg (show ¬ u < T by omega), dif_neg (show ¬ u < T + 1 by omega)]

theorem extE_init_agree {T : ℕ} (ω : Fin (T + 1) → Y) : ∀ v < T, extE ext xd (Fin.init ω) v = extE ext xd ω v := by
  intro v hv
  simp only [extE, dif_pos hv, dif_pos (show v < T + 1 by omega)]
  rfl

/-- **Identification.** The extended run records the external history and its trajectory is `dzRun` with the rule
of the whole external history. -/
theorem run_stX (hc : Causal rhX) (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) :
    ∀ (T : ℕ) (ω : Fin T → Y),
      (Pool.P0070.run (stX Lv sl B Bm xr ℓr E thr0 θ R K Bt lev ωs φ zOf ext rhX lay) (tr0D, fun _ => xd) T ω).2 =
        extE ext xd ω ∧
      ∀ a, (Pool.P0070.run (stX Lv sl B Bm xr ℓr E thr0 θ R K Bt lev ωs φ zOf ext rhX lay) (tr0D, fun _ => xd) T ω).1 a =
        dzRun Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev lay (zE sl B zOf ω) ωs φ (min a T)
  | 0, ω => by
    refine ⟨?_, fun a => ?_⟩
    · funext u; simp [Pool.P0070.run, extE]
    · simp only [Pool.P0070.run, Nat.min_zero]; rfl
  | T + 1, ω => by
    obtain ⟨ih2, ih1⟩ := run_stX hc lay T (Fin.init ω)
    have hrule : rhX (Function.update (Pool.P0070.run (stX Lv sl B Bm xr ℓr E thr0 θ R K Bt lev ωs φ zOf ext rhX lay)
        (tr0D, fun _ => xd) T (Fin.init ω)).2 T (ext (ω (Fin.last T)))) = rhX (extE ext xd ω) := by
      rw [ih2, extE_snoc_eq]
    have hcongr : ∀ b ≤ T, dzRun Lv sl B Bm xr ℓr (rhX (extE ext xd (Fin.init ω))) E thr0 θ R K Bt lev lay
        (zE sl B zOf (Fin.init ω)) ωs φ b =
        dzRun Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev lay (zE sl B zOf ω) ωs φ b := by
      intro b hb
      rw [dzRun_congr_z Lv sl B Bm xr ℓr _ E thr0 θ R K Bt lev ωs φ lay b
        (z' := zE sl B zOf ω) (fun v hv => by
          unfold zE
          exact extZ_init sl B (fun u => zOf (ω u)) v (by omega))]
      exact dzRun_congr_rh Lv sl B Bm xr ℓr E thr0 θ R K Bt lev ωs φ lay _ b fun a' ha' =>
        hc _ _ a' fun v hv => extE_init_agree ext xd ω v (by omega)
    refine ⟨?_, fun a => ?_⟩
    · show Function.update _ T _ = _
      rw [ih2, extE_snoc_eq]
    · show trStepD Lv sl B Bm xr ℓr (rhX (Function.update _ T (ext (ω (Fin.last T))))) E thr0 θ R K Bt lev ωs φ lay T
        _ (zOf (ω (Fin.last T))) a = _
      rw [hrule]
      simp only [trStepD]
      split_ifs with ha
      · rw [ih1 a, hcongr _ (by omega)]
        congr 1; omega
      · rw [ih1 T, Nat.min_self, hcongr T le_rfl, show min a (T + 1) = T + 1 by omega, dzRun_succ_obs]
        congr 2
        unfold zE
        rw [extZ_last]

variable [Fintype Y] (μ : Y → ℝ)

/-- A slot-permutation action on the unit coins that is compatible with the slot part, the external part and the
weights. -/
structure PermAct (zOf : Y → Fin B → RT D sl) (ext : Y → X) (μ : Y → ℝ) where
  act : ((j : Fin D) → Equiv.Perm (Fin (sl j))) → Equiv.Perm Y
  zOf_act : ∀ τ y, zOf (act τ y) = fun t => permRT sl τ (zOf y t)
  ext_act : ∀ τ y, ext (act τ y) = ext y
  μ_act : ∀ τ y, μ (act τ y) = μ y

/-- **Same law for blockwise-compatible layouts, with an external-reading rule.** -/
theorem trajX_law (hc : Causal rhX) (A : PermAct sl B zOf ext μ)
    (layA layB : (j : Fin D) → Finset ι → Fin (sl j) → Option ι)
    (hcomp : ∀ (j : Fin D) (V : Finset ι), Pool.P0070.Compat (layA j V) (layB j V))
    (T : ℕ) (f : (ℕ → GSt ι (Finset ι)) → ℝ) :
    ∑ ω : Fin T → Y, Pool.P0070.wR μ ω *
        f (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ layB T (zE sl B zOf ω)) =
      ∑ ω : Fin T → Y, Pool.P0070.wR μ ω *
        f (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ layA T (zE sl B zOf ω)) := by
  have hrun : ∀ (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (ω : Fin T → Y),
      trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ lay T (zE sl B zOf ω) =
        (Pool.P0070.run (stX Lv sl B Bm xr ℓr E thr0 θ R K Bt lev ωs φ zOf ext rhX lay) (tr0D, fun _ => xd) T ω).1 := by
    intro lay ω; funext a
    exact ((run_stX Lv sl B Bm xr ℓr E thr0 θ R K Bt lev ωs φ zOf ext xd rhX hc lay T ω).2 a).symm
  simp only [hrun]
  choose τ hτ using fun (p : (j : Fin D) × Finset ι) => Pool.P0070.exists_perm (layA p.1 p.2) (layB p.1 p.2) (hcomp p.1 p.2)
  let τs : (ℕ → ℕ → Finset ι) → (j : Fin D) → Equiv.Perm (Fin (sl j)) := fun sp j => τ ⟨j, blockMem Lv sp j⟩
  let σ : ℕ → (ℕ → GSt ι (Finset ι)) × (ℕ → X) → Equiv.Perm Y := fun u st =>
    A.act (τs (startPools E thr0 D Lv Bt ωs u (st.1 u).pools))
  refine Pool.P0070.sum_run_eq μ _ _ (tr0D, fun _ => xd) σ ?_ (fun u st y => A.μ_act _ y) T (fun st => f st.1)
  intro u st y
  simp only [stX, σ, A.ext_act]
  congr 1
  funext a
  simp only [trStepD]
  split_ifs
  · rfl
  · congr 1
    funext t
    rw [A.zOf_act]
    exact (obsR_perm Lv sl layA layB _ _ (fun j k => hτ ⟨j, _⟩ k) (zOf y t)).symm

open Classical Pool.P0111 in
/-- **The in-law step with an external-reading rule** (P0176's `law_sort_last_DZ` when the rule reads `ext`). -/
theorem law_sort_last_X (hc : Causal rhX) (A : PermAct sl B zOf ext μ) (c : ι) (T : ℕ)
    (G : (ℕ → GSt ι (Finset ι)) → Prop) :
    ∑ ω : Fin T → Y, Pool.P0070.wR μ ω *
        (if NoOverflowD Lv sl E thr0 Bt ωs T
              (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ (sortLay sl) T (zE sl B zOf ω)) ∧
            G (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ (sortLay sl) T (zE sl B zOf ω))
          then 1 else 0) =
      ∑ ω : Fin T → Y, Pool.P0070.wR μ ω *
        (if NoOverflowD Lv sl E thr0 Bt ωs T
              (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ (lastLay sl c) T (zE sl B zOf ω)) ∧
            G (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ (lastLay sl c) T (zE sl B zOf ω))
          then 1 else 0) := by
  set f : (ℕ → GSt ι (Finset ι)) → ℝ := fun tr => if NoOverflowD Lv sl E thr0 Bt ωs T tr ∧ G tr then 1 else 0
    with hf
  have hcap : ∀ (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (ω : Fin T → Y),
      f (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ (capLay sl lay) T (zE sl B zOf ω)) =
        f (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ lay T (zE sl B zOf ω)) := by
    intro lay ω
    obtain ⟨hiff, heq⟩ := trajD_cap Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ lay T
      (zE sl B zOf ω)
    by_cases h : NoOverflowD Lv sl E thr0 Bt ωs T
      (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ lay T (zE sl B zOf ω))
    · rw [heq h]
    · have h1 : ¬ (NoOverflowD Lv sl E thr0 Bt ωs T
          (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ (capLay sl lay) T (zE sl B zOf ω)) ∧
          G (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ (capLay sl lay) T
            (zE sl B zOf ω))) := fun h' => h (hiff.mp h'.1)
      have h2 : ¬ (NoOverflowD Lv sl E thr0 Bt ωs T
          (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ lay T (zE sl B zOf ω)) ∧
          G (trajD Lv sl B Bm xr ℓr (rhX (extE ext xd ω)) E thr0 θ R K Bt lev ωs φ lay T (zE sl B zOf ω))) :=
        fun h' => h h'.1
      simp only [hf, if_neg h1, if_neg h2]
  have hlaw := trajX_law Lv sl B Bm xr ℓr E thr0 θ R K Bt lev ωs φ (zOf := zOf) (ext := ext) (xd := xd) (rhX := rhX) (μ := μ) hc A
    (capLay sl (lastLay sl c)) (capLay sl (sortLay sl)) (fun j V => compat_cap (sl j) c V) T f
  simp only [hcap] at hlaw
  exact hlaw

end Law

end Pool.P0200
