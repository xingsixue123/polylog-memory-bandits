import Pool.P0164.ZCount

/-!
# Design Z's member process with per-thread slots, several slot rounds per unit, and retirement (P0166 §2)

The unit is a block of `B` rounds. Each round's type is one coin `RT = Option (Σ j, Fin (sl j))`: `none` (a round that
is not a slot round: exploitation or BASE) or `some ⟨j, k⟩` (slot `k` of thread `j`). On a slot round the occupant of
slot `k` in thread `j`'s layout is observed; its unit increment gains `ℓ/x_j`. A retired copy gains a fake `Bm` per
unit. At unit ends, P0065's merges run on the data (P0156's generic `gRun`), and copies retire by `rh`.

* Process: `RT`, `blockMem`, `obsR`, `dzC`, `dzIncO`, `dzUpdO`, `dzUpd`, **`dzRun`**.
* In-law step (P0150's N1 / P0166's C4′): `Vblk`, `obsU`, `dzStepO`, `dzRun_succ_obs`, `dzRun_congr_z`, `extZ`,
  `trStepD`, `tr0D`, `run_trStepD`, `wRT`, `wU`, `permRT`, `wRT_perm`, `obsR_perm`, **`trajD_law`** (blockwise-compatible
  layouts give the same trajectory law under independent rounds with per-thread weights `x_j`), `capLay`, `sortLay`,
  `lastLay`, `Fits`, `obsU_cap`, `dzRun_cap_eq`, `dzRun_cap_eq'`, `NoOverflowD`, `trajD`, `trajD_cap`,
  **`law_sort_last_DZ`**.
* Coupling: `blockMem_erase`, `dzC_congr`, `obsR_last_erase`, **`dz_forced_erase`**, `dz_not_mem_members_free`,
  `mem_blockMem_members`, **`dz_free_eq`**.
* Sizes: `dzC_bounds`, `dzInc_bounds`, **`prob_members_large_DZ`**.
-/

namespace Pool.P0176

open Finset Pool.P0095 Pool.P0065 Pool.P0052 Pool.P0156

section Def

variable {ι : Type} [LinearOrder ι] [Fintype ι] (D Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ)

/-- The round types. -/
abbrev RT := Option (Σ j : Fin D, Fin (sl j))

/-- The members of thread `j` in pools `sp`. -/
def blockMem (sp : ℕ → ℕ → Finset ι) (j : ℕ) : Finset ι := (Finset.range Lv).biUnion (sp j)

/-- The observation of one round: the thread and the occupant of the drawn slot, if any. -/
def obsR (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (sp : ℕ → ℕ → Finset ι) :
    RT D sl → Option (Fin D × ι)
  | none => none
  | some ⟨j, k⟩ => (lay j (blockMem Lv sp j) k).map fun x => (j, x)

variable (Bm : ℝ) (xr : Fin D → ℝ) (ℓr : ℕ → ι → ℝ)

/-- The contribution of one round's observation to copy `x`'s unit increment. -/
noncomputable def dzC (a : ℕ) (x : ι) (t : Fin B) : Option (Fin D × ι) → ℝ
  | none => 0
  | some (j, y) => if y = x then ℓr (a * B + t) x / xr j else 0

/-- The unit increments given the round observations `o`. A retired copy gains the fake `Bm` per unit; a unit has `B`
rounds, so the retired-segment domination of P0156/P0160 (fake data ≥ ALG's loss) needs `Bm ≥ B` (e.g. `Bm = B`),
which this file does not assume. -/
noncomputable def dzIncO (a : ℕ) (ret : Finset ι) (o : Fin B → Option (Fin D × ι)) : ι → ℝ :=
  fun x => if x ∈ ret then Bm else ∑ t : Fin B, dzC D B xr ℓr a x t (o t)

variable (rh : ℕ → ι → (ℕ → ℝ) → Bool)

/-- The update given the round observations. -/
noncomputable def dzUpdO (a : ℕ) (sp : ℕ → ℕ → Finset ι) (est : ι → ℕ → ℝ) (ret : Finset ι)
    (o : Fin B → Option (Fin D × ι)) : (ι → ℝ) × Finset ι :=
  (dzIncO D B Bm xr ℓr a ret o,
   ret ∪ (members D Lv sp).filter (fun x => rh a x (gStep a (dzIncO D B Bm xr ℓr a ret o) est x) = true))

/-- The update with layout `lay` and unit coins `z`. -/
noncomputable def dzUpd (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (z : ℕ → Fin B → RT D sl) :
    ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → Finset ι → (ι → ℝ) × Finset ι :=
  fun a sp est ret => dzUpdO D Lv B Bm xr ℓr rh a sp est ret (fun t => obsR D Lv sl lay sp (z a t))

variable {D} (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ) (lev : ℕ → ℕ → ℕ)

/-- **Design Z's member process** (data/pool side): P0156's generic process with `dzUpd`. -/
noncomputable abbrev dzRun (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (z : ℕ → Fin B → RT D sl)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) : ℕ → GSt ι (Finset ι) :=
  gRun E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh lay z) ∅ ωs φ

end Def


section Law

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ)
  (ℓr : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

/-- The start-pool members of thread `j` in unit `a`. -/
noncomputable def Vblk (a : ℕ) (st : GSt ι (Finset ι)) (j : ℕ) : Finset ι :=
  blockMem Lv (startPools E thr0 D Lv Bt ωs a st.pools) j

/-- The observations of a unit, given its coins. -/
noncomputable def obsU (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (sp : ℕ → ℕ → Finset ι)
    (zc : Fin B → RT D sl) : Fin B → Option (Fin D × ι) :=
  fun t => obsR D Lv sl lay sp (zc t)

/-- One unit, given its observations. -/
noncomputable def dzStepO (a : ℕ) (st : GSt ι (Finset ι)) (o : Fin B → Option (Fin D × ι)) : GSt ι (Finset ι) :=
  ⟨fun r => if Bt r ∣ a + 1 then
      mergeUpTo E (gStep a (dzUpdO D Lv B Bm xr ℓr rh a (startPools E thr0 D Lv Bt ωs a st.pools) st.est st.aux o).1
        st.est) θ R K (φ r) a (lev r a) (startPools E thr0 D Lv Bt ωs a st.pools r)
    else startPools E thr0 D Lv Bt ωs a st.pools r,
   gStep a (dzUpdO D Lv B Bm xr ℓr rh a (startPools E thr0 D Lv Bt ωs a st.pools) st.est st.aux o).1 st.est,
   (dzUpdO D Lv B Bm xr ℓr rh a (startPools E thr0 D Lv Bt ωs a st.pools) st.est st.aux o).2⟩

theorem dzRun_succ_obs (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (z : ℕ → Fin B → RT D sl) (a : ℕ) :
    dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ (a + 1) =
      dzStepO Lv B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ a (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a)
        (obsU Lv sl B lay (startPools E thr0 D Lv Bt ωs a
          (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a).pools) (z a)) := rfl

/-- **Causality in the unit coins.** -/
theorem dzRun_congr_z (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) {z z' : ℕ → Fin B → RT D sl} :
    ∀ a, (∀ v < a, z v = z' v) →
      dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a =
        dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z' ωs φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    rw [dzRun_succ_obs, dzRun_succ_obs, ih (fun v hv => h v (by omega)), h a (by omega)]

/-- Unit coins of the first `T` units, extended by non-slot rounds. -/
def extZ {T : ℕ} (ω : Fin T → Fin B → RT D sl) : ℕ → Fin B → RT D sl :=
  fun u => if h : u < T then ω ⟨u, h⟩ else fun _ => none

theorem extZ_init {T : ℕ} (ω : Fin (T + 1) → Fin B → RT D sl) : ∀ v < T, extZ sl B (Fin.init ω) v = extZ sl B ω v := by
  intro v hv
  simp only [extZ, dif_pos hv, dif_pos (show v < T + 1 by omega)]
  rfl

theorem extZ_last {T : ℕ} (ω : Fin (T + 1) → Fin B → RT D sl) : extZ sl B ω T = ω (Fin.last T) := by
  simp [extZ, Fin.last]

/-- The trajectory step. -/
noncomputable def trStepD (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (u : ℕ) (tr : ℕ → GSt ι (Finset ι))
    (zc : Fin B → RT D sl) : ℕ → GSt ι (Finset ι) :=
  fun a => if a ≤ u then tr a else
    dzStepO Lv B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ u (tr u)
      (obsU Lv sl B lay (startPools E thr0 D Lv Bt ωs u (tr u).pools) zc)

/-- The initial trajectory. -/
def tr0D : ℕ → GSt ι (Finset ι) := fun _ => ⟨fun _ _ => ∅, fun _ _ => 0, ∅⟩

theorem run_trStepD (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) :
    ∀ (T : ℕ) (ω : Fin T → Fin B → RT D sl) (a : ℕ),
    Pool.P0070.run (trStepD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay) tr0D T ω a =
      dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay (extZ sl B ω) ωs φ (min a T)
  | 0, ω, a => by simp only [Pool.P0070.run, Nat.min_zero]; rfl
  | T + 1, ω, a => by
    have hc : ∀ b ≤ T, dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay (extZ sl B (Fin.init ω)) ωs φ b =
        dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay (extZ sl B ω) ωs φ b := fun b hb =>
      dzRun_congr_z Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay b (fun v hv => extZ_init sl B ω v (by omega))
    simp only [Pool.P0070.run, trStepD]
    split_ifs with ha
    · rw [run_trStepD lay T (Fin.init ω) a, hc _ (by omega)]
      congr 1; omega
    · rw [run_trStepD lay T (Fin.init ω) T, Nat.min_self, hc T le_rfl, show min a (T + 1) = T + 1 by omega,
        dzRun_succ_obs, extZ_last]

/-- The round weights: `x_j` for each slot of thread `j`, `w0` for a non-slot round. -/
def wRT (w0 : ℝ) : RT D sl → ℝ
  | none => w0
  | some ⟨j, _⟩ => xr j

/-- The unit weight: independent rounds. -/
noncomputable def wU (w0 : ℝ) (zc : Fin B → RT D sl) : ℝ := ∏ t, wRT sl xr w0 (zc t)

/-- A permutation of the slots of every thread, acting on round types. -/
def permRT (τ : (j : Fin D) → Equiv.Perm (Fin (sl j))) : Equiv.Perm (RT D sl) :=
  Equiv.optionCongr (Equiv.sigmaCongrRight τ)

theorem wRT_perm (w0 : ℝ) (τ : (j : Fin D) → Equiv.Perm (Fin (sl j))) (r : RT D sl) :
    wRT sl xr w0 (permRT sl τ r) = wRT sl xr w0 r := by
  rcases r with _ | ⟨j, k⟩ <;> rfl

theorem obsR_perm (layA layB : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (sp : ℕ → ℕ → Finset ι)
    (τ : (j : Fin D) → Equiv.Perm (Fin (sl j))) (h : ∀ j k, layA j (blockMem Lv sp j) (τ j k) = layB j (blockMem Lv sp j) k)
    (r : RT D sl) : obsR D Lv sl layA sp (permRT sl τ r) = obsR D Lv sl layB sp r := by
  rcases r with _ | ⟨j, k⟩
  · rfl
  · show (layA j (blockMem Lv sp j) (τ j k)).map _ = (layB j (blockMem Lv sp j) k).map _
    rw [h j k]

/-- **Same law for blockwise-compatible layouts.** If at every member configuration the two layouts differ, within
each thread, by a permutation of that thread's slots, the trajectories up to `T` have the same law under independent
rounds with weights `wRT`. -/
theorem trajD_law (w0 : ℝ) (layA layB : (j : Fin D) → Finset ι → Fin (sl j) → Option ι)
    (hc : ∀ (j : Fin D) (V : Finset ι), Pool.P0070.Compat (layA j V) (layB j V))
    (T : ℕ) (f : (ℕ → GSt ι (Finset ι)) → ℝ) :
    ∑ ω : Fin T → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) ω *
        f (Pool.P0070.run (trStepD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ layB) tr0D T ω) =
      ∑ ω : Fin T → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) ω *
        f (Pool.P0070.run (trStepD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ layA) tr0D T ω) := by
  choose τ hτ using fun (p : (j : Fin D) × Finset ι) => Pool.P0070.exists_perm (layA p.1 p.2) (layB p.1 p.2) (hc p.1 p.2)
  let τs : (ℕ → ℕ → Finset ι) → (j : Fin D) → Equiv.Perm (Fin (sl j)) := fun sp j => τ ⟨j, blockMem Lv sp j⟩
  let σ : ℕ → (ℕ → GSt ι (Finset ι)) → Equiv.Perm (Fin B → RT D sl) := fun u tr =>
    Equiv.piCongrRight fun _ => permRT sl (τs (startPools E thr0 D Lv Bt ωs u (tr u).pools))
  refine Pool.P0070.sum_run_eq _ _ _ tr0D σ ?_ ?_ T f
  · intro u tr zc
    funext a
    simp only [trStepD]
    split_ifs
    · rfl
    · congr 1
      funext t
      exact (obsR_perm Lv sl layA layB _ _ (fun j k => hτ ⟨j, _⟩ k) (zc t)).symm
  · intro u tr zc
    unfold wU
    refine Finset.prod_congr rfl fun t _ => ?_
    exact wRT_perm sl xr w0 _ (zc t)

end Law

section Cap

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ)
  (ℓr : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

/-- The capped layout: a thread whose members do not fit in its slots observes nothing. -/
def capLay (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) : (j : Fin D) → Finset ι → Fin (sl j) → Option ι :=
  fun j => capOcc (sl j) (lay j)

/-- Every thread lays out its members in the order of the copy type `ι` (P0111's `occSort`): this is entry order
when `ι` is ordered by entry, as for the intended copy type. The law step holds for any order. -/
def sortLay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι := fun j => occSort (sl j)

/-- Copy `c` last within its thread, the other members in the order of `ι` (P0111's `occLast`). -/
def lastLay (c : ι) : (j : Fin D) → Finset ι → Fin (sl j) → Option ι := fun j => occLast (sl j) c

/-- Every thread's members fit in its slots. -/
def Fits (sp : ℕ → ℕ → Finset ι) : Prop := ∀ j : Fin D, (blockMem Lv sp j).card ≤ sl j

theorem obsU_cap (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (sp : ℕ → ℕ → Finset ι)
    (h : Fits Lv sl sp) (zc : Fin B → RT D sl) :
    obsU Lv sl B (capLay sl lay) sp zc = obsU Lv sl B lay sp zc := by
  funext t
  unfold obsU
  rcases zc t with _ | ⟨j, k⟩
  · rfl
  · show ((capOcc (sl j) (lay j)) (blockMem Lv sp j) k).map _ = (lay j (blockMem Lv sp j) k).map _
    simp only [capOcc, if_pos (h j)]

theorem dzRun_cap_eq (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (z : ℕ → Fin B → RT D sl) : ∀ a,
    (∀ u < a, Fits Lv sl (startPools E thr0 D Lv Bt ωs u
      (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ u).pools)) →
    dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (capLay sl lay) z ωs φ a =
      dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    rw [dzRun_succ_obs, dzRun_succ_obs, ih (fun u hu => h u (by omega)), obsU_cap Lv sl B lay _ (h a (by omega))]

theorem dzRun_cap_eq' (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (z : ℕ → Fin B → RT D sl) : ∀ a,
    (∀ u < a, Fits Lv sl (startPools E thr0 D Lv Bt ωs u
      (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (capLay sl lay) z ωs φ u).pools)) →
    dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (capLay sl lay) z ωs φ a =
      dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have ih' := ih (fun u hu => h u (by omega))
    have ha := h a (by omega)
    rw [ih'] at ha
    rw [dzRun_succ_obs, dzRun_succ_obs, ih', obsU_cap Lv sl B lay _ ha]

/-- No thread overflows before `T` along a trajectory. -/
def NoOverflowD (T : ℕ) (tr : ℕ → GSt ι (Finset ι)) : Prop :=
  ∀ u < T, Fits Lv sl (startPools E thr0 D Lv Bt ωs u (tr u).pools)

/-- The trajectory of a run up to `T`. -/
noncomputable def trajD (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (T : ℕ) (z : ℕ → Fin B → RT D sl) :
    ℕ → GSt ι (Finset ι) :=
  fun a => dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ (min a T)

theorem trajD_cap (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (T : ℕ) (z : ℕ → Fin B → RT D sl) :
    (NoOverflowD Lv sl E thr0 Bt ωs T (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (capLay sl lay) T z) ↔
      NoOverflowD Lv sl E thr0 Bt ωs T (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay T z)) ∧
    (NoOverflowD Lv sl E thr0 Bt ωs T (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay T z) →
      trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (capLay sl lay) T z =
        trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay T z) := by
  have hmin : ∀ u < T, min u T = u := fun u hu => Nat.min_eq_left hu.le
  constructor
  · constructor
    · intro h u hu
      have h' : ∀ v < u, Fits Lv sl (startPools E thr0 D Lv Bt ωs v
          (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (capLay sl lay) z ωs φ v).pools) := fun v hv => by
        have := h v (by omega); simp only [trajD, hmin v (by omega)] at this; exact this
      have := h u hu
      simp only [trajD, hmin u hu] at this ⊢
      rwa [dzRun_cap_eq' Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay z u h'] at this
    · intro h u hu
      have h' : ∀ v < u, Fits Lv sl (startPools E thr0 D Lv Bt ωs v
          (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ v).pools) := fun v hv => by
        have := h v (by omega); simp only [trajD, hmin v (by omega)] at this; exact this
      have := h u hu
      simp only [trajD, hmin u hu] at this ⊢
      rwa [dzRun_cap_eq Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay z u h']
  · intro h
    funext a
    simp only [trajD]
    refine dzRun_cap_eq Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay z _ fun u hu => ?_
    have := h u (by omega)
    simp only [trajD, hmin u (by omega)] at this
    exact this

open Classical in
/-- **The in-law step for Design Z's per-thread multi-slot process.** For every copy `c` and every event `G` of the
trajectory up to `T`, under independent rounds (slot `k` of thread `j` with weight `x_j`, non-slot rounds `w0`), the
weight of {no thread overflows before `T` ∧ `G`} is the same for the entry-order layout and the layout with `c` last
within its thread. -/
theorem law_sort_last_DZ (w0 : ℝ) (c : ι) (T : ℕ) (G : (ℕ → GSt ι (Finset ι)) → Prop) :
    ∑ ω : Fin T → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) ω *
        (if NoOverflowD Lv sl E thr0 Bt ωs T
              (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (sortLay sl) T (extZ sl B ω)) ∧
            G (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (sortLay sl) T (extZ sl B ω)) then 1 else 0) =
      ∑ ω : Fin T → Fin B → RT D sl, Pool.P0070.wR (wU sl B xr w0) ω *
        (if NoOverflowD Lv sl E thr0 Bt ωs T
              (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (lastLay sl c) T (extZ sl B ω)) ∧
            G (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (lastLay sl c) T (extZ sl B ω)) then 1 else 0) := by
  set f : (ℕ → GSt ι (Finset ι)) → ℝ := fun tr => if NoOverflowD Lv sl E thr0 Bt ωs T tr ∧ G tr then 1 else 0
    with hf
  have hrun : ∀ (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (ω : Fin T → Fin B → RT D sl),
      Pool.P0070.run (trStepD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay) tr0D T ω =
        trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay T (extZ sl B ω) := fun lay ω => by
    funext a; exact run_trStepD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay T ω a
  have hcap : ∀ (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (ω : Fin T → Fin B → RT D sl),
      f (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (capLay sl lay) T (extZ sl B ω)) =
        f (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay T (extZ sl B ω)) := by
    intro lay ω
    obtain ⟨hiff, heq⟩ := trajD_cap Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay T (extZ sl B ω)
    by_cases h : NoOverflowD Lv sl E thr0 Bt ωs T (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay T (extZ sl B ω))
    · rw [heq h]
    · have h1 : ¬ (NoOverflowD Lv sl E thr0 Bt ωs T
          (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (capLay sl lay) T (extZ sl B ω)) ∧
          G (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ (capLay sl lay) T (extZ sl B ω))) :=
        fun h' => h (hiff.mp h'.1)
      have h2 : ¬ (NoOverflowD Lv sl E thr0 Bt ωs T
          (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay T (extZ sl B ω)) ∧
          G (trajD Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ lay T (extZ sl B ω))) := fun h' => h h'.1
      simp only [hf, if_neg h1, if_neg h2]
  have hlaw := trajD_law Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev ωs φ w0 (capLay sl (lastLay sl c))
    (capLay sl (sortLay sl)) (fun j V => compat_cap (sl j) c V) T f
  simp only [hrun, hcap] at hlaw
  exact hlaw

end Cap

section Coupling

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ)
  (ℓr : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ)

theorem blockMem_erase (c : ι) (sp : ℕ → ℕ → Finset ι) (j : ℕ) :
    blockMem Lv (fun r ℓ => (sp r ℓ).erase c) j = (blockMem Lv sp j).erase c := by
  ext x
  simp only [blockMem, Finset.mem_biUnion, Finset.mem_range, Finset.mem_erase]
  constructor
  · rintro ⟨ℓ, hℓ, hx, h⟩; exact ⟨hx, ℓ, hℓ, h⟩
  · rintro ⟨hx, ℓ, hℓ, h⟩; exact ⟨ℓ, hℓ, hx, h⟩

theorem dzC_congr (a : ℕ) (x : ι) (t : Fin B) (o o' : Option (Fin D × ι))
    (h : ∀ j, o = some (j, x) ↔ o' = some (j, x)) : dzC D B xr ℓr a x t o = dzC D B xr ℓr a x t o' := by
  by_cases hx : ∃ j, o = some (j, x)
  · obtain ⟨j, hj⟩ := hx
    rw [hj, (h j).1 hj]
  · have h0 : ∀ o'' : Option (Fin D × ι), (¬ ∃ j, o'' = some (j, x)) → dzC D B xr ℓr a x t o'' = 0 := by
      intro o'' hn
      rcases o'' with _ | ⟨j, y⟩
      · rfl
      · show (if y = x then _ else _) = 0
        rw [if_neg]; rintro rfl; exact hn ⟨j, rfl⟩
    rw [h0 o hx, h0 o' (fun ⟨j, hj⟩ => hx ⟨j, (h j).2 hj⟩)]

/-- Copy-last within the thread: the other copies' observations do not see `c`. -/
theorem obsR_last_erase (c : ι) (sp : ℕ → ℕ → Finset ι) (r : RT D sl) (x : ι) (hx : x ≠ c) (j : Fin D) :
    obsR D Lv sl (lastLay sl c) sp r = some (j, x) ↔
      obsR D Lv sl (lastLay sl c) (fun r ℓ => (sp r ℓ).erase c) r = some (j, x) := by
  rcases r with _ | ⟨j', k⟩
  · simp [obsR]
  · show (occLast (sl j') c (blockMem Lv sp j') k).map _ = _ ↔ (occLast (sl j') c (blockMem Lv _ j') k).map _ = _
    rw [blockMem_erase]
    simp only [Option.map_eq_some_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨y, hy, rfl, rfl⟩; exact ⟨_, (occLast_erase (sl _) c _ k hx).1 hy, rfl, rfl⟩
    · rintro ⟨y, hy, rfl, rfl⟩; exact ⟨_, (occLast_erase (sl _) c _ k hx).2 hy, rfl, rfl⟩

/-- **Pathwise copy-last coupling for the per-thread process** (P0156's `z_forced_erase`). -/
theorem dz_forced_erase (z : ℕ → Fin B → RT D sl) {c : ι} {ωs : ι → Bool} (hc : ωs c = false)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) : ∀ a,
    (∀ r ℓ, ((dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z (forceS ωs c) (forceF K φ c) a).pools
        r ℓ).erase c = (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z ωs φ a).pools r ℓ) ∧
      (∀ x, x ≠ c → ∀ t,
        (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z (forceS ωs c) (forceF K φ c) a).est x t =
          (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z ωs φ a).est x t) ∧
      (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z (forceS ωs c) (forceF K φ c) a).aux.erase c =
        (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z ωs φ a).aux.erase c := by
  classical
  have hs : AgreeOff c (forceS ωs c) ωs := fun x hx => by simp [forceS, Function.update_of_ne hx]
  intro a
  induction a with
  | zero => exact ⟨fun r ℓ => by simp [gRun], fun x _ t => rfl, rfl⟩
  | succ a ih =>
    obtain ⟨hP, hE, hA⟩ := ih
    set F := dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z (forceS ωs c) (forceF K φ c) with hF
    set G := dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z ωs φ with hG
    have hPfun : (fun r ℓ => ((F a).pools r ℓ).erase c) = (G a).pools := by
      funext r ℓ; exact hP r ℓ
    have hS : ∀ r ℓ, (startPools E thr0 D Lv Bt (forceS ωs c) a (F a).pools r ℓ).erase c =
        startPools E thr0 D Lv Bt ωs a (G a).pools r ℓ := by
      intro r ℓ
      rw [startPools_erase c (forceS ωs c) ωs hs hc, hPfun]
    have hSfun : (fun r ℓ => (startPools E thr0 D Lv Bt (forceS ωs c) a (F a).pools r ℓ).erase c) =
        startPools E thr0 D Lv Bt ωs a (G a).pools := funext fun r => funext fun ℓ => hS r ℓ
    have hobs : ∀ x, x ≠ c → ∀ t j,
        obsR D Lv sl (lastLay sl c) (startPools E thr0 D Lv Bt (forceS ωs c) a (F a).pools) (z a t) = some (j, x) ↔
          obsR D Lv sl (lastLay sl c) (startPools E thr0 D Lv Bt ωs a (G a).pools) (z a t) = some (j, x) := by
      intro x hx t j
      rw [obsR_last_erase Lv sl c _ (z a t) x hx j, hSfun]
    have hret : ∀ x, x ≠ c → (x ∈ (F a).aux ↔ x ∈ (G a).aux) := by
      intro x hx
      constructor
      · intro h; have : x ∈ (F a).aux.erase c := Finset.mem_erase.2 ⟨hx, h⟩
        rw [hA] at this; exact (Finset.mem_erase.1 this).2
      · intro h; have : x ∈ (G a).aux.erase c := Finset.mem_erase.2 ⟨hx, h⟩
        rw [← hA] at this; exact (Finset.mem_erase.1 this).2
    have hinc : ∀ x, x ≠ c →
        gInc E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl c) z) ∅ (forceS ωs c) (forceF K φ c) a x =
          gInc E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh (lastLay sl c) z) ∅ ωs φ a x := by
      intro x hx
      show dzIncO D B Bm xr ℓr a (F a).aux _ x = dzIncO D B Bm xr ℓr a (G a).aux _ x
      unfold dzIncO
      by_cases h1 : x ∈ (G a).aux
      · rw [if_pos ((hret x hx).2 h1), if_pos h1]
      · rw [if_neg (fun h => h1 ((hret x hx).1 h)), if_neg h1]
        exact Finset.sum_congr rfl fun t _ => dzC_congr B xr ℓr a x t _ _ (hobs x hx t)
    have hE' : ∀ x, x ≠ c → ∀ t, (F (a + 1)).est x t = (G (a + 1)).est x t := by
      intro x hx t
      rw [hF, hG, gRun_succ_est, gRun_succ_est]
      simp only [gStep]
      split_ifs
      · exact hE x hx t
      · rw [hE x hx a, hinc x hx]
    refine ⟨fun r ℓ => ?_, fun x hx t => hE' x hx t, ?_⟩
    · rw [hF, hG, gRun_succ_pools, gRun_succ_pools]
      split_ifs with hB
      · rw [mergeUpTo_erase E _ θ R K c (forceF K φ c r) (φ r)
          (fun a ℓ k => by simp [forceF]) (fun a ℓ k x hx => by simp [forceF, hx]) a,
          show (fun i => (startPools E thr0 D Lv Bt (forceS ωs c) a (F a).pools r i).erase c) =
            startPools E thr0 D Lv Bt ωs a (G a).pools r from funext fun i => hS r i]
        refine congrFun (Pool.P0083.mergeUpTo_congr E θ R K _ _ (φ r) a _ (fun j x hx u _ => ?_) (lev r a)) ℓ
        have hxc : x ≠ c := by
          intro hxc'
          rw [hxc', ← hS r j] at hx
          exact Finset.notMem_erase c _ hx
        exact hE' x hxc u
      · exact hS r ℓ
    · have hmem : ∀ x, x ≠ c → (x ∈ members D Lv (startPools E thr0 D Lv Bt (forceS ωs c) a (F a).pools) ↔
          x ∈ members D Lv (startPools E thr0 D Lv Bt ωs a (G a).pools)) := by
        intro x hx
        rw [← hSfun, ← members_erase]
        simp [hx]
      ext x
      by_cases hx : x = c
      · subst hx; simp
      simp only [Finset.mem_erase, hx, ne_eq, not_false_eq_true, true_and]
      show x ∈ (dzUpdO D Lv B Bm xr ℓr rh a _ _ _ _).2 ↔ x ∈ (dzUpdO D Lv B Bm xr ℓr rh a _ _ _ _).2
      simp only [dzUpdO, Finset.mem_union, Finset.mem_filter]
      have hest : gStep a (dzIncO D B Bm xr ℓr a (F a).aux
            (fun t => obsR D Lv sl (lastLay sl c) (startPools E thr0 D Lv Bt (forceS ωs c) a (F a).pools) (z a t)))
            (F a).est x =
          gStep a (dzIncO D B Bm xr ℓr a (G a).aux
            (fun t => obsR D Lv sl (lastLay sl c) (startPools E thr0 D Lv Bt ωs a (G a).pools) (z a t))) (G a).est x :=
        funext fun t => hE' x hx t
      rw [hret x hx, hmem x hx, hest]

theorem dz_not_mem_members_free (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι) (z : ℕ → Fin B → RT D sl)
    {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (a : ℕ) :
    c ∉ members D Lv (startPools E thr0 D Lv Bt ωs a
      (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z ωs φ a).pools) := by
  intro h
  simp only [members, Finset.mem_biUnion, Finset.mem_range] at h
  obtain ⟨r, -, ℓ, -, h⟩ := h
  have := Pool.P0083.mem_startPools_sampled E thr0 D Lv Bt ωs a _ (by
    rw [gRun_pools_eq]
    exact Pool.P0083.mem_tpools_sampled E thr0 θ R K D Lv Bt lev _ ωs φ a) r ℓ c h
  rw [hc] at this; exact Bool.false_ne_true this

omit [Fintype ι] in
theorem mem_blockMem_members {sp : ℕ → ℕ → Finset ι} {j : Fin D} {x : ι} (hD : (j : ℕ) < D)
    (h : x ∈ blockMem Lv sp j) : x ∈ members D Lv sp := by
  simp only [blockMem, members, Finset.mem_biUnion, Finset.mem_range] at h ⊢
  obtain ⟨ℓ, hℓ, h⟩ := h
  exact ⟨j, hD, ℓ, hℓ, h⟩

/-- **The copy-free run of the coupling is the entry-order run.** -/
theorem dz_free_eq (z : ℕ → Fin B → RT D sl) {c : ι} {ωs : ι → Bool} (hc : ωs c = false)
    (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) : ∀ a,
    dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z ωs φ a =
      dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (sortLay sl) z ωs φ a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    have hobs : obsU Lv sl B (lastLay sl c) (startPools E thr0 D Lv Bt ωs a
        (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z ωs φ a).pools) (z a) =
        obsU Lv sl B (sortLay sl) (startPools E thr0 D Lv Bt ωs a
          (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev (lastLay sl c) z ωs φ a).pools) (z a) := by
      funext t
      unfold obsU
      rcases z a t with _ | ⟨j, k⟩
      · rfl
      · show (occLast (sl j) c _ k).map _ = (occSort (sl j) _ k).map _
        rw [occLast_of_not_mem (sl j) (fun h => dz_not_mem_members_free Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev
          (lastLay sl c) z hc φ a (mem_blockMem_members Lv j.2 h))]
    rw [dzRun_succ_obs, dzRun_succ_obs, hobs, ih]

end Coupling

section Sizes

variable {ι : Type} [LinearOrder ι] [Fintype ι] {D : ℕ} (Lv : ℕ) (sl : Fin D → ℕ) (B : ℕ) (Bm : ℝ) (xr : Fin D → ℝ)
  (ℓr : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) (E thr0 : ι → ℕ) (θ : ℝ) (R K : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ)

theorem dzC_bounds {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ xr j) (hℓ0 : ∀ u x, 0 ≤ ℓr u x)
    (hℓ1 : ∀ u x, ℓr u x ≤ 1) (a : ℕ) (x : ι) (t : Fin B) (o : Option (Fin D × ι)) :
    0 ≤ dzC D B xr ℓr a x t o ∧ dzC D B xr ℓr a x t o ≤ 1 / xmin := by
  rcases o with _ | ⟨j, y⟩
  · exact ⟨le_rfl, by positivity⟩
  · show 0 ≤ (if y = x then _ else _) ∧ (if y = x then _ else _) ≤ _
    have hj : 0 < xr j := lt_of_lt_of_le hxmin (hx j)
    split_ifs
    · refine ⟨div_nonneg (hℓ0 _ _) hj.le, ?_⟩
      calc ℓr (a * B + t) x / xr j ≤ 1 / xr j := div_le_div_of_nonneg_right (hℓ1 _ _) hj.le
        _ ≤ 1 / xmin := one_div_le_one_div_of_le hxmin (hx j)
    · exact ⟨le_rfl, by positivity⟩

/-- Unit increments lie in `[0, B/x_min]` (losses in `[0, 1]`, fake increment `Bm ≤ B/x_min`). -/
theorem dzInc_bounds {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ xr j) (hℓ0 : ∀ u x, 0 ≤ ℓr u x)
    (hℓ1 : ∀ u x, ℓr u x ≤ 1) (hBm0 : 0 ≤ Bm) (hBm : Bm ≤ B / xmin) (a : ℕ) (ret : Finset ι)
    (o : Fin B → Option (Fin D × ι)) (x : ι) :
    0 ≤ dzIncO D B Bm xr ℓr a ret o x ∧ dzIncO D B Bm xr ℓr a ret o x ≤ B / xmin := by
  unfold dzIncO
  split_ifs
  · exact ⟨hBm0, hBm⟩
  · refine ⟨Finset.sum_nonneg fun t _ => (dzC_bounds B xr ℓr hxmin hx hℓ0 hℓ1 a x t _).1, ?_⟩
    calc ∑ t : Fin B, dzC D B xr ℓr a x t (o t) ≤ ∑ _t : Fin B, 1 / xmin :=
          Finset.sum_le_sum fun t _ => (dzC_bounds B xr ℓr hxmin hx hℓ0 hℓ1 a x t _).2
      _ = B / xmin := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

open Pool.P0073 Pool.P0046 Pool.P0042 in
open Classical in
/-- **Pool sizes of the per-thread process** (P0109's bound through P0156's `prob_members_large_gen`), for every
layout and every fixed sequence of unit coins. -/
theorem prob_members_large_DZ {NE Lt : ℕ} (M0 : ℝ) (kk : ℕ) (lay : (j : Fin D) → Finset ι → Fin (sl j) → Option ι)
    (z : ℕ → Fin B → RT D sl) {ps p : ℝ} (hps : 0 ≤ ps ∧ ps ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hE : Monotone E) (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    {xmin : ℝ} (hxmin : 0 < xmin) (hx : ∀ j, xmin ≤ xr j) (hℓ0 : ∀ u x, 0 ≤ ℓr u x)
    (hℓ1 : ∀ u x, ℓr u x ≤ 1) (hBm0 : 0 ≤ Bm) (hBm : Bm ≤ B / xmin)
    (hR : 1 ≤ R) (hT : B / xmin * NE ≤ 2 ^ (R - 1) * θ) (hM0 : 16 * R ≤ M0) (hk : 4 * R * kk ≤ M0)
    (hp : p * (Real.exp 1 - 1) ≤ 1 / (32 * R)) (hlevLt : ∀ a < NE, ∀ r < D, lev r a ≤ Lt)
    (s0 : ℕ) (δs : ℝ)
    (hs : ∀ a r : ℕ, a < NE → r < D →
      ∑ F ∈ (Finset.univ.filter fun c => E c = a ∧ thr0 c = r).powerset,
        ps ^ F.card * (1 - ps) ^ ((Finset.univ.filter fun c => E c = a ∧ thr0 c = r).card - F.card) *
          (if s0 < F.card then 1 else 0) ≤ δs)
    (S : ℝ) (hM0S : M0 ≤ S) (hS0 : 0 ≤ S)
    (hρS : (1 - 1 / (4 * R : ℝ)) ^ K * (S + (s0 + D * Lv * S)) ≤ S) :
    ∑ ω : SlotT NE D Lt K → ι → Bool, bw2 (qOfT K D ps p) ω *
        (if ∀ a < NE, ((members D Lv (startPools E thr0 D Lv Bt (ωsOfT E K D ω) a
            (dzRun Lv sl B Bm xr ℓr rh E thr0 θ R K Bt lev lay z (ωsOfT E K D ω) (φOfT K D ω) a).pools)).card : ℝ) ≤
              D * ((s0 + D * Lv * S) + (Lv - 1 : ℕ) * S) + D * s0
          then 0 else 1)
      ≤ NE * D * δs + NE * D * (Lt + 1) * K * delta (Fintype.card ι) p R kk M0 :=
  prob_members_large_gen E thr0 θ R K D Lv Bt lev (dzUpd D Lv sl B Bm xr ℓr rh lay z) ∅ M0 kk hps hp0 hp1 hE hB hLv
    hlev (by positivity) (fun ωs φ a x => dzInc_bounds B Bm xr ℓr hxmin hx hℓ0 hℓ1 hBm0 hBm a _ _ x)
    hR hT hM0 hk hp hlevLt s0 δs hs S hM0S hS0 hρS

end Sizes

end Pool.P0176
