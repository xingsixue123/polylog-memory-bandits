import Pool.P0156.ZRun
import Pool.P0119.FOCount

/-!
# Bad walk points of Design Z's retirement process (P0119's count for P0156's `zRun`)

P0119 counts the bad opportunities of P0095's FO process: comparator copies that are not sampled and, forced into
their own copy-last run, are never evicted before `NE`. This file proves the same bound for P0156's retirement
process `zRun` (P0136's rule (b″) as retirement: fake data `1` per round until a merge removes the copy), for every
fixed retirement rule `rh`.

* Generic in P0156's `gRun`: `GSt_ext`, **`gRun_congr_slots`** (a copy's filter bits off its clock slots are not
  read; P0119's `foRun_congr_slots`), **`gRun_force_eq`** (the run on P0048's forced opportunity coins is the forced
  run; P0119's `foRun_force_eq`).
* The in-law step for `zRun` (P0111's `law_occSort_occLast`): `zUpdO`/`zUpd_eq` (the update reads the layout only
  through the observed slot content), `VstZ`, `zStepO`, `zRun_succ_obs`, `zRun_congr_y` (causality in the slots),
  `trStepZ`, `tr0Z`, `run_trStepZ`, `trajZ_law`, `zRun_cap_eq`, `zRun_cap_eq'`, `NoOverflowZ`, `trajZ`, `trajZ_cap`,
  **`law_occSort_occLast_Z`**.
* The count (P0119's `count_bad_FO`): `SurvZ`, `fSurvZ`, **`forced_lawZ`**, `VstZ_forced_card_le` (P0115's
  `Vat_forced_card_le`, from P0156's `z_forced_erase`/`z_free_eq`), `GoodAZ`, `bad_leZ`, `card_surv_leZ`, `cap_fSurvZ`,
  `card_bad_leZ`, `fGZ`, `cap_fGZ`, `hper_fGZ` and **`count_bad_Z`**:
  `E[#bad] ≤ D·Lv·S/π + D·NE·P(the actual run is not GoodAZ)`.
-/

namespace Pool.P0164

open Finset Pool.P0095 Pool.P0065 Pool.P0081 Pool.P0082 Pool.P0052 Pool.P0048 Pool.P0105 Pool.P0156

section Generic

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) {σ : Type} (upd : ℕ → (ℕ → ℕ → Finset ι) → (ι → ℕ → ℝ) → σ → (ι → ℝ) × σ) (aux0 : σ)

theorem GSt_ext {x x' : GSt ι σ} (h1 : x.pools = x'.pools) (h2 : x.est = x'.est) (h3 : x.aux = x'.aux) :
    x = x' := by
  cases x; cases x'; simp_all

/-- **The generic process ignores a copy's filter bits outside its clock slots** (P0119's `foRun_congr_slots`). -/
theorem gRun_congr_slots (ωs : ι → Bool) (c : ι) (φ φ' : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (h : ∀ r x ℓ k d, φ r x ℓ k d ≠ φ' r x ℓ k d →
      d = c ∧ ¬ (r = curT E thr0 D Bt c x ∧ InSlotsT E thr0 D Bt lev c x ℓ)) :
    ∀ a, gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ a = gRun E thr0 θ R K D Lv Bt lev upd aux0 ωs φ' a := by
  intro a
  induction a with
  | zero => rfl
  | succ a ih =>
    have hC : ∀ x u, u ≤ a + 1 → gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x u =
        gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ' x u := by
      intro x u hu
      rcases Nat.lt_or_eq_of_le hu with hu | hu
      · rw [← gEst_frozen E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x a (by omega),
          ← gEst_frozen E thr0 θ R K D Lv Bt lev upd aux0 ωs φ' x a (by omega), ih]
      · subst hu
        rw [gChat_succ, gChat_succ]
        have h1 : gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x a = gChat E thr0 θ R K D Lv Bt lev upd aux0 ωs φ' x a := by
          rw [← gEst_frozen E thr0 θ R K D Lv Bt lev upd aux0 ωs φ x a le_rfl,
            ← gEst_frozen E thr0 θ R K D Lv Bt lev upd aux0 ωs φ' x a le_rfl, ih]
        unfold gInc; rw [ih, h1]
    refine GSt_ext ?_ ?_ ?_
    · rw [gRun_pools_eq, gRun_pools_eq, tpools_congr_slots ωs c φ φ' h (a + 1)]
      exact Pool.P0083.tpools_congr E thr0 θ R K D Lv Bt lev _ _ ωs φ' (a + 1) (fun x _ u hu => hC x u hu)
    · rw [gRun_succ_est, gRun_succ_est]; unfold gInc; rw [ih]
    · show (upd a _ _ _).2 = (upd a _ _ _).2
      rw [ih]

attribute [local instance] coinFintype in
/-- **The generic run on a forced opportunity is the forced run** (P0119's `foRun_force_eq`). -/
theorem gRun_force_eq {NE Lt : ℕ} (c : ι) (hc : E c < NE) (ω : SlotC NE D Lt K × ι → Bool) (a : ℕ) :
    gRun E thr0 θ R K D Lv Bt lev upd aux0 (ωsC E NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω))
        (φC NE D Lt K (force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω)) a =
      gRun E thr0 θ R K D Lv Bt lev upd aux0 (forceS (ωsC E NE D Lt K ω) c) (forceF K (φC NE D Lt K ω) c) a := by
  classical
  rw [Pool.P0119.ωsC_force E thr0 K D Bt lev c hc ω]
  refine gRun_congr_slots E thr0 θ R K D Lv Bt lev upd aux0 _ c _ _ (fun r x ℓ k d hne => ?_) a
  by_cases hdc : d = c
  · refine ⟨hdc, fun hin => hne ?_⟩
    subst hdc
    unfold φC forceF force
    simp only [if_true]
    split_ifs with h1 h2
    · rfl
    · exact absurd (mem_oppSet_inr.2 ⟨rfl, hin⟩) h2
    · rfl
  · exfalso
    apply hne
    simp only [φC, forceF, force, hdc, if_false]
    split_ifs with h1 h2
    · exact absurd (mem_oppSet_inr.1 h2).1 hdc
    · rfl
    · rfl

end Generic


section Law

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool)
  (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)

/-- The retirement update given the observed slot content `o`. -/
noncomputable def zUpdO (a : ℕ) (sp : ℕ → ℕ → Finset ι) (est : ι → ℕ → ℝ) (ret : Finset ι) (o : Option ι) :
    (ι → ℝ) × Finset ι :=
  let inc : ι → ℝ := fun x => if x ∈ ret then 1 else if o = some x then (s : ℝ) * L a x else 0
  (inc, ret ∪ (members D Lv sp).filter (fun x => rh a x (gStep a inc est x) = true))

theorem zUpd_eq (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) (a : ℕ) (sp : ℕ → ℕ → Finset ι)
    (est : ι → ℕ → ℝ) (ret : Finset ι) :
    zUpd D Lv s L occ y rh a sp est ret = zUpdO D Lv s L rh a sp est ret (occ (members D Lv sp) (y a)) := rfl

/-- The start-pool members of a state. -/
noncomputable def VstZ (a : ℕ) (st : GSt ι (Finset ι)) : Finset ι :=
  members D Lv (startPools E thr0 D Lv Bt ωs a st.pools)

/-- One unit of the retirement process, given the observed slot content `o`. -/
noncomputable def zStepO (a : ℕ) (st : GSt ι (Finset ι)) (o : Option ι) : GSt ι (Finset ι) :=
  ⟨fun r => if Bt r ∣ a + 1 then
      mergeUpTo E (gStep a (zUpdO D Lv s L rh a (startPools E thr0 D Lv Bt ωs a st.pools) st.est st.aux o).1 st.est)
        θ R K (φ r) a (lev r a) (startPools E thr0 D Lv Bt ωs a st.pools r)
    else startPools E thr0 D Lv Bt ωs a st.pools r,
   gStep a (zUpdO D Lv s L rh a (startPools E thr0 D Lv Bt ωs a st.pools) st.est st.aux o).1 st.est,
   (zUpdO D Lv s L rh a (startPools E thr0 D Lv Bt ωs a st.pools) st.est st.aux o).2⟩

theorem zRun_succ_obs (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) (a : ℕ) :
    zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ (a + 1) =
      zStepO E thr0 θ R K D Lv Bt lev s L rh ωs φ a (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a)
        (occ (VstZ E thr0 D Lv Bt ωs a (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a)) (y a)) := rfl

/-- **Causality in the slots.** -/
theorem zRun_congr_y (occ : Finset ι → Fin s → Option ι) {y y' : ℕ → Fin s} : ∀ a, (∀ v < a, y v = y' v) →
    zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a = zRun E thr0 θ R K D Lv Bt lev s L occ y' rh ωs φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    rw [zRun_succ_obs, zRun_succ_obs, ih (fun v hv => h v (by omega)), h a (Nat.lt_succ_self a)]

/-- The trajectory step. -/
noncomputable def trStepZ (occ : Finset ι → Fin s → Option ι) (u : ℕ) (tr : ℕ → GSt ι (Finset ι)) (yv : Fin s) :
    ℕ → GSt ι (Finset ι) :=
  fun a => if a ≤ u then tr a else
    zStepO E thr0 θ R K D Lv Bt lev s L rh ωs φ u (tr u) (occ (VstZ E thr0 D Lv Bt ωs u (tr u)) yv)

/-- The initial trajectory. -/
def tr0Z : ℕ → GSt ι (Finset ι) := fun _ => ⟨fun _ _ => ∅, fun _ _ => 0, ∅⟩

theorem run_trStepZ [NeZero s] (occ : Finset ι → Fin s → Option ι) : ∀ (T : ℕ) (ω : Fin T → Fin s) (a : ℕ),
    Pool.P0070.run (trStepZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ) tr0Z T ω a =
      zRun E thr0 θ R K D Lv Bt lev s L occ (extY s ω) rh ωs φ (min a T)
  | 0, ω, a => by simp only [Pool.P0070.run, Nat.min_zero]; rfl
  | T + 1, ω, a => by
    have hc : ∀ b ≤ T, zRun E thr0 θ R K D Lv Bt lev s L occ (extY s (Fin.init ω)) rh ωs φ b =
        zRun E thr0 θ R K D Lv Bt lev s L occ (extY s ω) rh ωs φ b := fun b hb =>
      zRun_congr_y E thr0 θ R K D Lv Bt lev s L rh ωs φ occ b (fun v hv => extY_init s ω v (by omega))
    simp only [Pool.P0070.run, trStepZ]
    split_ifs with ha
    · rw [run_trStepZ occ T (Fin.init ω) a, hc _ (by omega)]
      congr 1; omega
    · rw [run_trStepZ occ T (Fin.init ω) T, Nat.min_self, hc T le_rfl, show min a (T + 1) = T + 1 by omega,
        zRun_succ_obs, extY_last]

theorem trajZ_law (occA occB : Finset ι → Fin s → Option ι) (hcompat : ∀ V, Pool.P0070.Compat (occA V) (occB V))
    (T : ℕ) (f : (ℕ → GSt ι (Finset ι)) → ℝ) :
    ∑ ω : Fin T → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) ω *
        f (Pool.P0070.run (trStepZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occB) tr0Z T ω) =
      ∑ ω : Fin T → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) ω *
        f (Pool.P0070.run (trStepZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occA) tr0Z T ω) := by
  choose τ hτ using fun V => Pool.P0070.exists_perm (occA V) (occB V) (hcompat V)
  refine Pool.P0070.sum_run_eq _ _ _ tr0Z (fun u tr => τ (VstZ E thr0 D Lv Bt ωs u (tr u))) ?_
    (fun _ _ _ => rfl) T f
  intro u tr y
  funext a
  simp only [trStepZ, hτ]

theorem zRun_cap_eq (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) : ∀ a,
    (∀ u < a, (VstZ E thr0 D Lv Bt ωs u (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ u)).card ≤ s) →
    zRun E thr0 θ R K D Lv Bt lev s L (capOcc s occ) y rh ωs φ a = zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    rw [zRun_succ_obs, zRun_succ_obs, ih (fun u hu => h u (by omega))]
    simp only [capOcc, if_pos (h a (by omega))]

theorem zRun_cap_eq' (occ : Finset ι → Fin s → Option ι) (y : ℕ → Fin s) : ∀ a,
    (∀ u < a, (VstZ E thr0 D Lv Bt ωs u (zRun E thr0 θ R K D Lv Bt lev s L (capOcc s occ) y rh ωs φ u)).card ≤ s) →
    zRun E thr0 θ R K D Lv Bt lev s L (capOcc s occ) y rh ωs φ a = zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ a := by
  intro a
  induction a with
  | zero => intro _; rfl
  | succ a ih =>
    intro h
    have ih' := ih (fun u hu => h u (by omega))
    have ha := h a (by omega)
    rw [zRun_succ_obs, zRun_succ_obs, ih']
    rw [ih'] at ha
    simp only [capOcc, if_pos ha]

/-- No overflow before `T` along a trajectory. -/
def NoOverflowZ (T : ℕ) (tr : ℕ → GSt ι (Finset ι)) : Prop := ∀ u < T, (VstZ E thr0 D Lv Bt ωs u (tr u)).card ≤ s

/-- The trajectory of a run up to `T`. -/
noncomputable def trajZ (occ : Finset ι → Fin s → Option ι) (T : ℕ) (y : ℕ → Fin s) : ℕ → GSt ι (Finset ι) :=
  fun a => zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ (min a T)

theorem trajZ_cap (occ : Finset ι → Fin s → Option ι) (T : ℕ) (y : ℕ → Fin s) :
    (NoOverflowZ E thr0 D Lv Bt s ωs T (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (capOcc s occ) T y) ↔
      NoOverflowZ E thr0 D Lv Bt s ωs T (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ T y)) ∧
    (NoOverflowZ E thr0 D Lv Bt s ωs T (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ T y) →
      trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (capOcc s occ) T y =
        trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ T y) := by
  have hmin : ∀ u < T, min u T = u := fun u hu => Nat.min_eq_left hu.le
  constructor
  · constructor
    · intro h u hu
      have h' : ∀ v < u, (VstZ E thr0 D Lv Bt ωs v
          (zRun E thr0 θ R K D Lv Bt lev s L (capOcc s occ) y rh ωs φ v)).card ≤ s := fun v hv => by
        have := h v (by omega); simp only [trajZ, hmin v (by omega)] at this; exact this
      have := h u hu
      simp only [trajZ, hmin u hu] at this ⊢
      rwa [zRun_cap_eq' E thr0 θ R K D Lv Bt lev s L rh ωs φ occ y u h'] at this
    · intro h u hu
      have h' : ∀ v < u, (VstZ E thr0 D Lv Bt ωs v
          (zRun E thr0 θ R K D Lv Bt lev s L occ y rh ωs φ v)).card ≤ s := fun v hv => by
        have := h v (by omega); simp only [trajZ, hmin v (by omega)] at this; exact this
      have := h u hu
      simp only [trajZ, hmin u hu] at this ⊢
      rwa [zRun_cap_eq E thr0 θ R K D Lv Bt lev s L rh ωs φ occ y u h']
  · intro h
    funext a
    simp only [trajZ]
    refine zRun_cap_eq E thr0 θ R K D Lv Bt lev s L rh ωs φ occ y _ fun u hu => ?_
    have := h u (by omega)
    simp only [trajZ, hmin u (by omega)] at this
    exact this

open Classical in
/-- **In-law transfer for the retirement process** (P0111's `law_occSort_occLast`). -/
theorem law_occSort_occLast_Z [NeZero s] (c : ι) (T : ℕ) (G : (ℕ → GSt ι (Finset ι)) → Prop) :
    ∑ ω : Fin T → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) ω *
        (if NoOverflowZ E thr0 D Lv Bt s ωs T (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (occSort s) T (extY s ω)) ∧
            G (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (occSort s) T (extY s ω)) then 1 else 0) =
      ∑ ω : Fin T → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) ω *
        (if NoOverflowZ E thr0 D Lv Bt s ωs T (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (occLast s c) T (extY s ω)) ∧
            G (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (occLast s c) T (extY s ω)) then 1 else 0) := by
  set f : (ℕ → GSt ι (Finset ι)) → ℝ := fun tr => if NoOverflowZ E thr0 D Lv Bt s ωs T tr ∧ G tr then 1 else 0
    with hf
  have hrun : ∀ (occ : Finset ι → Fin s → Option ι) (ω : Fin T → Fin s),
      Pool.P0070.run (trStepZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ) tr0Z T ω =
        trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ T (extY s ω) := fun occ ω => by
    funext a; exact run_trStepZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ T ω a
  have hcap : ∀ (occ : Finset ι → Fin s → Option ι) (ω : Fin T → Fin s),
      f (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (capOcc s occ) T (extY s ω)) =
        f (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ T (extY s ω)) := by
    intro occ ω
    obtain ⟨hiff, heq⟩ := trajZ_cap E thr0 θ R K D Lv Bt lev s L rh ωs φ occ T (extY s ω)
    by_cases h : NoOverflowZ E thr0 D Lv Bt s ωs T (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ T (extY s ω))
    · rw [heq h]
    · have h1 : ¬ (NoOverflowZ E thr0 D Lv Bt s ωs T
          (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (capOcc s occ) T (extY s ω)) ∧
          G (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (capOcc s occ) T (extY s ω))) := fun h' => h (hiff.mp h'.1)
      have h2 : ¬ (NoOverflowZ E thr0 D Lv Bt s ωs T (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ T (extY s ω)) ∧
          G (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ occ T (extY s ω))) := fun h' => h h'.1
      simp only [hf, if_neg h1, if_neg h2]
  have hlaw := trajZ_law E thr0 θ R K D Lv Bt lev s L rh ωs φ (capOcc s (occLast s c)) (capOcc s (occSort s))
    (compat_cap s c) T f
  simp only [hrun, hcap] at hlaw
  exact hlaw

end Law

section Count

attribute [local instance] coinFintype

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) {NE Lt : ℕ}

/-- The survival event of opportunity `c` on a trajectory: `c` is in some pool at `NE` and every sub-pool at
`NE` has at most `S` copies. -/
def SurvZ (NE S : ℕ) (c : ι) (tr : ℕ → GSt ι (Finset ι)) : Prop :=
  (∃ r ℓ, c ∈ (tr NE).pools r ℓ) ∧ ∀ r < D, ∀ ℓ < Lv, ((tr NE).pools r ℓ).card ≤ S

open Classical in
/-- The slot probability that, in the entry-order run on coins `ω`, nothing overflows before `NE` and the
copy `c` survives (with small pools). -/
noncomputable def fSurvZ [NeZero s] (S : ℕ) (c : ι) (ω : SlotC NE D Lt K × ι → Bool) : ℝ :=
  ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
    (if NoOverflowZ E thr0 D Lv Bt s (ωsC E NE D Lt K ω) NE
          (trajZ E thr0 θ R K D Lv Bt lev s L rh (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy)) ∧
        SurvZ D Lv NE S c
          (trajZ E thr0 θ R K D Lv Bt lev s L rh (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy))
      then 1 else 0)

theorem wR_nonneg_s {T : ℕ} (yy : Fin T → Fin s) : 0 ≤ Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy :=
  Finset.prod_nonneg fun _ _ => by positivity

theorem fSurv_nonnegZ [NeZero s] (S : ℕ) (c : ι) (ω : SlotC NE D Lt K × ι → Bool) :
    0 ≤ fSurvZ E thr0 θ R K D Lv Bt lev s L rh S c ω :=
  Finset.sum_nonneg fun yy _ => mul_nonneg (Pool.P0119.wR_nonneg_s s yy) (by split_ifs <;> norm_num)

open Classical in
/-- **Per-opportunity law step.** The slot probability that the FORCED copy-last run of `c` (on coins `ω`)
does not overflow and has `c` surviving equals `fSurv` at the forced coins: the forced run is the run on the
P0048-forced coins (`foRun_force_eq`), and P0111 moves copy-last to entry order. -/
theorem forced_lawZ [NeZero s] (S : ℕ) (c : ι) (hc : E c < NE) (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      (if NoOverflowZ E thr0 D Lv Bt s (forceS (ωsC E NE D Lt K ω) c) NE
            (trajZ E thr0 θ R K D Lv Bt lev s L rh (forceS (ωsC E NE D Lt K ω) c) (forceF K (φC NE D Lt K ω) c)
              (occLast s c) NE (extY s yy)) ∧
          SurvZ D Lv NE S c (trajZ E thr0 θ R K D Lv Bt lev s L rh (forceS (ωsC E NE D Lt K ω) c)
            (forceF K (φC NE D Lt K ω) c) (occLast s c) NE (extY s yy))
        then 1 else 0) =
      fSurvZ E thr0 θ R K D Lv Bt lev s L rh S c (force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω) := by
  set ω' := force (oppSet E thr0 D Bt lev NE Lt K c hc) oppVal ω
  have htr : ∀ yy : Fin NE → Fin s,
      trajZ E thr0 θ R K D Lv Bt lev s L rh (forceS (ωsC E NE D Lt K ω) c) (forceF K (φC NE D Lt K ω) c)
        (occLast s c) NE (extY s yy) =
      trajZ E thr0 θ R K D Lv Bt lev s L rh (ωsC E NE D Lt K ω') (φC NE D Lt K ω') (occLast s c) NE (extY s yy) := by
    intro yy; funext a
    simp only [trajZ]
    exact (gRun_force_eq E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occLast s c) (extY s yy) rh) ∅ c hc ω _).symm
  have hs := Pool.P0119.ωsC_force E thr0 K D Bt lev c hc ω
  simp only [htr]
  rw [← hs]
  unfold fSurvZ
  exact (law_occSort_occLast_Z E thr0 θ R K D Lv Bt lev s L rh (ωsC E NE D Lt K ω') (φC NE D Lt K ω') c NE
    (SurvZ D Lv NE S c)).symm

end Count

section Bad

attribute [local instance] coinFintype

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool)

/-- **Forced runs overflow at most one slot later than the actual run** (P0115's `Vat_forced_card_le`). -/
theorem VstZ_forced_card_le {c : ι} {ωs : ι → Bool} (hc : ωs c = false) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool)
    (y : ℕ → Fin s) (u : ℕ) :
    (VstZ E thr0 D Lv Bt (forceS ωs c) u
        (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh (forceS ωs c) (forceF K φ c) u)).card ≤
      (VstZ E thr0 D Lv Bt ωs u (zRun E thr0 θ R K D Lv Bt lev s L (occSort s) y rh ωs φ u)).card + 1 := by
  classical
  have hs : AgreeOff c (forceS ωs c) ωs := fun x hx => by simp [forceS, Function.update_of_ne hx]
  have hP : (fun r ℓ => ((zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh (forceS ωs c) (forceF K φ c)
      u).pools r ℓ).erase c) = (zRun E thr0 θ R K D Lv Bt lev s L (occSort s) y rh ωs φ u).pools := by
    funext r ℓ
    rw [(z_forced_erase E thr0 θ R K D Lv Bt lev s L y rh hc φ u).1 r ℓ,
      z_free_eq E thr0 θ R K D Lv Bt lev s L y rh hc φ u]
  have hV : (VstZ E thr0 D Lv Bt (forceS ωs c) u
      (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh (forceS ωs c) (forceF K φ c) u)).erase c =
      VstZ E thr0 D Lv Bt ωs u (zRun E thr0 θ R K D Lv Bt lev s L (occSort s) y rh ωs φ u) := by
    unfold VstZ
    rw [members_erase]
    congr 1
    funext r ℓ
    rw [startPools_erase c (forceS ωs c) ωs hs hc, hP]
  have := Finset.pred_card_le_card_erase (s := VstZ E thr0 D Lv Bt (forceS ωs c) u
    (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh (forceS ωs c) (forceF K φ c) u)) (a := c)
  rw [hV] at this
  omega

/-- The good event of the actual (entry-order) run: at most `s − 1` start-pool members before `T` and sub-pools of
size at most `S − 1` at `T`. -/
def GoodAZ (T S : ℕ) (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s) : Prop :=
  (∀ u < T, (VstZ E thr0 D Lv Bt ωs u (zRun E thr0 θ R K D Lv Bt lev s L (occSort s) y rh ωs φ u)).card + 1 ≤ s) ∧
    ∀ r < D, ∀ ℓ < Lv, ((zRun E thr0 θ R K D Lv Bt lev s L (occSort s) y rh ωs φ T).pools r ℓ).card + 1 ≤ S

open Classical in
/-- **A bad opportunity survives in its forced run, or the actual run is not good.** If `c` is not sampled and,
forced in, is never evicted before `T` (P0065's `evict … = none`, with the forced run's own estimates), then either
its forced copy-last run does not overflow and `c` survives at `T` with small pools, or the actual run fails
`GoodA`. -/
theorem bad_leZ (T S : ℕ) (cstar : ℕ → ℕ → ι) {ωs : ι → Bool} {φ : ℕ → ℕ → ℕ → Fin K → ι → Bool} (y : ℕ → Fin s)
    {j a : ℕ} (ha : a < T) (hc : ωs (cstar j a) = false)
    (hev : evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occLast s (cstar j a)) y rh) ∅ (forceS ωs (cstar j a)) (forceF K φ (cstar j a))) θ R K D Lv Bt lev T cstar ωs φ j a = none) :
    (1 : ℝ) ≤ (if NoOverflowZ E thr0 D Lv Bt s (forceS ωs (cstar j a)) T
            (trajZ E thr0 θ R K D Lv Bt lev s L rh (forceS ωs (cstar j a)) (forceF K φ (cstar j a))
              (occLast s (cstar j a)) T y) ∧
          SurvZ D Lv T S (cstar j a) (trajZ E thr0 θ R K D Lv Bt lev s L rh (forceS ωs (cstar j a))
            (forceF K φ (cstar j a)) (occLast s (cstar j a)) T y) then 1 else 0) +
      (if GoodAZ E thr0 θ R K D Lv Bt lev s L rh T S ωs φ y then 0 else 1) := by
  set c := cstar j a with hcdef
  by_cases hg : GoodAZ E thr0 θ R K D Lv Bt lev s L rh T S ωs φ y
  · rw [if_pos hg, add_zero, if_pos]
    have hmin : ∀ u, u ≤ T → min u T = u := fun u hu => Nat.min_eq_left hu
    refine ⟨fun u hu => ?_, ⟨?_, fun r hr ℓ hℓ => ?_⟩⟩
    · simp only [trajZ, hmin u hu.le]
      have h1 := VstZ_forced_card_le E thr0 θ R K D Lv Bt lev s L rh hc φ y u
      have h2 := hg.1 u hu
      omega
    · simp only [trajZ, Nat.min_self]
      unfold evict at hev
      split_ifs at hev with h
      have hal : Alive E thr0 (gChat E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occLast s c) y rh) ∅ (forceS ωs c)
          (forceF K φ c))
          θ R K D Lv Bt lev (forceS ωs c) (forceF K φ c) T c := by
        by_contra hna
        exact h ⟨T, ha, le_rfl, hna⟩
      obtain ⟨r, ℓ, hm⟩ := hal
      refine ⟨r, ℓ, ?_⟩
      rwa [← gRun_pools_eq] at hm
    · simp only [trajZ, Nat.min_self]
      have he := (z_forced_erase E thr0 θ R K D Lv Bt lev s L y rh hc φ T).1 r ℓ
      rw [z_free_eq E thr0 θ R K D Lv Bt lev s L y rh hc φ T] at he
      have h1 := Finset.pred_card_le_card_erase (s := (zRun E thr0 θ R K D Lv Bt lev s L (occLast s c) y rh
        (forceS ωs c) (forceF K φ c) T).pools r ℓ) (a := c)
      rw [he] at h1
      have h2 := hg.2 r hr ℓ hℓ
      omega
  · rw [if_neg hg]
    have : (0 : ℝ) ≤ (if NoOverflowZ E thr0 D Lv Bt s (forceS ωs c) T
            (trajZ E thr0 θ R K D Lv Bt lev s L rh (forceS ωs c) (forceF K φ c) (occLast s c) T y) ∧
          SurvZ D Lv T S c (trajZ E thr0 θ R K D Lv Bt lev s L rh (forceS ωs c) (forceF K φ c) (occLast s c) T y)
        then 1 else 0) := by split_ifs <;> norm_num
    linarith

end Bad

section Main

attribute [local instance] coinFintype

open Pool.P0111

variable {ι : Type} [LinearOrder ι] [Fintype ι] (E thr0 : ι → ℕ) (θ : ℝ) (R K D Lv : ℕ) (Bt : ℕ → ℕ)
  (lev : ℕ → ℕ → ℕ) (s : ℕ) (L : ℕ → ι → ℝ) (rh : ℕ → ι → (ℕ → ℝ) → Bool) {NE Lt : ℕ}

open Classical in
/-- At most `D·Lv·S` grid opportunities survive with small pools in one run. -/
theorem card_surv_leZ (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (ωs : ι → Bool) (φ : ℕ → ℕ → ℕ → Fin K → ι → Bool) (y : ℕ → Fin s) (S : ℕ) :
    (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ SurvZ D Lv NE S (cstar ja.1 ja.2)
      (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (occSort s) NE y)} : ℝ) ≤ D * Lv * S := by
  set F := (Finset.univ.filter fun ja : Fin D × Fin NE => Bt ja.1 ∣ ja.2 ∧ SurvZ D Lv NE S (cstar ja.1 ja.2)
      (trajZ E thr0 θ R K D Lv Bt lev s L rh ωs φ (occSort s) NE y)) with hF
  by_cases hne : F.Nonempty
  · obtain ⟨ja0, hja0⟩ := hne
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hja0
    have hsz := hja0.2.2
    simp only [trajZ, Nat.min_self] at hsz
    rw [gRun_pools_eq] at hsz
    have hinj : Set.InjOn (fun ja : Fin D × Fin NE => cstar ja.1 ja.2) (F : Set (Fin D × Fin NE)) := by
      rintro ⟨j, a⟩ hj1 ⟨j', a'⟩ hj2 heq
      simp only [hF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj1 hj2
      simp only at heq
      have h1 := hE j a (by omega) hj1.1 a.2
      have h2 := hE j' a' (by omega) hj2.1 a'.2
      have h3 := hthr j a (by omega) hj1.1 a.2
      have h4 := hthr j' a' (by omega) hj2.1 a'.2
      rw [heq] at h1 h3
      ext <;> simp only <;> omega
    have himg := Finset.card_image_of_injOn hinj
    have hA := card_alive_le hD hLv hlev _ _ NE S hsz (F.image fun ja : Fin D × Fin NE => cstar ja.1 ja.2)
      (fun c hc => by
        simp only [Finset.mem_image, hF, Finset.mem_filter, Finset.mem_univ, true_and] at hc
        obtain ⟨ja, ⟨-, hal, -⟩, rfl⟩ := hc
        obtain ⟨r, ℓ, hm⟩ := hal
        simp only [trajZ, Nat.min_self] at hm
        rw [gRun_pools_eq] at hm
        exact ⟨r, ℓ, hm⟩)
    rw [himg] at hA
    exact_mod_cast hA
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

open Classical in
theorem fSurv_gridZ [NeZero s] (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) :
    (if Bt ja.1 ∣ ja.2 then fSurvZ E thr0 θ R K D Lv Bt lev s L rh S (cstar ja.1 ja.2) ω else 0) =
      ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        (if Bt ja.1 ∣ ja.2 ∧ NoOverflowZ E thr0 D Lv Bt s (ωsC E NE D Lt K ω) NE
            (trajZ E thr0 θ R K D Lv Bt lev s L rh (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy)) ∧
          SurvZ D Lv NE S (cstar ja.1 ja.2)
            (trajZ E thr0 θ R K D Lv Bt lev s L rh (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy))
        then 1 else 0) := by
  by_cases h : Bt ja.1 ∣ ja.2
  · rw [if_pos h]
    unfold fSurvZ
    refine Finset.sum_congr rfl fun yy _ => ?_
    congr 1
    exact if_congr (by simp [h]) rfl rfl
  · rw [if_neg h]
    symm
    exact Finset.sum_eq_zero fun yy _ => by simp [h]

open Classical in
/-- The cap: in every coin vector, the grid opportunities carry total survival weight at most `D·Lv·S`. -/
theorem cap_fSurvZ [NeZero s] (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j) (S : ℕ)
    (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 then fSurvZ E thr0 θ R K D Lv Bt lev s L rh S (cstar ja.1 ja.2) ω else 0)
      ≤ D * Lv * S := by
  simp only [fSurv_gridZ E thr0 θ R K D Lv Bt lev s L rh cstar S _ ω]
  rw [Finset.sum_comm]
  calc ∑ yy : Fin NE → Fin s, ∑ ja : Fin D × Fin NE, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        (if Bt ja.1 ∣ ja.2 ∧ NoOverflowZ E thr0 D Lv Bt s (ωsC E NE D Lt K ω) NE
            (trajZ E thr0 θ R K D Lv Bt lev s L rh (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy)) ∧
          SurvZ D Lv NE S (cstar ja.1 ja.2)
            (trajZ E thr0 θ R K D Lv Bt lev s L rh (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy))
        then 1 else 0)
      ≤ ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy * (D * Lv * S) := by
        refine Finset.sum_le_sum fun yy _ => ?_
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (Pool.P0119.wR_nonneg_s s yy)
        refine le_trans ?_ (card_surv_leZ E thr0 θ R K D Lv Bt lev s L rh hD hLv hlev cstar hE hthr
          (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) S)
        rw [Finset.card_filter]
        push_cast
        exact Finset.sum_le_sum fun ja _ => by
          by_cases h1 : Bt ja.1 ∣ ja.2 ∧ NoOverflowZ E thr0 D Lv Bt s (ωsC E NE D Lt K ω) NE
              (trajZ E thr0 θ R K D Lv Bt lev s L rh (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy)) ∧
            SurvZ D Lv NE S (cstar ja.1 ja.2)
              (trajZ E thr0 θ R K D Lv Bt lev s L rh (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (occSort s) NE (extY s yy))
          · rw [if_pos h1, if_pos ⟨h1.1, h1.2.2⟩]
          · rw [if_neg h1]; split_ifs <;> norm_num
    _ = D * Lv * S := by
        rw [← Finset.sum_mul, Pool.P0097.sum_wR _ (by simp [Finset.sum_const, Finset.card_univ]) NE, one_mul]

open Classical in
/-- Pointwise: the bad opportunities are the surviving forced ones, plus all of them on runs that are not good. -/
theorem card_bad_leZ (cstar : ℕ → ℕ → ι) (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hD : 0 < D) (S : ℕ) (ω : SlotC NE D Lt K × ι → Bool) (yy : ℕ → Fin s) :
    (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occLast s (cstar ja.1 ja.2)) yy rh) ∅ (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ) ≤
      ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 ∧
          NoOverflowZ E thr0 D Lv Bt s (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
            (trajZ E thr0 θ R K D Lv Bt lev s L rh (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
              (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (occLast s (cstar ja.1 ja.2)) NE yy) ∧
          SurvZ D Lv NE S (cstar ja.1 ja.2) (trajZ E thr0 θ R K D Lv Bt lev s L rh
            (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
            (occLast s (cstar ja.1 ja.2)) NE yy) then 1 else 0) +
        D * NE * (if GoodAZ E thr0 θ R K D Lv Bt lev s L rh NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) yy then 0 else 1) := by
  rw [Finset.card_filter]
  push_cast
  have hcard : (D * NE : ℝ) = ∑ _ja : Fin D × Fin NE, (1 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]; push_cast; ring
  rw [hcard, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ja _ => ?_
  split_ifs with h1 h2 h3 h4 <;> try norm_num
  all_goals first
    | (have := bad_leZ E thr0 θ R K D Lv Bt lev s L rh NE S cstar yy (j := ja.1) (a := ja.2) ja.2.2 h1.2.1 h1.2.2
       rw [if_neg (fun h => by tauto), if_pos (by assumption)] at this; linarith)
    | (have := bad_leZ E thr0 θ R K D Lv Bt lev s L rh NE S cstar yy (j := ja.1) (a := ja.2) ja.2.2 h1.2.1 h1.2.2
       simp_all)

open Classical in
/-- The opportunity coordinates of grid point `ja` (empty off the grid). -/
noncomputable def SopG (cstar : ℕ → ℕ → ι) (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hD : 0 < D) (ja : Fin D × Fin NE) : Finset (SlotC NE D Lt K × ι) :=
  if h : Bt ja.1 ∣ ja.2 then oppSet E thr0 D Bt lev NE Lt K (cstar ja.1 ja.2)
    (by rw [hE ja.1 ja.2 (by omega) h ja.2.2]; exact ja.2.2) else ∅

open Classical in
/-- The survival weight of grid point `ja` (zero off the grid). -/
noncomputable def fGZ [NeZero s] (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) : ℝ :=
  if Bt ja.1 ∣ ja.2 then fSurvZ E thr0 θ R K D Lv Bt lev s L rh S (cstar ja.1 ja.2) ω else 0

theorem fG_nonnegZ [NeZero s] (cstar : ℕ → ℕ → ι) (S : ℕ) (ja : Fin D × Fin NE) (ω : SlotC NE D Lt K × ι → Bool) :
    0 ≤ fGZ E thr0 θ R K D Lv Bt lev s L rh cstar S ja ω := by
  unfold fGZ; split_ifs
  · exact fSurv_nonnegZ E thr0 θ R K D Lv Bt lev s L rh S _ ω
  · exact le_rfl

open Classical in
theorem cap_fGZ [NeZero s] (hD : 0 < D) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv) (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j) (S : ℕ)
    (Sop : Fin D × Fin NE → Finset (SlotC NE D Lt K × ι)) (ω : SlotC NE D Lt K × ι → Bool) :
    ∑ ja : Fin D × Fin NE, (if EvS (Sop ja) oppVal ω then fGZ E thr0 θ R K D Lv Bt lev s L rh cstar S ja ω else 0)
      ≤ D * Lv * S := by
  refine le_trans (Finset.sum_le_sum fun ja _ => ?_)
    (cap_fSurvZ E thr0 θ R K D Lv Bt lev s L rh hD hLv hlev cstar hE hthr S ω)
  by_cases h : EvS (Sop ja) oppVal ω
  · rw [if_pos h]; rfl
  · rw [if_neg h]; exact fG_nonnegZ E thr0 θ R K D Lv Bt lev s L rh cstar S ja ω

open Classical in
theorem hper_fGZ [NeZero s] (cstar : ℕ → ℕ → ι) (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hD : 0 < D) (S : ℕ) (ω : SlotC NE D Lt K × ι → Bool) (ja : Fin D × Fin NE) :
    ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      (if Bt ja.1 ∣ ja.2 ∧
        NoOverflowZ E thr0 D Lv Bt s (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
          (trajZ E thr0 θ R K D Lv Bt lev s L rh (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
            (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (occLast s (cstar ja.1 ja.2)) NE (extY s yy)) ∧
        SurvZ D Lv NE S (cstar ja.1 ja.2) (trajZ E thr0 θ R K D Lv Bt lev s L rh
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
          (occLast s (cstar ja.1 ja.2)) NE (extY s yy)) then 1 else 0) =
      fGZ E thr0 θ R K D Lv Bt lev s L rh cstar S ja (force (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω) := by
  by_cases h : Bt ja.1 ∣ ja.2
  · unfold fGZ Pool.P0119.SopG
    rw [if_pos h, dif_pos h]
    rw [← forced_lawZ E thr0 θ R K D Lv Bt lev s L rh S (cstar ja.1 ja.2) _ ω]
    refine Finset.sum_congr rfl fun yy _ => ?_
    congr 1
    exact if_congr (by simp [h]) rfl rfl
  · unfold fGZ
    rw [if_neg h]
    exact Finset.sum_eq_zero fun yy _ => by simp [h]

open Classical in
/-- **Expected number of bad opportunities of the FO walk** (the FO analogue of P0082's `count_bad`). Over the
sampling/filter coins (P0082's array, weights `wtv p`) and i.i.d. uniform slots, the expected number of grid
opportunities `(j, a)` whose comparator copy is not sampled and, forced into its own forced copy-last run, is never
evicted before `NE` is at most `D·Lv·S/π + D·NE·P(the actual run is not GoodA)`. -/
theorem count_bad_Z [NeZero s] (hB : BtHyp D Bt) (hLv : 0 < Lv) (hlev : ∀ r a, lev r a + 1 < Lv)
    (cstar : ℕ → ℕ → ι)
    (hE : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → E (cstar j a) = a)
    (hthr : ∀ j a, j ≤ D - 1 → Bt j ∣ a → a < NE → thr0 (cstar j a) = j)
    (p : SlotC NE D Lt K × ι → ℝ) (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1) (π : ℝ) (hπ : 0 < π)
    (hπ1 : π ≤ 1)
    (hpi : ∀ (j : Fin D) (a : Fin NE) (h : Bt j ∣ a),
      π ≤ piS p (oppSet E thr0 D Bt lev NE Lt K (cstar j a)
        (by rw [hE j a (by omega) h a.2]; exact a.2)) oppVal)
    (S : ℕ) :
    ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      (#{ja : Fin D × Fin NE | Bt ja.1 ∣ ja.2 ∧ ωsC E NE D Lt K ω (cstar ja.1 ja.2) = false ∧
        evict E thr0 (gChat E thr0 θ R K D Lv Bt lev (zUpd D Lv s L (occLast s (cstar ja.1 ja.2)) (extY s yy) rh) ∅ (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)))
          θ R K D Lv Bt lev NE cstar (ωsC E NE D Lt K ω) (φC NE D Lt K ω) ja.1 ja.2 = none} : ℝ)
      ≤ (D * Lv * S : ℝ) / π + D * NE * ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s,
        Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        (if GoodAZ E thr0 θ R K D Lv Bt lev s L rh NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) then 0 else 1) := by
  have hD := hB.hD
  have hw : ∀ ω, 0 ≤ wtv p ω := wtv_nonneg hp0 hp1
  have hwR : ∀ yy : Fin NE → Fin s, 0 ≤ Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy := Pool.P0119.wR_nonneg_s s
  have hpiG : ∀ ja : Fin D × Fin NE, π ≤ piS p (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal := by
    intro ja
    by_cases h : Bt ja.1 ∣ ja.2
    · unfold Pool.P0119.SopG; rw [dif_pos h]; exact hpi ja.1 ja.2 h
    · unfold Pool.P0119.SopG; rw [dif_neg h]; simp only [piS, Finset.prod_empty]; exact hπ1
  have hcap : ∀ ω : SlotC NE D Lt K × ι → Bool, ∑ ja : Fin D × Fin NE,
      (if EvS (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω then fGZ E thr0 θ R K D Lv Bt lev s L rh cstar S ja ω
        else 0) ≤ (D * Lv * S : ℝ) :=
    cap_fGZ E thr0 θ R K D Lv Bt lev s L rh hD hLv hlev cstar hE hthr S (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD)
  have hcount := Pool.P0119.forced_count_real p hp0 hp1 (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD) (fun _ => oppVal)
    (fGZ E thr0 θ R K D Lv Bt lev s L rh cstar S) (fG_nonnegZ E thr0 θ R K D Lv Bt lev s L rh cstar S)
    (D * Lv * S : ℝ) π hπ hpiG (fun ω => by convert hcap ω)
  refine le_trans (Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun yy _ =>
    mul_le_mul_of_nonneg_left (card_bad_leZ E thr0 θ R K D Lv Bt lev s L rh cstar hE hD S ω (extY s yy))
      (hwR yy)) (hw ω)) ?_
  simp only [mul_add, Finset.sum_add_distrib]
  have h1 : ∀ ω, ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      ∑ ja : Fin D × Fin NE, (if Bt ja.1 ∣ ja.2 ∧
        NoOverflowZ E thr0 D Lv Bt s (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) NE
          (trajZ E thr0 θ R K D Lv Bt lev s L rh (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2))
            (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2)) (occLast s (cstar ja.1 ja.2)) NE (extY s yy)) ∧
        SurvZ D Lv NE S (cstar ja.1 ja.2) (trajZ E thr0 θ R K D Lv Bt lev s L rh
          (forceS (ωsC E NE D Lt K ω) (cstar ja.1 ja.2)) (forceF K (φC NE D Lt K ω) (cstar ja.1 ja.2))
          (occLast s (cstar ja.1 ja.2)) NE (extY s yy)) then 1 else 0) =
      ∑ ja, fGZ E thr0 θ R K D Lv Bt lev s L rh cstar S ja (force (Pool.P0119.SopG E thr0 K D Bt lev cstar hE hD ja) oppVal ω) := by
    intro ω
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ja _ => ?_
    rw [← hper_fGZ E thr0 θ R K D Lv Bt lev s L rh cstar hE hD S ω ja]
  simp only [h1]
  have h2 : ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
      ((D : ℝ) * NE * (if GoodAZ E thr0 θ R K D Lv Bt lev s L rh NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω)
        (extY s yy) then 0 else 1)) =
      D * NE * ∑ ω, wtv p ω * ∑ yy : Fin NE → Fin s, Pool.P0070.wR (fun _ => 1 / (s : ℝ)) yy *
        (if GoodAZ E thr0 θ R K D Lv Bt lev s L rh NE S (ωsC E NE D Lt K ω) (φC NE D Lt K ω) (extY s yy) then 0 else 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun yy _ => by ring
  rw [h2]
  refine le_trans (le_of_eq ?_) (add_le_add_left hcount _)
  congr 1

end Main

end Pool.P0164
